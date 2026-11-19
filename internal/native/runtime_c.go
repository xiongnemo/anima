package native

// runtimeHeader contains the zero-external-dependency C11 runtime (POSIX + pthreads + OpenSSL 3.0)
// emitted by `anima build` into generated native executables.
const runtimeHeader = `#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include <ctype.h>
#include <time.h>
#include <errno.h>
#include <unistd.h>
#include <fcntl.h>
#include <pthread.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <netdb.h>
#include <openssl/ssl.h>
#include <openssl/evp.h>
#include <openssl/hmac.h>
#include <openssl/crypto.h>

typedef enum {
    VAL_VOID = 0,
    VAL_INT,
    VAL_BOOL,
    VAL_STR,
    VAL_NONE,
    VAL_LIST,
    VAL_MAP,
    VAL_ENTITY,
    VAL_VARIANT,
    VAL_CLOSURE,
    VAL_HANDLE
} ValKind;

typedef struct AnimaVal AnimaVal;
typedef struct AnimaList AnimaList;
typedef struct AnimaMap AnimaMap;
typedef struct AnimaEntity AnimaEntity;
typedef struct AnimaVariant AnimaVariant;
typedef struct AnimaClosure AnimaClosure;
typedef struct AnimaHandle AnimaHandle;

struct AnimaVal {
    ValKind kind;
    union {
        int64_t i;
        bool b;
        char *s;
        AnimaList *list;
        AnimaMap *map;
        AnimaEntity *ent;
        AnimaVariant *var;
        AnimaClosure *clos;
        AnimaHandle *hdl;
    } u;
};

struct AnimaList {
    size_t len;
    size_t cap;
    AnimaVal *items;
};

typedef struct {
    char *key;
    AnimaVal val;
} AnimaMapEntry;

struct AnimaMap {
    size_t len;
    size_t cap;
    AnimaMapEntry *entries;
};

struct AnimaEntity {
    char *type_name;
    size_t len;
    size_t cap;
    AnimaMapEntry *fields;
};

struct AnimaVariant {
    char *name;
    size_t len;
    AnimaVal *fields;
};

typedef AnimaVal (*AnimaClosureFn)(AnimaVal *upvals, int argc, AnimaVal *argv);

struct AnimaClosure {
    AnimaClosureFn fn;
    int num_upvals;
    AnimaVal *upvals;
};

typedef enum {
    HDL_LISTENER = 0,
    HDL_STREAM,
    HDL_FILE,
    HDL_THREADPOOL,
    HDL_CHANNEL,
    HDL_MUTEX,
    HDL_SEMAPHORE,
    HDL_SESSION,
    HDL_FUTURE,
    HDL_BYTEVIEW
} HandleKind;

typedef struct {
    AnimaClosure *clos;
    AnimaHandle *fut;
} PoolTask;

struct AnimaHandle {
    HandleKind kind;
    bool closed;
    int fd;
    FILE *fp;
    uint8_t *bytes;
    size_t bytes_len;
    // Mutex / Semaphore / Channel / Pool / Future
    pthread_mutex_t mu;
    pthread_cond_t cond_not_empty;
    pthread_cond_t cond_not_full;
    AnimaVal cell_val;
    int sem_count;
    // Channel ring buffer
    AnimaVal *chan_buf;
    size_t chan_cap;
    size_t chan_head;
    size_t chan_tail;
    size_t chan_count;
    // ThreadPool
    PoolTask *pool_q;
    size_t pool_cap;
    size_t pool_head;
    size_t pool_tail;
    size_t pool_count;
    int pool_nworkers;
    pthread_t *pool_threads;
    // Future
    bool fut_done;
    AnimaVal fut_val;
    pthread_t fut_thread;
    bool fut_has_thread;
};

static int g_argc = 0;
static char **g_argv = NULL;

static AnimaVal v_void(void) { AnimaVal v = {0}; v.kind = VAL_VOID; return v; }
static AnimaVal v_none(void) { AnimaVal v = {0}; v.kind = VAL_NONE; return v; }
static AnimaVal v_int(int64_t x) { AnimaVal v = {0}; v.kind = VAL_INT; v.u.i = x; return v; }
static AnimaVal v_bool(bool b) { AnimaVal v = {0}; v.kind = VAL_BOOL; v.u.b = b; return v; }
static AnimaVal v_str(const char *s) {
    AnimaVal v = {0}; v.kind = VAL_STR;
    v.u.s = strdup(s ? s : "");
    return v;
}

static bool v_truthy(AnimaVal v) {
    switch (v.kind) {
        case VAL_BOOL: return v.u.b;
        case VAL_INT: return v.u.i != 0;
        case VAL_STR: return v.u.s && v.u.s[0] != '\0';
        case VAL_NONE: case VAL_VOID: return false;
        case VAL_LIST: return v.u.list && v.u.list->len > 0;
        default: return true;
    }
}

static char *v_to_cstr(AnimaVal v);

static AnimaVal v_list_new(size_t n, AnimaVal *items) {
    AnimaList *l = calloc(1, sizeof(AnimaList));
    l->len = n;
    l->cap = n > 4 ? n : 4;
    l->items = calloc(l->cap, sizeof(AnimaVal));
    for (size_t i = 0; i < n; i++) l->items[i] = items[i];
    AnimaVal v = {0}; v.kind = VAL_LIST; v.u.list = l; return v;
}

static void v_list_push(AnimaVal listv, AnimaVal item) {
    AnimaList *l = listv.u.list;
    if (l->len >= l->cap) {
        l->cap = l->cap == 0 ? 4 : l->cap * 2;
        l->items = realloc(l->items, l->cap * sizeof(AnimaVal));
    }
    l->items[l->len++] = item;
}

static AnimaVal v_map_new(void) {
    AnimaMap *m = calloc(1, sizeof(AnimaMap));
    m->cap = 8;
    m->entries = calloc(m->cap, sizeof(AnimaMapEntry));
    AnimaVal v = {0}; v.kind = VAL_MAP; v.u.map = m; return v;
}

static void v_map_set(AnimaVal mv, const char *k, AnimaVal val) {
    AnimaMap *m = mv.u.map;
    for (size_t i = 0; i < m->len; i++) {
        if (strcmp(m->entries[i].key, k) == 0) {
            m->entries[i].val = val;
            return;
        }
    }
    if (m->len >= m->cap) {
        m->cap = m->cap == 0 ? 8 : m->cap * 2;
        m->entries = realloc(m->entries, m->cap * sizeof(AnimaMapEntry));
    }
    m->entries[m->len].key = strdup(k);
    m->entries[m->len].val = val;
    m->len++;
}

static AnimaVal v_map_get(AnimaVal mv, const char *k) {
    if (mv.kind != VAL_MAP || !mv.u.map) return v_none();
    for (size_t i = 0; i < mv.u.map->len; i++) {
        if (strcmp(mv.u.map->entries[i].key, k) == 0) return mv.u.map->entries[i].val;
    }
    return v_none();
}

// Element access for xs[i] and m[k]; a map key is the printed form of k.
static AnimaVal v_index_get(AnimaVal c, AnimaVal i) {
    if (c.kind == VAL_LIST && c.u.list && i.u.i >= 0 && (size_t)i.u.i < c.u.list->len) return c.u.list->items[i.u.i];
    if (c.kind == VAL_MAP) { char *k = v_to_cstr(i); AnimaVal r = v_map_get(c, k); free(k); return r; }
    return v_none();
}

static void v_index_set(AnimaVal c, AnimaVal i, AnimaVal val) {
    if (c.kind == VAL_LIST && c.u.list && i.u.i >= 0 && (size_t)i.u.i < c.u.list->len) { c.u.list->items[i.u.i] = val; return; }
    if (c.kind == VAL_MAP) { char *k = v_to_cstr(i); v_map_set(c, k, val); free(k); }
}

static AnimaVal v_entity_new(const char *tname) {
    AnimaEntity *e = calloc(1, sizeof(AnimaEntity));
    e->type_name = strdup(tname);
    e->cap = 8;
    e->fields = calloc(e->cap, sizeof(AnimaMapEntry));
    AnimaVal v = {0}; v.kind = VAL_ENTITY; v.u.ent = e; return v;
}

static void v_entity_set(AnimaVal ev, const char *k, AnimaVal val) {
    if (ev.kind == VAL_MAP) { v_map_set(ev, k, val); return; }
    if (ev.kind != VAL_ENTITY || !ev.u.ent) return;
    AnimaEntity *e = ev.u.ent;
    for (size_t i = 0; i < e->len; i++) {
        if (strcmp(e->fields[i].key, k) == 0) { e->fields[i].val = val; return; }
    }
    if (e->len >= e->cap) {
        e->cap = e->cap == 0 ? 8 : e->cap * 2;
        e->fields = realloc(e->fields, e->cap * sizeof(AnimaMapEntry));
    }
    e->fields[e->len].key = strdup(k);
    e->fields[e->len].val = val;
    e->len++;
}

static AnimaVal v_entity_get(AnimaVal ev, const char *k) {
    if (ev.kind == VAL_MAP) return v_map_get(ev, k);
    if (ev.kind != VAL_ENTITY || !ev.u.ent) return v_void();
    for (size_t i = 0; i < ev.u.ent->len; i++) {
        if (strcmp(ev.u.ent->fields[i].key, k) == 0) return ev.u.ent->fields[i].val;
    }
    return v_void();
}

static AnimaVal v_entity_clone(AnimaVal ev) {
    if (ev.kind != VAL_ENTITY || !ev.u.ent) return v_entity_new("Object");
    AnimaVal c = v_entity_new(ev.u.ent->type_name);
    for (size_t i = 0; i < ev.u.ent->len; i++) {
        v_entity_set(c, ev.u.ent->fields[i].key, ev.u.ent->fields[i].val);
    }
    return c;
}

static AnimaVal v_variant(const char *name, size_t n, AnimaVal *fields) {
    AnimaVariant *vr = calloc(1, sizeof(AnimaVariant));
    vr->name = strdup(name);
    vr->len = n;
    if (n > 0) {
        vr->fields = calloc(n, sizeof(AnimaVal));
        for (size_t i = 0; i < n; i++) vr->fields[i] = fields[i];
    }
    AnimaVal v = {0}; v.kind = VAL_VARIANT; v.u.var = vr; return v;
}

static AnimaVal v_ok(AnimaVal val) { return v_variant("Ok", 1, &val); }
static AnimaVal v_err(const char *msg) { AnimaVal s = v_str(msg); return v_variant("Err", 1, &s); }
static AnimaVal v_some(AnimaVal val) { return v_variant("Some", 1, &val); }

static bool v_is_variant(AnimaVal v, const char *name) {
    if (v.kind == VAL_NONE && strcmp(name, "None") == 0) return true;
    return v.kind == VAL_VARIANT && v.u.var && strcmp(v.u.var->name, name) == 0;
}

static AnimaVal v_variant_field(AnimaVal v, size_t idx) {
    if (v.kind == VAL_VARIANT && v.u.var && idx < v.u.var->len) return v.u.var->fields[idx];
    return v_none();
}

static bool v_eq(AnimaVal a, AnimaVal b) {
    if (a.kind != b.kind) return false;
    switch (a.kind) {
        case VAL_VOID: case VAL_NONE: return true;
        case VAL_INT: return a.u.i == b.u.i;
        case VAL_BOOL: return a.u.b == b.u.b;
        case VAL_STR: return strcmp(a.u.s, b.u.s) == 0;
        case VAL_VARIANT:
            if (strcmp(a.u.var->name, b.u.var->name) != 0 || a.u.var->len != b.u.var->len) return false;
            for (size_t i = 0; i < a.u.var->len; i++) {
                if (!v_eq(a.u.var->fields[i], b.u.var->fields[i])) return false;
            }
            return true;
        default: return false;
    }
}

static char *v_to_cstr(AnimaVal v) {
    char buf[128];
    switch (v.kind) {
        case VAL_VOID: return strdup("()");
        case VAL_NONE: return strdup("None");
        case VAL_INT: snprintf(buf, sizeof(buf), "%lld", (long long)v.u.i); return strdup(buf);
        case VAL_BOOL: return strdup(v.u.b ? "True" : "False");
        case VAL_STR: return strdup(v.u.s ? v.u.s : "");
        case VAL_VARIANT: {
            if (!v.u.var || v.u.var->len == 0) return strdup(v.u.var ? v.u.var->name : "None");
            char *inner = v_to_cstr(v.u.var->fields[0]);
            size_t len = strlen(v.u.var->name) + strlen(inner) + 4;
            char *out = malloc(len);
            snprintf(out, len, "%s(%s)", v.u.var->name, inner);
            free(inner);
            return out;
        }
        default: return strdup("<val>");
    }
}

static AnimaVal v_str_cat(AnimaVal a, AnimaVal b) {
    char *sa = v_to_cstr(a);
    char *sb = v_to_cstr(b);
    size_t la = strlen(sa), lb = strlen(sb);
    char *out = malloc(la + lb + 1);
    memcpy(out, sa, la);
    memcpy(out + la, sb, lb + 1);
    free(sa); free(sb);
    AnimaVal r = {0}; r.kind = VAL_STR; r.u.s = out; return r;
}

static AnimaVal v_closure(AnimaClosureFn fn, int nup, AnimaVal *ups) {
    AnimaClosure *c = calloc(1, sizeof(AnimaClosure));
    c->fn = fn;
    c->num_upvals = nup;
    if (nup > 0) {
        c->upvals = calloc((size_t)nup, sizeof(AnimaVal));
        memcpy(c->upvals, ups, (size_t)nup * sizeof(AnimaVal));
    }
    AnimaVal v = {0}; v.kind = VAL_CLOSURE; v.u.clos = c; return v;
}

static AnimaVal v_call_clos(AnimaVal cv, int argc, AnimaVal *argv) {
    if (cv.kind != VAL_CLOSURE || !cv.u.clos || !cv.u.clos->fn) return v_void();
    return cv.u.clos->fn(cv.u.clos->upvals, argc, argv);
}

static int64_t anima_len(AnimaVal v) {
    if (v.kind == VAL_LIST && v.u.list) return (int64_t)v.u.list->len;
    if (v.kind == VAL_MAP && v.u.map) return (int64_t)v.u.map->len;
    if (v.kind == VAL_STR && v.u.s) return (int64_t)strlen(v.u.s);
    if (v.kind == VAL_HANDLE && v.u.hdl && v.u.hdl->kind == HDL_BYTEVIEW) return (int64_t)v.u.hdl->bytes_len;
    return 0;
}

static AnimaVal anima_print(AnimaVal v) {
    char *s = v_to_cstr(v);
    printf("%s\n", s);
    fflush(stdout);
    free(s);
    return v_void();
}

// ─── std.fp combinators ───
static AnimaVal fp_filter(AnimaVal listv, AnimaVal fn) {
    AnimaVal out = v_list_new(0, NULL);
    if (listv.kind == VAL_LIST && listv.u.list) {
        for (size_t i = 0; i < listv.u.list->len; i++) {
            AnimaVal arg = listv.u.list->items[i];
            if (v_truthy(v_call_clos(fn, 1, &arg))) v_list_push(out, arg);
        }
    }
    return out;
}

static AnimaVal fp_map(AnimaVal listv, AnimaVal fn) {
    AnimaVal out = v_list_new(0, NULL);
    if (listv.kind == VAL_LIST && listv.u.list) {
        for (size_t i = 0; i < listv.u.list->len; i++) {
            AnimaVal arg = listv.u.list->items[i];
            v_list_push(out, v_call_clos(fn, 1, &arg));
        }
    }
    return out;
}

static AnimaVal fp_flat_map(AnimaVal listv, AnimaVal fn) {
    AnimaVal out = v_list_new(0, NULL);
    if (listv.kind == VAL_LIST && listv.u.list) {
        for (size_t i = 0; i < listv.u.list->len; i++) {
            AnimaVal arg = listv.u.list->items[i];
            AnimaVal r = v_call_clos(fn, 1, &arg);
            if (r.kind == VAL_LIST && r.u.list) {
                for (size_t j = 0; j < r.u.list->len; j++) v_list_push(out, r.u.list->items[j]);
            }
        }
    }
    return out;
}

static AnimaVal fp_fold(AnimaVal listv, AnimaVal init, AnimaVal fn) {
    AnimaVal acc = init;
    if (listv.kind == VAL_LIST && listv.u.list) {
        for (size_t i = 0; i < listv.u.list->len; i++) {
            AnimaVal args[2] = {acc, listv.u.list->items[i]};
            acc = v_call_clos(fn, 2, args);
        }
    }
    return acc;
}

static AnimaVal fp_sum(AnimaVal listv) {
    int64_t s = 0;
    if (listv.kind == VAL_LIST && listv.u.list) {
        for (size_t i = 0; i < listv.u.list->len; i++) s += listv.u.list->items[i].u.i;
    }
    return v_int(s);
}

static AnimaVal fp_filter_ok(AnimaVal listv) {
    AnimaVal out = v_list_new(0, NULL);
    if (listv.kind == VAL_LIST && listv.u.list) {
        for (size_t i = 0; i < listv.u.list->len; i++) {
            AnimaVal el = listv.u.list->items[i];
            if (v_is_variant(el, "Ok") || v_is_variant(el, "Some")) {
                v_list_push(out, v_variant_field(el, 0));
            }
        }
    }
    return out;
}

static AnimaVal fp_unwrap_or(AnimaVal v, AnimaVal def) {
    if (v_is_variant(v, "Ok") || v_is_variant(v, "Some")) return v_variant_field(v, 0);
    return def;
}

static AnimaVal fp_and_then(AnimaVal v, AnimaVal fn) {
    if (v_is_variant(v, "Ok") || v_is_variant(v, "Some")) {
        AnimaVal arg = v_variant_field(v, 0);
        return v_call_clos(fn, 1, &arg);
    }
    return v;
}

// ─── std.bytes & std.crypto (OpenSSL 3.0 EVP + HMAC) ───
static AnimaVal bytes_from_str(const char *s) {
    AnimaHandle *h = calloc(1, sizeof(AnimaHandle));
    h->kind = HDL_BYTEVIEW;
    h->bytes_len = strlen(s);
    h->bytes = malloc(h->bytes_len + 1);
    memcpy(h->bytes, s, h->bytes_len + 1);
    AnimaVal v = {0}; v.kind = VAL_HANDLE; v.u.hdl = h; return v;
}

static int hex_nibble(char c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    if (c >= 'A' && c <= 'F') return c - 'A' + 10;
    return 0;
}

static AnimaVal bytes_from_hex(const char *hx) {
    size_t n = strlen(hx) / 2;
    AnimaHandle *h = calloc(1, sizeof(AnimaHandle));
    h->kind = HDL_BYTEVIEW;
    h->bytes_len = n;
    h->bytes = calloc(n + 1, 1);
    for (size_t i = 0; i < n; i++) {
        h->bytes[i] = (uint8_t)((hex_nibble(hx[2*i]) << 4) | hex_nibble(hx[2*i+1]));
    }
    AnimaVal v = {0}; v.kind = VAL_HANDLE; v.u.hdl = h; return v;
}

static AnimaVal crypto_sha256(const char *s) {
    unsigned char hash[EVP_MAX_MD_SIZE];
    unsigned int out_len = 0;
    EVP_Digest(s, strlen(s), hash, &out_len, EVP_sha256(), NULL);
    char hexstr[128];
    for (unsigned int i = 0; i < out_len; i++) snprintf(hexstr + 2*i, 3, "%02x", hash[i]);
    return v_str(hexstr);
}

static AnimaVal crypto_hmac_sha256(const char *key, const char *msg) {
    unsigned char hash[EVP_MAX_MD_SIZE];
    unsigned int out_len = 0;
    HMAC(EVP_sha256(), key, (int)strlen(key), (const unsigned char *)msg, strlen(msg), hash, &out_len);
    char hexstr[128];
    for (unsigned int i = 0; i < out_len; i++) snprintf(hexstr + 2*i, 3, "%02x", hash[i]);
    return v_str(hexstr);
}

static AnimaVal crypto_ct_eq(const char *a, const char *b) {
    size_t la = strlen(a), lb = strlen(b);
    if (la != lb) return v_bool(false);
    return v_bool(CRYPTO_memcmp(a, b, la) == 0);
}

// ─── std.socket (POSIX TCP sockets) ───
static void set_fd_timeout(int fd, int64_t ms) {
    struct timeval tv;
    tv.tv_sec = ms / 1000;
    tv.tv_usec = (ms % 1000) * 1000;
    setsockopt(fd, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof(tv));
    setsockopt(fd, SOL_SOCKET, SO_SNDTIMEO, &tv, sizeof(tv));
}

static AnimaVal sock_listen_tcp(const char *host, int64_t port) {
    int fd = socket(AF_INET, SOCK_STREAM, 0);
    if (fd < 0) return v_err(strerror(errno));
    int yes = 1;
    setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &yes, sizeof(yes));
    struct sockaddr_in addr = {0};
    addr.sin_family = AF_INET;
    addr.sin_port = htons((uint16_t)port);
    if (inet_pton(AF_INET, host, &addr.sin_addr) <= 0) addr.sin_addr.s_addr = htonl(INADDR_ANY);
    if (bind(fd, (struct sockaddr *)&addr, sizeof(addr)) < 0) { close(fd); return v_err(strerror(errno)); }
    if (listen(fd, 64) < 0) { close(fd); return v_err(strerror(errno)); }
    AnimaHandle *h = calloc(1, sizeof(AnimaHandle));
    h->kind = HDL_LISTENER; h->fd = fd;
    AnimaVal v = {0}; v.kind = VAL_HANDLE; v.u.hdl = h;
    return v_ok(v);
}

static AnimaVal sock_connect_tcp(const char *host, int64_t port) {
    struct addrinfo hints = {0}, *res = NULL;
    hints.ai_family = AF_INET;
    hints.ai_socktype = SOCK_STREAM;
    char pstr[32];
    snprintf(pstr, sizeof(pstr), "%lld", (long long)port);
    if (getaddrinfo(host, pstr, &hints, &res) != 0 || !res) return v_err("dns/addr resolution failed");
    int fd = socket(res->ai_family, res->ai_socktype, res->ai_protocol);
    if (fd < 0) { freeaddrinfo(res); return v_err(strerror(errno)); }
    set_fd_timeout(fd, 5000);
    if (connect(fd, res->ai_addr, res->ai_addrlen) < 0) {
        int e = errno; close(fd); freeaddrinfo(res); return v_err(strerror(e));
    }
    freeaddrinfo(res);
    AnimaHandle *h = calloc(1, sizeof(AnimaHandle));
    h->kind = HDL_STREAM; h->fd = fd;
    AnimaVal v = {0}; v.kind = VAL_HANDLE; v.u.hdl = h;
    return v_ok(v);
}

static void hdl_close(AnimaVal hv);

static AnimaVal hdl_listener_port(AnimaVal hv) {
    struct sockaddr_in addr = {0};
    socklen_t alen = sizeof(addr);
    getsockname(hv.u.hdl->fd, (struct sockaddr *)&addr, &alen);
    return v_int(ntohs(addr.sin_port));
}

static AnimaVal hdl_listener_accept(AnimaVal hv, int64_t timeout_ms) {
    set_fd_timeout(hv.u.hdl->fd, timeout_ms);
    int cfd = accept(hv.u.hdl->fd, NULL, NULL);
    if (cfd < 0) return v_err(strerror(errno));
    set_fd_timeout(cfd, 5000);
    AnimaHandle *h = calloc(1, sizeof(AnimaHandle));
    h->kind = HDL_STREAM; h->fd = cfd;
    AnimaVal v = {0}; v.kind = VAL_HANDLE; v.u.hdl = h;
    return v_ok(v);
}

static AnimaVal hdl_stream_send(AnimaVal hv, const char *txt) {
    if (!hv.u.hdl || hv.u.hdl->closed) return v_err("socket closed");
    ssize_t n = send(hv.u.hdl->fd, txt, strlen(txt), 0);
    if (n < 0) return v_err(strerror(errno));
    return v_ok(v_int((int64_t)n));
}

static AnimaVal hdl_stream_recv(AnimaVal hv, int64_t max_b) {
    if (!hv.u.hdl || hv.u.hdl->closed) return v_err("socket closed");
    if (max_b <= 0) max_b = 4096;
    char *buf = malloc((size_t)max_b + 1);
    ssize_t n = recv(hv.u.hdl->fd, buf, (size_t)max_b, 0);
    if (n < 0) { int e = errno; free(buf); return v_err(strerror(e)); }
    if (n == 0) { free(buf); return v_err("EOF"); }
    buf[n] = '\0';
    AnimaVal r = v_ok(v_str(buf));
    free(buf);
    return r;
}

// ─── std.requests (HTTP/HTTPS over POSIX + OpenSSL) ───
static AnimaVal http_do(const char *method, const char *url, const char *body, int64_t timeout_ms) {
    bool is_https = strncmp(url, "https://", 8) == 0;
    const char *rest = is_https ? url + 8 : (strncmp(url, "http://", 7) == 0 ? url + 7 : url);
    const char *slash = strchr(rest, '/');
    char hostport[256] = {0};
    const char *path = slash ? slash : "/";
    if (slash) {
        size_t l = (size_t)(slash - rest);
        if (l >= sizeof(hostport)) l = sizeof(hostport) - 1;
        memcpy(hostport, rest, l);
    } else {
        strncpy(hostport, rest, sizeof(hostport) - 1);
    }
    char host[256] = {0};
    char port[16];
    strcpy(port, is_https ? "443" : "80");
    const char *colon = strchr(hostport, ':');
    if (colon) {
        size_t hl = (size_t)(colon - hostport);
        memcpy(host, hostport, hl);
        strncpy(port, colon + 1, sizeof(port) - 1);
    } else {
        strcpy(host, hostport);
    }

    struct addrinfo hints = {0}, *res = NULL;
    hints.ai_family = AF_UNSPEC;
    hints.ai_socktype = SOCK_STREAM;
    if (getaddrinfo(host, port, &hints, &res) != 0 || !res) return v_err("http dns failed");
    int fd = socket(res->ai_family, res->ai_socktype, res->ai_protocol);
    if (fd < 0) { freeaddrinfo(res); return v_err(strerror(errno)); }
    set_fd_timeout(fd, timeout_ms > 0 ? timeout_ms : 5000);
    if (connect(fd, res->ai_addr, res->ai_addrlen) < 0) {
        int e = errno; close(fd); freeaddrinfo(res); return v_err(strerror(e));
    }
    freeaddrinfo(res);

    SSL_CTX *ctx = NULL;
    SSL *ssl = NULL;
    if (is_https) {
        ctx = SSL_CTX_new(TLS_client_method());
        ssl = SSL_new(ctx);
        SSL_set_tlsext_host_name(ssl, host);
        SSL_set_fd(ssl, fd);
        if (SSL_connect(ssl) <= 0) {
            SSL_free(ssl); SSL_CTX_free(ctx); close(fd);
            return v_err("tls handshake failed");
        }
    }

    char reqbuf[4096];
    int reqlen = 0;
    if (body && body[0] != '\0') {
        reqlen = snprintf(reqbuf, sizeof(reqbuf),
            "%s %s HTTP/1.1\r\nHost: %s\r\nConnection: close\r\nContent-Length: %zu\r\nContent-Type: application/json\r\n\r\n%s",
            method, path, hostport, strlen(body), body);
    } else {
        reqlen = snprintf(reqbuf, sizeof(reqbuf),
            "%s %s HTTP/1.1\r\nHost: %s\r\nConnection: close\r\n\r\n",
            method, path, hostport);
    }
    if (ssl) SSL_write(ssl, reqbuf, reqlen);
    else send(fd, reqbuf, (size_t)reqlen, 0);

    size_t cap = 8192, total = 0;
    char *raw = malloc(cap);
    for (;;) {
        if (total + 2048 > cap) { cap *= 2; raw = realloc(raw, cap); }
        ssize_t n = ssl ? SSL_read(ssl, raw + total, 2048) : recv(fd, raw + total, 2048, 0);
        if (n <= 0) break;
        total += (size_t)n;
    }
    raw[total] = '\0';
    if (ssl) { SSL_shutdown(ssl); SSL_free(ssl); SSL_CTX_free(ctx); }
    close(fd);

    int status = 200;
    if (strncmp(raw, "HTTP/", 5) == 0) {
        const char *sp = strchr(raw, ' ');
        if (sp) status = atoi(sp + 1);
    }
    char *sep = strstr(raw, "\r\n\r\n");
    const char *rbody = sep ? sep + 4 : raw;
    AnimaVal ent = v_entity_new("HttpResponse");
    v_entity_set(ent, "status", v_int(status));
    v_entity_set(ent, "body", v_str(rbody));
    v_entity_set(ent, "ok", v_bool(status >= 200 && status < 300));
    free(raw);
    return v_ok(ent);
}

typedef struct {
    char *url;
    int64_t timeout_ms;
    AnimaHandle *fut;
} AsyncHttpArg;

static void *async_http_worker(void *arg) {
    AsyncHttpArg *a = (AsyncHttpArg *)arg;
    AnimaVal res = http_do("GET", a->url, "", a->timeout_ms);
    pthread_mutex_lock(&a->fut->mu);
    a->fut->fut_val = res;
    a->fut->fut_done = true;
    pthread_cond_broadcast(&a->fut->cond_not_empty);
    pthread_mutex_unlock(&a->fut->mu);
    free(a->url);
    free(a);
    return NULL;
}

static AnimaVal req_session_new(int64_t pool_sz) {
    (void)pool_sz;
    AnimaHandle *h = calloc(1, sizeof(AnimaHandle));
    h->kind = HDL_SESSION;
    AnimaVal v = {0}; v.kind = VAL_HANDLE; v.u.hdl = h; return v;
}

static AnimaVal req_session_get_async(AnimaVal sess, const char *url, int64_t ms) {
    (void)sess;
    AnimaHandle *fut = calloc(1, sizeof(AnimaHandle));
    fut->kind = HDL_FUTURE;
    pthread_mutex_init(&fut->mu, NULL);
    pthread_cond_init(&fut->cond_not_empty, NULL);
    AsyncHttpArg *arg = calloc(1, sizeof(AsyncHttpArg));
    arg->url = strdup(url);
    arg->timeout_ms = ms;
    arg->fut = fut;
    fut->fut_has_thread = true;
    pthread_create(&fut->fut_thread, NULL, async_http_worker, arg);
    AnimaVal v = {0}; v.kind = VAL_HANDLE; v.u.hdl = fut; return v;
}

static AnimaVal fut_await(AnimaVal fv) {
    AnimaHandle *f = fv.u.hdl;
    if (f->fut_has_thread) {
        pthread_join(f->fut_thread, NULL);
        f->fut_has_thread = false;
    }
    pthread_mutex_lock(&f->mu);
    while (!f->fut_done) pthread_cond_wait(&f->cond_not_empty, &f->mu);
    AnimaVal res = f->fut_val;
    pthread_mutex_unlock(&f->mu);
    return res;
}

static AnimaVal req_gather(AnimaVal listv) {
    AnimaVal out = v_list_new(0, NULL);
    if (listv.kind == VAL_LIST && listv.u.list) {
        for (size_t i = 0; i < listv.u.list->len; i++) {
            v_list_push(out, fut_await(listv.u.list->items[i]));
        }
    }
    return out;
}

// ─── std.concurrent (ThreadPool, Channel, Mutex, Semaphore) ───
static void *pool_worker(void *arg) {
    AnimaHandle *p = (AnimaHandle *)arg;
    for (;;) {
        pthread_mutex_lock(&p->mu);
        while (p->pool_count == 0 && !p->closed) {
            pthread_cond_wait(&p->cond_not_empty, &p->mu);
        }
        if (p->pool_count == 0 && p->closed) {
            pthread_mutex_unlock(&p->mu);
            break;
        }
        PoolTask task = p->pool_q[p->pool_head];
        p->pool_head = (p->pool_head + 1) % p->pool_cap;
        p->pool_count--;
        pthread_cond_signal(&p->cond_not_full);
        pthread_mutex_unlock(&p->mu);

        AnimaVal res = task.clos->fn(task.clos->upvals, 0, NULL);
        pthread_mutex_lock(&task.fut->mu);
        task.fut->fut_val = res;
        task.fut->fut_done = true;
        pthread_cond_broadcast(&task.fut->cond_not_empty);
        pthread_mutex_unlock(&task.fut->mu);
    }
    return NULL;
}

static AnimaVal conc_threadpool_new(int64_t workers, int64_t qcap) {
    if (workers <= 0) workers = 4;
    if (qcap <= 0) qcap = 16;
    AnimaHandle *h = calloc(1, sizeof(AnimaHandle));
    h->kind = HDL_THREADPOOL;
    pthread_mutex_init(&h->mu, NULL);
    pthread_cond_init(&h->cond_not_empty, NULL);
    pthread_cond_init(&h->cond_not_full, NULL);
    h->pool_cap = (size_t)qcap;
    h->pool_q = calloc(h->pool_cap, sizeof(PoolTask));
    h->pool_nworkers = (int)workers;
    h->pool_threads = calloc((size_t)workers, sizeof(pthread_t));
    for (int i = 0; i < workers; i++) pthread_create(&h->pool_threads[i], NULL, pool_worker, h);
    AnimaVal v = {0}; v.kind = VAL_HANDLE; v.u.hdl = h; return v;
}

static AnimaVal conc_pool_submit(AnimaVal pv, AnimaVal clos) {
    AnimaHandle *p = pv.u.hdl;
    AnimaHandle *fut = calloc(1, sizeof(AnimaHandle));
    fut->kind = HDL_FUTURE;
    pthread_mutex_init(&fut->mu, NULL);
    pthread_cond_init(&fut->cond_not_empty, NULL);
    pthread_mutex_lock(&p->mu);
    while (p->pool_count >= p->pool_cap && !p->closed) pthread_cond_wait(&p->cond_not_full, &p->mu);
    p->pool_q[p->pool_tail] = (PoolTask){ .clos = clos.u.clos, .fut = fut };
    p->pool_tail = (p->pool_tail + 1) % p->pool_cap;
    p->pool_count++;
    pthread_cond_signal(&p->cond_not_empty);
    pthread_mutex_unlock(&p->mu);
    AnimaVal v = {0}; v.kind = VAL_HANDLE; v.u.hdl = fut; return v;
}

static AnimaVal conc_channel_new(int64_t cap) {
    if (cap <= 0) cap = 8;
    AnimaHandle *h = calloc(1, sizeof(AnimaHandle));
    h->kind = HDL_CHANNEL;
    pthread_mutex_init(&h->mu, NULL);
    pthread_cond_init(&h->cond_not_empty, NULL);
    pthread_cond_init(&h->cond_not_full, NULL);
    h->chan_cap = (size_t)cap;
    h->chan_buf = calloc(h->chan_cap, sizeof(AnimaVal));
    AnimaVal v = {0}; v.kind = VAL_HANDLE; v.u.hdl = h; return v;
}

static AnimaVal conc_chan_send(AnimaVal cv, AnimaVal val) {
    AnimaHandle *c = cv.u.hdl;
    pthread_mutex_lock(&c->mu);
    while (c->chan_count >= c->chan_cap && !c->closed) pthread_cond_wait(&c->cond_not_full, &c->mu);
    if (c->closed) { pthread_mutex_unlock(&c->mu); return v_bool(false); }
    c->chan_buf[c->chan_tail] = val;
    c->chan_tail = (c->chan_tail + 1) % c->chan_cap;
    c->chan_count++;
    pthread_cond_signal(&c->cond_not_empty);
    pthread_mutex_unlock(&c->mu);
    return v_bool(true);
}

static AnimaVal conc_chan_recv(AnimaVal cv) {
    AnimaHandle *c = cv.u.hdl;
    pthread_mutex_lock(&c->mu);
    while (c->chan_count == 0 && !c->closed) pthread_cond_wait(&c->cond_not_empty, &c->mu);
    if (c->chan_count == 0 && c->closed) { pthread_mutex_unlock(&c->mu); return v_none(); }
    AnimaVal item = c->chan_buf[c->chan_head];
    c->chan_head = (c->chan_head + 1) % c->chan_cap;
    c->chan_count--;
    pthread_cond_signal(&c->cond_not_full);
    pthread_mutex_unlock(&c->mu);
    return v_some(item);
}

static AnimaVal conc_mutex_new(AnimaVal initv) {
    AnimaHandle *h = calloc(1, sizeof(AnimaHandle));
    h->kind = HDL_MUTEX;
    pthread_mutex_init(&h->mu, NULL);
    h->cell_val = initv;
    AnimaVal v = {0}; v.kind = VAL_HANDLE; v.u.hdl = h; return v;
}

static AnimaVal conc_sem_new(int64_t n) {
    AnimaHandle *h = calloc(1, sizeof(AnimaHandle));
    h->kind = HDL_SEMAPHORE;
    pthread_mutex_init(&h->mu, NULL);
    pthread_cond_init(&h->cond_not_empty, NULL);
    h->sem_count = (int)n;
    AnimaVal v = {0}; v.kind = VAL_HANDLE; v.u.hdl = h; return v;
}

static void hdl_sem_acquire(AnimaHandle *s) {
    pthread_mutex_lock(&s->mu);
    while (s->sem_count <= 0) pthread_cond_wait(&s->cond_not_empty, &s->mu);
    s->sem_count--;
    pthread_mutex_unlock(&s->mu);
}

static void hdl_sem_release(AnimaHandle *s) {
    pthread_mutex_lock(&s->mu);
    s->sem_count++;
    pthread_cond_signal(&s->cond_not_empty);
    pthread_mutex_unlock(&s->mu);
}

static void hdl_close(AnimaVal hv) {
    if (hv.kind != VAL_HANDLE || !hv.u.hdl) return;
    AnimaHandle *h = hv.u.hdl;
    if (h->closed) return;
    switch (h->kind) {
        case HDL_LISTENER:
        case HDL_STREAM:
            h->closed = true;
            if (h->fd >= 0) close(h->fd);
            break;
        case HDL_FILE:
            h->closed = true;
            if (h->fp) fclose(h->fp);
            break;
        case HDL_THREADPOOL:
            pthread_mutex_lock(&h->mu);
            h->closed = true;
            pthread_cond_broadcast(&h->cond_not_empty);
            pthread_cond_broadcast(&h->cond_not_full);
            pthread_mutex_unlock(&h->mu);
            for (int i = 0; i < h->pool_nworkers; i++) pthread_join(h->pool_threads[i], NULL);
            break;
        case HDL_CHANNEL:
            pthread_mutex_lock(&h->mu);
            h->closed = true;
            pthread_cond_broadcast(&h->cond_not_empty);
            pthread_cond_broadcast(&h->cond_not_full);
            pthread_mutex_unlock(&h->mu);
            break;
        default:
            h->closed = true;
            break;
    }
}

// ─── std.fs & std.cli & std.time ───
static AnimaVal fs_open(const char *path, const char *mode) {
    FILE *fp = fopen(path, (mode && strchr(mode, 'w')) ? "wb" : "rb");
    if (!fp) return v_err(strerror(errno));
    AnimaHandle *h = calloc(1, sizeof(AnimaHandle));
    h->kind = HDL_FILE; h->fp = fp;
    AnimaVal v = {0}; v.kind = VAL_HANDLE; v.u.hdl = h;
    return v_ok(v);
}

static AnimaVal fs_read_text(const char *path) {
    FILE *fp = fopen(path, "rb");
    if (!fp) return v_err(strerror(errno));
    fseek(fp, 0, SEEK_END);
    long sz = ftell(fp);
    fseek(fp, 0, SEEK_SET);
    char *buf = malloc((size_t)sz + 1);
    size_t nr = fread(buf, 1, (size_t)sz, fp);
    buf[nr] = '\0';
    fclose(fp);
    AnimaVal r = v_ok(v_str(buf));
    free(buf);
    return r;
}

static AnimaVal time_now_ms(void) {
    struct timespec ts;
    clock_gettime(CLOCK_REALTIME, &ts);
    return v_int((int64_t)ts.tv_sec * 1000 + ts.tv_nsec / 1000000);
}

// ─── std.json encode + minimal recursive JSON parser for schema decode ───
static void json_skip_ws(const char **p) {
    while (**p && isspace((unsigned char)**p)) (*p)++;
}

static char *json_parse_str(const char **p) {
    if (**p != '"') return NULL;
    (*p)++;
    size_t cap = 64, len = 0;
    char *out = malloc(cap);
    while (**p && **p != '"') {
        char ch = **p;
        if (ch == '\\' && (*p)[1]) {
            (*p)++;
            switch (**p) {
                case 'n': ch = '\n'; break;
                case 't': ch = '\t'; break;
                case 'r': ch = '\r'; break;
                default: ch = **p; break;
            }
        }
        if (len + 2 >= cap) { cap *= 2; out = realloc(out, cap); }
        out[len++] = ch;
        (*p)++;
    }
    if (**p == '"') (*p)++;
    out[len] = '\0';
    return out;
}

static AnimaVal json_parse_val(const char **p, bool *ok);

static AnimaVal json_parse_val(const char **p, bool *ok) {
    json_skip_ws(p);
    char ch = **p;
    if (ch == '"') {
        char *s = json_parse_str(p);
        AnimaVal v = v_str(s);
        free(s);
        return v;
    }
    if (strncmp(*p, "true", 4) == 0) { *p += 4; return v_bool(true); }
    if (strncmp(*p, "false", 5) == 0) { *p += 5; return v_bool(false); }
    if (strncmp(*p, "null", 4) == 0) { *p += 4; return v_none(); }
    if (ch == '-' || isdigit((unsigned char)ch)) {
        char *end = NULL;
        int64_t iv = strtoll(*p, &end, 10);
        if (end == *p) { *ok = false; return v_none(); }
        *p = end;
        return v_int(iv);
    }
    if (ch == '[') {
        (*p)++;
        AnimaVal list = v_list_new(0, NULL);
        json_skip_ws(p);
        if (**p == ']') { (*p)++; return list; }
        for (;;) {
            AnimaVal el = json_parse_val(p, ok);
            if (!*ok) return list;
            v_list_push(list, el);
            json_skip_ws(p);
            if (**p == ',') { (*p)++; continue; }
            if (**p == ']') { (*p)++; break; }
            *ok = false; break;
        }
        return list;
    }
    if (ch == '{') {
        (*p)++;
        AnimaVal m = v_map_new();
        json_skip_ws(p);
        if (**p == '}') { (*p)++; return m; }
        for (;;) {
            json_skip_ws(p);
            char *k = json_parse_str(p);
            if (!k) { *ok = false; return m; }
            json_skip_ws(p);
            if (**p != ':') { free(k); *ok = false; return m; }
            (*p)++;
            AnimaVal val = json_parse_val(p, ok);
            v_map_set(m, k, val);
            free(k);
            if (!*ok) return m;
            json_skip_ws(p);
            if (**p == ',') { (*p)++; continue; }
            if (**p == '}') { (*p)++; break; }
            *ok = false; break;
        }
        return m;
    }
    *ok = false;
    return v_none();
}

static AnimaVal json_encode(AnimaVal v) {
    if (v.kind == VAL_INT) { char b[64]; snprintf(b, sizeof(b), "%lld", (long long)v.u.i); return v_str(b); }
    if (v.kind == VAL_BOOL) return v_str(v.u.b ? "true" : "false");
    if (v.kind == VAL_STR) {
        size_t l = strlen(v.u.s);
        char *b = malloc(l*2 + 4);
        size_t j = 0;
        b[j++] = '"';
        for (size_t i = 0; i < l; i++) {
            if (v.u.s[i] == '"' || v.u.s[i] == '\\') b[j++] = '\\';
            b[j++] = v.u.s[i];
        }
        b[j++] = '"'; b[j] = '\0';
        AnimaVal r = v_str(b); free(b); return r;
    }
    if (v.kind == VAL_MAP && v.u.map) {
        AnimaVal acc = v_str("{");
        for (size_t i = 0; i < v.u.map->len; i++) {
            if (i > 0) acc = v_str_cat(acc, v_str(","));
            acc = v_str_cat(acc, json_encode(v_str(v.u.map->entries[i].key)));
            acc = v_str_cat(acc, v_str(":"));
            acc = v_str_cat(acc, json_encode(v.u.map->entries[i].val));
        }
        return v_str_cat(acc, v_str("}"));
    }
    if (v.kind == VAL_ENTITY && v.u.ent) {
        AnimaVal acc = v_str("{");
        for (size_t i = 0; i < v.u.ent->len; i++) {
            if (i > 0) acc = v_str_cat(acc, v_str(","));
            acc = v_str_cat(acc, json_encode(v_str(v.u.ent->fields[i].key)));
            acc = v_str_cat(acc, v_str(":"));
            acc = v_str_cat(acc, json_encode(v.u.ent->fields[i].val));
        }
        return v_str_cat(acc, v_str("}"));
    }
    if (v.kind == VAL_LIST && v.u.list) {
        AnimaVal acc = v_str("[");
        for (size_t i = 0; i < v.u.list->len; i++) {
            if (i > 0) acc = v_str_cat(acc, v_str(","));
            acc = v_str_cat(acc, json_encode(v.u.list->items[i]));
        }
        return v_str_cat(acc, v_str("]"));
    }
    return v_str("null");
}
`
