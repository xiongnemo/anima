package native

// runtimeHeader contains the zero-external-dependency C11 runtime (POSIX + pthreads + OpenSSL 3.0)
// emitted by `anima build` into generated native executables.
const runtimeHeader = `#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include <strings.h>
#include <ctype.h>
#include <time.h>
#include <errno.h>
#include <signal.h>
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
    char *path; // of a file, for its error messages
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

// Division as on the VM. A divisor of 0 stops the program with the VM's
// message instead of a signal: no verified program divides by zero, this is
// for the one the kernel got wrong. INT64_MIN / -1 wraps, as in Go.
static AnimaVal v_div(AnimaVal l, AnimaVal r, int line) {
    if (r.u.i == 0) {
        fflush(stdout);
        fprintf(stderr, "runtime error: runtime division by zero at line %d\n", line);
        exit(1);
    }
    if (r.u.i == -1) return v_int((int64_t)(0 - (uint64_t)l.u.i));
    return v_int(l.u.i / r.u.i);
}

static AnimaVal v_mod(AnimaVal l, AnimaVal r, int line) {
    if (r.u.i == 0) {
        fflush(stdout);
        fprintf(stderr, "runtime error: runtime modulo by zero at line %d\n", line);
        exit(1);
    }
    if (r.u.i == -1) return v_int(0);
    return v_int(l.u.i % r.u.i);
}
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
    if (c.kind == VAL_STR && c.u.s && i.u.i >= 0 && (size_t)i.u.i < strlen(c.u.s)) {
        // One byte of the string as a character, as the VM gives it.
        unsigned char b = (unsigned char)c.u.s[i.u.i];
        char out[3] = {0};
        if (b < 0x80) { out[0] = (char)b; }
        else { out[0] = (char)(0xC0 | (b >> 6)); out[1] = (char)(0x80 | (b & 0x3F)); }
        return v_str(out);
    }
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

// Equality (==), the same as Value.Equals in the VM: lists, maps and variants are
// equal when what they hold is equal, an entity is equal to itself only.
// EqOpen is the containers being compared: a pair met again while it is
// being compared is inside a cycle and holds nothing new to compare.
typedef struct EqOpen { const void *a; const void *b; const struct EqOpen *up; } EqOpen;

static bool v_eq_in(AnimaVal a, AnimaVal b, const EqOpen *up) {
    if (a.kind != b.kind) return false;
    EqOpen here = {NULL, NULL, up};
    switch (a.kind) {
        case VAL_VOID: case VAL_NONE: return true;
        case VAL_INT: return a.u.i == b.u.i;
        case VAL_BOOL: return a.u.b == b.u.b;
        case VAL_STR: return strcmp(a.u.s ? a.u.s : "", b.u.s ? b.u.s : "") == 0;
        case VAL_ENTITY: return a.u.ent == b.u.ent;
        case VAL_CLOSURE: return a.u.clos == b.u.clos;
        case VAL_HANDLE: return a.u.hdl == b.u.hdl;
        case VAL_LIST: here.a = a.u.list; here.b = b.u.list; break;
        case VAL_MAP: here.a = a.u.map; here.b = b.u.map; break;
        case VAL_VARIANT: here.a = a.u.var; here.b = b.u.var; break;
        default: return false;
    }
    if (here.a == here.b) return true;
    for (const EqOpen *o = up; o; o = o->up) {
        if (o->a == here.a && o->b == here.b) return true;
    }
    if (a.kind == VAL_LIST) {
        size_t na = a.u.list ? a.u.list->len : 0, nb = b.u.list ? b.u.list->len : 0;
        if (na != nb) return false;
        for (size_t i = 0; i < na; i++) {
            if (!v_eq_in(a.u.list->items[i], b.u.list->items[i], &here)) return false;
        }
        return true;
    }
    if (a.kind == VAL_MAP) {
        size_t na = a.u.map ? a.u.map->len : 0, nb = b.u.map ? b.u.map->len : 0;
        if (na != nb) return false;
        for (size_t i = 0; i < na; i++) {
            size_t j = 0;
            while (j < nb && strcmp(a.u.map->entries[i].key, b.u.map->entries[j].key) != 0) j++;
            if (j == nb || !v_eq_in(a.u.map->entries[i].val, b.u.map->entries[j].val, &here)) return false;
        }
        return true;
    }
    if (!a.u.var || !b.u.var) return false;
    if (strcmp(a.u.var->name, b.u.var->name) != 0 || a.u.var->len != b.u.var->len) return false;
    for (size_t i = 0; i < a.u.var->len; i++) {
        if (!v_eq_in(a.u.var->fields[i], b.u.var->fields[i], &here)) return false;
    }
    return true;
}

static bool v_eq(AnimaVal a, AnimaVal b) { return v_eq_in(a, b, NULL); }

// The order of two values, as Value.order in the VM: strings byte by byte,
// anything else as integers.
static int v_order(AnimaVal a, AnimaVal b) {
    if (a.kind == VAL_STR && b.kind == VAL_STR) return strcmp(a.u.s ? a.u.s : "", b.u.s ? b.u.s : "");
    return a.u.i < b.u.i ? -1 : (a.u.i > b.u.i ? 1 : 0);
}

static char *v_to_cstr(AnimaVal v);

// a in b: an element of a list, a key of a map, a part of a string.
static bool v_in(AnimaVal a, AnimaVal b) {
    if (b.kind == VAL_LIST && b.u.list) {
        for (size_t i = 0; i < b.u.list->len; i++) {
            if (v_eq(a, b.u.list->items[i])) return true;
        }
        return false;
    }
    if (b.kind == VAL_MAP && b.u.map) {
        char *k = v_to_cstr(a);
        bool found = false;
        for (size_t i = 0; i < b.u.map->len && !found; i++) found = strcmp(b.u.map->entries[i].key, k) == 0;
        free(k);
        return found;
    }
    if (b.kind == VAL_STR && a.kind == VAL_STR) return strstr(b.u.s ? b.u.s : "", a.u.s ? a.u.s : "") != NULL;
    return false;
}

// A value as text, the same as Value.String in the VM: map entries and
// entity fields in the order of their keys.
typedef struct { char *p; size_t len; size_t cap; } AnimaBuf;

static void buf_put(AnimaBuf *b, const char *s) {
    size_t n = strlen(s);
    if (b->len + n + 1 > b->cap) {
        b->cap = (b->len + n + 1) * 2;
        b->p = realloc(b->p, b->cap);
    }
    memcpy(b->p + b->len, s, n + 1);
    b->len += n;
}

static void buf_putn(AnimaBuf *b, const char *s, size_t n) {
    if (b->len + n + 1 > b->cap) {
        b->cap = (b->len + n + 1) * 2;
        b->p = realloc(b->p, b->cap);
    }
    memcpy(b->p + b->len, s, n);
    b->len += n;
    b->p[b->len] = 0;
}

static void v_fmt_key(AnimaBuf *b, const char *k) {
    char esc[8];
    buf_put(b, "\"");
    for (const unsigned char *c = (const unsigned char *)k; *c; c++) {
        if (*c == '"' || *c == '\\') { esc[0] = '\\'; esc[1] = (char)*c; esc[2] = 0; }
        else if (*c == '\n') strcpy(esc, "\\n");
        else if (*c == '\t') strcpy(esc, "\\t");
        else if (*c == '\r') strcpy(esc, "\\r");
        else if (*c < 0x20 || *c == 0x7f) snprintf(esc, sizeof(esc), "\\x%02x", *c);
        else { esc[0] = (char)*c; esc[1] = 0; }
        buf_put(b, esc);
    }
    buf_put(b, "\"");
}

static int v_entry_cmp(const void *a, const void *b) {
    return strcmp((*(AnimaMapEntry *const *)a)->key, (*(AnimaMapEntry *const *)b)->key);
}

static void v_fmt(AnimaBuf *b, AnimaVal v);

// The entries of a map or the fields of an entity, sorted by key.
static void v_fmt_entries(AnimaBuf *b, AnimaMapEntry *entries, size_t len, bool quoted) {
    AnimaMapEntry **order = malloc((len ? len : 1) * sizeof(*order));
    for (size_t i = 0; i < len; i++) order[i] = &entries[i];
    qsort(order, len, sizeof(*order), v_entry_cmp);
    for (size_t i = 0; i < len; i++) {
        if (i > 0) buf_put(b, ", ");
        if (quoted) { v_fmt_key(b, order[i]->key); buf_put(b, ": "); }
        else { buf_put(b, order[i]->key); buf_put(b, "="); }
        v_fmt(b, order[i]->val);
    }
    free(order);
}

static void v_fmt(AnimaBuf *b, AnimaVal v) {
    char num[32];
    switch (v.kind) {
        case VAL_VOID: buf_put(b, "()"); break;
        case VAL_NONE: buf_put(b, "None"); break;
        case VAL_INT: snprintf(num, sizeof(num), "%lld", (long long)v.u.i); buf_put(b, num); break;
        case VAL_BOOL: buf_put(b, v.u.b ? "True" : "False"); break;
        case VAL_STR: buf_put(b, v.u.s ? v.u.s : ""); break;
        case VAL_LIST:
            buf_put(b, "[");
            for (size_t i = 0; v.u.list && i < v.u.list->len; i++) {
                if (i > 0) buf_put(b, ", ");
                v_fmt(b, v.u.list->items[i]);
            }
            buf_put(b, "]");
            break;
        case VAL_MAP:
            buf_put(b, "{");
            if (v.u.map) v_fmt_entries(b, v.u.map->entries, v.u.map->len, true);
            buf_put(b, "}");
            break;
        case VAL_ENTITY:
            buf_put(b, v.u.ent && v.u.ent->type_name ? v.u.ent->type_name : "");
            buf_put(b, "(");
            if (v.u.ent) v_fmt_entries(b, v.u.ent->fields, v.u.ent->len, false);
            buf_put(b, ")");
            break;
        case VAL_VARIANT:
            if (!v.u.var) { buf_put(b, "None"); break; }
            buf_put(b, v.u.var->name);
            if (v.u.var->len == 0) break;
            buf_put(b, "(");
            for (size_t i = 0; i < v.u.var->len; i++) {
                if (i > 0) buf_put(b, ", ");
                v_fmt(b, v.u.var->fields[i]);
            }
            buf_put(b, ")");
            break;
        default: buf_put(b, "<val>"); break;
    }
}

static char *v_to_cstr(AnimaVal v) {
    AnimaBuf b = {0};
    buf_put(&b, "");
    v_fmt(&b, v);
    return b.p;
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

// SIGPIPE is ignored (see main), so that a write to a socket whose peer has
// gone is an Err and not the end of the program. Standard output is the
// exception, as in Go: when nobody reads it any more the program ends by
// that signal.
static void print_line(const char *s) {
    // A line longer than the buffer of stdout is written by printf itself:
    // its failure counts as much as that of the flush.
    if ((printf("%s\n", s) < 0 || fflush(stdout) != 0) && errno == EPIPE) {
        signal(SIGPIPE, SIG_DFL);
        raise(SIGPIPE);
    }
}

static AnimaVal anima_print(AnimaVal v) {
    char *s = v_to_cstr(v);
    print_line(s);
    free(s);
    return v_void();
}

// print(a, b, ...) writes its arguments on one line with a space between.
// The line goes out in one call, so that the lines of two threads do not mix.
static AnimaVal anima_print_n(int argc, AnimaVal *argv) {
    AnimaBuf b = {0};
    buf_put(&b, "");
    for (int i = 0; i < argc; i++) {
        if (i > 0) buf_put(&b, " ");
        v_fmt(&b, argv[i]);
    }
    print_line(b.p);
    free(b.p);
    return v_void();
}

// ─── std.fp combinators ───

static AnimaVal fp_any(AnimaVal listv, AnimaVal fn) {
    if (listv.kind == VAL_LIST && listv.u.list && fn.kind == VAL_CLOSURE) {
        for (size_t i = 0; i < listv.u.list->len; i++) {
            AnimaVal arg = listv.u.list->items[i];
            if (v_truthy(v_call_clos(fn, 1, &arg))) return v_bool(true);
        }
    }
    return v_bool(false);
}

static AnimaVal fp_all(AnimaVal listv, AnimaVal fn) {
    if (listv.kind == VAL_LIST && listv.u.list && fn.kind == VAL_CLOSURE) {
        for (size_t i = 0; i < listv.u.list->len; i++) {
            AnimaVal arg = listv.u.list->items[i];
            if (!v_truthy(v_call_clos(fn, 1, &arg))) return v_bool(false);
        }
    }
    return v_bool(true);
}

static AnimaVal fp_find(AnimaVal listv, AnimaVal fn) {
    if (listv.kind == VAL_LIST && listv.u.list && fn.kind == VAL_CLOSURE) {
        for (size_t i = 0; i < listv.u.list->len; i++) {
            AnimaVal arg = listv.u.list->items[i];
            if (v_truthy(v_call_clos(fn, 1, &arg))) return v_some(arg);
        }
    }
    return v_none();
}

// The elements of a list from index lo up to hi, in a list of their own.
static AnimaVal fp_slice(AnimaVal listv, int64_t lo, int64_t hi) {
    AnimaVal out = v_list_new(0, NULL);
    if (listv.kind != VAL_LIST || !listv.u.list) return out;
    int64_t len = (int64_t)listv.u.list->len;
    if (lo < 0) lo = 0;
    if (hi > len) hi = len;
    for (int64_t i = lo; i < hi; i++) v_list_push(out, listv.u.list->items[i]);
    return out;
}

static AnimaVal fp_take(AnimaVal listv, AnimaVal n) { return fp_slice(listv, 0, n.u.i); }

static AnimaVal fp_drop(AnimaVal listv, AnimaVal n) { return fp_slice(listv, n.u.i, INT64_MAX); }
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

// from_hex of anything but pairs of hex digits is an empty view, as on the VM.
static AnimaVal bytes_from_hex(const char *hx) {
    size_t len = strlen(hx);
    size_t n = len / 2;
    if (len % 2 != 0) n = 0;
    for (size_t i = 0; i < len && n > 0; i++) {
        if (!isxdigit((unsigned char)hx[i])) n = 0;
    }
    AnimaHandle *h = calloc(1, sizeof(AnimaHandle));
    h->kind = HDL_BYTEVIEW;
    h->bytes_len = n;
    h->bytes = calloc(n + 1, 1);
    for (size_t i = 0; i < n; i++) {
        h->bytes[i] = (uint8_t)((hex_nibble(hx[2*i]) << 4) | hex_nibble(hx[2*i+1]));
    }
    AnimaVal v = {0}; v.kind = VAL_HANDLE; v.u.hdl = h; return v;
}

// slice(lo, hi): the bytes lo..hi-1 of the view, the ends brought inside
// it. The bytes are shared: a view is never written.
static AnimaVal bytes_slice(AnimaVal hv, int64_t lo, int64_t hi) {
    AnimaHandle *h = calloc(1, sizeof(AnimaHandle));
    h->kind = HDL_BYTEVIEW;
    AnimaVal v = {0}; v.kind = VAL_HANDLE; v.u.hdl = h;
    if (hv.kind != VAL_HANDLE || !hv.u.hdl || hv.u.hdl->kind != HDL_BYTEVIEW) return v;
    int64_t n = (int64_t)hv.u.hdl->bytes_len;
    if (hi > n) hi = n;
    if (hi < 0) hi = 0;
    if (lo < 0) lo = 0;
    if (lo > hi) lo = hi;
    h->bytes = hv.u.hdl->bytes + lo;
    h->bytes_len = (size_t)(hi - lo);
    return v;
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
static int64_t mono_ms(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (int64_t)ts.tv_sec * 1000 + ts.tv_nsec / 1000000;
}

// How the head of an answer says its body ends.
enum { HTTP_UNTIL_CLOSE, HTTP_LENGTH, HTTP_CHUNKED, HTTP_NO_BODY };
typedef struct {
    size_t head_len; int status; int mode; size_t want;
    size_t chunk_at;  // in a chunked body: where the first chunk not all there yet starts
} HttpHead;

// Reads the head of the answer in raw, once all of it is there. Chunked
// wins over a Content-Length, and 204 and 304 have no body, as in Go.
static bool http_head(const char *raw, HttpHead *h) {
    const char *head_end = strstr(raw, "\r\n\r\n");
    if (!head_end) return false;
    h->head_len = (size_t)(head_end - raw) + 4;
    const char *sp = strchr(raw, ' ');
    h->status = sp && sp < head_end ? atoi(sp + 1) : 200;
    h->mode = HTTP_UNTIL_CLOSE;
    h->want = 0;
    h->chunk_at = 0;
    bool chunked = false;
    for (const char *line = strstr(raw, "\r\n"); line && line < head_end; line = strstr(line + 2, "\r\n")) {
        const char *f = line + 2;
        const char *eol = strstr(f, "\r\n");
        if (strncasecmp(f, "Content-Length:", 15) == 0) {
            long long want = atoll(f + 15);
            if (want >= 0) { h->mode = HTTP_LENGTH; h->want = (size_t)want; }
        } else if (strncasecmp(f, "Transfer-Encoding:", 18) == 0) {
            for (const char *p = f + 18; p + 7 <= eol; p++) {
                if (strncasecmp(p, "chunked", 7) == 0) chunked = true;
            }
        }
    }
    if (chunked) h->mode = HTTP_CHUNKED;
    if (h->status == 204 || h->status == 304) h->mode = HTTP_NO_BODY;
    return true;
}

// The chunks in p[0..n): 1 when they are all there, up to the last line of
// the trailer; 0 when more is to come; -1 for a length that is not hex, -2
// for a chunk that does not end in CRLF and -3 for a length of more than 16
// digits, the most Go takes. The bytes of the chunks, without
// their framing, are added to out when one is given. With at, reading
// starts at *at and *at is left at the first chunk that is not all there:
// a body in many chunks is then read once, not once for each read of the
// socket.
static int http_chunks(const char *p, size_t n, AnimaBuf *out, size_t *at) {
    size_t i = at ? *at : 0;
    for (;;) {
        if (at) *at = i;
        size_t j = i, size = 0;
        int digits = 0;
        while (j < n && isxdigit((unsigned char)p[j])) {
            int c = tolower((unsigned char)p[j]);
            if (++digits > 16) return -3;
            size = size * 16 + (size_t)(c <= '9' ? c - '0' : c - 'a' + 10);
            j++;
        }
        if (j >= n) return 0;
        if (digits == 0 || (p[j] != '\r' && p[j] != ';' && p[j] != ' ' && p[j] != '\t')) return -1;
        while (j + 1 < n && !(p[j] == '\r' && p[j + 1] == '\n')) j++;
        if (j + 1 >= n) return 0;
        i = j + 2;
        if (size == 0) {
            // The trailer: lines up to an empty one.
            for (;;) {
                j = i;
                while (j + 1 < n && !(p[j] == '\r' && p[j + 1] == '\n')) j++;
                if (j + 1 >= n) return 0;
                if (j == i) return 1;
                i = j + 2;
            }
        }
        if (size > n - i || n - i - size < 2) return 0;
        if (p[i + size] != '\r' || p[i + size + 1] != '\n') return -2;
        if (out) buf_putn(out, p + i, size);
        i += size + 2;
    }
}

// Whether the answer in raw[0..total) needs no more reading.
static bool http_complete(const char *raw, size_t total, HttpHead *h) {
    switch (h->mode) {
    case HTTP_NO_BODY: return true;
    case HTTP_LENGTH: return total - h->head_len >= h->want;
    case HTTP_CHUNKED: return http_chunks(raw + h->head_len, total - h->head_len, NULL, &h->chunk_at) != 0;
    }
    return false;
}

// A request that fails reads as on the VM: Get "url": why.
static AnimaVal http_err(const char *method, const char *url, const char *why, const char *more) {
    AnimaBuf b = {0};
    buf_put(&b, method[0] == 'P' ? "Post \"" : "Get \"");
    buf_put(&b, url); buf_put(&b, "\": "); buf_put(&b, why);
    if (more) {
        size_t at = b.len;
        buf_put(&b, more);
        if (b.len > at) b.p[at] = (char)tolower((unsigned char)b.p[at]);
    }
    AnimaVal r = v_err(b.p);
    free(b.p);
    return r;
}

// Whether a TLS read or write gave up because the socket's time ran out.
static bool http_tls_timed_out(SSL *ssl, int n) {
    int e = SSL_get_error(ssl, n);
    return e == SSL_ERROR_WANT_READ || e == SSL_ERROR_WANT_WRITE ||
        (e == SSL_ERROR_SYSCALL && (errno == EAGAIN || errno == EWOULDBLOCK));
}

static AnimaVal http_do(const char *method, const char *url, const char *body, int64_t timeout_ms) {
    // One time limit for the whole request, as http.Client.Timeout is.
    int64_t deadline = mono_ms() + (timeout_ms > 0 ? timeout_ms : 5000);
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
    if (getaddrinfo(host, port, &hints, &res) != 0 || !res) {
        char why[320];
        snprintf(why, sizeof(why), "dial tcp: lookup %s: no such host", host);
        return http_err(method, url, why, NULL);
    }
    int fd = socket(res->ai_family, res->ai_socktype, res->ai_protocol);
    if (fd < 0) { int e = errno; freeaddrinfo(res); return http_err(method, url, "dial tcp: socket: ", strerror(e)); }
    set_fd_timeout(fd, timeout_ms > 0 ? timeout_ms : 5000);
    if (connect(fd, res->ai_addr, res->ai_addrlen) < 0) {
        int e = errno;
        char ip[INET6_ADDRSTRLEN] = {0}, why[400];
        if (res->ai_family == AF_INET) inet_ntop(AF_INET, &((struct sockaddr_in *)res->ai_addr)->sin_addr, ip, sizeof(ip));
        else if (res->ai_family == AF_INET6) inet_ntop(AF_INET6, &((struct sockaddr_in6 *)res->ai_addr)->sin6_addr, ip, sizeof(ip));
        snprintf(why, sizeof(why), res->ai_family == AF_INET6 ? "dial tcp [%s]:%s: connect: " : "dial tcp %s:%s: connect: ", ip, port);
        close(fd); freeaddrinfo(res);
        return http_err(method, url, why, strerror(e));
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
            return http_err(method, url, "tls handshake failed", NULL);
        }
    }

    // The request is as long as its path and body make it.
    AnimaBuf req = {0};
    buf_put(&req, method); buf_put(&req, " "); buf_put(&req, path);
    buf_put(&req, " HTTP/1.1\r\nHost: "); buf_put(&req, hostport);
    buf_put(&req, "\r\nConnection: close\r\n");
    if (body && body[0] != '\0') {
        char len_line[64];
        snprintf(len_line, sizeof(len_line), "Content-Length: %zu\r\n", strlen(body));
        buf_put(&req, len_line);
        buf_put(&req, "Content-Type: application/json\r\n\r\n");
        buf_put(&req, body);
    } else {
        buf_put(&req, "\r\n");
    }
    bool timed_out = false;
    size_t sent = 0;
    while (sent < req.len) {
        int64_t left = deadline - mono_ms();
        if (left <= 0) { timed_out = true; break; }
        set_fd_timeout(fd, left);
        size_t part = req.len - sent > 65536 ? 65536 : req.len - sent;
        ssize_t n = ssl ? SSL_write(ssl, req.p + sent, (int)part) : send(fd, req.p + sent, part, MSG_NOSIGNAL);
        if (n < 0 && !ssl && errno == EINTR) continue;
        if (n <= 0) {
            // A server may answer and close before it has read everything:
            // what it said is read below.
            timed_out = ssl ? http_tls_timed_out(ssl, (int)n) : (errno == EAGAIN || errno == EWOULDBLOCK);
            break;
        }
        sent += (size_t)n;
    }
    free(req.p);

    size_t cap = 8192, total = 0;
    char *raw = malloc(cap);
    raw[0] = '\0';
    HttpHead head = {0};
    bool have_head = false;
    while (!timed_out) {
        // Room for one more read and the terminator after it.
        if (total + 2048 + 1 > cap) { cap *= 2; raw = realloc(raw, cap); }
        int64_t left = deadline - mono_ms();
        if (left <= 0) { timed_out = true; break; }
        set_fd_timeout(fd, left);
        ssize_t n = ssl ? SSL_read(ssl, raw + total, 2048) : recv(fd, raw + total, 2048, 0);
        if (n < 0 && !ssl && errno == EINTR) continue;
        if (n <= 0) {
            if (ssl) timed_out = n < 0 && http_tls_timed_out(ssl, (int)n);
            else timed_out = n < 0 && (errno == EAGAIN || errno == EWOULDBLOCK);
            break;
        }
        total += (size_t)n;
        raw[total] = '\0';
        // An answer that says where it ends is read no further: the server
        // may keep the connection open after it.
        if (!have_head) have_head = http_head(raw, &head);
        if (have_head && http_complete(raw, total, &head)) break;
    }
    if (ssl) { SSL_shutdown(ssl); SSL_free(ssl); SSL_CTX_free(ctx); }
    close(fd);

    // No answer is an error, as on the VM: not a response with status 200.
    // What goes wrong once the head is read is the error of reading the
    // body, which the VM gives without the request in front.
    if (timed_out) {
        free(raw);
        if (have_head) return v_err("context deadline exceeded (Client.Timeout or context cancellation while reading body)");
        return http_err(method, url, "context deadline exceeded (Client.Timeout exceeded while awaiting headers)", NULL);
    }
    if (total == 0) { free(raw); return http_err(method, url, "EOF", NULL); }
    if (strncmp(raw, "HTTP/", 5) != 0) { free(raw); return http_err(method, url, "malformed HTTP response", NULL); }
    if (!have_head) { free(raw); return http_err(method, url, "unexpected EOF", NULL); }

    const char *rbody = raw + head.head_len;
    AnimaBuf dechunked = {0};
    const char *bad = NULL;
    switch (head.mode) {
    case HTTP_NO_BODY:
        rbody = "";
        break;
    case HTTP_LENGTH:
        if (total - head.head_len < head.want) bad = "unexpected EOF";
        else raw[head.head_len + head.want] = '\0';
        break;
    case HTTP_CHUNKED: {
        buf_put(&dechunked, "");
        int r = http_chunks(rbody, total - head.head_len, &dechunked, NULL);
        if (r == 0) bad = "unexpected EOF";
        else if (r == -1) bad = "invalid byte in chunk length";
        else if (r == -2) bad = "malformed chunked encoding";
        else if (r == -3) bad = "http chunk length too large";
        else { dechunked.p[dechunked.len] = '\0'; rbody = dechunked.p; }
        break;
    }
    }
    if (bad) { free(raw); free(dechunked.p); return v_err(bad); }
    AnimaVal ent = v_entity_new("HttpResponse");
    v_entity_set(ent, "status", v_int(head.status));
    v_entity_set(ent, "body", v_str(rbody));
    v_entity_set(ent, "ok", v_bool(head.status >= 200 && head.status < 300));
    free(raw);
    free(dechunked.p);
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

// with_lock(f): the mutex holds f(what it held), set under the lock.
static void conc_mutex_with_lock(AnimaVal hv, AnimaVal fn) {
    if (hv.kind != VAL_HANDLE || !hv.u.hdl || hv.u.hdl->kind != HDL_MUTEX) return;
    AnimaHandle *h = hv.u.hdl;
    pthread_mutex_lock(&h->mu);
    AnimaVal held = h->cell_val;
    h->cell_val = v_call_clos(fn, 1, &held);
    pthread_mutex_unlock(&h->mu);
}

// parallel_map(xs, f): f of every element, each on a thread of its own,
// in the order of xs.
typedef struct { AnimaVal fn; AnimaVal arg; AnimaVal out; } ParMapJob;

static void *conc_parmap_run(void *p) {
    ParMapJob *j = p;
    j->out = v_call_clos(j->fn, 1, &j->arg);
    return NULL;
}

static AnimaVal conc_parallel_map(AnimaVal listv, AnimaVal fn) {
    AnimaVal out = v_list_new(0, NULL);
    if (listv.kind != VAL_LIST || !listv.u.list) return out;
    size_t n = listv.u.list->len;
    if (n == 0) return out;
    ParMapJob *jobs = calloc(n, sizeof(ParMapJob));
    pthread_t *ths = calloc(n, sizeof(pthread_t));
    for (size_t i = 0; i < n; i++) {
        jobs[i].fn = fn;
        jobs[i].arg = listv.u.list->items[i];
        int rc = pthread_create(&ths[i], NULL, conc_parmap_run, &jobs[i]);
        if (rc != 0) {
            // The calls run beside each other or not at all: one of them may
            // wait for what another gives, so none can be run here in turn.
            fprintf(stderr, "runtime error: parallel_map: cannot start a thread: %s\n", strerror(rc));
            exit(1);
        }
    }
    for (size_t i = 0; i < n; i++) {
        pthread_join(ths[i], NULL);
        v_list_push(out, jobs[i].out);
    }
    free(jobs); free(ths);
    return out;
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
            if (h->fd >= 0) close(h->fd);
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
// An error of the file system reads as on the VM: "open /p: no such file
// or directory".
static AnimaVal fs_err(const char *op, const char *path, int e) {
    AnimaBuf b = {0};
    buf_put(&b, op); buf_put(&b, " "); buf_put(&b, path); buf_put(&b, ": ");
    size_t at = b.len;
    buf_put(&b, strerror(e));
    if (b.len > at) b.p[at] = (char)tolower((unsigned char)b.p[at]);
    AnimaVal r = v_err(b.p);
    free(b.p);
    return r;
}

// "w" creates or empties the file and may read what it wrote; anything
// else opens it to read.
static AnimaVal fs_open(const char *path, const char *mode) {
    int fd = (mode && strchr(mode, 'w')) ? open(path, O_RDWR | O_CREAT | O_TRUNC | O_CLOEXEC, 0666)
                                         : open(path, O_RDONLY | O_CLOEXEC);
    if (fd < 0) return fs_err("open", path, errno);
    AnimaHandle *h = calloc(1, sizeof(AnimaHandle));
    h->kind = HDL_FILE; h->fd = fd; h->path = strdup(path);
    AnimaVal v = {0}; v.kind = VAL_HANDLE; v.u.hdl = h;
    return v_ok(v);
}

// What is left to read of fd, as Ok(str).
static AnimaVal fs_read_rest(int fd, const char *path) {
    AnimaBuf b = {0};
    char chunk[4096];
    for (;;) {
        ssize_t n = read(fd, chunk, sizeof(chunk));
        if (n < 0 && errno == EINTR) continue;
        if (n < 0) { int e = errno; free(b.p); return fs_err("read", path, e); }
        if (n == 0) break;
        buf_putn(&b, chunk, (size_t)n);
    }
    AnimaVal r = v_ok(v_str(b.p ? b.p : ""));
    free(b.p);
    return r;
}

static bool fs_write_all(int fd, const char *text, size_t len) {
    size_t done = 0;
    while (done < len) {
        ssize_t n = write(fd, text + done, len - done);
        if (n < 0 && errno == EINTR) continue;
        if (n < 0) return false;
        done += (size_t)n;
    }
    return true;
}

static AnimaVal fs_read_text(const char *path) {
    int fd = open(path, O_RDONLY | O_CLOEXEC);
    if (fd < 0) return fs_err("open", path, errno);
    AnimaVal r = fs_read_rest(fd, path);
    close(fd);
    return r;
}

static AnimaVal fs_file_read_text(AnimaVal hv) {
    AnimaHandle *h = hv.u.hdl;
    if (hv.kind != VAL_HANDLE || !h || h->kind != HDL_FILE) return v_err("not a file");
    if (h->closed) return fs_err("read", h->path, EBADF);
    return fs_read_rest(h->fd, h->path);
}

static AnimaVal fs_file_write_text(AnimaVal hv, const char *text) {
    AnimaHandle *h = hv.u.hdl;
    if (hv.kind != VAL_HANDLE || !h || h->kind != HDL_FILE) return v_err("not a file");
    if (h->closed) return fs_err("write", h->path, EBADF);
    size_t len = strlen(text);
    if (!fs_write_all(h->fd, text, len)) return fs_err("write", h->path, errno);
    return v_ok(v_int((int64_t)len));
}

// The text goes to a new file beside path, which then takes its name: a
// reader sees the old text or the new, never a part of it.
static AnimaVal fs_write_atomic(const char *path, const char *text) {
    const char *slash = strrchr(path, '/');
    AnimaBuf t = {0};
    if (!slash) buf_put(&t, ".");
    else if (slash == path) buf_put(&t, "");
    else buf_putn(&t, path, (size_t)(slash - path));
    buf_put(&t, "/.anima-tmp-XXXXXX");
    int fd = mkstemp(t.p);
    if (fd < 0) { AnimaVal r = fs_err("open", t.p, errno); free(t.p); return r; }
    size_t len = strlen(text);
    bool ok = fs_write_all(fd, text, len);
    if (close(fd) != 0) ok = false;
    if (!ok) { unlink(t.p); free(t.p); return v_err("write failed"); }
    if (rename(t.p, path) != 0) {
        int e = errno;
        unlink(t.p);
        AnimaBuf m = {0};
        buf_put(&m, "rename "); buf_put(&m, t.p); buf_put(&m, " "); buf_put(&m, path); buf_put(&m, ": ");
        size_t at = m.len;
        buf_put(&m, strerror(e));
        if (m.len > at) m.p[at] = (char)tolower((unsigned char)m.p[at]);
        AnimaVal r = v_err(m.p);
        free(m.p); free(t.p);
        return r;
    }
    free(t.p);
    return v_ok(v_int((int64_t)len));
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
