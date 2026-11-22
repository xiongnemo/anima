package native

// runtimeHeader contains the zero-external-dependency C11 runtime (POSIX + pthreads + OpenSSL 3.0)
// emitted by `anima build` into generated native executables.
const runtimeHeader = `#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdarg.h>
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
#include <poll.h>
#include <openssl/ssl.h>
#include <openssl/x509v3.h>
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

// A list, map, entity or variant being written, and those it is inside of.
// One met again inside itself is written "...": they are references, so one
// can hold itself, and its text would have no end. The VM writes the same.
typedef struct BoxOpen { const void *box; const struct BoxOpen *up; } BoxOpen;

static const void *v_box(AnimaVal v) {
    switch (v.kind) {
        case VAL_LIST: return v.u.list;
        case VAL_MAP: return v.u.map;
        case VAL_ENTITY: return v.u.ent;
        case VAL_VARIANT: return v.u.var;
        default: return NULL;
    }
}

static bool box_open(const void *box, const BoxOpen *up) {
    for (; box && up; up = up->up) if (up->box == box) return true;
    return false;
}

static void v_fmt_in(AnimaBuf *b, AnimaVal v, const BoxOpen *up);
static void v_fmt(AnimaBuf *b, AnimaVal v) { v_fmt_in(b, v, NULL); }

// The entries of a map or the fields of an entity, sorted by key.
static void v_fmt_entries(AnimaBuf *b, AnimaMapEntry *entries, size_t len, bool quoted, const BoxOpen *up) {
    AnimaMapEntry **order = malloc((len ? len : 1) * sizeof(*order));
    for (size_t i = 0; i < len; i++) order[i] = &entries[i];
    qsort(order, len, sizeof(*order), v_entry_cmp);
    for (size_t i = 0; i < len; i++) {
        if (i > 0) buf_put(b, ", ");
        if (quoted) { v_fmt_key(b, order[i]->key); buf_put(b, ": "); }
        else { buf_put(b, order[i]->key); buf_put(b, "="); }
        v_fmt_in(b, order[i]->val, up);
    }
    free(order);
}

static void v_fmt_in(AnimaBuf *b, AnimaVal v, const BoxOpen *up) {
    char num[32];
    BoxOpen here = { v_box(v), up };
    if (box_open(here.box, up)) { buf_put(b, "..."); return; }
    up = &here;
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
                v_fmt_in(b, v.u.list->items[i], up);
            }
            buf_put(b, "]");
            break;
        case VAL_MAP:
            buf_put(b, "{");
            if (v.u.map) v_fmt_entries(b, v.u.map->entries, v.u.map->len, true, up);
            buf_put(b, "}");
            break;
        case VAL_ENTITY:
            buf_put(b, v.u.ent && v.u.ent->type_name ? v.u.ent->type_name : "");
            buf_put(b, "(");
            if (v.u.ent) v_fmt_entries(b, v.u.ent->fields, v.u.ent->len, false, up);
            buf_put(b, ")");
            break;
        case VAL_VARIANT:
            if (!v.u.var) { buf_put(b, "None"); break; }
            buf_put(b, v.u.var->name);
            if (v.u.var->len == 0) break;
            buf_put(b, "(");
            for (size_t i = 0; i < v.u.var->len; i++) {
                if (i > 0) buf_put(b, ", ");
                v_fmt_in(b, v.u.var->fields[i], up);
            }
            buf_put(b, ")");
            break;
        case VAL_HANDLE:
            // The kinds are numbered as the VM numbers them.
            snprintf(num, sizeof(num), "<handle:%d>", v.u.hdl ? (int)v.u.hdl->kind : 0);
            buf_put(b, num);
            break;
        case VAL_CLOSURE: buf_put(b, "<fn>"); break;
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

// A str holds no NUL: it ends at one. The n bytes read from outside the
// program are Ok(str) when none of them is a NUL and an Err when one is, as
// on the VM.
#define ERR_TEXT_NUL "text holds a NUL"
static AnimaVal text_read(const char *p, size_t n) {
    if (n > 0 && memchr(p, '\0', n)) return v_err(ERR_TEXT_NUL);
    char *t = malloc(n + 1);
    if (n > 0) memcpy(t, p, n);
    t[n] = '\0';
    AnimaVal r = v_ok(v_str(t));
    free(t);
    return r;
}

static AnimaVal hdl_stream_recv(AnimaVal hv, int64_t max_b) {
    if (!hv.u.hdl || hv.u.hdl->closed) return v_err("socket closed");
    if (max_b <= 0) max_b = 4096;
    char *buf = malloc((size_t)max_b + 1);
    ssize_t n = recv(hv.u.hdl->fd, buf, (size_t)max_b, 0);
    if (n < 0) { int e = errno; free(buf); return v_err(strerror(e)); }
    if (n == 0) { free(buf); return v_err("EOF"); }
    AnimaVal r = text_read(buf, (size_t)n);
    free(buf);
    return r;
}

// ─── std.requests (HTTP/HTTPS over POSIX + OpenSSL) ───
static int64_t mono_ms(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (int64_t)ts.tv_sec * 1000 + ts.tv_nsec / 1000000;
}

// ─── The answer of an HTTP server ───
// It is read as Go's net/http reads it, which is what the VM runs: what Go
// takes, what it refuses and the words it refuses with are followed step by
// step, and the tests run both backends on the same answers. An answer is
// read from the bytes that have arrived so far, and again from where it
// stopped when more have: a server may keep the connection open after an
// answer that says where it ends. A NUL in it is a byte like any other;
// only a body that holds one is no str.
static int utf8_seq_len(const unsigned char *s);

typedef struct { char **v; size_t n; } HttpVals;

static void http_vals_add(HttpVals *vs, const char *s, size_t len) {
    vs->v = realloc(vs->v, (vs->n + 1) * sizeof(char *));
    char *c = malloc(len + 1);
    if (len > 0) memcpy(c, s, len);
    c[len] = '\0';
    vs->v[vs->n++] = c;
}

static void http_vals_free(HttpVals *vs) {
    for (size_t k = 0; k < vs->n; k++) free(vs->v[k]);
    free(vs->v);
    vs->v = NULL; vs->n = 0;
}

enum { HTTP_MORE, HTTP_DONE, HTTP_BAD, HTTP_FIELD, HTTP_END, HTTP_EOF };
enum { HTTP_FIRST_LINE, HTTP_FIELDS, HTTP_CHUNK, HTTP_TRAILER, HTTP_LENGTH, HTTP_TO_CLOSE };
// The size of the buffer Go reads a connection through: no line of a
// chunked body is longer.
#define HTTP_GO_BUF 4096

typedef struct {
    const char *p; size_t n; bool eof;  // what has arrived, and whether no more will
    size_t at;                          // it is read up to here
    int stage;
    bool first_field;                   // no field of this head is read yet
    bool after_1xx;                     // a 1xx answer came first and was passed over
    bool in_body;                       // the head is read: what fails now is the body
    int status, major, minor;
    HttpVals lengths, encodings, trailers, connections;
    bool upgrade;                       // the first Upgrade field has a value
    bool seen_upgrade;
    uint64_t want;                      // the length of a body that has one
    int64_t excess;                     // Go's count of the framing of a chunked body
    AnimaBuf chunks;                    // a chunked body without its framing
    const char *body; size_t body_len;
    char *bad;                          // why the answer is refused
} HttpAnswer;

static void http_answer_free(HttpAnswer *a) {
    http_vals_free(&a->lengths); http_vals_free(&a->encodings);
    http_vals_free(&a->trailers); http_vals_free(&a->connections);
    free(a->chunks.p); free(a->bad);
}

static int http_fail(HttpAnswer *a, char *why) { a->bad = why; return HTTP_BAD; }

// The line that starts at i, as Go's bufio gives it: without the LF or
// CR LF that ends it, and *next where the one after starts. 0 when its end
// has not arrived. Once the server has said all, what is left is a line as
// it is; -1 when nothing is.
static int http_line_at(const HttpAnswer *a, size_t i, const char **line, size_t *len, size_t *next) {
    const char *nl = i < a->n ? memchr(a->p + i, '\n', a->n - i) : NULL;
    if (nl) {
        size_t e = (size_t)(nl - a->p);
        *line = a->p + i;
        *len = e - i;
        if (*len > 0 && a->p[e - 1] == '\r') (*len)--;
        *next = e + 1;
        return 1;
    }
    if (!a->eof) return 0;
    if (i >= a->n) return -1;
    *line = a->p + i; *len = a->n - i; *next = a->n;
    return 1;
}

static void http_trim(const char **s, size_t *len) {
    while (*len > 0 && ((*s)[0] == ' ' || (*s)[0] == '\t')) { (*s)++; (*len)--; }
    while (*len > 0 && ((*s)[*len - 1] == ' ' || (*s)[*len - 1] == '\t')) (*len)--;
}

// Whether Go prints a character outside ASCII as itself. Go asks its
// Unicode tables; this knows the spaces, the controls, the format marks
// and the private areas, and takes the rest to be printed.
static bool go_prints(uint32_t r) {
    if (r <= 0xa0 || r == 0xad || r == 0x1680 || r == 0x3000 || r == 0xfeff) return false;
    if ((r >= 0x2000 && r <= 0x200f) || (r >= 0x2028 && r <= 0x202f) || (r >= 0x205f && r <= 0x206f)) return false;
    if ((r >= 0xe000 && r <= 0xf8ff) || (r >= 0xfff0 && r <= 0xfffb) || (r & 0xfffe) == 0xfffe || r >= 0xe0000) return false;
    return true;
}

// Adds s[0..len) to b as Go's %q writes it.
static void go_quote(AnimaBuf *b, const char *s, size_t len) {
    buf_put(b, "\"");
    for (size_t k = 0; k < len; k++) {
        unsigned char c = (unsigned char)s[k];
        char esc[16];
        if (c >= 0x80) {
            int n = utf8_seq_len((const unsigned char *)s + k);
            if (n == 0 || (size_t)n > len - k) { snprintf(esc, sizeof(esc), "\\x%02x", c); buf_put(b, esc); continue; }
            uint32_t r = n == 2 ? (c & 0x1fu) : n == 3 ? (c & 0x0fu) : (c & 0x07u);
            for (int m = 1; m < n; m++) r = (r << 6) | ((unsigned char)s[k + (size_t)m] & 0x3fu);
            if (go_prints(r)) buf_putn(b, s + k, (size_t)n);
            else { snprintf(esc, sizeof(esc), r < 0x10000 ? "\\u%04x" : "\\U%08x", (unsigned)r); buf_put(b, esc); }
            k += (size_t)n - 1;
            continue;
        }
        if (c == '"' || c == '\\') { esc[0] = '\\'; esc[1] = (char)c; esc[2] = 0; }
        else if (c == '\a') strcpy(esc, "\\a");
        else if (c == '\b') strcpy(esc, "\\b");
        else if (c == '\f') strcpy(esc, "\\f");
        else if (c == '\n') strcpy(esc, "\\n");
        else if (c == '\r') strcpy(esc, "\\r");
        else if (c == '\t') strcpy(esc, "\\t");
        else if (c == '\v') strcpy(esc, "\\v");
        else if (c < 0x20 || c == 0x7f) snprintf(esc, sizeof(esc), "\\x%02x", c);
        else { esc[0] = (char)c; esc[1] = 0; }
        buf_put(b, esc);
    }
    buf_put(b, "\"");
}

// what, then s[0..len): quoted as Go's %q quotes it, or as it is. No str
// holds a NUL: one in a line given as it is is written \x00, as the VM
// writes it.
static char *http_msg(const char *what, const char *s, size_t len, bool quoted) {
    AnimaBuf b = {0};
    buf_put(&b, what);
    if (quoted) { go_quote(&b, s, len); return b.p; }
    for (size_t k = 0; k < len; k++) {
        if (s[k] == '\0') buf_put(&b, "\\x00");
        else buf_putn(&b, s + k, 1);
    }
    return b.p;
}

// what, then the values as Go's %q writes a list of them: ["a" "b"].
static char *http_msg_vals(const char *what, const HttpVals *vs) {
    AnimaBuf b = {0};
    buf_put(&b, what); buf_put(&b, "[");
    for (size_t k = 0; k < vs->n; k++) {
        if (k > 0) buf_put(&b, " ");
        go_quote(&b, vs->v[k], strlen(vs->v[k]));
    }
    buf_put(&b, "]");
    return b.p;
}

static bool http_name_byte(unsigned char c) {
    return (c >= '0' && c <= '9') || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
        (c != 0 && strchr("!#$%&'*+-.^_\x60|~", c) != NULL);
}

static bool http_value_byte(unsigned char c) {
    return c >= 0x80 || c == '\t' || (c >= 0x20 && c < 0x7f);
}

// The field that starts at a->at, with the lines that go on with it, as
// Go's textproto takes it: a line that starts with a space or a tab goes on
// with the one before, a field has a colon, a name of token bytes and a
// value without control bytes. HTTP_FIELD with the field in kv, HTTP_END
// at the empty line that ends the fields, HTTP_EOF when the server stopped
// before one, HTTP_BAD for a field Go refuses, HTTP_MORE when the field
// has not all arrived.
static int http_field(HttpAnswer *a, AnimaBuf *kv) {
    const char *line = NULL;
    size_t len = 0, next = 0, i = a->at;
    if (a->first_field && i < a->n && (a->p[i] == ' ' || a->p[i] == '\t')) {
        if (http_line_at(a, i, &line, &len, &next) == 0) {
            if (a->n - i < HTTP_GO_BUF) return HTTP_MORE;
            len = HTTP_GO_BUF;
        }
        // Go quotes no more than 80 bytes of such a line.
        if (len > 80) return http_fail(a, strdup("message too large"));
        return http_fail(a, http_msg("malformed MIME header initial line: ", line, len, false));
    }
    int r = http_line_at(a, i, &line, &len, &next);
    if (r == 0) return HTTP_MORE;
    if (r < 0) return HTTP_EOF;
    if (len == 0) { a->at = next; return HTTP_END; }
    if (!memchr(line, ':', len)) return http_fail(a, http_msg("malformed MIME header: missing colon: ", line, len, true));
    http_trim(&line, &len);
    kv->len = 0;
    buf_putn(kv, line, len);
    size_t j = next;
    for (;;) {
        size_t k = j;
        while (k < a->n && (a->p[k] == ' ' || a->p[k] == '\t')) k++;
        // Whether the next line goes on with this one shows at its first
        // byte that is no space.
        if (k >= a->n && !a->eof) return HTTP_MORE;
        if (k == j) break;
        buf_putn(kv, " ", 1);
        r = http_line_at(a, k, &line, &len, &next);
        if (r == 0) return HTTP_MORE;
        j = k;
        if (r < 0) break;
        http_trim(&line, &len);
        buf_putn(kv, line, len);
        j = next;
    }
    size_t name_len = (size_t)((const char *)memchr(kv->p, ':', kv->len) - kv->p);
    bool ok = name_len > 0;
    bool spaced = false;
    for (size_t k = 0; ok && k < name_len; k++) {
        if (kv->p[k] == ' ') spaced = true;
        else ok = http_name_byte((unsigned char)kv->p[k]);
    }
    // Go writes a name its way, Content-Length, where the field is: a field
    // refused for its value is given with its name so written.
    bool upper = true;
    for (size_t k = 0; ok && !spaced && k < name_len; k++) {
        kv->p[k] = (char)(upper ? toupper((unsigned char)kv->p[k]) : tolower((unsigned char)kv->p[k]));
        upper = kv->p[k] == '-';
    }
    for (size_t k = name_len + 1; ok && k < kv->len; k++) ok = http_value_byte((unsigned char)kv->p[k]);
    if (!ok) return http_fail(a, http_msg("malformed MIME header line: ", kv->p, kv->len, false));
    a->at = j;
    a->first_field = false;
    return HTTP_FIELD;
}

// The first line of an answer, "HTTP/1.1 200 OK", read as Go reads it.
static int http_first_line(HttpAnswer *a, const char *line, size_t len) {
    const char *sp = memchr(line, ' ', len);
    if (!sp) return http_fail(a, http_msg("malformed HTTP response ", line, len, true));
    size_t proto_len = (size_t)(sp - line);
    const char *code = sp + 1;
    size_t rest = len - proto_len - 1;
    while (rest > 0 && code[0] == ' ') { code++; rest--; }
    const char *end = memchr(code, ' ', rest);
    size_t code_len = end ? (size_t)(end - code) : rest;
    // Three characters that Go's Atoi takes and that are not below zero.
    bool ok = code_len == 3;
    int n = 0;
    for (size_t k = 0; ok && k < 3; k++) {
        if (k == 0 && (code[0] == '+' || code[0] == '-')) continue;
        ok = code[k] >= '0' && code[k] <= '9';
        if (ok) n = n * 10 + (code[k] - '0');
    }
    if (ok && code[0] == '-' && n != 0) ok = false;
    if (!ok) return http_fail(a, http_msg("malformed HTTP status code ", code, code_len, true));
    ok = proto_len == 8 && memcmp(line, "HTTP/", 5) == 0 && line[5] >= '0' && line[5] <= '9' &&
        line[6] == '.' && line[7] >= '0' && line[7] <= '9';
    if (!ok) return http_fail(a, http_msg("malformed HTTP version ", line, proto_len, true));
    a->status = n;
    a->major = line[5] - '0';
    a->minor = line[7] - '0';
    return HTTP_DONE;
}

static bool http_name_is(const AnimaBuf *kv, size_t name_len, const char *name) {
    return name_len == strlen(name) && strncasecmp(kv->p, name, name_len) == 0;
}

// Whether a list of values separated by commas has the token.
static bool http_has_token(const char *v, const char *token) {
    for (;;) {
        const char *comma = strchr(v, ',');
        const char *s = v;
        size_t len = comma ? (size_t)(comma - v) : strlen(v);
        http_trim(&s, &len);
        if (len == strlen(token) && strncasecmp(s, token, len) == 0) return true;
        if (!comma) return false;
        v = comma + 1;
    }
}

// The name a Trailer field may not give, if it gives one.
static const char *http_bad_trailer(const HttpVals *vs) {
    static const char *const names[] = {"Transfer-Encoding", "Trailer", "Content-Length"};
    for (size_t k = 0; k < vs->n; k++) {
        const char *v = vs->v[k];
        for (;;) {
            const char *comma = strchr(v, ',');
            const char *s = v;
            size_t len = comma ? (size_t)(comma - v) : strlen(v);
            http_trim(&s, &len);
            for (size_t m = 0; m < 3; m++) {
                if (len == strlen(names[m]) && strncasecmp(s, names[m], len) == 0) return names[m];
            }
            if (!comma) break;
            v = comma + 1;
        }
    }
    return NULL;
}

// The head is read: what it says of the body, in the order Go looks at it.
// HTTP_MORE to go on reading, HTTP_DONE for an answer with no body.
static int http_head_end(HttpAnswer *a) {
    bool chunked = false;
    // A Transfer-Encoding counts from HTTP/1.1 on, and only "chunked" does.
    // Go takes HTTP/0.0 for HTTP/1.1.
    bool is_1_1 = a->major > 1 || (a->major == 1 && a->minor >= 1) || (a->major == 0 && a->minor == 0);
    if (a->encodings.n > 0 && is_1_1) {
        if (a->encodings.n != 1) return http_fail(a, http_msg_vals("too many transfer encodings: ", &a->encodings));
        const char *te = a->encodings.v[0];
        if (strcasecmp(te, "chunked") != 0) return http_fail(a, http_msg("unsupported transfer encoding: ", te, strlen(te), true));
        chunked = true;
    }
    bool has_length = a->lengths.n > 0;
    uint64_t length = 0;
    if (has_length) {
        const char *first = a->lengths.v[0];
        size_t first_len = strlen(first);
        http_trim(&first, &first_len);
        for (size_t k = 1; k < a->lengths.n; k++) {
            const char *other = a->lengths.v[k];
            size_t other_len = strlen(other);
            http_trim(&other, &other_len);
            if (other_len != first_len || memcmp(other, first, first_len) != 0) {
                return http_fail(a, http_msg_vals("http: message cannot contain multiple Content-Length headers; got ", &a->lengths));
            }
        }
        if (first_len == 0) return http_fail(a, strdup("invalid empty Content-Length \"\""));
        bool ok = true;
        for (size_t k = 0; ok && k < first_len; k++) {
            ok = first[k] >= '0' && first[k] <= '9' && length <= (INT64_MAX - (uint64_t)(first[k] - '0')) / 10;
            if (ok) length = length * 10 + (uint64_t)(first[k] - '0');
        }
        if (!ok) return http_fail(a, http_msg("bad Content-Length ", first, first_len, true));
    }
    if (chunked) {
        const char *name = http_bad_trailer(&a->trailers);
        if (name) return http_fail(a, http_msg("bad trailer key ", name, strlen(name), true));
    }
    bool is_1xx = a->status >= 100 && a->status <= 199;
    if (is_1xx && a->status != 101) {
        // Not the answer yet: the next one is.
        http_vals_free(&a->lengths); http_vals_free(&a->encodings);
        http_vals_free(&a->trailers); http_vals_free(&a->connections);
        a->upgrade = a->seen_upgrade = false;
        a->after_1xx = true;
        a->stage = HTTP_FIRST_LINE;
        return HTTP_MORE;
    }
    a->in_body = true;
    a->body = a->p + a->at;
    a->body_len = 0;
    bool switched = false;
    if (a->status == 101 && a->upgrade) {
        for (size_t k = 0; k < a->connections.n && !switched; k++) switched = http_has_token(a->connections.v[k], "Upgrade");
    }
    bool no_body = is_1xx || a->status == 204 || a->status == 304;
    if (switched) a->stage = HTTP_TO_CLOSE;
    else if (no_body) return HTTP_DONE;
    else if (chunked) { a->stage = HTTP_CHUNK; buf_putn(&a->chunks, "", 0); }
    else if (!has_length) a->stage = HTTP_TO_CLOSE;
    else if (length == 0) return HTTP_DONE;
    else { a->stage = HTTP_LENGTH; a->want = length; }
    return HTTP_MORE;
}

// The chunk that starts at a->at, read as Go's chunked reader reads it.
// HTTP_MORE when it is read and another follows or when it has not all
// arrived; a->at only moves past a chunk that is whole.
static int http_chunk(HttpAnswer *a) {
    size_t avail = a->n - a->at;
    const char *line = a->p + a->at;
    const char *nl = avail > 0 ? memchr(line, '\n', avail < HTTP_GO_BUF ? avail : HTTP_GO_BUF) : NULL;
    if (!nl) {
        if (avail >= HTTP_GO_BUF) return http_fail(a, strdup("header line too long"));
        if (a->eof) return http_fail(a, strdup("unexpected EOF"));
        return HTTP_MORE;
    }
    size_t len = (size_t)(nl - line) + 1;
    const char *cr = memchr(line, '\r', len);
    if (!cr) return http_fail(a, strdup("chunked line ends with bare LF"));
    if ((size_t)(cr - line) != len - 2) return http_fail(a, strdup("invalid CR in chunked line"));
    len -= 2;
    int64_t excess = (int64_t)((uint64_t)a->excess + len + 2);
    while (len > 0 && (line[len - 1] == ' ' || line[len - 1] == '\t')) len--;
    const char *semi = memchr(line, ';', len);
    if (semi) len = (size_t)(semi - line);
    if (len == 0) return http_fail(a, strdup("empty hex number for chunk length"));
    uint64_t size = 0;
    for (size_t k = 0; k < len; k++) {
        unsigned char c = (unsigned char)line[k];
        if (!isxdigit(c)) return http_fail(a, strdup("invalid byte in chunk length"));
        if (k == 16) return http_fail(a, strdup("http chunk length too large"));
        size = (size << 4) | (uint64_t)(c <= '9' ? c - '0' : (c | 0x20) - 'a' + 10);
    }
    // Go counts the bytes that are framing and not data, in 64 bits that
    // wrap, and refuses a body that is mostly framing.
    excess = (int64_t)((uint64_t)excess - (16 + 2 * size));
    if (excess < 0) excess = 0;
    size_t data = (size_t)(nl - a->p) + 1;
    if (size == 0) {
        a->at = data;
        a->stage = HTTP_TRAILER;
        return HTTP_MORE;
    }
    if (excess > 16 * 1024) return http_fail(a, strdup("chunked encoding contains too much non-data"));
    uint64_t have = a->n - data;
    if (have < size || have - size < 2) {
        if (a->eof) return http_fail(a, strdup("unexpected EOF"));
        return HTTP_MORE;
    }
    if (a->p[data + size] != '\r' || a->p[data + size + 1] != '\n') return http_fail(a, strdup("malformed chunked encoding"));
    buf_putn(&a->chunks, a->p + data, (size_t)size);
    a->excess = excess;
    a->at = data + (size_t)size + 2;
    return HTTP_MORE;
}

// What follows the last chunk: an empty line, or fields up to one.
static int http_trailer(HttpAnswer *a, AnimaBuf *kv) {
    size_t avail = a->n - a->at;
    const char *p = a->p + a->at;
    if (avail >= 2 && p[0] == '\r' && p[1] == '\n') return HTTP_DONE;
    if (avail < 2) {
        if (a->eof) return http_fail(a, strdup("http: unexpected EOF reading trailer"));
        return HTTP_MORE;
    }
    // Go reads fields only when it sees their end in its buffer.
    bool ends = false;
    size_t look = avail < HTTP_GO_BUF ? avail : HTTP_GO_BUF;
    for (size_t k = 4; k <= look && !ends; k++) ends = memcmp(p + k - 4, "\r\n\r\n", 4) == 0;
    if (!ends) {
        if (avail >= HTTP_GO_BUF || a->eof) return http_fail(a, strdup("http: suspiciously long trailer after chunked body"));
        return HTTP_MORE;
    }
    a->first_field = true;
    for (;;) {
        int r = http_field(a, kv);
        if (r == HTTP_FIELD) continue;
        if (r == HTTP_END) return HTTP_DONE;
        if (r == HTTP_EOF) return http_fail(a, strdup("http: unexpected EOF reading trailer"));
        return r;
    }
}

// Reads on in the answer, of which p[0..n) has arrived, and all of it if
// eof. HTTP_DONE with the status and the body, HTTP_BAD with why Go
// refuses it, HTTP_MORE when more has to arrive first.
static int http_answer(HttpAnswer *a, const char *p, size_t n, bool eof) {
    a->p = p; a->n = n; a->eof = eof;
    if (a->bad) return HTTP_BAD;
    AnimaBuf kv = {0};
    int r = HTTP_MORE;
    for (bool go = true; go;) {
        size_t was = a->at;
        int stage = a->stage;
        switch (a->stage) {
        case HTTP_FIRST_LINE: {
            const char *line = NULL;
            size_t len = 0, next = 0;
            int got = http_line_at(a, a->at, &line, &len, &next);
            if (got == 0) { r = HTTP_MORE; break; }
            if (got < 0) { r = http_fail(a, strdup("unexpected EOF")); break; }
            r = http_first_line(a, line, len);
            if (r == HTTP_BAD) break;
            a->at = next;
            a->stage = HTTP_FIELDS;
            a->first_field = true;
            r = HTTP_MORE;
            break;
        }
        case HTTP_FIELDS: {
            r = http_field(a, &kv);
            if (r == HTTP_EOF) { r = http_fail(a, strdup("unexpected EOF")); break; }
            if (r == HTTP_END) { r = http_head_end(a); break; }
            if (r != HTTP_FIELD) break;
            size_t name_len = (size_t)((const char *)memchr(kv.p, ':', kv.len) - kv.p);
            const char *val = kv.p + name_len + 1;
            size_t val_len = kv.len - name_len - 1;
            while (val_len > 0 && (val[0] == ' ' || val[0] == '\t')) { val++; val_len--; }
            // A field that is well formed holds no NUL.
            if (http_name_is(&kv, name_len, "Content-Length")) http_vals_add(&a->lengths, val, val_len);
            else if (http_name_is(&kv, name_len, "Transfer-Encoding")) http_vals_add(&a->encodings, val, val_len);
            else if (http_name_is(&kv, name_len, "Trailer")) http_vals_add(&a->trailers, val, val_len);
            else if (http_name_is(&kv, name_len, "Connection")) http_vals_add(&a->connections, val, val_len);
            else if (http_name_is(&kv, name_len, "Upgrade") && !a->seen_upgrade) { a->seen_upgrade = true; a->upgrade = val_len > 0; }
            r = HTTP_MORE;
            break;
        }
        case HTTP_CHUNK:
            r = http_chunk(a);
            break;
        case HTTP_TRAILER:
            r = http_trailer(a, &kv);
            if (r == HTTP_DONE) { a->body = a->chunks.p; a->body_len = a->chunks.len; }
            break;
        case HTTP_LENGTH:
            a->body = a->p + a->at;
            if (a->n - a->at >= a->want) { a->body_len = (size_t)a->want; r = HTTP_DONE; }
            else r = a->eof ? http_fail(a, strdup("unexpected EOF")) : HTTP_MORE;
            break;
        case HTTP_TO_CLOSE:
            a->body = a->p + a->at;
            a->body_len = a->n - a->at;
            r = a->eof ? HTTP_DONE : HTTP_MORE;
            break;
        }
        // On it goes while something was read.
        go = r == HTTP_MORE && (a->at != was || a->stage != stage);
    }
    free(kv.p);
    return r;
}

// ─── The URL of a request ───
// It is read as Go's net/url and net/http read it, which is what the VM
// runs: what Go takes for a URL, what it refuses and with which words, and
// what it then sends and dials. A URL is not cut where it "looks" cut: the
// host of http://a@b/ is b, and a line end in a path is no second header.
typedef struct { const char *p; size_t n; } Span;

static long span_find(Span s, char c) {
    const char *q = s.n ? memchr(s.p, c, s.n) : NULL;
    return q ? (long)(q - s.p) : -1;
}

static long span_rfind(Span s, char c) {
    for (size_t i = s.n; i > 0; i--) if (s.p[i - 1] == c) return (long)(i - 1);
    return -1;
}

static bool span_starts(Span s, const char *with) {
    size_t n = strlen(with);
    return s.n >= n && memcmp(s.p, with, n) == 0;
}

static void buf_span(AnimaBuf *b, Span s) {
    if (s.n > 0) buf_putn(b, s.p, s.n);
}

static bool url_alnum(unsigned char c) {
    return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9');
}

static int url_hex(unsigned char c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    if (c >= 'A' && c <= 'F') return c - 'A' + 10;
    return -1;
}

static bool url_among(unsigned char c, const char *set) { return c != 0 && strchr(set, c) != NULL; }

enum { URL_PATH, URL_USER, URL_HOST, URL_ZONE, URL_FRAG };

// Whether Go writes the byte c as %XX in that part of a URL (shouldEscape).
static bool url_escapes(unsigned char c, int part) {
    if (url_alnum(c)) return false;
    if ((part == URL_HOST || part == URL_ZONE) && url_among(c, "!$&'()*+,;=:[]<>\"")) return false;
    if (url_among(c, "-_.~")) return false;
    if (url_among(c, "$&+,/:;=?@")) {
        if (part == URL_PATH) return c == '?';
        if (part == URL_USER) return c == '@' || c == '/' || c == '?' || c == ':';
        if (part == URL_FRAG) return false;
    }
    if (part == URL_FRAG && url_among(c, "!()*")) return false;
    return true;
}

// before, then s as Go's %q writes it, then after.
static char *url_why(const char *before, Span s, const char *after) {
    AnimaBuf b = {0};
    buf_put(&b, before);
    go_quote(&b, s.p, s.n);
    buf_put(&b, after);
    return b.p;
}

// Go's unescape: NULL, or why s is not that part of a URL. What s stands
// for is added to out, if there is one; it may hold any byte.
static char *url_unescape(Span s, int part, AnimaBuf *out) {
    bool host = part == URL_HOST || part == URL_ZONE;
    for (size_t i = 0; i < s.n;) {
        unsigned char c = (unsigned char)s.p[i];
        if (c != '%') {
            if (host && c < 0x80 && url_escapes(c, part)) return url_why("invalid character ", (Span){s.p + i, 1}, " in host name");
            i++;
            continue;
        }
        int hi = i + 2 < s.n ? url_hex((unsigned char)s.p[i + 1]) : -1;
        int lo = i + 2 < s.n ? url_hex((unsigned char)s.p[i + 2]) : -1;
        if (hi < 0 || lo < 0) return url_why("invalid URL escape ", (Span){s.p + i, s.n - i > 3 ? 3 : s.n - i}, "");
        bool pct = memcmp(s.p + i, "%25", 3) == 0;
        // In a host only a byte outside ASCII is written escaped, and a %.
        if (part == URL_HOST && hi < 8 && !pct) return url_why("invalid URL escape ", (Span){s.p + i, 3}, "");
        int v = hi << 4 | lo;
        if (part == URL_ZONE && !pct && v != ' ' && url_escapes((unsigned char)v, URL_HOST)) return url_why("invalid URL escape ", (Span){s.p + i, 3}, "");
        i += 3;
    }
    if (!out) return NULL;
    for (size_t i = 0; i < s.n; i++) {
        char c = s.p[i];
        if (c == '%') {
            c = (char)(url_hex((unsigned char)s.p[i + 1]) << 4 | url_hex((unsigned char)s.p[i + 2]));
            i += 2;
        }
        buf_putn(out, &c, 1);
    }
    return NULL;
}

// Adds the bytes s[0..n) as Go's escape writes them in that part.
static void url_escape(AnimaBuf *b, const char *s, size_t n, int part) {
    for (size_t i = 0; i < n; i++) {
        unsigned char c = (unsigned char)s[i];
        if (url_escapes(c, part)) {
            char esc[4] = {'%', "0123456789ABCDEF"[c >> 4], "0123456789ABCDEF"[c & 15], 0};
            buf_putn(b, esc, 3);
        } else {
            buf_putn(b, s + i, 1);
        }
    }
}

// Adds a path or a fragment as Go sends and prints it (EscapedPath,
// EscapedFragment): as it was written if every byte of it may stand in a
// URL, and else what it stands for, escaped anew.
static void url_put_part(AnimaBuf *b, Span raw, int part) {
    bool as_written = true;
    for (size_t i = 0; i < raw.n && as_written; i++) {
        unsigned char c = (unsigned char)raw.p[i];
        as_written = url_among(c, "!$&'()*+,;=:@[]%") || !url_escapes(c, part);
    }
    // Go keeps no written form of a path that is its own escaped form,
    // and then knows the path * by itself.
    if (part == URL_PATH && raw.n == 3 && memcmp(raw.p, "%2A", 3) == 0) { buf_put(b, "*"); return; }
    if (as_written) { buf_span(b, raw); return; }
    AnimaBuf plain = {0};
    char *bad = url_unescape(raw, part, &plain);
    free(bad);
    url_escape(b, plain.p ? plain.p : "", plain.len, part);
    free(plain.p);
}

// Adds a query as it is sent and shown. Go sends it as written; a space,
// a quote, < or > or a byte outside ASCII in it is written %XX here, and
// on the VM, so that the first line of a request is one.
static void url_put_query(AnimaBuf *b, Span q) {
    for (size_t i = 0; i < q.n; i++) {
        unsigned char c = (unsigned char)q.p[i];
        if (c == ' ' || c == '"' || c == '<' || c == '>' || c >= 0x80) {
            char esc[4] = {'%', "0123456789ABCDEF"[c >> 4], "0123456789ABCDEF"[c & 15], 0};
            buf_putn(b, esc, 3);
        } else {
            buf_putn(b, q.p + i, 1);
        }
    }
}

static bool url_port_ok(Span port) {
    if (port.n == 0) return true;
    if (port.p[0] != ':') return false;
    for (size_t i = 1; i < port.n; i++) if (port.p[i] < '0' || port.p[i] > '9') return false;
    return true;
}

// What Go's netip.ParseAddr makes of s: 4 for an IPv4 address, 6 for an
// IPv6 one, 7 for an IPv6 one with a zone, 0 for no address.
static int url_addr(const char *s) {
    unsigned char raw[sizeof(struct in6_addr)];
    size_t at = strcspn(s, ".:%");
    if (s[at] == '.') return inet_pton(AF_INET, s, raw) == 1 ? 4 : 0;
    if (s[at] != ':') return 0;
    const char *pct = strchr(s, '%');
    if (!pct) return inet_pton(AF_INET6, s, raw) == 1 ? 6 : 0;
    if (pct[1] == '\0') return 0;
    char *addr = strndup(s, (size_t)(pct - s));
    bool ok = inet_pton(AF_INET6, addr, raw) == 1;
    free(addr);
    return ok ? 7 : 0;
}

typedef struct {
    AnimaBuf scheme;          // in lower case
    Span opaque;              // what follows the scheme, if no / does
    bool has_user, has_pass;
    AnimaBuf user, pass;      // what they stand for: any byte
    AnimaBuf host;            // with its port, as Go keeps it
    bool omit_host;
    Span path, query, frag;   // as written
    bool force_query;
} Url;

static void url_free(Url *u) {
    free(u->scheme.p); free(u->user.p); free(u->pass.p); free(u->host.p);
}

static char *url_host(Span h, Url *u) {
    long open = span_rfind(h, '[');
    if (open >= 0) {
        long close = span_rfind(h, ']');
        if (close < 0) return strdup("missing ']' in host");
        // What follows the ] is a port, so the [ is before it.
        Span port = {h.p + close + 1, h.n - (size_t)close - 1};
        if (!url_port_ok(port)) return url_why("invalid port ", port, " after host");
        Span name = {h.p + open + 1, (size_t)(close - open - 1)};
        size_t zone = name.n;
        for (size_t i = 0; i + 3 <= name.n; i++) if (memcmp(name.p + i, "%25", 3) == 0) { zone = i; break; }
        AnimaBuf plain = {0};
        char *bad = url_unescape((Span){name.p, zone}, URL_HOST, &plain);
        if (!bad && zone < name.n) bad = url_unescape((Span){name.p + zone, name.n - zone}, URL_ZONE, &plain);
        int kind = bad ? 0 : url_addr(plain.p ? plain.p : "");
        if (!bad && kind == 0) bad = strdup("invalid host");
        if (!bad && kind == 4) bad = strdup("invalid IP-literal");
        if (!bad) {
            buf_put(&u->host, "[");
            buf_put(&u->host, plain.p);
            buf_put(&u->host, "]");
            buf_putn(&u->host, port.p, port.n);
        }
        free(plain.p);
        return bad;
    }
    long colon = span_rfind(h, ':');
    if (colon >= 0) {
        Span port = {h.p + colon, h.n - (size_t)colon};
        if (!url_port_ok(port)) return url_why("invalid port ", port, " after host");
    }
    return url_unescape(h, URL_HOST, &u->host);
}

static char *url_authority(Span a, Url *u) {
    long at = span_rfind(a, '@');
    char *bad = url_host(at < 0 ? a : (Span){a.p + at + 1, a.n - (size_t)at - 1}, u);
    if (bad || at < 0) return bad;
    Span info = {a.p, (size_t)at};
    for (size_t i = 0; i < info.n; i++) {
        unsigned char c = (unsigned char)info.p[i];
        if (!url_alnum(c) && !url_among(c, "-._:~!$&'()*+,;=%@")) return strdup("net/url: invalid userinfo");
    }
    u->has_user = true;
    long colon = span_find(info, ':');
    bad = url_unescape(colon < 0 ? info : (Span){info.p, (size_t)colon}, URL_USER, &u->user);
    if (bad || colon < 0) return bad;
    u->has_pass = true;
    return url_unescape((Span){info.p + colon + 1, info.n - (size_t)colon - 1}, URL_USER, &u->pass);
}

// Go's url.Parse: NULL, or why raw is no URL. *named is how much of raw
// the error is about: Go names it without its fragment unless the fragment
// is what is wrong.
static char *url_parse(const char *raw, Url *u, size_t *named) {
    size_t all = strlen(raw);
    const char *hash = memchr(raw, '#', all);
    size_t n = hash ? (size_t)(hash - raw) : all;
    *named = n;
    for (size_t i = 0; i < n; i++) {
        unsigned char c = (unsigned char)raw[i];
        if (c < ' ' || c == 0x7f) return strdup("net/url: invalid control character in URL");
    }
    Span rest = {raw, n};
    for (size_t i = 0; i < n; i++) {
        unsigned char c = (unsigned char)raw[i];
        if ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')) continue;
        if ((c >= '0' && c <= '9') || c == '+' || c == '-' || c == '.') {
            if (i == 0) break;
            continue;
        }
        if (c == ':') {
            if (i == 0) return strdup("missing protocol scheme");
            for (size_t k = 0; k < i; k++) {
                char low = (char)tolower((unsigned char)raw[k]);
                buf_putn(&u->scheme, &low, 1);
            }
            rest = (Span){raw + i + 1, n - i - 1};
        }
        break;
    }
    long q = span_find(rest, '?');
    if (q >= 0 && (size_t)q == rest.n - 1) {
        u->force_query = true;
        rest.n--;
    } else if (q >= 0) {
        u->query = (Span){rest.p + q + 1, rest.n - (size_t)q - 1};
        rest.n = (size_t)q;
    }
    bool opaque = false;
    if (!span_starts(rest, "/")) {
        if (u->scheme.len > 0) {
            u->opaque = rest;
            opaque = true;
        } else {
            long slash = span_find(rest, '/');
            if (span_find((Span){rest.p, slash < 0 ? rest.n : (size_t)slash}, ':') >= 0)
                return strdup("first path segment in URL cannot contain colon");
        }
    }
    if (!opaque) {
        if ((u->scheme.len > 0 || !span_starts(rest, "///")) && span_starts(rest, "//")) {
            Span authority = {rest.p + 2, rest.n - 2};
            long slash = span_find(authority, '/');
            rest = slash < 0 ? (Span){authority.p + authority.n, 0} : (Span){authority.p + slash, authority.n - (size_t)slash};
            if (slash >= 0) authority.n = (size_t)slash;
            char *bad = url_authority(authority, u);
            if (bad) return bad;
        } else if (u->scheme.len > 0 && span_starts(rest, "/")) {
            u->omit_host = true;
        }
        char *bad = url_unescape(rest, URL_PATH, NULL);
        if (bad) return bad;
        u->path = rest;
    }
    if (hash && all > n + 1) {
        Span frag = {hash + 1, all - n - 1};
        char *bad = url_unescape(frag, URL_FRAG, NULL);
        if (bad) { *named = all; return bad; }
        u->frag = frag;
    }
    return NULL;
}

// The URL as Go names it in the error of a request: written anew from its
// parts, a password as ***.
static void url_shown(const Url *u, AnimaBuf *b) {
    if (u->scheme.len > 0) { buf_putn(b, u->scheme.p, u->scheme.len); buf_put(b, ":"); }
    if (u->opaque.n > 0) {
        buf_span(b, u->opaque);
    } else {
        bool authority = u->scheme.len > 0 || u->host.len > 0 || u->has_user;
        if (authority && !(u->omit_host && u->host.len == 0 && !u->has_user)) {
            if (u->host.len > 0 || u->path.n > 0 || u->has_user) buf_put(b, "//");
            if (u->has_pass) {
                buf_putn(b, u->user.p ? u->user.p : "", u->user.len);
                buf_put(b, ":***@");
            } else if (u->has_user) {
                url_escape(b, u->user.p ? u->user.p : "", u->user.len, URL_USER);
                buf_put(b, "@");
            }
            if (u->host.len > 0) url_escape(b, u->host.p, u->host.len, URL_HOST);
        }
        AnimaBuf path = {0};
        url_put_part(&path, u->path, URL_PATH);
        if (path.len > 0 && path.p[0] != '/' && u->host.len > 0) buf_put(b, "/");
        if (b->len == 0 && path.len > 0) {
            // A first part with a colon would read as a scheme.
            const char *slash = memchr(path.p, '/', path.len);
            if (memchr(path.p, ':', slash ? (size_t)(slash - path.p) : path.len)) buf_put(b, "./");
        }
        if (path.len > 0) buf_putn(b, path.p, path.len);
        free(path.p);
    }
    if (u->force_query || u->query.n > 0) { buf_put(b, "?"); url_put_query(b, u->query); }
    if (u->frag.n > 0) { buf_put(b, "#"); url_put_part(b, u->frag, URL_FRAG); }
    if (!b->p) buf_put(b, "");
}

static void buf_base64(AnimaBuf *b, const unsigned char *s, size_t n) {
    static const char set[] = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    for (size_t i = 0; i < n; i += 3) {
        uint32_t v = (uint32_t)s[i] << 16 | (i + 1 < n ? (uint32_t)s[i + 1] << 8 : 0) | (i + 2 < n ? s[i + 2] : 0);
        char out[5] = {set[v >> 18], set[(v >> 12) & 63], i + 1 < n ? set[(v >> 6) & 63] : '=', i + 2 < n ? set[v & 63] : '=', 0};
        buf_put(b, out);
    }
}

// Go's isDomainName: whether a name is one the DNS is asked for at all.
static bool http_is_name(const char *s) {
    size_t l = strlen(s);
    if (strcmp(s, ".") == 0) return true;
    if (l == 0 || l > 254 || (l == 254 && s[l - 1] != '.')) return false;
    char last = '.';
    bool letters = false;
    int part = 0;
    for (size_t i = 0; i < l; i++) {
        char c = s[i];
        if ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_') { letters = true; part++; }
        else if (c >= '0' && c <= '9') part++;
        else if (c == '-') { if (last == '.') return false; part++; letters = true; }
        else if (c == '.') { if (last == '.' || last == '-' || part > 63 || part == 0) return false; part = 0; }
        else return false;
        last = c;
    }
    return last != '-' && part <= 63 && letters;
}

// Whether a name is an IPv4 address in one of the old ways of writing one
// (127.1, 0x7f.0.0.1, 017700000001): one to four numbers, decimal, octal
// or hexadecimal, the last of them filling the bytes the others leave.
// getaddrinfo takes such a text for the address; Go takes it for a name.
static bool http_is_old_addr(const char *s) {
    unsigned long long max = 0xffffffffULL;
    for (int part = 0; part < 4; part++) {
        if (!isdigit((unsigned char)*s)) return false;
        char *end = NULL;
        errno = 0;
        unsigned long long v = strtoull(s, &end, 0);
        if (errno != 0) return false;
        if (*end == '\0') return v <= max;
        if (*end != '.' || v > 255 || part == 3) return false;
        max >>= 8;
        s = end + 1;
    }
    return false;
}

// An address to connect to, and its text as Go writes it in an error.
typedef struct {
    struct sockaddr_storage sa;
    socklen_t len;
    int family;
    char text[96];
} HttpPeer;

static void http_peer4(HttpPeer *p, struct in_addr a, int port, bool any) {
    struct sockaddr_in *sa = (struct sockaddr_in *)&p->sa;
    memset(p, 0, sizeof(*p));
    sa->sin_family = AF_INET; sa->sin_addr = a; sa->sin_port = htons((uint16_t)port);
    p->len = sizeof(*sa); p->family = AF_INET;
    char ip[INET_ADDRSTRLEN] = {0};
    if (!any) inet_ntop(AF_INET, &a, ip, sizeof(ip));
    snprintf(p->text, sizeof(p->text), "%s:%d", ip, port);
}

static void http_peer6(HttpPeer *p, const struct in6_addr *a, uint32_t scope, int port) {
    // An IPv4 address written as an IPv6 one is dialed as the IPv4 one.
    if (IN6_IS_ADDR_V4MAPPED(a)) {
        struct in_addr a4;
        memcpy(&a4, a->s6_addr + 12, 4);
        http_peer4(p, a4, port, false);
        return;
    }
    struct sockaddr_in6 *sa = (struct sockaddr_in6 *)&p->sa;
    memset(p, 0, sizeof(*p));
    sa->sin6_family = AF_INET6; sa->sin6_addr = *a; sa->sin6_port = htons((uint16_t)port); sa->sin6_scope_id = scope;
    p->len = sizeof(*sa); p->family = AF_INET6;
    // Go's text of it: the longest run of two or more zero fields is ::,
    // and no field is written as an IPv4 address.
    int best = -1, best_len = 0;
    uint16_t f[8];
    for (int i = 0; i < 8; i++) f[i] = (uint16_t)(a->s6_addr[2 * i] << 8 | a->s6_addr[2 * i + 1]);
    for (int i = 0; i < 8; i++) {
        int j = i;
        while (j < 8 && f[j] == 0) j++;
        if (j - i >= 2 && j - i > best_len) { best = i; best_len = j - i; }
        if (j > i) i = j - 1;
    }
    size_t at = 0;
    p->text[at++] = '[';
    for (int i = 0; i < 8; i++) {
        if (i == best) {
            p->text[at++] = ':'; p->text[at++] = ':';
            i += best_len - 1;
            continue;
        }
        if (i > 0 && i != best + best_len) p->text[at++] = ':';
        at += (size_t)snprintf(p->text + at, sizeof(p->text) - at, "%x", f[i]);
    }
    snprintf(p->text + at, sizeof(p->text) - at, "]:%d", port);
}

// A name is looked up on a thread of its own: getaddrinfo has no time
// limit, and the request has one.
typedef struct {
    pthread_mutex_t mu;
    pthread_cond_t cv;
    char *name;
    struct addrinfo *res;
    bool done, left;
} HttpLookup;

// A lookup goes on after the request that asked has run out of time, for
// as long as the system waits for a name server that does not answer. No
// more than HTTP_LOOKUPS are going on at once (Go keeps to 500 as well): a
// request that finds as many waits for one to end, within its own time.
#define HTTP_LOOKUPS 500
static struct {
    pthread_once_t once;
    pthread_mutex_t mu;
    pthread_cond_t cv;
    int n;
} http_lookups = {.once = PTHREAD_ONCE_INIT, .mu = PTHREAD_MUTEX_INITIALIZER};

static void http_cond_init(pthread_cond_t *cv) {
    pthread_condattr_t ca;
    pthread_condattr_init(&ca);
    pthread_condattr_setclock(&ca, CLOCK_MONOTONIC);
    pthread_cond_init(cv, &ca);
    pthread_condattr_destroy(&ca);
}

static void http_lookups_init(void) { http_cond_init(&http_lookups.cv); }

static void http_lookup_free(HttpLookup *l) {
    if (l->res) freeaddrinfo(l->res);
    pthread_mutex_destroy(&l->mu);
    pthread_cond_destroy(&l->cv);
    free(l->name);
    free(l);
}

static void *http_lookup_run(void *arg) {
    HttpLookup *l = arg;
    struct addrinfo hints = {0}, *res = NULL;
    hints.ai_family = AF_UNSPEC;
    hints.ai_socktype = SOCK_STREAM;
    if (getaddrinfo(l->name, NULL, &hints, &res) != 0) res = NULL;
    pthread_mutex_lock(&l->mu);
    l->res = res;
    l->done = true;
    bool left = l->left;
    pthread_cond_signal(&l->cv);
    pthread_mutex_unlock(&l->mu);
    // Nobody waits any more: what was found is this thread's to free.
    if (left) http_lookup_free(l);
    pthread_mutex_lock(&http_lookups.mu);
    http_lookups.n--;
    pthread_cond_signal(&http_lookups.cv);
    pthread_mutex_unlock(&http_lookups.mu);
    return NULL;
}

// The addresses of a name, or NULL: there are none, or (*late) the time of
// the request ran out first, be it before a thread was had to look it up.
static struct addrinfo *http_lookup(const char *name, int64_t deadline, bool *late) {
    struct timespec until = {(time_t)(deadline / 1000), (long)(deadline % 1000) * 1000000L};
    HttpLookup *l = calloc(1, sizeof(*l));
    pthread_mutex_init(&l->mu, NULL);
    http_cond_init(&l->cv);
    l->name = strdup(name);
    pthread_attr_t at;
    pthread_attr_init(&at);
    pthread_attr_setdetachstate(&at, PTHREAD_CREATE_DETACHED);
    pthread_once(&http_lookups.once, http_lookups_init);
    bool begun = false;
    pthread_mutex_lock(&http_lookups.mu);
    for (;;) {
        pthread_t th;
        if (http_lookups.n < HTTP_LOOKUPS && pthread_create(&th, &at, http_lookup_run, l) == 0) {
            http_lookups.n++;
            begun = true;
            break;
        }
        if (pthread_cond_timedwait(&http_lookups.cv, &http_lookups.mu, &until) != 0) break;
    }
    pthread_mutex_unlock(&http_lookups.mu);
    pthread_attr_destroy(&at);
    if (!begun) {
        http_lookup_free(l);
        *late = true;
        return NULL;
    }
    pthread_mutex_lock(&l->mu);
    while (!l->done && pthread_cond_timedwait(&l->cv, &l->mu, &until) != ETIMEDOUT) {}
    if (!l->done) {
        l->left = true;
        *late = true;
        pthread_mutex_unlock(&l->mu);
        return NULL;
    }
    struct addrinfo *res = l->res;
    l->res = NULL;
    pthread_mutex_unlock(&l->mu);
    http_lookup_free(l);
    return res;
}

// Why an address was not connected to, in Go's words. The first of them
// is the one that is kept.
static void http_undialed(AnimaBuf *why, const HttpPeer *p, const char *what, int err) {
    if (why->p) return;
    buf_put(why, "dial tcp ");
    buf_put(why, p->text);
    buf_put(why, what);
    size_t at = why->len;
    if (err > 0) buf_put(why, strerror(err));
    if (why->len > at) why->p[at] = (char)tolower((unsigned char)why->p[at]);
}

// The addresses of one kind (IPv4 or IPv6), tried in turn.
typedef struct {
    bool on, done;
    size_t left, next;     // how many are not yet tried, and where they are
    int fd;                // the one being connected to, or -1
    const HttpPeer *peer;
    AnimaBuf why;          // why the first that failed did
} HttpRacer;

// Connects to one of the addresses as Go's dialer does: a connected
// socket, or -1 and in *why the reason, if the time did not just run out.
// The addresses of the first one's kind are tried in turn, each until the
// system gives it up: the time of the request is not shared out among
// them, so one that does not answer keeps the ones after it from being
// tried. Those of the other kind are tried beside them once the first
// kind has failed or 300 ms have gone by, so that a machine whose IPv6
// goes nowhere is reached by IPv4. The first to connect is taken; if none
// does, the error is that of the first kind's first address that failed.
static int http_dial(const HttpPeer *peers, size_t npeers, int64_t deadline, AnimaBuf *why) {
    HttpRacer r[2] = {{.fd = -1}, {.fd = -1}};
    for (size_t i = 0; i < npeers; i++) r[peers[i].family == peers[0].family ? 0 : 1].left++;
    r[0].on = true;
    r[1].done = r[1].left == 0;
    int64_t second = mono_ms() + 300;
    int won = -1;
    while (won < 0 && !(r[0].done && r[1].done)) {
        if (mono_ms() >= deadline) break;
        if (!r[1].done && (r[0].done || mono_ms() >= second)) r[1].on = true;
        // Each kind that has no address in hand takes its next.
        for (int k = 0; k < 2 && won < 0; k++) {
            HttpRacer *x = &r[k];
            while (x->on && !x->done && x->fd < 0) {
                if (x->left == 0) { x->done = true; break; }
                if (mono_ms() >= deadline) break;
                while ((peers[x->next].family == peers[0].family) != (k == 0)) x->next++;
                x->peer = &peers[x->next++];
                x->left--;
                int s = socket(x->peer->family, SOCK_STREAM, 0);
                if (s < 0) { http_undialed(&x->why, x->peer, ": socket: ", errno); continue; }
                fcntl(s, F_SETFL, fcntl(s, F_GETFL, 0) | O_NONBLOCK);
                if (connect(s, (const struct sockaddr *)&x->peer->sa, x->peer->len) == 0) { won = s; break; }
                if (errno == EINPROGRESS || errno == EINTR) { x->fd = s; break; }
                int err = errno;
                close(s);
                http_undialed(&x->why, x->peer, ": connect: ", err);
            }
        }
        if (won >= 0) break;
        // Then it waits: for a socket, or for the other kind's turn to come.
        struct pollfd p[2];
        int np = 0, at[2] = {-1, -1};
        int64_t wake = deadline;
        for (int k = 0; k < 2; k++) {
            if (r[k].fd < 0) continue;
            at[k] = np;
            p[np++] = (struct pollfd){r[k].fd, POLLOUT, 0};
        }
        if (!r[1].on && !r[1].done && second < wake) wake = second;
        if (np == 0) continue;
        int64_t wait = wake - mono_ms();
        if (poll(p, (nfds_t)np, wait <= 0 ? 0 : wait > 60000 ? 60000 : (int)wait) < 0) continue;
        for (int k = 0; k < 2 && won < 0; k++) {
            HttpRacer *x = &r[k];
            if (x->fd < 0) continue;
            if (p[at[k]].revents == 0) continue;
            int err = 0;
            socklen_t el = sizeof(err);
            if (getsockopt(x->fd, SOL_SOCKET, SO_ERROR, &err, &el) < 0) err = errno;
            if (err == 0) { won = x->fd; x->fd = -1; break; }
            http_undialed(&x->why, x->peer, ": connect: ", err);
            close(x->fd);
            x->fd = -1;
        }
    }
    for (int k = 0; k < 2; k++) if (r[k].fd >= 0) close(r[k].fd);
    if (won >= 0) {
        fcntl(won, F_SETFL, fcntl(won, F_GETFL, 0) & ~O_NONBLOCK);
        free(r[0].why.p);
    } else {
        *why = r[0].why;
    }
    free(r[1].why.p);
    return won;
}

// The TLS handshake, for no longer than the request has: whether it was
// made, and (*late) whether it was the time that ended it.
static bool http_shake(SSL *ssl, int fd, int64_t deadline, bool *late) {
    int flags = fcntl(fd, F_GETFL, 0);
    fcntl(fd, F_SETFL, flags | O_NONBLOCK);
    bool made = false;
    for (;;) {
        int n = SSL_connect(ssl);
        if (n > 0) { made = true; break; }
        int e = SSL_get_error(ssl, n);
        if (e != SSL_ERROR_WANT_READ && e != SSL_ERROR_WANT_WRITE) break;
        int64_t left = deadline - mono_ms();
        if (left <= 0) { *late = true; break; }
        struct pollfd p = {fd, e == SSL_ERROR_WANT_READ ? POLLIN : POLLOUT, 0};
        if (poll(&p, 1, left > 60000 ? 60000 : (int)left) < 0 && errno != EINTR) break;
    }
    fcntl(fd, F_SETFL, flags);
    return made;
}

// A request that fails reads as on the VM: Get "url": why. who is the
// Get "url" of it.
static AnimaVal http_err(const char *who, const char *why, const char *more) {
    AnimaBuf b = {0};
    buf_put(&b, who); buf_put(&b, ": "); buf_put(&b, why);
    if (more) {
        size_t at = b.len;
        buf_put(&b, more);
        if (b.len > at) b.p[at] = (char)tolower((unsigned char)b.p[at]);
    }
    AnimaVal r = v_err(b.p);
    free(b.p);
    return r;
}

#define HTTP_LATE "context deadline exceeded (Client.Timeout exceeded while awaiting headers)"

// What fails before the head of the answer is read fails with these words
// once the time of the request is over, whatever it was that failed.
static AnimaVal http_late_or(const char *who, int64_t deadline, const char *why, const char *more) {
    if (mono_ms() >= deadline) return http_err(who, HTTP_LATE, NULL);
    return http_err(who, why, more);
}

// Whether a TLS read or write gave up because the socket's time ran out.
static bool http_tls_timed_out(SSL *ssl, int n) {
    int e = SSL_get_error(ssl, n);
    return e == SSL_ERROR_WANT_READ || e == SSL_ERROR_WANT_WRITE ||
        (e == SSL_ERROR_SYSCALL && (errno == EAGAIN || errno == EWOULDBLOCK));
}

// What was wrong with the certificates of the handshake this thread is in:
// the reason Go would give first, in Go's words.
static __thread struct {
    bool bad;
    int rank;
    char *why;
    const char *host;
} tls_seen;

static void tls_why(const char *a, const char *b, const char *c, const char *d) {
    AnimaBuf w = {0};
    buf_put(&w, a); buf_put(&w, b); buf_put(&w, c); buf_put(&w, d);
    free(tls_seen.why);
    tls_seen.why = w.p;
}

// A time as Go writes it (RFC 3339): Z for UTC, +hh:mm otherwise.
static void tls_time(const struct tm *tm, bool utc, char *out, size_t cap) {
    char z[8] = "Z";
    if (!utc) {
        strftime(z, sizeof(z), "%z", tm);
        if (!strcmp(z, "+0000")) strcpy(z, "Z");
        else { z[6] = '\0'; z[5] = z[4]; z[4] = z[3]; z[3] = ':'; }
    }
    size_t n = strftime(out, cap, "%Y-%m-%dT%H:%M:%S", tm);
    snprintf(out + n, cap - n, "%s", z);
}

// The names a certificate is valid for, as Go lists them to a host it is
// not valid for: its addresses to an address, its DNS names to a name.
static void tls_not_for(X509 *cert, const char *host) {
    unsigned char raw[sizeof(struct in6_addr)];
    bool is_ip = inet_pton(AF_INET, host, raw) == 1 || inet_pton(AF_INET6, host, raw) == 1;
    GENERAL_NAMES *sans = X509_get_ext_d2i(cert, NID_subject_alt_name, NULL, NULL);
    if (!sans && X509_check_host(cert, host, 0, X509_CHECK_FLAG_NO_PARTIAL_WILDCARDS, NULL) == 1) {
        tls_why("certificate relies on legacy Common Name field, use SANs instead", "", "", "");
        return;
    }
    AnimaBuf valid = {0};
    int ips = 0;
    for (int i = 0; i < sk_GENERAL_NAME_num(sans); i++) {
        GENERAL_NAME *g = sk_GENERAL_NAME_value(sans, i);
        char one[INET6_ADDRSTRLEN + 1] = {0};
        const char *name = NULL; size_t len = 0;
        if (is_ip && g->type == GEN_IPADD) {
            int n = ASN1_STRING_length(g->d.iPAddress);
            const unsigned char *d = ASN1_STRING_get0_data(g->d.iPAddress);
            if (n == 4) inet_ntop(AF_INET, d, one, sizeof(one));
            else if (n == 16) inet_ntop(AF_INET6, d, one, sizeof(one));
            else continue;
            ips++;
            name = one; len = strlen(one);
        } else if (!is_ip && g->type == GEN_DNS) {
            name = (const char *)ASN1_STRING_get0_data(g->d.dNSName);
            len = (size_t)ASN1_STRING_length(g->d.dNSName);
        } else continue;
        if (valid.len > 0) buf_put(&valid, ", ");
        // A name out of a certificate is not text yet: what cannot be
        // printed in it is left out of the message.
        for (size_t k = 0; k < len; k++) {
            char ch[2] = { (name[k] >= 0x20 && name[k] < 0x7f) ? name[k] : '?', 0 };
            buf_put(&valid, ch);
        }
    }
    GENERAL_NAMES_free(sans);
    if (is_ip && ips == 0)
        tls_why("cannot validate certificate for ", host, " because it doesn't contain any IP SANs", "");
    else if (valid.len == 0)
        tls_why("certificate is not valid for any names, but wanted to match ", host, "", "");
    else
        tls_why("certificate is valid for ", valid.p, ", not ", host);
    free(valid.p);
}

// Called for each thing wrong with a certificate. Go looks at the server's
// own dates first, then at its names, then for an authority, and names the
// first that fails; OpenSSL looks in another order, so every one is heard
// and the one Go would name is kept. The handshake is refused by http_do.
static int tls_refused(int ok, X509_STORE_CTX *sc) {
    if (ok) return 1;
    int err = X509_STORE_CTX_get_error(sc);
    X509 *cert = X509_STORE_CTX_get_current_cert(sc);
    bool own = X509_STORE_CTX_get_error_depth(sc) == 0;
    bool dates = cert && (err == X509_V_ERR_CERT_HAS_EXPIRED || err == X509_V_ERR_CERT_NOT_YET_VALID);
    bool names = cert && (err == X509_V_ERR_HOSTNAME_MISMATCH || err == X509_V_ERR_IP_ADDRESS_MISMATCH);
    // An authority out of its dates is named before one that is not known.
    int rank = dates ? (own ? 4 : 2) : names ? 3 : 1;
    tls_seen.bad = true;
    if (rank <= tls_seen.rank) return 1;
    tls_seen.rank = rank;
    if (dates) {
        bool late = err == X509_V_ERR_CERT_HAS_EXPIRED;
        struct tm edge = {0}, now = {0};
        char at[40] = "", is[40] = "";
        time_t t = time(NULL);
        localtime_r(&t, &now);
        tls_time(&now, false, is, sizeof(is));
        if (ASN1_TIME_to_tm(late ? X509_get0_notAfter(cert) : X509_get0_notBefore(cert), &edge) == 1)
            tls_time(&edge, true, at, sizeof(at));
        tls_why("certificate has expired or is not yet valid: current time ", is,
            late ? " is after " : " is before ", at);
    } else if (names) {
        tls_not_for(cert, tls_seen.host);
    } else {
        switch (err) {
        case X509_V_ERR_DEPTH_ZERO_SELF_SIGNED_CERT:
        case X509_V_ERR_SELF_SIGNED_CERT_IN_CHAIN:
        case X509_V_ERR_UNABLE_TO_GET_ISSUER_CERT:
        case X509_V_ERR_UNABLE_TO_GET_ISSUER_CERT_LOCALLY:
        case X509_V_ERR_UNABLE_TO_VERIFY_LEAF_SIGNATURE:
        case X509_V_ERR_CERT_UNTRUSTED:
        // A certificate that may not sign, or did not sign, is no authority.
        case X509_V_ERR_INVALID_CA:
        case X509_V_ERR_CERT_SIGNATURE_FAILURE:
        case X509_V_ERR_AKID_SKID_MISMATCH:
            tls_why("certificate signed by unknown authority", "", "", "");
            break;
        case X509_V_ERR_INVALID_PURPOSE:
            tls_why("certificate specifies an incompatible key usage", "", "", "");
            break;
        case X509_V_ERR_PATH_LENGTH_EXCEEDED:
            tls_why("too many intermediates for path length constraint", "", "", "");
            break;
        default:
            tls_why(X509_verify_cert_error_string(err), "", "", "");
        }
    }
    return 1;
}

// The request is sent to the server the URL names, at the address and port
// Go would dial, and fails with Go's words where Go's would.
static AnimaVal http_ask(const char *method, const Url *u, const char *who, const char *body, int64_t deadline) {
    bool is_https = strcmp(u->scheme.p ? u->scheme.p : "", "https") == 0;
    if (!is_https && strcmp(u->scheme.p ? u->scheme.p : "", "http") != 0) {
        char *why = url_why("unsupported protocol scheme ", (Span){u->scheme.p ? u->scheme.p : "", u->scheme.len}, "");
        AnimaVal r = http_late_or(who, deadline, why, NULL);
        free(why);
        return r;
    }
    if (u->host.len == 0) return http_late_or(who, deadline, "http: no Host in request URL", NULL);

    // The name or address to dial and its port, as Go splits the host.
    char *hostport = strdup(u->host.p);
    const char *port = is_https ? "443" : "80";
    char *colon = strrchr(hostport, ':');
    if (colon && url_port_ok((Span){colon, strlen(colon)})) {
        *colon = '\0';
        if (colon[1] != '\0') port = colon + 1;
    }
    char *host = hostport;
    size_t host_len = strlen(host);
    if (host_len >= 2 && host[0] == '[' && host[host_len - 1] == ']') { host[host_len - 1] = '\0'; host++; }

    // Go joins the two to one address and splits that again to dial it:
    // a ] in a name is where this goes wrong.
    AnimaBuf unmet = {0};
    const char *rb = strchr(host, ']');
    const char *digits = port;
    while (digits[0] == '0' && digits[1] != '\0') digits++;
    long portno = strlen(digits) > 5 ? 65536 : atol(digits);
    if (rb) {
        bool colons = strchr(host, ':') != NULL;
        buf_put(&unmet, "dial tcp: address ");
        if (colons) buf_put(&unmet, "[");
        buf_put(&unmet, host);
        buf_put(&unmet, colons ? "]:" : ":");
        buf_put(&unmet, port);
        buf_put(&unmet, !colons ? ": unexpected ']' in address" : rb[1] == ':' ? ": too many colons in address" : ": missing port in address");
    } else if (portno > 65535) {
        buf_put(&unmet, "dial tcp: address ");
        buf_put(&unmet, port);
        buf_put(&unmet, ": invalid port");
    }

    // Where to connect: the address written, this machine for no host at
    // all, or what the name is looked up to be. Only what Go takes for an
    // address is one: 127.1 and 0x7f.0.0.1 are names, and no host has them.
    HttpPeer *peers = NULL;
    size_t npeers = 0;
    if (!unmet.p) {
        int kind = url_addr(host);
        struct in_addr a4 = {0};
        struct in6_addr a6;
        if (host[0] == '\0') {
            peers = calloc(1, sizeof(HttpPeer));
            http_peer4(&peers[npeers++], a4, (int)portno, true);
        } else if (kind == 4 && inet_pton(AF_INET, host, &a4) == 1) {
            peers = calloc(1, sizeof(HttpPeer));
            http_peer4(&peers[npeers++], a4, (int)portno, false);
        } else if (kind == 6 && inet_pton(AF_INET6, host, &a6) == 1) {
            peers = calloc(1, sizeof(HttpPeer));
            http_peer6(&peers[npeers++], &a6, 0, (int)portno);
        } else {
            bool late = false;
            struct addrinfo *res = NULL;
            if (kind == 0 && http_is_name(host) && !http_is_old_addr(host)) res = http_lookup(host, deadline, &late);
            size_t found = 0;
            for (struct addrinfo *ai = res; ai; ai = ai->ai_next) found++;
            if (found > 0) peers = calloc(found, sizeof(HttpPeer));
            for (struct addrinfo *ai = res; ai; ai = ai->ai_next) {
                if (ai->ai_family == AF_INET) {
                    http_peer4(&peers[npeers++], ((struct sockaddr_in *)ai->ai_addr)->sin_addr, (int)portno, false);
                } else if (ai->ai_family == AF_INET6) {
                    struct sockaddr_in6 *sa = (struct sockaddr_in6 *)ai->ai_addr;
                    http_peer6(&peers[npeers++], &sa->sin6_addr, sa->sin6_scope_id, (int)portno);
                }
            }
            if (res) freeaddrinfo(res);
            if (npeers == 0) {
                buf_put(&unmet, "dial tcp: lookup ");
                buf_put(&unmet, host);
                buf_put(&unmet, ": no such host");
            }
        }
    }

    int fd = -1;
    if (npeers > 0) fd = http_dial(peers, npeers, deadline, &unmet);
    free(peers);
    if (fd < 0) {
        AnimaVal r = http_late_or(who, deadline, unmet.p ? unmet.p : HTTP_LATE, NULL);
        free(unmet.p); free(hostport);
        return r;
    }
    free(unmet.p);

    SSL_CTX *ctx = NULL;
    SSL *ssl = NULL;
    if (is_https) {
        // The server is who the URL says only if its certificate says so
        // and one of the system's authorities stands for it, as for Go:
        // SSL_CERT_FILE and SSL_CERT_DIR name others to both.
        ctx = SSL_CTX_new(TLS_client_method());
        SSL_CTX_set_min_proto_version(ctx, TLS1_2_VERSION);
        // The TLS 1.2 suites Go offers: a key agreed on anew for each
        // connection, with no export, RC4, 3DES or plain-RSA exchange.
        SSL_CTX_set_cipher_list(ctx,
            "ECDHE-ECDSA-AES128-GCM-SHA256:ECDHE-RSA-AES128-GCM-SHA256:"
            "ECDHE-ECDSA-AES256-GCM-SHA384:ECDHE-RSA-AES256-GCM-SHA384:"
            "ECDHE-ECDSA-CHACHA20-POLY1305:ECDHE-RSA-CHACHA20-POLY1305:"
            "ECDHE-ECDSA-AES128-SHA:ECDHE-RSA-AES128-SHA:"
            "ECDHE-ECDSA-AES256-SHA:ECDHE-RSA-AES256-SHA");
        SSL_CTX_set_default_verify_paths(ctx);
        SSL_CTX_set_verify(ctx, SSL_VERIFY_PEER, tls_refused);
        ssl = SSL_new(ctx);
        unsigned char ip[sizeof(struct in6_addr)];
        bool named = inet_pton(AF_INET, host, ip) != 1 && inet_pton(AF_INET6, host, ip) != 1;
        X509_VERIFY_PARAM *vp = SSL_get0_param(ssl);
        // A name is matched as Go matches it: a * stands for the whole
        // first label only, and the subject's common name is no name.
        X509_VERIFY_PARAM_set_hostflags(vp,
            X509_CHECK_FLAG_NO_PARTIAL_WILDCARDS | X509_CHECK_FLAG_NEVER_CHECK_SUBJECT);
        // Every certificate among the authorities stands for itself and
        // for what it signed, whether or not another signed it.
        X509_VERIFY_PARAM_set_flags(vp, X509_V_FLAG_PARTIAL_CHAIN);
        // "a.test." is the name "a.test", to the certificate and the server.
        char name[256];
        snprintf(name, sizeof(name), "%s", host);
        size_t nl = strlen(name);
        if (named && nl > 1 && name[nl - 1] == '.') name[nl - 1] = '\0';
        bool told = named ? X509_VERIFY_PARAM_set1_host(vp, name, 0) == 1
                          : X509_VERIFY_PARAM_set1_ip_asc(vp, host) == 1;
        // The name is told to the server as well; an address is not.
        if (named) SSL_set_tlsext_host_name(ssl, name);
        SSL_set_fd(ssl, fd);
        tls_seen.bad = false; tls_seen.rank = 0;
        tls_seen.host = host;
        bool late = false;
        bool shook = told && http_shake(ssl, fd, deadline, &late);
        // tls_refused lets the handshake go on to hear every reason, so
        // what it heard decides, not the handshake.
        bool refuse = !shook || tls_seen.bad || SSL_get_verify_result(ssl) != X509_V_OK;
        // The reason is this request's: no later one finds it, and a
        // thread that ends after one request leaves nothing behind.
        char *heard = tls_seen.why;
        tls_seen.why = NULL; tls_seen.host = NULL;
        if (refuse) {
            SSL_free(ssl); SSL_CTX_free(ctx); close(fd); free(hostport);
            if (!heard) return http_late_or(who, deadline, "tls handshake failed", NULL);
            AnimaBuf why = {0};
            buf_put(&why, "tls: failed to verify certificate: x509: ");
            buf_put(&why, heard);
            free(heard);
            AnimaVal refused = http_late_or(who, deadline, why.p, NULL);
            free(why.p);
            return refused;
        }
        free(heard);
    }

    // The request is as long as its path and body make it.
    AnimaBuf req = {0};
    buf_put(&req, method); buf_put(&req, " ");
    if (u->path.n == 0) buf_put(&req, "/");
    else url_put_part(&req, u->path, URL_PATH);
    if (u->force_query || u->query.n > 0) { buf_put(&req, "?"); url_put_query(&req, u->query); }
    buf_put(&req, " HTTP/1.1\r\nHost: "); buf_put(&req, u->host.p);
    buf_put(&req, "\r\nUser-Agent: anima\r\n");
    size_t body_len = body ? strlen(body) : 0;
    if (method[0] == 'P') {
        char len_line[64];
        snprintf(len_line, sizeof(len_line), "Content-Length: %zu\r\n", body_len);
        buf_put(&req, len_line);
    }
    // Who asks, if the URL says: user:password@host.
    if (u->has_user) {
        AnimaBuf pair = {0};
        if (u->user.len > 0) buf_putn(&pair, u->user.p, u->user.len);
        buf_put(&pair, ":");
        if (u->pass.len > 0) buf_putn(&pair, u->pass.p, u->pass.len);
        buf_put(&req, "Authorization: Basic ");
        buf_base64(&req, (const unsigned char *)pair.p, pair.len);
        buf_put(&req, "\r\n");
        free(pair.p);
    }
    if (body_len > 0) buf_put(&req, "Content-Type: application/json\r\n");
    buf_put(&req, "Connection: close\r\n\r\n");
    if (body_len > 0) buf_put(&req, body);
    free(hostport);
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
    HttpAnswer ans = {0};
    int got = HTTP_MORE;
    while (!timed_out) {
        if (total + 2048 > cap) { cap *= 2; raw = realloc(raw, cap); }
        int64_t left = deadline - mono_ms();
        if (left <= 0) { timed_out = true; break; }
        set_fd_timeout(fd, left);
        ssize_t n = ssl ? SSL_read(ssl, raw + total, 2048) : recv(fd, raw + total, 2048, 0);
        if (n < 0 && !ssl && errno == EINTR) continue;
        if (n <= 0) {
            if (ssl) timed_out = n < 0 && http_tls_timed_out(ssl, (int)n);
            else timed_out = n < 0 && (errno == EAGAIN || errno == EWOULDBLOCK);
            // The server has said all it will.
            if (!timed_out) got = http_answer(&ans, raw, total, true);
            break;
        }
        total += (size_t)n;
        // An answer that says where it ends is read no further: the server
        // may keep the connection open after it.
        got = http_answer(&ans, raw, total, false);
        if (got != HTTP_MORE) break;
    }
    if (ssl) { SSL_shutdown(ssl); SSL_free(ssl); SSL_CTX_free(ctx); }
    close(fd);

    // No answer is an error, as on the VM: not a response with status 200.
    // What goes wrong once the head is read is the error of reading the
    // body, which the VM gives without the request in front.
    AnimaVal answer;
    if (timed_out) {
        if (ans.in_body) answer = v_err("context deadline exceeded (Client.Timeout or context cancellation while reading body)");
        else answer = http_err(who, HTTP_LATE, NULL);
    } else if (total == 0) {
        answer = http_err(who, "EOF", NULL);
    } else if (got == HTTP_BAD && !ans.in_body) {
        AnimaBuf why = {0};
        buf_put(&why, "net/http: HTTP/1.x transport connection broken: ");
        buf_put(&why, ans.bad);
        answer = http_err(who, why.p, NULL);
        free(why.p);
    } else if (got == HTTP_BAD) {
        answer = v_err(ans.bad);
    } else {
        // The body is ans.body[0..ans.body_len): a NUL in it does not end
        // it, and makes it no str.
        AnimaVal text = text_read(ans.body, ans.body_len);
        if (v_is_variant(text, "Err")) {
            answer = text;
        } else {
            AnimaVal ent = v_entity_new("HttpResponse");
            v_entity_set(ent, "status", v_int(ans.status));
            v_entity_set(ent, "body", text.u.var->fields[0]);
            v_entity_set(ent, "ok", v_bool(ans.status >= 200 && ans.status < 300));
            answer = v_ok(ent);
        }
    }
    http_answer_free(&ans);
    free(raw);
    return answer;
}

static AnimaVal http_do(const char *method, const char *url, const char *body, int64_t timeout_ms) {
    // One time limit for the whole request, as http.Client.Timeout is.
    int64_t deadline = mono_ms() + (timeout_ms > 0 ? timeout_ms : 5000);
    Url u = {0};
    size_t named = 0;
    char *bad = url_parse(url, &u, &named);
    // A port that is empty is none.
    if (!bad && u.host.len > 0 && u.host.p[u.host.len - 1] == ':') u.host.p[--u.host.len] = '\0';
    // Two hosts Go takes are no host here, nor on the VM: an IPv6 address
    // with a zone, and a name outside ASCII, which Go rewrites before it
    // asks for it.
    if (!bad && u.host.len > 0 && strchr(u.host.p, '%')) bad = strdup("invalid host");
    for (size_t i = 0; !bad && i < u.host.len; i++) {
        if ((unsigned char)u.host.p[i] >= 0x80) bad = strdup("non-ASCII host name");
    }
    if (bad) {
        AnimaBuf b = {0};
        buf_put(&b, "parse ");
        go_quote(&b, url, named);
        buf_put(&b, ": ");
        buf_put(&b, bad);
        AnimaVal r = v_err(b.p);
        free(b.p); free(bad); url_free(&u);
        return r;
    }
    AnimaBuf shown = {0}, who = {0};
    url_shown(&u, &shown);
    buf_put(&who, method[0] == 'P' ? "Post " : "Get ");
    go_quote(&who, shown.p, shown.len);
    AnimaVal answer = http_ask(method, &u, who.p, body, deadline);
    free(shown.p); free(who.p); url_free(&u);
    return answer;
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
    AnimaVal r = text_read(b.p, b.len);
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

// ─── std.json ───

// The length of the well-formed UTF-8 sequence at s, or 0: what Go's
// unicode/utf8 takes for one.
static int utf8_seq_len(const unsigned char *s) {
    unsigned char c = s[0];
    int n = 0;
    if (c < 0x80) return 1;
    if (c >= 0xc2 && c <= 0xdf) n = 2;
    else if (c >= 0xe0 && c <= 0xef) n = 3;
    else if (c >= 0xf0 && c <= 0xf4) n = 4;
    if (n == 0) return 0;
    for (int i = 1; i < n; i++) if ((s[i] & 0xc0) != 0x80) return 0;
    if (n == 3 && ((c == 0xe0 && s[1] < 0xa0) || (c == 0xed && s[1] > 0x9f))) return 0;
    if (n == 4 && ((c == 0xf0 && s[1] < 0x90) || (c == 0xf4 && s[1] > 0x8f))) return 0;
    return n;
}

// JsonParser reads a JSON text as RFC 8259 defines one, and nothing else.
// It is the parser of the VM (jsonParser in json_parse.go), statement for
// statement, so that a text is read as the same value, or refused with the
// same words, on both backends. The end of the text is its NUL.
//
// A number that is not an int (one written with a fraction or an exponent,
// or outside 64 bits) has no value: it is an error where ints is set, and
// VAL_VOID, which is nothing a JSON text gives otherwise, where it is not.
// Of two members with one key the last is kept.
#define JSON_MAX_DEPTH 1000
typedef struct { const char *s; size_t i; bool ints; int depth; char *err; } JsonParser;

static void json_fail(JsonParser *p, const char *what) {
    if (p->err) return;
    char msg[96];
    snprintf(msg, sizeof(msg), "invalid JSON at offset %zu: %s", p->i, what);
    p->err = strdup(msg);
}

// json_unexpected fails at the byte the parser is on, or at the end.
static void json_unexpected(JsonParser *p) {
    json_fail(p, p->s[p->i] ? "unexpected character" : "unexpected end of text");
}

static void json_ws(JsonParser *p) {
    while (p->s[p->i] == ' ' || p->s[p->i] == '\t' || p->s[p->i] == '\n' || p->s[p->i] == '\r') p->i++;
}

static bool json_digit(JsonParser *p) { return p->s[p->i] >= '0' && p->s[p->i] <= '9'; }

static bool json_word(JsonParser *p, const char *w) {
    size_t n = strlen(w);
    if (strncmp(p->s + p->i, w, n) != 0) return false;
    p->i += n;
    return true;
}

// json_hex4 reads the four hex digits of a \u escape, or gives -1.
static int json_hex4(const char *s) {
    int r = 0;
    for (int i = 0; i < 4; i++) {
        char c = s[i];
        int d = c >= '0' && c <= '9' ? c - '0' : c >= 'a' && c <= 'f' ? c - 'a' + 10 : c >= 'A' && c <= 'F' ? c - 'A' + 10 : -1;
        if (d < 0) return -1;
        r = r * 16 + d;
    }
    return r;
}

// json_str reads a string, the parser being on its opening quote. NULL is
// given with an error; what is given otherwise is freed by the caller.
static char *json_str(JsonParser *p) {
    p->i++;
    AnimaBuf out = {0};
    buf_put(&out, "");
    for (;;) {
        unsigned char c = (unsigned char)p->s[p->i];
        if (c == 0) { json_unexpected(p); break; }
        if (c == '"') { p->i++; return out.p; }
        if (c < 0x20) { json_fail(p, "control character in string"); break; }
        if (c == '\\') {
            char e = p->s[p->i + 1];
            if (e == 0) { p->i++; json_unexpected(p); break; }
            if (e == 'u') {
                long cp = json_hex4(p->s + p->i + 2);
                if (cp < 0) { json_fail(p, "invalid escape"); break; }
                // A string here ends at a NUL, so it cannot hold one: the
                // text is refused on both backends.
                if (cp == 0) { json_fail(p, "NUL in string"); break; }
                p->i += 6;
                // Two escapes can be a surrogate pair; half a pair is
                // U+FFFD, and what follows it is read on its own.
                if (cp >= 0xd800 && cp <= 0xdbff) {
                    int lo = p->s[p->i] == '\\' && p->s[p->i + 1] == 'u' ? json_hex4(p->s + p->i + 2) : -1;
                    if (lo >= 0xdc00 && lo <= 0xdfff) {
                        cp = 0x10000 + ((cp - 0xd800) << 10) + (lo - 0xdc00);
                        p->i += 6;
                    } else cp = 0xfffd;
                } else if (cp >= 0xdc00 && cp <= 0xdfff) cp = 0xfffd;
                char u[5] = {0};
                if (cp < 0x80) u[0] = (char)cp;
                else if (cp < 0x800) {
                    u[0] = (char)(0xc0 | (cp >> 6));
                    u[1] = (char)(0x80 | (cp & 0x3f));
                } else if (cp < 0x10000) {
                    u[0] = (char)(0xe0 | (cp >> 12));
                    u[1] = (char)(0x80 | ((cp >> 6) & 0x3f));
                    u[2] = (char)(0x80 | (cp & 0x3f));
                } else {
                    u[0] = (char)(0xf0 | (cp >> 18));
                    u[1] = (char)(0x80 | ((cp >> 12) & 0x3f));
                    u[2] = (char)(0x80 | ((cp >> 6) & 0x3f));
                    u[3] = (char)(0x80 | (cp & 0x3f));
                }
                buf_put(&out, u);
                continue;
            }
            char ch;
            switch (e) {
                case '"': case '\\': case '/': ch = e; break;
                case 'b': ch = '\b'; break;
                case 'f': ch = '\f'; break;
                case 'n': ch = '\n'; break;
                case 'r': ch = '\r'; break;
                case 't': ch = '\t'; break;
                default: ch = 0; break;
            }
            if (ch == 0) { json_fail(p, "invalid escape"); break; }
            buf_putn(&out, &ch, 1);
            p->i += 2;
            continue;
        }
        // A byte that is not UTF-8 is U+FFFD, as json.encode writes it.
        int n = utf8_seq_len((const unsigned char *)p->s + p->i);
        if (n == 0) { buf_put(&out, "\xef\xbf\xbd"); p->i++; continue; }
        buf_putn(&out, p->s + p->i, (size_t)n);
        p->i += (size_t)n;
    }
    free(out.p);
    return NULL;
}

static AnimaVal json_number(JsonParser *p) {
    size_t start = p->i;
    if (p->s[p->i] == '-') p->i++;
    if (!json_digit(p)) { json_unexpected(p); return v_none(); }
    // A number does not start with a 0 it could do without: 01 ends at the
    // 0, and the 1 is where no character is expected.
    if (p->s[p->i] == '0') p->i++;
    else while (json_digit(p)) p->i++;
    bool is_int = true;
    if (p->s[p->i] == '.') {
        is_int = false;
        p->i++;
        if (!json_digit(p)) { json_unexpected(p); return v_none(); }
        while (json_digit(p)) p->i++;
    }
    if (p->s[p->i] == 'e' || p->s[p->i] == 'E') {
        is_int = false;
        p->i++;
        if (p->s[p->i] == '+' || p->s[p->i] == '-') p->i++;
        if (!json_digit(p)) { json_unexpected(p); return v_none(); }
        while (json_digit(p)) p->i++;
    }
    if (is_int) {
        // Only the digits of this number: strtoll would read on into the
        // text after a leading 0, which is not part of it.
        size_t k = start;
        bool neg = p->s[k] == '-';
        if (neg) k++;
        // Summed as a negative, which has room for the smallest int64.
        int64_t n = 0;
        bool fits = true;
        for (; k < p->i; k++) {
            int d = p->s[k] - '0';
            if (n < (INT64_MIN + d) / 10) { fits = false; break; }
            n = n * 10 - d;
        }
        if (fits && (neg || n != INT64_MIN)) return v_int(neg ? n : -n);
    }
    if (p->ints) { p->i = start; json_fail(p, "number is not an int"); return v_none(); }
    return v_void();
}

static AnimaVal json_value(JsonParser *p);

static bool json_open(JsonParser *p) {
    if (p->depth >= JSON_MAX_DEPTH) { json_fail(p, "nested too deep"); return false; }
    p->depth++;
    p->i++;
    json_ws(p);
    return true;
}

static AnimaVal json_array(JsonParser *p) {
    if (!json_open(p)) return v_none();
    AnimaVal out = v_list_new(0, NULL);
    if (p->s[p->i] == ']') { p->i++; p->depth--; return out; }
    for (;;) {
        json_ws(p);
        AnimaVal v = json_value(p);
        if (p->err) return v_none();
        v_list_push(out, v);
        json_ws(p);
        if (p->s[p->i] == ',') { p->i++; continue; }
        if (p->s[p->i] == ']') { p->i++; p->depth--; return out; }
        json_unexpected(p);
        return v_none();
    }
}

static AnimaVal json_object(JsonParser *p) {
    if (!json_open(p)) return v_none();
    AnimaVal out = v_map_new();
    if (p->s[p->i] == '}') { p->i++; p->depth--; return out; }
    for (;;) {
        json_ws(p);
        if (p->s[p->i] != '"') { json_unexpected(p); return v_none(); }
        char *k = json_str(p);
        if (p->err) return v_none();
        json_ws(p);
        if (p->s[p->i] != ':') { free(k); json_unexpected(p); return v_none(); }
        p->i++;
        json_ws(p);
        AnimaVal v = json_value(p);
        if (p->err) { free(k); return v_none(); }
        v_map_set(out, k, v);
        free(k);
        json_ws(p);
        if (p->s[p->i] == ',') { p->i++; continue; }
        if (p->s[p->i] == '}') { p->i++; p->depth--; return out; }
        json_unexpected(p);
        return v_none();
    }
}

static AnimaVal json_value(JsonParser *p) {
    char c = p->s[p->i];
    if (c == '"') {
        char *s = json_str(p);
        if (!s) return v_none();
        AnimaVal v = v_str(s);
        free(s);
        return v;
    }
    if (c == '{') return json_object(p);
    if (c == '[') return json_array(p);
    if (c == '-' || (c >= '0' && c <= '9')) return json_number(p);
    if (json_word(p, "true")) return v_bool(true);
    if (json_word(p, "false")) return v_bool(false);
    if (json_word(p, "null")) return v_none();
    json_unexpected(p);
    return v_none();
}

// json_parse gives the value of a JSON text, or sets *err to what is wrong
// with it (freed by the caller).
static AnimaVal json_parse(const char *s, bool ints, char **err) {
    JsonParser p = { s ? s : "", 0, ints, 0, NULL };
    json_ws(&p);
    AnimaVal v = json_value(&p);
    if (!p.err) {
        json_ws(&p);
        if (p.s[p.i]) json_fail(&p, "unexpected character");
    }
    *err = p.err;
    return v;
}

// json.decode with no type: the value of the text, whatever it is.
static AnimaVal json_decode_raw(const char *raw) {
    char *err = NULL;
    AnimaVal v = json_parse(raw, true, &err);
    if (err) { AnimaVal r = v_err(err); free(err); return r; }
    return v_ok(v);
}

// What json.decode[E] checks a value against: a type of the program, with
// the range of an int, the element type of a list, map or Option, and the
// fields and invariant of an entity. The compiler writes a table for each
// entity. What is decoded is typed as declared, so nothing is let through
// unchecked; the rule and the words are those of jsonAs in the VM.
enum { JT_INT, JT_BOOL, JT_STR, JT_LIST, JT_MAP, JT_OPTION, JT_ENTITY };
typedef struct JType JType;
typedef struct JEntity JEntity;
struct JType { int kind; bool ranged; int64_t lo; int64_t hi; const JType *elem; const JEntity *ent; };
typedef struct { const char *name; const JType *type; } JField;
struct JEntity { const char *name; const JField *fields; size_t n; bool (*inv)(AnimaVal); };

static char *json_as_msg(const char *fmt, ...) {
    va_list ap, aq;
    va_start(ap, fmt);
    va_copy(aq, ap);
    int n = vsnprintf(NULL, 0, fmt, ap);
    va_end(ap);
    char *out = malloc((size_t)n + 1);
    vsnprintf(out, (size_t)n + 1, fmt, aq);
    va_end(aq);
    return out;
}

// json_as gives raw as a value of type t, or sets *err to what is wrong.
// path names the part being checked, as E.xs[0], E.m["k"], E.inner.d.
static AnimaVal json_as(const JType *t, AnimaVal raw, AnimaBuf *path, char **err) {
    size_t at = path->len;
    switch (t->kind) {
        case JT_INT:
            if (raw.kind != VAL_INT) { *err = json_as_msg("schema error: field %s must be integer", path->p); return v_none(); }
            if (t->ranged && raw.u.i < t->lo) {
                *err = json_as_msg("schema violation: %s=%lld below minimum %lld", path->p, (long long)raw.u.i, (long long)t->lo);
                return v_none();
            }
            if (t->ranged && raw.u.i > t->hi) {
                *err = json_as_msg("schema violation: %s=%lld exceeds maximum %lld", path->p, (long long)raw.u.i, (long long)t->hi);
                return v_none();
            }
            return raw;
        case JT_BOOL:
            if (raw.kind != VAL_BOOL) { *err = json_as_msg("schema error: field %s must be bool", path->p); return v_none(); }
            return raw;
        case JT_STR:
            if (raw.kind != VAL_STR) { *err = json_as_msg("schema error: field %s must be str", path->p); return v_none(); }
            return raw;
        case JT_LIST: {
            if (raw.kind != VAL_LIST || !raw.u.list) { *err = json_as_msg("schema error: field %s must be list", path->p); return v_none(); }
            AnimaVal out = v_list_new(0, NULL);
            for (size_t i = 0; i < raw.u.list->len; i++) {
                char idx[32];
                snprintf(idx, sizeof(idx), "[%zu]", i);
                buf_put(path, idx);
                AnimaVal el = json_as(t->elem, raw.u.list->items[i], path, err);
                path->len = at; path->p[at] = 0;
                if (*err) return v_none();
                v_list_push(out, el);
            }
            return out;
        }
        case JT_MAP: {
            if (raw.kind != VAL_MAP || !raw.u.map) { *err = json_as_msg("schema error: field %s must be map", path->p); return v_none(); }
            AnimaMap *m = raw.u.map;
            // Checked in the order of the keys, so that the first thing
            // wrong is the one the VM names; kept in the order written.
            AnimaMapEntry **sorted = malloc((m->len + 1) * sizeof(*sorted));
            AnimaVal *vals = malloc((m->len + 1) * sizeof(*vals));
            for (size_t i = 0; i < m->len; i++) sorted[i] = &m->entries[i];
            qsort(sorted, m->len, sizeof(*sorted), v_entry_cmp);
            for (size_t i = 0; i < m->len && !*err; i++) {
                buf_put(path, "[");
                v_fmt_key(path, sorted[i]->key);
                buf_put(path, "]");
                vals[sorted[i] - m->entries] = json_as(t->elem, sorted[i]->val, path, err);
                path->len = at; path->p[at] = 0;
            }
            AnimaVal out = v_map_new();
            for (size_t i = 0; i < m->len && !*err; i++) v_map_set(out, m->entries[i].key, vals[i]);
            free(sorted);
            free(vals);
            return *err ? v_none() : out;
        }
        case JT_OPTION: {
            if (raw.kind == VAL_NONE) return v_none();
            AnimaVal in = json_as(t->elem, raw, path, err);
            if (*err) return v_none();
            return v_some(in);
        }
        case JT_ENTITY: {
            const JEntity *e = t->ent;
            if (raw.kind != VAL_MAP || !raw.u.map) { *err = json_as_msg("schema error: field %s must be %s", path->p, e->name); return v_none(); }
            AnimaVal ent = v_entity_new(e->name);
            for (size_t i = 0; i < e->n; i++) {
                const JField *f = &e->fields[i];
                AnimaVal fv = v_none();
                bool has = false;
                for (size_t k = 0; k < raw.u.map->len; k++) {
                    if (strcmp(raw.u.map->entries[k].key, f->name) == 0) { fv = raw.u.map->entries[k].val; has = true; break; }
                }
                if (!has && f->type->kind != JT_OPTION) {
                    *err = json_as_msg("schema error: missing field %s.%s", path->p, f->name);
                    return v_none();
                }
                buf_put(path, ".");
                buf_put(path, f->name);
                AnimaVal v = json_as(f->type, fv, path, err);
                path->len = at; path->p[at] = 0;
                if (*err) return v_none();
                v_entity_set(ent, f->name, v);
            }
            if (e->inv && !e->inv(ent)) {
                *err = json_as_msg("entity invariant violated for %s on JSON input", e->name);
                return v_none();
            }
            return ent;
        }
    }
    *err = json_as_msg("schema error: field %s is not read from JSON", path->p);
    return v_none();
}

static AnimaVal json_decode_as(const JEntity *e, const char *raw) {
    char *err = NULL;
    AnimaVal m = json_parse(raw, false, &err);
    if (err) { AnimaVal r = v_err(err); free(err); return r; }
    // Only an object is an entity: a null is not one with every field
    // absent.
    if (m.kind != VAL_MAP) {
        char *msg = json_as_msg("schema error: %s must be object", e->name);
        AnimaVal r = v_err(msg);
        free(msg);
        return r;
    }
    JType top = { JT_ENTITY, false, 0, 0, NULL, e };
    AnimaBuf path = {0};
    buf_put(&path, e->name);
    AnimaVal v = json_as(&top, m, &path, &err);
    free(path.p);
    if (err) { AnimaVal r = v_err(err); free(err); return r; }
    return v_ok(v);
}

// json_put_str writes s as Go's encoding/json does: the VM encodes with it.
// Control characters, <, > and & are escaped, U+2028 and U+2029 too, and a
// byte that is not UTF-8 becomes U+FFFD.
static void json_put_str(AnimaBuf *b, const char *str) {
    const unsigned char *s = (const unsigned char *)(str ? str : "");
    char esc[8];
    buf_put(b, "\"");
    while (*s) {
        unsigned char c = *s;
        if (c < 0x80) {
            if (c == '"' || c == '\\') { esc[0] = '\\'; esc[1] = (char)c; esc[2] = 0; }
            else if (c == '\n') strcpy(esc, "\\n");
            else if (c == '\r') strcpy(esc, "\\r");
            else if (c == '\t') strcpy(esc, "\\t");
            else if (c == '\b') strcpy(esc, "\\b");
            else if (c == '\f') strcpy(esc, "\\f");
            else if (c < 0x20 || c == 0x7f || c == '<' || c == '>' || c == '&') {
                if (c == 0x7f) { esc[0] = (char)c; esc[1] = 0; }
                else snprintf(esc, sizeof(esc), "\\u%04x", c);
            }
            else { esc[0] = (char)c; esc[1] = 0; }
            buf_put(b, esc);
            s++;
            continue;
        }
        int n = utf8_seq_len(s);
        if (n == 0) { buf_put(b, "\\ufffd"); s++; continue; }
        if (n == 3 && c == 0xe2 && s[1] == 0x80 && (s[2] == 0xa8 || s[2] == 0xa9)) {
            buf_put(b, s[2] == 0xa8 ? "\\u2028" : "\\u2029");
        } else {
            char seq[5] = {0};
            memcpy(seq, s, (size_t)n);
            buf_put(b, seq);
        }
        s += n;
    }
    buf_put(b, "\"");
}

static void json_put(AnimaBuf *b, AnimaVal v, const BoxOpen *up);

// The entries of a map or the fields of an entity, sorted by key as Go
// sorts the keys of a map.
static void json_put_entries(AnimaBuf *b, AnimaMapEntry *entries, size_t len, const BoxOpen *up) {
    AnimaMapEntry **order = malloc((len ? len : 1) * sizeof(*order));
    for (size_t i = 0; i < len; i++) order[i] = &entries[i];
    qsort(order, len, sizeof(*order), v_entry_cmp);
    buf_put(b, "{");
    for (size_t i = 0; i < len; i++) {
        if (i > 0) buf_put(b, ",");
        json_put_str(b, order[i]->key);
        buf_put(b, ":");
        json_put(b, order[i]->val, up);
    }
    buf_put(b, "}");
    free(order);
}

// A value met again inside itself is null, as on the VM.
static void json_put(AnimaBuf *b, AnimaVal v, const BoxOpen *up) {
    char num[32];
    BoxOpen here = { v_box(v), up };
    if (box_open(here.box, up)) { buf_put(b, "null"); return; }
    switch (v.kind) {
        case VAL_INT: snprintf(num, sizeof(num), "%lld", (long long)v.u.i); buf_put(b, num); break;
        case VAL_BOOL: buf_put(b, v.u.b ? "true" : "false"); break;
        case VAL_STR: json_put_str(b, v.u.s); break;
        case VAL_LIST:
            buf_put(b, "[");
            for (size_t i = 0; v.u.list && i < v.u.list->len; i++) {
                if (i > 0) buf_put(b, ",");
                json_put(b, v.u.list->items[i], &here);
            }
            buf_put(b, "]");
            break;
        case VAL_MAP:
            if (v.u.map) json_put_entries(b, v.u.map->entries, v.u.map->len, &here);
            else buf_put(b, "{}");
            break;
        case VAL_ENTITY:
            if (v.u.ent) json_put_entries(b, v.u.ent->fields, v.u.ent->len, &here);
            else buf_put(b, "{}");
            break;
        case VAL_VARIANT: {
            // Some(x) is x, which is what json.decode reads an Option
            // from; any other variant is its text. As on the VM.
            if (!v.u.var) { buf_put(b, "null"); break; }
            if (strcmp(v.u.var->name, "Some") == 0 && v.u.var->len == 1) { json_put(b, v.u.var->fields[0], &here); break; }
            AnimaBuf t = {0};
            buf_put(&t, "");
            v_fmt_in(&t, v, up);
            json_put_str(b, t.p);
            free(t.p);
            break;
        }
        default: buf_put(b, "null"); break;
    }
}

static AnimaVal json_encode(AnimaVal v) {
    AnimaBuf b = {0};
    buf_put(&b, "");
    json_put(&b, v, NULL);
    AnimaVal r = v_str(b.p);
    free(b.p);
    return r;
}
`
