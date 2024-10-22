// # Quine
// - ☑ Run the quine.
// - ☐ Check that the quine re-produces an identical value.
//
//     Make the quine take a `main` argument, and assert that it's
//     equal to the "main" binding at the end of execution.
//
//     This may work with the existing Cmp, but it also may be too slow
//     since we have many duplicated pins.  In the latter case, we will
//     need to use pin-hashing.

// # Correctness Issues
// - ✓ Bottom-safe version of the cmp jet (don't force first).

// # Minimize the Heap Layout
// - ☐ Bit-pack the nat size directly into the tag.
// - ☐ Bit-pack the law size directly into the tag.
// - ☐ Use smaller numbers for the law weights.
// - ☐ Don't store the law weights if we codegen (Law is a union type)

// # Only one mmap() region.
// - ☐ Put the JIT code directly on the laws.

// # Persist
// - ☐ Use offsets instead of pointers.
// - ☐ Second GC generation at the beginning of the mapping.
//     - Don't collect from the second generation.
//     - Move to the 2nd gen between evals (no stack)
//     - Layout should be: [2nd] [stack] [gap]? [fst]
//     - First: run normal gc to compact new data.
//         - But always copy to the right.
//     - Second: expand the second generation to make room for the new data.
//     - Third: move new data into the 2nd gen.
//         - Just traverse the 2nd gen, and move all objects.
//         - Reference into the first gen are just offset by a fixed number.
// - ☐ Use a disk-backed mmap() for the 2nd gen.
// - ☐ Sync to disk after each growth of the 2nd gen.
// - ☐ Figure out how to write snapshots + restore from snapshots.

// # WASM
// - ☐ Get this to compile to WASM.

// # No Stdlib
// - ✓ Seed loader uses only system calls, no stdlib IO.
// - ✓ Trace() does not use stdlib.
// - ☐ printv does not use stdlib.
// - ☐ repl() uses only system calls, no stdlib IO.
// - ✓ Remove all uses of malloc() (including in BSDNT).

#include <fcntl.h>
#include <stdint.h>
#define __STDC_WANT_LIB_EXT2__  1
#include <stdio.h>
#include <stdbool.h>
#include <ctype.h>
#include <stdarg.h>
#include <string.h>
#include <sys/param.h>
#include <sys/stat.h>
#include <inttypes.h>
#include <unistd.h>
#include <stdnoreturn.h>
#include "bsdnt/nn.h"
#include <sys/mman.h>

#include "linked_list.h"


// Config //////////////////////////////////////////////////////////////////////

#define BLOCK_SIZE 65536
#define STACK_SIZE 65536
#define HEAP_LOCAL ((void*)(1ULL<<24))
#define JIT_LOCAL  ((void*)(1ULL<<42))

#define TRACE_JET_MATCHES  0
#define TRACE_CALLS        0
#define TRACE_LAWS         0
#define ENABLE_GRAPHVIZ    0
#define STACK_BOUNDS_CHECK 0
#define CHECK_TAGS         0
#define CHECK_DIRECT       0
#define ENABLE_ASSERTIONS  0
#define ENABLE_VALIDATION  0
#define ENABLE_PRINTER     1

#if ENABLE_ASSERTIONS
#define ASSERT_(x) assert(x)
#else
static inline void ASSERT_(bool b) {}
#endif

// Types ///////////////////////////////////////////////////////////////////////

typedef uint64_t u64;

// Note that underlying enum number for BIG, PIN, LAW, APP are in
// sort-order.
typedef enum Type { BIG, PIN, LAW, APP, IND, MOV } Type;

typedef struct Value Value;

typedef struct Big { len_t size; } Big;
typedef struct Ind { Value *ptr; } Ind;

typedef struct Value Value;

typedef enum JetTag { J_ADD, J_SUB, J_MUL, J_DIV, J_MOD, J_DEC,
                      J_CMP, J_TRACE, J_NONE, } JetTag;

typedef struct Pin {
  Value *item;
  JetTag jet;
} Pin;

typedef struct LawWeight {
  u64 n_lets, n_calls;
} LawWeight;

typedef struct Law {
  Value *n; // Always a nat
  Value *a; // Always a nat
  Value *b;
  LawWeight w;
  // TODO
  // void (*mach_code)(void);
  // int num_cnsts;
  // // store cnsts here directly
} Law;

typedef struct App { Value *f, *g; } App;

struct Value {
  Type type;
  union { Pin p; Law l; App a; Big n; Ind i; };
};


////////////////////////////////////////////////////////////////////////////////
//  Prototypes

static len_t  ByteSz          (Value*);
static Value *normalize       (Value*);
static JetTag jet_match       (Value*);
static void   mk_app          (void);
static void   update          (u64);
static void   force           (void);
static bool   eval            (void);
static void   eval_update     (int);
static void   force_in_place  (int);
static void   frag_load       (Value**, u64, int*, u64*, u64**);
static bool   read_exp        (FILE *f);

#if ENABLE_GRAPHVIZ
static char        dot_lab[1024];
static bool        enable_graphviz = 0;
static const char *dot_dir_path = "./dot";

static char *p_ptr           (Value*);
static void  write_dot       (char*);
static void  write_dot_extra (char*, char*, Value*);
#endif

#if ENABLE_VALIDATION
void check_value (Value *v);
#else
#define check_value(v)
#endif

#if ENABLE_PRINTER
static void fprint_nat(FILE *, Value *);
static bool is_symbol(Value *);
static void fprintv(FILE*, Value*);
static void fprintv_internal(FILE *, Value *, int);
#else
#define fprint_nat(f,v)
#define fprintv(f,v)
#endif


// Utils ///////////////////////////////////////////////////////////////////////

noreturn void crash(char *s) { printf("Error: %s\n", s); exit(1); }
noreturn void pexit(char *s) { perror(s); exit(1); }

// Globals /////////////////////////////////////////////////////////////////////

#if TRACE_CALLS
int call_depth = 0; // for debugging traces
#endif

static char *loom       = NULL;
static char *heap_start = NULL;
static char *heap_end   = NULL;

static char *live_start = NULL;
static char *live_end   = NULL;
static char *hp         = NULL;

static Value **stack     = NULL;
static Value **stack_end = NULL;

// TODO: this isn't yet used, but the idea is to be able to codegen
// calls to things like push() as direct register operations.
register Value **sp asm ("r12"); // sp[0] is the top value

static Value **printer_seed  = NULL;
static Value **compiler_seed = NULL;
static Value **symbol_table  = NULL;


// GC Heap /////////////////////////////////////////////////////////////////////

void rts_init (void) {
    const int rwx = PROT_READ | PROT_WRITE | PROT_EXEC;

    const int heap_flags = MAP_PRIVATE | MAP_ANON;

    ssize_t initialLoomSz = (sizeof(Value) * STACK_SIZE) + BLOCK_SIZE;

    // Find a safe place to put the heap, then release it to avoid
    // massive core dumps.

    loom = mmap(NULL, (1ULL<<40), rwx, heap_flags | MAP_NORESERVE, -1, 0);

    if (loom == MAP_FAILED) perror("rts_init: reserve: mmap"), exit(1);

    int err = munmap(loom, (1ULL<<40));

    if (err != 0) perror("rts_init: munmap"), exit(1);

    // Then allocate the section that we need to start with using MAP_FIXED.

    loom = mmap(loom, initialLoomSz, rwx, heap_flags | MAP_FIXED, -1, 0);

    if (loom == MAP_FAILED) { perror("rts_init: mmap"); exit(1); }

    // Initialize the globals used for the stack/heap.

    stack      = (void*) loom;
    stack_end  = stack + STACK_SIZE;
    sp         = stack_end;

    heap_start = (void*) stack_end;
    heap_end   = heap_start + BLOCK_SIZE;
    live_start = heap_start;
    live_end   = heap_end;
    hp         = live_start;

}

/*
    {extend_mmap} doubles the size of the mapped heap until it covers
    the end of the live region.

    It uses MAP_FIXED to simply grow the mapped region.  We get the size
    of the current heap, and simply allocate another mmap region of the
    same size, immediately after the currently mapped region.

    Using MAP_FIXED is simple, but not robust or portable.

    This will double the heap_size *multiple times* if needed to cover
    the live area (but that shouldn't actually happen in practice).
*/
void extend_mmap (void) {
    const int rwx   = PROT_READ | PROT_WRITE | PROT_EXEC;
    const int flags = MAP_FIXED | MAP_PRIVATE | MAP_ANON;

    while (live_end > heap_end) {
        len_t heapSz = heap_end - heap_start;
        if (heap_end != mmap(heap_end, heapSz, rwx, flags, -1, 0))
            { perror("extend_mmap: mmap"); exit(1); }
        heap_end += heapSz;
    }
}

/*
    {heap_resize} sets the end of the live region to be twice as big as
    the amount of used data (after gc), rounded up to the nearest
    BLOCK_SIZE.
*/
void heap_resize (void) {
    ssize_t used_bytes = hp - live_start;
    ssize_t used_blocks = (((used_bytes + BLOCK_SIZE) - 1) / BLOCK_SIZE);
    ssize_t new_size = BLOCK_SIZE * 2 * used_blocks;
    live_end = live_start + new_size;
    extend_mmap();
}

static void cheney (void);

void gc (void) {

    // copy left
    if (heap_start < live_start) {
        hp = live_start = heap_start;
        hp = live_start;
        cheney();
        heap_resize();
        return;
    }

    // copy right
    if (heap_start == live_start) {
        ssize_t live_size = live_end - live_start;
        live_start = heap_start + (live_size * 2); // leave room for left-copy
        live_end   = live_start + live_size;
        hp         = live_start;
        extend_mmap();
        cheney();
        heap_resize();
        return;
    }

    crash("gc: impossible: bad live_start");
}

static inline void *alloc(size_t bytes) {
 again:
  char *res = hp;
  hp += bytes;
  if (hp > live_end) { gc(); goto again; }
  return res;
}

// argument is in bytes, but must be a multiple of 8.
static inline void *jit_alloc(size_t bytes) {
  crash("TODO: just put this directly into the law.");
}


// Direct Nats /////////////////////////////////////////////////////////////////

// if the high bit is set, then the remaining 63 bits should be interpreted as
// a nat. this is simpler than having to modify all pointers to mask/unmask
// their high bit.

// 2^63 - high bit
# define PTR_NAT_MASK          9223372036854775808ull
# define DIRECT_ZERO  ((Value*)9223372036854775808ull)
# define DIRECT_ONE   ((Value*)9223372036854775809ull)
# define DIRECT_TWO   ((Value*)9223372036854775810ull)

static inline bool is_direct(Value *x) {
  return (((u64) x) & PTR_NAT_MASK);
}

static inline u64 get_direct(Value *x) {
  return (u64) (((u64) x) & ~PTR_NAT_MASK);
}

static inline Value *DIRECT(u64 x) {
  #if CHECK_DIRECT
  if (x & PTR_NAT_MASK) crash("DIRECT: too big");
  #endif

  return (Value *) (x | PTR_NAT_MASK);
}


// Stack Operations ////////////////////////////////////////////////////////////

static inline ssize_t get_stack_size (void) {
  return (stack_end - sp);
}

static inline Value *deref (Value *x) {
  while (!is_direct(x) && x->type == IND) x = x->i.ptr;
  return x;
}

static inline Value *pop (void) {
  #if STACK_BOUNDS_CHECK
  if (sp >= stack_end) crash("pop: empty stack");
  #endif

  Value *res = *sp;
  sp++;
  return res;
}

static inline Value **get_ptr (u64 idx) {
  #if STACK_BOUNDS_CHECK
  if (sp+idx >= stack_end) crash("get: indexed off stack");
  #endif

  return sp+idx;
}

static inline void push_val (Value *x) {
  #if ENABLE_GRAPHVIZ
  char extra[50];
  char *x_p = p_ptr(x);
  sprintf(extra, "i[color=red];\ni -> %s", x_p);
  free(x_p);
  write_dot_extra("push_val", extra, x);
  #endif

  sp--;

  #if STACK_BOUNDS_CHECK
  if (sp < stack) crash("push_val: stack overflow");
  #endif

  *sp = x;
}

static inline Value *pop_deref (void)     { return deref(pop());       }
static inline Value *get       (u64 idx)  { return *get_ptr(idx);      }
static inline Value *get_deref (u64 idx)  { return deref(get(idx));    }

static inline void push(u64 idx) {
  #if ENABLE_GRAPHVIZ
  snprintf(dot_lab, 1024, "push %lu", idx);
  write_dot(dot_lab);
  #endif

  push_val(get_deref(idx));
}

// before: ..rest x y
// after:  ..rest y x
static inline void swap() {
  Value *n1 = pop();
  Value *n2 = pop();
  push_val(n1);
  push_val(n2);
}

static inline void slide (u64 count) {
  #if ENABLE_GRAPHVIZ
  snprintf(dot_lab, 1024, "slide %lu", count);
  write_dot(dot_lab);
  #endif

  #if STACK_BOUNDS_CHECK
  if (sp+count >= stack_end) crash("stack underflow");
  #endif

  sp[count] = *sp;
  sp += count;

  #if ENABLE_GRAPHVIZ
  snprintf(dot_lab, 1024, "post slide %lu", count);
  write_dot(dot_lab);
  #endif
}


////////////////////////////////////////////////////////////////////////////////
//  Accessors

static Value *deref(Value *x);

static inline void ck_pin(char *fn_nm, Value *x) {
  char s[14];
  sprintf(s, "%s not a PIN!", fn_nm);
  if (x->type != PIN) crash(s);
}

// we allow PIN LAWs
static inline void ck_law(char *fn_nm, Value *x) {
  char s[28];
  sprintf(s, "%s not a LAW or PIN-LAW!", fn_nm);
  if (x->type == LAW) return;
  if (x->type == PIN) {
    return ck_law(fn_nm, x->p.item);
  }
  crash(s);
}

static inline void ck_app(char *fn_nm, Value *x) {
  char s[15];
  sprintf(s, "%s not an APP!", fn_nm);
  if (x->type != APP) crash(s);
}

static inline void ck_nat(char *fn_nm, Value *x) {
  char s[14];
  sprintf(s, "%s not a BIG!", fn_nm);
  if (x->type != BIG) crash(s);
}

static inline void ck_ind(char *fn_nm, Value *x) {
  char s[14];
  sprintf(s, "%s not a IND!", fn_nm);
  if (x->type != IND) crash(s);
}

static inline Type TY(Value *x) {
  if (is_direct(x)) return BIG;
  return x->type;
}

#define SI static inline

SI bool IS_NAT(Value *x) { return (is_direct(x)  || x->type == BIG); }
SI bool IS_LAW(Value *x) { return (!is_direct(x) && x->type == LAW); }
SI bool IS_APP(Value *x) { return (!is_direct(x) && x->type == APP); }

static inline Value *IT(Value *x) {
  x = deref(x);
  #if CHECK_TAGS
  ck_pin("IT", x);
  #endif
  return x->p.item;
};

static inline Value *NM(Value *x) {
  x = deref(x);
  #if CHECK_TAGS
  ck_law("NM", x);
  #endif
  if (x->type == PIN) return NM(x->p.item);
  return x->l.n;
}

static inline Value *AR(Value *x) {
  x = deref(x);
  #if CHECK_TAGS
  ck_law("AR", x);
  #endif
  if (x->type == PIN) return AR(x->p.item);
  return x->l.a;
}

static inline Value *BD(Value *x) {
  x = deref(x);
  #if CHECK_TAGS
  ck_law("BD", x);
  #endif
  if (x->type == PIN) return BD(x->p.item);
  return x->l.b;
}

static inline Law FUNC(Value *x) {
  x = deref(x);
  if (x->type == PIN) return FUNC(x->p.item);
  return x->l;
}

static inline Value *HD(Value *x) {
  x = deref(x);
  #if CHECK_TAGS
  ck_app("HD", x);
  #endif
  return x->a.f;
};

static inline Value *TL(Value *x) {
  x = deref(x);
  #if CHECK_TAGS
  ck_app("TL", x);
  #endif
  return x->a.g;
};

static inline Value *IN(Value *x) {
  #if CHECK_TAGS
  ck_ind("IN", x);
  #endif
  return x->i.ptr;
};

static inline len_t WID(Value *v) {
  return v->n.size;
}

static inline word_t *BUF(Value *v) {
  return (void*) (&(v->n.size) + 1);
}

#define BIND_BUF_PTR(nm, v) \
  word_t tmp;               \
  char *nm;                 \
  if (is_direct(v)) {       \
    tmp = get_direct(v);    \
    nm = (char*) &tmp;      \
  } else {                  \
    nm = (char*) BUF(v);    \
  }

////////////////////////////////////////////////////////////////////////////////
//  Construction

/*
    WARNING!  It is not acceptable to allocate between
    start_bignat_alloc() and end_bignat_alloc() (or abort_bignat_alloc()).
    The finalizing functions *shrink* the initial allocation, and all hell
    will break loose if the nat is no longer that last thing on the heap.
*/

// just allocates the space. caller must fill buf.
Value *start_bignat_alloc(size_t num_words) {
  // tag size words..
  Value *res = (Value *)alloc(8 * (2 + num_words));
  res->type   = BIG;
  res->n.size = num_words;
  return res;
}

static inline void abort_bignat_alloc(Value *v) {
  hp -= ((2 + v->n.size) * 8);
}

// shrinks a "candidate" bignat and DECREASES THE SIZE OF THE HEAP so
// that the next thing will be allocated in the right place.
Value *end_bignat_alloc(Value *v) {
  size_t old_sz = v->n.size;
  size_t sz     = old_sz;
  word_t *buf   = BUF(v);

  while (sz && buf[sz - 1] == 0) sz--;

  if (sz == 0) {
    abort_bignat_alloc(v);
    return DIRECT_ZERO;
  }

  if (sz == 1 && 0 == (buf[0] >> 63)) {
    abort_bignat_alloc(v);
    return DIRECT(buf[0]);
  }

  if (sz == old_sz) return v;

  v->n.size = sz;            // shrink size
  hp -= (8 * (old_sz - sz)); // shrink heap
  return v;
}

// This needs to exist for now because the JIT generates calls to it.
void push_direct(u64 x) { return push_val(DIRECT(x)); }

static inline void push_word(u64 x) {
  if (!(x & PTR_NAT_MASK)) {
    push_val((Value *) (x | PTR_NAT_MASK));
    return;
  }

  Value *res = (Value *)alloc(3 * 8);
  res->type   = BIG;
  res->n.size = 1;
  BUF(res)[0] = x;
  push_val(res);
}

static inline Value *a_Pin(Value *item) {
  push_val(item);
  Value *res = (Value *)alloc(24); // tag, item, jet_tag
  item = pop();
  res->type = PIN;
  JetTag jet = jet_match(item);
  res->p = (Pin){ .item = item, .jet = jet };
  return res;
}

static inline Value *a_Law(Law l) {
  push_val(l.n);
  push_val(l.a);
  push_val(l.b);
  // tag name args body weights
  Value *res = (Value *)alloc(32 + sizeof(LawWeight));
  l.b = pop();
  l.a = pop();
  l.n = pop();
  *res = (Value){ .type = LAW, .l = l };
  return res;
}

////////////////////////////////////////////////////////////////////////////////
//  Nat Operators

int less=0, equals=1, greater=2;

static inline int cmp_direct(u64 a, u64 b) {
  if (a == b) return equals;
  if (a < b) return less;
  return greater;
}

static inline int big_cmp(Value *a, Value *b) {
  if (WID(a) != WID(b)) {
    return (WID(a) < WID(b)) ? less : greater;
  }

  int nnres = nn_cmp_m(BUF(a), BUF(b), WID(a));

  if (nnres < 0) return less;
  if (nnres == 0) return equals;
  return greater;
}

int cmp_recur(Value *a, Value *b) {
 tail_recur:
  a=deref(a), b=deref(b);

  if (is_direct(a))
    return (!is_direct(b))
             ? less
             : cmp_direct(get_direct(a), get_direct(b));

  if (is_direct(b)) return greater;

  if (a->type < b->type) return less;
  if (a->type > b->type) return greater;

  switch (a->type) {
  case BIG:
    return big_cmp(a, b);

  case PIN:
    a=IT(a); b=IT(b); goto tail_recur;

  case LAW:
    {
      int ord;
      if (b->type != LAW) return less;
      ord = cmp_recur(NM(a), NM(b));
      if (ord != 1) return ord;
      ord = cmp_recur(AR(a), AR(b));
      if (ord != 1) return ord;
      a=BD(a); b=BD(b); goto tail_recur;
    }

  case APP:
    {
      int ord = cmp_recur(HD(a), HD(b));
      if (ord != 1) return ord;
      a=TL(a); b=TL(b); goto tail_recur;
    }
  default:
    crash("cmp: impossible");
  }
}

// fast path for direct atoms, fallback to full cmp routine.
static inline int cmp_normalized(Value *a, Value *b) {
  if (is_direct(a) && is_direct(b))
    return cmp_direct(get_direct(a), get_direct(b));

  return cmp_recur(a,b);
}

static inline int cmp_lazy() {
  tail_recur:
    eval_update(0);
    eval_update(1); // TODO: which order does the PLAN eval in?
    Value *a = *sp++;
    Value *b = *sp++;

    if (a == b) return equals; // pointer-equality shortcut

    int aTy=TY(a), bTy=TY(b);

    if (aTy != APP) {
        if (bTy != APP) return cmp_normalized(a, b);
        return less;
    }

    if (bTy != APP) return greater;

    push_val(TL(b));
    push_val(TL(a));
    push_val(HD(b));
    push_val(HD(a));

    int ord = cmp_lazy();
    if (ord != 1) { sp += 2; return ord; }
    goto tail_recur;
}

static inline bool LT(Value *a, Value *b) {
  return cmp_normalized(a,b) == 0;
}

static inline bool GT(Value *a, Value *b) {
  return cmp_normalized(a,b) == 2;
}

static inline bool LTE(Value *a, Value *b) {
  return cmp_normalized(a,b) != 2;
}

static inline bool GTE(Value *a, Value *b) {
  return cmp_normalized(a,b) != 0;
}

static inline bool EQ(Value *a, Value *b) {
  return cmp_normalized(a,b) == 1;
}

static inline bool NEQ(Value *a, Value *b) {
  return cmp_normalized(a,b) != 1;
}

static inline bool EQZ(Value *x) {
   return (x == DIRECT_ZERO);
}

static inline bool EQ1(Value *x) {
  return (x == DIRECT_ONE);
}

static inline bool EQ2(Value *x) {
  return (x == DIRECT_TWO);
}

void WordPlusWord(u64 a, u64 b) {
  if (b <= (UINT64_MAX - a)) {
    push_word(a + b);
    return;
  }

  // overflow
  Value *res = start_bignat_alloc(2);
  u64 *buf = BUF(res);
  buf[0] = a + b;
  buf[1] = 1;
  push_val(res); // no need to push_val_end because never too small.
}

void BigPlusWord(u64 word, Value *big) {
  u64 bigSz = WID(big);

  // this is probably unnecessary, but is defensive against bad input.
  if (is_direct(big)) {
    WordPlusWord(word, get_direct(big));
    return;
  }
  if (bigSz == 1) {
    WordPlusWord(word, BUF(big)[0]);
    return;
  }

  u64 newSz = bigSz + 1;

  push_val(big);
  Value *res = start_bignat_alloc(newSz); // gc
  big        = pop();

  word_t carry    = nn_add1(BUF(res), BUF(big), bigSz, word);
  BUF(res)[bigSz] = carry;
  push_val(end_bignat_alloc(res));
}

// invariant: a.size >= b.size
// stack before: ..rest b a
// stack after:  ..rest (a+b)
void BigPlusBig(Value *a, Value *b) {
  u64 aSize = WID(a);
  u64 bSize = WID(b);

  if (aSize == 1) {
    if (bSize == 1) {
      WordPlusWord(BUF(a)[0], BUF(b)[0]);
      return;
    }

    BigPlusWord(BUF(a)[0], b);
    return;
  }

  if (bSize == 1) {
    BigPlusWord(BUF(b)[0], a);
    return;
  }

  long new_size = MAX(aSize, bSize) + 1;

  push_val(b);
  push_val(a);
  Value *res = start_bignat_alloc(new_size);
  a = pop();
  b = pop();

  if (aSize < bSize) {
    Value *tmp = a;
    a = b;
    b = tmp;
  }

  word_t *buf = BUF(res);
  word_t c = nn_add_c(buf, BUF(a), a->n.size, BUF(b), b->n.size, 0);
  buf[new_size - 1] = c;
  push_val(end_bignat_alloc(res));
}

// arguments must both have already been evaluated and coerced into nats.
void Add() {
  Value *a = pop_deref();
  Value *b = pop_deref();

  u64 aSmall = get_direct(a);
  u64 bSmall = get_direct(b);

  if (is_direct(a)) {
    if (is_direct(b)) {
      // no need to handle overflow, since u63 + u63 always fits in a u64.
      push_word(aSmall + bSmall);
      return;
    }

    BigPlusWord(aSmall, b);
    return;
  }

  if (is_direct(b)) {
    BigPlusWord(bSmall, a);
    return;
  }

  BigPlusBig(a, b);
}

void BigMinusDirect(Value *big, u64 direct) {
  u64 bigSz = big->n.size;
  push_val(big);                           // save
  Value *res  = start_bignat_alloc(bigSz); // gc
  big         = pop();                     // reload
  word_t *buf = BUF(res);
  word_t c = nn_sub1(buf, BUF(big), bigSz, direct);
  // a positive borrow (nonzero `c`) should only be possible if we
  // underflowed a single u64. our invariant is to convert to SMALL when we
  // reach 1 u64, so we should never encounter this case.
  ASSERT_ (c == 0);
  push_val(end_bignat_alloc(res));
}

void Dec() {
  #if ENABLE_GRAPHVIZ
  write_dot_extra("<Dec>", "", NULL);
  #endif

  Value *v = pop_deref();

  if (is_direct(v)) {
    u64 n = get_direct(v);
    push_val( (n == 0) ? DIRECT_ZERO : DIRECT(n - 1) );
    // the result is always direct because (x/u63 - 1) is always a u63
    // unless x==0.
    goto end;
  }

  BigMinusDirect(v, 1);

 end:
  #if ENABLE_GRAPHVIZ
  write_dot_extra("</Dec>", "", NULL);
  #endif
}

void Sub() {
  Value *a = pop();
  Value *b = pop();

  u64 aSmall = get_direct(a);
  u64 bSmall = get_direct(b);

  if (is_direct(a)) {
    if (is_direct(b)) {
      if (bSmall >= aSmall) {
        push_val(DIRECT_ZERO);
        return;
      }
      push_word(aSmall - bSmall);
      return;
    }
    push_val(DIRECT_ZERO);
    return;
  }

  if (is_direct(b)) {
    BigMinusDirect(a, bSmall);
    return;
  }

  u64 aSz = a->n.size;
  u64 bSz = a->n.size;

  if (aSz < bSz) {
    push_val(DIRECT_ZERO);
    return;
  }

  // Big - Big

  push_val(b);
  push_val(a);
  Value *res  = start_bignat_alloc(aSz); // gc
  a = pop();
  b = pop();

  word_t *buf = BUF(res);

  word_t borrow = nn_sub_c(buf, BUF(a), a->n.size, BUF(b), b->n.size, 0);
  if (borrow) {
    abort_bignat_alloc(res);
    push_val(DIRECT_ZERO);
  } else {
    push_val(end_bignat_alloc(res));
  }
}

void DirectTimesDirect(u64 a, u64 b) {
  if (a==0 || b==0) {
    push_val(DIRECT_ZERO);
    return;
  }

  u64 res = a * b;

  // if no overflow
  if ((res / a) == b) { // TODO does this always work?
    push_word(res);
    return;
  }

  Value *ret  = start_bignat_alloc(2); // gc
  word_t *buf = BUF(ret);
  buf[1] = nn_mul1(buf, &a, 1, b);
  push_val(end_bignat_alloc(ret));
}

// call alloc to reserve words
// fill in data
// truncate
// decrease hp.

void BigTimesDirect(u64 small, Value *big) {
  u64 newSz = big->n.size + 1;
  push_val(big);                          // save pointer to stack
  Value *res = start_bignat_alloc(newSz); // gc
  big = pop();                            // reload pointer
  word_t *buf = BUF(res);
  nn_zero(buf, newSz);
  word_t carry = nn_mul1(buf, BUF(big), big->n.size, small);
  buf[big->n.size] = carry;
  push_val(end_bignat_alloc(res));
}

void BigTimesBig(Value *a, Value *b) {
  long new_size = a->n.size + b->n.size;
  push_val(a);                               // save pointer
  push_val(b);                               // save pointer
  Value *res = start_bignat_alloc(new_size); // gc
  b = pop();                                 // reload pointer
  a = pop();                                 // reload pointer
  word_t *buf = BUF(res);
  nn_zero(buf, new_size);
  nn_mul_classical(buf, BUF(a), a->n.size, BUF(b), b->n.size);
  push_val(end_bignat_alloc(res));
}

void Mul() {
  Value *a = pop();
  Value *b = pop();

  u64 aSmall = get_direct(a);
  u64 bSmall = get_direct(b);

  if (is_direct(a)) {
    if (is_direct(b)) DirectTimesDirect(aSmall, bSmall);
    else BigTimesDirect(aSmall, b);
    return;
  }

  if (is_direct(b)) BigTimesDirect(bSmall, a);
  else BigTimesBig(a, b);
}

void DivModDirectDirect(u64 a, u64 b) {
  if (b == 0) {
    // we could crash here instead
    push_val(DIRECT_ZERO); // mod
    push_val(DIRECT_ZERO); // div
    return;
  }

  push_word(a % b); // mod
  push_word(a / b); // div
}

void DivModBigDirect(Value *a, u64 b) {
  if (b == 0) {
    // we could crash here instead
    push_val(DIRECT_ZERO); // mod
    push_val(DIRECT_ZERO); // div
    return;
  }
  long sz = a->n.size;

  push_val(a);                         // save a
  Value *res = start_bignat_alloc(sz); // gc
  a = pop();                           // restore a

  word_t *buf = BUF(res);
  nn_zero(buf, sz);
  word_t mod = nn_divrem1_simple(buf, BUF(a), sz, b);
  push_val(end_bignat_alloc(res)); // div
  push_word(mod);                  // mod
  swap();
  // need the swap() becuause push_word(mod) can invalidate
}

void DivModBigBig(Value *a, Value *b) {
  long aSz = WID(a);
  long bSz = WID(b);

  if (aSz < bSz) {
    push_val(a);           // mod
    push_val(DIRECT_ZERO); // div
    return;
  }

  // Copy a's words into a working buffer (which will be mutated by
  // `nn_divrem`).  TODO HACK: can stack overflow.
  word_t tmp[aSz];
  nn_copy(tmp, BUF(a), aSz);

  long sz = aSz - bSz + 1;

  push_val(b);                            // save
  Value *divres = start_bignat_alloc(sz); // gc
  b = pop();                              // restore

  word_t *buf = BUF(divres);
  nn_zero(buf, sz);

  nn_divrem(buf, tmp, aSz, BUF(b), bSz);

  push_val(end_bignat_alloc(divres));

  Value *modres = start_bignat_alloc(bSz);
  nn_copy(BUF(modres), tmp, bSz);
  push_val(end_bignat_alloc(modres));

  swap();
}

// stack before: ..rest b a
// stack after:  ..rest (a%b) (a/b)
void DivMod() {
  Value *a = pop();
  Value *b = pop();

  u64 aSmall = get_direct(a);
  u64 bSmall = get_direct(b);

  if (is_direct(a)) {
    if (is_direct(b)) DivModDirectDirect(aSmall, bSmall);
    else {
      push_val(a);           // mod
      push_val(DIRECT_ZERO); // div
    }
    return;
  }

  if (is_direct(b)) DivModBigDirect(a, bSmall);
  else DivModBigBig(a, b);
}

// stack before: ..rest b a
// stack after:  ..rest (a/b)
void Div() {
  DivMod();
  slide(1);
}

// stack before: ..rest b a
// stack after:  ..rest (a%b)
void Mod() {
  DivMod();
  pop();
}

////////////////////////////////////////////////////////////////////////////////
//  Jets

typedef struct Jet {
  Value *name; // if this is ever not direct, a more complex solution
               // will be required.
  u64 arity;
  JetTag tag;
} Jet;

static inline void to_nat(int i) {
  eval_update(i);
  Value **p = get_ptr(i);
  if (!IS_NAT(*p)) { *p = DIRECT_ZERO; }
}

static inline void force_in_place(int i) {
  push(i);
  force();
  Value **p = get_ptr(i);
  *p = deref(*p);
}

// causes a stack slot to be updated (and dereferenced) in place,
// otherwise leaving the stack shape the same as it was before.
void eval_update(int i) {
  Value **p = get_ptr(i);
 again:
  #if ENABLE_GRAPHVIZ
  write_dot_extra("<eval_update>", "", NULL);
  #endif
  if (is_direct(*p)) return;
  switch ((**p).type) {
  case IND:
    *p = deref(*p); // update the stack slot to not be indirect.
    goto again;
  case APP:
    push(i);
    bool did_eval = eval();
    if (did_eval) {
      update(i+1);
      *p = deref(*p); // never leave an indirection on the stack.
    } else {
      pop();
    }
    return;
  default:
    return;
  }
}

#define ADD   (Value*)9223372036861355073ULL
#define SUB   (Value*)9223372036861228371ULL
#define MUL   (Value*)9223372036861883725ULL
#define DIV   (Value*)9223372036862536004ULL
#define MOD   (Value*)9223372036861357901ULL
#define DEC   (Value*)9223372036861289796ULL
#define CMP   (Value*)9223372036862143811ULL
#define TRACE (Value*)9223372472313803348ULL

#define NUM_JETS 8
Jet jet_table[NUM_JETS] =
  { (Jet) { .name = ADD,   .arity = 2, .tag = J_ADD   }
  , (Jet) { .name = SUB,   .arity = 2, .tag = J_SUB   }
  , (Jet) { .name = MUL,   .arity = 2, .tag = J_MUL   }
  , (Jet) { .name = DIV,   .arity = 2, .tag = J_DIV   }
  , (Jet) { .name = MOD,   .arity = 2, .tag = J_MOD   }
  , (Jet) { .name = DEC,   .arity = 1, .tag = J_DEC   }
  , (Jet) { .name = CMP,   .arity = 2, .tag = J_CMP   }
  , (Jet) { .name = TRACE, .arity = 2, .tag = J_TRACE }
  };

////////////////////////////////////////////////////////////////////////////////
//  Seeds

void frag_load_cell(Value **tab, u64 tabSz, int *use, u64 *acc, u64 **mor) {
  frag_load(tab, tabSz, use, acc, mor); // .. f
  frag_load(tab, tabSz, use, acc, mor); // .. f x
  mk_app();                             // .. (f x)
}

u64 u64_bits (u64 w) {
  if (!w) { return 0; }
  return 64 - __builtin_clzll(w);
}

void frag_load(Value **tab, u64 tabSz, int *use, u64 *acc, u64 **mor) {
  u64 isCell = ((*acc >> *use) & 1ULL);

  // move forward by one bit.
  (*use)++;
  if (*use == 64) {
    *use = 0;
    *acc = **mor;
    *mor = (*mor)+1;
  }

  if (isCell) {
    frag_load_cell(tab, tabSz, use, acc, mor);
    return;
  }

  // `tmp` is the remaining bits from acc (high bits) combined
  // with the low bits of the next word.  We mask out the `refSz`
  // low bits from this to get the index into the backrefs table.

  u64 maxref = tabSz-1;
  u64 refSz = u64_bits(maxref);
  int remain = 64 - *use;
  u64 tmp = (remain==64) ? *acc : ((*acc >> *use) | (**mor << remain));// combine
  u64 ref = tmp & ((1ULL << refSz) - 1ULL);                            // mask

  // move forward by refSz bits.
  *use += refSz;
  if (*use >= 64) {
    *use -= 64;
    *acc = **mor;
    *mor = (*mor)+1;
  }

  push_val(tab[ref]);
}

void seed_load(u64 *inpbuf) {
  u64 n_holes = inpbuf[0];
  u64 n_bigs  = inpbuf[1];
  u64 n_words = inpbuf[2];
  u64 n_bytes = inpbuf[3];
  u64 n_frags = inpbuf[4];

  if (n_holes > 1) {
    fprintf(stderr, "file is just one seed, expected seedpod\n");
    exit(5);
  }

  u64 n_entries = n_bigs + n_words + n_bytes + n_frags + n_holes;

  if (n_entries == 0) crash("empty seed");

  // clever: store working table on stack to make everything GC safe.

  sp -= n_entries; // grow the stack
  for (int i=0; i<n_entries; i++) sp[i] = DIRECT_ZERO;
  Value **tab = sp;

  Value **next_ref = tab;

  if (n_holes) {
    *next_ref++ = a_Pin(DIRECT_ZERO);
  }

  // How big are the bignats?
  u64 bigwidths[n_bigs];
  for (int i=0; i<n_bigs; i++) {
    bigwidths[i] = inpbuf[5+i];
  }

  int used = 5 + n_bigs; // number of words used

  for (int i=0; i<n_bigs; i++) {
    u64 wid       = bigwidths[i];
    Value *bigres = start_bignat_alloc(wid);
    memcpy(BUF(bigres), inpbuf+used, wid*sizeof(u64));
    *next_ref++ = end_bignat_alloc(bigres);
    used += wid;
  }

  for (int i=0; i<n_words; i++) {
    push_word(inpbuf[used++]);
    *next_ref++ = pop();
  }

  {
    uint8_t *byte_buf = (void*) (inpbuf + used);
    for (int i=0; i<n_bytes; i++) {
      push_word(byte_buf[i]);
      *next_ref++ = pop();
    }
    used += (n_bytes / 8);
  }

  int use = 8 * (n_bytes%8);
  u64 acc = inpbuf[used];
  u64 *more = &inpbuf[used+1];

  for (int i=0; i<n_frags; i++) {
    u64 tabSz = (next_ref - tab);
    frag_load_cell(tab, tabSz, &use, &acc, &more);
    *next_ref++ = pop();
  }

  sp += (n_entries - 1); // drop everything besided the final entry.

  check_value(get(0));
  force_in_place(0);
  check_value(get(0));
}

void load_seed_file (const char *filename) {
  int fd = open(filename, O_RDONLY);
  if (fd < 0) pexit("open");

  struct stat statbuf;
  if (0 != fstat(fd, &statbuf)) pexit("fstat");

  u64 *buf = mmap(NULL, statbuf.st_size, PROT_READ, MAP_SHARED, fd, 0);
  if (buf == MAP_FAILED) pexit("mmap");

  if (0 != close(fd)) pexit("close");

  seed_load(buf);

  munmap(buf, statbuf.st_size);
}


////////////////////////////////////////////////////////////////////////////////
//  GC

static inline size_t alloc_size(Value *x) {
  // never direct (because this is called on an actual heap object).
  switch (x->type) {
  case BIG: return (8 * (2 + WID(x)));
  case APP: return 24;
  case IND: return 24;
  case PIN: return 24;
  case LAW: return 32 + sizeof(LawWeight);
  default:  crash("alloc_size: bad tag");
  }
}

Value *gc_copy(Value *x) {
  if (x == NULL || is_direct(x))
    return x;

  char *xc = (char*) x;

  // if this points into the tospace, we don't need to copy.
  if (xc >= live_start && xc < live_end)
    return x;

  if (x->type == MOV) return x->i.ptr;

  size_t sz = alloc_size(x);

  // copy + bump heap size
  Value *res = (Value*) hp;
  memcpy(hp, x, sz);
  hp += sz;

  // tell further references where to find the new pointer.
  x->type  = MOV;
  x->i.ptr = res;

  return res;
}

// Input is always a heap object, so never direct and never null.
static inline void gc_copy_refs(Value *x) {
  switch (x->type) {
  case PIN:
    x->p.item = gc_copy(x->p.item);
    break;
  case LAW:
    x->l.n = gc_copy(x->l.n);
    x->l.a = gc_copy(x->l.a);
    x->l.b = gc_copy(x->l.b);
    break;
  case APP:
    x->a.f = gc_copy(x->a.f);
    x->a.g = gc_copy(x->a.g);
    break;
  case BIG:
    break; // no refs
  case IND:
    x->i.ptr = gc_copy(x->i.ptr);
    break;
  default:
    fprintf(stderr, "gc_copy_refs: bad value: ptr=%p, tag=%d\n", x, x->type);
    crash("gc_copy_refs: impossible");
  }
}

static void cheney (void) {
  for (Value **p = sp; p < stack_end; p++) *p = gc_copy(*p);

  for (char *iter = live_start;
       iter < hp;
       iter += alloc_size((Value*)iter)
      ) {
    gc_copy_refs((Value*) iter);
  }
}

////////////////////////////////////////////////////////////////////////////////
//  Interpreter

static void update(u64 idx) {
  #if ENABLE_GRAPHVIZ
  snprintf(dot_lab, 1024, "update %lu", idx);
  write_dot(dot_lab);
  #endif

  Value *head = get_deref(0);
  Value *v    = get_deref(idx);
  if (head != v) {
    // no update needed if equal, and IND on self would form a cycle.
    v->type  = IND;
    v->i.ptr = head;
  }
  pop();
}


static inline void clone() {
  #if ENABLE_GRAPHVIZ
  write_dot("clone");
  # endif

  push_val(get_deref(0));
}

// before: ..rest f x
// after:  ..rest (f x)
static inline void mk_app() {
  #if ENABLE_GRAPHVIZ
  write_dot("mk_app");
  #endif

  Value *res = (Value *)alloc(24);
  res->type = APP;
  res->a.g = pop();
  res->a.f = pop();
  push_val(res);
}

// before: ..rest x f
// after:  ..rest (f x)
static inline void mk_app_rev (void) {
  #if ENABLE_GRAPHVIZ
  write_dot("mk_app_rev");
  #endif

  Value *res = (Value *)alloc(24);
  res->type = APP;
  res->a.f = pop();
  res->a.g = pop();
  push_val(res);
}

static inline void mk_pin (void) {
  #if ENABLE_GRAPHVIZ
  write_dot("mk_pin");
  #endif

  force_in_place(0);
  Value *top = pop();
  Value *p = a_Pin(normalize(top));
  push_val(p);
}

void weigh_law(bool on_spine, LawWeight *out, Value *x) {
 again:
  if (TY(x) != APP) return;                       // neither a let nor a call
  Value *car = HD(x);

  if (TY(car) != APP) return;                     // neither a let nor a call
  Value *caar = HD(car);

  if (on_spine && EQ1(caar)) {                    // ((1 x) b)
    out->n_lets++;                                // this is a let
    weigh_law(0, out, TL(car));                   // weigh the let expr
    x = TL(x);                                    // weigh the let body
    goto again;
  }

  if (EQZ(caar)) {                                // ((0 f) x)
    out->n_calls++;                               // this is a call
    on_spine = false;                             // no more lets
    weigh_law(0, out, TL(car));                   // weigh the call function
    x = TL(x);                                    // weigh the call argument
    goto again;
  }

  return;                                         // neither a let nor a call
}

Value *normalize (Value *v) {
 again:
  if (is_direct(v)) return v;
  switch (v->type) {
  case IND: v = IN(v); goto again;
  case APP:
    v->a.f = normalize(v->a.f);
    v->a.g = normalize(v->a.g);
    return v;
  default: // P/L/N: already normalized
    return v;
  }
}

void push_jit_fn_ptrs(void) {
  push_val(DIRECT((word_t) &slide));
  push_val(DIRECT((word_t) &update));
  push_val(DIRECT((word_t) &alloc));
  push_val(DIRECT((word_t) &mk_app_rev));
  push_val(DIRECT((word_t) &mk_app));
  push_val(DIRECT((word_t) &push));
  push_val(DIRECT((word_t) &push_direct));
  push_val(DIRECT((word_t) &eval));
  // [.. slide update alloc mkApRev mkAp push pushDirect eval]
}

len_t direct_byte_width(word_t w) {
  // printf("word=%lu, bits=%lu\n", w, u64_bits(w));
  return (u64_bits(w) + 7) / 8;
}


len_t ByteSz(Value *bar) {
    if (is_direct(bar)) {
      return direct_byte_width(get_direct(bar));
    }
    int sz           = WID(bar);
    word_t last_word = BUF(bar)[sz-1];
    return ((sz-1) * 8) + direct_byte_width(last_word);
}

len_t BarSz(Value *bar) {
  ASSERT_(IS_NAT(bar));
  len_t str_len = ByteSz(bar);
  if (str_len == 0) crash("BarSz: given zero");
  return str_len - 1;
}

void mk_law() {
  #if ENABLE_GRAPHVIZ
  write_dot("mk_law");
  #endif

  force_in_place(2);          // b
  to_nat(0);                  // a
  to_nat(1);                  // n

  Value *n = pop_deref();
  Value *a = pop_deref();
  Value *b = normalize(pop_deref());

  if (compiler_seed && false) {
    push_val(n);
    push_val(a);
    push_val(b);
                              // [.. n a b]
    push(0);                  // [.. n a b b]
    push(2);                  // [.. n a b b a]
    push_jit_fn_ptrs();       // [.. n a b b a 8xFnPtr]

    push_val(*compiler_seed); // [.. n a b b a 8xFnPtr jit]

    for (int i=0; i<10; i++) {
      mk_app_rev();
    }                         // [.. n a b (jit ...)]
    force_in_place(0);        // [.. n a b jitRes@(machBar, cnsts)]

    Value *pair    = pop();   // [.. n a b]
    Value *machBar = deref(TL(HD(pair)));
    // Value *cnsts   = TL(pair);
    fprintf(stderr, "pair: ");
    fprintv(stderr, pair);
    fprintf(stderr, "\n");

    fprintf(stderr, "machBar: ");
    fprintv(stderr, machBar);
    fprintf(stderr, "\n");

    word_t *code  = BUF(machBar);
    len_t codeSz  = BarSz(machBar);
    char *codePtr = jit_alloc(codeSz);
    memcpy(codePtr, code, codeSz);

    fprintf(stderr, "code_gen nm: ");
    fprintv(stderr, get(2));
    fprintf(stderr, "\n");
    fprintf(stderr, "codePtr: %p (sz=%lu)\ncode: 0x", codePtr, codeSz);
    for (int i = 0; i < codeSz; i++) {
      uint8_t byte = ((char*)code)[i];
      fprintf(stderr, "%02x", byte);
    }
    fprintf(stderr, "\n");

    crash("lol");

    // prereq:
    // - mmap a new heap area to put executable code into.
    // - subroutine for allocating into the executable heap area.
    // - compute the length of a Bar.
    // - update GC to work w/ Laws and their new num_cnsts, which will be stored
    //   at the end of them.
    // - GC needs to be able to copy them, and traverse over them.

    // jit return value:
    //
    // HD is Bar of the machine code
    // memcpy it into executable heap area.
    // store the fn ptr to it into the Law struct.
    // if compiler_seed is not defined, either fill it w/ NULL or eval_law.
    //
    // TL is cnsts
    // fetch cnsts from the row, count them, store in Law
    //
    // in run_law no_jet case, push cnsts to stack after self and before args.
  }

  Law l = { .n = n, .a = a, .b=b, .w = { .n_lets = 0, .n_calls = 0 } };

  weigh_law(1, &l.w, b);

  if (TRACE_LAWS) {
    fprintf(stderr, "law: name=");
    fprintv(stderr, n);
    fprintf(stderr, ",\t{lets=%lu, calls=%lu}\n", l.w.n_lets, l.w.n_calls);
  }

  push_val(a_Law(l));
}

void incr() {
  #if ENABLE_GRAPHVIZ
  write_dot("incr");
  #endif

  eval_update(0);
  Value *x = pop();

  if (is_direct(x)) {
    // this doesn't need to deal with overflow because get_direct returns
    // a u63, and push_word can handle a u64.
    push_word(get_direct(x) + 1);
    return;
  }

  if (x->type != BIG) {
    push_val(DIRECT_ONE);
    return;
  }

  BigPlusWord(1, x);
}

static inline void prim_case() {
  #if ENABLE_GRAPHVIZ
  write_dot("prim_case");
  #endif

  eval_update(5);

  Value *p = pop(); // m,z,a,l,p could be indirections, but that's fine.
  Value *l = pop();
  Value *a = pop();
  Value *z = pop();
  Value *m = pop();
  Value *o = pop();

  switch (TY(o)) {
    case PIN:
      push_val(IT(o)); // o
      push_val(p);     // o p
      mk_app_rev();    // (p o)
      break;
    case LAW:
      push_val(BD(o)); // b
      push_val(AR(o)); // b a
      push_val(NM(o)); // b a n
      push_val(l);     // b a n l
      mk_app_rev();    // b a (l n)
      mk_app_rev();    // b (l n a)
      mk_app_rev();    // (l n a b)
      break;
    case APP:
      push_val(TL(o)); // t
      push_val(HD(o)); // t h
      push_val(a);     // t h a
      mk_app_rev();    // t (a h)
      mk_app_rev();    // (a h t)
      break;
    case BIG: {
      if (EQZ(o)) {
        push_val(z);
        break;
      }
      push_val(m); // m
      push_val(o); // m o
      Dec();       // m d
      mk_app();    // (m d)
      break;
    }
    case IND: crash("plan_case: IND: impossible");
    case MOV: crash("MOV escaped GC");
  }

  eval();
}

static inline void setup_call(u64 depth) {
  #if ENABLE_GRAPHVIZ
  snprintf(dot_lab, 1024, "setup_call %lu", depth);
  write_dot(dot_lab);
  #endif

  // get the actual args by taking the tail of every arg-slot.
  Value **end = sp+depth;
  while (sp < end) { *sp = (**sp).a.g; sp++; }
  sp -= depth;
}

static inline void handle_oversaturated_application(u64 count) {
  #if ENABLE_GRAPHVIZ
  snprintf(dot_lab, 1024, "handle_oversaturated_application %lu", count);
  write_dot(dot_lab);
  #endif
  //
  // if our application is oversaturated, `depth` will exceed the arity. in this
  // case, we want to re-assemble the apps, and eval the result.
  for (u64 i = 0; i < count; i++) mk_app_rev();
  eval();
}

void backout(u64 depth) {
  #if ENABLE_GRAPHVIZ
  snprintf(dot_lab, 1024, "backout %lu", depth);
  write_dot(dot_lab);
  #endif
  //
  // pop stack of unwound apps.
  for (u64 i = 0; i < depth; i++) {
    pop();
  }
  // `eval` saved the outermost APP, and that should now be at the bottom
  // of the stack.
}

Value *kal(u64 maxRef, char **pool, Value *x) {
  if (is_direct(x)) {
    u64 xv = get_direct(x);
    if (xv > maxRef) return x;                   // unquoted constant
    return get(xv);                              // environment reference
  }

  if (x->type != APP) return x;                  // unquoted constant

  Value *hx = HD(x);

  if (EQZ(hx)) return TL(x);                     // quoted constant

  if (TY(hx) != APP) return x;                   // unquoted constant

  Value *hhx = HD(hx);

  if (!EQZ(hhx)) return x;                       // unquoted constant

  // (0 f g) is a call.

  Value *f = TL(hx);
  Value *g = TL(x);

  Value *this_call = (Value*) *pool;
  *pool += 24;
  this_call->type = APP;
  this_call->a.f  = kal(maxRef, pool, f);
  this_call->a.g  = kal(maxRef, pool, g);
  return this_call;
}

// 0 indicates no lets
u64 length_let_spine(Value *x) {
  u64 count = 0;
loop:
  if (TY(x) == APP) {
    Value *car = deref(HD(x));
    if (TY(car) == APP) {
      Value *caar = deref(HD(car));
      if (EQ1(caar)) {
        // ((1 v) k)
        count++;
        x = deref(TL(x));
        goto loop;
      }
    }
  }
  return count;
}

void eval_law(Law l) {
  u64 args = get_direct(l.a); // this code is unreachable with bignat arity
  u64 lets = l.w.n_lets;
  u64 kals = l.w.n_calls;
  int maxRef = args + lets;

  #if ENABLE_GRAPHVIZ
  {
    snprintf(dot_lab, 1024, "eval_law(arity=%lu, lets=%lu)", args, lets);
    write_dot(dot_lab);
  }
  #endif

  // we are allocating APPs and INDs, which are both 24 bytes.
  const size_t bytes = 24 * (lets + kals);

  push_val(l.b);                            // save (law body)
  char *mem = bytes ? alloc(bytes) : NULL; // gc
  Value *b  = pop();                       // restore (law body)

  // initialize letrec slots, since they might be referenced before they
  // are filled in, but leave APPs uninitialized.  KAL will initialize.

  #if ENABLE_GRAPHVIZ
  write_dot("starting graph construction");
  #endif

  char *apps = mem + lets*24;

  if (lets) {
    #if STACK_BOUNDS_CHECK
    if (sp-lets < stack) crash("eval_law: stack overflow");
    #endif

    // Add a black hole per let.
    sp -= lets;
    Value **fill = sp;
    for (u64 i = 0; i <= args; i++, fill++) *fill = fill[lets];
    for (u64 i = 0; i < lets;  i++, fill++) *fill = (Value*) (mem + 24*i);

    #if ENABLE_GRAPHVIZ
    for (u64 i = 0; i < lets; i++) {
      Value *ptr = (Value*) (mem + (i*24));
      ptr->type  = IND;
      ptr->i.ptr = NULL; // {type=IND, ptr=NULL} indicates a black hole
    }
    write_dot("added holes for lets");
    #endif

    // Compute the graph of each let, and fill the corresponding hole.
    for (u64 i = 0; i < lets; i++) {

      // (1 exp next)
      Value *next = TL(b);
      Value *exp  = TL(HD(b));
      b           = next;
      Value *gr   = kal(maxRef, &apps, exp);

      Value *ptr = (Value*) (mem + (i*24));
      ptr->type  = IND;
      ptr->i.ptr = gr;

      #if ENABLE_GRAPHVIZ
      write_dot("filled one");
      #endif
    }

  }

  #if ENABLE_GRAPHVIZ
  write_dot("constructing body graph");
  #endif

  Value *gr = kal(maxRef, &apps, b);
  push_val(gr);                 // .. self args slots bodyGr
  eval();                       // .. self args slots bodyWhnf
  return slide(maxRef+1);       // .. bodyWhnf
}

void Trace (char *end) {
    force_in_place(0);
    if (printer_seed == NULL) {
      fprintv(stderr, pop_deref());
      fprintf(stderr, "\n");
      return;
    }
    push_val(DIRECT(12));        // .. msg 12
    push_val(*printer_seed);     // .. msg 12 printer
    mk_app_rev();                // .. msg (printer 12)
    mk_app_rev();                // .. (printer 12 msg)
    force_in_place(0);           // .. msg_bar
    Value *ov = pop_deref();     // ..
    int bwid = ByteSz(ov);
    BIND_BUF_PTR(obuf, ov);
    char *bbuf = (void*) obuf;
    if (bwid < 1) return;
    int owid = bwid - 1;

    // TODO: Use a loop to handle larger outputs correctly.
    int endSz = strlen(end);
    if (owid != write(2, bbuf, owid)) pexit("write (TODO)");
    if (endSz != write(2, end, endSz)) pexit("write (TODO)");
}

void run_law(Value *self, u64 ar) {
  if (TY(self) != PIN) goto no_jet;

  switch (self->p.jet) {

  case J_ADD:
    to_nat(0);
    to_nat(1);
    Add();
    return;

  case J_SUB:
    to_nat(0);
    to_nat(1);
    Sub();
    return;

  case J_MUL:
    to_nat(0);
    to_nat(1);
    Mul();
    return;

  case J_DIV:
    to_nat(0);
    to_nat(1);
    Div();
    return;

  case J_MOD:
    to_nat(0);
    to_nat(1);
    Mod();
    return;

  case J_DEC:
    eval_update(0);
    Dec();
    return;

  case J_CMP:
    int ord = cmp_lazy();
    push_word(ord);
    return;

  case J_TRACE:                  // .. body msg
    Trace("\n");                 // .. body
    eval();                      // .. *body
    return;

  default:
    goto no_jet;
  }

 no_jet:
  // TODO push cnsts (in the right order)

  // self is still valid here, we haven't allocated
  push_val(self);
  eval_law(FUNC(self));
}

JetTag jet_match(Value *item) {
  item = deref(item);

  if (TY(item) != LAW) return J_NONE;

  Law l = item->l;

  for (int i = 0; i < NUM_JETS; i++) {
    Jet jet = jet_table[i];

    if (NEQ(l.a, DIRECT(jet.arity))) continue;
    if (NEQ(l.n, jet.name)) continue;

    if (TRACE_JET_MATCHES) {
      fprintf(stderr, "MATCH: jet name + arity match: ");
      fprintv(stderr, jet.name);
      fprintf(stderr, "\n");
    }

    return jet.tag;
  }

  if (TRACE_JET_MATCHES) {
    fprintf(stderr, "NO MATCH: pinned law is not a jet: ");
    fprintv(stderr, l.a);
    fprintf(stderr, "\n");
  }

  return J_NONE;
}

// returns true if it eval-ed
bool law_step(u64 depth) {
  #if ENABLE_GRAPHVIZ
  snprintf(dot_lab, 1024, "law_step %lu", depth);
  write_dot(dot_lab);
  #endif

  Value *self = pop_deref();
  if (GT(AR(self), DIRECT(depth))) {
    // unsaturated application. this is a little weird, but works?
    if (depth <= 1) {
      #if ENABLE_GRAPHVIZ
      write_dot("unsaturated / 0-backout");
      #endif
      return false;
    }
    backout(depth-1);
    return false;
  } else {

    // enable_graphviz=1;

    #if TRACE_CALLS
    for (int i=0; i<call_depth; i++) fprintf(stderr, " ");
    fprintv(stderr, get_deref(depth-1));
    fprintf(stderr, "\n");
    call_depth++;
    #endif

    setup_call(depth);

    #if ENABLE_ASSERTIONS
    if (!is_direct(AR(self))) crash("impossible: called law with huge arity");
    #endif

    u64 ar = get_direct(AR(self));

    run_law(self, ar);

    #if TRACE_CALLS
    if (TRACE_CALLS) {
      call_depth--;
      for (int i=0; i<call_depth; i++) fprintf(stderr, " ");
      fprintf(stderr, "=> ");
      fprintv(stderr, get_deref(0));
      fprintf(stderr, "\n");
    }
    #endif

    if (ar < depth) handle_oversaturated_application(depth - ar);
    return true;
  }
}

u64 prim_arity(Value *op) {
  if (!is_direct(op)) return 1;
  switch (get_direct(op)) {
    case 0:  return 1; // mk_pin
    case 1:  return 3; // mk_law
    case 2:  return 1; // incr
    case 3:  return 6; // case
    default: return 1;
  }
}

// this assumes there are sufficient stack args to saturate whichever primop
// we run.
void do_prim(Value *op) {
  #if ENABLE_GRAPHVIZ
  write_dot(dot_lab);
  #endif

  if (!is_direct(op)) goto exception_case;

  switch (get_direct(op)) {
    case 0:  return mk_pin();
    case 1:  return mk_law();
    case 2:  return incr();
    case 3:  return prim_case();
    default: goto exception_case;
  }
 exception_case:
  push_val(op);
  force_in_place(1);                 // *param tag
  fprintf(stderr, "Exception(");
  Trace("): ");                      // param
  Trace("\n");                       //
  exit(1);
}

bool unwind(u64 depth) {
 again:
  #if ENABLE_GRAPHVIZ
  snprintf(dot_lab, 1024, "unwind %lu", depth);
  write_dot(dot_lab);
  #endif
  //
  Value *x = get(0);

 without_ind:

  if (is_direct(x)) {
    backout(depth);
    return false;
  }

  switch (x->type) {
    case IND: {
        x = x->i.ptr;
        *sp = x;
        goto without_ind;
    }
    case APP: {
      push_val(HD(x));
      depth++;
      goto again;
    }
    case LAW: {
      return law_step(depth);
    }
    case PIN: {
      Value *item = deref(x->p.item);
      switch (TY(item)) {
        case BIG: {
          u64 arity = prim_arity(item);
          //
          if (depth < arity) {
            // if we are undersaturated, we backout.
            backout(depth);
            return false;
          }
          // run primop
          pop();
          setup_call(depth);
          do_prim(item);

          // oversaturated
          if (arity < depth) handle_oversaturated_application(depth - arity);

          return true;
        }
        // unwind "through" pins & apps
        // we don't increment `depth` here because we are just setting up
        // for the above APP case, which increments `depth`.
        case APP:
        case PIN: {
          pop(); // pop outer
          push_val(item);
          goto again;
        }
        case LAW: {
          return law_step(depth);
        }
        case IND: {
          crash("unwind: bad deref");
        }
        case MOV:
          crash("MOV escaped GC");
      }
    }
    case BIG: {
      backout(depth);
      return false;
    }
    case MOV:
      crash("MOV escaped GC");
    default:
      crash("unwind: this should never happen");
  }
}

// returns true if we eval-ed
bool eval() {
  #if ENABLE_GRAPHVIZ
  write_dot("eval");
  #endif
  //
  Value *x = get_deref(0);
  switch (TY(x)) {
    case APP:
      return unwind(0);
    case PIN:
    case LAW:
    case BIG:
      return false;
    case IND: crash("eval: IND");
    default:  crash("eval: bad tag");
  }
}

void force_whnf() {
  #if ENABLE_GRAPHVIZ
  write_dot("force_whnf");
  #endif
  //
  Value *top = pop_deref();
  if (TY(top) == APP) {
    push_val(TL(top));
    push_val(HD(top));
    force_whnf();
    force();
  }
}

void force() {
  #if ENABLE_GRAPHVIZ
  write_dot("force");
  #endif
  //
  Value *top = get_deref(0);
  if (TY(top) == APP) {
    clone();
    eval();
    update(1);
    force_whnf();
  } else {
    pop();
  }
}

////////////////////////////////////////////////////////////////////////////////
//  Runner

#define STR_BUF_LEN 4096
static char str_buf[STR_BUF_LEN];

static inline bool issym (char c) {
  return (c == '_' || isalnum(c));
}

// when `is_sym == true`,  we are parsing symbols.
// when `is_sym == false`, we are parsing digits.
// this seems tidier than passing a function pointer, as issym & isdigit do not
// have the same type (??).
void read_str_input(FILE *f, bool is_sym) {
  char c;
  int i=0;
  for (; true; i++) {
    str_buf[i] = c = fgetc(f);
    if (is_sym  && (!issym(c)))   break;
    if (!is_sym && (!isdigit(c))) break;
    if (i >= STR_BUF_LEN) crash("read_str_input: input too big");
  }
  str_buf[i] = 0;
  ungetc(c,f);
}

void read_atom(FILE *f) {
  read_str_input(f, false);
  //
  // y : # of bits required to store
  // x : length of string of '9's
  // approx linreg:
  // y = 3.324 x + 0.4513
  long bit_len = ((34 * strlen(str_buf)) / 10) + 1;
  long word_bits = 8 * sizeof(word_t);
  long nat_len = bit_len / word_bits;
  if ((bit_len % word_bits) > 0) nat_len++; // round up.
  //
  Value *res = start_bignat_alloc(nat_len);
  nn_zero(BUF(res), nat_len);
  static len_t dummy_len;
  nn_set_str(BUF(res), &dummy_len, str_buf);
  push_val(end_bignat_alloc(res));
}

// We take the already-read head of the app on the PLAN stack.
void read_app(FILE *f) {
  bool saw_space = false;
  while (true) {
    char c = fgetc(f);
    switch (c) {
      case '\r':
      case '\n':
      case '\t':
      case ' ':
        saw_space = true;
        continue;

      case ')':
        return;

      default:
        if (!saw_space) crash("expecting space or )");
        ungetc(c, f);
        read_exp(f);
        mk_app();
        continue;
    }
  }
}

void utf8_nat(char *str) {
  long byteSz = strlen(str);
  long wordSz = (7 + byteSz) / 8;
  Value *res = start_bignat_alloc(wordSz);
  nn_zero(BUF(res), wordSz);
  memcpy(BUF(res), str, byteSz);
  push_val(end_bignat_alloc(res));
}

void read_sym(FILE *f) {
  read_str_input(f, true);
  int len = strlen(str_buf);
  if (!len) crash("Empty symbol");
  utf8_nat(str_buf);
}

void bind_symbol(Value *nm, Value *v) {
  push_val(v);
  push_val(nm);
  push_val(*symbol_table);
  mk_app_rev();
  mk_app_rev();
  *symbol_table = pop();
}

void lookup_symbol() {
  Value *nm = pop();
  Value *x = *symbol_table;

  while (!is_direct(x)) {
    Value *hx = HD(x);
    Value *v  = TL(x);
    Value *k  = TL(hx);
    x=HD(hx);
    if (EQ(nm, k)) { push_val(v); return; }
  }

  fprintv(stderr, nm);
  crash(": symbol not found");
}

bool read_exp(FILE *f) {
again:
  char c = fgetc(f);

  if (feof(f)) return false;

  if (isalpha(c)) {
    ungetc(c, f);
    read_sym(f);
    lookup_symbol();
    return true;
  }

  switch (c) {
  case 0:
    return false;

  case '%':
    read_sym(f);
    return true;

  case ' ':
  case '\r':
  case '\n':
  case '\t':
    goto again;

  case ';':
    while (1) {
      char c = fgetc(f);
      if (feof(f)) return false;
      switch (c) {
      case 0:    return false;
      case '\n': goto again;
      default:   continue;
      }
    }

  case '#': {
    char n = fgetc(f);
    ungetc(n, f);
    if (isalpha(n)) {
      read_sym(f);
      mk_pin();
      return true;
    }
    if (isdigit(n)) {
      read_atom(f);
      mk_pin();
      return true;
    }
    fprintf(stderr, "Unexpected: '%c'\n", n);
    exit(2);
  }

  case '{': {
    char buf[1234] = {0};
    int depth = 1;
    for (int i=0; i<1234; i++) {
        buf[i] = fgetc(f);
        if (feof(f)) { crash("Unexpected EOF"); }
        switch (buf[i]) {
        case '{':
          depth++;
          continue;
        case '}':
          depth--;
          if (depth) continue;
          buf[i] = 0;
          if (i == 0) push_val(DIRECT_ZERO);
          else utf8_nat(buf);
          return true;
        default:
          continue;
        }
    }
    crash("string too big");
  }

  case '@': {
    read_str_input(f, true);
    int len = strlen(str_buf);
    if (!len) crash("Empty seed");
    char buf[1234] = "./seed/";
    strcpy(buf+7, str_buf);
    load_seed_file(buf);
    return true;
  }

  case '(':
      bool ret = read_exp(f);
      if (!ret) return false;
      read_app(f);
      return true;

  default:
    if (isdigit(c)) {
        ungetc(c, f);
        read_atom(f);
        return true;
    }
    fprintf(stderr, "Unexpected: '%c'\n", c);
    exit(2);
  }
}

static void repl (void) {
    { // load seed (starting state)
      static const char *sire_seed = "./seed/sire-in-sire";
      load_seed_file(sire_seed);
    }

    static char buf[128];

  next_input:
    int i=0;
    memset(buf, 0, 128);

  read_more:

    ssize_t bytes_read = read(0, buf+i, 1);

    if (bytes_read && i < 100 && buf[i] != '\n') { i++; goto read_more; }

    // Create a string from the input.  (TODO use a bar instead).
    buf[i+1] = 0;

    {
      Value *v = start_bignat_alloc(16);
      memcpy(BUF(v), buf, 128);
      push_val(end_bignat_alloc(v)); // state input
    }

    mk_app();                      // .. (state input)
    force_in_place(0);             // .. (0 output newstate)
    Value *res = pop();            // ..
    Value *nex = TL(res);
    Value *out = deref(TL(HD(res)));
    push_val(nex);                 // newstate

    int bwid = ByteSz(out);
    if (bwid > 1) {
      BIND_BUF_PTR(obuf, out);
      char *bbuf = (void*) obuf;
      int owid = bwid - 1;
      int wrote = fwrite(bbuf, 1, owid, stderr);
      ASSERT_(owid != wrote);
      fprintf(stderr, "\n");
    }

    if (i==0 && !bytes_read) { return; }

    goto next_input;
}

void test_repl (FILE *f) {
  bool isInteractive = isatty(fileno(f));

 next_input:
  if (isInteractive) printf(">> ");

 loop:
  char c = fgetc(f);

  if (feof(f)) return;

  switch (c) {
  case '\t':
  case '\n':
  case '\r':
  case ' ':
    goto loop;

  case ';':
    while (1) {
      char c = fgetc(f);
      if (feof(f)) return;
      switch (c) {
      case 0:    return;
      case '\n': goto next_input;
      default:   continue;
      }
    }

  case '!':
    if (!read_exp(f)) { crash("no value"); }
    if (!read_exp(f)) { crash("no value"); }
    force_in_place(0);
    force_in_place(1);
    Value *y = pop();
    Value *x = pop();

    if (NEQ(x,y)) {
      fprintf(stderr, "FAILED ");
      fprintv(stderr, x);
      fprintf(stderr, " != ");
      fprintv(stderr, y);
      fprintf(stderr, "\n");
      crash("assertion failed");
    }

    fprintf(stderr, "PASSED ");
    fprintv(stderr, x);
    fprintf(stderr, "\n");

    gc();

    goto next_input;

  case '=':
    read_sym(f);
    if (!read_exp(f)) { crash("no value"); }
    bind_symbol(get(1), get(0)); // this allocates
    #if ENABLE_PRINTER
    fprintf(stderr, "= ");
    fprintv(stderr, get(1));
    fprintf(stderr, " ..\n");
    #endif
    pop();
    pop();
    goto next_input;

  default:
    ungetc(c, f);
    if (!read_exp(f)) return;
    force_in_place(0);
    fprintv(stdout, pop_deref());
    printf("\n");
    goto next_input;
  }
}

int main (int argc, char **argv) {
  rts_init();

  { // load printer
    static const char *tracefile = "./seed/renderPlan";
    load_seed_file(tracefile);
    printer_seed=get_ptr(0);
  }

  { // setup symbol table (TODO: only the testing harness needs this)
    push_val(DIRECT_ZERO);
    symbol_table = get_ptr(0);
  }

  { // load the compiler seed
    load_seed_file("./seed/jit");
    compiler_seed = get_ptr(0);
  }

  #if ENABLE_GRAPHVIZ
  struct stat st = {0};
  if (stat(dot_dir_path, &st) == -1) {
    mkdir(dot_dir_path, 0700);
  }
  #endif

  switch (argc) {
  case 1:
    repl();
    break;

  case 2:
    char *filename = argv[1];
    FILE *f = fopen(filename, "r");
    test_repl(f);
    break;

  default:
    crash("bad usage");
  }

  #if ENABLE_GRAPHVIZ
  write_dot("main final");
  #endif
}

// Debug Printer ///////////////////////////////////////////////////////////////

#if ENABLE_PRINTER

void fprintv(FILE *f , Value *v) {
  switch (TY(v)) {
  case PIN:
    fprintf(f, "<");
    fprintv(f, IT(v));
    fprintf(f, ">");
    break;
  case LAW:
    fprintf(f, "{");
    fprint_nat(f, NM(v));
    fprintf(f, " ");
    fprint_nat(f, AR(v));
    fprintf(f, " ");
    fprintv_internal(f, BD(v), 0);
    fprintf(f, "}");
    break;
  default:
    fprintv_internal(f, v, 0);
  }
}

void fprintv_app(FILE *f, Value *v, int recur) {
  if (!IS_APP(v)) {
    return fprintv_internal(f, v, recur);
  }
  fprintv_app(f, HD(v), recur);
  fprintf(f, " ");
  fprintv_internal(f, TL(v), recur+1);
}

void fprint_nm (FILE *f, Value *law, int recur) {
  ASSERT_(IS_LAW(law));

  Value *nm = NM(law);

  ASSERT_(IS_NAT(nm));

  if (is_direct(nm)) {
    u64 w = get_direct(nm);
    char tmp[9] = {0};
    ((u64*) tmp)[0] = w;
    if (!is_symbol(nm)) goto fallback;
    fprintf(f, "%s", tmp);
    return;
  }

  {
    if (!is_symbol(nm)) { goto fallback; }
    int len = ByteSz(nm);
    BIND_BUF_PTR(nm_buf, nm);
    fwrite(nm_buf, 1, len, f);
    return;
  }

fallback:
  fprintf(f, "<");
  fprintv_internal(f, law, recur);
  fprintf(f, ">");
}

void fprintv_internal(FILE *f, Value *v, int recur) {
  v = deref(v);
  if (recur > 20) {
    fprintf(f, "‥");
    return;
  }

  if (is_direct(v)) {
    fprint_nat(f, v);
    return;
  }

  switch (v->type) {
    case PIN:
      Value *item = deref(IT(v));

      if (IS_LAW(item)) {
          fprint_nm(f, item, recur+1);
          break;
      }

      fprintf(f, "<");
      fprintv_internal(f, item, recur+1);
      fprintf(f, ">");
      break;
    case LAW:
      fprintf(f, "{");
      fprint_nat(f, NM(v));
      fprintf(f, "}");
      break;
    case APP:
      fprintf(f, "(");
      fprintv_app(f, v, recur+1);
      fprintf(f, ")");
      break;
    case BIG:
      fprint_nat(f, v);
      break;
    case IND:
      crash("fprintv_internal: got IND");
    default:
      fprintf(f, "!!");
      break;
  }
}

bool is_symbol(Value *v) {
  len_t len = ByteSz(v);

  BIND_BUF_PTR(str, v);

  if (len == 0) return false;
  if (len == 1) return isalpha(str[0]);
  for (int i=0; i<len; i++) {
    if (!issym(str[i])) return false;
  }
  return true;
}

bool is_string(Value *v) {
  len_t len = ByteSz(v);

  if (len < 2) return false;

  BIND_BUF_PTR(str, v);

  int depth = 1;
  for (int i=0; i<len; i++) {
    if (depth == 0) return false;
    char c = str[i];
    switch (c) {
    case 0:    return false;
    case '{':  depth++; continue;
    case '}':  depth--; continue;
    case '\n':
    case '\r': return false;
    default:   if (!isprint(c)) return false;
               else continue;
    }
  }
  return true;
}

void fprint_nat(FILE *f, Value *v) {
  ASSERT_(IS_NAT(v));

  BIND_BUF_PTR(buf, v);

  long len = ByteSz(v);
  long wordSz = is_direct(v) ? 1 : WID(v);

  if (v == DIRECT_ZERO) {
    fputc('0', f);
    return;
  }

  if (is_symbol(v)) {
    // symbolic, so we can print it as a string, with a leading `%`
    fputc('%', f);
    fwrite(buf, 1, len, f);
  } else if (is_string(v)) {
    fputc('{', f);
    fwrite(buf, 1, len, f);
    fputc('}', f);
  } else {
    // non-symbolic, so we use bsdnt to print as decimal
    char *tmp = nn_get_str((word_t*)buf, wordSz);
    fprintf(f, "%s", tmp);
    free(tmp);
  }
}

void show_direct_nat(char *buf, Value *v) {
  u64 nat = get_direct(v);
  if (is_symbol(v)) {
    u64 *lol = (u64*) buf;
    *lol = nat;
  } else {
    sprintf(buf, "%lu", nat);
  }
}


#endif


// Graphviz ////////////////////////////////////////////////////////////////////

#if ENABLE_GRAPHVIZ

int dot_count = 0;

char *p_ptr(Value *x) {
  char *buf = malloc(48);
  if (x == NULL) {
    sprintf(buf, "N_null");
  } else if (is_direct(x)) {
    sprintf(buf, "ptr_nat_%lu", get_direct(x));
  } else {
    sprintf(buf, "N_%p", x);
  }
  return buf;
}

Node *stack_to_list_heap_only() {
  ssize_t stack_size = get_stack_size();

  Node *l = NULL;
  if (stack_size == 0) return l;
  for (u64 i = 0; i < stack_size; i++) {
    if (is_direct(get(i))) continue;
    l = cons((void *)get(i), l);
  }
  return l;
}

// TODO turn `Node *` into `Value *` tree of APPs
void fprint_heap(FILE *f, Node *input, Node *seen) {
 again:
  // empty input - done
  if (null_list(input)) return;
  //
  Value *v = (Value *)input->ptr;
  input = input->next;
  //
  // if NULL or seen, recur on tail of input
  if ((v == NULL) || (member_list((void *)v, seen))) {
    goto again;
  }
  //
  // non-seen Value. print it, add `v` to `seen`, add any discovered addresses
  // to `input`.
  switch (TY(v)) {
    case PIN: {
      char *v_p = p_ptr(v);
      char *i_p = p_ptr(IT(v));
      if (is_direct(IT(v))) {
        fprintf(f, "%s [label = \"\\<%lu\\>\"];\n", v_p, get_direct(IT(v)));
      } else {
        fprintf(f, "%s [label=pin];\n", v_p);
        fprintf(f, "%s -> %s [arrowhead=box];\n", v_p, i_p);
        input = cons((void *)IT(v), input);
      }
      free(v_p);
      free(i_p);
      break;
    }
    case LAW: {
      char *v_p = p_ptr(v);
      // char *b_p = p_ptr(BD(v));
      fprintf(f, "%s [label=\"\\{", v_p);
      fprint_nat(f, NM(v));
      fprintf(f, "\\}\"];\n");
      // fprintf(f, " ar:");
      // fprint_nat(f, AR(v));
      // fprintf(f, "\"];\n");
      // fprintf(f, "%s -> %s [label=bd];\n", v_p, b_p);
      free(v_p);
      // free(b_p);
      // input = cons((void *)BD(v), input);
      break;
    }
    case APP: {
      char *v_p = p_ptr(v);
      Value *h = HD(v), *t = TL(v);
      char *h_p = p_ptr(h);
      char *t_p = p_ptr(t);
      char hbuf[256] = "", tbuf[256] = "";
      if (is_direct(h)) { show_direct_nat(hbuf, h); }
      if (is_direct(t)) { show_direct_nat(tbuf, t); }
      fprintf(f, "%s [label=\" <f> %s | <x> %s \"]", v_p, hbuf, tbuf);
      if (!is_direct(h)) {
        fprintf(f, "%s:f -> %s;\n", v_p, h_p);
        input = cons((void *)h, input);
      }
      if (!is_direct(t)) {
        fprintf(f, "%s:x -> %s;\n", v_p, t_p);
        input = cons((void *)t, input);
      }
      free(v_p);
      free(h_p);
      free(t_p);
      break;
    }
    case BIG: {
      char *v_p = p_ptr(v);
      fprintf(f, "%s [label=\"", v_p);
      fprint_nat(f, v);
      fprintf(f, "\"];\n");
      free(v_p);
      break;
    }
    case IND: {
      char *v_p = p_ptr(v);
      char *i_p = p_ptr(IN(v));
      fprintf(f, "%s [label=ind];\n", v_p);
      fprintf(f, "%s -> %s [arrowhead=dot];\n", v_p, i_p);
      free(v_p);
      free(i_p);
      input = cons((void *)IN(v), input);
      break;
    }
    case MOV:
      crash("MOV escaped GC");
  }
  seen = cons((void *)v, seen);
  goto again;
}

void fprint_stack(FILE *f) {
  // print "stack topper"
  // => stack [label="<ss> stack|<s0>|<s1>|<s2>", color=blue, height=2.5];
  fprintf(f, "stack [label=\"<ss> stack");

  ssize_t stack_size = get_stack_size();

  for (int i = 0; i < stack_size; i++) {
    char label[256] = "";
    if (is_direct(get(i))) show_direct_nat(label, get(i));
    fprintf(f, "| <s%d> %s ", i, label);
  }
  fprintf(f, "\", color=blue, height=2.5];\n");

  // print edges between stack topper Values
  for (int i = 0; i < stack_size; i++) {
    Value *v = get(i);
    if (is_direct(v)) continue;
    char *v_p = p_ptr(v);
    fprintf(f, "stack:s%d -> %s;\n", i, v_p);
    free(v_p);
  }
}


void write_dot_extra(char *label, char *extra, Value *v) {
  if (!enable_graphviz) return;
  char fp[20] = {0};
  sprintf(fp, "%s/%05d.dot", dot_dir_path, dot_count);
  dot_count++;
  FILE *f = fopen(fp, "w+");
  fprintf(f, "digraph {\nbgcolor=\"#665c54\"\n");
  fprintf(f, "label = \"%s\";\n", label);
  fprintf(f, "node [shape=record,width=.1,height=.1];\n");
  fprintf(f, "nodesep=.10;\n");
  fprintf(f, "rankdir=LR;\n");
  fprintf(f, "\n// stack\n");
  fprint_stack(f);
  fprintf(f, "\n// heap\n");

  Node *heap_input = stack_to_list_heap_only();
  if (v != NULL) {
    heap_input = cons((void *)v, heap_input);
  }
  fprint_heap(f, heap_input, NULL);

  fprintf(f, "\n// extra\n");
  fprintf(f, "%s\n", extra);
  fprintf(f, "}\n");
  fclose(f);
}

void write_dot(char *label) {
  write_dot_extra(label, "", NULL);
}
#endif


// Validation //////////////////////////////////////////////////////////////////

#if ENABLE_VALIDATION
void check_nat(Value *v) {
  if (v == NULL) crash("check_nat: NULL");

  if (is_direct(v)) return;

  if (v->type != BIG) crash("check_nat: not nat");

  word_t sz = v->n.size;

  if (sz == 0) crash("check_nat: bignat zero");

  if (sz == 1) {
    if (BUF(v)[0] < PTR_NAT_MASK) {
      crash("check_nat: direct atom encoded as bignat");
    }
    return;
  }

  if (BUF(v)[sz - 1] == 0) {
    crash("check_nat: bad size (high word is zero)");
  }
}

void check_value(Value *v) {
  if (v == NULL) crash("check_value: NULL");

  if (is_direct(v)) return;

  if ((char*)v < live_start) {
    fprintf(stderr, "check_value: %p is before the heap", v);
    crash("check_value");
  }

  if ((char*)v >= live_end) {
    fprintf(stderr, "check_value: %p is past the heap", v);
    crash("check_value");
  }

  switch (v->type) {
    case PIN:
      check_value(IT(v));
      break;
    case LAW:
      check_nat(NM(v));
      check_nat(AR(v));
      check_value(BD(v));
      break;
    case APP:
      check_value(HD(v));
      check_value(TL(v));
      break;
    case BIG:
      check_nat(v);
      break;
    case IND:
      check_value(IN(v));
      break;
    default:
      crash("BAD VALUE TAG");
  }
}
#endif
