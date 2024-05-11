#include <stdint.h>
#define __STDC_WANT_LIB_EXT2__  1
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <ctype.h>
#include <stdarg.h>
#include <string.h>
#include <sys/param.h>
#include <sys/stat.h>
#include <inttypes.h>
#include <unistd.h>
#include <stdnoreturn.h>
#include <sys/mman.h>

#include "bsdnt.h"


// Utils ///////////////////////////////////////////////////////////////////////

noreturn void crash(char *s) { printf("Error: %s\n", s); exit(1); }


////////////////////////////////////////////////////////////////////////////////
//  Typedefs

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
  word_t n_lets, n_calls;
} LawWeight;

typedef struct Law {
  Value *n; // Always a nat
  Value *a; // Always a nat
  Value *b;
  LawWeight w;
} Law;

typedef struct App { Value *f, *g; } App;

struct Value {
  Type type;
  union { Pin p; Law l; App a; Big n; Ind i; };
};

typedef uint64_t u64;


// Prototypes //////////////////////////////////////////////////////////////////

JetTag jet_match        (Value*);
static void mk_app      (void);
static void eval_update (int);
static bool eval        (void);
static void force       (void);
static void update      (u64);
static void cheney      (void);


// Config //////////////////////////////////////////////////////////////////////

#define STACK_SIZE 65536
#define BLOCK_SIZE 65536
#define HEAP_LOCAL ((void*)(1ULL<<24))


// Globals /////////////////////////////////////////////////////////////////////

static char *heap_start = NULL;
static char *heap_end   = NULL;

static char *live_start = NULL;
static char *live_end   = NULL;
static char *hp         = NULL;

static Value *stack[STACK_SIZE];
static u64 sp = 0;

static Value **printer_seed = NULL;


// GC Heap /////////////////////////////////////////////////////////////////////

void heap_init (void) {
    const int prot   = PROT_READ | PROT_WRITE;
    const int flags  = MAP_FIXED | MAP_PRIVATE | MAP_ANON | MAP_NORESERVE;

    if (HEAP_LOCAL != mmap(HEAP_LOCAL, BLOCK_SIZE, prot, flags, -1, 0))
        { perror("heap_init: mmap"); exit(1); }

    heap_start = HEAP_LOCAL;
    heap_end   = heap_start + BLOCK_SIZE;
    live_start = heap_start;
    live_end   = heap_end;
    hp         = live_start;
}

void extend_mmap (void) {
    const int prot   = PROT_READ | PROT_WRITE;
    const int flags  = MAP_FIXED | MAP_PRIVATE | MAP_ANON | MAP_NORESERVE;

    while (live_end > heap_end) {
        len_t mapped_bytes = heap_end - heap_start;
        if (heap_end != mmap(heap_end, mapped_bytes, prot, flags, -1, 0))
            { perror("extend_mmap: mmap"); exit(1); }
        heap_end += mapped_bytes;
    }
}

void heap_resize (void) {
    ssize_t used_bytes = hp - live_start;
    ssize_t used_blocks = (((used_bytes + BLOCK_SIZE) - 1) / BLOCK_SIZE);
    ssize_t new_size = BLOCK_SIZE * 2 * used_blocks;
    live_end = live_start + new_size;
    extend_mmap();
}

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


// Direct Atoms ////////////////////////////////////////////////////////////////

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
  return (Value *) (x | PTR_NAT_MASK);
}


// Stack ///////////////////////////////////////////////////////////////////////

static inline Value *deref(Value *x) {
  while (!is_direct(x) && x->type == IND) x = x->i.ptr;
  return x;
}

static inline Value *pop       (void)     { sp--; return stack[sp];    }
static inline Value **get_ptr  (u64 idx)  { return &stack[(sp-1)-idx]; }
static inline Value *pop_deref (void)     { return deref(pop());       }
static inline Value *get       (u64 idx)  { return *get_ptr(idx);      }
static inline Value *get_deref (u64 idx)  { return deref(get(idx));    }
static inline void push_val    (Value *x) { stack[sp] = x; sp++;       }
static inline void push        (u64 idx)  { push_val(get_deref(idx));  }

// before: ..rest x y
// after:  ..rest y x
static inline void swap() {
  Value *n1 = pop();
  Value *n2 = pop();
  push_val(n1);
  push_val(n2);
}

void slide(u64 count) {
  Value *top = get_deref(0);
  sp -= count;
  stack[sp-1] = top;
}


////////////////////////////////////////////////////////////////////////////////
//  Accessors

static Value *deref(Value *x);

static inline Type TY(Value *x) {
  if (is_direct(x)) return BIG;
  return x->type;
}

#define SI static inline

SI bool    IS_NAT (Value *x) { return (is_direct(x)  || x->type == BIG); }
SI bool    IS_LAW (Value *x) { return (!is_direct(x) && x->type == LAW); }
SI bool    IS_APP (Value *x) { return (!is_direct(x) && x->type == APP); }
SI Value  *IT     (Value *x) { return deref(x)->p.item;                  }
SI Value  *HD     (Value *x) { return deref(x)->a.f;                     }
SI Value  *TL     (Value *x) { return deref(x)->a.g;                     }
SI Value  *IN     (Value *x) { return x->i.ptr;                          }
SI len_t   WID    (Value *v) { return v->n.size;                         }
SI word_t *BUF    (Value *v) { return (void*) (&(v->n.size) + 1);        }

static inline Value *NM(Value *x) {
  x = deref(x);
  if (x->type == PIN) return NM(x->p.item);
  return x->l.n;
}

static inline Value *AR(Value *x) {
  x = deref(x);
  if (x->type == PIN) return AR(x->p.item);
  return x->l.a;
}

static inline Value *BD(Value *x) {
  x = deref(x);
  if (x->type == PIN) return BD(x->p.item);
  return x->l.b;
}

static inline Law FUNC(Value *x) {
  x = deref(x);
  if (x->type == PIN) return FUNC(x->p.item);
  return x->l;
}


// Allocation //////////////////////////////////////////////////////////////////

static inline void push_direct(u64 x) {
  return push_val(DIRECT(x));
}


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
  Value *res = (Value *)alloc(sizeof(Value));
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
  Value *res = (Value *)alloc(sizeof(Value));
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

SI bool LT  (Value *a, Value *b) { return cmp_normalized(a,b) == 0; }
SI bool GT  (Value *a, Value *b) { return cmp_normalized(a,b) == 2; }
SI bool LTE (Value *a, Value *b) { return cmp_normalized(a,b) != 2; }
SI bool GTE (Value *a, Value *b) { return cmp_normalized(a,b) != 0; }
SI bool EQ  (Value *a, Value *b) { return cmp_normalized(a,b) == 1; }
SI bool NEQ (Value *a, Value *b) { return cmp_normalized(a,b) != 1; }

SI bool EQZ(Value *x) { return (x == DIRECT_ZERO); }
SI bool EQ1(Value *x) { return (x == DIRECT_ONE); }
SI bool EQ2(Value *x) { return (x == DIRECT_TWO); }

static void WordPlusWord(u64 a, u64 b) {
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

static void BigPlusWord(u64 word, Value *big) {
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

static void BigPlusBig(Value *a, Value *b) {
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
static void Add() {
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

static void BigMinusDirect(Value *big, u64 direct) {
  u64 bigSz = big->n.size;
  push_val(big);                           // save
  Value *res  = start_bignat_alloc(bigSz); // gc
  big         = pop();                     // reload
  word_t *buf = BUF(res);
  nn_sub1(buf, BUF(big), bigSz, direct);
  push_val(end_bignat_alloc(res));
}

static void Dec() {
  Value *v = pop_deref();

  if (is_direct(v)) {
    u64 n = get_direct(v);
    push_val( (n == 0) ? DIRECT_ZERO : DIRECT(n - 1) );
    // the result is always direct because (x/u63 - 1) is always a u63
    // unless x==0.
    return;
  }

  BigMinusDirect(v, 1);
}

static void Sub() {
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

static void DirectTimesDirect(u64 a, u64 b) {
  if (a==0 || b==0) {
    push_val(DIRECT_ZERO);
    return;
  }

  u64 res = a * b;

  if ((res / a) == b) { // if no overflow
    push_word(res);
    return;
  }

  Value *ret  = start_bignat_alloc(2); // gc
  word_t *buf = BUF(ret);
  buf[1] = nn_mul1(buf, &a, 1, b);
  push_val(end_bignat_alloc(ret));
}

static void BigTimesDirect(u64 small, Value *big) {
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

static void BigTimesBig(Value *a, Value *b) {
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

static void Mul() {
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

static void DivModDirectDirect(u64 a, u64 b) {
  if (b == 0) {
    // TODO: Crash here
    push_val(DIRECT_ZERO); // mod
    push_val(DIRECT_ZERO); // div
    return;
  }

  push_word(a % b); // mod
  push_word(a / b); // div
}

static void DivModBigDirect(Value *a, u64 b) {
  if (b == 0) {
    // TODO: Crash here
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

static void DivModBigBig(Value *a, Value *b) {
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

static void DivMod() {
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

SI void Div() { DivMod(); slide(1); }
SI void Mod() { DivMod(); pop(); }

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
static void eval_update(int i) {
  Value **p = get_ptr(i);
 again:
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

#define NUM_JETS 8
Jet jet_table[NUM_JETS] =
  { { (Value*)9223372036861355073ULL, 2, J_ADD   }
  , { (Value*)9223372036861228371ULL, 2, J_SUB   }
  , { (Value*)9223372036861883725ULL, 2, J_MUL   }
  , { (Value*)9223372036862536004ULL, 2, J_DIV   }
  , { (Value*)9223372036861357901ULL, 2, J_MOD   }
  , { (Value*)9223372036861289796ULL, 1, J_DEC   }
  , { (Value*)9223372036862143811ULL, 2, J_CMP   }
  , { (Value*)9223372472313803348ULL, 2, J_TRACE }
  };


////////////////////////////////////////////////////////////////////////////////
//  Seeds

void frag_load(Value**, u64, int*, u64*, u64**);

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

void stack_grow(u64 count) {
  for (u64 i = 0; i < count; i++) push_val(NULL);
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

  stack_grow(n_entries);
  Value **tab = get_ptr(n_entries-1); // 0

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

  // The top-most entry is the result
  slide(n_entries - 1);
}

u64 *load_seed_file (const char *filename, u64 *sizeOut) {
  FILE *f = fopen (filename, "rb");

  if (!f) {
    fprintf(stderr, "\n%s\n", filename);
    crash("seed file does not exist");
  }

  fseek(f, 0, SEEK_END);
  u64 szBytes = ftell(f);

  u64 szWords = (szBytes / 8) + (szBytes%8 ? 1 : 0);

  fseek(f, 0, SEEK_SET);
  u64 *buf = calloc(szWords+1, 8); // We add an extra word here
                                   // so that we can over-read
                                   // by one word, this simplifies
                                   // decoding.
  if (!buf) crash("load_seed_file: allocation failed");
  if (fread (buf, 1, szBytes, f) != szBytes) crash("load_seed_file: can't read");
  fclose(f);

  *sizeOut = szWords;
  return buf;
}


////////////////////////////////////////////////////////////////////////////////
//  GC

// argument must always be a heap pointer, never direct.
static inline size_t alloc_size(Value *x) {
  if (x->type == BIG) return (8 * (2 + WID(x)));
  return sizeof(Value);
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
  for (u64 i = 0; i < sp; i++) { *get_ptr(i) = gc_copy(get(i)); }

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
  Value *head = get_deref(0);
  Value *v    = get_deref(idx);
  if (head != v) {
    // no update needed if equal, and IND on self would form a cycle.
    v->type  = IND;
    v->i.ptr = head;
  }
  pop();
}

static inline void mk_app() {
  Value *res = (Value *)alloc(sizeof(Value));
  res->type = APP;
  res->a.g = pop();
  res->a.f = pop();
  push_val(res);
}

static inline void mk_app_rev() {
  Value *res = (Value *)alloc(sizeof(Value));
  res->type = APP;
  res->a.f = pop();
  res->a.g = pop();
  push_val(res);
}

Value *normalize (Value *v) {
 again:
  if (is_direct(v)) return v;
  switch (v->type) {
  case IND: v = IN(v); goto again;
  case APP: v->a.f = normalize(v->a.f);
            v->a.g = normalize(v->a.g);
            return v;
  default:  return v;// P/L/N: already normalized
  }
}

void mk_pin() {
  Value *top = pop_deref();
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

  // neither a let nor a call
}

static inline len_t WordSz(word_t w) { return (u64_bits(w) + 7) / 8; }

len_t ByteSz(Value *bar) {
    if (is_direct(bar)) return WordSz(get_direct(bar));
    int sz           = WID(bar);
    word_t last_word = BUF(bar)[sz-1];
    return ((sz-1) * 8) + WordSz(last_word);
}

void mk_law() {
  to_nat(1); // a
  to_nat(2); // n

  Value *b = normalize(pop_deref());
  Value *a = pop_deref();
  Value *n = pop_deref();
  Law l = { .n = n, .a = a, .b=b, .w = { .n_lets = 0, .n_calls = 0 } };

  weigh_law(1, &l.w, b);

  push_val(a_Law(l));
}

void incr() {
  Value *x = pop_deref();

  if (is_direct(x)) {
    // this doesn't need to deal with overflow because get_direct returns
    // a u63, and push_word can handle a u64.
    push_word(get_direct(x) + 1);
    return;
  }

  if (x->type != BIG) push_val(DIRECT_ONE);
  else BigPlusWord(1, x);
}

void prim_case() {
  Value *o = pop_deref();
  Value *m = pop_deref();
  Value *z = pop_deref();
  Value *a = pop_deref();
  Value *l = pop_deref();
  Value *p = pop_deref();
  switch (TY(o)) {
    case PIN:
      push_val(IT(o)); // o
      push_val(p);     // o p
      mk_app_rev();    // (p o)
      return;
    case LAW:
      push_val(BD(o)); // b
      push_val(AR(o)); // b a
      push_val(NM(o)); // b a n
      push_val(l);     // b a n l
      mk_app_rev();    // b a (l n)
      mk_app_rev();    // b (l n a)
      mk_app_rev();    // (l n a b)
      return;
    case APP:
      push_val(TL(o)); // t
      push_val(HD(o)); // t h
      push_val(a);     // t h a
      mk_app_rev();    // t (a h)
      mk_app_rev();    // (a h t)
      return;
    case BIG: {
      if (EQZ(o)) {
        push_val(z);
        return;
      }
      push_val(m); // m
      push_val(o); // m o
      Dec();       // m d
      mk_app();    // (m d)
      return;
    }
    case IND: crash("plan_case: IND: impossible");
    case MOV:
      crash("MOV escaped GC");
  }
}

void setup_call(u64 depth) {
  // setup the call by pulling the TLs out of all apps which we have
  // unwound.
  for (u64 i = 0; i < depth; i++) {
    stack[(sp-1)-i] = TL(stack[(sp-1)-i]);
  }
}

void flip_stack(u64 depth) {
  if (depth == 0) return;
  Value *tmp;
  u64 d_1 = depth-1;
  for (u64 i = 0; i < depth/2; i++) {
    tmp                   = stack[(sp-1)-i];
    stack[(sp-1)-i]       = stack[(sp-1)-(d_1-i)];
    stack[(sp-1)-(d_1-i)] = tmp;
  }
}

void handle_oversaturated_application(u64 count) {
  // if our application is oversaturated, `depth` will exceed the arity. in this
  // case, we want to re-assemble the apps, and eval the result.
  for (u64 i = 0; i < count; i++) mk_app_rev();
  eval();
}

static inline void backout(u64 depth) {
  // pop stack of unwound apps.
  for (u64 i = 0; i < depth; i++) pop();
  // `eval` saved the outermost APP, and that should now be at the bottom
  // of the stack.
}

Value *kal(u64 maxRef, Value **pool, Value *x) {
  if (is_direct(x)) {
    u64 xv = get_direct(x);
    if (xv > maxRef) return x;                   // unquoted constant
    return get(maxRef - xv);                     // var ref
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

  Value *this_call = (*pool)++;                  // allocte (type is preset)
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

typedef struct GrMem {
  Value *holes;
  Value *apps;
} GrMem;

static void eval_law(Law l) {
  u64 args = get_direct(l.a); // this code is unreachable with bignat arity
  u64 lets = l.w.n_lets;
  u64 kals = l.w.n_calls;
  int maxRef = args + lets;

  const size_t bytes = sizeof(Value) * (lets + kals);

  push_val(l.b);                            // save (law body)
  Value *mem = bytes ? alloc(bytes) : NULL; // gc
  Value *b   = pop();                       // restore (law body)

  // initialize letrec slots, since they might be referenced before they
  // are filled in, but leave APPs uninitialized.  KAL will initialize.

  Value *holes = mem;
  Value *apps  = mem + lets;

  if (lets) {
    // Add a black hole per let.
    for (u64 i = 0; i < lets; i++) stack[sp++] = holes+i;

    // Compute the graph of each let, and fill the corresponding hole.
    for (u64 i = 0; i < lets; i++) {
      // (1 exp next)
      Value *next    = TL(b);
      Value *exp     = TL(HD(b));
      b              = next;
      Value *gr      = kal(maxRef, &apps, exp);
      holes[i].type  = IND;
      holes[i].i.ptr = gr;
    }

  }

  Value *gr = kal(maxRef, &apps, b);
  push_val(gr);                 // .. self args slots bodyGr
  eval();                       // .. self args slots bodyWhnf
  return slide(maxRef+1);       // .. bodyWhnf
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

void Trace (char *end) {
    force_in_place(0);
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
    fwrite(bbuf, 1, bwid - 1, stderr);
    fprintf(stderr, "%s", end);
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
    // TODO: cmp should only eval as much as needed in order to find
    // a difference.  These force calls are wrong.
    force_in_place(0);
    force_in_place(1);
    Value *a = pop();
    Value *b = pop();
    int ord = cmp_normalized(a, b);
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
  flip_stack(ar+1); // +num_constants
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

    return jet.tag;
  }

  return J_NONE;
}

// returns true if it eval-ed
bool law_step(u64 depth) {
  Value *self = pop_deref();
  if (GT(AR(self), DIRECT(depth))) {
    // unsaturated application. this is a little weird, but works?
    if (depth <= 1) return false;
    backout(depth-1);
    return false;
  } else {

    setup_call(depth);
    if (!is_direct(AR(self))) crash("impossible: called law with huge arity");
    u64 ar = get_direct(AR(self));
    run_law(self, ar);
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
  if (!is_direct(op)) goto exception_case;

  switch (get_direct(op)) {
    case 0: { // mk_pin
      pop();
      force_in_place(0);
      return mk_pin();
    }
    case 1: { // mk_law
      pop();
      force_in_place(0);          // b
      eval_update(1);             // a
      eval_update(2);             // n
      return mk_law();
    }
    case 2: { // incr
      pop();
      eval_update(0);
      return incr();
    }
    case 3: { // case
      pop();
      eval_update(0);
      prim_case();
      eval();
      return;
    }
    default: {
      goto exception_case;
    }
  }
exception_case:                      // param tag
  force_in_place(1);                 // *param tag
  fprintf(stderr, "Exception(");
  Trace("): ");                      // param
  Trace("\n");                       //
  exit(0);
}

bool unwind(u64 depth) {
 again:
  Value *x = get_deref(0);
  switch (TY(x)) {
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
          flip_stack(arity);
          push_val(item);
          do_prim(item);
          //
          if (arity < depth) {
            // oversaturated
            handle_oversaturated_application(depth - arity);
          } else {
            // application was perfectly saturated.
          }
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
    case IND: {
      crash("unwind: bad deref");
    }
    case MOV:
      crash("MOV escaped GC");
    default:
      crash("unwind: this should never happen");
  }
}

// returns true if we eval-ed
bool eval() {
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

void force_whnf (void) {
  Value *top = pop_deref();
  if (TY(top) == APP) {
    push_val(TL(top));
    push_val(HD(top));
    force_whnf();
    force();
  }
}

void force (void) {
  Value *top = get_deref(0);
  if (TY(top) == APP) {
    push_val(get_deref(0));
    eval();
    update(1);
    force_whnf();
  } else {
    pop();
  }
}

////////////////////////////////////////////////////////////////////////////////
//  Runner

static void repl (void) {
    { // load seed (starting state)
      static const char *sire_seed = "sire.seed";
      u64 seedSz;
      u64 *words = load_seed_file(sire_seed, &seedSz);
      seed_load(words);
      force_in_place(0);
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
      fwrite(bbuf, 1, owid, stderr);
      fprintf(stderr, "\n");
    }

    if (i==0 && !bytes_read) { return; }

    goto next_input;
}

int main (int argc, char **argv) {
  heap_init();

  { // load printer
    static const char *tracefile = "trace.seed";
    u64 seedSz;
    u64 *words = load_seed_file(tracefile, &seedSz);
    seed_load(words);
    force_in_place(0);
    printer_seed=get_ptr(0);
  }

  repl();
}
