#include <ctype.h>
#include <inttypes.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdnoreturn.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/param.h>
#include <unistd.h>

#include "bsdnt.h"

noreturn void crash(char *s) { printf("Error: %s\n", s); exit(1); }

#define HEAP_MAP_SZ (1ULL << 40) // 1 TB
#define BLOCK_SZ    65536

static char *tospace     = (char*) (1ULL << 24);
static char *hp          = (char*) (1ULL << 24);
static char *fromspace   = (char*) (1ULL << 41);
static char *tospace_end = (char*) ((1ULL << 24) + BLOCK_SZ);

static void gc();

static inline void *alloc(size_t bytes) {
 again:
  char *res = hp;
  hp += bytes;
  if (hp > tospace_end) { gc(); goto again; }
  return res;
}


////////////////////////////////////////////////////////////////////////////////
//  Typedefs

typedef uint64_t u64;

// Note that underlying enum number for NAT, PIN, LAW, APP are in
// sort-order.
typedef enum Type {
  NAT,
  PIN,
  LAW,
  APP,
  IND,
  MOV,
} Type;

typedef enum NatType {
  SMALL,
  BIG
} NatType;

typedef struct BigNat { len_t size; } BigNat;

typedef struct Value Value;

typedef enum JetTag {
  J_ADD,
  J_SUB,
  J_MUL,
  J_DIV,
  J_MOD,
  J_DEC,
  J_CMP,
  J_NONE,
} JetTag;

typedef struct Pin {
  Value *item;
  JetTag jet;
} Pin;

typedef struct LawWeight {
    u64 n_lets;
    u64 n_calls;
} LawWeight;

typedef struct Law {
  Value *n; // Always a nat
  Value *a; // Always a nat
  Value *b;
  LawWeight w;
} Law;

typedef struct App {
  Value *f;
  Value *g;
} App;

struct Value {
  Type type;
  union {
    Pin p;    // PIN
    Law l;    // LAW
    App a;    // APP
    BigNat n; // NAT
    Value *i; // IND
  };
};

////////////////////////////////////////////////////////////////////////////////
//  Prototypes

Value *normalize (Value*);
JetTag jet_match(Value*);

static void push_word(u64);
static Value *DIRECT(u64);

static void swap(void);
static void mk_app(void);
static void clone(void);
static Value *pop(void);
static Value *get(u64);
static Value *get_deref(u64);
static Value *pop_deref(void);
static void slide(u64);
static void update(u64);
static void push(u64);
static void push_val(Value*);
static Value **get_ptr(u64);

void BigPlusDirect(u64, u64);
void force();
bool eval();
void eval_update(int);
static void force_in_place();

void write_dot_extra(char*, char*, Value*);

void frag_load(Value**, u64, int*, u64*, u64**);
bool read_exp(FILE *f);

////////////////////////////////////////////////////////////////////////////////
//  Globals

#define STACK_SIZE 65536
Value *stack[STACK_SIZE];
u64 sp = 0;

////////////////////////////////////////////////////////////////////////////////
//  Nat pointer tagging (ptr-nat)

// if the high bit is set, then the remaining 63 bits should be interpreted as
// a nat. this is simpler than having to modify all pointers to mask/unmask
// their high bit.

// 2^63 - high bit
# define PTR_NAT_MASK          9223372036854775808ull
# define DIRECT_ZERO  ((Value*)9223372036854775808ull)
# define DIRECT_ONE   ((Value*)9223372036854775809ull)
# define DIRECT_TWO   ((Value*)9223372036854775810ull)

static inline bool is_direct(Value *x) {
  return (((word_t) x) & PTR_NAT_MASK);
}

static inline word_t get_direct(Value *x) {
  return (word_t) (((word_t) x) & ~PTR_NAT_MASK);
}

////////////////////////////////////////////////////////////////////////////////
//  Accessors

static inline Value *IN(Value *x) { return x->i; };

static inline Value *deref(Value *x) {
  if (is_direct(x)) return x;
  while (x->type == IND) x = IN(x);
  return x;
}

static inline Value *HD(Value *x) { return deref(x)->a.f; };

static inline Value *TL(Value *x) { return deref(x)->a.g; };

static inline Type TY(Value *x) {
  if (is_direct(x)) return NAT;
  return x->type;
}

static inline bool IS_NAT(Value *x) { return (TY(x) == NAT); }

static inline Value *IT(Value *x) {
  x = deref(x);
  return x->p.item;
};

static inline Value *NM(Value *x) {
  x = deref(x);
  if (x->type == PIN) return NM(x->i);
  return x->l.n;
}

static inline Value *AR(Value *x) {
  x = deref(x);
  if (x->type == PIN) return AR(x->i);
  return x->l.a;
}

static inline Value *BD(Value *x) {
  x = deref(x);
  if (x->type == PIN) return BD(x->i);
  return x->l.b;
}

static inline Law FUNC(Value *x) {
  x = deref(x);
  if (x->type == PIN) return FUNC(x->i);
  return x->l;
}

static inline len_t   WID (Value *v) { return v->n.size; }
static inline word_t *BUF (Value *v) { return (void*) (&(v->n.size) + 1); }


////////////////////////////////////////////////////////////////////////////////
//  Construction

// just allocates the space. caller must fill buf.
Value *start_bignat_alloc(size_t num_words) {
  // tag size words..
  Value *res = (Value *)alloc(8 * (2 + num_words));
  res->type   = NAT;
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

static inline Value *DIRECT(u64 x) {
  return (Value *) (x | PTR_NAT_MASK);
}

static inline void push_word(u64 x) {
  if (!(x & PTR_NAT_MASK)) {
    push_val((Value *) (x | PTR_NAT_MASK));
    return;
  }

  Value *res = (Value *)alloc(3 * 8);
  res->type   = NAT;
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
  case NAT:
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

// TODO change to `Value *` arg style of Mul/DivMod/etc
//
// invariant: a.size >= b.size
// stack before: ..rest b a
// stack after:  ..rest (a+b)
void BigPlusBig(u64 aSize, u64 bSize) {
  long new_size = MAX(aSize, bSize) + 1;
  Value *res = start_bignat_alloc(new_size);
  word_t *buf = BUF(res);
  Value *a = pop_deref();
  Value *b = pop_deref();
  word_t c = nn_add_c(buf, BUF(a), a->n.size, BUF(b), b->n.size, 0);
  buf[new_size - 1] = c;
  push_val(end_bignat_alloc(res));
}

void BigPlusDirect(u64 small, u64 bigSz) {
  u64 newSz       = bigSz + 1;
  Value *res      = start_bignat_alloc(newSz); // gc
  Value *big      = pop();
  word_t carry    = nn_add1(BUF(res), BUF(big), bigSz, small);
  BUF(res)[bigSz] = carry;
  push_val(end_bignat_alloc(res));
}

// arguments must both have already been evaluated and coerced into nats.
void Add() {
  Value *a = pop();
  Value *b = pop();

  u64 aSmall = get_direct(a);
  u64 bSmall = get_direct(b);

  if (is_direct(a)) {
    if (is_direct(b)) {
      // no need to handle overflow, since u63 + u63 always fits in a u64.
      push_word(aSmall + bSmall);
      return;
    }

    push_val(b);
    BigPlusDirect(aSmall, b->n.size);
    return;
  }

  if (is_direct(b)) {
    push_val(a);
    BigPlusDirect(bSmall, a->n.size);
    return;
  }

  push_val(b);
  push_val(a);
  BigPlusBig(a->n.size, b->n.size);
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
  // assert (c == 0);
  push_val(end_bignat_alloc(res));
}

void Dec() {

  Value *v = pop_deref();

  if (is_direct(v)) {
    u64 n = get_direct(v);
    push_val( (n == 0) ? DIRECT_ZERO : DIRECT(n - 1) );
    // the result is always direct because (x/u63 - 1) is always a u63
    // unless x==0.
  } else {
    BigMinusDirect(v, 1);
  }
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

#define NUM_JETS 7
Jet jet_table[NUM_JETS] =
  { (Jet) { .name = ADD,   .arity = 2, .tag = J_ADD   }
  , (Jet) { .name = SUB,   .arity = 2, .tag = J_SUB   }
  , (Jet) { .name = MUL,   .arity = 2, .tag = J_MUL   }
  , (Jet) { .name = DIV,   .arity = 2, .tag = J_DIV   }
  , (Jet) { .name = MOD,   .arity = 2, .tag = J_MOD   }
  , (Jet) { .name = DEC,   .arity = 1, .tag = J_DEC   }
  , (Jet) { .name = CMP,   .arity = 2, .tag = J_CMP   }
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

void stack_grow(u64 count) {
  for (u64 i = 0; i < count; i++) {
    push_val(NULL);
  }
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
//  Interpreter stack fns

static inline Value *pop() {
  sp--;
  return stack[sp];
}

static inline Value *pop_deref() {
  return deref(pop());
}

static inline Value **get_ptr(u64 idx) {
  if (idx >= sp) crash("get: indexed off stack");
  return &stack[(sp-1)-idx];
}

static inline Value *get(u64 idx) {
  return *get_ptr(idx);
}

static inline Value *get_deref(u64 idx) {
  return deref(get(idx));
}

////////////////////////////////////////////////////////////////////////////////
//  GC

static inline size_t alloc_size(Value *x) {
  if (x->type == NAT) return (8 * (2 + WID(x)));
  return sizeof(Value);
}

Value *gc_copy(Value *x) {
  if (x == NULL || is_direct(x))
    return x;

  // if this points into the tospace, we don't need to copy.
  if ((char*)x >= tospace && (char*)x < (tospace + HEAP_MAP_SZ))
    return x;

  if (x->type == MOV) return x->i;

  size_t sz = alloc_size(x);

  // copy + bump heap size
  Value *res = (Value*) hp;
  memcpy(hp, x, sz);
  hp += sz;

  // tell further references where to find the new pointer.
  x->type = MOV;
  x->i = res;

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
  case NAT:
    break;
  case IND:
    x->i = gc_copy(x->i);
    break;
  default:
    fprintf(stderr, "gc_copy_refs: bad value: ptr=%p, tag=%d\n", x, x->type);
    crash("gc_copy_refs: impossible");
  }
}

// Cheney's algorithm
static void gc() {
  // swap the two heaps (with the new heap being empty).
  char *tmp = fromspace;
  fromspace = tospace;
  tospace = tmp;
  hp = tospace;

  // copy roots to new heap.
  for (u64 i = 0; i < sp; i++) {
    *get_ptr(i) = gc_copy(get(i));
  }

  // copy all references from the new heap to the old heap
  for (char *iter = tospace; iter < hp; iter += alloc_size((Value*)iter)) {
    gc_copy_refs((Value*) iter);
  }

  long used     = hp - tospace;
  long new_size = BLOCK_SZ * (1 + (used/BLOCK_SZ));
       new_size = new_size + (new_size / 2);
  tospace_end   = tospace + new_size;
}


////////////////////////////////////////////////////////////////////////////////
//  Interpreter

static void update(u64 idx) {
  Value *head = get_deref(0);
  Value *v    = get_deref(idx);
  if (head != v) {
    // no update needed if equal, and IND on self would form a cycle.
    v->type = IND;
    v->i    = head;
  }
  pop();
}

static inline void push_val(Value *x) { stack[sp] = x; sp++; }
static inline void push(u64 idx)      { push_val(get_deref(idx)); }
static inline void clone()            { push_val(get_deref(0)); }

// before: ..rest f x
// after:  ..rest (f x)
static inline void mk_app() {
  Value *res = (Value *)alloc(sizeof(Value));
  res->type = APP;
  res->a.g = pop();
  res->a.f = pop();
  push_val(res);
}

// before: ..rest x f
// after:  ..rest (f x)
static inline void mk_app_rev() {
  Value *res = (Value *)alloc(sizeof(Value));
  res->type = APP;
  res->a.f = pop();
  res->a.g = pop();
  push_val(res);
}

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

  if (x->type != NAT) {
    push_val(DIRECT_ONE);
    return;
  }

  push_val(x);
  BigPlusDirect(1, x->n.size);
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
    case NAT: {
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

void backout(u64 depth) {
  // pop stack of unwound apps.
  for (u64 i = 0; i < depth; i++) {
    pop();
  }
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

void eval_law(Law l) {
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
      Value *next   = TL(b);
      Value *exp    = TL(HD(b));
      b             = next;
      Value *gr     = kal(maxRef, &apps, exp);
      holes[i].type = IND;
      holes[i].i    = gr;
    }

  }

  Value *gr = kal(maxRef, &apps, b);
  push_val(gr);                 // .. self args slots bodyGr
  eval();                       // .. self args slots bodyWhnf
  return slide(maxRef+1);       // .. bodyWhnf
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

  default:
    goto no_jet;
  }

 no_jet:
  // self is still valid here, we haven't allocated
  push_val(self);
  flip_stack(ar+1);
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
  }

  setup_call(depth);
  if (!is_direct(AR(self))) crash("impossible: called law with huge arity");
  u64 ar = get_direct(AR(self));

  run_law(self, ar);

  if (ar < depth) handle_oversaturated_application(depth - ar);
  return true;
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
exception_case:
  force_in_place(1); // param
  exit(1);
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
        case NAT: {
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
    case NAT: {
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
    case NAT:
      return false;
    case IND: crash("eval: IND");
    default:  crash("eval: bad tag");
  }
}

void force_whnf() {
  Value *top = pop_deref();
  if (TY(top) == APP) {
    push_val(TL(top));
    push_val(HD(top));
    force_whnf();
    force();
  }
}

void force() {
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

len_t direct_byte_width(word_t w) {
  printf("word=%lu, bits=%lu\n", w, u64_bits(w));
  return (u64_bits(w) + 7) / 8;
}

len_t nat_byte_width(Value *bar) {
    if (is_direct(bar)) {
      printf("direct\n");
      return direct_byte_width(get_direct(bar));
    }
    printf("indirect\n");
    int sz           = WID(bar) * 8;
    word_t last_word = ((char*)BUF(bar))[sz-1];
    return ((sz-1) * 8) + direct_byte_width(last_word);
}

len_t barlen(Value *bar) {
  if (!is_direct(bar) && bar->type != NAT)
    crash("barlen: not nat");
  len_t str_len = nat_byte_width(bar);
  printf("str_len=%lu\n", str_len);
  if (str_len == 0) crash("barlen: given zero");
  return str_len - 1;
}

void repl (void) {
    static char buf[128];

    static const char *filename = "sire.seed";
    u64 seedSz;
    u64 *words = load_seed_file(filename, &seedSz);
    seed_load(words);
    force_in_place(0);

  next_input:
    // putv(get(0));
    int i=0;
    memset(buf, 0, 128);

  read_more:

    ssize_t bytes_read = read(0, buf+i, 1);

    if (bytes_read && i < 100 && buf[i] != '\n') { i++; goto read_more; }

    // Create a string from the input.  (TODO use a bar instead).
    buf[i+1] = 0;
    Value *v = start_bignat_alloc(16);
    memcpy(BUF(v), buf, 128);
    push_val(end_bignat_alloc(v)); // state input

    mk_app();                      // (state input)
    force_in_place(0);             // (0 output newstate)
    v = pop();
    Value *output = TL(HD(v));
    v = TL(v);
    push_val(v);                   // newstate

    len_t wid = barlen(deref(output));

    if (wid) {
      int wrote;
      fprintf(stderr, "[%lu]", wid);
      if (wid != (wrote = write(1, BUF(output), wid))) {
        printf("tried=%ld, wrote=%d\n", wid, wrote);
        crash("write() failed");
      }
    }

    if (i==0 && !bytes_read) exit(0);

    goto next_input;
}


int main (int argc, char **argv) {
  int prot   = PROT_READ | PROT_WRITE;
  int flags  = MAP_FIXED | MAP_PRIVATE | MAP_ANON | MAP_NORESERVE;

  if (tospace != mmap((void*) tospace, HEAP_MAP_SZ, prot, flags, -1, 0))
      { perror("tospace: mmap"); exit(1); }

  if (fromspace != mmap((void*) fromspace, HEAP_MAP_SZ, prot, flags, -1, 0))
      { perror("fromspace: mmap"); exit(1); }

  repl();
}
