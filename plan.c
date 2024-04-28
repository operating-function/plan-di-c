// - TODO Use Cheney's algorithm to avoid large stack req during GC
// - TODO Actually (throw away + reuse) old heaps after GC.
// - TODO Separate "pinspace" gc generation (not collected / moved).
// - TODO pinspace backed by file.
// - TODO resume from pinspace snapshots + log
// - TODO WASM

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


////////////////////////////////////////////////////////////////////////////////
//  Crash

noreturn void crash(char *s) {
  printf("Error: %s\n", s);
  exit(1);
}


// Heap ////////////////////////////////////////////////////////////////////////

static char *heap_start = NULL;
static char *hp         = NULL;

// argument is in bytes, but must be a multiple of 8.
static inline void *alloc(size_t bytes) {
  char *res = hp;
  hp += bytes;
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

struct Value;

typedef struct Value Value;

typedef enum JetTag {
  J_ADD,
  J_SUB,
  J_MUL,
  J_DIV,
  J_MOD,
  J_DEC,
  J_CMP,
  J_TRACE,
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

int call_depth = 0;

char dot_lab[1024];

#define TRACE_JET_MATCHES  0
#define TRACE_CALLS        0
#define TRACE_LAWS         0
#define ENABLE_GRAPHVIZ    0
#define STACK_BOUNDS_CHECK 0
#define CHECK_TAGS         0

static bool enable_graphviz = 0;

void write_dot(char *);

Value *normalize (Value*);
JetTag jet_match(Value*);

static Value *direct(u64);

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
bool read_exp();

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
  return (((u64) x) & PTR_NAT_MASK);
}

static inline u64 get_direct(Value *x) {
  return (u64) (((u64) x) & ~PTR_NAT_MASK);
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
    return ck_law(fn_nm, x->i);
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
  sprintf(s, "%s not a NAT!", fn_nm);
  if (x->type != NAT) crash(s);
}

static inline void ck_ind(char *fn_nm, Value *x) {
  char s[14];
  sprintf(s, "%s not a IND!", fn_nm);
  if (x->type != IND) crash(s);
}

static inline Type TY(Value *x) {
  if (is_direct(x)) return NAT;
  return x->type;
}

static inline bool IS_NAT(Value *x) {
  return (TY(x) == NAT);
}

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
  if (x->type == PIN) return NM(x->i);
  return x->l.n;
}

static inline Value *AR(Value *x) {
  x = deref(x);
  #if CHECK_TAGS
  ck_law("AR", x);
  #endif
  if (x->type == PIN) return AR(x->i);
  return x->l.a;
}

static inline Value *BD(Value *x) {
  x = deref(x);
  #if CHECK_TAGS
  ck_law("BD", x);
  #endif
  if (x->type == PIN) return BD(x->i);
  return x->l.b;
}

static inline Law FUNC(Value *x) {
  x = deref(x);
  if (x->type == PIN) return FUNC(x->i);
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
  return x->i;
};

static inline len_t WID(Value *v) {
  return v->n.size;
}

static inline word_t *BUF(Value *v) {
  return (void*) (&(v->n.size) + 1);
}


////////////////////////////////////////////////////////////////////////////////
//  Printing

void check_nat(Value *v) {
  if (v == NULL) crash("check_nat: NULL");

  if (is_direct(v)) return;

  if (v->type != NAT) crash("check_nat: not nat");

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

  switch (TY(v)) {
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
    case NAT:
      check_nat(v);
      break;
    case IND:
      check_value(IN(v));
      break;
    default:
      crash("BAD VALUE TAG");
  }
}

void fprintf_value_internal(FILE *, Value *, int);

void fprintf_nat(FILE *, Value *);

bool is_symbol(const char *);
void fprintf_value(FILE*, Value*);

void fprintf_func_name (FILE *f, Value *law, int recur) {
  assert(TY(law) == LAW);

  Value *nm = NM(law);

  assert(TY(nm) == NAT);

  if (is_direct(nm)) {
    u64 w = get_direct(nm);
    char tmp[9] = {0};
    ((u64*) tmp)[0] = w;
    if (!is_symbol(tmp)) goto fallback;
    fprintf(f, "%s", tmp);
    return;
  }

  {
    long num_chars = nm->n.size * sizeof(word_t);
    char nat_str[num_chars+1];
    memcpy(nat_str, BUF(nm), num_chars);
    nat_str[num_chars] = 0;

    if (!is_symbol(nat_str)) { goto fallback; }
    fprintf(f, "%s", nat_str);
    return;
  }

fallback:
  fprintf(f, "<");
  fprintf_value_internal(f, law, recur);
  fprintf(f, ">");
}

void fprintf_value(FILE *f , Value *v) {
  switch (TY(v)) {
  case PIN:
    fprintf(f, "<");
    fprintf_value(f, IT(v));
    fprintf(f, ">");
    break;
  case LAW:
    fprintf(f, "{");
    fprintf_nat(f, NM(v));
    fprintf(f, " ");
    fprintf_nat(f, AR(v));
    fprintf(f, " ");
    fprintf_value_internal(f, BD(v), 0);
    fprintf(f, "}");
    break;
  default:
    fprintf_value_internal(f, v, 0);
  }
}

void fprintf_value_app(FILE *f, Value *v, int recur) {
  if (TY(v) != APP) {
    return fprintf_value_internal(f, v, recur);
  }
  fprintf_value_app(f, HD(v), recur);
  fprintf(f, " ");
  fprintf_value_internal(f, TL(v), recur+1);
}

void fprintf_value_internal(FILE *f, Value *v, int recur) {
  v = deref(v);
  if (recur > 20) {
    fprintf(f, "‥");
    return;
  }
  switch (TY(v)) {
    case PIN:
      Value *item = deref(IT(v));

      if (TY(item) == LAW) {
          fprintf_func_name(f, item, recur+1);
          break;
      }

      fprintf(f, "<");
      fprintf_value_internal(f, item, recur+1);
      fprintf(f, ">");
      break;
    case LAW:
      fprintf(f, "{");
      fprintf_nat(f, NM(v));
      fprintf(f, "}");
      break;
    case APP:
      fprintf(f, "(");
      fprintf_value_app(f, v, recur+1);
      fprintf(f, ")");
      break;
    case NAT:
      fprintf_nat(f, v);
      break;
    case IND:
      crash("fprintf_value_internal: got IND");
    default:
      fprintf(f, "!!");
      break;
  }
}

static inline bool issym (char c) {
  return (c == '_' || isalnum(c));
}

bool is_symbol(const char *str) {
  if (str[0] == 0) return false;
  if (str[1] == 0) return isalpha(str[0]);
  again: {
  char c = *str;
  if (!c) return true;
  if (!issym(c)) return false;
  str++;
  goto again;
  }
}


void fprintf_nat(FILE *f, Value *v) {
  assert(TY(v) == NAT);

  if (is_direct(v)) {
    u64 w = get_direct(v);
    char tmp[9] = {0};
    ((u64*) tmp)[0] = w;
    if (is_symbol(tmp)) {
      fprintf(f, "%%%s", tmp);
    } else {
      fprintf(f, "%" PRIu64, w);
    }
    return;
  }

  long num_chars = v->n.size * sizeof(word_t);
  // TODO: print string directly, instead of copying to the stack.
  char nat_str[num_chars+1];
  memcpy(nat_str, BUF(v), num_chars);
  nat_str[num_chars] = 0;

  if (is_symbol(nat_str)) {
    // symbolic, so we can print it as a string, with a leading `%`
    fprintf(f, "%%%s", nat_str);
  } else {
    // non-symbolic, so we use bsdnt to print as decimal
    char *tmp = nn_get_str(BUF(v), v->n.size);
    fprintf(f, "%s", tmp);
    free(tmp);
  }
}

bool is_symbol_nat(u64 nat) {
  char tmp[9] = {0};
  memcpy(tmp, (char *)(&nat), 8);
  return is_symbol(tmp);
}

void show_direct_nat(char *buf, Value *v) {
  u64 nat = get_direct(v);
  if (is_symbol_nat(nat)) {
    u64 *lol = (u64*) buf;
    *lol = nat;
  } else {
    sprintf(buf, "%lu", nat);
  }
}

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
    return direct(buf[0]);
  }

  if (sz == old_sz) return v;

  v->n.size = sz;            // shrink size
  hp -= (8 * (old_sz - sz)); // shrink heap
  return v;
}

static inline Value *direct(u64 x) {
  if (!(x & PTR_NAT_MASK)) {
    return (Value *) (x | PTR_NAT_MASK);
  }

  Value *res = start_bignat_alloc(1);
  BUF(res)[0] = x;
  return res; // always correct, no need to shrink.
}

static inline Value *a_Pin(Value *item) {
  Value *res = (Value *)alloc(sizeof(Value));
  res->type = PIN;
  JetTag jet = jet_match(item);
  res->p = (Pin){ .item = item, .jet = jet };
  return res;
}

static inline Value *a_Law(Law l) {
  Value *res = (Value *)alloc(sizeof(Value));
  *res = (Value){ .type = LAW, .l = l };
  return res;
}

static inline Value *a_App(Value *f, Value *g) {
  Value *res = (Value *)alloc(sizeof(Value));
  res->type = APP;
  res->a.f = f;
  res->a.g = g;
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

static inline void *realloc_(void *ptr, size_t sz) {
  void *res = realloc(ptr, sz);
  if (!res) {
    perror("realloc");
    exit(1);
  }
  return res;
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
      push_val(direct(aSmall + bSmall));
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
  word_t *buf = BUF(res);
  big         = pop_deref();               // reload
  word_t c = nn_sub1(buf, BUF(big), bigSz, direct);
  // a positive borrow (nonzero `c`) should only be possible if we
  // underflowed a single u64. our invariant is to convert to SMALL when we
  // reach 1 u64, so we should never encounter this case.
  assert (c == 0);
  push_val(end_bignat_alloc(res));
}

void Dec() {
  #if ENABLE_GRAPHVIZ
  write_dot_extra("<Dec>", "", NULL);
  #endif

  Value *v = pop_deref();

  if (is_direct(v)) {
    u64 n = get_direct(v);
    push_val( (n == 0) ? DIRECT_ZERO : direct(n - 1) );
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
      push_val(direct(aSmall - bSmall));
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
  word_t *buf = BUF(res);

  a = pop_deref();
  b = pop_deref();
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
    push_val(direct(res));
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
  nn_mul1(buf, BUF(big), big->n.size, small);
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

  push_val(direct(a % b)); // mod
  push_val(direct(a / b)); // div
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
  push_val(direct(mod));           // mod
  push_val(end_bignat_alloc(res)); // div
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
  Value *name;
  u64 arity;
  JetTag tag;
} Jet;

static inline void to_nat(int i) {
  eval_update(i);
  Value **p = get_ptr(i);
  if (!IS_NAT(*p)) { *p = direct(0); }
}

void before_eval(int i) {
  if (!TRACE_CALLS) return;
  for (int i=0; i<call_depth; i++) fprintf(stderr, " ");
  fprintf_value(stderr, get_deref(i));
  fprintf(stderr, "\n");
  call_depth++;
}

void after_eval(int i) {
  if (!TRACE_CALLS) return;
  call_depth--;
  for (int i=0; i<call_depth; i++) fprintf(stderr, " ");
  fprintf(stderr, "=> ");
  fprintf_value(stderr, get_deref(i));
  fprintf(stderr, "\n");
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

void stack_grow(u64 count) {
  #if ENABLE_GRAPHVIZ
  snprintf(dot_lab, 1024, "stack_grow %lu", count);
  write_dot(dot_lab);
  #endif
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
    *next_ref++ = a_Pin(direct(0));
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
    *next_ref++ = direct(inpbuf[used++]);
  }

  {
    uint8_t *byte_buf = (void*) (inpbuf + used);
    for (int i=0; i<n_bytes; i++) {
      *next_ref++ = direct(byte_buf[i]);
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

static inline Value *deref(Value *x) {
  while (TY(x) == IND) {
    x = IN(x);
  }
  return x;
}

static inline Value *pop() {
  if (sp == 0) crash("pop: empty stack");
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

// TODO this is linear in stack depth, which could cause overflow.  Use
// Cheney's algorithm.
//
// returns the moved pointer in the new heap
Value *gc_copy(Value *x) {
  if (x == NULL) return NULL;

  if (is_direct(x)) return x;

  if (x->type == MOV) return x->i;

  if (x->type == APP) {
    Value *f   = x->a.f;
    Value *g   = x->a.g;
    Value *res = a_App(NULL, NULL);
    x->type    = MOV;
    x->i       = res;
    res->a.f   = gc_copy(f);
    res->a.g   = gc_copy(g);
    return res;
  }

  Value *ret = alloc(sizeof(Value));

  switch (x->type) {
    case IND:
      if (x->i == x) { // trivial self-loop
        Value *res = alloc(sizeof(Value));
        res->type = IND;
        res->i    = res;
        return res;
      }
      ret = gc_copy(x->i);
      break;
    case PIN: {
      Value *it = gc_copy(IT(x));
      ret = a_Pin(it);
      break;
    }
    case LAW: {
      Value *nm = gc_copy(NM(x));
      Value *ar = gc_copy(AR(x));
      Value *bd = gc_copy(BD(x));
      ret = a_Law((Law){nm, ar, bd, x->l.w});
      break;
    case NAT:
      ret = start_bignat_alloc(WID(x));
      memcpy(BUF(ret), BUF(x), 8 * WID(x));
      // no need for end_bignat_alloc because input is always valid.
      break;
    }
    default:
      crash("gc_copy: impossible");
  }
  x->type = MOV;
  x->i = ret;
  return ret;
}

void gc() {
  for (u64 i = 0; i < sp; i++) {
    *get_ptr(i) = gc_copy(get(i));
  }
}

////////////////////////////////////////////////////////////////////////////////
//  DOT printing

int dot_count = 0;
char *dot_dir_path = "./dot";

char *p_ptr(Value *x) {
  char *buf = alloc(48);
  if (x == NULL) {
    sprintf(buf, "N_null");
  } else if (is_direct(x)) {
    sprintf(buf, "ptr_nat_%lu", get_direct(x));
  } else {
    sprintf(buf, "N_%p", x);
  }
  return buf;
}

// TODO turn `Node *` into `Value *` tree of APPs
void fprintf_heap(FILE *f, Node *input, Node *seen) {
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
      fprintf_nat(f, NM(v));
      fprintf(f, "\\}\"];\n");
      // fprintf(f, " ar:");
      // fprintf_nat(f, AR(v));
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
    case NAT: {
      char *v_p = p_ptr(v);
      fprintf(f, "%s [label=\"", v_p);
      fprintf_nat(f, v);
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

void fprintf_stack(FILE *f) {
  // print "stack topper"
  // => stack [label="<ss> stack|<s0>|<s1>|<s2>", color=blue, height=2.5];
  fprintf(f, "stack [label=\"<ss> stack");
  for (int i = 0; i < sp; i++) {
    char label[256] = "";
    if (is_direct(get(i))) show_direct_nat(label, get(i));
    fprintf(f, "| <s%d> %s ", i, label);
  }
  fprintf(f, "\", color=blue, height=2.5];\n");

  // print edges between stack topper Values
  for (int i = 0; i < sp; i++) {
    Value *v = get(i);
    if (is_direct(v)) continue;
    char *v_p = p_ptr(v);
    fprintf(f, "stack:s%d -> %s;\n", i, v_p);
    free(v_p);
  }
}

Node *stack_to_list_heap_only() {
  Node *l = NULL;
  if (sp == 0) return l;
  for (u64 i = 0; i < sp; i++) {
    if (is_direct(get(i))) continue;
    l = cons((void *)get(i), l);
  }
  return l;
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
  fprintf_stack(f);
  fprintf(f, "\n// heap\n");

  Node *heap_input = stack_to_list_heap_only();
  if (v != NULL) {
    heap_input = cons((void *)v, heap_input);
  }
  fprintf_heap(f, heap_input, NULL);

  fprintf(f, "\n// extra\n");
  fprintf(f, "%s\n", extra);
  fprintf(f, "}\n");
  fclose(f);
}

void write_dot(char *label) {
  write_dot_extra(label, "", NULL);
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
    v->type = IND;
    v->i    = head;
  }
  pop();
}

static inline void push_val(Value *x) {
  #if ENABLE_GRAPHVIZ
  char extra[50];
  char *x_p = p_ptr(x);
  sprintf(extra, "i[color=red];\ni -> %s", x_p);
  free(x_p);
  write_dot_extra("push_val", extra, x);
  #endif

  #if STACK_BOUNDS_CHECK
  if ((sp+1) > STACK_SIZE) crash("push_val: stack overflow");
  #endif

  stack[sp] = x;
  sp++;
}

static inline void push(u64 idx) {
  #if ENABLE_GRAPHVIZ
  snprintf(dot_lab, 1024, "push %lu", idx);
  write_dot(dot_lab);
  #endif

  push_val(get_deref(idx));
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
  //
  Value *x = pop();
  Value *f = pop();
  Value *fx = a_App(f, x);
  push_val(fx);
}

// before: ..rest x f
// after:  ..rest (f x)
static inline void mk_app_rev() {
  #if ENABLE_GRAPHVIZ
  write_dot("mk_app_rev");
  #endif
  //
  Value *f = pop();
  Value *x = pop();
  Value *ap = a_App(f, x);
  push_val(ap);
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
  #if ENABLE_GRAPHVIZ
  snprintf(dot_lab, 1024, "slide %lu", count);
  write_dot(dot_lab);
  #endif
  //
  Value *top = get_deref(0);
  sp -= count;
  stack[sp-1] = top;
  //
  #if ENABLE_GRAPHVIZ
  snprintf(dot_lab, 1024, "post slide %lu", count);
  write_dot(dot_lab);
  #endif
}

void mk_pin() {
  #if ENABLE_GRAPHVIZ
  write_dot("mk_pin");
  #endif

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
  #if ENABLE_GRAPHVIZ
  write_dot("mk_law");
  #endif

  to_nat(1); // a
  to_nat(2); // n
  Value *b = normalize(pop_deref());
  Value *a = pop_deref();
  Value *n = pop_deref();

  Law l = { .n = n, .a = a, .b=b, .w = { .n_lets = 0, .n_calls = 0 } };

  weigh_law(1, &l.w, b);

  if (TRACE_LAWS) {
    fprintf(stderr, "law: name=");
    fprintf_value(stderr, n);
    fprintf(stderr, ",\t{lets=%lu, calls=%lu}\n", l.w.n_lets, l.w.n_calls);
  }

  push_val(a_Law(l));
}

void incr() {
  #if ENABLE_GRAPHVIZ
  write_dot("incr");
  #endif

  Value *x = pop_deref();

  if (is_direct(x)) {
    push_val(direct(get_direct(x) + 1));
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
  #if ENABLE_GRAPHVIZ
  write_dot("prim_case");
  #endif

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
      push_val(o);  // o
      Dec();        // d
      push_val(m);  // d m
      mk_app_rev(); // (m d)
      return;
    }
    case IND: crash("plan_case: IND: impossible");
    case MOV:
      crash("MOV escaped GC");
  }
}

void setup_call(u64 depth) {
  #if ENABLE_GRAPHVIZ
  snprintf(dot_lab, 1024, "setup_call %lu", depth);
  write_dot(dot_lab);
  #endif

  // setup the call by pulling the TLs out of all apps which we have
  // unwound.
  for (u64 i = 0; i < depth; i++) {
    stack[(sp-1)-i] = TL(stack[(sp-1)-i]);
  }
}

void flip_stack(u64 depth) {
  #if ENABLE_GRAPHVIZ
  snprintf(dot_lab, 1024, "flip_stack %lu", depth);
  write_dot(dot_lab);
  #endif
  //
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
  #if ENABLE_GRAPHVIZ
  snprintf(dot_lab, 1024, "handle_oversaturated_application %lu", count);
  write_dot(dot_lab);
  #endif
  //
  // if our application is oversaturated, `depth` will exceed the arity. in this
  // case, we want to re-assemble the apps, and eval the result.
  for (u64 i = 0; i < count; i++) {
    mk_app_rev();
  }
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

  #if ENABLE_GRAPHVIZ
  {
    snprintf(dot_lab, 1024, "eval_law(arity=%lu, lets=%lu)", args, lets);
    write_dot(dot_lab);
  }
  #endif

  const size_t bytes = sizeof(Value) * (lets + kals);

  push_val(l.b);              // save (law body)
  Value *mem  = alloc(bytes); // gc
  Value *b = pop();           // restore (law body)

  // initialize letrec slots, since they might be referenced before they
  // are filled in, but leave APPs uninitialized.  KAL will initialize.

  Value *holes = mem;
  Value *apps  = mem + lets;

  #if ENABLE_GRAPHVIZ
  write_dot("starting graph construction");
  #endif

  if (lets) {
    // Add a black hole per let.
    for (u64 i = 0; i < lets; i++) stack[sp++] = holes+i;

    #if STACK_BOUNDS_CHECK
    if (sp > STACK_SIZE) crash("eval_law: stack overflow");
    #endif

    #if ENABLE_GRAPHVIZ
    for (u64 i = 0; i < lets; i++) {
      holes[i].type = IND;
      holes[i].i    = NULL;
    }
    write_dot("added holes for lets");
    #endif

    // Compute the graph of each let, and fill the corresponding hole.
    for (u64 i = 0; i < lets; i++) {
      // (1 exp next)
      Value *next   = TL(b);
      Value *exp    = TL(HD(b));
      b             = next;
      Value *gr     = kal(maxRef, &apps, exp);
      holes[i].type = IND;
      holes[i].i    = gr;

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
  before_eval(0);
  eval();                       // .. self args slots bodyWhnf
  after_eval(0);
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
    push_val(direct(ord));
    return;

  case J_TRACE:                   // .. body msg
    force_in_place(0);            // .. body msg
    Value *msg = pop();           // .. body
    fprintf_value(stdout, msg);
    fprintf(stdout, "\n");
    eval();                       // .. *body
    return;

  default:
    break;
  }

 no_jet:
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

    if (NEQ(l.a, direct(jet.arity))) continue;
    if (NEQ(l.n, jet.name)) continue;

    if (TRACE_JET_MATCHES) {
      fprintf(stderr, "MATCH: jet name + arity match: ");
      fprintf_value(stderr, jet.name);
      fprintf(stderr, "\n");
    }

    return jet.tag;
  }

  if (TRACE_JET_MATCHES) {
    fprintf(stderr, "NO MATCH: pinned law is not a jet: ");
    fprintf_value(stderr, l.a);
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
  //
  Value *self = pop_deref();
  if (GT(AR(self), direct(depth))) {
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

    if (TRACE_CALLS) {
      for (int i=0; i<call_depth; i++) fprintf(stderr, " ");
      fprintf_value(stderr, get_deref(depth-1));
      fprintf(stderr, "\n");
      call_depth++;
    }

    setup_call(depth);
    if (!is_direct(AR(self))) crash("impossible: called law with huge arity");
    u64 ar = get_direct(AR(self));

    run_law(self, ar);

    if (TRACE_CALLS) {
      call_depth--;
      for (int i=0; i<call_depth; i++) fprintf(stderr, " ");
      fprintf(stderr, "=> ");
      fprintf_value(stderr, get_deref(0));
      fprintf(stderr, "\n");
    }
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
  //
  if (!is_direct(op)) goto exception_case;

  // char lob[40];
  // sprintf(lob, "do_prim: %lu", get_direct(op));

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
  fprintf(stdout, "Exception(");
  fprintf_value(stdout, get_deref(0));
  fprintf(stdout, "): ");
  fprintf_value(stdout, get_deref(1));
  fprintf(stdout, "\n");
  exit(0);
}

bool unwind(u64 depth) {
 again:
  #if ENABLE_GRAPHVIZ
  snprintf(dot_lab, 1024, "unwind %lu", depth);
  write_dot(dot_lab);
  #endif
  //
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
    case NAT:
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

// when `is_sym == true`,  we are parsing symbols.
// when `is_sym == false`, we are parsing digits.
// this seems tidier than passing a function pointer, as issym & isdigit do not
// have the same type (??).
void read_str_input(bool is_sym) {
  char c;
  int i=0;
  for (; true; i++) {
    str_buf[i] = c = getchar();
    if (is_sym  && (!issym(c)))   break;
    if (!is_sym && (!isdigit(c))) break;
    if (i >= STR_BUF_LEN) crash("read_str_input: input too big");
  }
  str_buf[i] = 0;
  ungetc(c,stdin);
}

void read_atom() {
  read_str_input(false);
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
void read_app() {
  bool saw_space = false;
  while (true) {
    char c = getchar();
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
        ungetc(c, stdin);
        read_exp();
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

void read_sym() {
  read_str_input(true);
  int len = strlen(str_buf);
  if (!len) crash("Empty symbol");
  utf8_nat(str_buf);
}

Value **symbol_table;

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
  // fprintf(stderr, "TABLE: ");
  // fprintf_value(stderr, x);
  // fprintf(stderr, "\n");
  while (!is_direct(x)) {
    Value *hx = HD(x);
    Value *v  = TL(x);
    Value *k  = TL(hx);
    x=HD(hx);
    if (EQ(nm, k)) { push_val(v); return; }
  }
  fprintf_value(stderr, nm);
  crash("symbol not found");
}

bool read_exp() {
again:
  char c = getchar();

  if (feof(stdin)) return false;

  if (isalpha(c)) {
    ungetc(c, stdin);
    read_sym();
    lookup_symbol();
    return true;
  }

  switch (c) {
  case 0:
    return false;

  case '%':
    read_sym();
    return true;

  case ' ':
  case '\r':
  case '\n':
  case '\t':
    goto again;

  case ';':
    while (1) {
      char c = getchar();
      if (feof(stdin)) return false;
      switch (c) {
      case 0:    return false;
      case '\n': goto again;
      default:   continue;
      }
    }

  case '#': {
    char n = getchar();
    ungetc(n, stdin);
    if (isalpha(n)) {
      read_sym();
      mk_pin();
      return true;
    }
    if (isdigit(n)) {
      read_atom();
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
        buf[i] = getchar();
        if (feof(stdin)) { crash("Unexpected EOF"); }
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
    read_str_input(true);
    int len = strlen(str_buf);
    if (!len) crash("Empty seed");
    char buf[1234] = "./seed/";
    strcpy(buf+7, str_buf);
    u64 seedSz;
    u64 *words = load_seed_file(buf, &seedSz);
    seed_load(words);
    check_value(get(0));
    force_in_place(0);
    check_value(get(0));
    return true;
  }

  case '(':
      bool ret = read_exp();
      if (!ret) return false;
      read_app();
      return true;

  default:
    if (isdigit(c)) {
        ungetc(c, stdin);
        read_atom();
        return true;
    }
    fprintf(stderr, "Unexpected: '%c'\n", c);
    exit(2);
  }
}

void repl () {
  bool isInteractive = isatty(fileno(stdin));

 next_input:
  if (isInteractive) printf(">> ");

 loop:
  char c = getchar();

  if (feof(stdin)) return;

  switch (c) {
  case '\t':
  case '\n':
  case '\r':
  case ' ':
    goto loop;

  case ';':
    while (1) {
      char c = getchar();
      if (feof(stdin)) return;
      switch (c) {
      case 0:    return;
      case '\n': goto next_input;
      default:   continue;
      }
    }

  case '!':
    if (!read_exp()) { crash("no value"); }
    if (!read_exp()) { crash("no value"); }
    force_in_place(0);
    force_in_place(1);
    Value *y = pop();
    Value *x = pop();

    if (NEQ(x,y)) {
      fprintf(stderr, "FAILED ");
      fprintf_value(stderr, x);
      fprintf(stderr, " ");
      fprintf_value(stderr, y);
      fprintf(stderr, "\n");
      crash("assertion failed");
    }

    fprintf(stderr, "PASSED ");
    fprintf_value(stderr, x);
    fprintf(stderr, "\n");

    gc();

    goto next_input;


  case '=':
    read_sym();
    if (!read_exp()) { crash("no value"); }
    Value *val = pop();
    Value *nm  = pop();
    bind_symbol(nm, val);
    fprintf(stderr, "=(");
    fprintf_value(stderr, nm);
    fprintf(stderr, ") ");
    fprintf_value(stderr, val);
    fprintf(stderr, "\n");
    goto next_input;

  default:
    ungetc(c, stdin);
    if (!read_exp()) return;
    force_in_place(0);
    fprintf_value(stdout, pop_deref());
    printf("\n");
    goto next_input;
  }
}

#define HEAP_MAP_SZ (1ULL << 42) // 4 TB
#define HEAP_LOCAL  (1ULL << 24)

int main (void) {
  int prot   = PROT_READ | PROT_WRITE;
  int flags  = MAP_FIXED | MAP_PRIVATE | MAP_ANON | MAP_NORESERVE;
  heap_start = mmap((void*) HEAP_LOCAL, HEAP_MAP_SZ, prot, flags, -1, 0);
  hp         = heap_start;

  if (heap_start == MAP_FAILED) { perror("heap_init(): mmap"); exit(1); }

  push_val(DIRECT_ZERO);
  symbol_table = get_ptr(0);

  // Value *x = direct(UINT64_MAX);
  // Value *y = direct(3);
  // Value *arr[2] = { x, y };
  // Value *res = jet_table[0].jet_exec(arr);
  // fprintf_value(stdout, res);
  // printf("\n");

  #if ENABLE_GRAPHVIZ
  struct stat st = {0};
  if (stat(dot_dir_path, &st) == -1) {
    mkdir(dot_dir_path, 0700);
  }
  #endif

  repl();

  #if ENABLE_GRAPHVIZ
  write_dot("main final");
  #endif
}
