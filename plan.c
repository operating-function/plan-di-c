// TODO
//
// GC:
// - copy system malloc code
// - define malloc in terms of system-malloc
// - global heap ptr
// - global heap size
// - on each alloc, GC
// - system-malloc new heap
// - copy live stuff from old heap to new heap
// - free old heap

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

#include "linked_list.h"


////////////////////////////////////////////////////////////////////////////////
//  Crash

noreturn void crash(char *s) {
  printf("Error: %s\n", s);
  exit(1);
}


// Heap ////////////////////////////////////////////////////////////////////////

#define HEAP_CHUNK 8192

char *heap = NULL;
size_t heap_used = 0;
size_t heap_size = 0;

void *realloc(void *ptr, size_t sz) {
  crash("realloc(): not implemented");
}

void *slow_malloc(size_t bytes) {
  if (bytes % 8) bytes += (8 - (bytes % 8));
 again:
  // fprintf(stderr, "malloc(%lu, heap=%p, heap_used=%lu, heap_size=%lu)\n", bytes, heap, heap_used, heap_size);
  if (heap_used + bytes > heap_size) {
    if ((void*)(-1) == sbrk(HEAP_CHUNK))
      crash("sbrk failed");
    heap_size += HEAP_CHUNK;
    goto again;
  }
  char *result = heap + heap_used;
  heap_used += bytes;
  return result;
}

static inline void *our_malloc_words(size_t bytes) {
  if (heap_used + bytes > heap_size) {
    return slow_malloc(bytes);
  }
  char *result = heap + heap_used;
  heap_used += bytes;
  return result;
}

static inline void *our_calloc(size_t nmemb, size_t size) {
  size_t sz = nmemb * size;
  char *res = slow_malloc(sz);
  memset(res, 0, sz);
  return (void*) res;
}

void *reallocarray(void *ptr, size_t nmemb, size_t size) {
  crash("reallocarray(): not implemented");
}

void free(void *ptr)                    { return; }

void heap_init () {
  heap = sbrk(0);
  heap_size = HEAP_CHUNK;
  heap_used = 0;
  sbrk(HEAP_CHUNK);
}

void *calloc(size_t nmemb, size_t size) {
  if (heap == NULL) heap_init();
  return our_calloc(nmemb, size);
}

void *malloc(size_t bytes) {
  if (heap == NULL) heap_init();
  return slow_malloc(bytes);
}

static inline void *our_nn_init(size_t n_words) {
  return our_malloc_words(n_words * 8);
}


////////////////////////////////////////////////////////////////////////////////
//  Typedefs

typedef uint64_t u64;

typedef enum Type {
  PIN,
  LAW,
  APP,
  NAT,
  IND,
  HOL
} Type;

typedef enum NatType {
  SMALL,
  BIG
} NatType;

typedef struct BigNat {
  len_t size;
  nn_t buf;
} BigNat;

struct Value;

typedef struct Value Value;

typedef enum JetTag {
  J_ADD,
  J_SUB,
  J_MUL,
  J_DIV,
  J_MOD,
  J_DEC,
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

#define TRACE_JET_MATCHES  0
#define TRACE_CALLS        0
#define TRACE_LAWS         0
#define ENABLE_GRAPHVIZ    0
#define STACK_BOUNDS_CHECK 1

static bool enable_graphviz = 0;

void write_dot(char *);

Value *normalize (Value*);
JetTag jet_match(Value*);

static Value *direct(u64);

static void mk_app();
static void clone();
static Value *pop();
static Value *get();
static Value *get_deref();
static Value *pop_deref();
static void slide(u64);
static void update(u64);
static void push(u64);
static void push_val(Value*);
static Value **get_ptr(u64);

void BigPlusDirect(u64, u64);
void force();
bool eval();
void eval_update(int);

void write_dot_extra(char*, char*, Value*);

void frag_load(Value**, u64, int*, u64*, u64**);
Value *read_exp();

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
u64 ptr_nat_mask   =          9223372036854775808ull;
Value *direct_zero = (Value*) 9223372036854775808ull;
Value *direct_one  = (Value*) 9223372036854775809ull;
Value *direct_two  = (Value*) 9223372036854775810ull;

static inline bool is_direct(Value *x) {
  return (((u64) x) & ptr_nat_mask) != 0;
}

static inline u64 get_direct(Value *x) {
  return (u64) (((u64) x) & ~ptr_nat_mask);
}

////////////////////////////////////////////////////////////////////////////////
//  Accessors

#define CHECK_TAGS 1

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

static inline BigNat BN(Value *x) {
  if (is_direct(x)) crash("BN: got direct");
  x = deref(x);
  #if CHECK_TAGS
  ck_nat("BN", x);
  #endif
  return x->n;
};

static inline Value *IN(Value *x) {
  #if CHECK_TAGS
  ck_ind("IN", x);
  #endif
  return x->i;
};

////////////////////////////////////////////////////////////////////////////////
//  Printing

void check_nat(Value *v) {
  if (v == NULL) crash("check_nat: NULL");

  if (is_direct(v)) return;

  if (v->type != NAT) crash("check_nat: not nat");

  BigNat n = BN(v);

  if (n.size == 0) crash("check_nat: bignat zero");

  if (n.size == 1) {
    if (n.buf[0] < ptr_nat_mask) {
      crash("check_nat: direct atom encoded as bignat");
    }
    return;
  }

  if (n.buf[n.size - 1] == 0) {
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
    case HOL:
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

  BigNat n = BN(nm);

  {
    long num_chars = n.size *sizeof(word_t);
    char nat_str[num_chars+1];
    memcpy(nat_str, n.buf, num_chars);
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
    case HOL:
      fprintf(f, "<>");
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

  BigNat n = BN(v);

  long num_chars = n.size *sizeof(word_t);
  char nat_str[num_chars+1];
  memcpy(nat_str, n.buf, num_chars);
  nat_str[num_chars] = 0;

  if (is_symbol(nat_str)) {
    // symbolic, so we can print it as a string, with a leading `%`
    fprintf(f, "%%%s", nat_str);
  } else {
    // non-symbolic, so we use bsdnt to print as decimal
    char *tmp = nn_get_str(n.buf, n.size);
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

Value *a_Big(BigNat n) {
  while (n.size && n.buf[n.size - 1] == 0) n.size--;

  if (n.size == 0)
    return direct(0);

  if (n.size == 1 && 0 == (n.buf[0] >> 63)) {
    return direct(n.buf[0]);
  }

  Value *res = (Value *)our_malloc_words(sizeof(Value));
  *res = (Value){ .type = NAT, .n = n };
  return res;
}

void push_big(BigNat n) {
  push_val(a_Big(n));
}

static inline Value *direct(u64 x) {
  if (!(x >> 63)) return (Value *) (x | ptr_nat_mask);
  nn_t x_nat = our_nn_init(1);
  x_nat[0] = x;
  return a_Big((BigNat){ .size = 1, .buf = x_nat });
}

Value *a_Pin(Value *item) {
  Value *res = (Value *)our_malloc_words(sizeof(Value));
  res->type = PIN;
  JetTag jet = jet_match(item);
  res->p = (Pin){ .item = item, .jet = jet };
  return res;
}

Value *a_App(Value *f, Value *g) {
  Value *res = (Value *)our_malloc_words(sizeof(Value));
  res->type = APP;
  res->a.f = f;
  res->a.g = g;
  return res;
}

Value *a_Hol() {
  Value *res = (Value *)our_malloc_words(sizeof(Value));
  res->type = HOL;
  return res;
}

////////////////////////////////////////////////////////////////////////////////
//  Nat Operators

int less=0, equals=1, greater=2;

int cmp_direct(u64 a, u64 b) {
  if (a == b) return equals;
  if (a < b) return less;
  return greater;
}

int big_cmp(BigNat a, BigNat b) {
  if (a.size != b.size) {
    return (a.size < b.size) ? less : greater;
  }

  int nnres = nn_cmp_m(a.buf, b.buf, a.size);

  if (nnres < 0) return less;
  if (nnres == 0) return equals;
  return greater;
}

int cmp(Value *a, Value *b) {

  if (is_direct(a)) {
    if (!is_direct(b)) return less;
    return cmp_direct(get_direct(a), get_direct(b));
  }

  if (is_direct(b)) return greater;

  if (a->type == NAT) {
    if (b->type != NAT) return less;
    return big_cmp(a->n, b->n);
  }

  if (b->type == NAT) return greater;

  crash("make cmp support recursion");
}

static inline bool LT(Value *a, Value *b) {
  return cmp(a,b) == 0;
}

static inline bool GT(Value *a, Value *b) {
  return cmp(a,b) == 2;
}

static inline bool LTE(Value *a, Value *b) {
  return cmp(a,b) != 2;
}

static inline bool GTE(Value *a, Value *b) {
  return cmp(a,b) != 0;
}

static inline bool EQ(Value *a, Value *b) {
  return cmp(a,b) == 1;
}

static inline bool NEQ(Value *a, Value *b) {
  return cmp(a,b) != 1;
}

static inline bool EQZ(Value *x) {
   return (x == direct_zero);
}

static inline bool EQ1(Value *x) {
  return (x == direct_one);
}

static inline bool EQ2(Value *x) {
  return (x == direct_two);
}

static inline void *realloc_(void *ptr, size_t sz) {
  void *res = realloc(ptr, sz);
  if (!res) {
    perror("realloc");
    exit(1);
  }
  return res;
}

BigNat bigify(u64 *x) {
  u64 sz = (*x == 0) ? 0 : 1;
  return (BigNat){ .size = sz, .buf = x };
}

// TODO change to `Value *` arg style of Mul/DivMod/etc
//
// invariant: a.size >= b.size
// stack before: ..rest b a
// stack after:  ..rest (a+b)
void BigPlusBig(u64 aSize, u64 bSize) {
  long new_size = MAX(aSize, bSize) + 1;
  nn_t buf = our_nn_init(new_size); // gc
  BigNat a = BN(pop_deref());
  BigNat b = BN(pop_deref());
  word_t c = nn_add_c(buf, a.buf, a.size, b.buf, b.size, 0);
  buf[new_size - 1] = c;
  push_big((BigNat) { .size = new_size, .buf = buf });
}

void BigPlusDirect(u64 direct, u64 bigSz) {
  u64 newSz = bigSz + 1;
  nn_t buf = our_nn_init(newSz); // gc
  BigNat big = BN(pop());
  word_t carry = nn_add1(buf, big.buf, bigSz, direct);
  buf[bigSz] = carry;
  push_big((BigNat) { .size = newSz, .buf = buf });
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
    BigPlusDirect(aSmall, BN(b).size);
    return;
  }

  if (is_direct(b)) {
    push_val(a);
    BigPlusDirect(bSmall, BN(a).size);
    return;
  }

  push_val(b);
  push_val(a);
  BigPlusBig(BN(a).size, BN(b).size);
}

void BigMinusDirect(Value *big, u64 direct) {
  u64 bigSz = BN(big).size;
  push_val(big);                 // save
  nn_t buf = our_nn_init(bigSz); // gc
  BigNat n = BN(pop_deref());    // reload
  word_t c = nn_sub1(buf, n.buf, bigSz, direct);
  // a positive borrow (nonzero `c`) should only be possible if we
  // underflowed a single u64. our invariant is to convert to SMALL when we
  // reach 1 u64, so we should never encounter this case.
  assert (c == 0);
  push_big((BigNat){ .size = bigSz, .buf = buf });
}

void Dec() {
  #if ENABLE_GRAPHVIZ
  write_dot_extra("<Dec>", "", NULL);
  #endif

  Value *v = pop_deref(0);

  if (is_direct(v)) {
    u64 n = get_direct(v);
    push_val( (n == 0) ? direct_zero : direct(n - 1) );
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
        push_val(direct_zero);
        return;
      }
      push_val(direct(aSmall - bSmall));
      return;
    }
    push_val(direct_zero);
    return;
  }

  if (is_direct(b)) {
    BigMinusDirect(a, bSmall);
    return;
  }

  u64 aSz = BN(a).size;
  u64 bSz = BN(b).size;

  if (aSz < bSz) {
    push_val(direct_zero);
    return;
  }

  // Big - Big

  push_val(b);
  push_val(a);

  nn_t buf = our_nn_init(aSz); // gc

  BigNat aBig = BN(pop_deref());
  BigNat bBig = BN(pop_deref());
  word_t borrow = nn_sub_c(buf, aBig.buf, aBig.size, bBig.buf, bBig.size, 0);
  if (borrow) {
    push_val(direct_zero);
  } else {
    push_big((BigNat) { .size = aSz, .buf = buf });
  }
}

void DirectTimesDirect(u64 a, u64 b) {
  if (a==0 || b==0) {
    push_val(direct_zero);
    return;
  }

  u64 res = a * b;

  // if no overflow
  if ((res / a) == b) { // TODO does this always work?
    push_val(direct(res));
    return;
  }

  nn_t buf = our_nn_init(2);
  buf[1] = nn_mul1(buf, &a, 1, b);
  push_big((BigNat) { .size = 2, .buf = buf });
}

void BigTimesDirect(u64 small, Value *big) {
  u64 newSz = BN(big).size + 1;
  push_val(big);                 // save pointer to stack
  nn_t buf = our_nn_init(newSz); // gc
  nn_zero(buf, newSz);           //
  BigNat nat = BN(pop(0));       // reload pointer
  nn_mul1(buf, nat.buf, nat.size, small);
  push_big((BigNat){ .size = newSz, .buf = buf });
}

void BigTimesBig(Value *a, Value *b) {
  long new_size = BN(a).size + BN(b).size;
  push_val(a);
  push_val(b);
  nn_t buf = our_nn_init(new_size); // gc
  nn_zero(buf, new_size);           //
  b = pop(); a = pop();             // reload pointer
  BigNat aBig = BN(a);
  BigNat bBig = BN(b);
  nn_mul_classical(buf, aBig.buf, aBig.size, bBig.buf, bBig.size);
  push_big((BigNat){ .size = new_size, .buf = buf });
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
  if (b == 0)
    crash("divide by zero");

  push_val(direct(a % b)); // mod
  push_val(direct(a / b)); // div
}

void DivModBigDirect(Value *a, u64 b) {
  if (b == 0) {
    // we could crash here instead
    push_val(direct_zero); // mod
    push_val(direct_zero); // div
    return;
  }
  BigNat aBig = BN(a);
  long sz = aBig.size;
  push_val(a);                        // save a
  nn_t a_buf_clone = our_nn_init(sz); // gc
  nn_t buf = our_nn_init(sz);         // gc
  nn_zero(buf, sz);
  aBig = BN(pop());                   // restore a
  nn_copy(a_buf_clone, aBig.buf, sz); // copy a's buf (it will be mutated)
  word_t mod = nn_divrem1_simple(buf, a_buf_clone, sz, b);
  push_val(direct(mod));                        // mod
  push_big((BigNat){ .size = sz, .buf = buf }); // div
}

void DivModBigBig(Value *a, Value *b) {
  BigNat aBig = BN(a);
  BigNat bBig = BN(b);
  if (aBig.size < bBig.size) {
    push_val(a);           // mod
    push_val(direct_zero); // div
    return;
  }
  long sz = aBig.size - bBig.size + 1;
  push_val(b);                               // save b
  nn_t a_buf_clone = our_nn_init(aBig.size); // gc
  nn_copy(a_buf_clone, aBig.buf, aBig.size);
  nn_t buf = our_nn_init(sz);                // gc
  nn_zero(buf, sz);
  bBig = BN(pop());                          // restore b
  nn_divrem(buf, a_buf_clone, aBig.size, bBig.buf, bBig.size);
  push_big((BigNat){ .size = bBig.size, .buf = a_buf_clone }); // mod
  push_big((BigNat){ .size = sz,        .buf = buf });         // div
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
      push_val(direct_zero); // div
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
#define TRACE (Value*)9223372472313803348ULL

#define NUM_JETS 7
Jet jet_table[NUM_JETS] =
  { (Jet) { .name = ADD,   .arity = 2, .tag = J_ADD   }
  , (Jet) { .name = SUB,   .arity = 2, .tag = J_SUB   }
  , (Jet) { .name = MUL,   .arity = 2, .tag = J_MUL   }
  , (Jet) { .name = DIV,   .arity = 2, .tag = J_DIV   }
  , (Jet) { .name = MOD,   .arity = 2, .tag = J_MOD   }
  , (Jet) { .name = DEC,   .arity = 1, .tag = J_DEC   }
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
  char lab[20];
  sprintf(lab, "stack_grow %lu", count);
  write_dot(lab);
  #endif
  for (u64 i = 0; i < count; i++) {
    push_val(NULL);
  }
}

void seed_load(u64 *buf) {
  u64 n_holes = buf[0];
  u64 n_bigs  = buf[1];
  u64 n_words = buf[2];
  u64 n_bytes = buf[3];
  u64 n_frags = buf[4];

  if (n_holes > 1) {
    fprintf(stderr, "file is just one seed, expected seedpod\n");
    exit(5);
  }

  u64 n_entries = n_bigs + n_words + n_bytes + n_frags + n_holes;

  if (n_entries == 0) crash("empty seed");

  stack_grow(n_entries);
  Value **tab = get_ptr(n_entries-1); // 0

  Value **next_ref = tab;

  if (n_holes) {
    *next_ref++ = a_Pin(direct(0));
  }

  // How big are the bignats?
  u64 bigwidths[n_bigs];
  for (int i=0; i<n_bigs; i++) {
    bigwidths[i] = buf[5+i];
  }

  int used = 5 + n_bigs; // number of words used

  for (int i=0; i<n_bigs; i++) {
    u64 wid  = bigwidths[i];

    u64 *big_buf = calloc(wid, sizeof(u64));
    big_buf = memcpy(big_buf, buf+used, wid*sizeof(u64));
    BigNat big_nat = (BigNat){ .size=wid, .buf = big_buf } ;

    *next_ref++ = a_Big(big_nat);
    used += wid;
  }

  for (int i=0; i<n_words; i++) {
    *next_ref++ = direct(buf[used++]);
  }

  {
    uint8_t *byte_buf = (void*) (buf + used);
    for (int i=0; i<n_bytes; i++) {
      *next_ref++ = direct(byte_buf[i]);
    }
    used += (n_bytes / 8);
  }

  int use = 8 * (n_bytes%8);
  u64 acc = buf[used];
  u64 *more = &buf[used+1];

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

  if (!f) crash("seed file does not exist");

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
//  DOT printing

int dot_count = 0;
char *dot_dir_path = "./dot";

char *p_ptr(Value *x) {
  char *buf = our_malloc_words(48);
  if (x == NULL) {
    sprintf(buf, "N_null");
  } else if (is_direct(x)) {
    sprintf(buf, "ptr_nat_%lu", get_direct(x));
  } else {
    sprintf(buf, "N_%p", x);
  }
  return buf;
}

void fprintf_heap(FILE *f, Node *input, Node *seen) {
  // empty input - done
  if (null_list(input)) {
    free_list(seen, false);
    return;
  }
  Node *tmp = input;
  Value *v = (Value *)input->ptr;
  input = input->next;
  free(tmp);
  //
  // if NULL or seen, recur on tail of input
  if ((v == NULL) || (member_list((void *)v, seen))) {
    return fprintf_heap(f, input, seen);
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
    case HOL: {
      char *v_p = p_ptr(v);
      fprintf(f, "%s [label=hole];\n", v_p);
      free(v_p);
      break;
    }
  }
  seen = cons((void *)v, seen);
  return fprintf_heap(f, input, seen);
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
  char lab[20];
  sprintf(lab, "update %lu", idx);
  write_dot(lab);
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
  char lab[20];
  sprintf(lab, "push %lu", idx);
  write_dot(lab);
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
  char lab[20];
  sprintf(lab, "slide %lu", count);
  write_dot(lab);
  #endif
  //
  Value *top = get_deref(0);
  sp -= count;
  stack[sp-1] = top;
  //
  #if ENABLE_GRAPHVIZ
  sprintf(lab, "post slide %lu", count);
  write_dot(lab);
  #endif
}

void mk_pin() {
  #if ENABLE_GRAPHVIZ
  write_dot("mk_pin");
  #endif

  Value *top = pop_deref();
  if (TY(top) == HOL) crash("mk_pin: hol");
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
  case HOL: crash("plan_case: HOL");
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

  Value *res = (Value *)our_malloc_words(sizeof(Value));

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

  *res = (Value){ .type = LAW, .l = l };
  push_val(res);
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
    push_val(direct_one);
    return;
  }

  push_val(x);
  BigPlusDirect(1, BN(x).size);
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
    case HOL: crash("plan_case: HOL");
    case IND: crash("plan_case: IND: impossible");
  }
}

void setup_call(u64 depth) {
  #if ENABLE_GRAPHVIZ
  char lab[20];
  sprintf(lab, "setup_call %lu", depth);
  write_dot(lab);
  #endif

  // setup the call by pulling the TLs out of all apps which we have
  // unwound.
  for (u64 i = 0; i < depth; i++) {
    stack[(sp-1)-i] = TL(stack[(sp-1)-i]);
  }
}

void flip_stack(u64 depth) {
  #if ENABLE_GRAPHVIZ
  char lab[20];
  sprintf(lab, "flip_stack %lu", depth);
  write_dot(lab);
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
  char lab[50];
  sprintf(lab, "handle_oversaturated_application %lu", count);
  write_dot(lab);
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
  char lab[20];
  sprintf(lab, "backout %lu", depth);
  write_dot(lab);
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
  this_call->a.f = kal(maxRef, pool, f);
  this_call->a.g = kal(maxRef, pool, g);
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

GrMem law_alloc_graph(Law l) {
  int n_lets = l.w.n_lets;
  int n_kals = l.w.n_calls;
  int n_vals = n_lets + n_kals;

  Value *mem  = our_malloc_words(sizeof(Value) * n_vals);
  Value *iter = mem;

  for (int i=0; i<n_lets; i++, iter++)
    iter->type = HOL;

  for (int j=0; j<n_kals; j++, iter++) {
    iter->type = APP;
    iter->a.f = direct_zero;
    iter->a.g = direct_zero;
  }

  return (GrMem){ .holes = mem, .apps = mem + n_lets };
}

void eval_law(Law l) {
  u64 args = get_direct(l.a); // this code is unreachable with bignat arity
  u64 lets = l.w.n_lets;
  int maxRef = args + lets;

  #if ENABLE_GRAPHVIZ
  {
    char lab[40];
    sprintf(lab, "eval_law(arity=%lu, lets=%lu)", args, lets);
    write_dot(lab);
  }
  #endif

  push_val(l.b);                  // save (law body)
  GrMem mem = law_alloc_graph(l); // gc
  Value *b = pop();               // restore (law body)

  #if ENABLE_GRAPHVIZ
  write_dot("starting graph construction");
  #endif

  if (lets) {
    // Add a black hole per let.
    for (u64 i = 0; i < lets; i++) stack[sp++] = mem.holes+i;
    #if STACK_BOUNDS_CHECK
    if (sp > STACK_SIZE) crash("eval_law: stack overflow");
    #endif

    #if ENABLE_GRAPHVIZ
    write_dot("added holes for lets");
    #endif

    // Compute the graph of each let, and fill the corresponding hole.
    for (u64 i = 0; i < lets; i++) {
      // (1 exp next)
      Value *next       = TL(b);
      Value *exp        = TL(HD(b));
      b                 = next;
      Value *gr         = kal(maxRef, &mem.apps, exp);
      mem.holes[i].type = IND;
      mem.holes[i].i    = gr;

      #if ENABLE_GRAPHVIZ
      write_dot("filled one");
      #endif
    }

  }

  #if ENABLE_GRAPHVIZ
  write_dot("constructing body graph");
  #endif

  Value *gr = kal(maxRef, &mem.apps, b);
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

  case J_TRACE:
    push(0);                        // .. body msg msg
    force();                        // .. body MSG
    Value *msg = pop_deref();       // .. body
    fprintf_value(stdout, msg);
    fprintf(stdout, "\n");
    eval();                         // .. *body
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
  char lab[40];
  sprintf(lab, "law_step %lu", depth);
  write_dot(lab);
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
  char lab[40];
  write_dot(lab);
  #endif
  //
  if (!is_direct(op)) goto exception_case;

  // char lob[40];
  // sprintf(lob, "do_prim: %lu", get_direct(op));

  switch (get_direct(op)) {
    case 0: { // mk_pin
      pop();
      push(0); force();
      return mk_pin();
    }
    case 1: { // mk_law
      pop();
      push(0); force();           // b
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
  push(1); // param
  force();
  fprintf(stderr, "Exception: ");
  fprintf_value(stderr, get_deref(0));
  fprintf(stderr, "\n\n\t");
  fprintf_value(stderr, get_deref(1));
  fprintf(stderr, "\n");
  exit(1);
}

bool unwind(u64 depth) {
 again:
  #if ENABLE_GRAPHVIZ
  char lab[20];
  sprintf(lab, "unwind %lu", depth);
  write_dot(lab);
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
        case HOL: {
          crash("unwind: <loop>");
        }
        case IND: {
          crash("unwind: bad deref");
        }
      }
    }
    case NAT: {
      backout(depth);
      return false;
    }
    case HOL: {
      crash("unwind: <loop>");
    }
    case IND: {
      crash("unwind: bad deref");
    }
  }
  crash("this should never happen");
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
    case HOL: crash("eval: HOL");
    case IND: crash("eval: IND");
    default:  crash("eval: bad tag");
  }
}

void force_whnf() {
  #if ENABLE_GRAPHVIZ
  write_dot("force_whnf");
  #endif
  //
  Value *top = pop_deref(0);
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

Value *read_atom() {
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
  nn_t nat_buf = our_nn_init(nat_len);
  nn_zero(nat_buf, nat_len);
  len_t actual_len;
  nn_set_str(nat_buf, &actual_len, str_buf);
  BigNat big = { .size = nat_len, .buf = nat_buf };
  return a_Big(big);
}

void eat_spaces() {
  char c;
  while (isspace(c = getchar()));
  ungetc(c, stdin);
}

Value *read_app(Value *f) {
  while (true) {
    char c = getchar();
    switch (c) {
      case '\r':
      case '\n':
      case '\t':
      case ' ':
        eat_spaces();
        c = getchar();
        if (c == ')') return f;
        ungetc(c, stdin);
        f = a_App(f,read_exp());
        continue;
      case ')':
        return f;
      default:
        crash("expecting space or )");
    }
  }
}

Value *utf8_nat(char *str) {
  long byteSz = strlen(str);
  long wordSz = (7 + byteSz) / 8;
  nn_t buf = our_nn_init(wordSz);
  nn_zero(buf, wordSz);
  memcpy(buf, str, byteSz);
  return a_Big((BigNat){ .size = wordSz, .buf = buf });
}

Value *read_sym() {
  read_str_input(true);
  int len = strlen(str_buf);
  if (!len) crash("Empty symbol");
  Value *ret = utf8_nat(str_buf);
  return ret;
}

Value *read_exp() {
  char c = getchar();
  if (!c) return NULL;
  switch (c) {
  case '%':
      return read_sym();

  case '#': {
    char n = getchar();
    if (isdigit(n)) {
          ungetc(n, stdin);
          return a_Pin(read_atom());
      }
      fprintf(stderr, "Unexpected: '%c'\n", n);
      exit(2);
      return NULL;
  }
  case '{': {
    char buf[1234] = {0};
    for (int i=0; i<1234; i++) {
        buf[i] = getchar();
        if (feof(stdin)) { crash("Unexpected EOF"); }
        if (buf[i] == '}') {
            buf[i] = 0;
            if (i == 0) { return direct_zero; }
            return utf8_nat(buf);
        }
    }
    crash("string too big");
  }
  case '<': {
    char buf[1234] = "./seed/";
    for (int i=7; i<1234; i++) {
        buf[i] = getchar();
        if (feof(stdin)) {
            crash("Unexpected EOF");
        }
        if (buf[i] == '>') {
            buf[i] = 0;
            u64 seedSz;
            u64 *words = load_seed_file(buf, &seedSz);
            seed_load(words);
            check_value(get(0));
            push(0);
            force();
            Value *loaded = get(0);
            check_value(loaded);
            // enable_graphviz=1;
            return loaded;
        }
    }
    crash("load files");
    return NULL;
  }
  case '(':
      eat_spaces();
      Value *f = read_exp();
      return read_app(f);

  default:
    if (isdigit(c)) {
        ungetc(c, stdin);
        return read_atom();
    }
    fprintf(stderr, "Unexpected: '%c'\n", c);
    exit(2);
    return NULL;
  }
}

Value *read_exp_top() {
  eat_spaces();
  if (feof(stdin)) return NULL;
  return read_exp();
}

int main (void) {
  if (heap == NULL) { heap_init(); }

  // Value *x = direct(UINT64_MAX);
  // Value *y = direct(3);
  // Value *arr[2] = { x, y };
  // Value *res = jet_table[0].jet_exec(arr);
  // fprintf_value(stdout, res);
  // printf("\n");

  struct stat st = {0};
  if (stat(dot_dir_path, &st) == -1) {
    mkdir(dot_dir_path, 0700);
  }
  bool isInteractive = isatty(fileno(stdin));
  again:
    if (isInteractive) printf(">> ");
    Value *v = read_exp_top();
    if (!v) {
      return 0;
    }

    fprintf(stderr, "\n");
    push_val(v);
    clone();
    force();

    #if ENABLE_GRAPHVIZ
    write_dot("main final");
    #endif

    Value *res = pop_deref();
    fprintf_value(stdout, res);
    printf("\n");

    goto again;
}
