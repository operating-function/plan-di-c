// TODO
//
// - [ ] make an example evaluation which takes a while.
//   - use that to test whether optimizations are effective.
//

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <ctype.h>
#include <stdarg.h>
#include <string.h>
#include <inttypes.h>
#include <unistd.h>

////////////////////////////////////////////////////////////////////////////////
//  Typedefs

typedef uint64_t u64;

typedef enum Type {
  PIN,
  LAW,
  APP,
  NAT,
  HOL
} Type;

typedef enum NatType {
  SMALL,
  BIG
} NatType;

typedef struct Nat {
  NatType type;
  union {
    u64 direct;
    struct {
      u64 size;
      u64 *buf;
    };
  };
} Nat;

struct Value;

typedef struct Law {
  Nat n;
  Nat a;
  struct Value ** b;
} Law;

typedef struct App {
  struct Value ** f;
  struct Value ** g;
} App;

typedef struct Value {
  Type type;
  union {
    struct Value ** p;
    Law l;
    App a;
    Nat n;
  };
} Value;

////////////////////////////////////////////////////////////////////////////////
//  Crash

void crash(char * s) {
  printf("Error: %s\n", s);
  exit(1);
}

////////////////////////////////////////////////////////////////////////////////
//  Accessors

#define CHECK_TAGS 1

static inline void ck_pin(char * fn_nm, Value * x) {
  char s[14];
  sprintf(s, "%s not a PIN!", fn_nm);
  if (x->type != PIN) crash(s);
}

static inline void ck_law(char * fn_nm, Value * x) {
  char s[14];
  sprintf(s, "%s not a LAW!", fn_nm);
  if (x->type != LAW) crash(s);
}

static inline void ck_app(char * fn_nm, Value * x) {
  char s[15];
  sprintf(s, "%s not an APP!", fn_nm);
  if (x->type != APP) crash(s);
}

static inline void ck_nat(char * fn_nm, Value * x) {
  char s[14];
  sprintf(s, "%s not a NAT!", fn_nm);
  if (x->type != NAT) crash(s);
}

static inline Type TY(Value ** x) {
  return (*x)->type;
}

static inline Value ** IT(Value ** x) {
  #ifdef CHECK_TAGS
  ck_pin("IT", *x);
  #endif
  return (*x)->p;
};

static inline Nat NM(Value ** x) {
  #ifdef CHECK_TAGS
  ck_law("NM", *x);
  #endif
  return (*x)->l.n;
}

static inline Nat AR(Value ** x) {
  #ifdef CHECK_TAGS
  ck_law("AR", *x);
  #endif
  return (*x)->l.a;
}

static inline Value ** BD(Value ** x) {
  #ifdef CHECK_TAGS
  ck_law("BD", *x);
  #endif
  return (*x)->l.b;
}

static inline Value ** HD(Value ** x) {
  #ifdef CHECK_TAGS
  ck_app("HD", *x);
  #endif
  return (*x)->a.f;
};

static inline Value ** TL(Value ** x) {
  #ifdef CHECK_TAGS
  ck_app("TL", *x);
  #endif
  return (*x)->a.g;
};

static inline Nat NT(Value ** x) {
  #ifdef CHECK_TAGS
  ck_nat("NT", *x);
  #endif
  return (*x)->n;
};

////////////////////////////////////////////////////////////////////////////////
//  Printing

static const bool tracing = false;

int print_depth = 0;

void trace_print(const char * format, ...) {
  int d = print_depth*2;
  if (tracing) {
    for (int i=0; i<d; i++) putchar(' ');
    va_list args;
    va_start(args, format);
    vprintf(format, args);
    va_end(args);
  }
}

#define VERBOSE_TRACING 0

#if VERBOSE_TRACING
#define trace_verbose(...) trace_print(__VA_ARGS__)
#else
#define trace_verbose(...) ;
#endif

void check_nat(Nat n) {
    return;
}

void check_value(Value **v) {
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
      check_nat(NT(v));
      break;
    case HOL:
      break;
    default:
      crash("BAD VALUE TAG");
  }
}

void print_value_internal(Value**, char*, int);

char * print_value_t(Value ** v) {
  if (tracing) {
    char * buf = malloc(4096*sizeof(char));
    print_value_internal(v, buf, 0);
    return buf;
  }
  return NULL;
}

char * print_value(Value ** v) {
  char * buf = malloc(4096*sizeof(char));
  print_value_internal(v, buf, 0);
  return buf;
}

void print_value_app(Value ** v, char * buf, int recur) {
  if (TY(v) != APP) {
    return  print_value_internal(v, buf, recur);
  }
  print_value_app(HD(v), buf, recur);
  sprintf(buf + strlen(buf), " ");
  print_value_internal(TL(v), buf, recur+1);
}

void print_nat_internal(Nat, char *);

void print_value_internal(Value ** v, char * buf, int recur) {
  if (recur > 10) {
    sprintf(buf + strlen(buf), "‥");
    return;
  }
  switch (TY(v)) {
    case PIN:
      sprintf(buf + strlen(buf), "<");
      print_value_internal(IT(v), buf, recur+1);
      sprintf(buf + strlen(buf), ">");
      break;
    case LAW:
      sprintf(buf + strlen(buf), "{");
      print_nat_internal(NM(v), buf);
      sprintf(buf + strlen(buf), " ");
      print_nat_internal(AR(v), buf);
      sprintf(buf + strlen(buf), " ");
      print_value_internal(BD(v), buf, recur+1);
      sprintf(buf + strlen(buf), "}");
      break;
    case APP:
      sprintf(buf + strlen(buf), "(");
      print_value_app(v, buf, recur+1);
      sprintf(buf + strlen(buf), ")");
      break;
    case NAT:
      print_nat_internal(NT(v), buf);
      break;
    case HOL:
      sprintf(buf + strlen(buf), "<>");
      break;
  }
}

char * print_nat(Nat n) {
  // TODO this is presumably unsafe for large nats?
  char * buf = malloc(512*sizeof(char));
  print_nat_internal(n, buf);
  return buf;
}

static inline bool issym (char c) {
  return (c == '_' || isalnum(c));
}

bool is_symbol (const char *str) {
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

void print_nat_internal(Nat n, char * buf) {
  switch (n.type) {
    case SMALL: {
      char tmp[9] = {0};
      ((u64*)tmp)[0] = n.direct;
      if (is_symbol(tmp)) {
        buf[strlen(buf)] = '%';
        strcpy(buf + strlen(buf), tmp);
      } else {
        sprintf(buf + strlen(buf), "%" PRIu64, n.direct);
      }
      break;
    }
    // add is_symbol case which attempts to print nat bytes
    case BIG: {
      char *tmp = (char*)n.buf;
      if (is_symbol(tmp)) {
        // TODO this is unsafe b/c we don't know how big `buf` is.
        buf[strlen(buf)] = '%';
        strcpy(buf + strlen(buf), tmp);
      } else {
        // TODO print this as an actual integer. this seems difficult, however
        // there is prior art in Haskell:
        // https://hackage.haskell.org/package/base-4.18.0.0/docs/src/GHC.Show.html#integerToString
        sprintf(buf + strlen(buf), "[");
        sprintf(buf + strlen(buf), "%" PRIu64, n.buf[0]);
        for (int i=1; i<n.size; i++) {
          sprintf(buf + strlen(buf), " %" PRIu64, n.buf[i]);
        }
        sprintf(buf + strlen(buf), "]");
      }
      break;
    }
  }
}

////////////////////////////////////////////////////////////////////////////////
//  Construction

Nat d_Nat(u64 n) {
  return (Nat){.type = SMALL, .direct = n};
}

Value ** a_Nat(u64 n) {
  Value * res = (Value *)malloc(sizeof(Value));
  res->type = NAT;
  res->n = d_Nat(n);
  Value ** ptr = (Value **)malloc(sizeof(Value*));
  *ptr = res;
  return ptr;
}

Value ** a_Big(Nat n) {
  Value * res = (Value *)malloc(sizeof(Value));
  res->type = NAT;
  res->n = n;
  Value ** ptr = (Value **)malloc(sizeof(Value*));
  *ptr = res;
  return ptr;
}

Value ** a_Pin(Value ** v) {
  Value * res = (Value *)malloc(sizeof(Value));
  res->type = PIN;
  res->p = v;
  Value ** ptr = (Value **)malloc(sizeof(Value*));
  *ptr = res;
  return ptr;
}

Value ** a_Law(Nat n, Nat a, Value ** b) {
  Value * res = (Value *)malloc(sizeof(Value));
  res->type = LAW;
  res->l.n = n;
  res->l.a = a;
  res->l.b = b;
  Value ** ptr = (Value **)malloc(sizeof(Value*));
  *ptr = res;
  return ptr;
}

Value ** a_App(Value ** f, Value ** g) {
  Value * res = (Value *)malloc(sizeof(Value));
  res->type = APP;
  res->a.f = f;
  res->a.g = g;
  Value ** ptr = (Value **)malloc(sizeof(Value*));
  *ptr = res;
  return ptr;
}

Value ** a_Hol() {
  Value * res = (Value *)malloc(sizeof(Value));
  res->type = HOL;
  Value ** ptr = (Value **)malloc(sizeof(Value*));
  *ptr = res;
  return ptr;
}

////////////////////////////////////////////////////////////////////////////////
//  Mutation

void update(Value ** t, Value ** x) {
  trace_verbose("pre:  %p(%p) <== %p(%p)\n", (void *)t, (void *)*t, (void *)x, (void *)*x);
  if (TY(x) == HOL) {
    trace_verbose("update: *t = *x;\n");
    *t = *x;
  } else {
    trace_verbose("update: **t = **x;\n");
    **t = **x;
  }
  trace_verbose("post: %p(%p) <== %p(%p)\n", (void *)t, (void *)*t, (void *)x, (void *)*x);
}

////////////////////////////////////////////////////////////////////////////////
//  Nat Operators

bool EQ(Nat a, Nat b) {
  if ((a.type == SMALL) && b.type == SMALL)
    return (a.direct == b.direct);
  if ((a.type == BIG) && b.type == BIG) {
    if (a.size != b.size) return false;
    for (int i=0; i<a.size; i++) {
      if (a.buf[i] != b.buf[i]) return false;
    }
    return true;
  }
  return false;
}

bool NEQ(Nat a, Nat b) {
  return !(EQ(a, b));
}

bool LT(Nat a, Nat b) {
  switch (a.type) {
    case SMALL:
      switch (b.type) {
        case SMALL:
          return (a.direct < b.direct);
        case BIG:
          return true;
      }
    case BIG:
      switch (b.type) {
        case SMALL:
          return false;
        case BIG:
          if (a.size != b.size) return (a.size < b.size);
          for (int i=(a.size-1); i>=0; i--) {
            if (a.buf[i] == b.buf[i]) continue;
            return (a.buf[i] < b.buf[i]);
          }
          return false;
      }
  }
}

bool GT(Nat a, Nat b) {
  switch (a.type) {
    case SMALL:
      switch (b.type) {
        case SMALL:
          return (a.direct > b.direct);
        case BIG:
          return false;
      }
    case BIG:
      switch (b.type) {
        case SMALL:
          return true;
        case BIG:
          if (a.size != b.size) return (a.size > b.size);
          for (int i=(a.size-1); i>=0; i--) {
            if (a.buf[i] == b.buf[i]) continue;
            return (a.buf[i] > b.buf[i]);
          }
          return false;
      }
  }
}

bool LTE(Nat a, Nat b) {
  return !(GT(a, b));
}

bool GTE(Nat a, Nat b) {
  return !(LT(a, b));
}

// just to silence warnings
static inline void *realloc_(void *ptr, size_t sz) {
  void *res = realloc(ptr, sz);
  if (!res) {
    perror("realloc");
    exit(1);
  }
  return res;
}

// TODO can we make an in-place mutative version of this, also?
Nat Inc(Nat n) {
  switch(n.type) {
    case SMALL:
      if (n.direct == UINT64_MAX) {
        u64 * buf = malloc(2*sizeof(u64));
        buf[0] = 0;
        buf[1] = 1;
        return (Nat){ .type = BIG, .size = 2, .buf = buf };
      }
      return (Nat){ .type = SMALL, .direct = (n.direct+1) };
    case BIG: {
      int i = 0;
      u64  new_size = n.size;
      u64  *new_buf = malloc(n.size * sizeof(u64));
      new_buf = memcpy(new_buf, n.buf, n.size*sizeof(u64));
      while (i < n.size) {
        if (n.buf[i] == UINT64_MAX) {
          new_buf[i] = 0;
          i++;
          continue;
        } else {
          new_buf[i] = n.buf[i] + 1;
          i++;
          break;
        }
      }
      if (i == n.size) {
        new_size++;
        realloc_(new_buf, new_size * sizeof(u64));
        new_buf[i] = 1;
      }
      return (Nat){ .type = BIG, .size = new_size, .buf = new_buf };
    }
  }
}

// TODO can we make an in-place mutative version of this, also?
Nat Dec(Nat n) {
  switch(n.type) {
    case SMALL:
      if (n.direct == 0) {
        crash("decrement underflow");
      }
      return (Nat){ .type = SMALL, .direct = (n.direct-1) };
    case BIG: {
      int i = 0;
      u64  new_size = n.size;
      u64  *new_buf = malloc(n.size * sizeof(u64));
      new_buf = memcpy(new_buf, n.buf, n.size*sizeof(u64));
      while (i < n.size) {
        if (n.buf[i] == 0) {
          new_buf[i] = UINT64_MAX;
          i++;
          continue;
        } else {
          new_buf[i] = n.buf[i] - 1;
          i++;
          break;
        }
      }
      if ((i == n.size) && (new_buf[i-1] == 0)){
        new_size--;
        realloc_(new_buf, new_size * sizeof(u64));
        new_buf[i] = UINT64_MAX;
      }
      return (Nat){ .type = BIG, .size = new_size, .buf = new_buf };
    }
  }
}

Nat Sub(Nat a, Nat b) {
  if ((a.type == SMALL) && (b.type == SMALL)) {
    if (a.direct < b.direct) crash("subtract underflow");
    return (Nat){ .type = SMALL, .direct = (a.direct - b.direct) };
  }
  if ((a.type == SMALL) && (b.type == BIG)) crash("subtract underflow");

  u64 new_size = a.size;
  u64 * new_buf = malloc(new_size * sizeof(u64));
  new_buf = memcpy(new_buf, a.buf, new_size*sizeof(u64));

  if ((a.type == BIG) && (b.type == SMALL)) {
    u64 * b_buf = malloc(sizeof(u64));
    *b_buf = b.direct;
    b = (Nat){ .type = BIG, .size = 1, .buf = b_buf };
  }
  if (a.size < b.size) crash("subtract underflow");

  for (int i=0; i<b.size; i++) {
    if (new_buf[i] < b.buf[i]) {
      new_buf[i] = UINT64_MAX - ((b.buf[i] - (new_buf[i] + 1)));
      int c = i + 1;
      while (true) {
        if (c >= new_size) {
          crash("subtract underflow");
        }
        if (new_buf[c] == 0) {
          new_buf[c] = UINT64_MAX;
          c++;
        } else {
          new_buf[c] = new_buf[c] - 1;
          c++;
          break;
        }
      }
      if ((c == new_size) && (new_buf[c-1] == 0)){
        new_size--;
        realloc_(new_buf, new_size * sizeof(u64));
      }

    } else {
      new_buf[i] = new_buf[i] - b.buf[i];
    }
  }
  return (Nat){ .type = BIG, .size = new_size, .buf = new_buf };
}

////////////////////////////////////////////////////////////////////////////////
//  Combinator

Value ** F(Value ** o);
Value ** E(Value ** o);
Value ** L(Nat n, Nat e, Value ** v, Value ** b);
Value ** R(Nat n, Value ** e, Value ** b);

Value ** I(Value ** f, Value ** e, Nat n) {
  trace_print("I[%s, %s, %s]\n", print_value_t(f), print_value_t(e), print_nat(n));
  if (EQ(n, d_Nat(0))) {
    if (TY(e) == APP) {
      return TL(e);
    } else {
      return e;
    }
  } else {
    if (TY(e) == APP) {
      return I(f, HD(e), Dec(n));
    } else {
      return f;
    }
  }
}

Nat A_(Value ** o) {
  switch (TY(o)) {
    case APP: {
      Nat head = A_(HD(o));
      if (EQ(head, d_Nat(0))) return d_Nat(0);
      return Dec(head);
    }
    case PIN: {
      Value ** it = IT(o);
      switch (TY(it)) {
        case NAT: {
          Nat nt = NT(it);
          if ((nt.type) == BIG) return d_Nat(1);
          switch (nt.direct) {
            case 1:
            case 3:  return d_Nat(3);
            case 4:  return d_Nat(5);
            default: return d_Nat(1);
          }
        }
        default:
          return A_(IT(o));
      }
    }
    case LAW:
      return AR(o);
    case NAT:
      return d_Nat(0);
    case HOL:
      crash("<<loop>>");
      return d_Nat(0);
  }
}

Nat A(Value ** o) {
  trace_print("A[%s]\n", print_value_t(o));
  Nat res = A_(o);
  // if (tracing) printf(" ==> %s\n", print_value_t(res));
  return res;
}

Nat N(Value ** o) {
  trace_print("N[%s]\n", print_value_t(o));
  Value ** norm = E(o);
  if (TY(norm) == NAT) return NT(norm);
  return d_Nat(0);
}

Value ** L(Nat i, Nat n, Value ** e, Value ** x) {
  trace_print("L[%s, %s, %s, %s]\n", print_nat(i), print_nat(n), print_value_t(e), print_value_t(x));
  if (TY(x) == APP) {
    if (TY(HD(x)) == APP) {
      if (TY(HD(HD(x))) == NAT) {
        if (EQ(NT(HD(HD(x))), d_Nat(1))) {
          Value ** v = TL(HD(x));
          Value ** b = TL(x);
          Value ** ret = I(a_Hol(), e, Sub(n,i));
          trace_verbose("L: ret: %s\n", print_value_t(ret));
          update(ret, R(n, e, v));
          trace_verbose("\t <== %s\n", print_value_t(ret));
          return L(Inc(i), n, e, b);
        }
      }
    }
  }
  return R(n, e, x);
}

Value ** R(Nat n, Value ** e, Value ** b){
  trace_print("R[%s, %s, %s]\n", print_nat(n), print_value_t(e), print_value_t(b));
  if (TY(b) == NAT && LTE(NT(b), n)) {
    return I(a_Hol(), e, Sub(n, NT(b)));
  }
  if (TY(b) == APP) {
    if (TY(HD(b)) == APP) {
      if ((TY(HD(HD(b))) == NAT) && EQ(NT(HD(HD(b))), d_Nat(0))) {
        Value ** f = TL(HD(b));
        Value ** x = TL(b);
        return a_App(R(n, e, f), R(n, e, x));
      }
    } else if ((TY(HD(b)) == NAT) && EQ(NT(HD(b)), d_Nat(2))) {
        Value ** x = TL(b);
        return x;
    }
  }
  return b;
}

Value ** C(Value ** z, Value ** p, Nat n) {
  trace_print("C[%s, %s, %s]\n", print_value_t(z), print_value_t(p), print_nat(n));
  if (EQ(n, d_Nat(0))) {
    return z;
  } else {
    return a_App(p, a_Big(Dec(n)));
  }
}

Value ** P(Value ** p, Value ** l, Value ** a, Value ** n, Value ** o) {
  trace_print("P[%s, %s, %s, %s, %s]\n", print_value_t(p), print_value_t(l), print_value_t(a), print_value_t(n), print_value_t(o));
  switch (TY(o)) {
    case APP:
      return a_App(a_App(a, HD(o)), TL(o));
    case PIN:
      return a_App(p, IT(o));
    case LAW:
      return a_App(a_App(a_App(l, a_Big(NM(o))), a_Big(AR(o))), BD(o));
    case NAT:
      return a_App(n, o);
    case HOL:
      crash("<<loop>>");
      return NULL;
  }
}

Value ** S(Value ** o) {
  trace_print("S[%s]\n", print_value_t(o));
  if (TY(o) == APP) {
    switch (TY(HD(o))) {
      case APP:
        return a_App(S(HD(o)), TL(o));
      case PIN: {
        Value ** v = IT(HD(o));
        Type t = TY(v);
        if ((t != LAW) && (t != NAT)) {
          return S(a_App(v, TL(o)));
        }
      }
      default:
        return o;
    }
  }
  return o;
}

Value ** B(Nat a, Nat n, Value ** e, Value ** b, Value ** x) {
  trace_print("B[%s, %s, %s, %s, %s]\n", print_nat(a), print_nat(n), print_value_t(e), print_value_t(b), print_value_t(x));
  if (TY(x) == APP) {
    Value ** h = HD(x);
    if (TY(h) == APP) {
      Value ** hh = HD(h);
      if (TY(hh) == NAT) {
        if (EQ(NT(hh), d_Nat(1))) {
          return B(a, Inc(n), a_App(e, a_Hol()), b, TL(x));
        }
      }
    }
  }
  return L(Inc(a), n, e, b);
}

Value ** X(Value ** k, Value ** e) {
  trace_print("X[%s, %s]\n", print_value_t(k), print_value_t(e));
  switch (TY(k)) {
    case HOL:
      crash("<<loop>>");
    case APP:
      return X(HD(k), e);
    case LAW: {
      Nat a = AR(k);
      Value ** b = BD(k);
      return B(a, a, e, b, b);
    }
    case PIN:
      return X(IT(k), e);
    case NAT:
      break;
  }

  Value **b, **a, **n, **p, **l, **x, **z;
  Nat k_n = NT(k);
  if (k_n.type == BIG) crash(print_value(e));
  switch (k_n.direct) {
    case 0:
      x = TL(e);
      return a_Pin(F(x));
    case 1:
      b = TL(e);
      a = TL(HD(e));
      n = TL(HD(HD(e)));
      Nat nn = N(n);
      trace_print("<makeLaw %s>\n", print_nat(nn));
      print_depth++;
      Value **r = a_Law(nn, N(a), F(b));
      print_depth--;
      trace_print("</makeLaw %s>\n", print_nat(nn));
      return r;
    case 2:
      x = TL(e);
      return a_Big(Inc(N(x)));
    case 3:
      x = TL(e);
      p = TL(HD(e));
      z = TL(HD(HD(e)));
      return C(z, p, N(x));
    case 4:
      x = TL(e);
      n = TL(HD(e));
      a = TL(HD(HD(e)));
      l = TL(HD(HD(HD(e))));
      p = TL(HD(HD(HD(HD(e)))));
      return P(p, l, a, n, E(x));
  }
  crash(print_value(e));
  return NULL;
}

Value ** E(Value ** o) {
  trace_print("E[%s]\n", print_value_t(o));
  switch (TY(o)) {
    case HOL:
      crash("<<loop>>");
    case APP:
      print_depth++;
      E(HD(o));
      Nat arity = A(HD(o));
      trace_verbose("E arity: %s, val: %s\n", print_nat(arity), print_value(HD(o)));
      if (EQ(arity, d_Nat(1))) {
        update(o, S(o));
        trace_verbose("S[] ==>  %s\n", print_value_t(o));
        update(o, X(o,o));
        trace_verbose("</X %s>\n", print_value(o));
        E(o);
      }
      print_depth--;
      trace_verbose("E[] ==> %s\n", print_value_t(o));
      return o;
    case PIN:
    case LAW:
    case NAT:
      return o;
  }
}

Value ** F(Value ** o) {
  trace_print("F[%s]\n", print_value_t(o));
  o = E(o);
  if (TY(o) == APP) {
    F(HD(o));
    F(TL(o));
  }
  return o;
}


////////////////////////////////////////////////////////////////////////////////
//  Seeds

Value ** frag_load(Value ***tab, u64 tabSz, int *, u64 *, u64 **);

Value ** frag_load_cell(Value ***tab, u64 tabSz, int *use, u64 *acc, u64 **mor) {
  Value **f = frag_load(tab, tabSz, use, acc, mor);
  Value **x = frag_load(tab, tabSz, use, acc, mor);
  return a_App(f,x);
}

u64 u64_bits (u64 w) {
  if (!w) { return 0; }
  return 64 - __builtin_clzll(w);
}

Value ** frag_load(Value ***tab, u64 tabSz, int *use, u64 *acc, u64 **mor) {
  u64 isCell = ((*acc >> *use) & 1ULL);

  // move forward by one bit.
  (*use)++;
  if (*use == 64) {
    *use = 0;
    *acc = **mor;
    *mor = (*mor)+1;
  }

  if (isCell) {
    return frag_load_cell(tab, tabSz, use, acc, mor);
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

  return tab[ref];
}

Value ** seed_load(u64 *buf) {
  u64 n_holes = buf[0];
  u64 n_bigs  = buf[1];
  u64 n_words = buf[2];
  u64 n_bytes = buf[3];
  u64 n_frags = buf[4];

  if (n_holes != 0) {
    fprintf(stderr, "file is just one seed, expected seedpod\n");
    exit(5);
  }

  u64 n_entries = n_bigs + n_words + n_bytes + n_frags;

  Value ***tab = malloc(sizeof(Value*) * n_entries);

  // How big are the bignats?
  u64 bigwidths[n_bigs];
  for (int i=0; i<n_bigs; i++) {
    bigwidths[i] = buf[5+i];
  }

  Value ***next_ref = tab;
  int used = 5 + n_bigs; // number of words used

  for (int i=0; i<n_bigs; i++) {
    u64 wid  = bigwidths[i];

    u64 * big_buf = calloc(wid, sizeof(u64));
    big_buf = memcpy(big_buf, buf+used, wid*sizeof(u64));
    Nat big_nat = (Nat){.type=BIG, .size=wid, .buf = big_buf};

    *next_ref++ = a_Big(big_nat);
    used += wid;
  }

  for (int i=0; i<n_words; i++) {
    *next_ref++ = a_Nat(buf[used++]);
  }

  {
    uint8_t *byte_buf = (void*) (buf + used);
    for (int i=0; i<n_bytes; i++) {
      *next_ref++ = a_Nat(byte_buf[i]);
    }
    used += (n_bytes / 8);
  }

  int use = 8 * (n_bytes%8);
  u64 acc = buf[used];
  u64 *more = &buf[used+1];

  for (int i=0; i<n_frags; i++) {
    u64 tabSz = (next_ref - tab);
    *next_ref++ = frag_load_cell(tab, tabSz, &use, &acc, &more);
  }

  return next_ref[-1];
}

u64 *load_seed_file (const char* filename, u64 *sizeOut) {
  FILE * f = fopen (filename, "rb");

  if (!f) exit(2);

  fseek(f, 0, SEEK_END);
  u64 szBytes = ftell(f);

  u64 szWords = (szBytes / 8) + (szBytes%8 ? 1 : 0);

  fseek(f, 0, SEEK_SET);
  u64 *buf = calloc(szWords+1, 8); // We add an extra word here
                                   // so that we can over-read
                                   // by one word, this simplifies
                                   // decoding.
  if (!buf) exit(3);
  if (fread (buf, 1, szBytes, f) != szBytes) exit(4);
  fclose(f);

  *sizeOut = szWords;
  return buf;
}

////////////////////////////////////////////////////////////////////////////////
//  Runner

void run(Value ** v) {
  trace_print("RUN[%s]\n", print_value(v));
  trace_print("  ->\n", print_value(v));
  print_depth++;
  Value ** res = F(v);
  print_depth--;
  trace_print("%s\n", print_value(res));
}

// TODO handle atoms bigger than U64_MAX - this will just overflow
Value **read_atom() {
  char c;
  u64 acc = 0;
  while (isdigit(c = getchar())) {
    u64 tst = (UINT64_MAX - (c - '0')) / 10;
    if (acc > tst) crash("read_atom(): overflow");
    acc = acc*10 + (c - '0');
  }
  ungetc(c,stdin);
  return a_Nat(acc);
}

void eat_spaces() {
  char c;
  while (isspace(c = getchar()));
  ungetc(c, stdin);
}

Value **read_exp();

Value **read_app(Value **f) {
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

#define BUF_LEN 1024

Value **read_sym() {
    // TODO handle larger sizes
    // sketch:
    //   - loop with buf, allocating new memory, until done.
    //   - count the total # of chars
    //   - allocate `nat_buf` using the total # chars
    //   - copy each char buf into `nat_buf`, sequentially.
    static char buf[BUF_LEN];
    char c, *out=buf;
    int buf_chars = 0;
    while (issym(c = getchar())) {
      if (buf_chars++ >= BUF_LEN) crash("sym too big");
      *out++ = c;
    }
    if (feof(stdin)) crash("Unexpected EOF\n");
    ungetc(c, stdin);
    int len = strlen(buf);
    if (!len)    crash("Empty symbol");
    if (len > 8) {
      int u64_sz = sizeof(u64);
      int u64_len = (len / u64_sz) + 1;
      u64 * nat_buf = calloc(u64_sz, u64_len);
      strcpy((char*)nat_buf, buf);
      Nat n = (Nat){.type=BIG, .size=u64_len, .buf = nat_buf};
      return a_Big(n);
    } else {
      u64 word = 0;
      strcpy((char*)&word, buf);
      return a_Nat(word);
    }
}

Value **read_exp() {
  again: {
    char c = getchar();
    if (!c) return NULL;
    switch (c) {
    case '%': {
        return read_sym();
    }
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
    case '<': {
        char buf[1234] = {0};
        for (int i=0; i<1234; i++) {
            buf[i] = getchar();
            if (feof(stdin)) {
                crash("Unexpected EOF");
            }
            if (buf[i] == '>') {
                buf[i] = 0;
                u64 seedSz;
                u64 *words = load_seed_file(buf, &seedSz);
                Value **loaded = seed_load(words);
                check_value(loaded);
                return loaded;
            }
        }
        crash("load files");
        return NULL;
    }
    case '(': {
        eat_spaces();
        Value **f = read_exp();
        return read_app(f);
    }
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
}

Value **read_exp_top() {
 again:
  eat_spaces();
  if (feof(stdin)) return NULL;
  return read_exp();
}

int main (void) {
  bool isInteractive = isatty(fileno(stdin));
  again:
    if (isInteractive) printf(">> ");
    Value **v = read_exp_top();
    if (!v) return 0;
    run(v);
    printf("%s\n", print_value(v));
    goto again;
    return 0;
}
