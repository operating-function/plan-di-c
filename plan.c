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

#include "bsdnt/nn.h"

#include "linked_list.h"

////////////////////////////////////////////////////////////////////////////////
//  Typedefs

typedef uint32_t u32;
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

typedef struct Nat {
  NatType type;
  union {
    u64 direct;
    struct {
      len_t size;
      nn_t nat;
    };
  };
} Nat;

struct Value;

typedef struct Law {
  Nat n;
  Nat a;
  struct Value * b;
} Law;

typedef struct App {
  struct Value * f;
  struct Value * g;
} App;

typedef struct Value {
  Type type;
  union {
    struct Value * p; // PIN
    Law l;            // LAW
    App a;            // APP
    Nat n;            // NAT
    struct Value * i; // IND
  };
} Value;

////////////////////////////////////////////////////////////////////////////////
//  Globals

#define STACK_SIZE 4096
Value **stack;
u64 sp;

////////////////////////////////////////////////////////////////////////////////
//  Crash

void crash(char * s) {
  printf("Error: %s\n", s);
  exit(1);
}

////////////////////////////////////////////////////////////////////////////////
//  Accessors

#define CHECK_TAGS 1

Value * deref(Value * x);

static inline void ck_pin(char * fn_nm, Value * x) {
  char s[14];
  sprintf(s, "%s not a PIN!", fn_nm);
  if (x->type != PIN) crash(s);
}

// we allow PIN LAWs
static inline void ck_law(char * fn_nm, Value * x) {
  char s[28];
  sprintf(s, "%s not a LAW or PIN-LAW!", fn_nm);
  if (x->type == LAW) return;
  if (x->type == PIN) {
    return ck_law(fn_nm, x->i);
  }
  crash(s);
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

static inline void ck_ind(char * fn_nm, Value * x) {
  char s[14];
  sprintf(s, "%s not a IND!", fn_nm);
  if (x->type != IND) crash(s);
}

static inline Type TY(Value * x) {
  return x->type;
}

static inline bool IS_NAT(Value * x) {
  return (TY(x) == NAT);
}

// TODO apply `deref` on all accessor return values?

static inline Value * IT(Value * x) {
  x = deref(x);
  #ifdef CHECK_TAGS
  ck_pin("IT", x);
  #endif
  return x->p;
};

static inline Nat NM(Value * x) {
  x = deref(x);
  #ifdef CHECK_TAGS
  ck_law("NM", x);
  #endif
  if (x->type == PIN) return NM(x->i);
  return x->l.n;
}

static inline Nat AR(Value * x) {
  x = deref(x);
  #ifdef CHECK_TAGS
  ck_law("AR", x);
  #endif
  if (x->type == PIN) return AR(x->i);
  return x->l.a;
}

static inline Value * BD(Value * x) {
  x = deref(x);
  #ifdef CHECK_TAGS
  ck_law("BD", x);
  #endif
  if (x->type == PIN) return BD(x->i);
  return x->l.b;
}

static inline Value * HD(Value * x) {
  x = deref(x);
  #ifdef CHECK_TAGS
  ck_app("HD", x);
  #endif
  return x->a.f;
};

static inline Value * TL(Value * x) {
  x = deref(x);
  #ifdef CHECK_TAGS
  ck_app("TL", x);
  #endif
  return x->a.g;
};

static inline Nat NT(Value * x) {
  x = deref(x);
  #ifdef CHECK_TAGS
  ck_nat("NT", x);
  #endif
  return x->n;
};

static inline Value * IN(Value * x) {
  #ifdef CHECK_TAGS
  ck_ind("IN", x);
  #endif
  return x->i;
};

////////////////////////////////////////////////////////////////////////////////
//  Printing

void check_nat(Nat n) {
    return;
}

void check_value(Value *v) {
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

void fprintf_value_internal(FILE *, Value *, int);

void fprintf_value(FILE *f , Value * v) {
  fprintf_value_internal(f, v, 0);
}

void fprintf_value_app(FILE * f, Value * v, int recur) {
  if (TY(v) != APP) {
    return fprintf_value_internal(f, v, recur);
  }
  fprintf_value_app(f, HD(v), recur);
  fprintf(f, " ");
  fprintf_value_internal(f, TL(v), recur+1);
}

void fprintf_nat(FILE *, Nat);

void fprintf_value_internal(FILE * f, Value * v, int recur) {
  v = deref(v);
  if (recur > 10) {
    fprintf(f, "‥");
    return;
  }
  switch (TY(v)) {
    case PIN:
      fprintf(f, "<");
      fprintf_value_internal(f, IT(v), recur+1);
      fprintf(f, ">");
      break;
    case LAW:
      fprintf(f, "{");
      fprintf_nat(f, NM(v));
      fprintf(f, " ");
      fprintf_nat(f, AR(v));
      fprintf(f, " ");
      fprintf_value_internal(f, BD(v), recur+1);
      fprintf(f, "}");
      break;
    case APP:
      fprintf(f, "(");
      fprintf_value_app(f, v, recur+1);
      fprintf(f, ")");
      break;
    case NAT:
      fprintf_nat(f, NT(v));
      break;
    case HOL:
      fprintf(f, "<>");
      break;
    case IND:
      crash("fprintf_value_internal: got IND");
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

void fprintf_nat(FILE * f, Nat n) {
  switch (n.type) {
    case SMALL: {
      char tmp[9] = {0};
      memcpy(tmp, (char *)&n.direct, 8);
      if (is_symbol(tmp)) {
        fprintf(f, "%%%s", tmp);
      } else {
        fprintf(f, "%" PRIu64, n.direct);
      }
      break;
    }
    case BIG: {
      long num_chars = n.size * 4;
      // add 1 for null terminator
      char * nat_str = calloc((num_chars+1), sizeof(char));
      memcpy(nat_str, n.nat, num_chars);
      if (!(is_symbol(nat_str))) {
        free(nat_str);
        nat_str = nn_get_str(n.nat, n.size);
      }
      fprintf(f, "%%%s", nat_str);
      free(nat_str);
      break;
    }
  }
}

////////////////////////////////////////////////////////////////////////////////
//  Construction

Nat d_Nat(u64 n) {
  return (Nat){.type = SMALL, .direct = n};
}

Value * a_Nat(u64 n) {
  Value * res = (Value *)malloc(sizeof(Value));
  res->type = NAT;
  res->n = d_Nat(n);
  return res;
}

Value * a_Big(Nat n) {
  Value * res = (Value *)malloc(sizeof(Value));
  res->type = NAT;
  res->n = n;
  return res;
}

Value * a_Pin(Value * v) {
  Value * res = (Value *)malloc(sizeof(Value));
  res->type = PIN;
  res->p = v;
  return res;
}

Value * a_Law(Nat n, Nat a, Value * b) {
  Value * res = (Value *)malloc(sizeof(Value));
  res->type = LAW;
  res->l.n = n;
  res->l.a = a;
  res->l.b = b;
  return res;
}

Value * a_App(Value * f, Value * g) {
  Value * res = (Value *)malloc(sizeof(Value));
  res->type = APP;
  res->a.f = f;
  res->a.g = g;
  return res;
}

Value * a_Hol() {
  Value * res = (Value *)malloc(sizeof(Value));
  res->type = HOL;
  return res;
}

////////////////////////////////////////////////////////////////////////////////
//  Nat Operators

bool EQ(Nat a, Nat b) {
  if ((a.type == SMALL) && b.type == SMALL)
    return (a.direct == b.direct);
  if ((a.type == BIG) && b.type == BIG) {
    if (a.size != b.size) return false;
    int res = nn_equal_m(a.nat, b.nat, a.size);
    return (res == 1);
  }
  return false;
}

bool EQZ(Nat a) {
  return (EQ(a, d_Nat(0)));
}

bool EQ1(Nat a) {
  return (EQ(a, d_Nat(1)));
}

bool EQ2(Nat a) {
  return (EQ(a, d_Nat(2)));
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
          int res = nn_cmp_m(a.nat, b.nat, a.size);
          return (res < 0);
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
          int res = nn_cmp_m(a.nat, b.nat, a.size);
          return (res > 0);
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

Nat Inc(Nat n) {
  switch(n.type) {
    case SMALL:
      if (n.direct == UINT64_MAX) {
        long sz = 3;
        nn_t nat_buf = nn_init(sz);
        nn_zero(nat_buf, sz);
        nn_bit_set(nat_buf, 65);
        return (Nat){ .type = BIG, .size = sz, .nat = nat_buf };
      }
      return (Nat){ .type = SMALL, .direct = (n.direct+1) };
    case BIG: {
      len_t new_size = n.size;
      nn_t nat_buf = nn_init(new_size);
      word_t c = nn_add1(nat_buf, n.nat, n.size, 1);
      if (c > 0) {
        new_size++;
        realloc_(nat_buf, new_size * sizeof(word_t));
        nat_buf[new_size-1] = c;
      }
      return (Nat){ .type = BIG, .size = new_size, .nat = nat_buf };
    }
  }
}

Nat Dec(Nat n) {
  switch(n.type) {
    case SMALL:
      if (n.direct == 0) {
        return d_Nat(0);
      }
      return (Nat){ .type = SMALL, .direct = (n.direct-1) };
    case BIG: {
      len_t new_size = n.size;
      nn_t nat_buf = nn_init(new_size);
      word_t c = nn_sub1(nat_buf, n.nat, n.size, 1);
      // borrow (nonzero c) should only be possible if we underflowed a single
      // u32. our invariant is to convert to SMALL when we reach 2 u32, so we
      // should never encounter this case.
      assert (c == 0);
      if ((nat_buf[n.size] == 0)) {
        new_size--;
        if (new_size == 2) {
          // shrink BIG to SMALL
          u64 direct;
          assert (new_size * sizeof(word_t) == 8);
          memcpy((char *)direct, nat_buf, 8);
          nn_clear(nat_buf);
          return (Nat){ .type = SMALL, .direct = direct };
        }
        realloc_(nat_buf, new_size * sizeof(word_t));
      }
      return (Nat){ .type = BIG, .size = new_size, .nat = nat_buf };
    }
  }
}

// TODO
Nat Add(Nat a, Nat b) {
  crash("Add: unimpl");
}

// TODO
Nat Sub(Nat a, Nat b) {
  crash("Sub: unimpl");
}

// TODO
Nat Mul(Nat a, Nat b) {
  crash("Mul: unimpl");
}

// TODO
Nat Div(Nat a, Nat b) {
  crash("Div: unimpl");
}

////////////////////////////////////////////////////////////////////////////////
//  Jets

typedef struct Jet {
  char * name;
  u64 arity;
  Value * (*jet_exec)(Value **args);
} Jet;

Value * to_nat(Value * x) {
  return (IS_NAT(x)) ? x : a_Nat(0);
}

Value * add_jet(Value **args) {
  Nat x = NT(to_nat(args[0]));
  Nat y = NT(to_nat(args[1]));
  return a_Big(Add(x, y));
}

Value * sub_jet(Value **args) {
  Nat x = NT(to_nat(args[0]));
  Nat y = NT(to_nat(args[1]));
  return a_Big(Sub(x, y));
}

Value * mul_jet(Value **args) {
  Nat x = NT(to_nat(args[0]));
  Nat y = NT(to_nat(args[1]));
  return a_Big(Mul(x, y));
}

Value * div_jet(Value **args) {
  Nat x = NT(to_nat(args[0]));
  Nat y = NT(to_nat(args[1]));
  return a_Big(Div(x, y));
}

Value * dec_jet(Value **args) {
  Nat x = NT(to_nat(args[0]));
  return a_Big(Dec(x));
}

#define NUM_JETS 5
Jet jet_table[NUM_JETS] =
  { (Jet) {.name = "_Add", .arity = 2, .jet_exec = add_jet }
  , (Jet) {.name = "_Sub", .arity = 2, .jet_exec = sub_jet }
  , (Jet) {.name = "_Mul", .arity = 2, .jet_exec = mul_jet }
  , (Jet) {.name = "_Div", .arity = 2, .jet_exec = div_jet }
  , (Jet) {.name = "_Dec", .arity = 1, .jet_exec = dec_jet }
  };

////////////////////////////////////////////////////////////////////////////////
//  Seeds

Value * frag_load(Value **tab, u64 tabSz, int *, u64 *, u64 **);

Value * frag_load_cell(Value **tab, u64 tabSz, int *use, u64 *acc, u64 **mor) {
  Value *f = frag_load(tab, tabSz, use, acc, mor);
  Value *x = frag_load(tab, tabSz, use, acc, mor);
  return a_App(f,x);
}

u64 u64_bits (u64 w) {
  if (!w) { return 0; }
  return 64 - __builtin_clzll(w);
}

Value * frag_load(Value **tab, u64 tabSz, int *use, u64 *acc, u64 **mor) {
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

Value * seed_load(u64 *buf) {
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

  Value **tab = malloc(sizeof(Value*) * n_entries);

  // How big are the bignats?
  u64 bigwidths[n_bigs];
  for (int i=0; i<n_bigs; i++) {
    bigwidths[i] = buf[5+i];
  }

  Value **next_ref = tab;
  int used = 5 + n_bigs; // number of words used

  for (int i=0; i<n_bigs; i++) {
    u64 wid  = bigwidths[i];

    u64 * big_buf = calloc(wid, sizeof(u64));
    big_buf = memcpy(big_buf, buf+used, wid*sizeof(u64));
    Nat big_nat = (Nat){.type=BIG, .size=wid, .nat = NULL};

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
//  Interpreter stack fns

Value * deref(Value * x) {
  while (TY(x) == IND) {
    x = IN(x);
  }
  return x;
}

Value * pop() {
  if (sp == 0) crash("pop: empty stack");
  sp--;
  return stack[sp];
}

Value * pop_deref() {
  return deref(pop());
}

Value ** get_ptr(u64 idx) {
  if (idx >= sp) crash("get: indexed off stack");
  return &stack[(sp-1)-idx];
}

Value * get(u64 idx) {
  return *get_ptr(idx);
}

Value * get_deref(u64 idx) {
  return deref(get(idx));
}

////////////////////////////////////////////////////////////////////////////////
//  DOT printing

int dot_count = 0;
char * dot_file_path = "./dot";

char * p_ptr(Value * x) {
  char * buf = malloc(20*sizeof(char));
  if (x == NULL) {
    sprintf(buf, "N_null");
  } else {
    sprintf(buf, "N_%p", x);
  }
  return buf;
}

void fprintf_heap(FILE *f, Node *input, Node *seen) {
  // empty input - done
  if (null_list(input)) return;
  Value * v = (Value *)input->ptr;
  input = input->next;
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
      char * v_p = p_ptr(v);
      char * i_p = p_ptr(IT(v));
      fprintf(f, "%s [label=pin];\n", v_p);
      fprintf(f, "%s -> %s [arrowhead=box];\n", v_p, i_p);
      free(v_p);
      free(i_p);
      input = cons((void *)IT(v), input);
      break;
    }
    case LAW: {
      char * v_p = p_ptr(v);
      char * b_p = p_ptr(BD(v));
      fprintf(f, "%s [label=\"law nm:", v_p);
      fprintf_nat(f, NM(v));
      fprintf(f, " ar:");
      fprintf_nat(f, AR(v));
      fprintf(f, "\"];\n");
      fprintf(f, "%s -> %s [label=bd];\n", v_p, b_p);
      free(v_p);
      free(b_p);
      input = cons((void *)BD(v), input);
      break;
    }
    case APP: {
      char * v_p = p_ptr(v);
      char * h_p = p_ptr(HD(v));
      char * t_p = p_ptr(TL(v));
      fprintf(f, "%s [label=\"@\"]", v_p);
      fprintf(f, "%s -> %s [arrowhead=crow];\n", v_p, h_p);
      fprintf(f, "%s -> %s [arrowhead=vee];\n",  v_p, t_p);
      free(v_p);
      free(h_p);
      free(t_p);
      input = cons((void *)HD(v), input);
      input = cons((void *)TL(v), input);
      break;
    }
    case NAT: {
      char * v_p = p_ptr(v);
      fprintf(f, "%s [label=\"", v_p);
      fprintf_nat(f, NT(v));
      fprintf(f, "\"];\n");
      free(v_p);
      break;
    }
    case IND: {
      char * v_p = p_ptr(v);
      char * i_p = p_ptr(IN(v));
      fprintf(f, "%s [label=ind];\n", v_p);
      fprintf(f, "%s -> %s [arrowhead=dot];\n", v_p, i_p);
      free(v_p);
      free(i_p);
      input = cons((void *)IN(v), input);
      break;
    }
    case HOL: {
      char * v_p = p_ptr(v);
      fprintf(f, "%s [label=hole];\n", v_p);
      free(v_p);
      break;
    }
  }
  seen = cons((void *)v, seen);
  return fprintf_heap(f, input, seen);
}

void fprintf_stack(FILE *f, Node *input) {
  // print "stack topper"
  // => stack [label="<ss> stack|<s0>|<s1>|<s2>", color=blue, height=2.5];
  fprintf(f, "stack [label=\"<ss> stack");
  for (int i = 0; i < length_list(input); i++)
    fprintf(f, "|<s%d>", i);
  fprintf(f, "\", color=blue, height=2.5];\n");

  // print edges between stack topper Values
  int i = 0;
  while (input != NULL) {
    Value * v = (Value *)input->ptr;
    char * v_p = p_ptr(v);
    fprintf(f, "stack:s%d -> %s;\n", i, v_p);
    free(v_p);
    input = input->next;
    i++;
  }
}

Node * stack_to_list() {
  Node * l = NULL;
  if (sp == 0) return l;
  for (u64 i = 0; i < sp; i++) {
    l = cons((void *)get(i), l);
  }
  return l;
}

void write_dot_extra(char *label, char *extra, Value * v) {
  char fp[20] = {0};
  sprintf(fp, "%s/%05d.dot", dot_file_path, dot_count);
  dot_count++;
  FILE * f = fopen(fp, "w+");
  fprintf(f, "digraph {\nbgcolor=\"#665c54\"\n");
  fprintf(f, "label = \"%s\";\n", label);
  fprintf(f, "node [shape=record,width=.1,height=.1];\n");
  fprintf(f, "nodesep=.10;\n");
  fprintf(f, "rankdir=LR;\n");
  fprintf(f, "\n// stack\n");
  Node * s_l = stack_to_list();
  fprintf_stack(f, s_l);
  fprintf(f, "\n// heap\n");
  Node * heap_input = s_l;
  if (v != NULL) {
    heap_input = cons((void *)v, heap_input);
  }
  fprintf_heap(f, heap_input, NULL);
  free(s_l);
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

void update(u64 idx) {
  char lab[20];
  sprintf(lab, "update %lu", idx);
  write_dot(lab);
  //
  Value *head = get_deref(0);
  Value *v    = get_deref(idx);
  if (head != v) {
    // no update needed if equal, and IND on self would form a cycle.
    v->type = IND;
    v->i    = head;
  }
  pop();
}

void push_val(Value *x) {
  char extra[50];
  sprintf(extra, "i[color=red];\ni -> %s", p_ptr(x));
  write_dot_extra("push_val", extra, x);
  if ((sp+1) > STACK_SIZE) crash("push_val: stack overflow");
  stack[sp] = x;
  sp++;
}

void push(u64 idx) {
  char lab[20];
  sprintf(lab, "push %lu", idx);
  write_dot(lab);
  //
  push_val(get_deref(idx));
}

void clone() {
  write_dot("clone");
  //
  push_val(get_deref(0));
}

// before: stack = [n1 n2   rest..]
// after:  stack = [(n2 n1) rest..]
void mk_app() {
  write_dot("mk_app");
  //
  Value * n1 = pop();
  Value * n2 = pop();
  Value * ap = a_App(n2, n1);
  push_val(ap);
}

// before: stack = [n1 n2   rest..]
// after:  stack = [(n1 n2) rest..]
void mk_app_rev() {
  write_dot("mk_app_rev");
  //
  Value * n1 = pop();
  Value * n2 = pop();
  Value * ap = a_App(n1, n2);
  push_val(ap);
}

// before: stack = [n1 n2   rest..]
// after:  stack = [n2 n1   rest..]
void swap() {
  Value * n1 = pop();
  Value * n2 = pop();
  push_val(n1);
  push_val(n2);
}

void stack_grow(u64 count) {
  char lab[20];
  sprintf(lab, "stack_grow %lu", count);
  write_dot(lab);
  for (u64 i = 0; i < count; i++) {
    push_val(NULL);
  }
}

void stack_fill_holes(u64 offset, u64 count) {
  char lab[40];
  sprintf(lab, "stack_fill_holes offset:%lu count:%lu", offset, count);
  write_dot(lab);
  for (u64 i = 0; i < count; i++) {
    *(get_ptr(i+offset)) = a_Hol();
  }
}

void alloc(u64 count) {
  char lab[20];
  sprintf(lab, "alloc %lu", count);
  write_dot(lab);
  //
  stack_grow(count);
  stack_fill_holes(0, count);
}

void slide(u64 count) {
  char lab[20];
  sprintf(lab, "slide %lu", count);
  write_dot(lab);
  //
  Value * top = get_deref(0);
  sp -= count;
  stack[sp-1] = top;
  //
  sprintf(lab, "post slide %lu", count);
  write_dot(lab);
}

void mk_pin() {
  write_dot("mk_pin");
  Value * top = pop_deref();
  if (TY(top) == HOL) crash("mk_pin: hol");
  Value * p = a_Pin(top);
  push_val(p);
}

void mk_law() {
  write_dot("mk_law");
  Value * b = pop_deref();
  Value * a = pop_deref();
  Value * n = pop_deref();
  Nat n_ = NT(n);
  Nat a_ = NT(a);
  push_val(a_Law(n_, a_, b));
}

void incr() {
  write_dot("incr");
  Value * x = pop_deref();
  Nat n = (IS_NAT(x)) ? Inc(NT(x)) : d_Nat(1);
  push_val(a_Big(n));
}

void nat_case() {
  write_dot("nat_case");
  Value * x = pop_deref();
  Value * p = pop_deref();
  Value * z = pop_deref();
  if (IS_NAT(x)) {
    Nat x_ = NT(x);
    if (GT(x_, d_Nat(0))) {
      Value * dec_x = a_Big(Dec(x_));
      Value * ap    = a_App(p, dec_x);
      return push_val(ap);
    }
  }
  return push_val(z);
}

void plan_case() {
  write_dot("plan_case");
  Value * x = pop_deref();
  Value * n = pop_deref();
  Value * a = pop_deref();
  Value * l = pop_deref();
  Value * p = pop_deref();
  switch (TY(x)) {
    case PIN: {
      Value * ap = a_App(p, IT(x));
      push_val(ap);
      return;
    }
    case LAW: {
      Value * ap1 = a_App(l,   a_Big(NM(x)));
      Value * ap2 = a_App(ap1, a_Big(AR(x)));
      Value * ap3 = a_App(ap2, BD(x));
      push_val(ap3);
      return;
    }
    case APP: {
      Value * ap1 = a_App(a,   HD(x));
      Value * ap2 = a_App(ap1, TL(x));
      push_val(ap2);
      return;
    }
    case NAT: {
      Value * ap = a_App(n, x);
      push_val(ap);
      return;
    }
    case HOL: crash("plan_case: HOL");
    case IND: crash("plan_case: IND: impossible");
  }
}

void setup_call(u64 depth) {
  char lab[20];
  sprintf(lab, "setup_call %lu", depth);
  write_dot(lab);
  //
  // setup the call by pulling the TLs out of all apps which we have
  // unwound.
  for (u64 i = 0; i < depth; i++) {
    stack[(sp-1)-i] = TL(stack[(sp-1)-i]);
  }
}

void flip_stack(u64 depth) {
  char lab[20];
  sprintf(lab, "flip_stack %lu", depth);
  write_dot(lab);
  //
  if (depth == 0) return;
  Value * tmp;
  u64 d_1 = depth-1;
  for (u64 i = 0; i < depth/2; i++) {
    tmp                   = stack[(sp-1)-i];
    stack[(sp-1)-i]       = stack[(sp-1)-(d_1-i)];
    stack[(sp-1)-(d_1-i)] = tmp;
  }
}

void eval();

void handle_oversaturated_application(u64 count) {
  char lab[50];
  sprintf(lab, "handle_oversaturated_application %lu", count);
  write_dot(lab);
  //
  // if our application is oversaturated, `depth` will exceed the arity. in this
  // case, we want to re-assemble the apps, and eval the result.
  for (u64 i = 0; i < count; i++) {
    mk_app_rev();
  }
  eval();
}

void backout(u64 depth) {
  char lab[20];
  sprintf(lab, "backout %lu", depth);
  write_dot(lab);
  //
  // pop stack of unwound apps.
  for (u64 i = 0; i < depth; i++) {
    pop();
  }
  // `eval` saved the outermost APP, and that should now be at the bottom
  // of the stack.
}

u64 nat_to_u64(Nat x) {
  if (x.type == BIG) crash("nat_to_u64: BIG!");
  return x.direct;
}

// stack invariant: kal receives its arg `x` at the bottom of the stack. it
// replaces `x` w/ the evaluation of `x`.
//
// kal expects `n` to be the right value for any var-refs in `x` to be at the
// correct depth when they are subtracted from `n`. `n` must take `x` into
// account.
void kal(u64 n) {
  char lab[40];
  sprintf(lab, "kal %lu", n);
  write_dot(lab);
  //
  Value * x = get_deref(0);
  if (IS_NAT(x)) {
    Nat x_nat = NT(x);
    if (LTE(x_nat, d_Nat(n))) {
      push(n - nat_to_u64(x_nat));
      goto end;
    }
    goto raw_const;
  }
  if (TY(x) == APP) {
    Value * car = deref(HD(x));
    if (TY(car) == APP) {
      Value * caar = deref(HD(car));
      if ((IS_NAT(caar)) && EQZ(NT(caar))) {
        // x: ((0 f) y)
        Value * f = deref(TL(car));
        Value * y = deref(TL(x)); // => [(f y) ...]
        push_val(y);              // => [y (f y) ...]
        push_val(f);              // => [f y (f y) ...]
        kal(n+2);                 // => [fres y (f y) ..]
        swap();                   // => [y fres (f y) ..]
        kal(n+2);                 // => [yres fres (f y) ...]
        mk_app();                 // => [(fres yres) (f y) ...]
        eval();                   // => [app_res (f y) ...]
        goto end;
      }
    } else if ((IS_NAT(car)) && EQ2(NT(car))) {
      // (2 y)
      push_val(deref(TL(x)));
      goto end;
    }
  }
raw_const:
  push_val(x);
end:
  return slide(1);
}

// 0 indicates no lets
u64 length_let_spine(Value * x) {
  u64 count = 0;
loop:
  if (TY(x) == APP) {
    Value * car = deref(HD(x));
    if (TY(car) == APP) {
      Value * caar = deref(HD(car));
      if ((IS_NAT(caar)) && EQ1(NT(caar))) {
        // ((1 v) k)
        count++;
        x = deref(TL(x));
        goto loop;
      }
    }
  }
  return count;
}

void eval_law(u64 n) {
  char lab[40];
  sprintf(lab, "eval_law %lu", n);
  write_dot(lab);
  //
  Value * x = pop_deref();
  u64 m = length_let_spine(x);
  //
  stack_grow(m);
  push_val(x);
  stack_fill_holes(1, m);
  //
  Value * b;
  for (u64 i = 0; i < m; i++) {
                                // => [((1 v) b) allocs ...]
    x = pop_deref();            // => [allocs ...]
    push_val(deref(TL(x)));     // => [b allocs ...]
    push_val(deref(TL(HD(x)))); // => [v b allocs ...]
    kal(n+m+1);                 // => [vres b allocs ...]
    update((m+1)-i);            // => [b allocs ...]
  }
                                // => [b allocs ...]
  kal(n+m);                     // => [bres allocs ...]
  eval(); // TODO why is this needed?
  return slide(n+m);
}

void law_step(u64 depth) {
  char lab[40];
  sprintf(lab, "law_step %lu", depth);
  write_dot(lab);
  //
  Value * self = pop_deref();
  if (GT(AR(self), d_Nat(depth))) {
    // unsaturated application. this is a little weird, but works?
    if (depth <= 1) {
      write_dot("unsaturated / 0-backout");
      return;
    }
    backout(depth-1);
  } else {
    setup_call(depth);
    push_val(self);
    flip_stack(depth+1);
    u64 ar = nat_to_u64(AR(self));
    push_val(BD(self));
    eval_law(ar+1);
    if (ar < depth) {
      // oversaturated application
      handle_oversaturated_application(depth - ar);
    }
  }
}

void force();

// 0 indicates an invalid primop.
u64 prim_arity(u64 prim) {
  switch (prim) {
    case 0: { // mk_pin
      return 1;
    }
    case 1: { // mk_law
      return 3;
    }
    case 2: { // incr
      return 1;
    }
    case 3: { // nat_case
      return 3;
    }
    case 4: { // plan_case
      return 5;
    }
    default:
      return 0;
  }
}

// this assumes there are sufficient stack args to saturate whichever primop
// we run.
void do_prim(u64 prim) {
  char lab[40];
  sprintf(lab, "do_prim: %lu", prim);
  write_dot(lab);
  //
  switch (prim) {
    case 0: { // mk_pin
      u64 arity = prim_arity(prim);
      eval();
      return mk_pin();
    }
    case 1: { // mk_law
      u64 arity = prim_arity(prim);
      push(0); force(); // n
      push(1); force(); // a
      push(2); force(); // b
      return mk_law();
    }
    case 2: { // incr
      u64 arity = prim_arity(prim);
      eval();
      return incr();
    }
    case 3: { // nat_case
      u64 arity = prim_arity(prim);
      eval(); // x
      nat_case();
      return eval();
    }
    case 4: { // plan_case
      u64 arity = prim_arity(prim);
      eval(); // x
      plan_case();
      return eval();
    }
  }
}

void unwind(u64 depth) {
  char lab[20];
  sprintf(lab, "unwind %lu", depth);
  write_dot(lab);
  //
  Value * x = get_deref(0);
  switch (TY(x)) {
    case APP: {
      push_val(HD(x));
      return unwind(depth+1);
    }
    case LAW: {
      return law_step(depth);
    }
    case PIN: {
      Value * y = deref(x->p);
      switch (y->type) {
        case NAT: {
          pop(); // pop primop
          u64 prim_u64 = nat_to_u64(NT(y));
          u64 arity = prim_arity(prim_u64);
          //
          if ((arity == 0) || (depth < arity)) {
            // 0 indicates an invalid primop. in that case, or if we are
            // undersaturated, we backout. we subtract 1 since we already popped
            // the primop above.
            return backout(depth-1);
          }
          // run primop
          setup_call(depth);
          flip_stack(arity);
          do_prim(prim_u64);
          //
          if (arity < depth) {
            // oversaturated
            return handle_oversaturated_application(depth - arity);
          } else {
            // application was perfectly saturated.
            return;
          }
        }
        // unwind "through" pins & apps
        // we don't increment `depth` here because we are just setting up
        // for the above APP case, which increments `depth`.
        case APP:
        case PIN: {
          pop(); // pop outer pin
          push_val(y);
          return unwind(depth);
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
      return backout(depth);
    }
    case HOL: {
      crash("unwind: <loop>");
    }
    case IND: {
      crash("unwind: bad deref");
    }
  }
}

void eval() {
  write_dot("eval");
  //
  Value * x = get_deref(0);
  switch (TY(x)) {
    case APP: {
      return unwind(0);
    }
    case PIN:
    case LAW:
    case NAT: {
      return;
    }
    case HOL: crash("eval: HOL");
    case IND: crash("eval: IND");
  }
}

void force_whnf() {
  write_dot("force_whnf");
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
  write_dot("force");
  //
  Value * top = get_deref(0);
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

Value * run(Value * v) {
  stack = malloc(STACK_SIZE*sizeof(Value *));
  sp = 0;
  //
  push_val(v);
  clone();
  force();
  //
  write_dot("main final");
  Value *res = pop_deref();
  return res;
}

// TODO handle atoms bigger than U64_MAX - this will just overflow
Value *read_atom() {
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

Value *read_exp();

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

#define BUF_LEN 1024

Value *read_sym() {
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
      int u32_sz = sizeof(u32);
      int u32_len = (len / u32_sz) + 1;
      nn_t nat_buf = nn_init(u32_len);
      // TODO is this little endian?
      strcpy((char*)nat_buf, buf);
      Nat n = (Nat){.type=BIG, .size=u32_len, .nat = nat_buf};
      return a_Big(n);
    } else {
      u64 word = 0;
      memcpy((char*)&word, buf, len);
      return a_Nat(word);
    }
}

Value *read_exp() {
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
                Value *loaded = seed_load(words);
                check_value(loaded);
                return loaded;
            }
        }
        crash("load files");
        return NULL;
    }
    case '(': {
        eat_spaces();
        Value *f = read_exp();
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

Value *read_exp_top() {
 again:
  eat_spaces();
  if (feof(stdin)) return NULL;
  return read_exp();
}

int main (void) {
  // Value * x = a_Nat(2);
  // Value * y = a_Nat(3);
  // Value * arr[2] = { x, y };
  // Value * res = jet_table[1].jet_exec(arr);
  // printf("%s\n", print_value(res));

  bool isInteractive = isatty(fileno(stdin));
  again:
    if (isInteractive) printf(">> ");
    Value *v = read_exp_top();
    if (!v) return 0;
    Value * res = run(v);
    fprintf_value(stdout, res);
    printf("\n");
    goto again;
    return 0;
}
