#include <stdbool.h>
#include <stdio.h>

#define UNUSED(...) (void)(__VA_ARGS__)
// #define _DEBUG
#ifdef _DEBUG
#define DEBUG(...) printf(__VA_ARGS__)
#define DBG(...) dbgprint(__VA_ARGS__)
#else
#define DEBUG(...)
#define DBG(...) (void)(__VA_ARGS__)
#endif

#define MIN(A, B)                                                              \
  ({                                                                           \
    typeof((A)) a = (A);                                                       \
    typeof((B)) b = (B);                                                       \
    a < b ? a : b;                                                             \
  })
#define BOXED(P)                                                               \
  ({                                                                           \
    SmallValue v = {.p = (P)};                                                 \
    v;                                                                         \
  })
#define UNBOXED_INT_FITS(N)                                                    \
  ({                                                                           \
    long long n = (N);                                                         \
    (n >= 0 && n <= ShortTag_IntMask) ||                                       \
        (n < 0 && n >= -(long long)ShortTag_IntMask - 1);                      \
  })
#define UNBOXED_INT(N)                                                         \
  ({                                                                           \
    long long n = (N);                                                         \
    SmallValue v = {.n = ShortTag_Present | ShortTag_Int |                     \
                         (n & ShortTag_IntMask) |                              \
                         ((n < 0) ? ShortTag_IntSignBit : 0)};                 \
    v;                                                                         \
  })
#define READ_UNBOXED_INT(N)                                                    \
  ({                                                                           \
    long long n = (N);                                                         \
    if (n & ShortTag_IntSignBit) {                                             \
      n &= ShortTag_IntMask;                                                   \
      n |= ShortTag_SignExtension;                                             \
    } else                                                                     \
      n &= ShortTag_IntMask;                                                   \
    n;                                                                         \
  })

typedef enum : unsigned char {
  Tag_Poison,
  Tag_Nil,
  Tag_False,
  Tag_True,
  Tag_Pair,
  Tag_Int,
  // interned symbol
  Tag_Sym,
  // non-interned string
  Tag_Str,
  // continuation/execution frame
  Tag_Cont,
  // lisp function
  Tag_Closure,
  // lisp macro (first arg = env, rest = whatever was passed to the macro)
  // returns a (env . value) pair
  Tag_Macro,
  // c function
  Tag_Ffi,
  Tag_FfiEx,
  // c macro
  Tag_FfiMacro,
  Tag_FfiMacroEx,
  // used for storing a single pointer + function for freeing it
  Tag_Userdata,
} Tag;

typedef enum {
  // if ShortTag_Present (highest bit) is set in the pointer, then it's
  // actually a boxed value
  // we do not have to have unboxed reprs for nil/false/true as their pointers
  // are stable
  // same goes for symbols
  // so this is only used for integers for now
  ShortTag_Present = 0x8000000000000000,
  ShortTag_Mask = 0x8000000000000000,
  // use read_value for reading this, don't rely on particular constants
  ShortTag_Int = 0x8000000000000000,
  ShortTag_IntSignBit = 0x4000000000000000,
  ShortTag_SignExtension = 0xC000000000000000,
  // representable values:
  // - 0 .. 0x3FFFFFFFFFFFFFFF
  // - 0xC000000000000000 .. 0xFFFFFFFFFFFFFFFF
  //  -0x4000000000000000 .. -1
  ShortTag_IntMask = 0x3FFFFFFFFFFFFFFF,
} ShortTag;

// certain values may fit in a pointer!
// if the pointer's msb is set, do n & ShortTag_Mask and compare it against
// various ShortTags
// note: while it may be tempting to use unboxed values where possible, if you
// unbox and rebox the value you pay more than if you just never unboxed it in
// the first place
typedef union {
  const struct Value *p;
  unsigned long long n;
} SmallValue;

typedef struct {
  // currently code is expected to be in the format:
  // (arg1 arg2 arg3) . body
  SmallValue code;
  // linked list of name . value
  SmallValue env;
} Closure;

typedef struct {
  const char *p;
  size_t n;
} Str, Sym;

typedef struct {
  Sym sym;
  // boxed version of the symbol
  SmallValue boxed;
} SymEntry;

typedef struct State {
  struct Cont *frame;
  SmallValue ret;
} State;

typedef SmallValue (*lisp_ffi_p)(SmallValue args, SmallValue userdata);
typedef SmallValue (*lisp_macro_p)(SmallValue args, SmallValue *env,
                                   SmallValue userdata);
// returns true if they want to return a value
// returns false if they want to push a stack frame and transfer control flow
typedef bool (*lisp_ffi_ex_p)(SmallValue args, SmallValue userdata,
                              State *state);
typedef bool (*lisp_macro_ex_p)(SmallValue args, SmallValue userdata,
                                State *state);
typedef SmallValue (*lisp_free_p)(void *userdata);

typedef enum : unsigned char {
  // invalid
  Cont_Poison,
  // in the process of evaluating everything in `code`, consing it to `args`,
  // reversing the result and `apply`ing it
  Cont_Expr,
  // in the process of evaluating everything in `code` and simply saving the
  // results to `ret`
  Cont_Body,
  // in the process of evaluating everything in `code` and interpreting it as a
  // macro return result
  Cont_MacroBody,
  // marked bit for gc, always reset after gc is done
  Cont_Marked = 128,
} ContKind;

// an execution frame/continuation
// "code" is where execution is to continue
// "env" is current environment
// "args" is arguments collected so far (will be called upon reaching nil in
// code) "parent" is return address
typedef struct Cont {
  SmallValue code;
  SmallValue env;
  // for Cont_Expr: args (built one by one before running)
  // otherwise: undefined
  SmallValue args;
  int parent_idx;
  ContKind kind;
  // how many interpreters are currently using this continuation
  // note that it may also be referenced by values
  // (this isn't about parallel interpreters but about nested interpreters)
  //
  // also, how many other live continuations reference this
  unsigned short refcount;
  // also, +1 for value cells that reference this
  unsigned char heap_refcount;
} Cont;

typedef struct Value {
  Tag tag;
  unsigned char refcount;
  bool mark;
  union {
    Closure closure;
    Cont *cont;
    struct {
      long long n;
      // FIXME: this is for arbitrary precision ints, but it's not implemented
      SmallValue next;
    } i;
    SymEntry *sym;
    struct {
      const char *p;
      int n;
      // false, if ever true gc adjustments will be necessary
      bool heap;
    } str;
    struct {
      SmallValue car;
      SmallValue cdr;
    } pair;
    struct {
      union {
        lisp_ffi_p f;
        lisp_ffi_ex_p fex;
        lisp_macro_p m;
        lisp_macro_ex_p mex;
      };
      // may be null
      SmallValue userdata;
    } ffi;
    struct {
      lisp_free_p free;
      void *data;
    } userdata;
  };
} Value;

_Static_assert(sizeof(Value) == 24, "gc cell size mismatch");

void dbgprint(SmallValue val);

[[noreturn]] void panic(const char *msg, SmallValue val) {
  fprintf(stderr, "%s\n", msg);
  if (val.p != NULL) {
    dbgprint(val);
    printf("\n");
  }
  while (true) {
  }
}

typedef struct {
  int idx;
} SymIdx;

// real impl would use hashmap
SymEntry symbols[4096];
int sym_count = 0;
// real impl would use a heap+gc
Value values[4096];
int min_val = 0;
int val_count = 0;
// real impl would use a heap+gc
Cont stack_frames[4096];
int frame_count = 0;

typedef enum {
// symbols must come first as their indices are reused for interned symbol
// table
#define SYM(K, V) K,
#include "symbols.def"
#undef SYM
  Const_Poison,
  Const_Nil,
  Const_False,
  Const_True,
  Const_Count,
} Values;

SmallValue VPOISON = {.p = &values[Const_Poison]};
SmallValue VNIL = {.p = &values[Const_Nil]};
SmallValue VBOOL[2] = {{.p = &values[Const_False]}, {.p = &values[Const_True]}};

void init() {
  for (int i = 0; i < sizeof(stack_frames) / sizeof(stack_frames[0]); ++i) {
    stack_frames[i].refcount = 0;
    stack_frames[i].heap_refcount = 0;
  }
  values[Const_Poison].tag = Tag_Poison;
  values[Const_Nil].tag = Tag_Nil;
  values[Const_False].tag = Tag_False;
  values[Const_True].tag = Tag_True;
#define SYM(N, S)                                                              \
  {                                                                            \
    Sym sym = {(S), __builtin_strlen((S))};                                    \
    SymEntry s = {sym, &values[N]};                                            \
    symbols[sym_count] = s;                                                    \
    Value v = {Tag_Sym, .sym = &symbols[sym_count++]};                         \
    values[N] = v;                                                             \
  }
#include "symbols.def"
#undef SYM
  val_count = Const_Count;
  min_val = val_count;
}

void gc();

inline SmallValue alloc_value_raw(Value val) {
  while (true)
    if (val_count == sizeof(values) / sizeof(values[0])) {
      val_count = min_val;
      gc();
    } else if (val_count > sizeof(values) / sizeof(values[0])) {
      panic("too many values???", BOXED(NULL));
    } else if (values[val_count].tag == Tag_Poison) {
      break;
    } else {
      ++val_count;
    }
  values[val_count] = val;
  return BOXED(&values[val_count++]);
}

SmallValue intern_sym(Sym sym) {
  for (int i = 0; i < sym_count; ++i) {
    if (sym.n != symbols[i].sym.n)
      continue;
    if (!__builtin_memcmp(sym.p, symbols[i].sym.p, sym.n))
      return symbols[i].boxed;
  }

  if (sym_count >= sizeof(symbols) / sizeof(symbols[0]))
    panic("symtab overflow", BOXED(NULL));
  Value val = {Tag_Sym, .sym = &symbols[sym_count++]};
  val.sym->sym = sym;
  val.sym->boxed = alloc_value_raw(val);
  return val.sym->boxed;
}

Cont *alloc_frame(Cont val) {
  val.refcount = 0;
  val.heap_refcount = 0;
  while (stack_frames[frame_count].refcount +
         stack_frames[frame_count].heap_refcount) {
    frame_count =
        (frame_count + 1) % (sizeof(stack_frames) / sizeof(stack_frames[0]));
  }
  Cont *ret = &stack_frames[frame_count];
  if (val.parent_idx == frame_count) {
    DEBUG("%p\n", ret);
    panic("allocating a cyclic frame", BOXED(NULL));
  }
  *ret = val;
  frame_count =
      (frame_count + 1) % (sizeof(stack_frames) / sizeof(stack_frames[0]));
  return ret;
}

#define REFUNREFFRAME(ref_frame, unref_frame, refcount)                        \
  void ref_frame(Cont *frame) {                                                \
    if (!frame)                                                                \
      return;                                                                  \
    DEBUG("frefing %p from %d\n", frame, frame->refcount);                     \
    if (frame->refcount++ == 0)                                                \
      if (frame->parent_idx >= 0)                                              \
        ref_frame(&stack_frames[frame->parent_idx]);                           \
  }                                                                            \
  void unref_frame(Cont *frame) {                                              \
    if (!frame)                                                                \
      return;                                                                  \
    DEBUG("unfrefing %p from %d\n", frame, frame->refcount);                   \
    if (--frame->refcount == 0)                                                \
      if (frame->parent_idx >= 0)                                              \
        unref_frame(&stack_frames[frame->parent_idx]);                         \
  }

REFUNREFFRAME(ref_frame, unref_frame, refcount);
REFUNREFFRAME(ref_frame_heap, unref_frame_heap, heap_refcount);

inline void ref_val(SmallValue val) {
  if (val.n & ShortTag_Present)
    return;
  if (!val.p)
    return;
  // DEBUG("incing %p\n", val.p);
  ++((Value *)val.p)->refcount;
}

inline void unref_val(SmallValue val) {
  if (val.n & ShortTag_Present)
    return;
  if (!val.p)
    return;
  // DEBUG("decing %p\n", val.p);
  --((Value *)val.p)->refcount;
}

void pop_frames() {
  while (frame_count > 0 &&
         stack_frames[frame_count - 1].refcount +
                 stack_frames[frame_count - 1].heap_refcount ==
             0) {
    DEBUG("popping stack frame\n");
    --frame_count;
  }
}

#define ALLOCF(x, s)                                                           \
  ({                                                                           \
    Cont *c = alloc_frame((x));                                                \
    DEBUG("alloc frame %ld: " s "\n", c - stack_frames);                       \
    c;                                                                         \
  })
#define SETALLOCF(st, f, S)                                                    \
  {                                                                            \
    State *s = (st);                                                           \
    Cont *old = s->frame;                                                      \
    if (f.parent_idx == old - stack_frames) {                                  \
      s->frame = ALLOCF(f, S);                                                 \
      ++s->frame->refcount;                                                    \
    } else if (old && old->refcount == 1 && old->heap_refcount == 0 &&         \
               f.parent_idx == old->parent_idx) {                              \
      old->code = f.code;                                                      \
      old->env = f.env;                                                        \
      old->args = f.args;                                                      \
    } else {                                                                   \
      if (f.parent_idx >= 0)                                                   \
        ref_frame(&stack_frames[f.parent_idx]);                                \
      unref_frame(old);                                                        \
      pop_frames();                                                            \
      s->frame = ALLOCF(f, S);                                                 \
      ref_frame(s->frame);                                                     \
      if (f.parent_idx >= 0)                                                   \
        unref_frame(&stack_frames[f.parent_idx]);                              \
    }                                                                          \
  }
#define SETRET(st, f)                                                          \
  {                                                                            \
    State *s = (st);                                                           \
    SmallValue v = (f);                                                        \
    unref_val(s->ret);                                                         \
    ref_val(s->ret = v);                                                       \
  }
#define SETF(st, f)                                                            \
  {                                                                            \
    State *s = (st);                                                           \
    Cont *c = (f);                                                             \
    Cont *old = s->frame;                                                      \
    s->frame = c;                                                              \
    ref_frame(c);                                                              \
    if (old)                                                                   \
      unref_frame(old), pop_frames();                                          \
  }
#define POPF(st)                                                               \
  {                                                                            \
    if (--(st)->frame->refcount + (st)->frame->heap_refcount == 0 &&           \
        frame_count == (st)->frame - stack_frames + 1) {                       \
      do {                                                                     \
        --frame_count;                                                         \
      } while (frame_count > 0 &&                                              \
               stack_frames[frame_count - 1].refcount +                        \
                       stack_frames[frame_count - 1].heap_refcount ==          \
                   0);                                                         \
    }                                                                          \
    if ((st)->frame->parent_idx >= 0)                                          \
      (st)->frame = &stack_frames[(st)->frame->parent_idx];                    \
    else                                                                       \
      (st)->frame = NULL;                                                      \
  }

#define VISIT_VAL(v, visit)                                                    \
  switch (v.tag) {                                                             \
  case Tag_Poison:                                                             \
  case Tag_Nil:                                                                \
  case Tag_False:                                                              \
  case Tag_True:                                                               \
  case Tag_Sym:                                                                \
  case Tag_Str:                                                                \
  case Tag_Userdata:                                                           \
    break;                                                                     \
  case Tag_Ffi:                                                                \
  case Tag_FfiEx:                                                              \
  case Tag_FfiMacro:                                                           \
  case Tag_FfiMacroEx:                                                         \
    if (v.ffi.userdata.n)                                                      \
      visit(v.ffi.userdata);                                                   \
    break;                                                                     \
  case Tag_Pair:                                                               \
    visit(v.pair.car);                                                         \
    visit(v.pair.cdr);                                                         \
    break;                                                                     \
  case Tag_Int:                                                                \
    if (v.i.next.n)                                                            \
      visit(v.i.next);                                                         \
    break;                                                                     \
  case Tag_Cont:                                                               \
    /* raw continuation isn't a value, don't visit it */                       \
    break;                                                                     \
  case Tag_Closure:                                                            \
  case Tag_Macro:                                                              \
    visit(v.closure.code);                                                     \
    visit(v.closure.env);                                                      \
    break;                                                                     \
  }

inline void mark_frame(Cont *cont);
void mark_value(SmallValue val) {
  if (!val.p)
    return;
  if (val.n & ShortTag_Present)
    return;
  if (val.p - values < min_val)
    return;
  if (val.p->mark)
    return;
  ((Value *)val.p)->mark = true;
  Value v = *val.p;
  if (v.tag == Tag_Cont)
    mark_frame(v.cont);
  VISIT_VAL(v, mark_value);
}

inline void mark_frame(Cont *cont) {
  while (cont && !(cont->kind & Cont_Marked)) {
    cont->kind |= Cont_Marked;
    mark_value(cont->args);
    mark_value(cont->code);
    mark_value(cont->env);
    cont = (cont->parent_idx >= 0) ? &stack_frames[cont->parent_idx] : NULL;
  }
}

inline void mark() {
  for (int i = min_val; i < sizeof(values) / sizeof(values[0]); ++i)
    values[i].mark = false;
  // visit all active closures and recursively mark all values as ued
  for (int i = 0; i < sizeof(stack_frames) / sizeof(stack_frames[0]); ++i) {
    if (stack_frames[i].refcount)
      mark_frame(&stack_frames[i]);
  }
  // ^ note: we don't consider heap_refcount for continuations
  //   because heap_refcount is necessarily conservative, it will instead
  //   be handled by mark_value
  // visit all objects referenced by C code
  for (int i = min_val; i < sizeof(values) / sizeof(values[0]); ++i) {
    if (values[i].refcount && !values[i].mark)
      mark_value(BOXED(&values[i]));
  }
  for (int i = 0; i < sizeof(stack_frames) / sizeof(stack_frames[0]); ++i)
    stack_frames[i].kind &= ~Cont_Marked;
}

void free_value(Value val) {
  switch (val.tag) {
  case Tag_Poison:
  case Tag_Nil:
  case Tag_False:
  case Tag_True:
  case Tag_Sym:
  case Tag_Str:
  case Tag_Ffi:
  case Tag_FfiEx:
  case Tag_FfiMacro:
  case Tag_FfiMacroEx:
  case Tag_Pair:
  case Tag_Int:
  case Tag_Closure:
  case Tag_Macro:
    break;
  case Tag_Userdata:
    val.userdata.free(val.userdata.data);
    break;
  case Tag_Cont:
    unref_frame_heap(val.cont);
    break;
  }
}

inline void sweep() {
  for (int i = min_val; i < sizeof(values) / sizeof(values[0]); ++i)
    if (!values[i].mark && values[i].tag != Tag_Sym) {
      free_value(values[i]);
      values[i].tag = Tag_Poison;
    }
}

void gc() {
  mark();
  sweep();
}

static inline SmallValue alloc_value(Value val) {
  switch (val.tag) {
  case Tag_Nil:
    return VNIL;
  case Tag_Int:
    if (!val.i.next.n && UNBOXED_INT_FITS(val.i.n))
      return UNBOXED_INT(val.i.n);
  case Tag_False:
    return VBOOL[false];
  case Tag_True:
    return VBOOL[true];
  case Tag_Sym:
    return val.sym->boxed;
  case Tag_Cont:
    // closures are normally refcounted and cleared immediately upon no longer
    // being needed this marks them as used by the heap, which stops that
    // mechanism
    ref_frame_heap(val.cont);
  default:
    break;
  }
  VISIT_VAL(val, ref_val);
  SmallValue ret = alloc_value_raw(val);
  VISIT_VAL(val, unref_val);
  return ret;
}

inline Value read_value(SmallValue val) {
  if (val.n & ShortTag_Present) {
    if (val.n & ShortTag_Int) {
      Value ret = {Tag_Int, .i = {READ_UNBOXED_INT(val.n), BOXED(NULL)}};
      return ret;
    } else {
      panic("invalid short tag", val);
    }
  } else {
    return *val.p;
  }
}

void exit_comment(const char **code) {
  while (true)
    switch (**code) {
    case 0:
    case '\n':
    case '\r':
      return;
    default:
      ++*code;
      break;
    }
}

void skip_ws(const char **code) {
  while (true) {
    switch (**code) {
    case ' ':
    case '\t':
    case '\r':
    case '\v':
    case '\n':
      ++*code;
      break;
    case ';':
      exit_comment(code);
      break;
    default:
      return;
    }
  }
}

#define PUSH(env, x)                                                           \
  {                                                                            \
    SmallValue env0 = (env);                                                   \
    ref_val(env0);                                                             \
    env = cons((x), env0);                                                     \
    unref_val(env0);                                                           \
  }

static inline SmallValue cons(SmallValue car, SmallValue cdr) {
  Value val = {Tag_Pair, .pair = {car, cdr}};
  return alloc_value(val);
}

SmallValue negate(SmallValue n) {
  Value x = read_value(n);
  if (x.tag != Tag_Int)
    panic("negating non-int", n);
  Value r = {Tag_Int, .i = {-x.i.n, BOXED(NULL)}};
  return alloc_value(r);
}

#define READ0(S, ARGS)                                                         \
  SmallValue X;                                                                \
  {                                                                            \
    Value pair = read_value(ARGS);                                             \
    if (pair.tag != Tag_Nil)                                                   \
      panic(#S " expected 0 arguments, got 1+", ARGS);                         \
  }
#define READ1(S, ARGS, X)                                                      \
  SmallValue X;                                                                \
  {                                                                            \
    Value pair = read_value(ARGS);                                             \
    if (pair.tag != Tag_Pair)                                                  \
      panic(#S " expected 1 argument, got 0", ARGS);                           \
    X = pair.pair.car;                                                         \
    if (pair.pair.cdr.p != VNIL.p)                                             \
      panic(#S " expected 1 argument, got 2+", ARGS);                          \
  }
#define READ2(S, ARGS, X, Y)                                                   \
  SmallValue X, Y;                                                             \
  {                                                                            \
    Value pair = read_value(ARGS);                                             \
    if (pair.tag != Tag_Pair)                                                  \
      panic(#S " expected 2 arguments, got 0", ARGS);                          \
    X = pair.pair.car;                                                         \
    pair = read_value(pair.pair.cdr);                                          \
    if (pair.tag != Tag_Pair)                                                  \
      panic(#S " expected 2 arguments, got 1", ARGS);                          \
    Y = pair.pair.car;                                                         \
    if (pair.pair.cdr.p != VNIL.p)                                             \
      panic(#S " expected 2 arguments, got 3+", ARGS);                         \
  }
#define READ3(S, ARGS, X, Y, Z)                                                \
  SmallValue X, Y, Z;                                                          \
  {                                                                            \
    Value pair = read_value(ARGS);                                             \
    if (pair.tag != Tag_Pair)                                                  \
      panic(#S " expected 3 arguments, got 0", ARGS);                          \
    X = pair.pair.car;                                                         \
    pair = read_value(pair.pair.cdr);                                          \
    if (pair.tag != Tag_Pair)                                                  \
      panic(#S " expected 3 arguments, got 1", ARGS);                          \
    Y = pair.pair.car;                                                         \
    pair = read_value(pair.pair.cdr);                                          \
    if (pair.tag != Tag_Pair)                                                  \
      panic(#S " expected 3 arguments, got 2", ARGS);                          \
    Z = pair.pair.car;                                                         \
    if (pair.pair.cdr.p != VNIL.p)                                             \
      panic(#S " expected 3 arguments, got 4+", ARGS);                         \
  }
// be mindful of refcounts when extending
#define BINOP(name, name2, op)                                                 \
  SmallValue name(SmallValue n, SmallValue m) {                                \
    Value x = read_value(n);                                                   \
    Value y = read_value(m);                                                   \
    if (x.tag != Tag_Int)                                                      \
      panic(#name2 " a non-int", n);                                           \
    if (y.tag != Tag_Int)                                                      \
      panic(#name2 " a non-int", m);                                           \
    Value r = {Tag_Int, .i = {x.i.n op y.i.n, BOXED(NULL)}};                   \
    return alloc_value(r);                                                     \
  }                                                                            \
  SmallValue name##_ffi(SmallValue args, SmallValue _userdata) {               \
    UNUSED(_userdata);                                                         \
    READ2(name, args, n, m);                                                   \
    return name(n, m);                                                         \
  }
#define BOOLOP(name, name2, op)                                                \
  SmallValue name(SmallValue n, SmallValue m) {                                \
    Value x = read_value(n);                                                   \
    Value y = read_value(m);                                                   \
    if (x.tag != Tag_Int)                                                      \
      panic(#name2 " a non-int", n);                                           \
    if (y.tag != Tag_Int)                                                      \
      panic(#name2 " a non-int", m);                                           \
    if (x.i.n op y.i.n)                                                        \
      return VBOOL[true];                                                      \
    return VBOOL[false];                                                       \
  }                                                                            \
  SmallValue name##_ffi(SmallValue args, SmallValue _userdata) {               \
    UNUSED(_userdata);                                                         \
    READ2(name, args, n, m);                                                   \
    return name(n, m);                                                         \
  }

BINOP(mul, multiplying, *);
BINOP(add, adding, +);
BINOP(sub, subracting, -);
BINOP(div, dividing, /);
BOOLOP(lt, comparing, <);
BOOLOP(le, comparing, <=);
BOOLOP(gt, comparing, >);
BOOLOP(ge, comparing, >=);
BOOLOP(eq, comparing, ==);
BOOLOP(ne, comparing, !=);

SmallValue parse(const char **code);
SmallValue parse_list(const char **code) {
  skip_ws(code);
  SmallValue lhs = parse(code);
  ref_val(lhs);
  if (lhs.p == NULL) {
    unref_val(lhs);
    return VNIL;
  }
  skip_ws(code);
  SmallValue rhs;
  if (**code == '.') {
    ++*code;
    rhs = parse(code);
  } else {
    rhs = parse_list(code);
  }
  unref_val(lhs);
  SmallValue ret = cons(lhs, rhs);
  return ret;
}

// if list, parse this as a list
SmallValue parse(const char **code) {
  skip_ws(code);
  switch (**code) {
  case 0:
  case ')':
    return BOXED(NULL);
  case '"': {
    ++*code;
    Str str = {*code, 0};
    while (**code != '"') {
      switch (**code) {
      case 0:
        panic("unclosed string literal", BOXED(NULL));
      default:
        ++*code;
        ++str.n;
        break;
      }
    }
    ++*code;
    Value val = {Tag_Str, .str = {str.p, str.n, false}};
    return alloc_value(val);
  }
  case '\'': {
    ++*code;
    SmallValue val = parse(code);
    if (val.p == NULL)
      panic("expected a symbol", val);
    return cons(symbols[Sym_Quote].boxed, cons(val, VNIL));
  }
  case '(': {
    ++*code;
    SmallValue ret = parse_list(code);
    if (**code != ')')
      panic("expected )", ret);
    ++*code;
    return ret;
  }
  // just a regular symbol... or maybe a number?
  default: {
    Sym ret = {*code, 0};
    bool number = true;
    while (true) {
      switch (**code) {
      case 0:
      case ' ':
      case '\t':
      case '\r':
      case '\v':
      case '\n':
      case ')': {
        if (ret.n == 0)
          return BOXED(NULL);
        if (number && ret.p[0] == '-' && ret.n == 1)
          number = false;
        if (number) {
          Value n0 = {Tag_Int, .i = {0, BOXED(NULL)}};
          SmallValue n = alloc_value(n0);
          n0.i.n = 10;
          SmallValue ten = alloc_value(n0);
          bool sign = ret.p[0] == '-';
          if (sign)
            ++ret.p;
          for (int i = 0; i < ret.n; ++i) {
            n = mul(n, ten);
            n0.i.n = ret.p[i] - '0';
            SmallValue digit = alloc_value(n0);
            n = add(n, digit);
          }
          if (sign)
            n = negate(n);
          return n;
        }
        return intern_sym(ret);
      }
      case '-':
        if (*code != ret.p)
          number = false;
      default:
        number = number && ((**code >= '0' && **code <= '9') || **code == '-');
        ++*code;
        ++ret.n;
        break;
      }
    }
  }
  }
}

SmallValue reverse(SmallValue list) {
  if (list.p == VNIL.p)
    return list;
  Value v = read_value(list);
  if (v.pair.cdr.p == VNIL.p)
    return list;
  SmallValue ret = VNIL;
  ref_val(list);
  while (true) {
    if (v.tag != Tag_Pair)
      panic("reverse expected a list", list);
    ret = cons(v.pair.car, ret);
    unref_val(list);
    if (v.pair.cdr.p == VNIL.p)
      break;
    ref_val(v.pair.cdr);
    list = v.pair.cdr;
    v = read_value(list);
  }
  return ret;
}

SmallValue bind_env(SmallValue bindings, SmallValue operands, SmallValue env) {
  DEBUG("binding ");
  DBG(bindings);
  DEBUG("\n");
  while (true) {
    if (bindings.p == VNIL.p) {
      if (operands.p != VNIL.p) {
        panic("function arity mismatch", operands);
      }
      return env;
    }
    Value b = read_value(bindings);
    switch (b.tag) {
    case Tag_Sym: {
      // just bind the rest
      PUSH(env, cons(bindings, operands));
      operands = VNIL;
    }
    case Tag_Pair: {
      Value target = read_value(b.pair.car);
      if (target.tag != Tag_Sym)
        panic("function argument binding is not a symbol", b.pair.car);
      Value args = read_value(operands);
      if (args.tag != Tag_Pair)
        panic("function arity mismatch", operands);
      PUSH(env, cons(b.pair.car, args.pair.car));
      operands = args.pair.cdr;
      bindings = b.pair.cdr;
      break;
    }
    default:
      panic("function argument bindings are not a symbol or a list", bindings);
    }
  }
}

// - ensure the stack top has no more code to execute
// - ensure the stack top is not a macro (if it's a macro and we pop it we won't
// know it's a macro)
// - ensure we keep at least one stack frame active at all times
// - if all of the above is ok, we do a tail call
#define PREPARE_CALL(st)                                                       \
  if (st->frame->code.p == VNIL.p && st->frame->kind == Cont_Body &&           \
      st->frame->parent_idx >= 0) {                                            \
    do                                                                         \
      POPF(st)                                                                 \
    while (st->frame->code.p == VNIL.p && st->frame->kind == Cont_Body &&      \
           st->frame->parent_idx >= 0);                                        \
  }

bool apply(State *st, SmallValue operator, SmallValue args) {
  Value op = read_value(operator);
  switch (op.tag) {
  case Tag_Closure:
  case Tag_Macro:
    DEBUG("applying ");
    DBG(operator);
    DEBUG("\n");
    Value code = read_value(op.closure.code);
    if (code.tag != Tag_Pair)
      panic("closure code not a list", op.closure.code);
    SmallValue bindings = code.pair.car;
    SmallValue body = code.pair.cdr;
    ref_val(body);
    ref_val(bindings);
    ref_val(args);
    ref_val(operator);
    if (op.tag != Tag_Macro)
      PREPARE_CALL(st);
    DBG(operator);
    DEBUG("\n");
    Cont fr = {
        .code = body,
        .env = bind_env(bindings, args, op.closure.env),
        .args = VPOISON,
        .parent_idx = st->frame - stack_frames,
        .kind = op.tag == Tag_Macro ? Cont_MacroBody : Cont_Body,
    };
    unref_val(body);
    unref_val(bindings);
    unref_val(args);
    unref_val(operator);
    SETALLOCF(st, fr, "closure app");
    return false;
  case Tag_Ffi:
    ref_val(args);
    ref_val(operator);
    SETRET(st, op.ffi.f(args, op.ffi.userdata));
    unref_val(args);
    unref_val(operator);
    return true;
  case Tag_FfiEx: {
    ref_val(args);
    ref_val(operator);
    bool ret = op.ffi.fex(args, op.ffi.userdata, st);
    unref_val(args);
    unref_val(operator);
    return ret;
  }
  case Tag_FfiMacro: {
    SmallValue env = st->frame->env;
    ref_val(args);
    ref_val(operator);
    ref_val(env);
    SETRET(st, op.ffi.m(args, &env, op.ffi.userdata));
    if (env.p != st->frame->env.p) {
      Cont f = {
          .code = st->frame->code,
          .env = env,
          .args = st->frame->args,
          .parent_idx = st->frame->parent_idx,
          .kind = st->frame->kind,
      };
      SETALLOCF(st, f, "ffi macro app");
    }
    unref_val(env);
    unref_val(args);
    unref_val(operator);
    return true;
  }
  case Tag_FfiMacroEx: {
    ref_val(args);
    ref_val(operator);
    bool ret = op.ffi.mex(args, op.ffi.userdata, st);
    unref_val(args);
    unref_val(operator);
    return ret;
  }
  case Tag_Cont: {
    ref_val(args);
    ref_val(operator);
    SETF(st, op.cont);
    Value a = read_value(args);
    if (a.tag != Tag_Pair)
      panic("expected 1 argument to a continuation", args);
    if (a.pair.cdr.p != VNIL.p)
      panic("expected exactly 1 argument to a continuation", args);
    SETRET(st, a.pair.car);
    unref_val(args);
    unref_val(operator);
    return true;
  }
  default:
    panic("applying a non-function", cons(operator, args));
  }
}

// TODO: separate storage for immutable frames?
// either way some kind of incremental GC for them or similar
SmallValue eval(SmallValue code0, SmallValue env0) {
  Cont frame0 = {
      .code = code0,
      .env = env0,
      .args = VPOISON,
      .parent_idx = -1,
      .kind = Cont_Body,
  };
  State st = {
      NULL,
      VNIL,
  };
  SETALLOCF(&st, frame0, "init");
  while (st.frame) {
    DEBUG("a\n");
#ifdef _DEBUG
#define ITER_CONT(C, B)                                                        \
  {                                                                            \
    for (Cont *C = st.frame; C;                                                \
         C = C->parent_idx >= 0 ? &stack_frames[C->parent_idx] : NULL) {       \
      B;                                                                       \
    }                                                                          \
  }
#else
#define ITER_CONT(C, B)
#endif
    // ITER_CONT(cont, DEBUG(" ~~~~ %ld", cont - stack_frames));
    DEBUG("\ncode:");
    ITER_CONT(cont, DEBUG(" ~~~~ "); DBG(cont->code));
    DEBUG("\nenv:");
    ITER_CONT(cont, DEBUG(" ~~~~ "); DBG(cont->env));
    DEBUG("\nargs:");
    ITER_CONT(cont, DEBUG(" ~~~~ "); DBG(cont->args));
    DEBUG("\n");
    Value c = read_value(st.frame->code);
    Value a = read_value(st.frame->args);
    if (st.frame->kind == Cont_Expr && a.tag == Tag_Pair &&
        a.pair.cdr.p == VNIL.p) {
      // we are now evaluating a function's arguments. but if this is a macro,
      // we shouldn't evaluate it.
      Value f = read_value(a.pair.car);
      if (f.tag == Tag_Macro || f.tag == Tag_FfiMacro ||
          f.tag == Tag_FfiMacroEx) {
        DEBUG("?");
        if (c.tag != Tag_Pair && c.tag != Tag_Nil)
          panic("macro arguments are not a list", st.frame->code);
        DBG(st.frame->code);
        DEBUG(" applying to ");
        DBG(a.pair.car);
        DEBUG("\n");
        SmallValue code = st.frame->code;
        POPF(&st);
        SmallValue env_code = code;
        if (f.tag == Tag_Macro)
          env_code = cons(st.frame->env, env_code);
        bool returned = apply(&st, a.pair.car, env_code);
        DBG(st.ret);
        DEBUG("/frame%ld\n", st.frame - stack_frames);
        if (returned && st.frame && st.frame->kind == Cont_Expr) {
          frame0.code = st.frame->code;
          frame0.env = st.frame->env;
          frame0.args = cons(st.ret, st.frame->args);
          frame0.kind = st.frame->kind;
          DEBUG("pushing");
          DBG(frame0.args);
          DEBUG("\n");
          frame0.parent_idx = st.frame->parent_idx;
          SETALLOCF(&st, frame0, "macro application");
        }
        continue;
      }
    }
    if (c.tag == Tag_Nil) {
      DEBUG("n\n");
      // no more code, pop the stack frame and push ret to args
      // in function body: (a b c) means run a, run b, run c, set ret
      // in expression: (a b c) means run a, run b, run c, apply a to (b c),
      // push ret to parent's args if necessary
      bool returned = false;
      if (st.frame->kind == Cont_Body) {
        // we weren't in the midst of a call - we were just evaluating a body
        // expression by expression - we can just move on
        POPF(&st);
        returned = true;
      } else if (st.frame->kind == Cont_MacroBody) {
        // this was a macro, we need to set the env accordingly
        POPF(&st);
        returned = true;
        Value r = read_value(st.ret);
        if (r.tag != Tag_Pair)
          panic("macros must return (env . ret) pairs", st.ret);
        ref_val(r.pair.car);
        SETRET(&st, r.pair.cdr);
        if (r.pair.car.p != st.frame->env.p) {
          frame0 = *st.frame;
          frame0.env = r.pair.car;
          SETALLOCF(&st, frame0, "macro env ret");
        }
        unref_val(r.pair.car);
      } else {
        // we were evaluating something for a call, now we're done so call it
        // (which simply involves pushing a frame to the stack)
        // (except if it's a native function then just call it directly mhm)
        SmallValue a = reverse(st.frame->args);
        Value args = read_value(a);
        if (args.tag != Tag_Pair)
          panic("arguments must be a list", a);
        POPF(&st);
        DBG(a);
        DEBUG("\n");
        DEBUG("applying\n");
        ref_val(a);
        returned = apply(&st, args.pair.car, args.pair.cdr);
        unref_val(a);
      }
      if (returned && st.frame && st.frame->kind == Cont_Expr) {
        frame0.code = st.frame->code;
        frame0.env = st.frame->env;
        frame0.args = cons(st.ret, st.frame->args);
        frame0.parent_idx = st.frame->parent_idx;
        frame0.kind = st.frame->kind;
        DEBUG("pushing arg: ");
        DBG(frame0.args);
        DEBUG("\n");
        SETALLOCF(&st, frame0, "code ptr bump");
      }
    } else if (c.tag == Tag_Pair) {
      DEBUG("p\n");
      // some code is still remaining in this expression or function body
      // push it
      Value car = read_value(c.pair.car);
      // the next frame will move forward by one expression
      frame0.code = c.pair.cdr;
      frame0.env = st.frame->env;
      frame0.args = st.frame->args;
      frame0.parent_idx = st.frame->parent_idx;
      frame0.kind = st.frame->kind;
      if (car.tag == Tag_Pair) {
        // this is a call
        SETALLOCF(&st, frame0, "code ptr bump");
        frame0.code = c.pair.car;
        frame0.env = st.frame->env;
        frame0.args = VNIL;
        frame0.parent_idx = st.frame - stack_frames;
        frame0.kind = Cont_Expr;
        SETALLOCF(&st, frame0, "nested call");
      } else {
        // this is not a call, simply set ret
        if (car.tag == Tag_Sym) {
          for (Value e = read_value(st.frame->env); e.tag != Tag_Nil;
               e = read_value(e.pair.cdr)) {
            Value car = read_value(e.pair.car);
            if (car.pair.car.p == c.pair.car.p) {
              SETRET(&st, car.pair.cdr);
              goto DONE;
            }
          }
          panic("unbound identifier", c.pair.car);
        } else {
          SETRET(&st, c.pair.car);
        }
      DONE:
        if (frame0.kind == Cont_Expr) {
          frame0.args = cons(st.ret, frame0.args);
        }
        SETALLOCF(&st, frame0, "code ptr bump");
      }
    } else {
      panic("function code is not a list", st.frame->code);
    }
  }
  return st.ret;
}

void dbgprint(SmallValue value) {
  Value val = read_value(value);
  switch (val.tag) {
  case Tag_Poison:
    printf("<unallocated cell@%p>", value.p);
    break;
  case Tag_Nil:
    printf("()");
    break;
  case Tag_False:
    printf("false");
    break;
  case Tag_True:
    printf("true");
    break;
  case Tag_Cont:
    printf("<continuation>");
    break;
  case Tag_Ffi:
  case Tag_FfiEx:
    printf("<ffi>");
    break;
  case Tag_FfiMacro:
  case Tag_FfiMacroEx:
    printf("<ffi-macro>");
    break;
  case Tag_Closure:
  case Tag_Macro: {
    if (val.tag == Tag_Closure)
      printf("(lambda ");
    else
      printf("(macro ");
    dbgprint(val.closure.code);
    printf(")");
    break;
  }
  case Tag_Int:
    printf("%lld", val.i.n);
    break;
  case Tag_Pair: {
    printf("(");
    while (true) {
      dbgprint(val.pair.car);
      if (val.pair.cdr.p == VNIL.p)
        break;
      Value cdr = read_value(val.pair.cdr);
      if (cdr.tag == Tag_Pair) {
        printf(" ");
        val = cdr;
        continue;
      }
      printf(" . ");
      dbgprint(val.pair.cdr);
      break;
    }
    printf(")");
    break;
  }
  case Tag_Sym:
    printf("'");
    for (int i = 0; i < val.sym->sym.n; ++i)
      printf("%c", val.sym->sym.p[i]);
    break;
  case Tag_Str:
    printf("\"");
    for (int i = 0; i < val.str.n; ++i)
      printf("%c", val.str.p[i]);
    printf("\"");
    break;
  case Tag_Userdata:
    printf("<userdata>");
    break;
  }
}

SmallValue lambda_ffi(SmallValue args, SmallValue *env, SmallValue _userdata) {
  UNUSED(_userdata);
  Value val = {Tag_Closure, .closure = {.code = args, .env = *env}};
  return alloc_value(val);
}

SmallValue macro_fi(SmallValue args, SmallValue *env, SmallValue _userdata) {
  UNUSED(_userdata);
  DEBUG("mkmacro ");
  DBG(args);
  DEBUG(" ~~~ ");
  DBG(*env);
  DEBUG("\n");
  Value val = {Tag_Macro, .closure = {.code = args, .env = *env}};
  return alloc_value(val);
}

SmallValue quote_ffi(SmallValue args, SmallValue *env, SmallValue _userdata) {
  UNUSED(_userdata);
  UNUSED(env);
  READ1(quote, args, a);
  return a;
}

bool define_ffi(SmallValue args, SmallValue _userdata, State *state) {
  UNUSED(_userdata);
  Value data = read_value(args);
  if (data.tag != Tag_Pair)
    panic("define not passed enough arguments", args);
  if (state->frame->kind != Cont_Body && state->frame->kind != Cont_MacroBody)
    panic("defines can't be used as a function argument", args);
  Value binding = read_value(data.pair.car);
  if (binding.tag == Tag_Sym) {
    Value val = {Tag_Closure, .closure = {.code = cons(VNIL, data.pair.cdr),
                                          .env = state->frame->env}};
    SmallValue computation = alloc_value(val);
    ref_val(computation);
    SmallValue a = cons(data.pair.car, VNIL);
    ref_val(a);
    val.closure.code = cons(a, state->frame->code);
    unref_val(a);
    val.closure.env = state->frame->env;
    SmallValue body = alloc_value(val);
    ref_val(body);
    unref_val(computation);
    SmallValue code =
        cons(cons(body, cons(cons(computation, VNIL), VNIL)), VNIL);
    unref_val(body);
    // ((lambda (name) (rest)) (lambda () body))
    // (body computation)
    Cont frame0 = {
        .code = code,
        .env = state->frame->env,
        .args = state->frame->args,
        .parent_idx = state->frame->parent_idx,
        .kind = state->frame->kind,
    };
    ref_val(frame0.code);
    ref_val(frame0.env);
    PREPARE_CALL(state);
    unref_val(frame0.code);
    unref_val(frame0.env);
    SETALLOCF(state, frame0, "define");
    return false;
  } else if (binding.tag == Tag_Pair) {
    // potentially self-referential function
    SmallValue args = binding.pair.cdr;
    Value b = read_value(binding.pair.car);
    // SmallValue code = data.pair.cdr;
    if (b.tag != Tag_Sym)
      panic("define expects function name to be a symbol", binding.pair.car);

    Value code = {Tag_Pair, .pair = {args, data.pair.cdr}};
    Value val = {Tag_Closure, .closure = {.code = alloc_value(code),
                                          .env = state->frame->env}};
    SmallValue ret = alloc_value(val);
    SmallValue env = state->frame->env;
    PUSH(env, cons(binding.pair.car, ret));
    // mutation is fine here since we just created it
    ((Value *)ret.p)->closure.env = env;
    Cont frame0 = {
        .code = state->frame->code,
        .env = env,
        .args = state->frame->args,
        .parent_idx = state->frame->parent_idx,
        .kind = state->frame->kind,
    };
    SETALLOCF(state, frame0, "define (lambda)");
    return false;
  } else {
    panic("define passed non-symbol, non-list binding", args);
  }
}

bool if_ffi_2(SmallValue args, SmallValue userdata, State *state) {
  Value u = read_value(userdata);
  if (u.tag != Tag_Pair)
    panic("if: internal error", userdata);
  READ1(if - internal, args, val);
  Cont frame0 = {
      .code = (val.p == VBOOL[false].p) ? cons(u.pair.cdr, VNIL)
                                        : cons(u.pair.car, VNIL),
      .env = state->frame->env,
      .args = VPOISON,
      .parent_idx = state->frame - stack_frames,
      .kind = Cont_Body,
  };
  PREPARE_CALL(state);
  SETALLOCF(state, frame0, "if");
  return false;
}

bool if_ffi(SmallValue args, SmallValue _userdata, State *state) {
  UNUSED(_userdata);
  READ3(if, args, cond, yes, no);
  Value next = {Tag_FfiEx, .ffi = {.fex = if_ffi_2, .userdata = cons(yes, no)}};
  SmallValue n = alloc_value(next);
  SmallValue env = state->frame->env;
  ref_val(n);
  Cont frame0 = {
      .code = cons(cons(n, cons(cond, VNIL)), VNIL),
      .env = env,
      .args = VPOISON,
      .parent_idx = state->frame - stack_frames,
      .kind = Cont_Body,
  };
  unref_val(n);
  ref_val(frame0.code);
  ref_val(env);
  PREPARE_CALL(state);
  unref_val(frame0.code);
  unref_val(env);
  SETALLOCF(state, frame0, "if");
  return false;
}

bool eval_ffi(SmallValue args, SmallValue _userdata, State *state) {
  UNUSED(_userdata);
  Value env_code = read_value(args);
  if (env_code.tag != Tag_Pair)
    panic("expected env and code as args", args);
  Cont frame0 = {
      .code = env_code.pair.cdr,
      .env = env_code.pair.car,
      .args = VPOISON,
      .parent_idx = state->frame - stack_frames,
      .kind = Cont_Body,
  };
  PREPARE_CALL(state);
  SETALLOCF(state, frame0, "eval");
  return false;
}

bool apply_ffi(SmallValue args, SmallValue _userdata, State *state) {
  UNUSED(_userdata);
  READ2(apply, args, f, a);
  return apply(state, f, a);
}

bool call_cc_ffi(SmallValue args, SmallValue _userdata, State *state) {
  UNUSED(_userdata);
  READ1(call_cc, args, f);
  Value val = {Tag_Cont, .cont = state->frame};
  return apply(state, f, cons(alloc_value(val), VNIL));
}

SmallValue cons_ffi(SmallValue args, SmallValue _userdata) {
  UNUSED(_userdata);
  READ2(cons, args, car, cdr);
  return cons(car, cdr);
}

SmallValue car_ffi(SmallValue args, SmallValue _userdata) {
  UNUSED(_userdata);
  READ1(car, args, x);
  Value v = read_value(x);
  if (v.tag != Tag_Pair)
    panic("car expected a pair", x);
  return v.pair.car;
}

SmallValue cdr_ffi(SmallValue args, SmallValue _userdata) {
  UNUSED(_userdata);
  READ1(cdr, args, x);
  Value v = read_value(x);
  if (v.tag != Tag_Pair)
    panic("cdr expected a pair", x);
  return v.pair.cdr;
}

SmallValue printn_ffi(SmallValue args, SmallValue _userdata) {
  UNUSED(_userdata);
  READ1(cdr, args, x);
  dbgprint(x);
  printf("\n");
  return VNIL;
}

SmallValue intp_ffi(SmallValue args, SmallValue _userdata) {
  UNUSED(_userdata);
  READ1(int?, args, x);
  return VBOOL[read_value(x).tag == Tag_Int];
}

SmallValue default_env() {
  SmallValue env = VNIL;
#define ADD_BUILTIN(K, V, T, F)                                                \
  {                                                                            \
    Value val;                                                                 \
    val.tag = T;                                                               \
    val.ffi.userdata.p = NULL;                                                 \
    val.ffi.F = (V);                                                           \
    PUSH(env, cons(symbols[K].boxed, alloc_value(val)));                       \
  }
#define ADD_MACRO(K, V) ADD_BUILTIN(K, V, Tag_FfiMacro, m)
#define ADD_FUNC(K, V) ADD_BUILTIN(K, V, Tag_Ffi, f)
#define ADD_MACRO_EX(K, V) ADD_BUILTIN(K, V, Tag_FfiMacroEx, mex)
#define ADD_FUNC_EX(K, V) ADD_BUILTIN(K, V, Tag_FfiEx, fex)
  ADD_MACRO(Sym_Lambda, lambda_ffi);
  ADD_MACRO(Sym_Macro, macro_fi);
  ADD_MACRO_EX(Sym_Define, define_ffi);
  ADD_MACRO(Sym_Quote, quote_ffi);
  ADD_MACRO_EX(Sym_If, if_ffi);
  ADD_FUNC_EX(Sym_Eval, eval_ffi);
  ADD_FUNC_EX(Sym_Apply, apply_ffi);
  ADD_FUNC_EX(Sym_CallCc, call_cc_ffi);
  ADD_FUNC(Sym_Cons, cons_ffi);
  ADD_FUNC(Sym_Car, car_ffi);
  ADD_FUNC(Sym_Cdr, cdr_ffi);
  ADD_FUNC(Sym_Add, add_ffi);
  ADD_FUNC(Sym_Mul, mul_ffi);
  ADD_FUNC(Sym_Sub, sub_ffi);
  ADD_FUNC(Sym_Div, div_ffi);
  ADD_FUNC(Sym_Lt, lt_ffi);
  ADD_FUNC(Sym_Le, le_ffi);
  ADD_FUNC(Sym_Gt, gt_ffi);
  ADD_FUNC(Sym_Ge, ge_ffi);
  ADD_FUNC(Sym_Eq, eq_ffi);
  ADD_FUNC(Sym_Ne, ne_ffi);
  ADD_FUNC(Sym_IntP, intp_ffi);
  ADD_FUNC(Sym_Printn, printn_ffi);
  PUSH(env, cons(symbols[Sym_Nil].boxed, VNIL));
  PUSH(env, cons(symbols[Sym_False].boxed, VBOOL[false]));
  PUSH(env, cons(symbols[Sym_True].boxed, VBOOL[true]));
  return env;
}

int main() {
  init();
  // const char *code = "(define define (macro (env code) (cons env code))) (d x
  // 5) x"; const char *code = "(define (run n) (if (> n 4096) n (run (+ n 1))))
  // (run 0)";
  // const char *code = "(define (fib n) (if (< n 2) n (+ (fib (- n 1)) (fib (-
  // n "
  //                   "2))))) (fib 30)";
  // const char *code = "(define def (macro (env name code)
  // ((lambda (c) (cons (cons (cons name c) env) c)) (eval env code)))) (define
  // (x) (def a 5)) (x) a";
  // const char *code = "(define (x x) (if (< x 5) (define x 5) 456) x) (x 3)";
  // const char *code = "(define x 5) x";
  // const char *code = "((lambda (x) (if (int? x) (print! x) (x 5))) (call/cc
  // (lambda (x) x)))";
  const char *code =
      "(define x (call/cc (lambda (x) x))) (if (int? x) (print! x) (x 5))";
  // const char *code = "((lambda (x) (if (int? x) (print! x) (print! x))) 5)";
  SmallValue parsed = parse_list(&code);
  ref_val(parsed);
  SmallValue env = default_env();
  unref_val(parsed);
  // dbgprint(env);
  // return 0;
  dbgprint(eval(parsed, env));
  DEBUG("\n");
}
