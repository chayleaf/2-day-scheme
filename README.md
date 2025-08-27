# 2 day Scheme

A minimal Scheme interpreter with first class macros, tail recursion optimization and call/cc support that
I made in two days (lacking most builtins you'd normally find in a Scheme) as my first ever Lisp.
It doesn't use malloc, instead it allocates in a 4096 cell arena, garbage collecting every time it goes through
all 4096 cells.

Performance is fairly optimal for what the interpreter is doing - about half of the runtime is spent looking up
names in linked list environments, and about 30% is spent reversing argument lists (which have to be built
in evaluation order and then reversed to get into the format the function expects).

Any kind of analysis for optimizing environments would be complicated because of first class macros
(e.g. you can do `(define d define) (d x 5)`). That said, you could get a lot of performance back by creating
fast paths for functions with known arities (so you don't have to build the argument list). I think the current
implementation is perfect due to its simplicity.

Macros can be defined in either C code or in Scheme itself (using `macro` instead of `lambda`, accepting
an additional `env` argument as the first argument, and returning a pair of env and value). `apply` and `eval`
functions are both available. All builtins should natively support continuations.
