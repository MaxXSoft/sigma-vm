# Lisp

A [Lisp](https://en.wikipedia.org/wiki/Lisp_(programming_language)) to Sigma VM bytecode compiler.

The compiler reads Lisp program from a file or standard input, parses it into ASTs, generates [A-normal form (ANF)](https://en.wikipedia.org/wiki/A-normal_form) intermediate representations of the input program, and finally generates Sigma VM bytecode from ANFs.

## Usage

First compile built-in functions:

```
cargo run --bin lisp -- -p lisp/lib/builtins.sbas -o builtins.sbc
```

Then compile a Lisp program:

```
cargo run --bin lisp -- lisp/examples/fib.sbas -o fib.sbc
```

And run the compiled program with `sigma` (enable release build for speed):

```
cargo run --bin sigma -r -- fib.sbc
```

Or compile and run the program with a single command:

```
cargo run --bin lisp -- lisp/examples/fib.sbas | cargo run --bin sigma -r
```

When running the program, Sigma VM will load the built-ins from `builtins.sbc`, so make sure that `builtins.sbc` is located in the current working directory. You can also specify the library search path by running:

```
cargo run --bin sigma -r -- -L path/contains/builtins fib.sbc
```

## Examples

There are some example programs in [`examples`](examples) directory:

* [`fib.lisp`](examples/fib.lisp): a program that calculates the first 21 terms of Fibonacci series.
* [`lisp.lisp`](examples/lisp.lisp): a Lisp interpreter written in Lisp.

## Supported Syntax and Built-ins

* Floating point numbers, symbols, strings, lists.
* `(define var value)`: defines a new variable.
* `(require "module" (sym1 sym2 ...))`: imports symbols from another module.
* `(provide sym1 sym2 ...)`: exports symbols defined in the current module.
* `(lambda (p1 p2 ...) ...)`: creates a closure (function object).
* `(f a1 a2 ...)`: calls a function.
* `(quote ...)` or `'...`: quotes a value.
* `(cond (c1 v1) (c2 v2) ... ('t else))`: select value by conditions.
* `(atom? v)`: check if value is an atom (i.e. not a list).
* `(number? v)`: check if value is a number.
* `(eq? v1 v2)`: check if two values are equal.
* `(car l)`: gets the first element of the given list.
* `(cdr l)`: gets the rest elements of the given list.
* `(cons v l)`: inserts the given value at the beginning of the list.
* `(list v1 v2 ...)`: creates a list by the given values.
* Arithmetic/logical operations: `(+ n1 n2)`, `(- ...)`, `(* ...)`, `(/ ...)`, `(> ...)`, `(< ...)`, `(>= ...)`, `(<= ...)` and `(= ...)`.
* `(print v)`: prints the given value for debugging and then returns it.
