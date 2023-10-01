# Lisp

A [Lisp](https://en.wikipedia.org/wiki/Lisp_(programming_language)) to Sigma VM bytecode compiler.

The compiler reads Lisp program from a file or standard input, parses it into ASTs, generates [A-normal form (ANF)](https://en.wikipedia.org/wiki/A-normal_form) intermediate representations of the input program, and finally generates Sigma VM bytecode from ANFs.

## Usage

First compile built-in functions:

```
cargo run --bin lisp -- lisp/lib/builtins.sbas -o builtins.sbc
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
