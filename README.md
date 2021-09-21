## Overview

`func-DRAT` is the product of my [Bachelor's thesis](https://github.com/mckirk/func-drat/blob/master/thesis/thesis.pdf) at the chair for Logic and Verification at TU Munich.
It is essentially an DRAT-proof checker similar to [DRAT-trim](https://github.com/marijnheule/drat-trim), but written in OCaml.
DRAT proofs can be emitted by SAT solvers to certify that a propositional formula is unsatisfiable.
For details on unsatisfiability proofs and the DRAT proof format, consult the [accompanying thesis](https://github.com/mckirk/func-drat/blob/master/thesis/thesis.pdf) or [DRAT-trim's documentation](https://github.com/marijnheule/drat-trim).

The main motivation behind implementing a DRAT-proof checker in a functional programming language was to create the basis for a formally verified checker that was intended to be developed later.

Development moved in a different direction, however:
Instead of leading to a formally verified DRAT checker, the optimizations found during development of `func-DRAT` were incorporated into the [GRAT suite](https://www21.in.tum.de/~lammich/grat/), which consists of the unverified `GRATgen` (converting DRAT proofs to an easier-to-check GRAT form) and the verified `GRATchk`, which checks the resulting GRAT-proofs' validity.

---

## Getting Started

`func-DRAT` requires the `batteries` and `cppo` packages, which can be installed with
```
opam install batteries cppo
```

Afterwards, `func-DRAT` can be built (with all optimizations) using
```
make opt
```

To check a DRAT proof for a given formula, use

```
funcdrat formula.cnf --proof=formula.drat
```

---

## Usage

```
funcdrat cnf [options]

  options:

    -h, --help            show this help message and exit
    -pSTR, --proof=STR    Path to proof file (defaults to [cnf_name].drat)
    -wSTR, --whole=STR    Write all clauses and lemmas into given file after
                          parsing
    -cSTR, --core=STR     Write core clauses into given file
    -lSTR, --lemmas=STR   Write proof core into given file
    --core-deletions      Skip deletions of non-core clauses in proof core
    -rFLOAT, --report=FLOAT
                          Report progress every n seconds
```

---

## Building

`func-DRAT` was originally developed on and benchmarked against version `4.04.1+flambda` of the OCaml compiler.
It was confirmed to also work on a newer version, such as `4.12.0`, where building looks as follows:

```
opam switch create 4.12.0+flambda --package=ocaml-variants.4.12.0+options,ocaml-option-flambda
eval $(opam env)
opam install batteries cppo

make opt
```

---

## Make Targets

- `opt`:
    with flambda and unboxed-types optimizations
- `noinl`:
    no inlining, for better readability of assembly code for analysis
- `verb`:
    additional verbose output during proof checking
- `asserts`:
    check assertions during execution
- `bt`:
    output a backtrace following an exception
- `deb`:
    debugging target with asserts, backtraces and verbose/debug information

Note: When switching targets, it is generally necessary to issue a `make clean` beforehand, to make sure code gets recompiled even if it only changes thanks to a precompiler flag.