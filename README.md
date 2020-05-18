# The correctness of the library Printer Сombinators with Сhoice

## About
Here is the proof of the library correctness printer combinators with choice with Pareto filtering optimisation. The proof is relative to the base implementation.
## Building the Project

### Requirements
* [Coq 8.9.1](https://coq.inria.fr)
* [Hahn library](https://github.com/vafeiadis/hahn) (`coq-hahn`)

### Building Manually

To build the project, one needs to install `hahn` library, which the project
depends on. This might be done by running
```
opam remote add coq-weakmemory-local -k git https://github.com/weakmemory/local-coq-opam-archive
opam install coq-hahn
```
After that, one needs to run `make`.

## Description of code
  - *FuncCorrect.v*—correctness of combinators and layouts.
  - *IsLess.v*— partial order properties.
  - *ListEqTrivalProof.v*—relationship of the minimum height with the context lemma.
  - *MinHeight.v*— properties of the Pareto set and proof of the correctness of the library.
