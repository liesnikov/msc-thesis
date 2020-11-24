# Extending and Automating Iris Proof Mode with Ltac2

This contains Coq development Bohdan Liesnikov's Master's thesis.

## File description

* `utils.v` -- miscellaneous Ltac2 functions and notations. Evar management library.
* `ltac2_tactics.v` -- Ltac2 tactics for regular MoSeL.
* `imatch.v` -- `iMatch` for regular MoSeL
* `tauto_solver.v` -- naïve brute-force solver for regular MoSeL
* `test.v` -- examples of usage for tactics, `iMatch` and the solver

* `splitting/named_prop.v` -- entailment predicate with Boolean expressions
* `splitting/named_prop_notation.v` -- notation definitions for it
* `splitting/connection.v` -- connection lemma between regular MoSeL entailment and the new one
* `splitting/splitting_tactics.v` -- Coq tactics for the new entailment predicate
* `splitting/splitting_ltac2_tactics.v` -- Ltac2 tactics for the entailment predicate
* `splitting/splitting_imatch.v` -- iMatch for the entailment predicate
* `splitting/tactics.v` -- wrapper module for easy import

* `splitting/isolver.v` -- solver from Chapter 6
* `splitting/heaplang.v` -- Coq lemmas for heaplang (no Ltac2 tactics)

* `splitting/test_imatch.v`, `splitting/test.v` -- examples of usage for tactics, `iMatch` and the solver


## Build instructions

This was tested with Coq 8.11.1, iris version `dev.2020-04-09.0.272f29d3` and coq-stdpp `dev.2020-04-03.1.eeef6250`.

To get development environment use the following commands:

Create a new switch
```
$ opam switch create . 4.07.1
$ eval $(opam env)
```

Add relevant repositories
```
$ opam repo add coq-released https://coq.inria.fr/opam/released
$ opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
```
Install right version of the packages
```
$ opam install coq.8.11.1
$ opam install coq-iris.dev.2020-04-09.0.272f29d3
$ opam install coq-iris-string-ident
```

Build the files
```
$ unzip archive.zip -d coq
$ cd coq
$ coq_makefile -f _CoqProject -o Makefile
$ make
$ cd splitting
$ coq_makefile -f _CoqProject -o Makefile
$ make
```
