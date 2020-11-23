This was tested with Coq 8.11.1, iris version `dev.2020-04-09.0.272f29d3` and coq-stdpp `dev.2020-04-03.1.eeef6250`.


# Build instructions

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
