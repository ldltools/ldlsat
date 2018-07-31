# Summary

[*ldlsat*](https://github.com/ldltools/ldlsat) is a SAT solver for
[LDL](https://www.cs.rice.edu/~vardi/).

For each input LDL formula,
ldlsat first translates it to
[MSO](https://en.wikipedia.org/wiki/Monadic_second-order_logic),
and then passes the generated (equivalent) MSO formula
to the [mona](http://www.brics.dk/mona/) tool for solving its satisfiability.

# Examples

&ensp; (to be filled in)

# Installation on Debian/Ubuntu
## Prerequisites
- [ocaml](https://ocaml.org) (v4.05 or higher. tested with 4.06.1)  
  run: `apt-get install ocaml`  
  Alternatively, you can install a particular version of the compiler using opam  
  run: `opam switch 4.06.1` for example
- [opam](https://opam.ocaml.org) (ocaml package manager)  
  run: `apt-get install opam`
- ocaml packages: ocamlfind, yojson, ppx\_deriving, ppx\_deriving\_yojson  
  for each of these packages,  
  run: `opam install package`
- [mona](http://www.brics.dk/mona/) (v1.4)  
  run: `wget http://www.brics.dk/mona/download/mona-1.4-17.tar.gz`  
  expand the archive, and build/install the tool as is instructed.
- [graphviz](http://www.graphviz.org/) (optional)  
  run: `apt-get install graphviz`

## Build
- run `make && make install` in the top directory  
  Tools including `ldlsat` will be built and installed into `/usr/local/bin`.  
  To change the installation directory,
  run `make PREFIX=<prefix> install` instead (default: `PREFIX=/usr/local`).

# Installation on Darwin
In addition to the tools listed above, you also need the following:

- GNU common utilities  
  run: `brew install coreutils debianutils`
- GNU sed/awk  
  run: `brew install gnu-sed gawk`
- GNU make (v4.1 or higher)  
  run: `brew install remake`

# Testing
- run: `make -C tests dfa`  
  DFA files generated from test cases in LDL will appear in `tests/out`
