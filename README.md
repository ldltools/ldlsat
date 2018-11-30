# Summary

[*ldlsat*](https://github.com/ldltools/ldlsat) is a SAT solver for
[LDL<sub>f</sub>](https://www.cs.rice.edu/~vardi/),
an extension of [LTL](https://en.wikipedia.org/wiki/Linear_temporal_logic).

For each input LDL<sub>f</sub> formula,
_ldlsat_ first translates it to
[MSO](https://en.wikipedia.org/wiki/Monadic_second-order_logic),
and then passes the generated (equivalent) MSO formula
to the [mona](http://www.brics.dk/mona/) tool for solving its satisfiability.

# Examples

## Propositional

<pre>
<code>
$ echo 'a & (a -> b) -> b' | ldlsat
valid
$ echo 'a & !a' | ldlsat
unsatisfiable
</code>
</pre>

## LTL / Modal

<pre>
<code>
$ echo '[{true}*]a -> a' | ldlsat
valid
$ echo '[{true}](a -> b) -> [{true}]a -> [{true}]b' | ldlsat  ## distribution (K)
valid
$ echo '[{true}]a -> a' | ldlsat  ## reflexitivity (T)
satisfiable
$ echo 'a -> [{true}]<{true}>a' | ldlsat  ## symmetry (B)
satisfiable
</code>
</pre>

Note

- [] and <> in LTL are equivalent with [{true}\*] and <{true}\*> in LDL, respectively.
- [] and <> in standard propositional modal logics correspond with [{true}] and <{true}> in LDL, respectively.

## LDL<sub>f</sub>

<pre>
<code>
$ echo '<{a}*>a -> a' | ldlsat
valid
$ echo '<{a & !b}; {!a & b}>(a & last) -> [{a}*; {b}]last' | ldlsat
valid
$ echo '<{a}; {!b}>last & [{a}]b' | ldlsat
unsatisfiable
</code>
</pre>

Note that formulas should conform to [this grammar](docs/README.md).

# Installation on Docker

- run `docker build -t ldltools/ldlsat .` in the top directory

# Installation on Debian/Ubuntu
## Prerequisites
- [ocaml](https://ocaml.org) (v4.05 or higher. tested with 4.07.0)  
  run: `apt-get install ocaml`  
  Alternatively, you can install a particular version of the compiler using opam  
  run: `opam switch 4.07.0` for example
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

# Installation on macOS (Darwin)
In addition to the tools listed above, you also need the following:

- GNU common utilities  
  run: `brew install coreutils debianutils`
- GNU sed/awk  
  run: `brew install gnu-sed gawk`
- GNU make (v4.1 or higher)  
  run: `brew install remake`  
  and build with `MAKE=remake remake` instead of `make` 

# Testing
- run: `make -C tests test`  
  run unit tests
- run: `make -C tests dfa`  
  generate DFA files from various LDL<sub>f</sub> formulas into `tests/out`
