# v1.0.4 (2019-03-15)

- [ldlsat] pack all ocaml modules into "Ldlsat" for modularity
- [ldlsat] support DIMACS CNF
- [toysat] add a new simple SAT solver, called toysat
  - DPLL w/o any smart heuristics
  - support DIMACS CNF for reading/writing propositional formulas
  - note: "ldlsimp --sat" now uses toysat, while ldlsat remains fully relying on mona

# v1.0.3 (2018-11-30)

- [ldlmc] support reachability checking (`ldlmc --reachability`)
- add man pages for ldlsat/ldlmc

## fix
- [ldlsimp] resolve (@0d72177)  
  simp\_uniq and simp\_equiv in ldlsimp.ml now correctly simplify formulas
  in a recursive-descent manner.  
  (note these remain inefficient and need further improvement.)

# v1.0.2 (2018-10-01)

- add grammar in svg/html into docs/grammar
- add Dockerfile

## fix
- [ldl2re] fix incorrect handling of the _"last"_ modal formula (@0368e67)

# v1.0.0 (2018-07-31)

initial public release.
