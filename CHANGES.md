# v1.1.0rc

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
- [ldl2re] fix incorrect handling of the "last" non-propositional formula (@0368e67)

# v1.0.0 (2018-07-31)

initial public release.
