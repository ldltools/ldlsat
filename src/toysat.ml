(*
 * (C) Copyright IBM Corp. 2019.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *)

open Ldl

(* ================================================================================
   common predicates
   ================================================================================
 *)

(* literal = atomic formula or its negation *)
let rec literal_p = function
  | Ldl_atomic "last" -> false
  | Ldl_atomic _ -> true
  | Ldl_neg f -> literal_p f
  | Ldl_conj [] | Ldl_disj [] -> true
  | _ -> false

(* clause? *)
let rec clause_p (c : formula) =
  (* examine if c is a disjunction of literals *)
  match c with
  | _ when literal_p c -> true
  | Ldl_conj [] -> true
  | Ldl_disj disj ->
      (match List.find_opt (fun f -> not (literal_p f)) disj with None -> true | Some _ -> false)
  | _ -> false

(* no modality? *)
let rec propositional_p f =
  match f with
  | _ when literal_p f -> true
  | Ldl_neg g -> propositional_p g
  | Ldl_conj gs | Ldl_disj gs ->
      (match List.find_opt (fun g -> not (propositional_p g)) gs with None -> true | Some _ -> false)
  | Ldl_impl (g1, g2) -> (propositional_p g1) && (propositional_p g2)

  | Ldl_atomic "last" -> false
  | Ldl_modal _ -> false
  | _ -> false

(** cnf_p/dnf_p -- harmless nestings are permitted *)

let rec cnf_p f =
  cnf_p_helper 1 f

and cnf_p_helper k f =
  match f with
  | _ when literal_p f -> true
  | Ldl_neg _ -> false

  | Ldl_conj [] -> true
  | Ldl_conj gs ->
      (match List.find_opt (fun g -> not (cnf_p_helper k g)) gs with
      |	None -> true
      | Some _ -> false)

  | Ldl_disj [] -> true
  | Ldl_disj _ when k = 0 -> false
  | Ldl_disj _ when k = 1 -> dnf_p_helper 0 f

  | Ldl_impl _ -> false
	(* should not appear *)
  | Ldl_modal _ ->
      invalid_arg @@ "[cnf_p_helper] " ^ string_of_formula f

and dnf_p f =
  dnf_p_helper 1 f

and dnf_p_helper k f =
  match f with
  | _ when literal_p f -> true
  | Ldl_neg _ -> false

  | Ldl_disj [] -> true
  | Ldl_disj gs ->
      (match List.find_opt (fun g -> not (dnf_p_helper k g)) gs with
      |	None -> true
      | Some _ -> false)

  | Ldl_conj [] -> true
  | Ldl_conj _ when k = 0 -> false
  | Ldl_conj _ when k = 1 -> cnf_p_helper 0 f

  | Ldl_impl _ -> false
	(* should not appear *)
  | Ldl_modal _ ->
      invalid_arg @@ "[dnf_p_helper] " ^ string_of_formula f

(* ================================================================================
   helpers
   ================================================================================
 *)

(* note:
   when f includes negation(s),
   `canonicalize_literal f` strictly reduces the number of negations.
*)
let rec canonicalize_literal f =
  assert (literal_p f);
  match f with
  | Ldl_atomic _ -> f
  | Ldl_conj [] -> Ldl_atomic "true"
  | Ldl_disj [] -> Ldl_atomic "false"
  | Ldl_neg (Ldl_neg g) -> canonicalize_literal g
  | Ldl_neg (Ldl_atomic "true") -> Ldl_atomic "false"
  | Ldl_neg (Ldl_atomic "false") -> Ldl_atomic "true"
  | Ldl_neg (Ldl_atomic _) -> f
  | Ldl_neg g -> canonicalize_literal (Ldl_neg (canonicalize_literal g))
  | _ -> invalid_arg @@ "[canonicalize_literal] " ^ string_of_formula f

(* literal -> (name, polarity) *)
let rec expose_literal f =
  assert (literal_p f);
  expose_literal_rec 1 f

and expose_literal_rec sign f =
  assert (abs sign = 1);
  match f with
  | Ldl_atomic p -> p, sign
  | Ldl_neg (Ldl_atomic p) -> p, - sign
  | Ldl_conj [] -> "true", sign
  | Ldl_disj [] -> "false", - sign
  | _ -> expose_literal_rec sign @@ canonicalize_literal f

let rec canonicalize_clause c =
  assert (clause_p c);
  let literals =
    match c with
    | _ when literal_p c -> [c]
    | Ldl_disj disj -> disj
    | _ -> invalid_arg @@ "[canonicalize_clause] " ^ string_of_formula c
  in let literals' =
    try
      List.fold_left
	(fun rslt l ->
	  assert (literal_p l);
	  let l = canonicalize_literal l in
	  match l with
	  | Ldl_atomic "true" -> raise Exit
	  | Ldl_atomic "false" -> rslt
	  | _ -> rslt @ [l])
	[] literals
    with Exit -> [Ldl_atomic "true"]
  in let c' =
    match literals' with
    | [] -> Ldl_atomic "false"
    | [l] -> l
    | _ -> Ldl_disj literals'
  in c'

(* flatten *)

let rec flatten f =
  match f with
  | Ldl_atomic _ -> f
  | Ldl_neg g -> Ldl_neg (flatten g)
  | Ldl_conj fs ->
      let fs' = flatten_conj (List.map flatten fs) in
      if List.length fs' = 1 then List.hd fs' else Ldl_conj fs'
  | Ldl_disj fs ->
      let fs' = flatten_disj (List.map flatten fs) in
      if List.length fs' = 1 then List.hd fs' else Ldl_disj fs'
  | Ldl_impl (f', g) -> Ldl_impl ((flatten f'), flatten g)
  | _ -> invalid_arg @@ "[flatten] " ^ string_of_formula f

(* f1 ∧ f2 ∧ ... -> f1' ∧ f2' ∧ ...
   ** non-recursive
 *)
and flatten_conj (fs : formula list) =
  List.fold_left
    (fun rslt f -> match f with Ldl_conj fs' -> rslt @ fs' | _ -> rslt @ [f])
    [] fs

(* ** non-recursive *)
and flatten_disj (fs : formula list) =
  List.fold_left
    (fun rslt f -> match f with Ldl_disj fs' -> rslt @ fs' | _ -> rslt @ [f])
    [] fs

(* find variables in clauses *)
let rec find_variables clauses =
  List.fold_left find_variables_rec [] clauses |> List.sort compare

and find_variables_rec rslt f =
  assert (propositional_p f);
  match f with
  | Ldl_atomic "true" | Ldl_atomic "false" -> rslt
  | Ldl_atomic x when not (List.mem x rslt) -> rslt @ [x]
  | Ldl_neg g -> find_variables_rec rslt g
  | Ldl_conj gs | Ldl_disj gs ->
      List.fold_left (fun rslt g -> find_variables_rec rslt g) rslt gs
  | Ldl_impl (g1, g2) ->
      List.fold_left (fun rslt g -> find_variables_rec rslt g) rslt [g1; g2]
  | _ -> rslt

(* ================================================================================
   tseitin (equi-satisfiable)
   ================================================================================
 *)

let rec tseitin ?(prefix = "__aux") f =
  let f = flatten f in
  assert (propositional_p f);
  if cnf_p f then match f with Ldl_conj (g :: gs) -> g :: gs | _ -> [f] else
  let (alist : (string option * formula) list), _ =
    cnf_tseitin_helper1 prefix ([], 1) f
  in
  assert (not (literal_p f) || match alist with [None, _] -> true | _ -> false);
  (*
  List.iter
    (function
      | None, f -> Printf.eprintf "%s\n" (string_of_formula f)
      | Some p, f -> Printf.eprintf "%s == %s\n" p (string_of_formula f))
    alist;
   *)
  let clauses =
    List.fold_left
      (fun rslt pair ->
	rslt @
	match pair with
	| None, f -> [f]
	| Some p, f ->
	    List.fold_left
	      (fun rslt c ->
		let c' = canonicalize_clause c in
		match c' with
		| Ldl_atomic "true" -> rslt
		| _ -> rslt @ [c'])
	      [] (cnf_tseitin_expand (p, f)))
      (match alist with (Some p, _) :: _ -> [Ldl_atomic p] | _ -> [])
      alist
  in
  assert (cnf_p @@ Ldl_conj clauses);
  clauses

(* cnf_tseitin_helper1 prefix (alist, k) f -> alist'
   where each element of alist' is of the following form:
   - (None, g)     (when g is a literal)
   - (Some p, g)  (o.w.)
     - p is a fresh new symbol, indicating p <=> g
     - g is a forumula that includes a single logical connective
 *)
and cnf_tseitin_helper1 prefix (alist, k) f =
  let gensym k = prefix ^ (string_of_int k)
  in
  (*
  Printf.eprintf ";; cnf_tseitin_helper1: k = %d, alist_len = %d\n" k (List.length alist);
  Printf.eprintf ";; %s\n" (string_of_formula f);
   *)
  match f with
  | _ when literal_p f -> [None, f] @ alist, k
  | Ldl_neg g -> 
      let pairs, alist', k' = cnf_tseitin_helper2 prefix (alist, k + 1) [g]
      in let f' =
	match pairs with
	| [Some p, _] -> Ldl_neg (Ldl_atomic p)
	| _ -> failwith "cnf_tseitin_helper1"
      in (Some (gensym k), f') :: alist', k'
  | Ldl_conj gs ->
      let pairs, alist', k' = cnf_tseitin_helper2 prefix (alist, k + 1) gs
      in let f' =
	Ldl_conj (List.map (function None, g -> g | Some p, _ -> Ldl_atomic p) pairs)
      in (Some (gensym k), f') :: alist', k'
  | Ldl_disj gs ->
      let pairs, alist', k' = cnf_tseitin_helper2 prefix (alist, k + 1) gs
      in let f' =
	Ldl_disj (List.map (function None, g -> g | Some p, _ -> Ldl_atomic p) pairs)
      in (Some (gensym k), f') :: alist', k'
  | Ldl_impl (g1, g2) ->
      (*cnf_tseitin_helper1 prefix (alist, k) (Ldl_disj [Ldl_neg g1; g2])*)
      let pairs, alist', k' = cnf_tseitin_helper2 prefix (alist, k + 1) [g1; g2]
      in let f' =
	let pair1 :: pair2 :: _ = pairs
	in let g1' = match pair1 with None, g1' -> g1' | Some p1, _ -> Ldl_atomic p1
	in let g2' = match pair2 with None, g2' -> g2' | Some p2, _ -> Ldl_atomic p2
	in Ldl_impl (g1', g2')
      in (Some (gensym k), f') :: alist', k'

  | _ -> invalid_arg @@ "[cnf_tseitin_helper1] " ^ string_of_formula f

(* gs -> (alist1, alist2)
   where
   - the i-th element of alist1 corresponds of gs[i] and is of the following form:
     - (None, f)     (when f is a literal)
     - (Some p, f')  (o.w.)
       - p is a fresh new symbol (generated from k)
       - f' (where f and f' are equi-satisfiable)
   - alist2 carries pairs for the subformulas included in gs
 *)
and cnf_tseitin_helper2 prefix (alist, k) gs =
  (*
  Printf.eprintf ";; cnf_tseitin_helper2: k = %d, alist_len = %d\n" k (List.length alist);
   *)
  let alist1, alist2, k' =
    List.fold_left
      (fun (pairs, alist, k) g ->
	let alist', k' = cnf_tseitin_helper1 prefix (alist, k) g
	in
	assert (alist' <> []);
	match alist' with
	| (None, g') :: rest ->
	    pairs @ [None, g'], rest, k'
	| hd :: rest ->
	    pairs @ [hd], alist', k'
	| _ -> failwith "cnf_tseitin_helper2")
      ([], alist, k) gs
  in
  assert (List.length alist1 = List.length gs);
  alist1, alist2, k'

and cnf_tseitin_expand (x, f) =
  match f with
  | Ldl_neg (Ldl_atomic y) ->
      (* x == !y
	 = (!x ∨ !y) ∧ (x ∨ y)
       *)
      let lr = [Ldl_disj [Ldl_neg (Ldl_atomic x); Ldl_neg (Ldl_atomic y)]]
      and rl = [Ldl_disj [Ldl_atomic x; Ldl_atomic y]]
      in lr @ rl

  | Ldl_conj gs ->
      (* x == p1 ∧ p2 ∧ ..
	 = (!x ∨ (p1 ∧ p2 ∧ ..)) ∧ (x ∨ !(p1 ∧ p2 ∧ ..))
	 = (!x ∨ p1) ∧ (!x ∨ p2) ∧ .. ∧ (x ∨ !p1 ∨ !p2 ∨ ..)
       *)
      let lr = List.map (fun g -> Ldl_disj [Ldl_neg (Ldl_atomic x); g]) gs
      and rl = [Ldl_disj (Ldl_atomic x :: List.map (fun g -> Ldl_neg g) gs)]
      in lr @ rl
  | Ldl_disj gs ->
      (* x == p1 ∨ p2 ∨ ..
	 = (!x ∨ (p1 ∨ p2 ∨ ..)) ∧ (x ∨ !(p1 ∨ p2 ∨ ..))
	 = (!x ∨ p1 ∨ p2 ∨ ..) ∧ (x ∨ !p1) ∧ (x ∨ !p2) ∧ ..
       *)
      let lr = [Ldl_disj (Ldl_neg (Ldl_atomic x) :: gs)]
      and rl = List.map (fun g -> Ldl_disj [Ldl_atomic x; Ldl_neg g]) gs
      in lr @ rl
  | Ldl_impl (g1, g2) ->
      (* x == p1 -> p2
	 = (!x ∨ !p1 ∨ p2) ∧ (x ∨ (p1 ∧ !p2))
	 = (!x ∨ !p1 ∨ p2) ∧ (x ∨ p1) ∧ (x ∨ !p2)
       *)
      let lr = [Ldl_disj [Ldl_neg (Ldl_atomic x); Ldl_neg g1; g2]]
      and rl = [Ldl_disj [Ldl_atomic x; g1]; Ldl_disj [Ldl_atomic x; Ldl_neg g2]]
      in lr @ rl
  | _ -> failwith @@ "cnf_tseitin_expand: " ^ (string_of_formula f)


(* ================================================================================
   DPLL_rec
   ================================================================================
 *)

module DPLL_rec = struct

exception Unsat

(* unit_propagate *)

(* unit_propagate (p, b) clauses -> clauses' *)
let rec unit_propagate ((p, b) : string * bool) (clauses : formula list) =
  let clauses' =
    List.fold_left
      (fun clauses' c ->
	let c' = unit_propagate_helper (p, b) c
	in clauses' @ match c' with Ldl_atomic "true" -> [] | _ -> [c'])
      [] clauses
  in clauses'

(* unit_propagate_helper (p, sign) c -> c' *)
and unit_propagate_helper (p, b) (c : formula) =
  assert (clause_p c);
  let literals =
    match c with _ when literal_p c -> [c] | Ldl_disj disj -> disj | _ -> assert false
  in let literals' =
    try
      List.fold_left
	(fun literals' l ->
	  assert (literal_p l);
	  let l = canonicalize_literal l in let p', sign' = expose_literal l in
	  assert (p' <> "true" && p' <> "false");
	  if p <> p' then
	    literals' @ [l]
	  else if sign' = if b then 1 else -1 then
	    (* case: l = true *)
	    raise Exit
	  else
	    (* case: l = false *)
	    literals')
	[] literals
    with Exit -> [Ldl_atomic "true"]
  in
  flatten (Ldl_disj literals')

(* unit_find : clauses -> found
   where
   found : (string * (int list * int list)) list
   found[i] = (p, ([j1; j2; ..], [k1; k2; ..])) indicates
   - p (or ¬p) appears as a unit clause
   - p appears at the j1,j2,..-th clauses
   - ¬p appears at the k1,k2,..-th clauses
    *)
let unit_find (clauses : formula list) =
  let add_literal ((alist : (string * (int list * int list)) list), i) l =
    let p, sign =
	match canonicalize_literal l with
	| Ldl_atomic p -> p, 1
	| Ldl_neg (Ldl_atomic p) -> p, -1
	| _ -> assert false
    in
    let alist' : (string * (int list * int list)) list =
      match List.assoc_opt p alist with
      | None ->
	  alist @ [p, if sign = 1 then [i], [] else [], [i]]
      | Some (pos, neg) ->
	  let pos', neg' = if sign = 1 then pos @ [i], neg else pos, neg @ [i]
	  in
	  if pos' <> [] && neg' <> [] then raise Unsat;
	  List.remove_assoc p alist @ [p, (pos', neg')]
    in alist', i + 1
  in let elims, _ =
    List.fold_left
      (fun (alist, i) c ->
	assert (clause_p c);
	match c with
	| _ when literal_p c -> add_literal (alist, i) c
	| Ldl_disj [l] -> add_literal (alist, i) l
	| _ -> alist, i + 1)
      ([], 0) clauses
  in elims

(* elimination ops -- preserving equi-satisfiability
   - elim_pure_literals
   - elim_subsumption
 *)

(* pure literal elimination
   clauses -> clauses', eliminated
 *)
let rec elim_pure_literals (clauses : formula list) =
  let _, _, (elims : (string * (int * int list)) list) =
    (* elims[i] = (x, (1 or -1, [k1; k2; ..]) indicates:
       - x is a pure literal. sign = 1: x, sign = -1: ¬x
       - it appears the k1,k2,..-th clauses (0-based)
     *)
    List.fold_left
      elim_pure_literals_helper    
      (0, [], []) clauses
  in
  (*List.iter (fun (p, _) -> Printf.eprintf "(%s)" p) elims; output_string stderr "\n";*)
  let indices : int list =
    (* i in indices <=> clauses[i] includes pure literals *)
    List.fold_left (fun rslt (_, (_, indices)) -> rslt @ indices) [] elims
  in let clauses', _ =
    List.fold_left
      (fun (rslt, i) c -> (if List.mem i indices then rslt else rslt @ [c]), i + 1)
      ([], 0) clauses
  in
  clauses', List.map fst elims

and elim_pure_literals_helper (i, keeps, elims) c =
  assert (clause_p c);
  let literals =
    match c with
    | _ when literal_p c -> [c]
    | Ldl_disj literals -> literals
    | _ -> assert false
  in let keeps', elims' =
    List.fold_left
      (fun (keeps, elims) l ->
	match l with
	| Ldl_atomic p | Ldl_neg (Ldl_atomic p) ->
	    if List.mem p keeps then keeps, elims else
	    let sign =
	      match l with Ldl_atomic _ -> 1 | _ -> -1
	    in let keeps', elims' =
	      match List.assoc_opt p elims with
	      | None -> keeps, elims @ [p, (sign, [i])]
	      | Some (s, indices) when s = sign ->
		  keeps,
		  if List.mem i indices
		  then elims
		  else List.remove_assoc p elims @ [p, (sign, indices @ [i])]
	      | Some _ ->
		  keeps @ [p], List.remove_assoc p elims
	      | _ -> assert false
	    in keeps', elims'
	| _ -> assert false)
      (keeps, elims) literals
  in i + 1, keeps', elims'

(* subsumption elimination *)
let elim_subsumption (clauses : formula list) =
  clauses

(* clean-up ops
   - elim_const
   - elim_taut
 *)

(* constant elimination *)
let rec elim_const (clauses : formula list) =
  List.fold_left
    (fun rslt c -> elim_const_helper rslt c)
    [] clauses

and elim_const_helper clauses c =
  assert (clause_p c);
  match c with
  | _ when literal_p c -> clauses @ [c]
  | Ldl_disj literals ->
      let clauses' =
	try
	  let literals' =
	    List.fold_left
	      (fun rslt l ->
		let l' = canonicalize_literal l
		in
		match l' with
		| Ldl_atomic "true" -> raise Exit
		| Ldl_atomic "false" -> rslt
		| _ -> rslt @ [l'])
	      [] literals
	  in
	  clauses @ [Ldl_disj literals']
	with Exit -> clauses
      in clauses'
  |_ when clause_p c ->
      elim_const_helper clauses (canonicalize_clause c)
  | _ ->
      invalid_arg @@ "[elim_const_helper] " ^ string_of_formula c

(* tautology elimination *)
let rec elim_taut (clauses : formula list) =
  try
    List.fold_left
      (fun rslt c -> elim_taut_helper rslt c)
      [] clauses
  with Unsat -> [Ldl_atomic "false"]

and elim_taut_helper clauses c =
  assert (clause_p c);
  match c with
  | Ldl_atomic "true" -> clauses
  | Ldl_atomic "false" -> raise Unsat
  | Ldl_atomic _ | Ldl_neg (Ldl_atomic _) -> clauses @ [c]
  | _ when literal_p c -> elim_taut_helper clauses (canonicalize_literal c)
  | Ldl_disj literals ->
      let literals =
	List.sort
	  (fun l1 l2 ->
	    match l1, l2 with
	    | Ldl_atomic p1, Ldl_atomic p2
	    | Ldl_neg (Ldl_atomic p1), Ldl_neg (Ldl_atomic p2) ->
		compare p1 p2
	    | Ldl_atomic p1, Ldl_neg (Ldl_atomic p2) ->
		if p1 = p2 then 1 else compare p1 p2
	    | Ldl_neg (Ldl_atomic p1), Ldl_atomic p2 ->
		if p1 = p2 then -1 else compare p1 p2
	    | _ -> assert false)
	  (List.map canonicalize_literal literals)
      in let clauses' =
	try
	  let literals', l_opt =
	    List.fold_left
	      (fun (rslt, l1_opt) l2 ->
		let l2 = canonicalize_literal l2
		in
		match l1_opt, l2 with
		| _, Ldl_atomic "true" -> raise Exit
		| _, Ldl_atomic "false" -> rslt, l1_opt
		| None, _ -> rslt, Some l2
		| Some l1, _ when equal l1 l2 ->
		    rslt, Some l2
		| Some l1, _ when equal (canonicalize_literal (Ldl_neg l1)) l2 ->
		    raise Exit
		| Some l1, _ -> rslt @ [l1], Some l2
		| _ -> assert false)
	      ([], None) literals
	  in
	  clauses @ [Ldl_disj (literals' @ match l_opt with Some l -> [l] | None -> [])]
	with Exit -> clauses
      in clauses'
  |_ when clause_p c ->
      elim_taut_helper clauses (canonicalize_clause c)
  | _ ->
      invalid_arg @@ "[elim_taut_helper] " ^ string_of_formula c

(* *)
let rec solve (clauses : formula list) =
  let unassigned = find_variables clauses
  in let solved, assigned = solve_rec (unassigned, []) clauses
  in
  solved, assigned

and solve_rec (unassigned, assigned) clauses =
  if false then
    begin
      output_string stderr @@ ";; [solve_rec] " ^ string_of_formula (Ldl_conj clauses) ^ "\n";
      output_string stderr @@ "unassigned:";
      List.iter (fun p -> output_string stderr @@ " " ^ p) unassigned;
      output_string stderr "\n";
      output_string stderr @@ "assigned:";
      List.iter
	(fun (p, b) -> output_string stderr @@ (if b then " " else " !") ^ p)
	assigned;
      output_string stderr "\n";
      flush stderr;
    end;

  let clauses = elim_const clauses |> elim_taut
  in let solved, assigned' =
    match clauses with
    | [Ldl_atomic "false"] -> false, []
    | [] | [Ldl_atomic "true"] -> true, assigned
    | _ when unassigned = [] ->
	(* should have turned into [false], [], or [true] *)
	assert false;
	true, assigned
    | _ when unassigned <> []->
	let p :: unassigned' = unassigned in

	(* case: p *)
	let solved1, assigned1 =
	  unit_propagate (p, true) clauses |> solve_rec (unassigned', assigned @ [p, true])
	in
	if solved1 then
	  true, assigned1

	(* case: ¬p *)
	else
	  unit_propagate (p, false) clauses |> solve_rec (unassigned', assigned @ [p, false])
  in
  solved, assigned'

end

(* ================================================================================
   satisfiability
   ================================================================================
 *)

let solve (clauses : formula list) =
  assert (let f = Ldl_conj clauses in propositional_p f && cnf_p f);
  DPLL_rec.solve clauses

(* ================================================================================
   dimacs
   ================================================================================
 *)

(* dimacs_parse *)

(* parse a propositional formula in the DIMACS format.
   `names` indicates the variable names
 *)

let dimacs_parse ?(names = [||]) ic =
  let rec split line =
    split_rec (line, String.length line) ([], "") 0
  and split_rec (str, len) (rslt, word) pos =
    if pos >= len then
      rslt @ if word = "" then [] else [word]
    else if List.mem str.[pos] [' '; '\t'; '\n'] then
      if word = ""
      then split_rec (str, len) (rslt, word) (pos + 1)
      else split_rec (str, len) (rslt @ [word], "") (pos + 1)
    else
      split_rec (str, len) (rslt, word ^ String.sub str pos 1) (pos + 1)
  in

  let nvar, ncls =
    let line = ref "c" in
    try
      while !line.[0] != 'p' do line := input_line ic done;
      let words = split !line
      in
      assert (List.length words >= 4 && List.nth words 1 = "cnf");
      int_of_string (List.nth words 2), int_of_string (List.nth words 3)
    with End_of_file -> failwith "[dimacs_parse] no 'p' line detected"
  in    

  let names =
    if Array.length names >= nvar then names else
    Array.init nvar (fun i -> "p" ^ string_of_int (i + 1))
  in let rec read_clauses (rslt, k) ic =
    try
      let line = input_line ic in
      if line.[0] = 'c' then read_clauses (rslt, k) ic else
      let words : string list = split line
      in let literals =
	let nword = List.length words
	in let _ =
	  (* each line should be 0-terminated *)
	  if nword <= 1 || List.nth words (nword - 1) <> "0" then
	    failwith @@ Printf.sprintf "[dimacs_parse] invalid line (%d): %S" k line
	in
	List.fold_left
	  (fun rslt w ->
	    let i = int_of_string w in
	    assert (abs i <= nvar);
	    if i = 0 then
	      rslt
	    else if i > 0 then
	      rslt @ [Ldl_atomic names.(i - 1)]
	    else
	      rslt @ [Ldl_neg (Ldl_atomic names.(abs i - 1))])
	  [] words
      in read_clauses (rslt @ [Ldl_disj literals], k + 1) ic
    with End_of_file -> rslt, k
  in let clauses, nread =
    read_clauses ([], 0) ic
  in
  if not (nread = ncls) then
    failwith @@ Printf.sprintf "[dimacs_parse] #line (%d) <> %d" nread ncls;
  assert (nread = ncls);
  clauses

(* dimacs_print *)

let rec dimacs_print ?(verbose = false) oc (clauses : formula list) =
  let alist = find_variables clauses |> List.mapi (fun i x -> x, i + 1)
  in 

  (* header *)
  if verbose then
    begin
      output_string oc "c";
      List.iter (function x, i -> Printf.fprintf oc " [%d] %s" i x) alist;
      output_string oc "\n";
    end;
  Printf.fprintf oc "p cnf %d %d\n" (List.length alist) (List.length clauses);

  (* clauses *)
  List.iter
    (fun clause ->
      if verbose then Printf.fprintf oc "c %s\n" (string_of_formula clause);
      List.iter
	(fun k -> Printf.fprintf oc "%d " k)
	(dimacs_print_helper alist [] clause);
      Printf.fprintf oc "0\n")
    clauses

(* clause (= [l; l'; ...]) -> [k; k'; ...]
   where k, k', .. are the literals in the dimacs numeric form, that is,
   - case k > 0: l
   - case k < 0: ¬l
 *)
and dimacs_print_helper (alist : (string * int) list) (rslt : int list) (c : formula) =
  assert (clause_p c);
  match c with
  | _ when literal_p c ->
      let p, sign = expose_literal (canonicalize_literal c) in
      assert (List.mem_assoc p alist);
      let k = sign * List.assoc p alist in
      assert (not (List.mem k rslt || List.mem (- k) rslt));
      rslt @ [k]
  | Ldl_conj [] -> rslt
  | Ldl_disj gs -> List.fold_left (dimacs_print_helper alist) rslt gs
  | _ -> failwith "dimacs_print_helper"

