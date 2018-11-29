(* $Id: $ *)
(*
 * (C) Copyright IBM Corp. 2018.
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

let rec propositional = function
  | f when literal_p f -> true
  | Ldl_conj fs | Ldl_disj fs ->
      List.fold_left (fun b f -> b && propositional f) true fs
  | Ldl_impl (f, g) -> (propositional f) && (propositional g)
  | Ldl_modal _ -> false
  | _ -> false

(* literal = atomic formula or its negation *)
and literal_p = function
  | Ldl_atomic "last" -> false
  | Ldl_atomic _ -> true
  | Ldl_neg f -> literal_p f
  | Ldl_conj [] | Ldl_disj [] -> true
  | _ -> false

(* (disjunctive) clause? *)
let rec clause_p (c : formula) =
  (* examine if c is a disjunction of literals *)
  match c with
  | _ when literal_p c -> true
  | Ldl_conj [] -> true
  | Ldl_disj disj ->
      (try let _ = List.find (fun f -> not (literal_p f)) disj in false with Not_found -> true)
  | _ -> false

(** cnf_p *)

let rec cnf_p f =
  cnf_p_rec 0 f

and cnf_p_rec (depth : int) = function
  | Ldl_atomic _ -> true
  | Ldl_neg (Ldl_atomic _) -> true
  | Ldl_neg _ -> false

  | Ldl_conj [] -> true
  | Ldl_conj fs when depth = 0 ->
      (try let _ = List.find (fun f -> not (cnf_p_rec (depth + 1) f)) fs in false
       with Not_found -> true)
  | Ldl_conj _ -> false

  | Ldl_disj [] -> true
  | Ldl_disj fs when depth <= 1 ->
      (try let _ = List.find (fun f -> not (cnf_p_rec (depth + 1) f)) fs in false
       with Not_found -> true)
  | Ldl_disj _ -> false

  | Ldl_impl _ -> false
	(* should not appear *)
  | Ldl_modal _ -> true

(** dnf_p *)

let rec dnf_p f =
  dnf_p_rec 0 f

and dnf_p_rec (depth : int) = function
  | Ldl_atomic _ -> true
  | Ldl_neg (Ldl_atomic _) -> true
  | Ldl_neg _ -> false

  | Ldl_conj [] -> true
  | Ldl_conj fs when depth <= 1 ->
      (try let _ = List.find (fun f -> not (dnf_p_rec (depth + 1) f)) fs in false
       with Not_found -> true)

  | Ldl_disj [] -> true
  | Ldl_disj fs when depth = 0 ->
      (try let _ = List.find (fun f -> not (dnf_p_rec (depth + 1) f)) fs in false
       with Not_found -> true)
  | Ldl_disj _ -> false
	(* disj within a conj is not a dnf *)

  | Ldl_impl _ -> false
	(* should not appear *)
  | Ldl_modal _ -> true

(* ================================================================================
   flatten
   ================================================================================
 *)

let rec flatten f =
  match f with
  | Ldl_atomic _ -> f
  | Ldl_neg f' -> Ldl_neg (flatten f')
  | Ldl_conj fs ->
      let fs' = flatten_conj (List.map flatten fs) in
      if List.length fs' = 1 then List.hd fs' else Ldl_conj fs'
  | Ldl_disj fs ->
      let fs' = flatten_disj (List.map flatten fs) in
      if List.length fs' = 1 then List.hd fs' else Ldl_disj fs'
  | Ldl_impl (f', g) -> Ldl_impl ((flatten f'), flatten g)
  | Ldl_modal _ -> f

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

(* ================================================================================
   simp_flatten/simp_sort/simp_uniq/simp_clause
   ================================================================================
 *)

(* simp_flatten *)

let rec simp_flatten f =
  match f with
  | Ldl_atomic _ -> f
  | Ldl_neg f' -> Ldl_neg (simp_flatten f')
  | Ldl_conj fs ->
      let fs' = simp_flatten_conj (List.map simp_flatten fs) in
      if List.length fs' = 1 then List.hd fs' else Ldl_conj fs'
  | Ldl_disj fs ->
      let fs' = simp_flatten_disj (List.map simp_flatten fs) in
      if List.length fs' = 1 then List.hd fs' else Ldl_disj fs'
  | Ldl_impl (f', g) -> Ldl_impl ((simp_flatten f'), simp_flatten g)
  | Ldl_modal _ -> f

and simp_flatten_conj (fs : formula list) =
  List.fold_left
    (fun rslt f -> match f with Ldl_conj fs' -> rslt @ fs' | _ -> rslt @ [f])
    [] fs

and simp_flatten_disj (fs : formula list) =
  List.fold_left
    (fun rslt f -> match f with Ldl_disj fs' -> rslt @ fs' | _ -> rslt @ [f])
    [] fs

(* simp_sort *)

let rec simp_sort f =
  (*if not (cnf_p f || dnf_p f) then failwith ("simp_sort: " ^ show_formula f);*)
  assert (cnf_p f || dnf_p f);
  let f' = simp_flatten f in
  let is_cnf, is_dnf = cnf_p f', dnf_p f' in
  assert (is_cnf || is_dnf);
  match f' with
  | Ldl_atomic _ | Ldl_neg _ | Ldl_modal _ -> f'

  (* cnf *)
  | Ldl_disj fs when is_cnf ->
      (* fs = literals *)
      Ldl_disj (simp_sort_literals fs)
  | Ldl_conj fs when is_cnf ->
      (* fs = disjuncts = [Ldl_disj _; Ldl_disj _; ..] *)
      let fs' =	List.map (function Ldl_disj gs -> gs | f -> [f]) fs in
      Ldl_conj (List.map (fun disj -> Ldl_disj disj) (simp_sort_clauses (List.map simp_sort_literals fs')))

(*
  (* dnf *)
  | Ldl_conj fs when is_dnf ->
      (* fs = literals *)
      (*simp_sort_conj f'*)
      Ldl_conj (simp_sort_literals fs)
  | Ldl_disj fs when is_dnf ->
      (* fs = conjuncts = [Ldl_conj _; Ldl_conj _; ..] *)
      Ldl_disj (List.sort simp_sort_disj_comp (List.map simp_sort_conj fs))
 *)

  (* dnf *)
  | Ldl_conj fs when is_dnf ->
      (* fs = literals *)
      Ldl_conj (simp_sort_literals fs)
  | Ldl_disj fs when is_dnf ->
      (* fs = conjuncts = [Ldl_conj _; Ldl_conj _; ..] *)
      let fs' =	List.map (function Ldl_conj gs -> gs | f -> [f]) fs in
      Ldl_disj (List.map (fun conj -> Ldl_conj conj) (simp_sort_clauses (List.map simp_sort_literals fs')))

  | _ -> failwith "simp_sort"

(* fs = list of literals *)
and simp_sort_literals (fs : formula list) =
  List.sort simp_comp_literals fs

(* f1, f2: literal *)
and simp_comp_literals f1 f2 =
  match f1 with
  | Ldl_atomic str1 ->
      let rslt =
	match f2 with
	| Ldl_atomic str2 -> String.compare str1 str2
	| Ldl_neg (Ldl_atomic str2) when str1 = str2 -> -1
	| Ldl_neg (Ldl_atomic str2) -> String.compare str1 str2
	| Ldl_conj [] -> simp_comp_literals f1 (Ldl_atomic "true")
	| Ldl_disj [] -> simp_comp_literals f1 (Ldl_atomic "false")
	| Ldl_modal _ -> -1
	| _ -> failwith "simp_comp_literals:1"
      in rslt
  | Ldl_neg (Ldl_atomic str1) ->
      let rslt =
	match f2 with
	| Ldl_atomic str2 when str1 = str2 -> 1
	| Ldl_atomic str2 -> String.compare str1 str2
	| Ldl_neg (Ldl_atomic str2) when str1 = str2 -> 0
	| Ldl_neg (Ldl_atomic str2) -> String.compare str1 str2
	| Ldl_conj [] -> simp_comp_literals f1 (Ldl_atomic "true")
	| Ldl_disj [] -> simp_comp_literals f1 (Ldl_atomic "false")
	| Ldl_modal _ -> -1
	| _ -> failwith "simp_comp_literals:2"
      in rslt
  | Ldl_conj [] -> simp_comp_literals (Ldl_atomic "true") f2
  | Ldl_disj [] -> simp_comp_literals (Ldl_atomic "false") f2
  | _ -> failwith "simp_comp_literals:3"

(* f = list of clauses *)
and simp_sort_clauses (clauses : formula list list) =
  List.sort simp_comp_clauses clauses

(* f1, f2: conjunctive/disjunctive clause (list of literals) *)
and simp_comp_clauses (c1 : formula list) (c2 : formula list) =
  match c1 with
  | [] ->
      let rslt =
	match c2 with
	| [] -> 1
	| f2' :: rest2 -> -1
      in rslt
  | f1' :: rest1 ->
      let rslt =
	match c2 with
	| [] -> 1
	| f2' :: rest2 ->
	    let c = simp_comp_literals f1' f2' in
	    if c = 0
	    then simp_comp_clauses rest1 rest2
	    else c
      in rslt

(*
(* f = clause (disj of literals) *)
and simp_sort_disj (f : formula) =
  match f with
  | Ldl_disj fs -> Ldl_disj (List.sort simp_sort_disj_comp fs)
  | Ldl_conj [] -> f
  | Ldl_conj [f'] -> f'
  | Ldl_conj _ -> failwith "simp_sort_disj"
  | _ -> f

(* f = conjunctive clause (conj of literals) *)
and simp_sort_conj (f : formula) =
  match f with
  | Ldl_conj fs -> Ldl_conj (List.sort simp_sort_disj_comp fs)
  | Ldl_disj [] -> f
  | Ldl_disj [f'] -> f'
  | Ldl_disj _ -> failwith "simp_sort_conj"
  | _ -> f

(* f1, f2: conjunctive clause *)
and simp_sort_disj_comp f1 f2 =
  match f1 with
  | Ldl_atomic str1 ->
      let rslt =
	match f2 with
	| Ldl_atomic str2 -> String.compare str1 str2
	| Ldl_neg (Ldl_atomic str2) when str1 = str2 -> -1
	| Ldl_neg (Ldl_atomic str2) -> String.compare str1 str2
	| Ldl_conj _ -> simp_sort_disj_comp (Ldl_conj [f1]) f2
	| Ldl_disj [] -> -1
	| Ldl_disj _ | Ldl_impl _ -> failwith "simp_sort_disj_comp:1"
	| Ldl_modal _ -> -1
      in rslt
  | Ldl_neg (Ldl_atomic str1) ->
      let rslt =
	match f2 with
	| Ldl_atomic str2 when str1 = str2 -> 1
	| Ldl_atomic str2 -> String.compare str1 str2
	| Ldl_neg (Ldl_atomic str2) when str1 = str2 -> 0
	| Ldl_neg (Ldl_atomic str2) -> String.compare str1 str2
	| Ldl_conj _ -> simp_sort_disj_comp (Ldl_conj [f1]) f2
	| Ldl_disj [] -> -1
	| Ldl_disj _ | Ldl_impl _ -> failwith "simp_sort_disj_comp:2"
	| Ldl_modal _ -> -1
      in rslt
  | Ldl_conj [] ->
      let rslt =
	match f2 with
	| Ldl_conj [] -> 0
	| Ldl_conj _ -> -1
	| Ldl_disj [] -> -1
	| Ldl_disj _ -> failwith "simp_sort_disj_comp:3"
	| _ -> -1
      in rslt
  | Ldl_conj (f1' :: rest1) ->
      let rslt =
	match f2 with
	| Ldl_atomic _ | Ldl_neg _ | Ldl_modal _ ->
	    simp_sort_disj_comp f1 (Ldl_conj [f2])
	| Ldl_conj [] -> 1
	| Ldl_conj (f2' :: rest2) ->
	    let c = simp_sort_disj_comp f1' f2' in
	    if c = 0
	    then simp_sort_disj_comp (Ldl_conj rest1) (Ldl_conj rest2)
	    else c
	| Ldl_disj [] -> -1
	| _  -> failwith "simp_sort_disj_comp:4"
      in rslt
  | Ldl_disj [] ->
      let rslt =
	match f2 with Ldl_conj [] -> 1 | Ldl_disj [] -> 0 | _ -> 1
      in rslt
  | Ldl_modal _ ->
      let rslt =
	match f2 with
	| Ldl_modal _ -> 0
	| _ -> 1
      in rslt
  | _ -> failwith "simp_sort_disj_comp:5"
 *)

(* simp_uniq -- fold consecutive identical formulas into one *)

let rec simp_uniq f =
  assert (dnf_p f || cnf_p f);
  simp_uniq_rec f

and simp_uniq_rec f =
  match f with
  | Ldl_conj fs -> Ldl_conj (simp_uniq_helper (List.map simp_uniq_rec fs))
  | Ldl_disj fs -> Ldl_disj (simp_uniq_helper (List.map simp_uniq_rec fs))
  | _ -> f

and simp_uniq_helper fs =
  if fs = [] then [] else
  let gs, g =
    List.fold_left
      (fun (rslt, f) f' ->
	if equal f f' then rslt, f else (rslt @ [f]), f')
      ([], List.hd fs) (List.tl fs)
  in gs @ [g]

(* simp_clause *)

let rec simp_clause c =
  assert (clause_p c);
  match c with
  | _ when literal_p c -> c
  | Ldl_disj literals ->
      (try
	List.find (function Ldl_atomic "true" | Ldl_conj [] -> true | _ -> false) literals
       with Not_found ->
	 let literals' =
	   List.filter (function Ldl_atomic "false" | Ldl_disj [] -> false | _ -> true) literals in
	 List.iter (fun l -> assert (literal_p l)) literals';
         Ldl_disj literals' |> simp_sort |> simp_uniq |> flatten)
  | _ ->
      failwith "simp_clause"

(* ================================================================================
   cnf/dnf
   ================================================================================
 *)

(** cnf *)

let rec cnf f =
  let f' = f |> flatten |> cnf_rec in
  (*if not (cnf_p f') then failwith ("cnf: " ^ show_formula f');*)
  assert (cnf_p f');
  f'

(* f -> f' in cnf *)
and cnf_rec f =
  let f' =
    match f with
    | Ldl_atomic _ -> f
    | Ldl_neg f' -> cnf_neg f'
    | Ldl_conj fs -> flatten (Ldl_conj (List.map cnf_rec fs))
    | Ldl_disj fs -> cnf_disj (List.map cnf_rec fs)
    | Ldl_impl (f1, f2) -> cnf_disj [cnf_neg f1; cnf_rec f2]
    | _ -> f
  in
  assert (cnf_p f');
  f'

(* f -> !f in cnf *)
and cnf_neg f =
  let f' =
    match f with
    | Ldl_atomic _ -> Ldl_neg f
    | Ldl_neg f' -> cnf_rec f'
    | Ldl_conj fs -> cnf_disj (List.map cnf_neg fs)
	  (* ¬ (f1 ∧ f2) = ¬f1 ∨ ¬f2 *)
    | Ldl_disj fs -> flatten (Ldl_conj (List.map cnf_neg fs))
	  (* ¬ (f1 ∨ f2) = ¬f1 ∧ ¬f2 *)
    | Ldl_impl (f1, f2) -> cnf_rec (Ldl_conj [f1; Ldl_neg f2])
    | _ -> flatten (Ldl_neg f)
  in
  assert (cnf_p f');
  f'

(* fs = {f | f is cnf} -> Ldl_conj [f1'; f2'; ..]
   steps
   - split fs to disj and conjs
   - disj ∨ conjs -> disjs
     f ∨ (g ∧ h) = (f ∨ g) ∧ (f ∨ h)
   - returns: Ldl_conj disjs
 *)
and cnf_disj fs =
  let (disj : formula list), (conjs : formula list list) = cnf_disj_split ([], []) fs in
  (* disj = disj [f1; f2; f3; ...],  conjs = disj [conj1; conj2; ..] *)
  let fs'=
    List.fold_left
      (fun (rslt : formula list) (conj : formula list) ->
	(* rslt = conj [disj1; disj2; ..], conj = conj [g1; g2'; ..]
	   rslt ∨ conj -> conj [disj1∨g1; conj2∧g2; ...] *)
	List.fold_left
	  (fun rslt' rslt_elt ->
	    let clauses =
	      List.map (fun conj_elt -> flatten (Ldl_disj [rslt_elt; conj_elt])) conj
	    in rslt' @ clauses)
	  [] rslt)
      [Ldl_disj disj] conjs in
  let f' = flatten (Ldl_conj fs')
  in
  assert (cnf_p f');
  f'

(* fs = disj [conj1; ...] -> (disjs, conjs) *)
and cnf_disj_split (disjs, conjs) fs =
  if fs = [] then (disjs, conjs) else
  let f :: rest = fs in
  (* f is in cnf *)
  match f with
  | Ldl_atomic _ -> cnf_disj_split ((disjs @ [f]), conjs) rest
  | Ldl_neg f' ->  cnf_disj_split ((disjs @ [f]), conjs) rest
  | Ldl_conj fs' -> cnf_disj_split (disjs, conjs @ [fs']) rest
  | Ldl_disj fs' -> cnf_disj_split ((disjs @ fs'), conjs) rest
  | Ldl_impl (f1, f2) -> failwith "cnf_disj_split"
  | _ -> cnf_disj_split ((disjs @ [f]), conjs) rest

(** dnf *)

let rec dnf f =
  let f' = dnf_rec (flatten f) in
  (*if not (dnf_p f') then failwith ("dnf: " ^ show_formula f);*)
  assert (dnf_p f');
  f'

and dnf_rec f =
  match f with
  | Ldl_atomic _ -> f
  | Ldl_neg f' -> dnf_neg f'
(*| Ldl_conj fs -> dnf_conj (List.map dnf_rec fs)*)
  | Ldl_conj fs -> dnf_conj_smart (List.map dnf_rec fs)
  | Ldl_disj fs -> Ldl_disj (List.map dnf_rec fs)
  | Ldl_impl (f1, f2) -> Ldl_disj [dnf_neg f1; dnf_rec f2]
  | _ -> f

(* f -> !f in dnf *)
and dnf_neg f =
  match f with
  | Ldl_atomic _ -> Ldl_neg f
  | Ldl_neg f' -> dnf_rec f'
	(* ¬ (¬f) = f *)
  | Ldl_conj fs -> Ldl_disj (List.map dnf_neg fs)
	(* ¬ (f1 ∧ f2) = ¬f1 ∨ ¬f2 *)
(*| Ldl_disj fs -> dnf_conj (List.map dnf_neg fs)*)
  | Ldl_disj fs -> dnf_conj_smart (List.map dnf_neg fs)
	(* ¬ (f1 ∨ f2) = ¬f1 ∧ ¬f2 *)
  | Ldl_impl (f1, f2) -> dnf_rec (Ldl_conj [f1; Ldl_neg f2])
	(* ¬ (f1 -> f2) = f1 ∧ ¬f2 *)
  | _ -> Ldl_neg f

(* f1 ∧ f2 ∧ ... -> g1 ∨ g2 ∨ ... *)
and dnf_conj fs =
  let conj, (disjs : formula list list) = dnf_conj_split ([], []) fs in
  (* conj = conj [f1; f2; f3; ...],  disjs = conj [disj1; disj2; ..] *)
  let fs'=
    List.fold_left
      (fun rslt disj ->
	(* rslt = disj [conj1; conj2; ..], disj = disj [g1; g2'; ..]
	   rslt /\ disj -> disj [conj1/\g1; conj2/\g2; ...] *)
	assert (dnf_p (Ldl_disj rslt) && dnf_p (Ldl_disj disj));
	List.fold_left
	  (fun rslt' rslt_elt ->
	    rslt' @ List.map (fun disj_elt -> Ldl_conj [rslt_elt; disj_elt]) disj)
	  [] rslt)
      [Ldl_conj conj] disjs in
  Ldl_disj fs'

(* a bit smarter, hopefully -- experimental *)
and dnf_conj_smart fs =
  let (conj : formula list), (disjs : formula list list) = dnf_conj_split ([], []) fs in
  (* conj = conj [f1; f2; f3; ...], which is in dnf
     disjs = conj [disj1; disj2; ..], which is subject to normalization
   *)
  let fs' : formula list =
    (* fs' -- disjunctive *)
    List.fold_left
      (fun (rslt : formula list) (disj : formula list) ->
	(* rslt = disj [conj1; conj2; ..], disj = disj [g1; g2'; ..]
	   rslt ∧ disj -> disj [conj1 ∧ g1; conj2 ∧ g2; ...] *)
	assert (dnf_p (Ldl_disj rslt) && dnf_p (Ldl_disj disj));
	List.fold_left
	  (fun (rslt' : formula list) (rslt_elt : formula) ->
	    let conjs : formula list =
	      List.map
		(fun (disj_elt : formula) ->
		  let conjs' : formula list = flatten_conj [disj_elt; rslt_elt] in

		  (* quick simplification *)
		  let conjs' : formula list =
		    if List.mem (Ldl_atomic "false") conjs' then [Ldl_atomic "false"] else
		    List.fold_left
		      (fun (rslt : formula list) (conj : formula) ->
			match conj with
			| Ldl_atomic "true" -> rslt
			| Ldl_neg (Ldl_atomic "false") -> rslt
			| _ when List.mem conj rslt -> rslt
			| _ -> rslt @ [conj])
		      [] conjs' in

		  Ldl_conj conjs')
		disj
	    in rslt' @ conjs)
	  [] rslt)
      [Ldl_conj conj] disjs in
  Ldl_disj fs'

(* fs = f1 ∧ f2 ∧ ... -> (f1' ∧ f2' ∧ ...), (g1 ∨ g2 ∨ ...) *)
and dnf_conj_split ((conj : formula list), (disjs : formula list list)) fs =
  if fs = [] then (conj, disjs) else
  let f :: rest = fs in
  (* f is in dnf *)
  match f with
  | Ldl_atomic _ -> dnf_conj_split ((conj @ [f]), disjs) rest
  | Ldl_neg _ -> dnf_conj_split ((conj @ [f]), disjs) rest
  | Ldl_conj fs' -> dnf_conj_split ((conj @ fs'), disjs) rest
  | Ldl_disj fs' -> dnf_conj_split (conj, disjs @ [fs']) rest
  | Ldl_impl (f1, f2) -> failwith "dnf_conj_split"
  | _ -> dnf_conj_split ((conj @ [f]), disjs) rest

(* ================================================================================
   simp_equiv
   ================================================================================
 *)

(* equiv
   - !!a = a
   - true /\ a = a
   - false /\ a = false
   - true \/ a = true
   - false \/ a = a
   - a /\ a = a
   - a \/ a = a
   - a /\ !a = false
   - a \/ !a = true
 *)

let rec simp_equiv f =
  let tt = Ldl_atomic "true" and ff = Ldl_atomic "false" in
  match f with
  | Ldl_atomic _ -> f

  | Ldl_neg f' when f' = tt -> ff
  | Ldl_neg f' when f' = ff -> tt
  | Ldl_neg (Ldl_atomic _) -> f
  | Ldl_neg (Ldl_neg f') -> simp_equiv f'
  | Ldl_neg f' -> Ldl_neg (simp_equiv f')

  | Ldl_conj [] -> tt
  | Ldl_conj fs ->
      let f' =
	match simp_equiv_conj [] (List.map simp_equiv fs) with
	| [] -> tt | [f'] -> f'	| fs' -> Ldl_conj fs'
      in f'
  | Ldl_disj [] -> ff
  | Ldl_disj fs ->
      let f' =
	match simp_equiv_disj [] (List.map simp_equiv fs) with
	| [] -> ff | [f'] -> f'	| fs' -> Ldl_disj fs'
      in f'

  | _ -> f

and simp_equiv_conj rslt conj =
  let tt = Ldl_atomic "true" and ff = Ldl_atomic "false" in
  match conj with
  | [] -> rslt
  | f :: rest when f = ff || f = Ldl_neg tt -> [ff]
  | f :: rest when f = tt || f = Ldl_neg ff -> simp_equiv_conj rslt rest
  | f :: rest when List.mem (Ldl_neg f) rest (* f ∧ ¬f *) -> [ff]
  | Ldl_neg f :: rest when List.mem f rest (* ¬f ∧ f *) -> [ff]
  | f :: rest when List.mem f rslt (* duplicate *) ->
      simp_equiv_conj rslt rest
  | f :: rest -> simp_equiv_conj (rslt @ [f]) rest

and simp_equiv_disj rslt disj =
  let tt = Ldl_atomic "true" and ff = Ldl_atomic "false" in
  match disj with
  | [] -> rslt
  | f :: rest when f = tt || f = Ldl_neg ff -> [tt]
  | f :: rest when f = ff || f = Ldl_neg tt -> simp_equiv_disj rslt rest
  | f :: rest when List.mem (Ldl_neg f) rest (* f ∨ ¬f *) -> [tt]
  | Ldl_neg f :: rest when List.mem f rest (* ¬f ∨ f *) -> [tt]
  | f :: rest when List.mem f rslt (* duplicate *) ->
      simp_equiv_disj rslt rest
  | f :: rest -> simp_equiv_disj (rslt @ [f]) rest

(*
and simp_equiv_conj (fs : formula list) =
  let tt = Ldl_atomic "true" and ff = Ldl_atomic "false" in
  if List.mem ff fs then [ff] else
  List.fold_left
    (fun rslt f ->
      match f with
      | _ when f = tt -> rslt
      | _ when List.mem f rslt -> rslt
      | _ when List.mem (Ldl_neg f) fs -> [ff]
      | _ -> rslt @ [f])
    [] fs

and simp_equiv_disj fs =
  let tt = Ldl_atomic "true" and ff = Ldl_atomic "false" in
  if List.mem tt fs then [tt] else
  List.fold_left
    (fun rslt f ->
      match f with
      | _ when f = ff -> rslt
      | _ when List.mem f rslt -> rslt
      | _ when List.mem (Ldl_neg f) fs -> [tt]
      | _ -> rslt @ [f])
    [] fs
 *)

let simp_safe f =
  f |> simp_equiv |> simp_flatten |> cnf |> simp_sort |> simp_uniq |> flatten
  (*f |> dnf |> simp_flatten |> dnf |> simp_sort |> simp_uniq*)
  (*f |> flatten |> simp_equiv |> resolve |> dnf |> simp_flatten |> simp_sort*)

(* ================================================================================
   resolve
   ================================================================================
 *)

(* find a single complement pair for resolution.
   note: detecting more than one pair will not make any difference
*)
exception PairFound of (Ldl.formula * Ldl.formula)

let complement_pair (clause1 : formula list) (clause2 : formula list) =
(*
  Printf.eprintf ";; complement_pair\n   %s\n   %s\n"
    (string_of_formula (Ldl_disj clause1))
    (string_of_formula (Ldl_disj clause2));
  flush_all ();
 *)
  try
    let _ =
      List.find
	(fun elt ->
	  let found_opt =
	    List.find_opt
	      (fun elt' ->
		match elt, elt' with
		| Ldl_atomic a, Ldl_neg (Ldl_atomic a') when a = a' -> true
		| Ldl_neg (Ldl_atomic a), Ldl_atomic a' when a = a' -> true
		| _ -> false)
	      clause2
	  in
	  match found_opt with
	  | None -> false
	  | Some elt' -> raise (PairFound (elt, elt')))
	clause1
    in raise Not_found
  with PairFound pair -> pair

(* resolve1: clause1 clause2 -> clause3
   {p}, {¬p,q} => {q}
   {p}, {¬p} => {} = {false} (indicates: ⊥)
   {p,q}, {¬p,¬q} => {q,¬q} or {p,¬p} => {true} (should be distinguished from {})
   {p,q,r}, {¬p,¬q,r} => {p,¬p,r} or {q,¬q,r} => {true}
   {p}, {q} => Not_found
 *)
let rec resolve1 (disj1 : formula list) (disj2 : formula list) =
  (*
  Printf.eprintf ";; resolve1\n   %s\n   %s\n"
    (string_of_formula (Ldl_disj disj1))
    (string_of_formula (Ldl_disj disj2));
  flush_all ();
   *)
  assert (disj1 <> [] && disj2 <> []);
  if not (all_literal_p disj1 && all_literal_p disj2) then
    invalid_arg "resolve1: non-literal detected";
  assert (all_literal_p disj1 && all_literal_p disj2);

  let disj1', disj2' = resolve1_helper [] disj1, resolve1_helper [] disj2 in
  if disj1' = [] || disj2' = [] then [] (* indicates ⊥ *) else

  let elt1, elt2 = complement_pair disj1' disj2' in
(*
  if pairs <> [] then Printf.eprintf "   => %d pair(s) found\n" (List.length pairs);
  if pairs = [] then raise Not_found else
*)
  assert (List.mem elt1 disj1' && List.mem elt2 disj2');
  if disj1' = [elt1] && disj2' = [elt2] then [] (* indicates ⊥ *) else

  let disj3 =
    (List.filter ((<>) elt1) disj1') @ List.filter ((<>) elt2) disj2'
  in resolve1_helper [] disj3

and resolve1_helper (rslt : formula list) (disj : formula list) =
  let tt = Ldl_atomic "true" and ff = Ldl_atomic "false" in
  match disj with
  | [] -> rslt
  | f :: rest when f = tt || f = Ldl_neg ff -> [tt]
  | f :: rest when f = ff || f = Ldl_neg tt -> resolve1_helper rslt rest
  | f :: rest when List.mem (Ldl_neg f) rest (* f ∨ ¬f *) -> [tt]
  | Ldl_neg f :: rest when List.mem f rest (* ¬f ∨ f *) -> [tt]
  | f :: rest when List.mem f rslt (* duplicate *) ->
      resolve1_helper rslt rest
  | f :: rest -> resolve1_helper (rslt @ [f]) rest

(*
and resolvable1 f g =
  match f, g with
  | Ldl_atomic a, Ldl_neg (Ldl_atomic b) when a = b -> true
  | Ldl_neg (Ldl_atomic a), Ldl_atomic b when a = b -> true
  | _ -> false  
*)

and all_literal_p (clause : formula list) =
  try
    let _ = List.find (fun f -> not (literal_p f)) clause in false
  with Not_found -> true

(* resolve: f -> g (in cnf)
   ** very inefficient. needs to update!
 *)
let rec resolve (f : formula) =
(*
  Printf.eprintf ";; resolve: %s\n" (string_of_formula f); flush_all ();
 *)
  let f = if cnf_p f then f else cnf f in
  assert (cnf_p f);
  let f = simp_safe f in
  match f with
  | Ldl_conj [] -> f
  | Ldl_conj [g] -> g
  | Ldl_conj clauses ->
      let clauses' : formula list =
	try resolve_rec [] clauses
	with Exit (* resolution fails, indicating ⊥ *) -> [Ldl_disj []] in
      List.iter (fun c -> assert (clause_p c)) clauses';

      (* post-process *)
      let clauses'' : formula list =
	try
	  List.fold_left
	    (fun rslt c ->
	    match c with
	    | Ldl_disj [] (* false *) -> raise Exit
	    | Ldl_disj disj ->
		let c'' =
		  match resolve1_helper [] disj with
		  | [Ldl_atomic "true"] -> rslt
		  | _ -> rslt @ [c]
		in c''
	    | _ -> rslt @ [c])
	    [] clauses'
	with Exit -> [Ldl_atomic "false"]
      in flatten @@ Ldl_conj clauses''

     (*
      let rec postproc (clauses : formula list) =
	try postproc_rec [] clauses with Exit -> [Ldl_atomic "false"]
      and postproc_rec (rslt : formula list) (clauses : formula list) =
	if clauses = [] then rslt else
	let c :: rest = clauses in
	match simp_clause (flatten c) with
	| Ldl_atomic "true" -> postproc_rec rslt rest
	| Ldl_atomic "false" -> raise Exit
	| Ldl_disj [] -> [Ldl_atomic "false"]
	| c' -> postproc_rec (rslt @ [c']) rest in
      let clauses'' = postproc clauses' in
      List.iter (fun c -> assert (clause_p c)) clauses'';

      Ldl_conj clauses'' |> simp_sort |> simp_uniq |> flatten
      *)

  | Ldl_disj [] -> Ldl_atomic "false"
  | Ldl_disj disj -> flatten @@ Ldl_disj (resolve1_helper [] disj)
  | _ -> f

(* resolve_rec resolved clauses -> clauses'
   where
   - resolved = {(i, j) | i <= j, clauses[i] and clauses[j] has no complement pair}
   - clauses = all clauses generated so far

   at each iteration,
   - resolve_rec traverses over all combinations (c[i], c[j]) in clauses * clauses, and
     finds (c[i], c[j]) that are not yet resolved (i.e., (i,j) is not in resolved).
   - if no such pair is found, recursion terminates
   - o.w. resolve them, and generate a new clause c'.
     - if c' = {} then recursion terminates
     - o.w. proceed to another iteration with clauses' = clauses + generated clauses.

   rslt and clauses are of the form [Ldl_disj ..; Ldl_disj ..]
 *)
and resolve_rec (resolved : (int * int) list) (clauses : formula list) =
(*
  Printf.eprintf ";; resolve_rec\n";
  List.iter (fun c -> Printf.eprintf "   %s\n" (string_of_formula c)) clauses;
  flush_all ();
*)
  assert (cnf_p (Ldl_conj clauses));
  let clause_to_disj c =
    match c with
    | Ldl_disj disj -> disj
    | Ldl_conj [] -> [c]
    | Ldl_conj _ -> failwith @@ "clause_to_disj: " ^ show_formula c
    | _ -> [c]
  in
  let added, resolved', _ =
    List.fold_left
      (fun (added, resolved, i) (c1 : formula) ->
	(*Printf.eprintf "(c1=%s)" (show_formula c1); flush_all ();*)
	let disj1 = clause_to_disj c1 in
	let added, resolved, _ =
	  List.fold_left
	    (fun (added, resolved, j) (c2 : formula) ->
	      (*Printf.eprintf "(c2=%s)" (show_formula c1); flush_all ();*)
	      let disj2 = clause_to_disj c2 in
	      let added, resolved =
		if j = i then added, resolved else
		let k1, k2 = min i j, max i j in
		if List.mem (k1, k2) resolved then
		  added, resolved
		else
		  try
		    match resolve1 disj1 disj2 with
		    | [] ->
			(*Printf.eprintf "** false\n"; flush_all ();*)
			raise Exit (* indicating ⊥ (clause {}) has been generated *)
		    | disj3 ->
			let added', resolved' =
			  match simp_safe (Ldl_disj disj3) with
			  | Ldl_atomic "false" | Ldl_disj [] -> raise Exit
			  | Ldl_atomic "true"  | Ldl_conj [] -> added, resolved @ [k1, k2]
			  | c' -> added @ [c'], resolved @ [k1, k2]
			in added', resolved'
		  with Not_found -> added, resolved @ [k1, k2]
	      in added, resolved, j + 1)
	    (added, resolved, 0) clauses
	in added, resolved, i + 1)
      ([], resolved, 0) clauses in

  let mem c clauses =
    List.mem c clauses in
  let clauses' =
    List.fold_left
      (fun rslt c ->
	let c = simp_safe c in if mem c rslt then rslt else rslt @ [c])
      clauses added in

  if clauses' = clauses
  then clauses
  else resolve_rec resolved' clauses'

(* ================================================================================
   simp
   ================================================================================
 *)

let simp_resolve f =
  let tt = Ldl_atomic "true" and ff = Ldl_atomic "false" in
  if resolve (Ldl_neg f) |> flatten = ff then tt else
  let g = resolve f |> flatten in
  g

(* simplifier for propositional formulas *)

let rec simp f =
  (*simp_rec f (simp1 f) |> simp_resolve |> simp1*)
  let g = simp_resolve f in simp_rec g (simp_safe g) 10
    
and simp_rec prev curr n =
  if n = 0 then curr else
  if prev = curr
  then curr
  else simp_rec curr (simp_safe curr) (n - 1)

(* ================================================================================
   simplifiers for ldl formulas
   ================================================================================
 *)

(* canonicalize does no simplification
   but just apply simp_flatten into the entire propositional parts of a modal formula
 *)
let rec canonicalize f =
  (*canonicalize_rec (simp f)*)
  canonicalize_rec (simp_flatten f)

and canonicalize_rec f =
  match f with
  | Ldl_atomic _ -> f
  | Ldl_neg f' -> Ldl_neg (canonicalize f')
  | Ldl_conj fs -> Ldl_conj (List.map canonicalize fs)
  | Ldl_disj fs -> Ldl_disj (List.map canonicalize fs)
  | Ldl_impl (f', g) -> Ldl_impl ((canonicalize f'), canonicalize g)
  | Ldl_modal (m, r, f') ->
      Ldl_modal (m, canonicalize_path r, canonicalize f')
  | _ -> f

and canonicalize_path r =
  match r with
  | Path_prop f when propositional f -> Path_prop (canonicalize f)
  | Path_prop f -> Path_prop f
  | Path_seq [r'] -> canonicalize_path r'
  | Path_seq ((Path_seq rs) :: rs') -> canonicalize_path (Path_seq (rs @ rs'))
  | Path_seq rs -> Path_seq (List.map canonicalize_path rs)
  | Path_sum [r'] -> canonicalize_path r'
  | Path_sum rs -> Path_sum (List.map canonicalize_path rs)
  | Path_test f -> Path_test (canonicalize f)
  | Path_star r' -> Path_star (canonicalize_path r')
  | _ -> r    

let rec nnf f =
  match f with
  | Ldl_atomic a -> f

  | Ldl_neg (Ldl_atomic a) -> f
  | Ldl_neg (Ldl_neg f') -> nnf f'
  | Ldl_neg (Ldl_conj fs) -> nnf (Ldl_disj (List.map (fun f' -> Ldl_neg f') fs))
  | Ldl_neg (Ldl_disj fs) -> nnf (Ldl_conj (List.map (fun f' -> Ldl_neg f') fs))
  | Ldl_neg (Ldl_impl (f', g)) -> nnf (Ldl_conj [f'; Ldl_neg g])

  | Ldl_neg (Ldl_modal (Mod_ex, p, g)) -> nnf (Ldl_modal (Mod_all, p, Ldl_neg g))
  | Ldl_neg (Ldl_modal (Mod_all, p, g)) -> nnf (Ldl_modal (Mod_ex, p, Ldl_neg g))

  | Ldl_conj fs -> Ldl_conj (List.map nnf fs)
  | Ldl_disj fs -> Ldl_disj (List.map nnf fs)
  | Ldl_impl (f', g) -> Ldl_impl (nnf f', nnf g)

  | Ldl_modal (m, p, f') -> Ldl_modal (m, p, nnf f')

