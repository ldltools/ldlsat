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
   predicates for distinguishing modal and propositional formulas
   ================================================================================
 *)

let rec modal_p f =
  not @@ propositional_p f

and propositional_p f =
  try propositional_p_rec f with Exit -> false

and propositional_p_rec f =
  match f with
  | _ when literal_p f -> true
  | Ldl_neg g -> propositional_p_rec g
  | Ldl_conj gs | Ldl_disj gs ->
      List.fold_left (fun b g -> b && propositional_p_rec g) true gs
  | Ldl_impl (g1, g2) -> (propositional_p_rec g1) && (propositional_p_rec g2)

  | Ldl_atomic "last" -> raise Exit
  | Ldl_modal _ -> raise Exit

  | _ ->
      assert false;
      false

(* literal = atomic formula or its negation *)
and literal_p = function
  | Ldl_atomic "last" -> false
  | Ldl_atomic _ -> true
  | Ldl_neg f -> literal_p f
  | Ldl_conj [] | Ldl_disj [] -> true
  | _ -> false

(* ================================================================================
   operations for modal formulas
   ================================================================================
 *)

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

(* canonicalize does no simplification
   but just apply simp_flatten into the entire propositional parts of a modal formula
 *)
let rec canonicalize f =
  (*canonicalize_rec (simp f)*)
  canonicalize_rec f

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
  | Path_prop f when propositional_p f -> Path_prop (canonicalize f)
  | Path_prop f -> Path_prop f
  | Path_seq [r'] -> canonicalize_path r'
  | Path_seq ((Path_seq rs) :: rs') -> canonicalize_path (Path_seq (rs @ rs'))
  | Path_seq rs -> Path_seq (List.map canonicalize_path rs)
  | Path_sum [r'] -> canonicalize_path r'
  | Path_sum rs -> Path_sum (List.map canonicalize_path rs)
  | Path_test f -> Path_test (canonicalize f)
  | Path_star r' -> Path_star (canonicalize_path r')
  | _ -> r    

(* ================================================================================
   propositional simplifier
   ================================================================================
 *)

module PropSimp = struct

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
(*
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
  let rec del_double_neg f =
    match f with Ldl_neg (Ldl_neg g) -> del_double_neg g | _ -> f
  in let f1, f2 = del_double_neg f1, del_double_neg f2
  in
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
	| _ -> failwith @@ "[simp_comp_literals:2] " ^ (string_of_formula f2)
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

(*
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
 *)

(* simp_clause *)
(*
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

let simp f =
  f |> simp_flatten |> simp_equiv |> simp_flatten
  (*f |> simp_equiv |> simp_flatten |> cnf |> simp_sort |> simp_uniq |> flatten*)
  (*f |> dnf |> simp_flatten |> dnf |> simp_sort |> simp_uniq*)
  (*f |> flatten |> simp_equiv |> resolve |> dnf |> simp_flatten |> simp_sort*)

end

(* ================================================================================
   simplifier
   ================================================================================
 *)

let simp f =
  if propositional_p f
  then
    PropSimp.simp f
  else
    canonicalize f
