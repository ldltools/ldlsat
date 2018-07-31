(* $Id: re2mso.ml,v 1.5 2018/01/11 01:06:37 sato Exp sato $ *)

open Re
open Mso

(* ================================================================================
   helper functions
   ================================================================================
 *)

let newsym = Mso.newsym

(* *)
let rec unbound1 f =
  let rslt : string list = unbound1_rec [] [] f
  in List.sort_uniq compare rslt

and unbound1_rec bound rslt = function
  | Mso_atomic _ -> rslt
  | Mso_neg f' -> unbound1_rec bound rslt f'
  | Mso_conj fs | Mso_disj fs ->
      List.fold_left (fun rslt' f' -> unbound1_rec bound rslt' f') rslt fs
  | Mso_impl (f1, f2) ->
      unbound1_rec bound (unbound1_rec bound rslt f1) f2

  | Mso_app (_, args) ->
      List.fold_left
	(fun rslt' -> function
	  | Tm1 tm1 -> unbound1_term1 bound rslt' tm1
	  | Tm2 tm2 -> failwith "unbound1_rec(app)")
	rslt args
  | Mso_mem (tm1, tm2) -> unbound1_term1 bound rslt tm1
  | Mso_comp1 (op, tm1, tm1') ->
      unbound1_term1 bound (unbound1_term1 bound rslt tm1) tm1'
  | Mso_comp2 _ -> failwith "unbound1_rec:comp2"

  | Mso_all1 fn ->
      let x = newsym "_p" in unbound1_rec (bound @ [x]) rslt (fn (Tm1_var x))
  | Mso_all2 fn -> failwith "unbound1_rec:all2"
  | Mso_ex1 fn ->
      let x = newsym "_p" in unbound1_rec (bound @ [x]) rslt (fn (Tm1_var x))
  | Mso_ex2 fn -> failwith "unbound1_rec:ex2"

and unbound1_term1 bound rslt = function
  | Tm1_var x when List.mem x bound -> rslt
  | Tm1_var "$" -> rslt
  | Tm1_var x -> rslt @ [x]
  | Tm1_int i -> rslt
  | Tm1_exp (op, arg1, arg2) -> unbound1_term1 bound (unbound1_term1 bound rslt arg1) arg2
  | Tm1_app (name, args) ->
      List.fold_left (fun rslt' arg -> unbound1_term1 bound rslt' arg) rslt args

and unbound1_term2 bound rslt = function
  | Tm2_var x when List.mem x bound -> rslt
  | Tm2_var x -> rslt @ [x]
  | _ -> failwith "unbound1_term2"
 
(* *)
let rec find_props (p : Re.prop) =
  List.sort compare (find_props_rec [] p)

and find_props_rec rslt = function
  | Prop_atomic a when List.mem a rslt -> rslt
  | Prop_atomic a when List.mem a ["true"; "false"; "last"] -> rslt
  | Prop_atomic a -> rslt @ [a]

  | Prop_neg p -> find_props_rec rslt p
  | Prop_conj ps | Prop_disj ps ->
      List.fold_left (fun rslt' p -> find_props_rec rslt' p) rslt ps
  | Prop_impl (p1, p2) ->
      List.fold_left (fun rslt' p -> find_props_rec rslt' p) rslt [p1; p2]

(* subst1_term (Tm1_var x) tm1 tm -> tm' *)
let rec subst1_term (x : string) (tm : term1) = function
  | Tm1_var y when y = x -> tm
  | Tm1_var y -> Tm1_var y
  | Tm1_int i -> Tm1_int i
  | Tm1_exp (op, arg1, arg2) ->
      Tm1_exp (op, (subst1_term x tm arg1), subst1_term x tm arg2)
  | Tm1_app (name, args) ->
      Tm1_app (name, List.map (subst1_term x tm) args)

(* subst1 (Tm1_var x) tm1 f -> f' *)
let rec subst1 (x : string) (tm : term1) f =
  match f with
  | Mso_atomic _ -> f
  | Mso_neg f' -> Mso_neg (subst1 x tm f')
  | Mso_conj fs -> Mso_conj (List.map (subst1 x tm) fs)
  | Mso_disj fs -> Mso_disj (List.map (subst1 x tm) fs)
  | Mso_impl (f1, f2) -> Mso_impl ((subst1 x tm f1), subst1 x tm f2)

  | Mso_app (pred, args) ->
      let args' : term list =
	List.map (function Tm1 tm1 -> Tm1 (subst1_term x tm tm1) | Tm2 tm2 -> Tm2 tm2) args
      in Mso_app (pred, args')
  | Mso_mem (tm1, tm2) -> Mso_mem ((subst1_term x tm tm1), tm2)
  | Mso_comp1 (op, tm1, tm1') -> Mso_comp1 (op, (subst1_term x tm tm1), subst1_term x tm  tm1')
  | Mso_comp2 _ -> f

  | Mso_all1 fn -> Mso_all1 (fun tm1 -> subst1 x tm (fn tm1))
  | Mso_all2 fn -> Mso_all2 (fun tm2 -> subst1 x tm (fn tm2))
  | Mso_ex1 fn -> Mso_ex1 (fun tm1 -> subst1 x tm (fn tm1))
  | Mso_ex2 fn -> Mso_ex2 (fun tm2 -> subst1 x tm (fn tm2))

let rec subst1_pred x tm = function
  | Pred_prop prop -> Pred_prop (subst1 x tm prop)
  | Pred_abs1 fn -> Pred_abs1 (fun _p -> subst1_pred x tm (fn _p))
  | Pred_abs2 fn -> Pred_abs2 (fun _P -> subst1_pred x tm (fn _P))

(* (name, p) in ps -- detects MSO predicates that are already declared *)
let rec find_pred (p : pred) = function
  | [] -> raise Not_found
  | (Decl_pred (name, p')) :: _ when pred_equal p p' -> name, p'
  | _ :: rest -> find_pred p rest


(* ================================================================================
   re -> mso
   ================================================================================
 *)

(* re2mso e -> decls *)
let rec re2mso (e : re) =
  (* re e -> mso f *)
  let p0 = newsym "_p" in
  let decls, (pairs : (re * formula) list ) =
    match e with
    | Re_inter es ->
	List.fold_left
	  (fun (decls', fs') e ->
	    (*let q = newsym "_p" in*)
	    (*
	    let decls1, ps, f1 =
	      (* case: p <= max ($) *)
	      let decls11, ps11, f11 = re2mso_rec [] [] (p0, None) false e in
	      (* case: p = max ($) + 1 *)
	      let decls12, ps12, f12 = re2mso_rec [] [] (p0, None) true e in
	      decls11 @ decls12, ps11 @ ps12, split_cases0 f11 f12
	     *)
	    let decls1, ps, f1 = re2mso_rec [] [] (p0, None) e
	    in
	    (decls' @ decls1), fs' @ [e, f1])
	  ([], []) es
    | _ -> 
	(*let q = newsym "_p" in*)
	(*
	let decls', ps, f =
	  (* case: p <= max ($) *)
	  let decls11, ps11, f11 = re2mso_rec [] [] (p0, None) false e in
	  (* case: p = max ($) + 1 *)
	  let decls12, ps12, f12 = re2mso_rec [] [] (p0, None) true e in
	  (*decls11 @ decls12, ps11 @ ps12, split_cases0 f11 f12*)
	  decls11 @ decls12, ps11 @ ps12, split_cases0 f11 f12
	 *)
	let decls', ps, f = re2mso_rec [] [] (p0, None) e
	in
	(*print_formula (fun s -> output_string stderr s; flush_all ()) f;*)
	decls', [e, f] in

  (* post-processing *)
  let vars1 =
    List.sort_uniq compare
      (List.fold_left (fun rslt -> function Decl_var1 xs -> rslt @ xs | _ -> rslt) [] decls)
  and vars2 =
    List.sort_uniq compare
      (List.fold_left (fun rslt -> function Decl_var2 xs -> rslt @ xs | _ -> rslt) [] decls) in

  (*
  let last =
    (* pred last (var1 p) = p = max ($);
     *)
    Pred_abs1 (fun _p ->
    Pred_prop (Mso_comp1 (Comp_eq, _p, Tm1_app ("max", [Tm1_var "$"])))) in
   *)
  let consec =
    (* macro consecutive_in_set (var1 p, var1 q, var2 P) =
       p < q & p in P & q in P & all1 r: p < r & r < q => r notin P;
     *)
    Pred_abs1 (fun _p -> Pred_abs1 (fun _q -> Pred_abs2 (fun _P ->
    Pred_prop (Mso_conj [Mso_comp1 (Comp_lt, _p, _q);
			 Mso_mem (_p, _P); Mso_mem (_q, _P);
			 Mso_all1 (fun _r ->
			   Mso_impl (Mso_conj [Mso_comp1 (Comp_lt, _p, _r);
					       Mso_comp1 (Comp_lt, _r, _q)],
				     Mso_neg (Mso_mem (_r, _P))))]))))
  in
  let decls0 =
    [Decl_macro ("consecutive_in_set", consec)] in
  let decls' =
    [Decl_var2 vars2; Decl_var1 vars1]
    @ decls0
    @ List.filter (function Decl_var1 _ | Decl_var2 _ -> false | _ -> true) decls
  in

  (* {(e, f)} *)
  let pairs' =
    List.map
      (fun pair ->
	let f1 = subst1 p0 (Tm1_int 0) (snd pair) in
	let fv = unbound1 f1 in
	let f2 = List.fold_left (fun rslt x -> Mso_ex1 (fun p -> subst1 x p rslt)) f1 fv
	in (fst pair), f2)
      pairs in
  let decls'' =
    List.fold_left
      (fun rslt (e, f) -> rslt @ [Decl_comment (Re.string_of_re e); Decl_formula f])
      decls' pairs'
  in Decl_comment (Re.string_of_re e) :: decls''

(* re2mso_rec decls ps (p, q_opt) e -> (decls', ps', f)
   - decls: Mso.decl list
     predicates/macros that need to be declared in the top level
   - ps: list of position variables that need to be quantified
     ps is extended in the Re_seq/Re_test/Re_modal cases
   - p, q_opt: p and q_opt points to the start/end positions of e
     case q_opt = None: q is unused.
     case q_opt = Some q: q is referred to elsewhere and needs to be instantiated
   - e: RE expression to convert
 *)
and re2mso_rec (decls : decl list) (ps : string list) (p, q_opt) (e : re) =
  match e with
  | Re_prop (Prop_atomic "last") when q_opt = None ->
      assert (q_opt = None);
      decls, ps, re2mso_prop p (Prop_atomic "last")

  | Re_prop prop when q_opt = None ->
      let f = re2mso_prop p prop in
      let decls' = decls @ [Decl_var2 (find_props prop)] in
      decls', ps, f
  | Re_prop prop ->
      (* prop appears in a Re_seq expression *)
      assert (q_opt <> None);
      let q = match q_opt with Some q -> q in
      let f = re2mso_prop p prop in
      let g = Mso_comp1 (Comp_eq, (Tm1_var q), (Tm1_exp (Arith_add, (Tm1_var p), Tm1_int 1))) in
      (* g = (q = p + 1) *)
      let decls' = decls @ [Decl_var2 (find_props prop)] in
      decls', ps, Mso_conj [f; g]

  | Re_neg e' ->
      let decls', ps', f' = re2mso_rec decls ps (p, q_opt) e' in
      decls', ps, Mso_neg f'

  | Re_union es -> re2mso_union decls ps (p, q_opt) [] es
  | Re_inter es -> re2mso_inter decls ps (p, q_opt) [] es

  | Re_seq [e'] ->
      re2mso_rec decls ps (p, q_opt) e'
  | Re_seq (e' :: rest) ->
      (* (e'; rest)(p, q) -> e'(p, p') ∧ rest(p', q) *)
      let p' = newsym "_p" in

      (* e' *)
      let decls1, ps1, f1 = re2mso_rec decls [] (p, Some p') e' in

      (* rest *)
      let decls2, ps2, f2 = re2mso_rec decls1 [] (p', q_opt) (Re_seq rest) in

      let decls', ps', f' =
	decls2,
	ps @ ps1 @ [p'] @ ps2,
	Mso_conj [f1; f2]
      in
      decls', ps', f'

  | Re_star e' ->
      (* star(e', p, q)
	 = ∃P: p ∈ P ∧ q ∈ P ∧ ∀r, r': consecutive(r, r', P) → e'(r, r') *)
      assert (q_opt <> None);
      let q = match q_opt with Some q -> q in

      (* pred1: iter (r, r') *)
      let r = newsym "_p" and r' = newsym "_p" in
      let decls1, ps1, f = re2mso_rec decls [] (r, Some r') e' in
        (* ps1 = pos vars (incl. r and r') in f that need to be quantifed *)
      let pred1_args = List.filter (fun x -> x <> r && x <> r') (unbound1 f) in
        (* pred1_args = pos vars in f that are not quantified by all1/ex1 *)
      let rec bind_ex f = function
	| [] -> f
	| x :: rest -> bind_ex (Mso_ex1 (fun _p -> subst1 x _p f)) rest in
      let f' : formula = bind_ex f (List.rev pred1_args) in
        (* quantify all unbound pos vars in f with "ex1" *)
      let pred1 =
	(* pred1 (_r, _r') *)
	Pred_abs1 (fun _r -> Pred_abs1 (fun _r' ->
	  Pred_prop (subst1 r' _r' (subst1 r _r f'))))
      in

      (* check if pred1 is already included in decls *)
      let (pred1_name, pred1), decls1 =
	try (find_pred pred1 decls1), decls1
	with Not_found ->
	  let pred1_name = newsym "_iter"
	  in (pred1_name, pred1), decls1 @ [Decl_pred (pred1_name, pred1)]
      in
      (*Printf.eprintf ";; %s\n" pred1_name; flush_all ();*)

      (* pred2: star (p, q) *)
      let prop2 =
	(* ∃P: p ∈ P ∧ q ∈ P ∧ ∀r, r': consecutive(r, r', P) → e'(r, r') *)
	Mso_ex2 (fun _P ->
	Mso_conj [Mso_mem ((Tm1_var p), _P);
		  Mso_mem ((Tm1_var q), _P);
		  Mso_comp1 (Comp_le, Tm1_var p, Tm1_var q);
		  Mso_all1 (fun _r ->
		  Mso_all1 (fun _r' ->
		  Mso_impl (Mso_app ("consecutive_in_set", [Tm1 _r; Tm1 _r'; Tm2 _P]),
			    Mso_app (pred1_name, [Tm1 _r; Tm1 _r']))))]) in
      let pred2 =
	Pred_abs1 (fun _p ->
	Pred_abs1 (fun _q ->
	  subst1_pred q _q (subst1_pred p _p (Pred_prop prop2))))
      in

      (* check if pred2 is already included in decls *)
      let (pred2_name, pred2), decls2 =
	try (find_pred pred2 decls1), decls1
	with Not_found ->
	  let pred2_name = newsym "_star"
	  in (pred2_name, pred2), decls1 @ [Decl_pred (pred2_name, pred2)]
      in
      (*Printf.eprintf ";; %s\n" pred2_name; flush_all ();*)
      decls2, ps, (Mso_app (pred2_name, List.map (fun x -> Tm1 (Tm1_var x)) [p; q]))

  | Re_test e' ->
      (* e'? -> e'(p, q) & p = q *)
      assert (q_opt <> None);
      let q = match q_opt with Some q -> q in
      let p' = newsym "_p" in
      let decls', ps', f = re2mso_rec decls [] (p, Some p') e' in
      decls', (ps @ ps' @ [p']), Mso_conj [f; Mso_comp1 (Comp_eq, Tm1_var p, Tm1_var q)]

  | Re_modal (Mod_ex, e1, e2) ->
      (* π ⊨ ∃π1: π1 ∈ e1 & |π1| < |π| & π2 ⊨ e2 where π = π1 . π2
	 = Mso_ex1 (fun p' -> (re2mso decls p e1) & p' <= max ($) & (re2mso decls p' e2))
       *)
      (*assert (q_opt <> None);
      let q = match q_opt with Some q -> q in
       *)
      let p' = newsym "_p" in
      (* p' <= max ($) *)
      let f3 = Mso_comp1 (Comp_le, (Tm1_var p'), Tm1_app ("max", [Tm1_var "$"])) in

      let decls11, ps11, f11 = re2mso_rec decls [] (p, Some p') e1 in
      let decls12, ps12, f12 = re2mso_rec decls11 [] (p', q_opt) e2 in

      (* p_is_last <=> p = max ($) + 1 *)
      (* case: tm1 <= max ($) *)

      let decls', ps', f' =
	decls12,
	ps11 @ [p'] @ ps12,
	Mso_conj [f3; f11; f12]
      in

      let f'' =
	List.fold_left
	  (fun f' p' -> Mso_ex1 (fun pos -> subst1 p' pos f'))
	  f' (List.rev ps')
      in
      decls', ps, f''

  | Re_modal (Mod_all, e1, e2) ->
      let e' = Re_neg (Re_modal (Mod_ex, e1, Re_neg e2))
      in re2mso_rec decls ps (p, q_opt) e'

  | _ -> failwith ("re2mso_rec: " ^ string_of_re e)

and re2mso_prop pos = function
  | Prop_atomic "last" -> Mso_app ("_last", [Tm1 (Tm1_var pos)])
  | Prop_atomic "true" -> Mso_atomic "true"
  | Prop_atomic "false" -> Mso_atomic "false"
  | Prop_atomic a -> Mso_mem ((Tm1_var pos), Tm2_var a)

  | Prop_neg p -> Mso_neg (re2mso_prop pos p)
  | Prop_conj ps -> Mso_conj (List.map (re2mso_prop pos) ps)
  | Prop_disj ps -> Mso_disj (List.map (re2mso_prop pos) ps)
  | Prop_impl (p1, p2) ->Mso_impl ((re2mso_prop pos p1), re2mso_prop pos p2)
  | _ -> failwith "re2mso_prop"

and re2mso_union decls ps (p, q) fs = function
  | [] -> decls, ps, Mso_disj fs
  | e :: es ->
      let decls1, ps1, f1 = re2mso_rec decls [] (p, q) e
      in re2mso_union decls1 (ps @ ps1) (p, q) (fs @ [f1]) es

and re2mso_inter decls ps (p, q) fs = function
  | [] -> decls, ps, Mso_conj fs
  | e :: es ->
      let decls1, ps1, f1 = re2mso_rec decls [] (p, q) e
      in re2mso_inter decls1 (ps @ ps1) (p, q) (fs @ [f1]) es
