(* $Id: mso.ml,v 1.5 2018/01/11 01:06:37 sato Exp sato $ *)
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

type formula =
  | Mso_atomic of string
  | Mso_neg of formula
  | Mso_conj of formula list
  | Mso_disj of formula list
  | Mso_impl of formula * formula

  | Mso_app of string * term list
  | Mso_mem of term1 * term2
  | Mso_comp1 of comp_op * term1 * term1
  | Mso_comp2 of comp_op * term2 * term2

  | Mso_all1 of (term1 -> formula)
  | Mso_all2 of (term2 -> formula)
  | Mso_ex1 of (term1 -> formula)
  | Mso_ex2 of (term2 -> formula)

  (* internal *)
(*
  | Mso_unbound1 of (string * formula)
  | Mso_unbound2 of (string * formula)
*)

and term =
  | Tm1 of term1
  | Tm2 of term2

(* 1st order -- position variable *)
and term1 =
  | Tm1_var of string
  | Tm1_int of int
  | Tm1_exp of arith_op * term1 * term1
  | Tm1_app of string * term1 list

(* 2nd order *)
and term2 =
  | Tm2_var of string

(*
and exp =
  | Exp_term1 of term1
  | Exp_term2 of term2
  | Exp_formula of formula
 *)

and comp_op =
  | Comp_eq
  | Comp_gt | Comp_lt
  | Comp_ge | Comp_le

and arith_op =
  | Arith_add
  | Arith_sub

(*[@@deriving show, eq]*)
[@@deriving show]

(* predicate or macro *)
type pred =
  | Pred_prop of formula
  | Pred_abs1 of (term1 -> pred)
  | Pred_abs2 of (term2 -> pred)

(*[@@deriving show, eq]*)
[@@deriving show]

type decl =
  | Decl_var1 of string list
  | Decl_var2 of string list
  | Decl_pred of string * pred
  | Decl_macro of string * pred
  | Decl_formula of formula
  | Decl_comment of string

[@@deriving show]

type prog =
    decl list

[@@deriving show]

let _symcount = ref 0
let newsym prefix =
  incr _symcount;
  (*Printf.eprintf "(%d)" !_symcount; flush_all ();*)
  prefix ^ "_" ^ (string_of_int !_symcount)

(** equality *)

let rec formula_equal (f1 : formula) (f2 : formula) =
  match f1, f2 with
  | Mso_atomic a1, Mso_atomic a2 when a1 = a2 -> true
  | Mso_neg g1, Mso_neg g2 -> formula_equal g1 g2
  | Mso_conj [], Mso_conj [] | Mso_disj [], Mso_disj [] -> true
  | Mso_conj (g1 :: gs1), Mso_conj (g2 :: gs2) when formula_equal g1 g2 ->
      formula_equal (Mso_conj gs1) (Mso_conj gs2)
  | Mso_disj (g1 :: gs1), Mso_disj (g2 :: gs2) when formula_equal g1 g2 ->
      formula_equal (Mso_disj gs1) (Mso_disj gs2)
  | Mso_impl (g11, g12), Mso_impl (g21, g22) ->
      formula_equal g11 g21 && formula_equal g12 g22
  | Mso_app (fn1, []), Mso_app (fn2, []) when fn1 = fn2 -> true
  | Mso_app (fn1, arg1 :: args1), Mso_app (fn2, arg2 :: args2) when fn1 = fn2 ->
      term_equal arg1 arg2 && formula_equal (Mso_app (fn1, args1)) (Mso_app (fn2, args2))
  | Mso_mem (p1, s1), Mso_mem (p2, s2) -> term1_equal p1 p2 && term2_equal s1 s2
  | Mso_comp1 (op1, p11, p12), Mso_comp1 (op2, p21, p22) when op1 = op2 ->
      term1_equal p11 p21 && term1_equal p12 p22
  | Mso_comp2 (op1, s11, s12), Mso_comp2 (op2, s21, s22) when op1 = op2 ->
      term2_equal s11 s21 && term2_equal s12 s22
  | Mso_all1 fn1, Mso_all1 fn2 ->
	let tm = Tm1_var (newsym "_p") in formula_equal (fn1 tm) (fn2 tm)
  | Mso_all2 fn1, Mso_all2 fn2 ->
	let tm = Tm2_var (newsym "_P") in formula_equal (fn1 tm) (fn2 tm)
  | Mso_ex1 fn1, Mso_ex1 fn2 ->
	let tm = Tm1_var (newsym "_p") in formula_equal (fn1 tm) (fn2 tm)
  | Mso_ex2 fn1, Mso_ex2 fn2 ->
	let tm = Tm2_var (newsym "_P") in formula_equal (fn1 tm) (fn2 tm)
  | _ -> false

and pred_equal (p1 : pred) (p2 : pred) =
  match p1, p2 with
  | Pred_prop f1, Pred_prop f2 ->
      formula_equal f1 f2
  | Pred_abs1 fn1, Pred_abs1 fn2 ->
      let tm = Tm1_var (newsym "_p") in pred_equal (fn1 tm) (fn2 tm)
  | Pred_abs2 fn1, Pred_abs2 fn2 ->
      let tm = Tm2_var (newsym "_P") in pred_equal (fn1 tm) (fn2 tm)
  | _ -> failwith "pred_equal"

and term_equal tm1 tm2 =
  match tm1, tm2 with
  | Tm1 tm1', Tm1 tm2' -> term1_equal tm1' tm2'
  | Tm2 tm1', Tm2 tm2' -> term2_equal tm1' tm2'
  | _ -> false

and term1_equal tm1 tm2 =
  match tm1, tm2 with
  | Tm1_var x1, Tm1_var x2 when x1 = x2 -> true
  | Tm1_int i1, Tm1_int i2 when i1 = i2 -> true
  | Tm1_exp (op1, p11, p12), Tm1_exp (op2, p21, p22) when op1 = op2 ->
      term1_equal p11 p21 && term1_equal p12 p22
  | Tm1_app (fn1, []), Tm1_app (fn2, []) when fn1 = fn2 -> true
  | Tm1_app (fn1, arg1 :: args1), Tm1_app (fn2, arg2 :: args2) when fn1 = fn2 ->
      term1_equal arg1 arg2 && term1_equal (Tm1_app (fn1, args1)) (Tm1_app (fn2, args2))
  | _ -> false

and term2_equal tm1 tm2 =
  match tm1, tm2 with
  | Tm2_var x1, Tm2_var x2 when x1 = x2 -> true
  | _ -> false

(** pretty-printing *)

let _preamble =
  (*"m2l-str;\n";*)
  (*
  "ws1s;\n"
  ^ "var2 $ where ~ex1 p where true: p notin $ & p + 1 in $;\n"
  ^ "allpos $;\n"
  ^ "defaultwhere1 (p) = p in $;\n"
  ^ "defaultwhere2 (P) = P sub $;\n"
  ^ "macro last (var1 p) = p = max ($);\n"
   *)

  (*
  "ws1s;\n"
  ^ "var2 $ where ~ex1 p where true: p notin $ & p + 1 in $;\n"
  ^ "allpos $;\n"
  ^ "defaultwhere1 (p) = p in $ | p = max ($) + 1;\n"
  ^ "defaultwhere2 (P) = P sub $;\n"
  ^ "macro last (var1 p) = p <= max ($) + 1 => p = max ($);\n"
  ^ "macro _true (var1 p) = p in $;\n"
  ^ "macro _false (var1 p) = p notin $;\n"
   *)

  (* cf. mona 1.4 user manual sec6.6 *)
  "ws1s;\n"
  ^ "var2 $ where ~ex1 p where true: p notin $ & p + 1 in $;\n"
  ^ "allpos $;\n"
  ^ "defaultwhere1 (p) = all1 r: r < p => r in $;\n"
  ^ "defaultwhere2 (P) = all1 p: p in P => all1 r: r < p => r in $;\n"
  ^ "macro _last (var1 p) = p = max ($) & $ ~= {};\n"
  ^ "$ ~= {};\n"

let rec string_of_mso p =
  let str = ref "" in
  let concat str' = str := !str ^ str' in
  print_mso concat ~verbose:false p;
  !str

and print_mso out ?(verbose = false) ?(preamble = _preamble) decls =
  (* preamble *)
  out preamble;

  (* decls *)
  List.iter (print_decl out ~verbose) decls;

  ()

and print_decl out ?(verbose=false) = function
  | Decl_var1 [] -> ()
  | Decl_var1 xs ->
      out ("var1 " ^ (List.hd xs));
      List.iter (fun x -> out (", " ^ x)) (List.tl xs);
      out ";\n"
  | Decl_var2 [] -> ()
  | Decl_var2 xs when xs <> [] ->
      out ("var2 " ^ (List.hd xs));
      List.iter (fun x -> out (", " ^ x)) (List.tl xs);
      out ";\n"
  | Decl_pred (name, pred) ->
      let args = pred_args [] pred in
      out ("pred " ^ name ^ " (");
      print_pred_args out args pred;
      out ") =\n  ";
      print_pred_body out args pred;
      out ";\n";

  | Decl_macro (name, pred) ->
      let args = pred_args [] pred in
      out ("macro " ^ name ^ " (");
      print_pred_args out args pred;
      out ") =\n  ";
      print_pred_body out args pred;
      out ";\n";
  
  | Decl_formula f ->
      print_formula out f;
      out ";\n";

  | Decl_comment str when verbose ->
      out "# "; out str; out "\n"
  | Decl_comment str ->
      ()

and pred_args rslt = function
  | Pred_prop _ -> rslt
  | Pred_abs1 fn ->
      let x1 = newsym "_p" in pred_args (rslt @ [x1]) (fn (Tm1_var x1))
  | Pred_abs2 fn ->
      let x2 = newsym "_P" in pred_args (rslt @ [x2]) (fn (Tm2_var x2))

and print_pred_args out args = function
  | Pred_prop _ -> ()
  | Pred_abs1 fn ->
      let x1 = List.hd args in
      out ("var1 " ^ x1);
      if List.length args > 1 then out ", ";
      print_pred_args out (List.tl args) (fn (Tm1_var x1))
  | Pred_abs2 fn ->
      let x2 = List.hd args in
      out ("var2 " ^ x2);
      if List.length args > 1 then out ", ";
      print_pred_args out (List.tl args) (fn (Tm2_var x2))

and print_pred_body out args = function
  | Pred_prop f -> print_formula out f
  | Pred_abs1 fn ->
      let x1 = List.hd args in
      print_pred_body out (List.tl args) (fn (Tm1_var x1))
  | Pred_abs2 fn ->
      let x2 = List.hd args in
      print_pred_body out (List.tl args) (fn (Tm2_var x2))

and print_term out = function
  | Tm1 tm1 -> print_term1 out tm1
  | Tm2 tm2 -> print_term2 out tm2

and print_term1 out tm1 =
  match tm1 with
  | Tm1_var x -> out x
  | Tm1_int i -> out (string_of_int i)
  | Tm1_exp (op, arg1, arg2) ->
      print_term1 out arg1;
      out " "; print_arith_op out op; out " ";
      print_term1 out arg2
  | Tm1_app (fn, args) ->
      out (fn ^ " (");
      print_term1 out (List.hd args);
      List.iter	(fun tm -> out ", "; print_term1 out tm) (List.tl args);
      out ")"

and print_term2 out tm2 =
  match tm2 with
  | Tm2_var x -> out x
  | _ -> failwith "print_term2"

and print_comp_op out op =
  let tbl = [Comp_eq, "="; Comp_gt, ">"; Comp_lt, "<"; Comp_ge, ">="; Comp_le, "<="]
  in out (List.assoc op tbl)

and print_arith_op out op =
  let tbl = [Arith_add, "+"; Arith_sub, "-"]
  in out (List.assoc op tbl)

and print_formula out f =
  match f with
  | Mso_atomic a ->
      out a
  | Mso_neg f' when formula_prec f' <= formula_prec f ->
      out "~"; print_formula out f'
  | Mso_neg f' ->
      out "~"; out "("; print_formula out f'; out ")"

  | Mso_conj [] ->
      assert (false);
  | Mso_conj (f' :: rest) ->
      if formula_prec f' <= formula_prec f
      then print_formula out f'
      else (out "("; print_formula out f'; out ")");
      List.iter
	(fun f' ->
	   out " & ";
	  if formula_prec f' <= formula_prec f
	  then print_formula out f'
	  else (out "("; print_formula out f'; out ")"))
	rest
  | Mso_disj [] ->
      assert (false);
  | Mso_disj (f' :: rest) ->
      if formula_prec f' <= formula_prec f
      then print_formula out f'
      else (out "("; print_formula out f'; out ")");
      List.iter
	(fun f' ->
	   out " | ";
	  if formula_prec f' <= formula_prec f
	  then print_formula out f'
	  else (out "("; print_formula out f'; out ")"))
	rest

  | Mso_impl (f1, f2) ->
      let impl = "=>" in
      let _ =
	match (formula_prec f1 < formula_prec f), (formula_prec f2 <= formula_prec f) with
	| false, false ->
	    out "("; print_formula out f1; out ")";
	    out (" " ^ impl ^ " ");
	    out "("; print_formula out f2; out ")"
	| false, true  ->
	    out "("; print_formula out f1; out ")";
	    out (" " ^ impl ^ " ");
	    print_formula out f2
	| true, false  ->
	    print_formula out f1;
	    out (" " ^ impl ^ " ");
	    out "("; print_formula out f2; out ")"
	| true, true   ->
	    print_formula out f1;
	    out (" " ^ impl ^ " ");
	    print_formula out f2
      in ()

  | Mso_app (pred, args) ->
      out pred;
      out " (";
      assert (args <> []);
      print_term out (List.hd args);
      List.iter (fun tm -> out ", "; print_term out tm) (List.tl args);
      out ")";

  | Mso_mem (tm1, tm2) ->
      print_term1 out tm1;
      out " in ";
      print_term2 out tm2
  | Mso_comp1 (op, tm1, tm1') ->
      print_term1 out tm1;
      out " "; print_comp_op out op; out " ";
      print_term1 out tm1'
  | Mso_comp2 (op, tm2, tm2') ->
      failwith "print_formula:comp2"

  | Mso_all1 fn ->
      let pos = newsym "_p" in
      out ("all1 " ^ pos ^ ": ");
      print_formula out (fn (Tm1_var pos))
  | Mso_all2 fn ->
      failwith "print_formula:all2"
  | Mso_ex1 fn ->
      let pos = newsym "_p" in
      out ("ex1 " ^ pos ^ ": ");
      print_formula out (fn (Tm1_var pos))
  | Mso_ex2 fn ->
      let _P = newsym "_P" in
      out ("ex2 " ^ _P ^ ": ");
      print_formula out (fn (Tm2_var _P))

  (* internal *)
(*
  | Mso_unbound1 (x, f) ->
      failwith "print_formula:unbound1"
  | Mso_unbound2 (x, f) ->
      failwith "print_formula:unbound2"
*)
  | _ ->
      failwith "print_formula:??"

(* precedence: neg < and < lor < implies *)
(* precedence: grouping (()) < *, ? < concat (;) < choice (+) *)
and formula_prec = function
  | Mso_atomic _ -> 0
  | Mso_neg _ -> 100
  | Mso_conj _ -> 200
  | Mso_disj _ -> 400
  | Mso_impl _ -> 500

  | Mso_app _ -> 0
  | Mso_mem _ -> 150
  | Mso_comp1 _ -> 150
  | Mso_comp2 _ -> 150

  | Mso_all1 _ -> 800
  | Mso_all2 _ -> 800
  | Mso_ex1 _ -> 800
  | Mso_ex2 _ -> 800

  (* internal *)
(*
  | Mso_unbound1 _ -> 500
  | Mso_unbound2 _ -> 500
 *)
