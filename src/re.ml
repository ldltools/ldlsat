(* $Id: re.ml,v 1.3 2018/01/09 07:54:43 sato Exp $ *)
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
open Ldlsimp

type re =
  | Re_prop of prop
  | Re_neg of re
  | Re_union of re list
  | Re_inter of re list
  | Re_seq of re list
  | Re_star of re
  | Re_test of re
  | Re_modal of modality * re * re

and prop =
  | Prop_atomic of string
  | Prop_neg of prop
  | Prop_conj of prop list
  | Prop_disj of prop list
  | Prop_impl of prop * prop

[@@deriving show, yojson]
	
(* ================================================================================
   ldl -> re
   ================================================================================
 *)

let rec re_of_formula f =
  re_of_formula_rec (nnf f)

and re_of_formula_rec f =
  match f with
  | _ when propositional f -> Re_prop (prop_of_formula f)
  | Ldl_atomic "last" -> Re_prop (prop_of_formula f)  (* work-around*)
  | Ldl_neg f -> Re_neg (re_of_formula f)
  | Ldl_conj fs -> Re_inter (List.map re_of_formula_rec fs)
  | Ldl_disj fs -> Re_union (List.map re_of_formula_rec fs)
  | Ldl_impl (f', g) -> re_of_formula_rec (Ldl_disj [Ldl_neg f'; g])
  | Ldl_modal (m, p, f') -> Re_modal (m, (re_of_path p), re_of_formula_rec f')
  | _ -> invalid_arg ("re_of_formula_rec: " ^ Ldl.string_of_formula f)

and prop_of_formula = function
  | Ldl_atomic a -> Prop_atomic a
  | Ldl_neg f -> Prop_neg (prop_of_formula f)
  | Ldl_conj [] -> prop_of_formula (Ldl_atomic "true")
  | Ldl_conj fs -> Prop_conj (List.map prop_of_formula fs)
  | Ldl_disj [] -> prop_of_formula (Ldl_atomic "false")
  | Ldl_disj fs -> Prop_disj (List.map prop_of_formula fs)
  | Ldl_impl (f, g) -> Prop_impl ((prop_of_formula f), prop_of_formula g)
  | Ldl_modal (m, p, f) -> invalid_arg "prop_of_formula"

and re_of_path = function
  | Path_prop f -> Re_prop (prop_of_formula f)
  | Path_seq ps -> Re_seq (List.map re_of_path ps)
  | Path_sum ps -> Re_union (List.map re_of_path ps)
  | Path_star p -> Re_star (re_of_path p)
  | Path_test f -> Re_test (re_of_formula f)

(* ================================================================================
   pretty-printing
   ================================================================================
 *)

(* fancy symbols *)
let top, bot, neg, conj, disj, impl, forall, exists, mem, inter, union =
  if false
  then "top", "bot", "!", "&", "|", "->", "forall ", "exists ", "in", "&", "|"
  else
      (Printf.sprintf "%c%c%c" (Char.chr 0xe2) (Char.chr 0x8a) (Char.chr 0xa4)),
      (* ⊤ *)
      (Printf.sprintf "%c%c%c" (Char.chr 0xe2) (Char.chr 0x8a) (Char.chr 0xa5)),
      (* ⊥ *)
      (Printf.sprintf "%c%c" (Char.chr 0xc2) (Char.chr 0xac)),
      (* ¬ *)
      (Printf.sprintf "%c%c%c" (Char.chr 0xe2) (Char.chr 0x88) (Char.chr 0xa7)),
      (* ∧ *)
      (Printf.sprintf "%c%c%c" (Char.chr 0xe2) (Char.chr 0x88) (Char.chr 0xa8)),
      (* ∨ *)
      (Printf.sprintf "%c%c%c" (Char.chr 0xe2) (Char.chr 0x86) (Char.chr 0x92)),
      (* → *)
      (Printf.sprintf "%c%c%c" (Char.chr 0xe2) (Char.chr 0x88) (Char.chr 0x80)),
      (* ∀ *)
      (Printf.sprintf "%c%c%c" (Char.chr 0xe2) (Char.chr 0x88) (Char.chr 0x83)),
      (* ∃ *)
      (Printf.sprintf "%c%c%c" (Char.chr 0xe2) (Char.chr 0x88) (Char.chr 0x88)),
      (* ∈ *)
      (Printf.sprintf "%c%c%c" (Char.chr 0xe2) (Char.chr 0x88) (Char.chr 0xa9)),
      (* ∩ *)
      (Printf.sprintf "%c%c%c" (Char.chr 0xe2) (Char.chr 0x88) (Char.chr 0xaa))
      (* ∪ *)

let rec string_of_re e =
  let str = ref "" in
  let concat str' = str := !str ^ str' in
  print_re concat e;
  !str

and print_re out e =
  match e with
  | Re_prop p ->
      out "{"; print_prop out p; out "}"
  | Re_neg e' when re_prec e' <= re_prec e ->
      out neg; print_re out e'
  | Re_neg e' ->
      out (neg ^ "("); print_re out e'; out ")"
  | Re_inter [] -> out top
  | Re_inter [e'] when re_prec e' <= re_prec e -> print_re out e'
  | Re_inter [e'] -> out "("; print_re out e'; out ")"
  | Re_inter (e' :: es) when re_prec e' <= re_prec e ->
      print_re out e';
      out (" " ^ inter ^ " ");
      print_re out (Re_inter es)
  | Re_inter (e' :: es) ->
      out "("; print_re out e'; out ")";
      out (" " ^ inter ^ " ");
      print_re out (Re_inter es)

  | Re_union [] -> out bot
  | Re_union [e'] when re_prec e' <= re_prec e -> print_re out e'
  | Re_union [e'] -> out "("; print_re out e'; out ")"
  | Re_union (e' :: es) when re_prec e' <= re_prec e ->
      print_re out e';
      out (" " ^ union ^ " ");
      print_re out (Re_union es)
  | Re_union (e' :: es) ->
      out "("; print_re out e'; out ")";
      out (" " ^ union ^ " ");
      print_re out (Re_union es)

  | Re_seq [e'] when re_prec e' <= re_prec e ->
      print_re out e'
  | Re_seq [e'] ->
      out "("; print_re out e'; out ")"
  | Re_seq (e' :: es) when re_prec e' <= re_prec e ->
      print_re out e';
      out ".";
      print_re out (Re_seq es)
  | Re_seq (e' :: es) ->
      out "("; print_re out e'; out ")";
      out ".";
      print_re out (Re_seq es)

  | Re_star e' when re_prec e' <= re_prec e ->
      print_re out e'; out "*"
  | Re_star e' ->
      out "("; print_re out e'; out ")*"

  | Re_test e' ->
      out "("; print_re out e'; out ")?"

  | Re_modal (Mod_all, e1, e2) ->
      out (forall ^ "p: ");
      out ("p " ^ mem ^ " "); print_re out e1;
      out (" " ^ impl ^ " ");
      out "p."; print_re out e2

  | Re_modal (Mod_ex, e1, e2) ->
      out (exists ^ "p " ^ mem ^ " "); print_re out e1; out ": ";
      out "p.";
      out "("; print_re out e2; out ")"

  | _ ->
      failwith ("print_re: " ^ show_re e)

(* precedence: grouping (()) < *, ? < concat (;) < choice (+) *)
and re_prec = function
  | Re_prop _ -> 0
  | Re_neg _ -> 100
  | Re_inter _ -> 200
  | Re_union _ -> 400
  | Re_seq _ -> 300
  | Re_star _ -> 30
  | Re_test _ -> 50
  | Re_modal _ -> 500

and print_prop out p =
  match p with
  | Prop_atomic a ->
      out a

  | Prop_neg p' when prop_prec p' <= prop_prec p ->
      out neg; print_prop out p'
  | Prop_neg p' ->
      out neg; out "("; print_prop out p'; out ")"

  | Prop_conj [p'] when prop_prec p' <= prop_prec p ->
      print_prop out p'
  | Prop_conj [p'] ->
      out "("; print_prop out p'; out ")"
  | Prop_conj (p' :: ps) when prop_prec p' <= prop_prec p ->
      print_prop out p';
      out (" " ^ conj ^ " ");
      print_prop out (Prop_conj ps)
  | Prop_conj (p' :: ps) ->
      out "("; print_prop out p'; out ")";
      out (" " ^ conj ^ " ");
      print_prop out (Prop_conj ps)

  | Prop_disj [p'] when prop_prec p' <= prop_prec p ->
      print_prop out p'
  | Prop_disj [p'] ->
      out "("; print_prop out p'; out ")"
  | Prop_disj (p' :: ps) when prop_prec p' <= prop_prec p ->
      print_prop out p';
      out (" " ^ disj ^ " ");
      print_prop out (Prop_disj ps)
  | Prop_disj (p' :: ps) ->
      out "("; print_prop out p'; out ")";
      out (" " ^ disj ^ " ");
      print_prop out (Prop_disj ps)

  | Prop_impl (p', q) ->
      let _ =
	match (prop_prec p' < prop_prec p), (prop_prec q <= prop_prec p) with
	| false, false ->
	    out "("; print_prop out p'; out ")";
	    out (" " ^ impl ^ " ");
	    out "("; print_prop out q; out ")"
	| false, true  ->
	    out "("; print_prop out p'; out ")";
	    out (" " ^ impl ^ " ");
	    print_prop out q
	| true, false  ->
	    print_prop out p';
	    out (" " ^ impl ^ " ");
	    out "("; print_prop out q; out ")"
	| true, true   ->
	    print_prop out p';
	    out (" " ^ impl ^ " ");
	    print_prop out q
      in ()

  | _ -> failwith ("print_prop: " ^ show_prop p)

(* precedence: neg < and < lor < implies *)
and prop_prec = function
  | Prop_atomic _ -> 0
  | Prop_neg _ -> 10
  | Prop_conj _ -> 100
  | Prop_disj _ -> 200
  | Prop_impl _ -> 300

