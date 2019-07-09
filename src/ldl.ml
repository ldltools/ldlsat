(* $Id: ldl.ml,v 1.3 2017/10/21 07:41:10 sato Exp $ *)
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

(*open Sexplib.Std*)

type formula =
  | Ldl_atomic of string
  | Ldl_neg of formula
  | Ldl_conj of formula list
  | Ldl_disj of formula list
  | Ldl_impl of formula * formula
  | Ldl_modal of modality * path * formula

and modality =
  | Mod_all | Mod_ex

and path =
  | Path_prop of formula
	(** should be propositional *)
  | Path_seq of path list
  | Path_sum of path list
  | Path_test of formula
  | Path_star of path

[@@deriving eq, ord, show, yojson]
(*[@@deriving eq, ord, show, yojson, sexp_of]*)
(*[@@deriving show { with_path = false }, yojson, eq, ord]*)

(* ================================================================================
   modality / equality
   ================================================================================
 *)

let rec modal f =
  match f with
  | Ldl_atomic "last" -> true
  | Ldl_atomic _ -> false
  | Ldl_neg g -> modal g
  | Ldl_conj gs | Ldl_disj gs ->
      (match List.find_opt modal gs with None -> false | Some _ -> true)
  | Ldl_impl (g1, g2) -> modal g1 || modal g2
  | Ldl_modal _ -> true

let rec equal f1 f2 =
  match f1, f2 with
  | Ldl_atomic a1, Ldl_atomic a2
    -> a1 = a2
  | Ldl_neg g1, Ldl_neg g2
    -> equal g1 g2

  | Ldl_conj fs1, Ldl_conj fs2
  | Ldl_disj fs1, Ldl_disj fs2
    when List.length fs1 = List.length fs2
    -> List.fold_left2 (fun b f1 f2 -> b && equal f1 f2) true fs1 fs2

  | Ldl_modal (Mod_all, p1, g1), Ldl_modal (Mod_all, p2, g2)
  | Ldl_modal (Mod_ex, p1, g1), Ldl_modal (Mod_ex, p2, g2)
    -> path_equal p1 p2 && equal g1 g2

  | _ -> false

and path_equal p1 p2 =
  match p1, p2 with
  | Path_prop f1, Path_prop f2
    -> equal f1 f2

  | Path_seq ps1, Path_seq ps2
  | Path_sum ps1, Path_sum ps2
    when List.length ps1 = List.length ps2
    -> List.fold_left2 (fun b p1 p2 -> b && path_equal p1 p2) true ps1 ps2

  | Path_test f1, Path_test f2
    -> equal f1 f2
  | Path_star p1, Path_star p2
    -> path_equal p1 p2

  | _ -> false

(* ================================================================================
   parser
   ================================================================================
 *)

let formula_of_string str =
(*
  Ldl_p.formula Ldl_l.token (Lexing.from_string str)
 *)
  failwith ("formula_of_string: " ^ str)

(* ================================================================================
   printer
   ================================================================================
 *)

let rec string_of_formula ?(fancy = false) ?(ltl = false) f =
  let str = ref "" in
  let concat str' = str := !str ^ str' in
  print_formula concat ~fancy ~ltl f;
  !str

and print_formula out ?(fancy = false) ?(ltl = false) (f : formula) =
  (*print_formula_rec out ~fancy (Ldlsimp.canonicalize f)*)
  print_formula_rec out ~fancy ~ltl f

and print_formula_rec out ?(fancy=false) ?(ltl = false) (f : formula) =
  let top, bot, neg, conj, disj, impl =
    if not fancy
    then "top", "bot", "!", "&", "|", "->"
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
      (Printf.sprintf "%c%c%c" (Char.chr 0xe2) (Char.chr 0x86) (Char.chr 0x92))
      (* → *)
  in
  match f with
  | Ldl_atomic "true" when fancy -> out top
  | Ldl_atomic "false" when fancy -> out bot
  | Ldl_atomic a -> out a

  | Ldl_neg f' when prec f' <= prec f -> out neg; print_formula_rec out ~fancy ~ltl f'
  | Ldl_neg f' -> out (neg ^ "("); print_formula_rec out ~fancy ~ltl f'; out ")"

  | Ldl_conj [] -> out "true"
  | Ldl_conj [f'] when prec f' <= prec f -> print_formula_rec out ~fancy ~ltl f'
  | Ldl_conj [f'] -> out "("; print_formula_rec out ~fancy ~ltl f'; out ")"
  | Ldl_conj (f' :: fs) when prec f' <= prec f ->
      print_formula_rec out ~fancy ~ltl f';
      out (" " ^ conj ^ " ");
      print_formula_rec out ~fancy ~ltl (Ldl_conj fs)
  | Ldl_conj (f' :: fs) ->
      out "("; print_formula_rec out ~fancy ~ltl f'; out ")";
      out (" " ^ conj ^ " ");
      print_formula_rec out ~fancy ~ltl (Ldl_conj fs)

  | Ldl_disj [] -> out "false"
  | Ldl_disj [f'] when prec f' <= prec f -> print_formula_rec out ~fancy ~ltl f'
  | Ldl_disj [f'] -> out "("; print_formula_rec out ~fancy ~ltl f'; out ")"
  | Ldl_disj (f' :: fs) when prec f' <= prec f ->
      print_formula_rec out ~fancy ~ltl f';
      out (" " ^ disj ^ " ");
      print_formula_rec out ~fancy ~ltl (Ldl_disj fs)
  | Ldl_disj (f' :: fs) ->
      out "("; print_formula_rec out ~fancy ~ltl f'; out ")";
      out (" " ^ disj ^ " ");
      print_formula_rec out ~fancy ~ltl (Ldl_disj fs)

  | Ldl_impl (f', g) ->
      let _ =
	match (prec f' < prec f), (prec g <= prec f) with
	| false, false ->
	    out "("; print_formula out ~fancy ~ltl f'; out ")";
	    out (" " ^ impl ^ " ");
	    out "("; print_formula out ~fancy ~ltl g; out ")"
	| false, true  ->
	    out "("; print_formula out ~fancy ~ltl f'; out ")";
	    out (" " ^ impl ^ " ");
	    print_formula out ~fancy ~ltl g
	| true, false  ->
	    print_formula out ~fancy ~ltl f';
	    out (" " ^ impl ^ " ");
	    out "("; print_formula out ~fancy ~ltl g; out ")"
	| true, true   ->
	    print_formula out ~fancy ~ltl f';
	    out (" " ^ impl ^ " ");
	    print_formula out ~fancy ~ltl g
      in ()

  | Ldl_modal (m, r, f') when ltl ->
      let _ =
	match m, r with
	| Mod_all, Path_star (Path_prop (Ldl_atomic "true")) ->
	    out "G"
	| Mod_ex,  Path_star (Path_prop (Ldl_atomic "true")) ->
	    out "F"
	| Mod_ex,  Path_prop (Ldl_atomic "true") ->
	    out "X"
	| _ ->
	    invalid_arg ("[print_formula_rec] " ^ string_of_formula ~fancy f)
      in
      if prec f' < prec f
      then print_formula out ~fancy ~ltl f'
      else (out "("; print_formula out ~fancy ~ltl f'; out ")")

  | Ldl_modal (m, r, f') ->
      out (match m with Mod_all -> "[" | _ -> "<");
      print_path out ~fancy ~ltl r;
      out (match m with Mod_all -> "]" | _ -> ">");
      if prec f' < prec f
      then print_formula out ~fancy ~ltl f'
      else (out "("; print_formula out ~fancy ~ltl f'; out ")")

(* precedence: neg < and < lor < implies *)
and prec = function
  | Ldl_atomic _ -> 0
  | Ldl_neg _ -> 10
  | Ldl_conj _ -> 100
  | Ldl_disj _ -> 200
  | Ldl_impl _ -> 300
  | Ldl_modal _ -> 30

and print_path out ?(fancy=false) ?(ltl = false) r =
  match r with
  | Path_prop f ->
      out "{"; print_formula out ~fancy ~ltl f; out "}"

  (* seq *)
  | Path_seq [r'] when path_prec r' <= path_prec r ->
      print_path out ~fancy ~ltl r'
  | Path_seq [r'] ->
      out "("; print_path out ~fancy ~ltl r'; out ")"
  | Path_seq (r' :: rs) when path_prec r' <= path_prec r ->
      print_path out ~fancy ~ltl r';
      out "; ";
      print_path out ~fancy ~ltl (Path_seq rs)
  | Path_seq (r' :: rs) ->
      out "("; print_path out ~fancy ~ltl r'; out ")";
      out "; ";
      print_path out ~fancy ~ltl (Path_seq rs)

  (* sum *)
  | Path_sum [r'] when path_prec r' <= path_prec r ->
      print_path out ~fancy ~ltl r'
  | Path_sum [r'] ->
      out "("; print_path out ~fancy ~ltl r'; out ")"
  | Path_sum (r' :: rs) when path_prec r' <= path_prec r ->
      print_path out ~fancy ~ltl r';
      out " + ";
      print_path out ~fancy ~ltl (Path_sum rs)
  | Path_sum (r' :: rs) ->
      out "("; print_path out ~fancy ~ltl r'; out ")";
      out "; ";
      print_path out ~fancy ~ltl (Path_sum rs)

  (* test *)
  | Path_test f ->
      out "{"; print_formula out ~fancy ~ltl f; out "}?"

  (* star *)
  | Path_star r' when path_prec r' <= path_prec r ->
      print_path out ~fancy ~ltl r'; out "*"
  | Path_star r' ->
      out "("; print_path out ~fancy ~ltl r'; out ")*"

(* precedence: grouping (()) < *, ? < concat (;) < choice (+) *)
and path_prec = function
  | Path_prop _ -> 0
  | Path_seq rs -> 100
  | Path_sum rs -> 200
  | Path_test f -> 50
  | Path_star r -> 30
