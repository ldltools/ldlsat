(* $Id: ldl.mli,v 1.3 2017/10/21 07:41:10 sato Exp $ *)
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

(** modality / equality *)

val modal : formula -> bool

val equal : formula -> formula -> bool

(** parsing *)

val formula_of_string : string -> formula

(** pretty-printing *)

val print_formula : (string -> unit) -> ?fancy:bool -> formula -> unit
val string_of_formula : ?fancy:bool -> formula -> string

(** ppx-generated *)

val equal_formula : formula -> formula -> bool
val compare_formula : formula -> formula -> int

val pp_formula : Format.formatter -> formula -> unit
val pp_modality : Format.formatter -> modality -> unit
val show_formula : formula -> string

val formula_of_yojson : Yojson.Safe.json -> (formula, string) Result.result
val formula_to_yojson : formula -> Yojson.Safe.json
val modality_to_yojson : modality -> Yojson.Safe.json
val modality_of_yojson : Yojson.Safe.json -> (modality, string) Result.result

(*
val sexp_of_formula : formula -> Sexplib.Sexp.t
 *)
