(* $Id: re.mli,v 1.3 2018/01/09 07:54:43 sato Exp $ *)
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

type re =
  | Re_prop of prop
  | Re_neg of re
  | Re_union of re list
  | Re_inter of re list
  | Re_seq of re list
  | Re_star of re
  | Re_test of re
  | Re_modal of Ldl.modality * re * re

and prop =
  | Prop_atomic of string
  | Prop_neg of prop
  | Prop_conj of prop list
  | Prop_disj of prop list
  | Prop_impl of prop * prop

(** re from ldl *)

val re_of_formula : Ldl.formula -> re

(** pretty-printer *)

val print_re : (string -> unit) -> re -> unit
val string_of_re : re -> string

(** ppx-generated *)

val pp_re : Format.formatter -> re -> unit
val show_re : re -> string

val re_of_yojson : Yojson.Safe.t -> (re, string) Result.result
val re_to_yojson : re -> Yojson.Safe.t
