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

(** for propositional formulas *)

val propositional : formula -> bool

val cnf : formula -> formula
val dnf : formula -> formula
val flatten : formula -> formula
val resolve : formula -> formula

val simp : formula -> formula
val simp_flatten : formula -> formula
val simp_sort : formula -> formula
val simp_uniq : formula -> formula

(** for ldl formulas *)

val canonicalize : formula -> formula
val nnf : formula -> formula
