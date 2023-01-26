(* $Id: afw.mli,v 1.3 2017/10/21 07:42:33 sato Exp $ *)
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

type afw =
    { props : string array;			(** atomic propositions *)
      mutable states_ex : state list;		(** choice *)
      mutable states_all : state list;		(** parallel *)
      mutable delta : (state * (assignment option * state) list ref) list;
      init : state;
      mutable nnodes : int * int;
      mutable nedges : int;
    }

and state =
    Ldl.formula

and assignment =
    Ldl.formula

(** pretty-printing *)

val output_afw_in_dot : out_channel -> afw -> unit

(** ppx-generated *)

val pp_afw : Format.formatter -> afw -> unit
val pp_state : Format.formatter -> state -> unit
val pp_assignment : Format.formatter -> assignment -> unit

val show_afw : afw -> string
val show_state : state -> string

val afw_of_yojson : Yojson.Safe.t -> (afw, string) Result.result
val afw_to_yojson : afw ->  Yojson.Safe.t
val state_of_yojson : Yojson.Safe.t -> (state, string) Result.result
val state_to_yojson : state ->  Yojson.Safe.t
val assignment_of_yojson : Yojson.Safe.t -> (assignment, string) Result.result
val assignment_to_yojson : assignment ->  Yojson.Safe.t
