(* $Id: afw.mli,v 1.3 2017/10/21 07:42:33 sato Exp $ *)

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

val afw_of_yojson : Yojson.Safe.json -> (afw, string) Result.result
val afw_to_yojson : afw ->  Yojson.Safe.json
val state_of_yojson : Yojson.Safe.json -> (state, string) Result.result
val state_to_yojson : state ->  Yojson.Safe.json
val assignment_of_yojson : Yojson.Safe.json -> (assignment, string) Result.result
val assignment_to_yojson : assignment ->  Yojson.Safe.json
