(* $Id: mso.mli,v 1.1 2017/10/21 07:41:45 sato Exp $ *)

(** formula *)
type formula =
  | Mso_atomic of string
  | Mso_neg of formula
  | Mso_conj of formula list
  | Mso_disj of formula list
  | Mso_impl of formula * formula

  | Mso_app of string * term list
	(** predicate/macro call *)
  | Mso_mem of term1 * term2
  | Mso_comp1 of comp_op * term1 * term1
  | Mso_comp2 of comp_op * term2 * term2

  | Mso_all1 of (term1 -> formula)
  | Mso_all2 of (term2 -> formula)
  | Mso_ex1 of (term1 -> formula)
  | Mso_ex2 of (term2 -> formula)

and term =
  | Tm1 of term1
  | Tm2 of term2

(** 1st order term -- position variable *)
and term1 =
  | Tm1_var of string
  | Tm1_int of int
  | Tm1_exp of arith_op * term1 * term1
  | Tm1_app of string * term1 list

(** 2nd order term -- state variable *)
and term2 =
  | Tm2_var of string

and comp_op =
  | Comp_eq
  | Comp_gt | Comp_lt
  | Comp_ge | Comp_le

and arith_op =
  | Arith_add
  | Arith_sub

(** predicate or macro *)
type pred =
  | Pred_prop of formula
  | Pred_abs1 of (term1 -> pred)
  | Pred_abs2 of (term2 -> pred)

type decl =
  | Decl_var1 of string list
  | Decl_var2 of string list
  | Decl_pred of string * pred
  | Decl_macro of string * pred
  | Decl_formula of formula
  | Decl_comment of string

type prog =
    decl list

(** structural equality *)

val formula_equal : formula -> formula -> bool
val pred_equal : pred -> pred -> bool

(** pretty-printer *)

val print_mso : (string -> unit) -> ?verbose:bool -> ?preamble:string -> prog -> unit
val print_formula : (string -> unit) -> formula -> unit
val string_of_mso : prog -> string

(** ppx-generated *)

val show_formula : formula -> string
val pp_prog : Format.formatter -> prog -> unit
val show_prog : prog -> string

(** auxiliary *)
    
val newsym : string -> string
