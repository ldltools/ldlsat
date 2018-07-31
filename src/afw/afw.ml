(* $Id: afw.ml,v 1.3 2017/10/21 07:42:33 sato Exp $ *)

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

[@@deriving show, yojson]

(** pretty-printing *)

let output_afw_in_dot oc (m : afw) =
  Printf.fprintf oc "digraph {\n  graph [charset=\"UTF-8\"]\n";
  (* nodes *)
  Printf.fprintf oc "  init [label=\"\",shape=point]\n";
  let print_states prefix n =
    List.iteri
      (fun i f ->
	Printf.fprintf oc "  %d [label=\"" (i + n);
	output_string oc
	  (match f with
	  | Ldl.Ldl_atomic "true" -> "accept\",style=filled,color=lightgrey"
	  | Ldl.Ldl_atomic "false" -> "reject\",style=filled,color=\".7 .3 .9\""
	  | _ -> (Ldl.string_of_formula f) ^ "\"");
	if prefix = "all" then output_string oc ",shape=box";
	Printf.fprintf oc "]%s\n" (if f = m.init then " // init" else ""))
  in
  print_states "ex" 0 m.states_ex;
  print_states "all" (fst m.nnodes) m.states_all;
  (* edges *)
  Printf.fprintf oc "  init -> ";
  let states = m.states_ex @ m.states_all in
  let _ =
    try
      List.iteri
	(fun i q -> if q = m.init then (Printf.fprintf oc "%d\n" i; raise Exit))
	states
      with Exit -> ()
  in ();
  let string_of_state q =
    assert (List.mem q states);
    let i = ref (-1) in
    try
      List.iteri (fun i' q' -> if q' = q then (i := i'; raise Exit)) states;
      failwith (show_state q)
    with
      Exit -> assert (!i >= 0); string_of_int !i
  and string_of_assignment = function
    | None -> ""
    | Some a ->	Ldl.string_of_formula a
	(*
	let str, _ =
	  Array.fold_left
	    (fun (str', i) x ->
	      (str' ^ (if a land (1 lsl i) <> 0 then "" else "!") ^ x ^ " "), i + 1)
	    ("", 0) m.props
	in str
	*)
  in
  List.iter
    (fun (q, es) ->
      List.iter
	(fun (a, q') ->
	  Printf.fprintf oc "  %s -> %s [label=\"%s\"]\n"
	    (string_of_state q) (string_of_state q') (string_of_assignment a))
	!es)
    m.delta;
  Printf.fprintf oc "}\n"
