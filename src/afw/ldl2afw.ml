(* $Id: ldl2afw.ml,v 1.3 2017/10/21 07:42:33 sato Exp $ *)

open Ldl
open Ldlsimp
open Afw
open Printf

(** f -> afw *)
let rec translate (f : formula) =
  let f' = nnf (canonicalize f) in
  let has_last, prop_seq =
    List.fold_left
      (fun (b, names) name ->
	if name = "last" then (true, names) else (b, names @ [name]))
      (false, []) (find_props [] f') in
  let props : string array = Array.of_list prop_seq in

  let q_last, q_neg_last = (Ldl_atomic "last"), (Ldl_neg (Ldl_atomic "last"))
  and q_true, q_false = (Ldl_atomic "true"), (Ldl_atomic "false") in
  let delta0 =
    if has_last
    then
      [q_last, ref [(None, q_true); (Some (Ldl_atomic "true"), q_false)];
       q_neg_last, ref [(None, q_false); (Some (Ldl_atomic "true"), q_true)]]
    else [] in

  let m : afw =
    { props = props;
      states_ex = [q_true; q_false] @ (if has_last then [q_last; q_neg_last] else []);
      states_all = [];
      delta = delta0;
      init = f';
      nnodes = (0, 0);
      nedges = 0;
    }
  in
  construct m m.init;
  assert (List.mem m.init m.states_ex || List.mem m.init m.states_all);
  (* remove "last" and/or "!last" if either is unreachable *)
  let reachable = find_reachable m m.init [] in
  let _ =
    if not (List.mem q_last reachable) then
      (m.states_ex <- List.filter (fun f -> f != q_last) m.states_ex;
       m.delta <- List.filter (fun (f, _) -> f != q_last) m.delta);
    if not (List.mem q_neg_last reachable) then
      (m.states_ex <- List.filter (fun f -> f != q_neg_last) m.states_ex;
       m.delta <- List.filter (fun (f, _) -> f != q_neg_last) m.delta);
  in
  m.nnodes <- List.length m.states_ex, List.length m.states_all;
  m.nedges <- List.fold_left (fun n (_, es) -> n + List.length !es) 0 m.delta;
  m

and find_reachable (m : afw) f (reachable : formula list) =
  if List.mem f reachable then reachable else
  List.fold_left
    (fun rslt (_, f') -> find_reachable m f' rslt)
    (reachable @ [f])
    (try !(List.assoc f m.delta) with Not_found -> [])

(** construct m f constructs a new state (f, None)
   where f = currently-focusing ldl (sub)formula
   invariant
   - f has no assignment yet, which means
     - state to construct here = (f, None)
     - the next states (directly-reachable from (f, None)) = {(f, Some a) | a in all possible assignements}
       (f, None) -a-> (f, Some a) indicates that a has been chosen as the assignment for the current formula f.
   note:
   - (f, None) should always have at most one predecessor state,
     the edge from which to (f, None) should be epsilon
   - (f, None) is registered (to m.states_ex) in this function
     whereas m.states_all is used only when an assignment for f is already determined
   - (f, Some a) is not registered in this function but will be in construct_epsilon
   - (f, None) -a-> (f, Some a) is not registered in this function
     but will be in construct_iter or construct_iter_symbolic
   - construct is called when the previous assignment allows no further processing
     of f, that is,
     - when starting a new afw construction (where f = the input formula), or
     - when f = <phi>f' or f = [phi]f' (where phi is propositional)
 *)
and construct (m : afw) f =
  construct_rec m f

(* case: ex/all, suffix a = epsilon under a *)
and construct_rec m f =
  if mem f m.states_ex
  then assert (not (mem f m.states_all))
  else
    if mem f m.states_all
    then ()
    else construct_rec1 m f

and construct_rec1 m f =
  let curr = f in
  assert (not (mem curr m.states_ex) && not (mem curr m.states_all));
  let tt, ff = (Ldl_atomic "true"), (Ldl_atomic "false") in
  match f with

  (* propositional formula *)
  | _ when propositional f ->
      add_to_ex m curr;
      add_to_delta m (curr, Some f, tt);
      add_to_delta m (curr, Some (Ldl_neg f), ff);

  | Ldl_atomic _ ->
      failwith "construct_rec1: atomic"
  | Ldl_neg f' when not (propositional f') ->
      failwith "construct_rec1: neg (not supported)"

  (* conj -- parallel *)
  | Ldl_conj fs
    when not (mem curr m.states_all) ->
      add_to_all m curr;
      List.iter
	(fun f' ->
	  add_to_delta m (curr, None, f');
	  construct_rec m f')
	fs
  (* disj -- choice *)
  | Ldl_disj fs
    when not (mem curr m.states_ex) ->
      add_to_ex m curr;
      List.iter
	(fun f' ->
	  add_to_delta m (curr, None, f');
	  construct_rec m f')
	fs

  (* modal: propositional *)
  | Ldl_modal (Mod_ex, Path_prop p, f')
    when not (mem curr m.states_ex) ->
      add_to_ex m curr;
      add_to_delta m (curr, Some p, f');
      construct_rec m f';
      add_to_delta m (curr, Some (Ldl_neg p), ff);

  | Ldl_modal (Mod_all, Path_prop p, f')
    when not (mem curr m.states_ex) ->
      add_to_ex m curr;
      add_to_delta m (curr, Some p, f');
      construct_rec m f';
      add_to_delta m (curr, Some (Ldl_neg p), tt);

  (* modal: sequence *)
  | Ldl_modal (mm, Path_seq [p], f')
    when not (mem curr m.states_ex) ->
      add_to_ex m curr;
      let g = Ldl_modal (mm, p, f') in
      add_to_delta m (curr, None, g);
      construct_rec m g
  | Ldl_modal (mm, Path_seq (p::ps), f')
    when not (mem curr m.states_ex) ->
      add_to_ex m curr;
      let g = Ldl_modal (mm, p, canonicalize (Ldl_modal (mm, Path_seq ps, f'))) in
      add_to_delta m (curr, None, g);
      construct_rec m g

  (* modal: sum *)
  | Ldl_modal (Mod_ex, Path_sum ps, f')
    when not (mem curr m.states_ex) ->
      add_to_ex m curr;
      assert (List.length ps > 0);
      List.iter
	(fun p ->
	  let g = Ldl_modal (Mod_ex, p, f') in
	  add_to_delta m (curr, None, g);
	  construct_rec m g)
	ps
  | Ldl_modal (Mod_all, Path_sum ps, f')
    when not (mem curr m.states_ex) ->
      add_to_all m curr;
      assert (List.length ps > 0);
      List.iter
	(fun p ->
	  let g = Ldl_modal (Mod_all, p, f') in
	  add_to_delta m (curr, None, g);
	  construct_rec m g)
	ps

  (* modal: test *)
  | Ldl_modal (Mod_ex, Path_test p, f')
    when not (mem curr m.states_ex) ->
      add_to_all m curr;
      add_to_delta m (curr, None, p);
      construct_rec m p;
      add_to_delta m (curr, None, f');
      construct_rec m f'

  | Ldl_modal (Mod_all, Path_test p, f')
    when not (mem curr m.states_ex) ->
      add_to_ex m curr;

      let g = nnf (Ldl_neg p) in
      let g = canonicalize g in
      add_to_delta m (curr, None, g);
      construct_rec m g;

      add_to_delta m (curr, None, f');
      construct_rec m f'

  (* modal: star *)
  | Ldl_modal (Mod_ex, Path_star p, f')
    when not (mem curr m.states_ex) ->
      let _ =
	match p with
	| Path_test t ->
	    add_to_ex m curr;
	    add_to_delta m (curr, None, f');
	    construct_rec m f'
	| _ ->
	    add_to_ex m curr;
	    add_to_delta m (curr, None, f');
	    construct_rec m f';
	    let g = Ldl_modal (Mod_ex, p, Ldl_modal (Mod_ex, Path_star p, f')) in
	    let g = canonicalize g in
	    add_to_delta m (curr, None, g);
	    construct_rec m g;
      in ()
  | Ldl_modal (Mod_all, Path_star p, f')
    when not (mem curr m.states_ex) ->
      let _ =
	match p with
	| Path_test t ->
	    add_to_ex m curr;
	    add_to_delta m (curr, None, f');
	    construct_rec m f'
	| _ ->
	    (*add_to_all m curr;*)
	    add_to_ex m curr;
	    add_to_delta m (curr, None, f');
	    construct_rec m f';
	    let g = Ldl_modal (Mod_all, p, Ldl_modal (Mod_all, Path_star p, f')) in
	    let g = canonicalize g in
	    add_to_delta m (curr, None, g);
	    construct_rec m g;
      in ()

  | _ ->
      (*eprintf "** %s\n" (show_formula f);*)
      failwith "construct_rec: unsupported case"

and add_to_ex m f =
  if not (mem f m.states_ex) then
    begin
      m.states_ex <- m.states_ex @ [f];
      (*eprintf "state: ex(%s, %d)\n" (Ldl.show_formula f) (match a with Some i -> i | None -> -1)*)
    end

and add_to_all m f =
  if not (mem f m.states_all) then
    begin
      m.states_all <- m.states_all @ [f];
      (*eprintf "state: all(%s, %d)\n" (Ldl.show_formula f) (match a with Some i -> i | None -> -1)*)
    end

and add_to_delta m (q1, tr, q2) =
  if not (mem_edge (q1, tr, q2) m.delta) then
  try
    let edges = List.assoc q1 m.delta in
    edges := !edges @ [tr, q2]
  with
    Not_found -> m.delta <- m.delta @ [q1, ref [tr, q2]]

and find_props rslt = function
  | Ldl_atomic "true" | Ldl_atomic "false"  -> rslt
  | Ldl_atomic p when not (List.mem p rslt) -> rslt @ [p]
  | Ldl_atomic p -> rslt
  | Ldl_neg f -> find_props rslt f
  | Ldl_conj fs | Ldl_disj fs
    -> List.fold_left (fun rslt f -> find_props rslt f) rslt fs
  | Ldl_impl (f, g) -> find_props (find_props rslt f) g

  | Ldl_modal (_, p, f) -> find_props (find_props_in_path rslt p) f

and find_props_in_path rslt = function
  | Path_prop f | Path_test f -> find_props rslt f
  | Path_seq ps | Path_sum ps -> List.fold_left (fun rslt p -> find_props_in_path rslt p) rslt ps
  | Path_star p -> find_props_in_path rslt p

and mem f (qs : state list) =
  assert (f = canonicalize f);
  List.mem f qs

and mem_edge (f1, tr, f2) delta =
  try
    let edges = List.assoc f1 delta in List.mem (tr, f2) !edges
  with
    Not_found -> false

(*
and mem (f, i) (qs : state list) =
   let b = ref false in
   let _ =
     try
       List.iter
	 (fun (g, j) -> if i = j && Ldl.equal f g then (b := true; raise Exit))
	 qs
     with Exit -> ()
   in !b

and mem_edge ((f1, i1), tr, (f2, i2)) delta =
   let b = ref false in
   let _ =
     try
       List.iter
	 (fun ((f1', i1'), tr', (f2', i2')) ->
	   if i1 = i1' && Ldl.equal f1 f2 && tr = tr' && i2 = i2' && Ldl.equal f2 f2'
	   then (b := true; raise Exit))
	 delta
     with Exit -> ()
   in !b
 *)

(*
(* works only when f is propositional *)
and eval_formula (f : Ldl.formula) (m, q, a) =
  match f with
  | Ldl_atomic p -> eval_prop p (m, q, a)
  | Ldl_neg f -> not (eval_formula f (m, q, a))
  | Ldl_conj fs -> List.fold_left (fun b f -> b && eval_formula f (m, q, a)) true fs
  | Ldl_disj fs -> List.fold_left (fun b f -> b || eval_formula f (m, q, a)) false fs
  | Ldl_impl (f, g) -> eval_formula (Ldl_disj [Ldl_neg f; g]) (m, q, a)
  | Ldl_modal _ ->
      failwith ("eval_formula: " ^ show_formula f)

and eval_prop (p : string) (m, q, a) =
  match p with
  | "true" -> true | "false" -> false
  | "last" when q = (Ldl_atomic "last", None) -> true
  | "last" -> false
  | _ ->
      (*assert (Array.mem p m.props);*)
      assert (try array_find (fun _ q -> p = q) m.props; true with Not_found -> false);
      let i = index p m in
      assert (0 <= i && i < Array.length m.props);
      let pow = Big_int.shift_left_big_int Big_int.unit_big_int i in
      (* pow = 2^i *)
      not (Big_int.eq_big_int (Big_int.and_big_int (Big_int.big_int_of_int a) pow) Big_int.zero_big_int)

and index p m =
  let i = ref (-1) in
  let _ =
    try
      Array.iteri (fun j q -> if p = q then (i := j; raise Exit)) m.props;
      raise Not_found
    with Exit -> assert (!i >= 0)
  in !i

and array_find p l =
  let rslt = ref (0, None) in
  let _ =
    try
      Array.iteri (fun i elt -> if p i elt then (rslt := (i, Some elt); raise Exit)) l;
      raise Not_found
    with Exit -> assert (snd (!rslt) <> None)
  in !rslt
*)
