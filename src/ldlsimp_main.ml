(* $Id: ldlsimp_main.ml,v 1.1 2018/01/22 10:23:35 sato Exp $ *)
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

open Ldlsat
open Printf

let stdin = open_in "/dev/stdin"
let opt_o = ref "unspecified" ;;
let opt_o_channel = ref stdout ;;
let opt_parse_only = ref false
let opt_verbose = ref false
let opt_fmt_in = ref "unspecified"
let opt_fmt_out = ref "unspecified"

let opt_nnf = ref false
let opt_dnf = ref false
let opt_tactic = ref ""
let opt_sat = ref false

let synopsis prog =
  printf "%s (version %s)\n" (Filename.basename prog) (Version.get ());
  printf "usage: %s <option>* <ldl_file>\n" (Filename.basename prog);
  List.iter (output_string stdout)
    ["options:\n";
     "  --tac <tac>,..\tapply tactics (default: simp)\n";
     "\t\t\t<tac> ::= simp | nnf | neg | tseitin\n";
     "  --sat\t\t\trun as a propositional SAT solver (resolution-based)\n";
     "  -p\t\t\tterminate after parsing\n";
     "  -o <file>\t\toutput to <file>\n";
     "  -t <fmt>\t\toutput in <fmt> (\"ldl\", \"caml\", \"json\", \"dimacs\")\n";
     "  -h\t\t\tdisplay this message\n"]

(* input *)

let rec input_formula ic = function
  | "ldl" ->
      Ldl_p.formula Ldl_l.token (Lexing.from_channel ic)
  | "json" ->
      let json =  Yojson.Safe.from_channel ic in
      (match Ldl.formula_of_yojson json with
	Ok f -> f | Error msg -> failwith msg)
  | "dimacs" ->
      Ldl.Ldl_conj (Toysat.dimacs_parse ic)

  | "unspecified" ->
      let lst = ref [] in
      let _ =
	try
	  while true do
	    let str = Bytes.make 1024 (Char.chr 0) in
	    lst := !lst @ [str];
	    really_input ic str 0 1024;
	  done
	with End_of_file -> () in
      let str' = Bytes.concat "" !lst in
      let str' = Bytes.sub str' 0 (Bytes.index str' (Char.chr 0)) in
      formula_from_string str' "unspecified"
  | fmt ->
      failwith ("unknown format: " ^ fmt)

and formula_from_string str = function
  | "ldl" ->
      Ldl_p.formula Ldl_l.token (Lexing.from_string str)
  | "json" ->
      let json =  Yojson.Safe.from_string str in
      (match Ldl.formula_of_yojson json with
	Ok f -> f | Error msg -> failwith msg)
  | "dimacs" ->
      dimacs_parse str

  | "unspecified" when Bytes.length str < 6 ->
      formula_from_string str "ldl"
  | "unspecified" ->
      if Bytes.sub str 0 6 = "[\"Ldl_" then
	formula_from_string str "json"
      else if looks_like_dimacs str (Bytes.length str) 0 then
	dimacs_parse str
      else
	formula_from_string str "ldl"
  | fmt ->
      failwith ("unknown format: " ^ fmt)

and looks_like_dimacs str len pos =
  (* check if "p cnf" is included *)
  assert (pos < len);
  if pos + 5 > len then false else if String.sub str pos 5 = "p cnf" then true
  else
    try
      looks_like_dimacs str len @@ 1 + String.index_from str pos '\n'
    with Not_found -> false    

and dimacs_parse str =
  let tempname, oc = Filename.open_temp_file "dimacs" ".cnf"
  in output_string oc str; close_out oc;

  let ic = open_in tempname
  in let f = Ldl.Ldl_conj (Toysat.dimacs_parse ic)
  in close_in ic; Sys.remove tempname;
  f

(* output *)

let output_formula oc f = function
  | "ldl"  | "unspecified" ->
      Ldl.print_formula (fun s -> output_string oc s; flush_all ()) f;
      output_string oc "\n"
  | "caml" ->
      output_string oc (Ldl.show_formula f);
      output_string oc "\n";
  | "json" ->
      let json = Ldl.formula_to_yojson f in
      Yojson.Safe.to_channel oc json;
      output_string oc "\n"
  | "dimacs" ->
      if !opt_verbose then output_string oc @@ "c " ^ Ldl.string_of_formula f ^ "\n";
      Toysat.dimacs_print ~verbose: !opt_verbose oc (Toysat.tseitin f)
  | fmt ->
      failwith ("unknown format: " ^ fmt)

let output_solution oc (solved, model) = function
  | _ ->
      if not solved then
	output_string oc "unsatisfiable\n"
      else
	let _ =
	  output_string oc "satisfiable\n";
	  List.iter
	    (fun (p, b) ->
	      let str =
		Ldl.string_of_formula @@ if b then Ldl_atomic p else Ldl_neg (Ldl_atomic p)
	      in output_string oc @@ str ^ " ")
	    model;
	  output_string oc "\n"
	in ()

(* formula transformation *)
let rec apply_tactic f = function
  | "simp" -> Ldlsimp.simp f

  | "id" | "nop" -> f
  | "neg" -> Ldl.Ldl_neg f
  | "nnf" -> Ldlsimp.nnf f

  (* propositional-only *)
  | "tseitin" ->
      Ldl_conj (Toysat.tseitin f)

  | tac -> invalid_arg @@ "[apply_tactic] " ^ tac

(* main *)
let main argc argv =
  let i = ref 1
  and infile = ref "/dev/stdin"
  and outfile = ref "/dev/stdout" in
  while !i < argc do
    let _ =
      match argv.(!i) with
      | "-" ->
	  infile := "/dev/stdin";
      | "--ldl" ->
	  opt_fmt_in := "ldl"
      | "--json" ->
	  opt_fmt_in := "json"
      | "--dimacs" ->
	  opt_fmt_in := "dimacs"

      | "--tac" | "--tactic" ->
	  opt_tactic := argv.(!i+1); incr i;
      | "--sat" ->
	  opt_sat := true
      | "-p" | "--parse-only" ->
	  opt_parse_only := true

      | "-o" | "--output" ->
	  outfile := argv.(!i+1); incr i;
      | "-t" ->
	  opt_fmt_out := argv.(!i+1); incr i;

      | "-v" | "--verbose" ->
	  opt_verbose := true
      | "-q" | "--silent" ->
	  opt_verbose := false
      | "-V" | "--version" ->
	  printf "%s\n" (Version.get ());
	  raise Exit
      | "-h" | "--help"  ->
	  synopsis argv.(0); exit 0
      | _  when argv.(!i).[0] = '-' ->
	  failwith ("unknown option: " ^ argv.(!i))

      | _    ->
	  infile := argv.(!i)
    in incr i
  done;

  (* input *)
  if not (Sys.file_exists !infile) then
    (eprintf "file does not exist: %S\n" !infile; raise Not_found);

  (* output *)
  let oc = open_out !outfile in
  at_exit (fun _ -> close_out oc);

  (* parse a proposition in ldl *)
  let ic = open_in !infile
  in let f : Ldl.formula = input_formula ic !opt_fmt_in
  in
  close_in ic;
  if !opt_parse_only then
    begin
      output_formula oc f !opt_fmt_out;
      raise Exit
    end;

  (* sat *)
  if !opt_sat then
    begin
      let s = Toysat.solve @@ Toysat.tseitin f in
      output_solution oc s !opt_fmt_out;
      raise Exit
    end;

  (* simp *)
  let rec split str i n rslt =
    if i = n then rslt else
    try
      let j = String.index_from str i ','
      in split str (j + 1) n (rslt @ [String.sub str i (j - i)])
    with Not_found -> rslt @ [String.sub str i (n - i)]
  in let tactics = split !opt_tactic 0 (String.length !opt_tactic) []
  in let f' =
    List.fold_left
      (fun rslt t ->
	if !opt_verbose then
	  (output_formula oc rslt !opt_fmt_out; fprintf oc "[%s]\n" t; flush_all ());
	apply_tactic rslt t)
      f (if tactics = [] then ["simp"] else tactics)
  in
  output_formula oc f' !opt_fmt_out;

  (* clean-up *)
  ()
;;

(* toplevel *)
assert (not !Sys.interactive);
try
  main (Array.length Sys.argv) Sys.argv
with   
| Exit -> exit 0
| Failure s ->
    flush_all ();
    eprintf "** Failure: %s\n" s;
    exit 1;
| Invalid_argument s ->
    flush_all ();
    eprintf "** Invalid_argument: %s\n" s;
    exit 1;
| Not_found ->
    flush_all ();
    eprintf "** Something seems missing!\n";
    exit 1;
| End_of_file ->
    flush_all ();
    eprintf "** Unexpected end of file\n";
    exit 1;
