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

open Ldlsat
open Printf

let stdin = open_in "/dev/stdin"
let opt_o = ref "unspecified" ;;
let opt_o_channel = ref stdout ;;
let opt_parse_only = ref false ;;
let opt_until = ref "mso" ;;
let opt_verbose = ref false ;;
let opt_fmt_in = ref "unspecified" ;;
let opt_fmt_out = ref "unspecified" ;;
let opt_nopreamble = ref false;;

let synopsis prog =
  printf "%s (version %s)\n" (Filename.basename prog) (Version.get ());
  printf "usage: %s <option>* <ldl_file>\n" (Filename.basename prog);
  List.iter (output_string stdout)
    ["options:\n";
     "  -p\t\t\tterminate after parsing\n";
     "  -o <file>\t\toutput to <file>\n";
     "  -t <fmt>\t\toutput in <fmt> (\"json\", \"caml\")\n";
     "  -u <stage>\t\tterminate when <stage> gets reached\n";
     "  \t\t\t<stage> ::= ldl | afw | re | mso\n";
     "  -h\t\t\tdisplay this message\n"]

(* input *)

let rec input_formula ic = function
  | "ldl" | "pretty" ->
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
      let str' : bytes = Bytes.concat (Bytes.of_string "") !lst in
      let str' : bytes = Bytes.sub str' 0 (Bytes.index str' (Char.chr 0)) in
      formula_from_string (Bytes.to_string str') "unspecified"
  | fmt ->
      failwith ("unknown format: " ^ fmt)

and formula_from_string (str : string) = function
  | "ldl" | "pretty" ->
      Ldl_p.formula Ldl_l.token (Lexing.from_string str)
  | "json" ->
      let json =  Yojson.Safe.from_string str in
      (match Ldl.formula_of_yojson json with
	Ok f -> f | Error msg -> failwith msg)
  | "dimacs" ->
      dimacs_parse str
  | "unspecified" when String.length str < 6 ->
      formula_from_string str "pretty"
  | "unspecified" ->
      if String.sub str 0 6 = "[\"Ldl_" then
	formula_from_string str "json"
      else if looks_like_dimacs str (String.length str) 0 then
	dimacs_parse str
      else
	formula_from_string str "pretty"

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
  | "ldl" | "unspecified" ->
      Ldl.print_formula (fun s -> output_string oc s; flush_all ()) f;
      output_string oc "\n"
  | "ltl" ->
      Ldl.print_formula (fun s -> output_string oc s; flush_all ()) ~ltl: true f;
      output_string oc "\n"
  | "caml" ->
      output_string oc (Ldl.show_formula f);
      output_string oc "\n";
  | "json" ->
      let json = Ldl.formula_to_yojson f in
      Yojson.Safe.to_channel oc json;
      output_string oc "\n"
  | _ ->
      failwith "unknown output format"

let rec output_afw oc m = function
  | "dot" | "graphviz" | "unspecified" ->
      Afw.output_afw_in_dot oc m
  | "caml" ->
      output_string oc (Afw.show_afw m);
      output_string oc "\n";
  | "json" ->
      let json = Afw.afw_to_yojson m in
      Yojson.Safe.to_channel oc json;
      output_string oc "\n"
  | _ ->
      failwith "unknown output format"

let output_re oc e = function
  | "re" | "unspecified" ->
      Re.print_re (fun s -> output_string oc s; flush_all ()) e;
      output_string oc "\n"
  | "caml" ->
      output_string oc (Re.show_re e);
      output_string oc "\n";
  | "json" ->
      let json = Re.re_to_yojson e in
      Yojson.Safe.to_channel oc json;
      output_string oc "\n"
  | _ ->
      failwith "unknown output format"

let output_mso oc p = function
  | "mso" | "mona" | "unspecified" ->
      let out = fun s -> output_string oc s; flush_all () in
      if !opt_nopreamble
      then Mso.print_mso out p ~verbose:!opt_verbose ~preamble:""
      else Mso.print_mso out p ~verbose:!opt_verbose
  | "caml" ->
      output_string oc (Mso.show_prog p);
      output_string oc "\n";
  | _ ->
      failwith "unknown output format"

(* *)
let main argc argv =
  let i = ref 1
  and infile = ref "/dev/stdin"
  and outfile = ref "/dev/stdout" in
  while !i < argc do
    let _ =
      match argv.(!i) with
      | "-" ->
	  infile := "/dev/stdin";
      | "-o" | "--output" when !i + 1 < argc ->
	  outfile := argv.(!i+1); incr i;

      | "-s" when !i + 1 < argc ->
	  opt_fmt_in := argv.(!i+1); incr i;
      | "-t" when !i + 1 < argc ->
	  opt_fmt_out := argv.(!i+1); incr i;

      | "--ldl" ->
	  opt_fmt_in := "pretty"
      | "--json" ->
	  opt_fmt_in := "json"
      | "--dimacs" ->
	  opt_fmt_in := "dimacs"

      | "-p" | "--parse-only" ->
	  opt_parse_only := true
      | "--nopreamble" ->
	  
	  opt_nopreamble := true
      | "-u" | "--until" when !i + 1 < argc ->
	  if not (List.mem argv.(!i + 1) ["ldl"; "afw"; "re"; "mso"]) then invalid_arg argv.(!i + 1);
	  opt_until := argv.(!i + 1); incr i;

      | "-v" | "--verbose" ->
	  opt_verbose := true
      | "-q" | "--silent" ->
	  opt_verbose := false
      | "-V" | "--version" ->
	  printf "%s\n" (Version.get ());
	  raise Exit
      | "-h" | "--help"  ->
	  synopsis argv.(0); exit 0

      | _ when argv.(!i).[0] = '-' ->
	  invalid_arg @@ "invalid option: " ^ argv.(!i)
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

  (* parse a ldl formula *)
  let ic = open_in !infile in
  at_exit (fun _ -> close_in ic);
  let f = input_formula ic !opt_fmt_in in
  if !opt_parse_only || !opt_until = "ldl" then
    begin
      output_formula oc f !opt_fmt_out;
      raise Exit
    end;

  (* ldl -> afw *)
  if !opt_until = "afw" then
    begin
      let m : Afw.afw = Ldl2afw.translate f in
      output_afw oc m !opt_fmt_out;
      raise Exit
    end;

  (* ldl -> re *)
  let e : Re.re = Re.re_of_formula f in
  if !opt_until = "re" then
    begin
      output_re oc e !opt_fmt_out;
      raise Exit
    end;

  (* re -> mso *)
  let p : Mso.prog = Re2mso.re2mso e in

  output_mso oc p !opt_fmt_out;
  flush_all ();

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
    eprintf ";; Failure: %s\n" s;
    exit 1;
| Not_found ->
    flush_all ();
    eprintf ";; Something seems missing!\n";
    exit 1;
| End_of_file ->
    flush_all ();
    eprintf ";; Unexpected end of file\n";
    exit 1;
