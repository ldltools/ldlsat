(* $Id: ldl2afw_main.ml,v 1.3 2017/10/21 07:42:33 sato Exp $ *)

open Printf

let stdin = open_in "/dev/stdin"
let opt_o = ref "unspecified" ;;
let opt_o_channel = ref stdout ;;
let opt_parse_only = ref false ;;
let opt_verbose = ref false ;;
let opt_fmt_in = ref "unspecified" ;;
let opt_fmt_out = ref "unspecified" ;;

let synopsis prog =
  printf "usage: %s [-p] <ldl_file>\n" (Filename.basename prog)

let rec input_formula ic = function
  | "ldl" | "pretty" ->
      Ldl_p.formula Ldl_l.token (Lexing.from_channel ic)
  | "json" ->
      let json =  Yojson.Safe.from_channel ic in
      (match Ldl.formula_of_yojson json with
	Ok f -> f | Error msg -> failwith msg)
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
  | _ ->
      failwith "unknown format"

and formula_from_string str = function
  | "ldl" | "pretty" ->
      Ldl_p.formula Ldl_l.token (Lexing.from_string str)
  | "json" ->
      let json =  Yojson.Safe.from_string str in
      (match Ldl.formula_of_yojson json with
	Ok f -> f | Error msg -> failwith msg)
  | "unspecified" when Bytes.length str < 6 ->
      formula_from_string str "pretty"
  | "unspecified" ->
      if Bytes.sub str 0 6 = "[\"Ldl_" then
	formula_from_string str "json"
      else
	formula_from_string str "pretty"

let output_formula oc f = function
  | "ldl" | "pretty" ->
      Ldl.print_formula (fun s -> output_string oc s; flush_all ()) f;
      output_string oc "\n"
  | "caml" ->
      output_string oc (Ldl.show_formula f);
      output_string oc "\n";
  | "json" | "unspecified" ->
      let json = Ldl.formula_to_yojson f in
      Yojson.Safe.to_channel oc json;
      output_string oc "\n"
  | _ ->
      failwith "unknown output format"

let rec output_afw oc m = function
  | "caml" ->
      output_string oc (Afw.show_afw m);
      output_string oc "\n";
  | "json" | "unspecified" ->
      let json = Afw.afw_to_yojson m in
      Yojson.Safe.to_channel oc json;
      output_string oc "\n"
  | "dot" ->
      Afw.output_afw_in_dot oc m
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
      | "-o" | "--output" ->
	  outfile := argv.(!i+1); incr i;
      | "-t" ->
	  opt_fmt_out := argv.(!i+1); incr i;
      | "--ldl" ->
	  opt_fmt_in := "pretty"
      | "--json" ->
	  opt_fmt_in := "json"

      | "-p" | "--parse-only" ->
	  opt_parse_only := true
      | "-v" | "--verbose" ->
	  opt_verbose := true
      | "-q" | "--silent" ->
	  opt_verbose := false
      | "-h" | "--help"  ->
	  synopsis argv.(0); exit 0

      | _    ->
	  infile := argv.(!i)
    in incr i
  done;

  (* input *)
  if not (Sys.file_exists !infile) then
    (synopsis argv.(0); invalid_arg ("file does not exist: '" ^ !infile ^ "'"));

  (* output *)
  let oc = open_out !outfile in

  (* parse a ldl formula *)
  let ic = open_in !infile in
  let formula = input_formula ic !opt_fmt_in in
  if !opt_parse_only then
    begin
      output_formula oc formula !opt_fmt_out;
      raise Exit
    end;

  (* afw *)
  let afw : Afw.afw = Ldl2afw.translate formula in
  output_afw oc afw !opt_fmt_out;

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
