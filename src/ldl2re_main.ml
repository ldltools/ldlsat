(* $Id: ldl2re_main.ml,v 1.2 2017/10/21 07:41:26 sato Exp $ *)

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
  | "ldl" | "unspecified" ->
      Ldl.print_formula (fun s -> output_string oc s; flush_all ()) f;
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

let rec output_re oc e = function
  | "re" ->
      Re.print_re (fun s -> output_string oc s; flush_all ()) e
  | "caml" ->
      output_string oc (Re.show_re e);
      output_string oc "\n";
  | "json" | "unspecified" ->
      let json = Re.re_to_yojson e in
      Yojson.Safe.to_channel oc json;
      output_string oc "\n"
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
  let f = input_formula ic !opt_fmt_in in
  if !opt_parse_only then
    begin
      output_formula oc f !opt_fmt_out;
      raise Exit
    end;

  (* re *)
  let e : Re.re = Re.re_of_formula f in
  output_re oc e !opt_fmt_out;
  output_string oc "\n";

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
