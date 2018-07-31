(* $Id: re2mso_main.ml,v 1.1 2017/10/21 07:41:45 sato Exp $ *)

open Printf

let stdin = open_in "/dev/stdin"
let opt_o = ref "unspecified" ;;
let opt_o_channel = ref stdout ;;
let opt_parse_only = ref false ;;
let opt_verbose = ref false ;;
let opt_fmt_in = ref "unspecified" ;;
let opt_fmt_out = ref "unspecified" ;;

let opt_nopreamble = ref false;;

let synopsis prog =
  printf "usage: %s [-p] <re_file>\n" (Filename.basename prog)

let input_re ic = function
  | "json" | "unspecified" ->
      let json =  Yojson.Safe.from_channel ic in
      (match Re.re_of_yojson json with
	Ok f -> f | Error msg -> failwith msg)
  | _ ->
      failwith "unknown format"

let output_re oc e = function
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

let output_mso oc p = function
  | "mso" | "mona" ->
      let out = fun s -> output_string oc s; flush_all () in
      if !opt_nopreamble
      then Mso.print_mso out p ~verbose:!opt_verbose ~preamble:""
      else Mso.print_mso out p ~verbose:!opt_verbose
  | "caml" | "unspecified" ->
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
      | "--nopreamble" ->
	  opt_nopreamble := true

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
  let e : Re.re = input_re ic !opt_fmt_in in
  if !opt_parse_only then
    begin
      output_re oc e !opt_fmt_out;
      raise Exit
    end;

  (* mso *)
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
