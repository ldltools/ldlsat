(* $Id: ldlsimp_main.ml,v 1.1 2018/01/22 10:23:35 sato Exp $ *)

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

let synopsis prog =
  printf "usage: %s <option>* <ldl_file>\n" (Filename.basename prog);
  let msg =
    "options:\n"
    ^ "  --tac <tac>,..\tapply tactics (default: simp)\n"
    ^ "\t\t\t<tac> ::= simp | res | nnf | cnf | dnf | flat\n"
    ^ "  -o <file>\t\toutput to <file>\n"
    ^ "  -p\t\t\tparse-only\n"
    ^ "  -h\t\t\tdisplay this message\n"
  in output_string stdout msg

let rec input_formula ic = function
  | "ldl" ->
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
  | fmt ->
      failwith ("unknown format: " ^ fmt)

and formula_from_string str = function
  | "ldl" ->
      Ldl_p.formula Ldl_l.token (Lexing.from_string str)
  | "json" ->
      let json =  Yojson.Safe.from_string str in
      (match Ldl.formula_of_yojson json with
	Ok f -> f | Error msg -> failwith msg)
  | "unspecified" when Bytes.length str < 6 ->
      formula_from_string str "ldl"
  | "unspecified" ->
      if Bytes.sub str 0 6 = "[\"Ldl_" then
	formula_from_string str "json"
      else
	formula_from_string str "ldl"
  | fmt ->
      failwith ("unknown format: " ^ fmt)

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
  | fmt ->
      failwith ("unknown format: " ^ fmt)

let apply_tactic f = function
  (* propositional *)
  | "simp" -> Ldlsimp.simp f
  | "simp_sort" | "sort" -> Ldlsimp.simp_sort f
  | "simp_uniq" | "uniq" -> Ldlsimp.simp_uniq f
  | "simp_flatten" -> Ldlsimp.simp_flatten f

  | "resolve" | "res" -> Ldlsimp.resolve f
  | "dnf" -> Ldlsimp.dnf f
  | "cnf" -> Ldlsimp.cnf f
  | "flatten" | "flat" -> Ldlsimp.flatten f

  (* ldl *)
  | "nnf" -> Ldlsimp.nnf f
  | tac -> invalid_arg tac

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
      | "-p" | "--parse-only" ->
	  opt_parse_only := true
      | "--ldl" ->
	  opt_fmt_in := "ldl"
      | "--json" ->
	  opt_fmt_in := "json"

      | "--tac" | "--tactic" ->
	  opt_tactic := argv.(!i+1); incr i;

      | "-o" | "--output" ->
	  outfile := argv.(!i+1); incr i;
      | "-t" ->
	  opt_fmt_out := argv.(!i+1); incr i;

      | "-v" | "--verbose" ->
	  opt_verbose := true
      | "-q" | "--silent" ->
	  opt_verbose := false
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

  (* parse a proposition in ldl *)
  let ic = open_in !infile in
  let f = input_formula ic !opt_fmt_in in
  if !opt_parse_only then
    begin
      output_formula oc f !opt_fmt_out;
      raise Exit
    end;

  (* simp *)
  let rec split str i n rslt =
    if i = n then rslt else
    try
      let j = String.index_from str i ','
      in split str (j + 1) n (rslt @ [String.sub str i (j - i)])
    with Not_found -> rslt @ [String.sub str i (n - i)] in
  let tactics = split !opt_tactic 0 (String.length !opt_tactic) [] in
  let f' =
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
