(* $Id: afwprint_main.ml,v 1.1 2017/10/21 07:42:33 sato Exp $ *)
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
let opt_verbose = ref 0 ;;
let opt_fmt_in = ref "unspecified" ;;
let opt_fmt_out = ref "unspecified" ;;

let synopsis prog =
  printf "usage: %s [-p] <dfa_file>\n" (Filename.basename prog)

(* afw *)
let input_afw ic = function
  | "json"  | "unspecified" ->
      let dfa =  Yojson.Safe.from_channel ic in
      (match Afw.afw_of_yojson dfa with
	Result.Ok f -> f | Result.Error msg -> failwith msg)
  | fmt ->
      failwith ("input_afw: unknown format " ^ fmt)

(* afw *)
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

  let ic = open_in !infile in
  let m = input_afw ic !opt_fmt_in in
  output_afw oc m !opt_fmt_out;

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
