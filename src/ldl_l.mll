(* $Id: ldl_l.mll,v 1.4 2018/01/09 07:54:43 sato Exp $ *)
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

(* header *)
{
open Ldl_p

}

(* tokens *)

let letter = [ 'a'-'z' 'A'-'Z' ]
(*let special_initial = [ '$' '*' '_' ]*)
let special_initial = [ '_' ]
let initial = letter | special_initial
(*let initial = letter*)
let digit = ['0'-'9']
let special_subsequent = [ '_' '.' ]
let subseqent = letter | digit | special_subsequent
(*let subseqent = letter | digit*)
let identifier = initial subseqent *

(*let sign = "" | '+' | '-'*)
let sign = "" | '+' | '-'
(*let integer = sign digit+*)
let integer = digit+
let suffix = "" | ('e' sign digit+)  
let real = digit+ '.' digit+ suffix | '.' digit+ suffix
let number = integer | real

let boolean = "false" | "true"

let string_element = "''" | [^ '\"' '\\'] | "\\\"" | '\\'
let string = '\"' string_element * '\"'

let newline = (  '\n' | '\r' | "\n\r" )
let whitespace = [' ' '\t'] | newline
(*let atmosphere = whitespace | comment*)
let atmosphere = whitespace
let intertoken_space = atmosphere +

let any_string = [^ '\n' '\r' ] *

(* entry points *)
rule token = parse
| "//" any_string (newline | eof)
		{ token lexbuf }

(*
| "true"	{ BOOL true }
| "false"	{ BOOL false }
| "last"	{ LAST }
*)

| "not"		{ NOT }
| "and"		{ AND }
| "or"		{ OR }
| "&&"		{ AND }
| "||"		{ OR }
| "->"		{ IMPLIES }
| "<->"		{ EQUIV }

(* unicode symbols -- not supported *)
(*
"\xe2\x8a\xa4"	{ NAME "true" }
"\xe2\x8a\xa5"	{ NAME "false" }
"\xc2\xac"	{ NOT }
"\xe2\x88\xa7"	{ AND }
"\xe2\x88\xa8"	{ OR }
"\xe2\x86\x92"	{ IMPLIES }
*)

| '!'		{ EXCLAM }
| '~'		{ TILDE }
| '<'		{ LT }
| '>'		{ GT }
| '('		{ LPAREN }
| ')'		{ RPAREN }
| '{'		{ LBRACE }
| '}'		{ RBRACE }
| '['		{ LBRACK }
| ']'		{ RBRACK }
| ':'		{ COLON }
| ';'		{ SEMI }
| ','		{ COMMA }
| '.'		{ DOT }
| '@'		{ AT }
| '&'		{ AND }

| '='		{ EQUAL }
| '+'		{ PLUS }
| '-'		{ MINUS }
| '*'		{ STAR }
| '/'		{ SLASH }
| '%'		{ PERCENT }
| '?'		{ QUESTION }
| "|"		{ OR }

(* SYMBOL *)
| identifier	{ let s = Lexing.lexeme lexbuf in
		  (*Printf.eprintf "<SYM(%s)>" s; flush_all ();*)
		  NAME s }
(* LITERAL *)
| string	{ let s = Lexing.lexeme lexbuf in
		  (*Printf.eprintf "<STR(%s)>" s;*)
		  STRING (String.sub s 1 (String.length s - 2)) }

(*
| integer	{ let str = Lexing.lexeme lexbuf in
		  let n =
		    try int_of_string str
		    with Failure "int_of_string" ->
		      Printf.eprintf
			"invalid term: %S (out of [%d,%d]) --> 0\n"
			str min_int max_int;
		      0
		  in
		  (*Logger.printf "<INT(%d)>" n;*)
		  INT n }
| real		{ let n = float_of_string (Lexing.lexeme lexbuf) in
		  (*Printf.eprintf "<REAL(%.2f)>" n;*)
		  REALNUMBER n }
*)

| whitespace	{ token lexbuf }
| newline	{ token lexbuf }

| eof		{ EOF }

(* trailer *)
{
}
