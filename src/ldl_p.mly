// $Id: ldl_p.mly,v 1.4 2018/01/09 07:54:43 sato Exp $
//
// (C) Copyright IBM Corp. 2018.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//

%{
open Ldl

let parse_error s =
  print_endline s;
  let pos = Parsing.symbol_start_pos () in
  Printf.printf "line:%d, bol:%d, cnum:%d\n" pos.pos_lnum pos.pos_bol pos.pos_cnum;
  flush stdout

%}

%start	formula
%type<Ldl.formula> formula

%token	<string> NAME
%token	<string> STRING
%token	LAST

%left	OR
%left	AND
%right	IMPLIES
%right	EQUIV

%right	EQUAL
%left	EQ NE
%left	GT LT GE LE
%right	NEG NOT EXCLAM TILDE
%left	STAR
%left	QUESTION

%token	OR
%token	AND
%token	IMPLIES EQUIV
%token	EQUAL

%token	EQ NE
%token	GT LT GE LE
%token	TILDE NEG NOT EXCLAM DOT SLASH PERCENT
%token	PLUS MINUS
%token	QUESTION
%token	STAR

%token	LPAREN RPAREN LBRACE RBRACE LBRACK RBRACK
%token	SEMI COLON COMMA AT
%token	EOF

%%

// ================================================================================
// formula
// ================================================================================
// precedence: neg < and < lor < implies

formula	: formula0
	  { $1 }
	| formula0 IMPLIES formula // right-assoc
	  { Ldl_impl ($1, $3) }
	| formula0 EQUIV formula
	  { Ldl_conj [Ldl_impl ($1, $3); Ldl_impl ($3, $1);] }
	| error
	  { failwith "formula" }
	;

formula0
	: formula1
	  { $1 }
	| formula0 OR formula1
	  { match $1 with Ldl_disj s -> Ldl_disj (s @ [$3]) | _ -> Ldl_disj [$1; $3] }
	;

formula1
	: formula2
	  { $1 }
	| formula1 AND formula2
	  { match $1 with Ldl_conj s -> Ldl_conj (s @ [$3]) | _ -> Ldl_conj [$1; $3] }
	;

formula2
	: formula3
	  { $1 }
//	| modal_formula
//	  { $1 }
	;

formula3
	: NAME
	  { Ldl_atomic $1 }
	| modal_path formula3
	  { Ldl_modal (fst $1, snd $1, $2) }
	| neg formula3
	  { match $2 with Ldl_neg p -> p | _ -> Ldl_neg $2 }
	| LPAREN formula RPAREN
	  { $2 }
	;

//modal_formula
//	: modal_path modal_formula
//	  { Ldl_modal (fst $1, snd $1, $2) }
//	| modal_path formula3
//	  { Ldl_modal (fst $1, snd $1, $2) }
//	;

modal_path
	: LT path GT
	  { Mod_ex, $2 }
	| LBRACK path RBRACK
	  { Mod_all, $2 }
// special cases: <> = <{true}*>, [] = [{true}*]
//	| LT GT
//	  { Mod_ex, Path_star (Path_prop (Ldl_atomic "true")) }
//	| LBRACK RBRACK
//	  { Mod_all, Path_star (Path_prop (Ldl_atomic "true")) }
	;

// negation operator
neg	: NOT
	    {}
	| EXCLAM
	    {}
	| TILDE
	    {}
	;

// ================================================================================
// path
// ================================================================================
// precedence: grouping (()) < *, ? < concat (;) < choice (+)

path	: path1
	  { $1 }
	| path PLUS path1
	  { Path_sum [$1; $3] }
	| error
	  { failwith "path" }
	;

path1	: path2
	  { $1 }
	| path1 SEMI path2
	  { match $1, $3 with
	    | Path_seq s, _ -> Path_seq (s @ [$3])
	    | _, Path_seq s -> Path_seq ($1 :: s)
	    | _ -> Path_seq [$1; $3]
	  }
	;

path2	: path3
	  { $1 }
	| LBRACE formula RBRACE QUESTION
	  { Path_test $2 }
	| LBRACE formula RBRACE QUESTION path3
	  { Path_seq [Path_test $2; $5] }
	| path3 STAR
	  { Path_star $1 }
	;

path3	: LBRACE formula RBRACE
	  { assert (Ldlsimp.propositional $2); Path_prop $2 }
	| neg path3
	  { failwith "'!path' not supported" }
	| LPAREN path RPAREN
	  { $2 }
	;	

%%
