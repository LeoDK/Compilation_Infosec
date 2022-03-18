open Yaccparser
open Generated_parser
open Report
open Utils
open Options
open Ast
open Symbols


let parse = parse_S

let to_yacc_token = function
| SYM_EOF -> Yaccparser.SYM_EOF
| SYM_IDENTIFIER(s) -> Yaccparser.SYM_IDENTIFIER s
| SYM_INTEGER(i) -> Yaccparser.SYM_INTEGER i
| SYM_VOID -> Yaccparser.SYM_VOID
| SYM_CHAR -> Yaccparser.SYM_CHAR
| SYM_INT -> Yaccparser.SYM_INT
| SYM_STRUCT -> Yaccparser.SYM_STRUCT
| SYM_SEMICOLON -> Yaccparser.SYM_SEMICOLON
| SYM_POINT -> Yaccparser.SYM_POINT
| SYM_IF -> Yaccparser.SYM_IF
| SYM_ELSE -> Yaccparser.SYM_ELSE
| SYM_PLUS -> Yaccparser.SYM_PLUS
| SYM_MINUS -> Yaccparser.SYM_MINUS
| SYM_ASTERISK -> Yaccparser.SYM_ASTERISK
| SYM_DIV -> Yaccparser.SYM_DIV
| SYM_EQUALITY -> Yaccparser.SYM_EQUALITY
| SYM_ASSIGN -> Yaccparser.SYM_ASSIGN
| SYM_LPARENTHESIS -> Yaccparser.SYM_LPARENTHESIS
| SYM_RPARENTHESIS -> Yaccparser.SYM_RPARENTHESIS
| SYM_LBRACE -> Yaccparser.SYM_LBRACE
| SYM_RBRACE -> Yaccparser.SYM_RBRACE
| SYM_WHILE -> Yaccparser.SYM_WHILE
| SYM_RETURN -> Yaccparser.SYM_RETURN
| SYM_COMMA -> Yaccparser.SYM_COMMA
| SYM_LT -> Yaccparser.SYM_LT
| SYM_LEQ -> Yaccparser.SYM_LEQ
| SYM_GT -> Yaccparser.SYM_GT
| SYM_GEQ -> Yaccparser.SYM_GEQ
| SYM_NOTEQ -> Yaccparser.SYM_NOTEQ
| SYM_MOD -> Yaccparser.SYM_MOD
| SYM_BOOL_NOT -> Yaccparser.SYM_BOOL_NOT
| SYM_BOOL_AND -> Yaccparser.SYM_BOOL_AND
| SYM_BOOL_OR -> Yaccparser.SYM_BOOL_OR
| SYM_ARROW -> Yaccparser.SYM_ARROW
| SYM_BITWISE_OR -> Yaccparser.SYM_BITWISE_OR
| SYM_BITWISE_AND -> Yaccparser.SYM_BITWISE_AND
| SYM_BIT_NOT -> Yaccparser.SYM_BIT_NOT
| SYM_XOR -> Yaccparser.SYM_XOR
| SYM_CHARACTER(c) -> Yaccparser.SYM_CHARACTER c
| SYM_STRING(s) -> Yaccparser.SYM_STRING s
| SYM_LBRACKET -> Yaccparser.SYM_LBRACKET
| SYM_RBRACKET -> Yaccparser.SYM_RBRACKET
| SYM_ALLOC -> Yaccparser.SYM_ALLOC
| SYM_EXTERN -> Yaccparser.SYM_EXTERN
| SYM_INCLUDE(s) -> Yaccparser.SYM_INCLUDE s
| SYM_AMPERSAND -> Yaccparser.SYM_AMPERSAND

let advance (l: ('a list * 'a list)) : ('a * ('a list * 'a list)) option =
  let lbef, laft = l in
  match laft with
    [] -> None
  | a::r -> Some (a, (a::lbef, r))

let back (l: ('a list * 'a list)) : ('a list * 'a list) option =
  let lbef, laft = l in
  match lbef with
    [] -> None
  | a::r -> Some ((r, a::laft))




let menhir_parser (toks: (Symbols.token * Lexing.position option) list) () =
  let mtoks = ref ([], toks) in
  let get_tok () =
    match advance !mtoks with
    | None -> (Yaccparser.SYM_EOF, Lexing.dummy_pos, Lexing.dummy_pos)
    | Some ((t, p), l) ->
      mtoks := l;
      (to_yacc_token t, Lexing.dummy_pos, Lexing.dummy_pos)
  in
  let mparser = MenhirLib.Convert.Simplified.traditional2revised Yaccparser.main in
  match mparser get_tok with
  | ast -> OK (ast, [])
  | exception Yaccparser.Error ->
    match back !mtoks with
    | None  ->  Error (Printf.sprintf "Parser error while reading '???'\n")
    | Some (lbef, laft) ->
    Error (Printf.sprintf "Parser error while reading '%s'\n"
              (String.concat " " (List.map (fun (t, _) -> string_of_symbol t) (take 20 laft)))
           )

let parser toks () =
  if !Options.alpaga_parser
  then parse toks ()
  else menhir_parser toks ()

let pass_parse tokens =
  match parser tokens () with
  | Error msg -> record_compile_result ~error:(Some msg) "Parsing"; Error msg
  | OK (ast, tokens) ->
    record_compile_result "Parsing";
    dump !ast_tree draw_ast_tree ast (call_dot "ast" "AST");
    if !ast_dump then Format.printf "%s\n" (string_of_ast ast) else ();
    OK (ast, tokens)
