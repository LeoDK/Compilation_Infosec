{
open Symbols
exception SyntaxError of string
exception Eof
}


let digit = ['0'-'9']
let letter = ['a'-'z' 'A'-'Z']
let id = letter (digit|letter|'_')*

rule token = parse
  | [' ' '\t' '\r'] { token lexbuf }
  | '\n' { Lexing.new_line lexbuf; token lexbuf }
  | ("0x" ['0'-'9''a'-'f''A'-'F']+) as i { SYM_INTEGER (int_of_string i) }
  | ['0'-'9']+ as i { SYM_INTEGER (int_of_string i) }
  | '+' { SYM_PLUS }
  | "->" { SYM_ARROW }
  | "&&" { SYM_BOOL_AND }
  | "||" { SYM_BOOL_OR }
  | "!" { SYM_BOOL_NOT }
  | '&' { SYM_BITWISE_AND }
  | '~' { SYM_BIT_NOT }
  | '-' { SYM_MINUS }
  | '*' { SYM_ASTERISK }
  | "//" { single_line_comment lexbuf }
  | "/*" { multi_line_comment lexbuf }
  | '/' { SYM_DIV }
  | '.' { SYM_POINT }
  | "void" { SYM_VOID }
  | "char" { SYM_CHAR }
  | "int" { SYM_INT }
  | "struct" { SYM_STRUCT }
  | "if" { SYM_IF }
  | "else" { SYM_ELSE }
  | "alloc" { SYM_ALLOC }
  | "==" { SYM_EQUALITY }
  | "=" { SYM_ASSIGN }
  | "while" { SYM_WHILE }
  | "return" { SYM_RETURN }
  | id as s { SYM_IDENTIFIER s}
  | '{' { SYM_LBRACE }
  | '}' { SYM_RBRACE }
  | '(' { SYM_LPARENTHESIS }
  | ')' { SYM_RPARENTHESIS }
  | '[' { SYM_LBRACKET }
  | ']' { SYM_RBRACKET }
  | ';' { SYM_SEMICOLON }
  | ',' { SYM_COMMA }
  | ">=" { SYM_GEQ }
  | "<=" { SYM_LEQ }
  | '>' { SYM_GT }
  | '<' { SYM_LT }
  | "!=" { SYM_NOTEQ }
  | '^' { SYM_XOR }
  | '%' { SYM_MOD }
  | '\'' { parse_char lexbuf }
  | '"' { read_string (Buffer.create 17) lexbuf  }
  | eof { SYM_EOF }
  | _ as x { failwith (Printf.sprintf "unexpected char '%c' at %s \n" x (string_of_position (Lexing.lexeme_start_p lexbuf)))}
    

and parse_char = parse
  | "\\n'" { SYM_CHARACTER '\n' }
  | "\\0'" { SYM_CHARACTER (char_of_int 0) }
  | "\\r'" { SYM_CHARACTER '\r' }
  | "\\t'" { SYM_CHARACTER '\t' }
  | _ as c '\'' { SYM_CHARACTER c}
  | _ as x { failwith (Printf.sprintf "unexpected char literal '%c'\n" x) }

and read_string buf =
  parse
  | '"'       { SYM_STRING (Buffer.contents buf) }
  | '\\' '/'  { Buffer.add_char buf '/'; read_string buf lexbuf }
  | '\\' '\\' { Buffer.add_char buf '\\'; read_string buf lexbuf }
  | '\\' 'b'  { Buffer.add_char buf '\b'; read_string buf lexbuf }
  | '\\' 'f'  { Buffer.add_char buf '\012'; read_string buf lexbuf }
  | '\\' 'n'  { Buffer.add_char buf '\n'; read_string buf lexbuf }
  | '\\' 'r'  { Buffer.add_char buf '\r'; read_string buf lexbuf }
  | '\\' 't'  { Buffer.add_char buf '\t'; read_string buf lexbuf }
  | [^ '"' '\\']+
    { Buffer.add_string buf (Lexing.lexeme lexbuf);
      read_string buf lexbuf
    }
  | _ { raise (SyntaxError ("Illegal string character: " ^ Lexing.lexeme lexbuf)) }
  | eof { raise (SyntaxError ("String is not terminated")) }

and single_line_comment = parse
  | ['\n' '\r'] { Lexing.new_line lexbuf; token lexbuf }
  | _ { single_line_comment lexbuf }

and multi_line_comment = parse
  | "*/" { token lexbuf }
  | '\n' { Lexing.new_line lexbuf; multi_line_comment lexbuf }
  | _ {multi_line_comment lexbuf}
