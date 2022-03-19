tokens SYM_EOF SYM_IDENTIFIER<string> SYM_INTEGER<int> SYM_CHARACTER<char> SYM_VOID
tokens SYM_PLUS SYM_MINUS SYM_ASTERISK SYM_DIV SYM_MOD
tokens SYM_LPARENTHESIS SYM_RPARENTHESIS SYM_LBRACE SYM_RBRACE
tokens SYM_ASSIGN SYM_SEMICOLON SYM_RETURN SYM_IF SYM_WHILE SYM_ELSE SYM_COMMA
tokens SYM_EQUALITY SYM_NOTEQ SYM_LT SYM_LEQ SYM_GT SYM_GEQ
tokens SYM_VOID SYM_INT SYM_CHAR
non-terminals S INSTR INSTRS BLOC ELSE EXPR FACTOR
non-terminals INSTR_DECLARATION_RIGHT INSTR_IDENTIFIER_RIGHT 
non-terminals LPARAMS_DECLARATION REST_PARAMS_DECLARATION
non-terminals LPARAMS_EXPR REST_PARAMS_EXPR
non-terminals IDENTIFIER INTEGER CHARACTER
non-terminals FUNDEF FUNDEFS
non-terminals FACTOR_IDENTIFIER_RIGHT FUNCALL
non-terminals ADD_EXPRS ADD_EXPR
non-terminals MUL_EXPRS MUL_EXPR
non-terminals CMP_EXPRS CMP_EXPR
non-terminals EQ_EXPRS EQ_EXPR
non-terminals TYPE
axiom S
{
  open Symbols
  open Ast
  open BatPrintf
  open BatBuffer
  open Batteries
  open Utils

  let rec resolve_associativity (term: tree) (other: (tag*tree) list) : tree =
    match other with
    | [] -> term
    | (next_tag, next_tree)::tail -> resolve_associativity (Node (next_tag, [term; next_tree])) tail
}

rules
S -> FUNDEFS SYM_EOF { Node (Tlistglobdef, $1) }
FUNDEFS -> FUNDEF FUNDEFS { $1::$2 }
FUNDEFS -> { [] }
FUNDEF -> TYPE SYM_IDENTIFIER SYM_LPARENTHESIS LPARAMS_DECLARATION SYM_RPARENTHESIS INSTR { Node (Tfundef, [ $1;
                                                                                                    Node (Tfunname, [StringLeaf $2]);
                                                                                                    Node (Tfunargs, $4);
                                                                                                    Node (Tfunbody, [$6]) ]) }
TYPE -> SYM_VOID { Node (Ttype, [StringLeaf "void"]) }
TYPE -> SYM_INT { Node (Ttype, [StringLeaf "int"]) }
TYPE -> SYM_CHAR { Node (Ttype, [StringLeaf "char"]) }

LPARAMS_DECLARATION -> TYPE IDENTIFIER REST_PARAMS_DECLARATION { Node (Tdeclaration, [$1; $2])::$3 }
LPARAMS_DECLARATION -> { [] }
REST_PARAMS_DECLARATION -> SYM_COMMA LPARAMS_DECLARATION { $2 }
REST_PARAMS_DECLARATION -> { [] }

LPARAMS_EXPR -> EXPR REST_PARAMS_EXPR { $1::$2 }
LPARAMS_EXPR -> { [] }
REST_PARAMS_EXPR -> SYM_COMMA LPARAMS_EXPR { $2 }
REST_PARAMS_EXPR -> { [] }


INSTR -> SYM_IF SYM_LPARENTHESIS EXPR SYM_RPARENTHESIS BLOC ELSE { Node (Tif, [ $3; $5; $6 ]) }
INSTR -> SYM_WHILE SYM_LPARENTHESIS EXPR SYM_RPARENTHESIS INSTR { Node (Twhile, [ $3; $5 ]) }
INSTR -> SYM_RETURN EXPR SYM_SEMICOLON { Node (Treturn, [$2]) }
INSTR -> BLOC { $1 }
INSTR -> TYPE IDENTIFIER INSTR_DECLARATION_RIGHT { $3 (Node (Tdeclaration, [$1;$2])) }
INSTR_DECLARATION_RIGHT -> SYM_ASSIGN EXPR SYM_SEMICOLON { fun x -> Node (Tassign, [x; $2]) }
INSTR_DECLARATION_RIGHT -> SYM_SEMICOLON { fun x -> x }
INSTR -> IDENTIFIER INSTR_IDENTIFIER_RIGHT { $2 $1 }
INSTR_IDENTIFIER_RIGHT -> SYM_ASSIGN EXPR SYM_SEMICOLON { fun x -> Node (Tassign, [ x; $2 ]) }
INSTR_IDENTIFIER_RIGHT -> FUNCALL SYM_SEMICOLON { $1 }
FUNCALL -> SYM_LPARENTHESIS LPARAMS_EXPR SYM_RPARENTHESIS { fun x -> Node (Tfuncall, [ Node (Tfunname, [x]);
                                                                                       Node (Tfunargs, $2) ]) }

EXPR -> EQ_EXPR EQ_EXPRS { resolve_associativity $1 $2 }
EQ_EXPR -> CMP_EXPR CMP_EXPRS { resolve_associativity $1 $2 }
CMP_EXPR -> ADD_EXPR ADD_EXPRS { resolve_associativity $1 $2 }
ADD_EXPR -> MUL_EXPR MUL_EXPRS { resolve_associativity $1 $2 }
MUL_EXPR -> FACTOR { $1 }
FACTOR -> SYM_MINUS FACTOR { Node (Tneg, [$2]) }
FACTOR -> IDENTIFIER FACTOR_IDENTIFIER_RIGHT { $2 $1 }
FACTOR_IDENTIFIER_RIGHT -> FUNCALL { $1 }
FACTOR_IDENTIFIER_RIGHT -> { fun x -> x }
FACTOR -> INTEGER { $1 }
FACTOR -> CHARACTER { $1 }
FACTOR -> SYM_LPARENTHESIS EXPR SYM_RPARENTHESIS { $2 }
IDENTIFIER -> SYM_IDENTIFIER { Node (Tidentifier, [StringLeaf $1]) }
INTEGER -> SYM_INTEGER { Node (Tint, [IntLeaf $1]) }
CHARACTER -> SYM_CHARACTER { Node (Tchar, [CharLeaf $1]) }

MUL_EXPRS -> SYM_ASTERISK MUL_EXPR MUL_EXPRS { (Tmul, $2)::$3 }
MUL_EXPRS -> SYM_DIV MUL_EXPR MUL_EXPRS { (Tdiv, $2)::$3 }
MUL_EXPRS -> SYM_MOD MUL_EXPR MUL_EXPRS { (Tmod, $2)::$3 }
MUL_EXPRS -> { [] }
ADD_EXPRS -> SYM_PLUS ADD_EXPR ADD_EXPRS { (Tadd, $2)::$3 }
ADD_EXPRS -> SYM_MINUS ADD_EXPR ADD_EXPRS { (Tsub, $2)::$3 }
ADD_EXPRS -> { [] }
CMP_EXPRS -> SYM_NOTEQ CMP_EXPR CMP_EXPRS { (Tcne, $2)::$3 }
CMP_EXPRS -> SYM_LT CMP_EXPR CMP_EXPRS { (Tclt, $2)::$3 }
CMP_EXPRS -> SYM_LEQ CMP_EXPR CMP_EXPRS { (Tcle, $2)::$3 }
CMP_EXPRS -> SYM_GT CMP_EXPR CMP_EXPRS { (Tcgt, $2)::$3 }
CMP_EXPRS -> SYM_GEQ CMP_EXPR CMP_EXPRS { (Tcge, $2)::$3 }
CMP_EXPRS -> { [] }
EQ_EXPRS -> SYM_EQUALITY EQ_EXPR EQ_EXPRS { (Tceq, $2)::$3 }
EQ_EXPRS -> { [] }
ELSE -> SYM_ELSE INSTR { $2 }
ELSE -> { NullLeaf }
BLOC -> SYM_LBRACE INSTRS SYM_RBRACE { Node (Tblock, $2) }
INSTRS -> INSTR INSTRS { $1::$2 }
INSTRS -> { [] }
