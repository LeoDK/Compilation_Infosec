open Ast
open Batteries
open Prog
open Utils

type binop = Eadd | Emul | Emod | Exor | Ediv | Esub (* binary operations *)
           | Eclt | Ecle | Ecgt | Ecge | Eceq | Ecne (* comparisons *)
type unop = Eneg

type expr =
  | Ebinop of binop * expr * expr
  | Eunop of unop * expr
  | Eint of int
  | Echar of char
  | Evar of string
  | Efuncall of string * expr list

type instr =
  | Iassign of string * expr
  | Iif of expr * instr * instr
  | Iwhile of expr * instr
  | Iblock of instr list
  | Ireturn of expr
  | Ifuncall of string * expr list
  | Ideclaration of string

type efun = {
  funargs: (string * typ) list;
  funbody: instr;
  funvartype: (string, typ) Hashtbl.t;
  funrettype: typ;
}

type eprog = efun prog
