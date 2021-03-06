open Elang
open Prog
open Utils
open Batteries
open BatList

(* Different expressions than in elang, since elang expressions can be at a higher abstraction level.
   For instance, there is no char representation of an expr, only integers (and this is how we represent all values in memory) *)
type expr =
  | Eint of int
  | Evar of string
  | Ebinop of binop * expr * expr
  | Eunop of unop * expr
  | Ecall of string * expr list
  | Estk of int
  | Eload of expr * int

(* A CFG node contains its successor id as last parameter *)
type cfg_node =
  | Cassign of string * expr * int
  | Creturn of expr
  | Ccmp of expr * int * int
  | Cnop of int
  | Ccall of string * expr list * int
  | Cstore of expr * expr * int * int

(* [cfgfunbody] is a Hashtable whose keys are CFG node unique identifiers,
   and values are cfg_node types *)
type cfg_fun = {
  cfgfunargs: string list;
  cfgfunbody: (int, cfg_node) Hashtbl.t;
  cfgentry: int;
  cfgfunstksz: int;
}

type cprog = cfg_fun prog

(* [succs cfg n] donne l'ensemble des successeurs d'un nœud [n] dans un CFG
   [cfg]. *)
let succs cfg n =
  match Hashtbl.find_option cfg n with
  | None -> Set.empty
  | Some (Cassign (_, _, s)) -> Set.singleton s
  | Some (Creturn _) -> Set.empty
  | Some (Ccmp (_, s1, s2)) -> Set.of_list [s1;s2]
  | Some (Cnop s) -> Set.singleton s
  | Some (Ccall (fname, args, s)) -> Set.singleton s
  | Some (Cstore (addr, v, size, s)) -> Set.singleton s


(* [preds cfg n] donne l'ensemble des prédécesseurs d'un nœud [n] dans un CFG [cfg]
   *)
let preds cfgfunbody n =
  Hashtbl.fold (fun m m' acc ->
      match m' with
      | Cassign (_, _, s)
      | Ccall (_,_,s)
      | Cstore (_, _, _, s)
      | Cnop s -> if s = n then Set.add m acc else acc
      | Creturn _ -> acc
      | Ccmp (_, s1, s2) -> if s1 = n || s2 = n then Set.add m acc else acc
    ) cfgfunbody Set.empty


let size_binop b e1 e2 =
  1 + e1 + e2

let size_unop u e =
  1 + e

let rec size_expr (e: expr) : int =
  match e with
  | Ebinop (b, e1, e2) -> size_binop b (size_expr e1) (size_expr e2)
  | Eunop (u, e) -> size_unop u (size_expr e)
  | Eint _
  | Estk _
  | Evar _ -> 1
  | Eload (e, size) -> 1 + size_expr e
  | Ecall (fname, args) -> 1 + List.fold_left (fun acc arg -> acc + size_expr arg) 0 args

let rec size_instr (i: cfg_node) : int =
  match (i : cfg_node) with
  | Cassign (v, e, s) -> 1 + size_expr e
  | Creturn e -> 1 + (size_expr e)
  | Ccmp (e, s1, s2) -> 1 + size_expr e
  | Cnop s -> 1
  | Ccall (fname, args, s) -> size_expr (Ecall (fname, args))
  | Cstore (addr, v, size, s) -> 1 + (size_expr addr) + (size_expr v)

let size_fun f =
  Hashtbl.fold (fun k v acc -> acc + size_instr v) f 0

