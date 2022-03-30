open Batteries
open Elang
open Cfg
open Rtl
open Prog
open Utils
open Report
open Rtl_print
open Options

(* Une partie de la génération de RTL consiste à allouer les variables dans des
   pseudo-registres RTL.

   Ces registres sont en nombre illimité donc ce problème est facile.

   Étant donnés :
   - [next_reg], le premier numéro de registre disponible (pas encore alloué à
   une variable)
   - [var2reg], une liste d'associations dont les clés sont des variables et les
   valeurs des numéros de registres
   - [v] un nom de variable (de type [string]),

   [find_var (next_reg, var2reg) v] renvoie un triplet [(r, next_reg, var2reg)]:

   - [r] est le registre RTL associé à la variable [v]
   - [next_reg] est le nouveau premier registre disponible
   - [var2reg] est la nouvelle association nom de variable/registre.

*)
let find_var (next_reg, var2reg) v =
  match List.assoc_opt v var2reg with
    | Some r -> (r, next_reg, var2reg)
    | None -> (next_reg, next_reg + 1, assoc_set var2reg v next_reg)

(* [rtl_instrs_of_cfg_expr (next_reg, var2reg) e reg_opt] construit une liste
   d'instructions RTL correspondant à l'évaluation d'une expression E.

   Le retour de cette fonction est un quadruplet [(r,l,next_reg,var2reg)], où :
   - [r] est le registre RTL dans lequel le résultat de l'évaluation de [e] aura
     été stocké
   - [l] est une liste d'instructions RTL.
   - [next_reg] est le nouveau premier registre disponible
   - [var2reg] est la nouvelle association nom de variable/registre.
*)
let rec rtl_instrs_of_cfg_expr (next_reg, var2reg) (e: expr) =
  match e with
  | Ebinop (op, e1, e2) -> let rs1, l1, next_reg, var2reg = rtl_instrs_of_cfg_expr (next_reg, var2reg) e1 in
                           let rs2, l2, next_reg, var2reg = rtl_instrs_of_cfg_expr (next_reg, var2reg) e2 in
                           (next_reg, l1 @ l2 @ [Rbinop (op, next_reg, rs1, rs2)], next_reg+1, var2reg)
  | Eunop (op, e) -> let rs, l, n, var2reg = rtl_instrs_of_cfg_expr (next_reg, var2reg) e in
                     (next_reg, l @ [Runop (op, next_reg, rs)], next_reg+1, var2reg)
  | Eint value -> (next_reg, [Rconst (next_reg, value)], next_reg+1, var2reg)
  | Evar var -> let r, next_reg, var2reg = find_var (next_reg, var2reg) var in
                (r, [], next_reg, var2reg)
  | Ecall (fname, args) -> let rargs, l, next_reg, var2reg = rtl_instrs_of_fun_args (next_reg, var2reg) args in
                           (next_reg, l @ [Rcall (Some next_reg, fname, rargs)], next_reg+1, var2reg)
  | Estk offset -> (next_reg, [Rstk (next_reg, offset)], next_reg+1, var2reg)
  | Eload (addr, size) -> let rs, l, next_reg, var2reg = rtl_instrs_of_cfg_expr (next_reg, var2reg) addr in
                          (next_reg, l @ [Rload (next_reg, rs, size)], next_reg+1, var2reg)

and rtl_instrs_of_fun_args (next_reg, var2reg) args =
  match args with
  | h::t -> let r, l, next_reg, var2reg = rtl_instrs_of_cfg_expr (next_reg, var2reg) h in
            let rlist, llist, next_reg, var2reg = rtl_instrs_of_fun_args (next_reg, var2reg) t in
            (r::rlist, l @ llist, next_reg, var2reg)
  | [] -> ([], [], next_reg, var2reg)

let is_cmp_op =
  function Eclt -> Some Rclt
         | Ecle -> Some Rcle
         | Ecgt -> Some Rcgt
         | Ecge -> Some Rcge
         | Eceq -> Some Rceq
         | Ecne -> Some Rcne
         | _ -> None

let rtl_cmp_of_cfg_expr (e: expr) =
  match e with
  | Ebinop (b, e1, e2) ->
    (match is_cmp_op b with
     | None -> (Rcne, e, Eint 0)
     | Some rop -> (rop, e1, e2))
  | _ -> (Rcne, e, Eint 0)


let rtl_instrs_of_cfg_node ((next_reg:int), (var2reg: (string*int) list)) (c: cfg_node) =
  match c with
  | Cassign (v, e, s) -> let rd, next_reg, var2reg = find_var (next_reg, var2reg) v in
                         let rs, l, next_reg, var2reg = rtl_instrs_of_cfg_expr (next_reg, var2reg) e in
                         (l @ [Rmov (rd, rs); Rjmp s], next_reg, var2reg)
  | Creturn (e) -> let r, l, next_reg, var2reg = rtl_instrs_of_cfg_expr (next_reg, var2reg) e in
                   (l @ [Rret r], next_reg, var2reg)
  | Ccmp (e, s1, s2) -> let cmp, e1, e2 = rtl_cmp_of_cfg_expr e in
                        let rs1, l1, next_reg, var2reg = rtl_instrs_of_cfg_expr (next_reg, var2reg) e1 in
                        let rs2, l2, next_reg, var2reg = rtl_instrs_of_cfg_expr (next_reg, var2reg) e2 in
                        (l1 @ l2 @ [Rbranch (cmp, rs1, rs2, s1); Rjmp s2], next_reg, var2reg)
  | Cnop (s) -> ([Rjmp s], next_reg, var2reg)
  | Ccall (fname, args, s) -> let rargs, l, next_reg, var2reg = rtl_instrs_of_fun_args (next_reg, var2reg) args in
                              (l @ [Rcall (None, fname, rargs); Rjmp s], next_reg, var2reg)
  | Cstore (addr, value, size, s) ->  let rd, l_addr, next_reg, var2reg = rtl_instrs_of_cfg_expr (next_reg, var2reg) addr in
                                      let rs, l_value, next_reg, var2reg = rtl_instrs_of_cfg_expr (next_reg, var2reg) value in
                                      (l_addr @ l_value @ [Rstore (rd, rs, size); Rjmp s], next_reg, var2reg)

let rtl_instrs_of_cfg_fun cfgfunname cf =
  let (rargs, next_reg, var2reg) =
    List.fold_left (fun (rargs, next_reg, var2reg) a ->
        let (r, next_reg, var2reg) = find_var (next_reg, var2reg) a in
        (rargs @ [r], next_reg, var2reg)
      )
      ([], 0, []) cf.cfgfunargs
  in
  let rtlfunbody = Hashtbl.create 17 in
  let (next_reg, var2reg) = Hashtbl.fold (fun n node (next_reg, var2reg)->
      let (l, next_reg, var2reg) = rtl_instrs_of_cfg_node (next_reg, var2reg) node in
      Hashtbl.replace rtlfunbody n l;
      (next_reg, var2reg)
    ) cf.cfgfunbody (next_reg, var2reg) in
  {
    rtlfunargs = rargs;
    rtlfunentry = cf.cfgentry;
    rtlfunbody;
    rtlfuninfo = var2reg;
    rtlfunstksz = cf.cfgfunstksz;
  }

let rtl_of_gdef funname = function
    Gfun f -> Gfun (rtl_instrs_of_cfg_fun funname f)

let rtl_of_cfg cp = List.map (fun (s, gd) -> (s, rtl_of_gdef s gd)) cp

let pass_rtl_gen cfg =
  let rtl = rtl_of_cfg cfg in
  dump !rtl_dump dump_rtl_prog rtl
    (fun file () -> add_to_report "rtl" "RTL" (Code (file_contents file)));
  OK rtl
