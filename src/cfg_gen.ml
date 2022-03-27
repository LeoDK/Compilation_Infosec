open Batteries
open Elang
open Elang_gen
open Cfg
open Utils
open Prog
open Report
open Cfg_print
open Options

(* cfg_expr_of_eexpr converts an [Elang.expr] into a [Cfg.expr res].
   [typ_var] is a hashtable which contains the type of each local variable
   [typ_fun] is a hashtable which contains the signature of each encountered function so far
   [funvarinmem] is a hashtable which gives the offset (from the stack pointer) of a given variable saved in memory
   [e] is the Elang expression to convert
*)
let rec cfg_expr_of_eexpr (typ_var: (string, typ) Hashtbl.t) (typ_fun: (string, typ list * typ) Hashtbl.t)
                          (funvarinmem: (string, int) Hashtbl.t) (e: Elang.expr) : expr res =
  match e with

  | Elang.Eint i -> OK (Eint i)

  | Elang.Echar c -> OK (Eint (Char.code c))

  | Elang.Ebinop (b, e1, e2) ->
    type_expr typ_var typ_fun e1 >>= fun t1 ->
    type_expr typ_var typ_fun e2 >>= fun t2 ->
    cfg_expr_of_eexpr typ_var typ_fun funvarinmem e1 >>= fun cfg_e1 ->
    cfg_expr_of_eexpr typ_var typ_fun funvarinmem e2 >>= fun cfg_e2 ->
    begin match (t1, t2) with
    (* *(p + i) actually points to p + sizeof( *p ) * i *)
    | (Tptr t1', _) ->  size_type t1' >>= fun s1 ->
                        OK (Ebinop (b, cfg_e1, Ebinop (Emul, cfg_e2, Eint s1)))
    | (_, Tptr t2') ->  size_type t2' >>= fun s2 ->
                        OK (Ebinop (b, Ebinop (Emul, cfg_e1, Eint s2), cfg_e2))
    | (_, _) -> OK (Ebinop (b, cfg_e1, cfg_e2))
    end

  | Elang.Eunop (u, e) ->
    cfg_expr_of_eexpr typ_var typ_fun funvarinmem e >>= fun cfg_e ->
    OK (Eunop (u, cfg_e))

  | Elang.Evar v ->
    begin match Hashtbl.find_option funvarinmem v with
    | Some addr ->  type_expr typ_var typ_fun e >>= fun t ->
                    size_type t >>= fun size ->
                    OK (Eload (Estk addr, size))
    | None -> OK (Evar v)
    end

  | Elang.Efuncall (funname, args) ->
    cfg_exprs_of_args typ_var typ_fun funvarinmem args >>= fun cfg_args ->
    OK (Ecall (funname, cfg_args))

  | Elang.Eaddrof v ->
    begin match Hashtbl.find_option funvarinmem v with
    | Some addr -> OK (Estk addr)
    | None -> Error (Printf.sprintf "%s is not located in memory in cfg_expr_of_eexpr !\n" v)
    end

  | Elang.Eload e' ->   cfg_expr_of_eexpr typ_var typ_fun funvarinmem e' >>= fun cfg_e' ->
                        type_expr typ_var typ_fun e >>= fun t ->
                        size_type t >>= fun size ->
                        OK (Eload (cfg_e', size))

(* In case of a function call, we use this function to convert all parameters (which are expressions)
   to CFG expressions *)
and cfg_exprs_of_args typ_var typ_fun funvarinmem (args: Elang.expr list) : expr list res =
  match args with
  | h::t -> cfg_expr_of_eexpr typ_var typ_fun funvarinmem h >>= fun cfg_h ->
            cfg_exprs_of_args typ_var typ_fun funvarinmem t >>= fun cfg_t ->
            OK (cfg_h::cfg_t)
  | [] -> OK ([])

(* [cfg_node_of_einstr next cfg succ i] builds the CFG node(s) that correspond
   to the E instruction [i].

   [cfg] is the current state of the control-flow graph.

   [succ] is the successor of this node in the CFG, i.e. where to go after this
   instruction.

   [next] is the next available CFG node identifier.

   This function returns a pair (n, next) where [n] is the identifer of the
   node generated, and [next] is the new next available CFG node identifier.

   Hint: several nodes may be generated for a single E instruction.
*)
let rec cfg_node_of_einstr  (typ_var: (string, typ) Hashtbl.t) (typ_fun: (string, typ list * typ) Hashtbl.t) (funvarinmem: (string, int) Hashtbl.t)
                            (next: int) (cfg : (int, cfg_node) Hashtbl.t) (succ: int) (i: instr) : (int * int) res =
  match i with

  | Elang.Iassign (v, e) ->
    cfg_expr_of_eexpr typ_var typ_fun funvarinmem e >>= fun cfg_e ->
    begin match Hashtbl.find_option funvarinmem v with
    | Some addr ->  type_expr typ_var typ_fun e >>= fun t ->
                    size_type t >>= fun size ->
                    Hashtbl.replace cfg next (Cstore (Estk addr, cfg_e, size, succ));
                    OK (next, next + 1)
    | None -> Hashtbl.replace cfg next (Cassign (v, cfg_e, succ)); 
              OK (next, next + 1)
    end;

  | Elang.Iif (c, ithen, ielse) ->
    cfg_expr_of_eexpr typ_var typ_fun funvarinmem c >>= fun cfg_c ->
    cfg_node_of_einstr typ_var typ_fun funvarinmem next cfg succ ithen >>= fun (nthen, next) ->
    cfg_node_of_einstr typ_var typ_fun funvarinmem next cfg succ ielse  >>= fun (nelse, next) ->
    Hashtbl.replace cfg next (Ccmp(cfg_c, nthen, nelse));
    OK (next, next + 1)

  | Elang.Iwhile (c, i) ->
    cfg_expr_of_eexpr typ_var typ_fun funvarinmem c >>= fun cfg_c ->
    let (cmp, next) = (next, next+1) in
    cfg_node_of_einstr typ_var typ_fun funvarinmem next cfg cmp i >>= fun (nthen, next) ->
    Hashtbl.replace cfg cmp (Ccmp(cfg_c, nthen, succ));
    OK (cmp, next + 1)

  | Elang.Iblock il ->
    List.fold_right (fun i acc ->
        acc >>= fun (succ, next) ->
        cfg_node_of_einstr typ_var typ_fun funvarinmem next cfg succ i
      ) il (OK (succ, next))

  | Elang.Ireturn e ->
    cfg_expr_of_eexpr typ_var typ_fun funvarinmem e >>= fun cfg_e ->
    Hashtbl.replace cfg next (Creturn cfg_e); OK (next, next + 1)

  | Elang.Ifuncall (funname, args) ->
    cfg_exprs_of_args typ_var typ_fun funvarinmem args >>= fun cfg_args ->
    Hashtbl.replace cfg next (Ccall (funname, cfg_args, succ));
    OK (next, next+1)

  | Elang.Ideclaration v ->
    Hashtbl.replace cfg next (Cnop(succ));
    OK (next, next+1)

  | Elang.Istore (addr, value) ->
    cfg_expr_of_eexpr typ_var typ_fun funvarinmem addr >>= fun cfg_addr ->
    cfg_expr_of_eexpr typ_var typ_fun funvarinmem value >>= fun cfg_value ->
    type_expr typ_var typ_fun value >>= fun t ->
    size_type t >>= fun size ->
    Hashtbl.replace cfg next (Cstore (cfg_addr, cfg_value, size, succ));
    OK (next, next+1)

(* Some nodes may be unreachable after the CFG is entirely generated.
   [reachable_nodes n cfg] constructs the set of node identifiers that are
   reachable from the entry node [n]. *)
let rec reachable_nodes n (cfg: (int,cfg_node) Hashtbl.t) =
  let rec reachable_aux n reach =
    if Set.mem n reach then reach
    else let reach = Set.add n reach in
      match Hashtbl.find_option cfg n with
      | None -> reach
      | Some (Cnop succ)
      | Some (Ccall (_, _, succ))
      | Some (Cstore (_, _, _, succ))
      | Some (Cassign (_, _, succ)) -> reachable_aux succ reach
      | Some (Creturn _) -> reach
      | Some (Ccmp (_, s1, s2)) ->
        reachable_aux s1 (reachable_aux s2 reach)
  in reachable_aux n Set.empty

(* [cfg_fun_of_efun f] builds the CFG for E function [ef]. *)
let cfg_fun_of_efun typ_fun ef =
  let cfg = Hashtbl.create 17 in
  Hashtbl.replace cfg 0 (Creturn (Eint 0));
  cfg_node_of_einstr ef.funvartype typ_fun ef.funvarinmem 1 cfg 0 ef.funbody >>= fun (node, _) ->
  (* remove unreachable nodes *)
  let r = reachable_nodes node cfg in
  Hashtbl.filteri_inplace (fun k _ -> Set.mem k r) cfg;
  (* Add current function to known functions *)
  OK { cfgfunargs = (List.map fst ef.funargs);
       cfgfunbody = cfg;
       cfgentry = node;
       cfgfunstksz = ef.funstksz;
     }

let cfg_gdef_of_edef typ_fun gname (gd : efun gdef): cfg_fun gdef res =
  match gd with
    Gfun ef ->  cfg_fun_of_efun typ_fun ef >>= fun cf ->
                Hashtbl.replace typ_fun gname ((List.map snd ef.funargs), ef.funrettype);
                OK (Gfun cf)

let cfg_prog_of_eprog (ep: eprog) : cfg_fun prog res =
  let aux (acc: (((string, (typ list * typ)) Hashtbl.t) * cprog) res) ((e_gname, e_gd): string * efun gdef) =
    acc >>= fun (typ_fun, cp) ->
    cfg_gdef_of_edef typ_fun e_gname e_gd >>= fun cfg_gd ->
    OK (typ_fun, cp@[(e_gname, cfg_gd)])
  in
  let typ_fun = Hashtbl.create (List.length ep) in
  List.fold_left aux (OK (typ_fun, [])) ep >>= fun (typ_fun, cp) ->
  OK (cp)

let pass_cfg_gen ep =
  match cfg_prog_of_eprog ep with
  | Error msg ->
    record_compile_result ~error:(Some msg) "CFG"; Error msg
  | OK cfg ->
    record_compile_result "CFG";
    dump !cfg_dump dump_cfg_prog cfg (call_dot "cfg" "CFG");
    OK cfg
