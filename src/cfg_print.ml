open Batteries
open Cfg
open Elang_print
open Prog
open Utils

let rec dump_cfgexpr : expr -> string = function
  | Ebinop(b, e1, e2) -> Format.sprintf "(%s %s %s)" (dump_cfgexpr e1) (dump_binop b) (dump_cfgexpr e2)
  | Eunop(u, e) -> Format.sprintf "(%s %s)" (dump_unop u) (dump_cfgexpr e)
  | Eint i -> Format.sprintf "%d" i
  | Evar s -> Format.sprintf "%s" s
  | Ecall (fname, args) -> Format.sprintf "%s(%s)" fname (dump_cfgcall_args args)

and dump_cfgcall_args (args: expr list) : string =
  match args with
  | h::t -> let tdump = (dump_cfgcall_args t) in
            if String.length tdump <> 0 then
              (dump_cfgexpr h) ^ "," ^ (dump_cfgcall_args t)
            else
              dump_cfgexpr h
  | [] -> ""

let dump_list_cfgexpr l =
  l |> List.map dump_cfgexpr |> String.concat ", "


let dump_arrows oc fname n (node: cfg_node) =
  match node with
  | Cassign (_, _, succ)
  | Cnop succ ->
    Format.fprintf oc "n_%s_%d -> n_%s_%d\n" fname n fname succ
  | Creturn _ -> ()
  | Ccmp (_, succ1, succ2) ->
    Format.fprintf oc "n_%s_%d -> n_%s_%d [label=\"then\"]\n" fname n fname succ1;
    Format.fprintf oc "n_%s_%d -> n_%s_%d [label=\"else\"]\n" fname n fname succ2
  | Ccall (funname, args, s) ->
    Format.fprintf oc "n_%s_%d -> n_%s_%d\n" fname n fname s


let dump_cfg_node oc (node: cfg_node) =
  match node with
  | Cassign (v, e, _) -> Format.fprintf oc "%s = %s" v (dump_cfgexpr e)
  | Creturn e -> Format.fprintf oc "return %s" (dump_cfgexpr e)
  | Ccmp (e, _, _) -> Format.fprintf oc "%s" (dump_cfgexpr e)
  | Cnop _ -> Format.fprintf oc "nop"
  | Ccall (fname, args, s) -> Format.fprintf oc "call %s(%s)" fname (dump_cfgcall_args args)


let dump_liveness_state oc ht state =
  Hashtbl.iter (fun n cn ->
      Format.fprintf oc "%a : " dump_cfg_node cn;
      let vs = Hashtbl.find_default state n Set.empty in
      Set.iter (fun v ->Format.fprintf oc "%s, " v) vs;
      Format.fprintf oc "\n";
      flush_all ()
    ) ht

let dump_cfg_fun oc cfgfunname ({ cfgfunargs; cfgfunbody; cfgentry; }: cfg_fun) =
  Format.fprintf oc "subgraph cluster_%s {\n label=\"%s\";\n" cfgfunname cfgfunname;
  Hashtbl.iter (fun n node ->
      Format.fprintf oc "n_%s_%d [label=\"%a\" xlabel=\"%d\" shape=%s];\n" cfgfunname n dump_cfg_node node n (if n = cfgentry then "rectangle peripheries=2" else "rectangle");
      dump_arrows oc cfgfunname n node
    ) cfgfunbody;
  Format.fprintf oc "}\n"

let dump_cfg_prog oc (cp: cprog) =
  Format.fprintf oc "digraph G{\n";
  dump_prog dump_cfg_fun oc cp;
  Format.fprintf oc "\n}"

