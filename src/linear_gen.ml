open Batteries
open Rtl
open Linear
open Prog
open Utils
open Report
open Linear_print
open Options
open Linear_liveness

let succs_of_rtl_instr (i: rtl_instr) =
  match i with
  | Rtl.Rbranch (_, _, _, s1) -> [s1]
  | Rtl.Rjmp s -> [s]
  | _ -> []

let rec succs_of_rtl_instrs il : int list =
  List.concat (List.map succs_of_rtl_instr il)

(* effectue un tri topologique des blocs.  *)

let sort_blocks (nodes: (int, rtl_instr list) Hashtbl.t) (entry: int) =
  let rec add_block order n =
    let il = Hashtbl.fold (fun n' il' acc -> if n=n' then il' else acc) nodes [] in
    let succs = succs_of_rtl_instrs il in
    let new_succs = List.filter (fun x -> not (List.mem x order)) succs in
    List.fold_left add_block (order@[n]) new_succs
  in add_block [] entry

(* Supprime les jumps inutiles (Jmp à un label défini juste en dessous). *)
let rec remove_useless_jumps (l: rtl_instr list) =
  match l with
  | [] -> []
  | (Rtl.Rjmp s)::(Rtl.Rlabel label)::t -> let t' = remove_useless_jumps t in
                                          if (s = label)
                                          then (Rtl.Rlabel label)::t'
                                          else (Rtl.Rjmp s)::(Rtl.Rlabel label)::t'
  | h::t -> h::(remove_useless_jumps t)


(* Remove labels that are never jumped to. *)
let remove_useless_labels (l: rtl_instr list) =
  let f label acc elem =
    match elem with
    | Rtl.Rjmp s -> acc || (s=label)
    | Rtl.Rbranch(cmp, rs1, rs2, s) -> acc || (s=label)
    | _ -> acc
  in
  let is_useful_label label =
    List.fold_left (f label) false l
  in
  let is_useful_instr i =
    match i with
    | Rtl.Rlabel label -> is_useful_label label
    | _ -> true
  in
  List.filter is_useful_instr l


let linear_of_rtl_fun rf =
  let block_order = sort_blocks rf.rtlfunbody rf.rtlfunentry in
  let linearinstrs =
    Rjmp rf.rtlfunentry ::
    List.fold_left (fun l n ->
        match Hashtbl.find_option rf.rtlfunbody n with
        | None -> l
        | Some li -> l @ Rlabel(n) :: li
      ) [] block_order in
  { linearfunargs = rf.rtlfunargs;
    linearfunbody =
      linearinstrs |> remove_useless_jumps |> remove_useless_labels;
    linearfuninfo = rf.rtlfuninfo;
    linearfunstksz = rf.rtlfunstksz;
  }

let linear_of_rtl_gdef = function
    Gfun f -> Gfun (linear_of_rtl_fun f)

let linear_of_rtl r =
  assoc_map linear_of_rtl_gdef r

let pass_linearize rtl =
  let linear = linear_of_rtl rtl in
  let lives = liveness_linear_prog linear in
  dump !linear_dump (fun oc -> dump_linear_prog oc (Some lives)) linear
    (fun file () -> add_to_report "linear" "Linear" (Code (file_contents file)));
  OK (linear, lives)
