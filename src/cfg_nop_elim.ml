open BatList
open Batteries
open Prog
open Utils
open Cfg
open Report
open Cfg_print
open Options

(* Élimination des NOPs. *)

(* [nop_transitions cfg] donne la liste des transitions NOP dans un CFG.
   Si le nœud [n] contient [Cnop s], alors [(n,s)] devrait être dans le résultat.
*)
let nop_transitions (cfgfunbody: (int, cfg_node) Hashtbl.t) : (int * int) list =
  let get_list key value acc =
    match value with
    | Cnop s -> (key,s)::acc
    | _ -> acc
  in
  Hashtbl.fold get_list cfgfunbody []


(* [follow n l visited] donne le premier successeur à partir de [n] qui ne soit
   pas un NOP. Pour connaître le successeur d'un nœud NOP, on utilisera la liste
   [l] telle que produite précédemment. Pour rappel [(x,y)] dans [l] signifie
   qu'il y a un transition depuis un nœud [x] qui contient une instruction [Cnop
   y].

   L'ensemble [visited] est utilisé pour éviter les boucles.
   *)
let rec follow (n: int) (l: (int * int) list) (visited: int Set.t) : int =
  if Set.mem n visited then
    -1 (* On a déjà visité ce noeud et on n'a pas trouvé de non NOP, on renvoie -1 *)
  else
  (* Si on a un nop, cette liste représente tous ses successeurs *)
  let s = List.fold_left (fun acc (n',s) -> if n'=n then Set.add s acc else acc) Set.empty l in
  if Set.cardinal s = 0 then
    n (* pas un nop *)
  else
    Set.fold (fun elem acc -> if acc = -1 then (follow elem l (Set.add n visited)) else acc) s (-1)

(* [nop_transitions_closed] contient la liste [(n,s)] telle que l'instruction au
   nœud [n] est le début d'une chaîne de NOPs qui termine au nœud [s]. Les
   enseignants du cours de compilation sont heureux de vous offrir cette
   fonction. *)
let nop_transitions_closed cfgfunbody =
  List.map (fun (node_id, node) ->
      (node_id, follow node_id (nop_transitions cfgfunbody) Set.empty))
    (nop_transitions cfgfunbody)

(* Nous allons maintenant réécrire notre programme pour remplacer les
   successeurs [s] de chaque nœud du CFG de la manière suivante : si [s] est le
   début d'une chaîne de NOPs, on remplace [s] par la fin de cette chaîne, en
   éliminant ainsi les nœuds NOPs. *)

(* [replace_succ nop_succs s] donne le nouveau nom du nœud [s], en utilisant la
   liste [nop_succs] (telle que renvoyée par [nop_transitions_closed]). *)
let replace_succ nop_succs s : int =
  List.fold_left (fun acc (n,s') -> if n=s then s' else acc) s nop_succs

(* [replace_succs nop_succs n] remplace le nœud [n] par un nœud équivalent où on
   a remplacé les successeurs, en utilisant la liste [nop_succs]. *)
let replace_succs nop_succs (n: cfg_node) =
  match n with
  | Cassign (v,e,s) -> Cassign (v,e,replace_succ nop_succs s)
  | Creturn e -> Creturn e
  | Cprint (e,s) -> Cprint (e,replace_succ nop_succs s)
  | Ccmp (e,s1,s2) -> Ccmp (e, replace_succ nop_succs s1, replace_succ nop_succs s2)
  | Cnop s -> Cnop (replace_succ nop_succs s)

(*
(* [nop_elim_fun f] applique la fonction [replace_succs] à chaque nœud du CFG. *)
let nop_elim_fun ({ cfgfunargs; cfgfunbody; cfgentry } as f: cfg_fun) =
  let nop_transf = nop_transitions_closed cfgfunbody in
  (* On utilise la fonction [Hashtbl.filter_map f h] qui permet d'appliquer une
     fonction à chaque nœud de [h] et d'éliminer ceux pour lesquels [f] renvoie
     [None].

     On souhaite éliminer les nœuds qui n'ont pas de prédécesseurs
     (inaccessibles), et appliquer la fonction [replace_succs] aux nœuds qui
     resteront.
  *)
  let cfgfunbody = Hashtbl.filter_map (fun n node ->
      Some node
    ) cfgfunbody in
  (* La fonction renvoyée est composée du nouveau [cfgfunbody] que l'on vient de
     calculer, et le point d'entrée est transformé en conséquence. *)
  {f with cfgfunbody; cfgentry = replace_succ nop_transf cfgentry }
*)

let nop_elim_fun ({ cfgfunargs; cfgfunbody; cfgentry } as f: cfg_fun) =
  let nop_succs = nop_transitions_closed cfgfunbody in
  (* On commence par remplacer chaque successeur *)
  let cfgfunbody = Hashtbl.map (fun n node -> replace_succs nop_succs node) cfgfunbody in
  (* On enlève tous les noeuds inaccessibles (sans prédecesseurs) *)
  (* Cas particulier : noeud d'entrée (2 cas) : si pas NOP, il faut le conserver *)
  let replace n node =
    if n=cfgentry then
      match node with
      | Cnop s -> None
      | _ -> Some node
    else
      if Set.cardinal (preds cfgfunbody n) = 0 then
        None
      else
        Some node
  in
  let cfgfunbody = Hashtbl.filter_map replace cfgfunbody in
  {f with cfgfunbody; cfgentry = replace_succ nop_succs cfgentry}

let nop_elim_gdef gd =
  match gd with
    Gfun f -> Gfun (nop_elim_fun f)

let nop_elimination cp =
  if !Options.no_cfg_ne
  then cp
  else assoc_map nop_elim_gdef cp

let pass_nop_elimination cfg =
  let cfg = nop_elimination cfg in
  record_compile_result "NopElim";
  dump (!cfg_dump >*> fun s -> s ^ "3") dump_cfg_prog cfg
    (call_dot "cfg-after-nop" "CFG after NOP elim");
  OK cfg
