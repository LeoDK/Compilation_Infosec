open Batteries
open Cfg
open Prog
open Utils

(* Analyse de vivacité *)

(* [vars_in_expr e] renvoie l'ensemble des variables qui apparaissent dans [e]. *)
let rec vars_in_expr (e: expr) =
  match e with
  | Ebinop (op, e1, e2) -> Set.union (vars_in_expr e1) (vars_in_expr e2)
  | Eunop (op, e') -> vars_in_expr e'
  | Eint value -> Set.empty
  | Evar var -> Set.singleton var
  | Ecall (fname, args) -> vars_in_args args
  | Estk offset -> Set.empty
  | Eload (addr, size) -> vars_in_expr addr

and vars_in_args (e: expr list) =
  match e with
  | h::t -> Set.union (vars_in_expr h) (vars_in_args t)
  | [] -> Set.empty

(* [live_cfg_node node live_after] renvoie l'ensemble des variables vivantes
   avant un nœud [node], étant donné l'ensemble [live_after] des variables
   vivantes après ce nœud. *)
let live_cfg_node (node: cfg_node) (live_after: string Set.t) =
  match node with
  | Cassign (v, e, s) -> Set.union (vars_in_expr e) (Set.remove v live_after)
  | Creturn (e) -> vars_in_expr e
  | Ccmp (e, s1, s2) -> Set.union (vars_in_expr e) live_after
  | Cnop (s) -> live_after
  | Ccall (fname, args, s) -> Set.union (vars_in_args args) live_after
  | Cstore (addr, value, size, s) ->  let used = Set.union (vars_in_expr addr) (vars_in_expr value) in
                                      Set.union live_after used

(* [live_after_node cfg n] renvoie l'ensemble des variables vivantes après le
   nœud [n] dans un CFG [cfg]. [lives] est l'état courant de l'analyse,
   c'est-à-dire une table dont les clés sont des identifiants de nœuds du CFG et
   les valeurs sont les ensembles de variables vivantes avant chaque nœud. *)
let live_after_node cfg n (lives: (int, string Set.t) Hashtbl.t) : string Set.t =
  let succs_in = Set.filter_map (fun s -> Hashtbl.find_option lives s) (succs cfg n) in
  Set.fold (fun elem acc -> Set.union elem acc) succs_in Set.empty

(* [live_cfg_nodes cfg lives] effectue une itération du calcul de point fixe.

   Cette fonction met à jour l'état de l'analyse [lives] et renvoie un booléen
   qui indique si le calcul a progressé durant cette itération (i.e. s'il existe
   au moins un nœud n pour lequel l'ensemble des variables vivantes avant ce
   nœud a changé). *)
let live_cfg_nodes cfg (lives : (int, string Set.t) Hashtbl.t) =
  let update (n: int) (node: cfg_node) (acc: bool) =
    let new_live = live_cfg_node node (live_after_node cfg n lives) in
    let changed = match Hashtbl.find_option lives n with
                  | Some old_live -> not (Set.equal old_live new_live)
                  | None -> not (Set.is_empty new_live )
    in
    let _ = Hashtbl.replace lives n new_live in
    acc || changed
  in
  Hashtbl.fold update cfg false 

(* [live_cfg_fun f] calcule l'ensemble des variables vivantes avant chaque nœud
   du CFG en itérant [live_cfg_nodes] jusqu'à ce qu'un point fixe soit atteint.
   *)
let live_cfg_fun (f: cfg_fun) : (int, string Set.t) Hashtbl.t =
  let lives = Hashtbl.create 17 in
  let rec iter () = if (live_cfg_nodes (f.cfgfunbody) lives) then iter () else () in
  iter();
  lives
