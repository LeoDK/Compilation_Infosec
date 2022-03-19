open Elang
open Batteries
open BatList
open Prog
open Utils
open Builtins
open Utils

let binop_bool_to_int f x y = if f x y then 1 else 0

(* [eval_binop b x y] évalue l'opération binaire [b] sur les arguments [x]
   et [y]. *)
let eval_binop (b: binop) : int -> int -> int =
  match b with
  | Eadd -> fun x y -> x + y
  | Emul -> fun x y -> x * y
  | Emod -> fun x y -> x mod y
  | Exor -> fun x y -> x lxor y
  | Ediv -> fun x y -> x / y
  | Esub -> fun x y -> x - y
  | Eclt -> fun x y -> if x < y then 1 else 0
  | Ecle -> fun x y -> if x <= y then 1 else 0
  | Ecgt -> fun x y -> if x > y then 1 else 0
  | Ecge -> fun x y -> if x >= y then 1 else 0
  | Eceq -> fun x y -> if x = y then 1 else 0
  | Ecne -> fun x y -> if x <> y then 1 else 0

(* [eval_unop u x] évalue l'opération unaire [u] sur l'argument [x]. *)
let eval_unop (u: unop) : int -> int =
  match u with
  | Eneg -> fun x -> -x

(* [eval_eexpr st e] évalue l'expression [e] dans l'état [st]. Renvoie une
   erreur si besoin. *)
let rec eval_eexpr (oc: Format.formatter) (st: int state) (ep: eprog) (e : expr) : (int * int state) res =
  match e with
  | Eint n -> OK (n, st)
  | Echar c -> OK (Char.code c, st)
  | Evar id -> option_to_res_bind (Hashtbl.find_option st.env id) 
               (Printf.sprintf "In eval_eexpr : unable to find variable %s" id)
               (fun x -> OK (x,st))
  | Ebinop (op, e1, e2) -> eval_eexpr oc st ep e1 >>= fun (e1, st) ->
                           eval_eexpr oc st ep e2 >>= fun (e2, st) ->
                           OK (eval_binop op e1 e2, st)
  | Eunop (op, e) -> eval_eexpr oc st ep e >>= fun (e, st) ->
                     OK ((eval_unop op e), st)
  | Efuncall (funname, args) -> int_of_args oc st ep args >>= fun args' ->
                                find_function ep funname >>= fun func ->
                                eval_efun oc st ep func funname args' >>= fun (ret, state) ->
                                (match ret with
                                 | Some ret' -> OK (ret', state)
                                 | None -> let arg_str = List.fold_left (fun acc elem -> acc ^ " " ^ (string_of_int elem)) "" args' in
                                          Error (Format.sprintf "E: Called function %s(%s) but got no return value in expr" funname arg_str))

(* [eval_einstr oc st ins] évalue l'instrution [ins] en partant de l'état [st].

   Le paramètre [oc] est un "output channel", dans lequel la fonction "print"
   écrit sa sortie, au moyen de l'instruction [Format.fprintf].

   Cette fonction renvoie [(ret, st')] :

   - [ret] est de type [int option]. [Some v] doit être renvoyé lorsqu'une
   instruction [return] est évaluée. [None] signifie qu'aucun [return] n'a eu
   lieu et que l'exécution doit continuer.

   - [st'] est l'état mis à jour. *)
and eval_einstr (oc: Format.formatter) (st: int state) (ep: eprog) (ins: instr) :
  (int option * int state) res =
  match ins with
  | Iassign (var, var_expr) -> eval_eexpr oc st ep var_expr >>= fun (var_expr_res, st) ->
                               Hashtbl.replace st.env var var_expr_res;
                               OK(None, st)
  | Iif (cond, instr_then, instr_else) -> eval_eexpr oc st ep cond >>= fun (cond_res,st) ->
                                          if cond_res <> 0 then
                                            eval_einstr oc st ep instr_then
                                          else
                                            eval_einstr oc st ep instr_else
  | Iwhile (cond, instr_loop) -> eval_eexpr oc st ep cond >>= fun (cond_res,st) ->
                                 if cond_res <> 0 then
                                   eval_einstr oc st ep instr_loop >>= fun (res, st') ->
                                   (match res with
                                   | None -> eval_einstr oc st' ep ins
                                   | Some ret_val -> OK(res, st'))
                                 else
                                   OK(None, st)
  | Iblock (h::t) -> eval_einstr oc st ep h >>= fun (res, st') ->
                     (match res with
                     | None -> eval_einstr oc st' ep (Iblock t)
                     | Some ret_val -> OK(res, st'))
  | Iblock ([]) -> OK(None, st)
  | Ireturn (ret_expr) -> eval_eexpr oc st ep ret_expr >>= fun (expr_res,st) ->
                          OK(Some expr_res, st)
  | Ifuncall (fname, args) -> int_of_args oc st ep args >>= fun args' ->
                              (match find_function ep fname with
                              | OK func -> eval_efun oc st ep func fname args'
                              | Error e -> do_builtin oc st.mem fname args' >>= fun ret ->
                                          OK (ret, st))
  | Ideclaration varname -> OK (None, st)

and int_of_args (oc: Format.formatter) (st: int state) (ep: eprog) (args: expr list) : int list res =
  match args with
  | h::t -> eval_eexpr oc st ep h >>= fun (ret, st) ->
            int_of_args oc st ep t >>= fun args_int ->
            OK(ret::args_int)
  | [] -> OK ([])

(* [eval_efun oc st f fname vargs] évalue la fonction [f] (dont le nom est
   [fname]) en partant de l'état [st], avec les arguments [vargs].

   Cette fonction renvoie un couple (ret, st') avec la même signification que
   pour [eval_einstr]. *)
and eval_efun (oc: Format.formatter) (st: int state) (ep: eprog) ({funargs; funbody; funvartype; funrettype}: efun)
    (fname: string) (vargs: int list)
  : (int option * int state) res =
  (* L'environnement d'une fonction (mapping des variables locales vers leurs
     valeurs) est local et un appel de fonction ne devrait pas modifier les
     variables de l'appelant. Donc, on sauvegarde l'environnement de l'appelant
     dans [env_save], on appelle la fonction dans un environnement propre (Avec
     seulement ses arguments), puis on restore l'environnement de l'appelant. *)
  let env_save = Hashtbl.copy st.env in
  let env = Hashtbl.create 17 in
  match List.iter2 (fun a v -> Hashtbl.replace env a v) (List.map fst funargs) vargs with
  | () ->
    eval_einstr oc {st with env} ep funbody >>= fun (v, st') ->
    OK (v, { st' with env = env_save })
  | exception Invalid_argument _ ->
    Error (Format.sprintf
             "E: Called function %s with %d arguments, expected %d.\n"
             fname (List.length vargs) (List.length funargs)
          )

(* [eval_eprog oc ep memsize params] évalue un programme complet [ep], avec les
   arguments [params].

   Le paramètre [memsize] donne la taille de la mémoire dont ce programme va
   disposer. Ce n'est pas utile tout de suite (nos programmes n'utilisent pas de
   mémoire), mais ça le sera lorsqu'on ajoutera de l'allocation dynamique dans
   nos programmes.

   Renvoie:

   - [OK (Some v)] lorsque l'évaluation de la fonction a lieu sans problèmes et renvoie une valeur [v].

   - [OK None] lorsque l'évaluation de la fonction termine sans renvoyer de valeur.

   - [Error msg] lorsqu'une erreur survient.
   *)
let eval_eprog oc (ep: eprog) (memsize: int) (params: int list) : int option res =
  let st = init_state memsize in
  find_function ep "main" >>= fun f ->
  (* ne garde que le nombre nécessaire de paramètres pour la fonction "main". *)
  let n = List.length f.funargs in
  let params = take n params in
  eval_efun oc st ep f "main" params >>= fun (v, st) ->
  OK v
