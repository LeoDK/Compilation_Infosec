open Elang
open Elang_gen
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
   erreur si besoin. [sp] est le stack pointer courant *)
let rec eval_eexpr  (oc: Format.formatter) (st: int state) (sp : int) (ep: eprog) (ef: efun)
                    (typ_fun: (string, typ list * typ) Hashtbl.t) (e : expr)  : (int * int state) res =
  match e with
  | Eint n -> OK (n, st)

  | Echar c -> OK (Char.code c, st)

  | Evar v -> begin match Hashtbl.find_option ef.funvarinmem v with
              (* Variable in memory *)
              | Some offset ->  begin match Hashtbl.find_option ef.funvartype v with
                                      | Some t -> size_type t >>= fun size ->
                                                  Mem.read_bytes_as_int st.mem (sp + offset) size >>= fun value ->
                                                  OK (value, st)
                                      | None -> Error (Printf.sprintf "In eval_eexpr : unable to find type of variable %s\n" v)
                                end
              (* Variable in env (a priori in a register, if possible) *)
              | None -> begin match Hashtbl.find_option st.env v with
                        | Some v' -> OK (v', st)
                        | None -> Error (Printf.sprintf "In eval_eexpr : unable to find variable %s in env\n" v)
                        end
              end

  | Ebinop (op, e1, e2) ->  eval_eexpr oc st sp ep ef typ_fun e1 >>= fun (e1', st) ->
                            eval_eexpr oc st sp ep ef typ_fun e2 >>= fun (e2', st) ->
                            type_expr ef.funvartype typ_fun e1 >>= fun t1 ->
                            type_expr ef.funvartype typ_fun e2 >>= fun t2 ->
                            begin match (t1,t2) with
                            (* *(p+i) = val stores [val] at address [p + i * sizeof( *p )] *)
                            | (Tptr t1', _) ->  size_type t1' >>= fun t1'' ->
                                                OK (eval_binop op e1' (e2' * t1''), st)
                            | (_, Tptr t2') ->  size_type t2' >>= fun t2'' ->
                                                OK (eval_binop op (e1' * t2'') e2', st)
                            | (_,_) -> OK (eval_binop op e1' e2', st)
                            end

  | Eunop (op, e) -> eval_eexpr oc st sp ep ef typ_fun e >>= fun (e, st) ->
                     OK ((eval_unop op e), st)

  | Efuncall (fname, args) -> int_of_args oc st sp ep ef typ_fun args >>= fun (args', st) ->
                              find_function ep fname >>= fun ef' ->
                              eval_efun oc st sp ep ef' typ_fun fname args' >>= fun (ret, st) ->
                              begin match ret with
                              | Some ret' -> OK (ret', st)
                              | None -> let arg_str = List.fold_left (fun acc elem -> acc ^ " " ^ (string_of_int elem)) "" args' in
                                        Error (Format.sprintf "E: Called function %s(%s) but got no return value in expr" fname arg_str)
                              end

  | Eaddrof v ->  begin match Hashtbl.find_option ef.funvarinmem v with
                  | Some addr -> OK (addr, st)
                  | None -> Error (Printf.sprintf "Variable %s is not located in memory\n" v)
                  end

  | Eload addr ->   type_expr ef.funvartype typ_fun e >>= fun t ->
                    begin match t with
                    | Tptr t' ->  size_type t' >>= fun size ->
                                  eval_eexpr oc st sp ep ef typ_fun addr >>= fun (addr', st) ->
                                  Mem.read_bytes_as_int st.mem addr' size >>= fun value ->
                                  OK (value, st)
                    | t' -> Error (Printf.sprintf "Cannot load value at address given by expression of type %s in eval_eexpr\n" (string_of_type t'))
                    end

(* [eval_einstr oc st ins] évalue l'instrution [ins] en partant de l'état [st].

   Le paramètre [oc] est un "output channel", dans lequel la fonction "print"
   écrit sa sortie, au moyen de l'instruction [Format.fprintf].

   Cette fonction renvoie [(ret, st')] :

   - [ret] est de type [int option]. [Some v] doit être renvoyé lorsqu'une
   instruction [return] est évaluée. [None] signifie qu'aucun [return] n'a eu
   lieu et que l'exécution doit continuer.

   - [st'] est l'état mis à jour. *)
and eval_einstr (oc: Format.formatter) (st: int state) (sp: int) (ep: eprog) (ef: efun)
                (typ_fun: (string, typ list * typ) Hashtbl.t) (ins: instr)  : (int option * int state) res =
  match ins with
  | Iassign (v, e) -> eval_eexpr oc st sp ep ef typ_fun e >>= fun (e', st) ->
                      begin match Hashtbl.find_option ef.funvarinmem v with
                      | Some offset ->  type_expr ef.funvartype typ_fun e >>= fun t ->
                                        size_type t >>= fun size ->
                                        Mem.write_bytes st.mem (sp + offset) (split_bytes size e') >>= fun _ ->
                                        OK (None, st)
                      | None -> Hashtbl.replace st.env v e';
                                OK(None, st)
                      end

  | Iif (e, i1, i2) ->  eval_eexpr oc st sp ep ef typ_fun e >>= fun (e', st) ->
                        if e' <> 0 then
                          eval_einstr oc st sp ep ef typ_fun i1
                        else
                          eval_einstr oc st sp ep ef typ_fun i2

  | Iwhile (e, i) ->  eval_eexpr oc st sp ep ef typ_fun e >>= fun (e', st) ->
                      if e' <> 0 then
                        eval_einstr oc st sp ep ef typ_fun i >>= fun (res, st) ->
                        begin match res with
                        | None -> eval_einstr oc st sp ep ef typ_fun ins
                        | Some ret -> OK (res, st)
                        end
                      else
                        OK(None, st)

  | Iblock (h::t) -> eval_einstr oc st sp ep ef typ_fun h >>= fun (h', st) ->
                     begin match h' with
                     | None -> eval_einstr oc st sp ep ef typ_fun (Iblock t)
                     | Some ret_val -> OK(h', st)
                     end

  | Iblock ([]) -> OK(None, st)

  | Ireturn e ->  eval_eexpr oc st sp ep ef typ_fun e >>= fun (e', st) ->
                  OK (Some e', st)

  | Ifuncall (fname, args) -> int_of_args oc st sp ep ef typ_fun args >>= fun (args', st) ->
                              begin match find_function ep fname with
                              | OK ef' -> eval_efun oc st sp ep ef' typ_fun fname args' >>= fun (res, st) ->
                                          OK (None, st)
                              | Error err -> do_builtin oc st.mem fname args' >>= fun ret ->
                                              OK (None, st)
                              end

  | Ideclaration varname -> OK (None, st)

  | Istore (addr, value) -> type_expr ef.funvartype typ_fun value >>= fun tval ->
                            (* Here we assume types are OK (done in elang_gen *)
                            size_type tval >>= fun size ->
                            eval_eexpr oc st sp ep ef typ_fun addr >>= fun (addr', st) ->
                            eval_eexpr oc st sp ep ef typ_fun value >>= fun (value', st) ->
                            Mem.write_bytes st.mem (sp+addr') (split_bytes size value') >>= fun _ ->
                            Printf.printf "DEBUG : In store %d at address %d\n" value' addr';
                            Mem.read_bytes_as_int st.mem (sp+addr') size >>= fun res ->
                            Printf.printf "%d\n" res;
                            OK (None, st)

and int_of_args oc st sp ep ef typ_fun (args: expr list) : (int list * int state) res =
  match args with
  | h::t -> eval_eexpr oc st sp ep ef typ_fun h >>= fun (h', st) ->
            int_of_args oc st sp ep ef typ_fun t >>= fun (t', st) ->
            OK(h'::t', st)
  | [] -> OK ([], st)

(* [eval_efun oc st f fname vargs] évalue la fonction [f] (dont le nom est
   [fname]) en partant de l'état [st], avec les arguments [vargs].

   Cette fonction renvoie un couple (ret, st') avec la même signification que
   pour [eval_einstr]. *)
and eval_efun (oc: Format.formatter) (st: int state) (sp: int) (ep: eprog) (ef: efun)
              (typ_fun: (string, typ list * typ) Hashtbl.t) (fname: string) (vargs: int list)
              : (int option * int state) res =
  (* L'environnement d'une fonction (mapping des variables locales vers leurs
     valeurs) est local et un appel de fonction ne devrait pas modifier les
     variables de l'appelant. Donc, on sauvegarde l'environnement de l'appelant
     dans [env_save], on appelle la fonction dans un environnement propre (Avec
     seulement ses arguments), puis on restaure l'environnement de l'appelant. *)
  let env_save = Hashtbl.copy st.env in
  let env = Hashtbl.create 17 in
  match List.iter2 (fun a v -> Hashtbl.replace env a v) (List.map fst ef.funargs) vargs with
  | () ->
    eval_einstr oc {st with env} (sp - ef.funstksz) ep ef typ_fun ef.funbody >>= fun (v, st') ->
    OK (v, { st' with env = env_save })
  | exception Invalid_argument _ ->
    Error (Format.sprintf
             "E: Called function %s with %d arguments, expected %d.\n"
             fname (List.length vargs) (List.length ef.funargs)
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
  find_function ep "main" >>= fun ef ->
  (* ne garde que le nombre nécessaire de paramètres pour la fonction "main". *)
  let n = List.length ef.funargs in
  let params = take n params in
  let typ_fun = Hashtbl.create (List.length ep) in
  List.iter (fun (fname, Gfun ef) -> Hashtbl.replace typ_fun fname (List.map snd ef.funargs, ef.funrettype)) ep;
  eval_efun oc st memsize ep ef typ_fun "main" params >>= fun (v, st) ->
  OK v
