open Prog
open Elang
open Elang_run
open Batteries
open BatList
open Cfg
open Utils
open Builtins

(* Evaluate a CFG expression [e] with current state [st] in CFG program [cp]
   If successful, returns the value corresponding to evaluation of this expr,
   as well as the new state (there can be side effects of expressions, for instance if we call functions) *)
let rec eval_cfgexpr oc st (cp: cprog) (e: expr) : (int * int state) res =
  match e with
  | Ebinop(b, e1, e2) ->
    eval_cfgexpr oc st cp e1 >>= fun (v1,st) ->
    eval_cfgexpr oc st cp e2 >>= fun (v2,st) ->
    let v = eval_binop b v1 v2 in
    OK (v, st)
  | Eunop(u, e) ->
    eval_cfgexpr oc st cp e >>= fun (v1,st) ->
    let v = (eval_unop u v1) in
    OK (v,st)
  | Eint i -> OK (i,st)
  | Evar s ->
    begin match Hashtbl.find_option st.env s with
      | Some v -> OK (v,st)
      | None -> Error (Printf.sprintf "Unknown variable %s\n" s)
    end
  | Ecall (fname, args) ->
    find_function cp fname >>= fun f ->
    int_of_args oc st cp args >>= fun args' ->
    eval_cfgfun oc st cp fname f args' >>= fun (ret, st) ->
    (match ret with
     | Some ret' -> OK (ret', st)
     | None -> let arg_str = List.fold_left (fun acc elem -> acc ^ " " ^ (string_of_int elem)) "" args' in
               Error (Format.sprintf "CFG: Called function %s(%s) but got no return value in expr" fname arg_str))

(* Evaluate CFG instruction of index [n], where [ht] is the hashtable corresponding to the
   current function body. If successful, returns a value (in case of a return instruction),
   as well as the new state *)
and eval_cfginstr oc st (cp: cprog) (ht: (int, cfg_node) Hashtbl.t) (n: int): (int option * int state) res =
  match Hashtbl.find_option ht n with
  | None -> Error (Printf.sprintf "Invalid node identifier\n")
  | Some node ->
    match node with
    | Cnop succ ->
      eval_cfginstr oc st cp ht succ
    | Cassign(v, e, s) ->
      eval_cfgexpr oc st cp e >>= fun (i,st) ->
      Hashtbl.replace st.env v i;
      eval_cfginstr oc st cp ht s
    | Ccmp(cond, i1, i2) ->
      eval_cfgexpr oc st cp cond >>= fun (i,st) ->
      if i = 0 then eval_cfginstr oc st cp ht i2 else eval_cfginstr oc st cp ht i1
    | Creturn(e) ->
      eval_cfgexpr oc st cp e >>= fun (e,st) ->
      OK (Some e, st)
    | Ccall (fname, args, s) ->
      int_of_args oc st cp args >>= fun args' ->
      (match find_function cp fname with
       | OK f -> eval_cfgfun oc st cp fname f args'
       | Error e -> do_builtin oc st.mem fname args' >>= fun ret ->
                    OK (ret, st)) >>= fun (_, st') ->
      eval_cfginstr oc st' cp ht s

(* In case of function calls, we need to evaluate all argument CFG expressions first.
   This function returns, on success, the list of values corresponding to the evaluation of arguments *)
and int_of_args (oc: Format.formatter) (st: int state) (cp: cprog) (args: expr list) : int list res =
  match args with
  | h::t -> eval_cfgexpr oc st cp h >>= fun (ret, st) ->
            int_of_args oc st cp t >>= fun args_int ->
            OK(ret::args_int)
  | [] -> OK ([])

(* Evaluate a full CFG function *)
and eval_cfgfun oc st cp cfgfunname { cfgfunargs;
                                      cfgfunbody;
                                      cfgentry} vargs : (int option * int state) res =
  (* Create a new state (local variables) for the function *)
  let st' = { st with env = Hashtbl.create 17 } in
  (* Put the argument values in state environment *)
  match List.iter2 (fun a v -> Hashtbl.replace st'.env a v) cfgfunargs vargs with
  | () -> eval_cfginstr oc st' cp cfgfunbody cfgentry >>= fun (v, st') ->
          OK (v, {st' with env = st.env})
  | exception Invalid_argument _ -> Error (Format.sprintf "CFG: Called function %s with %d arguments, expected %d.\n"
                                      cfgfunname (List.length vargs) (List.length cfgfunargs)
                                    )

(* Evaluate a full CFG program, which is just a list of global definitions *)
let eval_cfgprog oc (cp: cprog) memsize params =
  let st = init_state memsize in
  find_function cp "main" >>= fun f ->
  let n = List.length f.cfgfunargs in
  let params = take n params in
  eval_cfgfun oc st cp "main" f params >>= fun (v, st) ->
  OK v
