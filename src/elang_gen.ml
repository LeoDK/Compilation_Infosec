open Ast
open Elang
open Prog
open Report
open Options
open Batteries
open Elang_print
open Utils

let tag_is_binop =
  function
  | Tadd -> true
  | Tsub -> true
  | Tmul -> true
  | Tdiv -> true
  | Tmod -> true
  | Txor -> true
  | Tcle -> true
  | Tclt -> true
  | Tcge -> true
  | Tcgt -> true
  | Tceq -> true
  | Tcne  -> true
  | _    -> false

let tag_is_unop =
  function
  | Tneg -> true
  | _ -> false

let binop_of_tag =
  function
  | Tadd -> Eadd
  | Tsub -> Esub
  | Tmul -> Emul
  | Tdiv -> Ediv
  | Tmod -> Emod
  | Txor -> Exor
  | Tcle -> Ecle
  | Tclt -> Eclt
  | Tcge -> Ecge
  | Tcgt -> Ecgt
  | Tceq -> Eceq
  | Tcne -> Ecne
  | _ -> assert false

let unop_of_tag =
  function
  | Tneg -> Eneg
  | _ -> assert false


(* [type_expr typ_var typ_fun e] checks and returns the type of expression [e].
   [typ_var] represents all local variables types,
   [typ_fun] represents all known function signatures (argument types and return type) *)
let rec type_expr (typ_var : (string, typ) Hashtbl.t) (typ_fun : (string, typ list * typ) Hashtbl.t) (e : expr) : typ res =
  match e with
  | Ebinop (op, e1, e2) ->  type_expr typ_var typ_fun e1 >>= fun t1 ->
                            type_expr typ_var typ_fun e2 >>= fun t2 ->
                            if (t1 <> t2) then
                              Error "Both sides of binary expression are not of same type\n"
                            else
                              OK (t1)

  | Eunop (op, e) ->  type_expr typ_var typ_fun e >>= fun t ->
                      OK (t)

  | Eint i -> OK (Tint)

  | Echar c -> OK (Tchar)

  | Evar varname ->
    begin match Hashtbl.find_option typ_var varname with
    | Some t -> OK (t)
    | None -> Error (Printf.sprintf "Unkown type of variable %s in expression\n" varname)
    end

  | Efuncall (funname, arglist) ->
    funcall_check_signature funname arglist typ_var typ_fun

(* [funcall_check_signature funname arglist typ_var typ_fun] checks if [funname] function signature
   matches the types of the given arguments. On success, returns the return type of the function *)
and funcall_check_signature fname (arglist : expr list) typ_var typ_fun : typ res =
  let equal (l1 : 'a list) (l2 : 'a list) =
    let ret, leftover = List.fold_left (fun (ret,acc) elem -> match acc with
                                                              | h::t -> ((ret) && (h=elem), t)
                                                              | [] -> (false, [])) (true, l1) l2
    in (leftover = []) && ret
  in
  (* Get the types of the arguments *)
  let arglisttypes = List.map (type_expr typ_var typ_fun) arglist in
  List.fold_left (fun acc elem -> elem >>= fun t -> acc >>= fun a -> OK (a@[t])) (OK []) arglisttypes >>= fun arglisttypes ->
  match Hashtbl.find_option typ_fun fname with
    (* Compare function signature with given arguments *)
  | Some (argstype, rettype) -> if equal argstype arglisttypes then
                                  OK (rettype)
                                else
                                  Error (Printf.sprintf "Given %s function arguments do not match function signature\n" fname)
  | None -> Error (Printf.sprintf "No function called %s\n" fname)


(* [make_eexpr_of_ast a] builds an expression corresponding to a tree [a].
   If the tree is not well-formed, or if the types do not match, fails with an [Error] message. *)
let rec make_eexpr_of_ast (a: tree) typ_var typ_fun : expr res =
  let res =
    match a with
    | Node (t, [e1; e2]) when tag_is_binop t -> make_eexpr_of_ast e1 typ_var typ_fun >>= fun expr1 ->
                                                make_eexpr_of_ast e2 typ_var typ_fun >>= fun expr2 ->
                                                type_expr typ_var typ_fun expr1 >>= fun _ ->
                                                type_expr typ_var typ_fun expr2 >>= fun _ ->
                                                OK (Ebinop ((binop_of_tag t), expr1, expr2))

    | Node (t, [e]) when tag_is_unop t -> make_eexpr_of_ast e typ_var typ_fun >>= fun expr ->
                                          type_expr typ_var typ_fun expr >>= fun _ ->
                                          OK (Eunop ((unop_of_tag t), expr))

    | Node (Tidentifier, [StringLeaf varname]) -> type_expr typ_var typ_fun (Evar varname) >>= fun _ ->
                                                  OK (Evar varname)

    | Node (Tint, [IntLeaf value]) -> OK (Eint value)

    | Node (Tfuncall, [ Node (Tfunname, [ Node (Tidentifier, [StringLeaf funname]) ]);
                        Node (Tfunargs, args) ]) -> exprs_of_args args typ_var typ_fun >>= fun args_exprs ->
                                                    funcall_check_signature funname args_exprs typ_var typ_fun >>= fun _ ->
                                                    OK (Efuncall (funname, args_exprs))

    | _ -> Error (Printf.sprintf "Unacceptable ast in make_eexpr_of_ast %s" (string_of_ast a))

  in
  match res with
  | OK _ -> res
  | Error msg -> Error (Format.sprintf "In make_eexpr_of_ast %s:\n%s" (string_of_ast a) msg)

(* Make a list of E expressions corresponding to the list of given parameters, represented by trees *)
and exprs_of_args (args : tree list) typ_var typ_fun : expr list res =
  match args with
  | h::t -> make_eexpr_of_ast h typ_var typ_fun >>= fun h' ->
            exprs_of_args t typ_var typ_fun >>= fun t' ->
            OK(h'::t')
  | [] -> OK ([])

(* Check if a variable is already declared *)
let is_declared typ_var varname =
  match Hashtbl.find_option typ_var varname with
  | Some t -> true
  | None -> false

(* Check that [varname] is of type [t] *)
let check_type typ_var typ_fun varname t : bool =
  match Hashtbl.find_option typ_var varname with
  | Some t' -> t=t'
  | None -> false

(* Make instruction from ast [a] *)
let rec make_einstr_of_ast (a: tree) typ_var typ_fun : instr res =
  let res =
    match a with

    | Node (Tdeclaration, [Node(Ttype, [StringLeaf t]); Node (Tidentifier, [StringLeaf varname])]) ->
        type_of_string t >>= fun t ->
        (* We should not be able to declare a void variable *)
        if t = Tvoid then
          Error (Printf.sprintf "Cannot declare variable %s of type void\n" varname)
        else
          (* We should not redeclare a variable *)
          if is_declared typ_var varname then
            Error (Printf.sprintf "Redifinition of variable %s\n" varname)
          else
            (Hashtbl.replace typ_var varname t;
            OK (Ideclaration varname))

    | Node (Tassign, [Node(Tidentifier,[StringLeaf varname]); e_ast]) ->
        make_eexpr_of_ast e_ast typ_var typ_fun >>= fun e ->
        type_expr typ_var typ_fun e >>= fun t ->
        (* Check that both sides are of same type *)
        if check_type typ_var typ_fun varname t then
          OK (Iassign(varname, e))
        else
          Error (Printf.sprintf "Error in expression : %s is not of same type as rvalue\n" varname)

    | Node (Tassign, [Node (Tdeclaration, [Node (Ttype, [StringLeaf t]); Node (Tidentifier, [StringLeaf varname])]); e]) ->
        (* Decompose in 2 steps : first a declaration, and then the assignement. For instance, int x = 0 becomes
           int x; x=0; *)
        make_einstr_of_ast (Node (Tdeclaration, [Node (Ttype, [StringLeaf t]); Node (Tidentifier, [StringLeaf varname])])) typ_var typ_fun >>= fun i1 ->
        make_einstr_of_ast (Node (Tassign, [Node(Tidentifier, [StringLeaf varname]); e])) typ_var typ_fun >>= fun i2 ->
        OK (Iblock [i1;i2])

    | Node (Tif, [e;i1;i2]) ->
        make_eexpr_of_ast e typ_var typ_fun >>= fun expr ->
        make_einstr_of_ast i1 typ_var typ_fun >>= fun instr1 ->
        make_einstr_of_ast i2 typ_var typ_fun >>= fun instr2 ->
        OK (Iif (expr, instr1, instr2))

    | Node (Twhile, [e;i]) ->
        make_eexpr_of_ast e typ_var typ_fun >>= fun expr ->
        make_einstr_of_ast i typ_var typ_fun >>= fun instr ->
        OK (Iwhile (expr, instr))

    | Node (Tblock, i_list) ->
        list_map_res (fun a' -> make_einstr_of_ast a' typ_var typ_fun) i_list >>= fun instr_list ->
        OK (Iblock instr_list)

    | Node (Treturn, [e]) ->
        make_eexpr_of_ast e typ_var typ_fun >>= fun expr ->
        OK (Ireturn expr)

    | Node (Tfuncall, [ Node (Tfunname, [ Node (Tidentifier, [StringLeaf funname]) ]);
                        Node (Tfunargs, args) ]) -> exprs_of_args args typ_var typ_fun >>= fun args_expr ->
                                                    funcall_check_signature funname args_expr typ_var typ_fun >>= fun _ ->
                                                    OK (Ifuncall (funname, args_expr))

    | NullLeaf ->
        OK (Iblock [])

    | _ -> Error (Printf.sprintf "Unacceptable ast in make_einstr_of_ast %s"
                    (string_of_ast a))
  in
  match res with
    OK o -> res
  | Error msg -> Error (Format.sprintf "In make_einstr_of_ast %s:\n%s"
                          (string_of_ast a) msg)

(* Get type of arguments, given as a list of AST *)
let rec get_args_types (args_nodes : tree list) : (string * typ) list res =
  match args_nodes with
  | (Node (Tdeclaration, [Node(Ttype, [StringLeaf t]); Node (Tidentifier, [StringLeaf varname])]))::tail ->
    type_of_string t >>= fun t' ->
    get_args_types tail >>= fun tail' ->
    OK ((varname, t')::tail')
  | [] -> OK []
  | _ -> Error "Unacceptable ast in make_args_of_ast_list\n"

(* Make the CFG function that corresponds too the AST [a] *)
let make_fundef_of_ast (a: tree) typ_fun : (string * efun) res =
  match a with
  | Node (Tfundef, [Node (Ttype, [StringLeaf frettype]);
                    Node(Tfunname, [StringLeaf fname]);
                    Node (Tfunargs, fargs);
                    Node (Tfunbody, [fbody])]) ->
    type_of_string frettype >>= fun funrettype ->
    (* Get the types of the arguments *)
    get_args_types fargs >>= fun funargs ->
    let typ_var = Hashtbl.create (List.length fargs) in
    (* Putting arguments in local variables *)
    List.iter (fun (varname, t) -> Hashtbl.replace typ_var varname t) funargs;
    make_einstr_of_ast fbody typ_var typ_fun >>= fun fbody ->
    (* Adding current function to known function signatures *)
    Hashtbl.add typ_fun fname ((List.map snd funargs), funrettype);
    OK(fname, {funargs = funargs; funbody = fbody; funvartype = typ_var; funrettype = funrettype})
  | _ ->
    Error (Printf.sprintf "make_fundef_of_ast: Expected a Tfundef, got %s."
             (string_of_ast a))

let make_eprog_of_ast (a: tree) : eprog res =
  match a with
  | Node (Tlistglobdef, l) ->
    let rec make_fundef_of_ast_list (a_subnodes : tree list) typ_fun : eprog res =
      begin match a_subnodes with
      | h::t->  make_fundef_of_ast h typ_fun >>= fun (fname, f) ->
                Hashtbl.add typ_fun fname (List.map snd f.funargs, f.funrettype);
                make_fundef_of_ast_list t typ_fun >>= fun t' ->
                OK ((fname, Gfun f)::t')
      | [] -> OK []
      end
    in
    let typ_fun = Hashtbl.create (List.length l) in
    Hashtbl.replace typ_fun "print" ([Tint], Tvoid);
    Hashtbl.replace typ_fun "print_int" ([Tint], Tvoid);
    Hashtbl.replace typ_fun "print_char" ([Tchar], Tvoid);
    make_fundef_of_ast_list l typ_fun
  | _ ->
    Error (Printf.sprintf "make_fundef_of_ast: Expected a Tlistglobdef, got %s."
             (string_of_ast a))

let pass_elang ast  =
  match make_eprog_of_ast ast with
  | Error msg ->
    record_compile_result ~error:(Some msg) "Elang";
    Error msg
  | OK  ep ->
    dump !e_dump dump_e ep (fun file () ->
        add_to_report "e" "E" (Code (file_contents file))); OK ep

