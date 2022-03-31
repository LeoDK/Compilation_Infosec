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

let is_type_compat (t1: typ) (t2: typ) =
  match t1 with
  | Tint -> begin match t2 with
            | Tint
            | Tchar -> true
            | _ -> false
            end
  | Tchar ->  begin match t2 with
              | Tint
              | Tchar -> true
              | _ -> false
              end
  | Tvoid ->  begin match t2 with
              | Tvoid -> true
              | _ -> false
              end
  | Tptr t1' -> begin match t2 with
                | Tptr t2' -> (t1'=t2')
                | _ -> false
                end


(* [type_expr typ_var typ_fun e] checks and returns the type of expression [e].
   [typ_var] represents all local variables types,
   [typ_fun] represents all known function signatures (argument types and return type) *)
let rec type_expr (typ_var : (string, typ) Hashtbl.t) (typ_fun : (string, typ list * typ) Hashtbl.t) (e : expr) : typ res =
  match e with
  | Ebinop (op, e1, e2) ->  type_expr typ_var typ_fun e1 >>= fun t1 ->
                            type_expr typ_var typ_fun e2 >>= fun t2 ->
                            begin match t1 with
                            | Tptr tp ->  if (t2 = Tint || t2 = Tchar) && ((op = Eadd) || (op=Esub)) then
                                            OK (Tptr tp)
                                          else if (t2 = Tptr tp) && ((op=Ecle) || (op=Eclt) || (op=Ecge)
                                                                  || (op=Ecgt) || (op=Eceq) || (op=Ecne)) then
                                            OK (Tptr tp)
                                          else Error (Printf.sprintf "Binary operation between pointer and %s not allowed\n" (string_of_type t2))
                            | _ ->
                              begin match t2 with
                              | Tptr tp ->  if (t1 = Tint || t2 = Tchar) && (op=Eadd) then
                                              OK (Tptr tp)
                                            else Error (Printf.sprintf "Binary operation between pointer and %s not allowed\n" (string_of_type t2))
                              | _ ->  if (t1 = Tint && t2 = Tchar) || (t1 = Tchar && t2 = Tint) then
                                        OK (Tint)
                                      else if (t1 <> t2) then
                                        Error "Both sides of binary expression are not of same type\n"
                                      else
                                        OK (t1)
                              end
                            end

  | Eunop (op, e) ->  type_expr typ_var typ_fun e >>= fun t ->
                      OK (t)

  | Eint i -> OK (Tint)

  | Echar c -> OK (Tchar)

  | Evar varname ->
    begin match Hashtbl.find_option typ_var varname with
    | Some t -> OK (t)
    | None -> Error (Printf.sprintf "Unkown type of variable %s in expression\n" varname)
    end

  | Efuncall (fname, arglist) ->
    funcall_check_signature fname arglist typ_var typ_fun

  | Eaddrof v ->
    type_expr typ_var typ_fun (Evar v) >>= fun t ->
    OK (Tptr t)

  | Eload e' ->
    type_expr typ_var typ_fun e' >>= fun t ->
    begin match t with
      | Tptr t' -> OK (t')
      | _ -> Error "Type error : dereferencing non pointer expression\n"
    end

(* [funcall_check_signature fname arglist typ_var typ_fun] checks if [nname] function signature
   matches the types of the given arguments. On success, returns the return type of the function *)
and funcall_check_signature fname (arglist : expr list) typ_var typ_fun : typ res =
  let equal (l1 : 'a list) (l2 : 'a list) =
    let ret, leftover = List.fold_left (fun (ret,acc) elem -> match acc with
                                                              | h::t -> ((ret) && (is_type_compat h elem), t)
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


(* Returns the set of variables which addresses are taken (with & operator) *)
let addr_taken_expr (e: expr) : string Set.t =
  let rec aux (e: expr) (acc: string Set.t) =
    match e with
    | Ebinop (op, e1, e2) -> aux e2 (aux e1 acc)
    | Eunop (op, e) -> aux e acc
    | Efuncall (fname, arglist) -> List.fold_left (fun acc' elem -> aux elem acc') acc arglist
    | Eaddrof v -> Set.add v acc
    | Eload e -> aux e acc
    | _ -> acc
  in
  aux e Set.empty


(* [make_eexpr_of_ast a] builds an expression corresponding to a tree [a].
   If the tree is not well-formed, or if the types do not match, fails with an [Error] message. *)
let rec make_eexpr_of_ast (a: tree) typ_var typ_fun : expr res =
  let res =
    match a with
    | Node (t, [e1; e2]) when tag_is_binop t -> make_eexpr_of_ast e1 typ_var typ_fun >>= fun expr1 ->
                                                make_eexpr_of_ast e2 typ_var typ_fun >>= fun expr2 ->
                                                type_expr typ_var typ_fun expr1 >>= fun t1 ->
                                                type_expr typ_var typ_fun expr2 >>= fun t2 ->
                                                if t1 <> t2 then
                                                  begin match t1 with
                                                  | Tptr t1' -> if (t2 = Tint || t2 = Tchar) && (t = Tadd || t = Tsub) then
                                                                  OK (Ebinop ((binop_of_tag t), expr1, expr2))
                                                                else
                                                                  Error "Left and right hand sides are not type compatible\n"
                                                  | Tchar
                                                  | Tint -> begin match t2 with
                                                            | Tptr t2' -> if t = Tadd then
                                                                            OK (Ebinop ((binop_of_tag t), expr1, expr2))
                                                                          else
                                                                            Error "Left and right hand sides are not type compatible\n"
                                                            | Tchar -> OK (Ebinop ((binop_of_tag t), expr1, expr2))
                                                            | Tint -> OK (Ebinop ((binop_of_tag t), expr1, expr2))
                                                            | _ -> Error "Left and right hand sides are not type compatible\n"
                                                            end
                                                  | _ -> Error "Left and right hand sides are not type compatible\n"
                                                  end
                                                else
                                                  OK (Ebinop ((binop_of_tag t), expr1, expr2))

    | Node (t, [e]) when tag_is_unop t -> make_eexpr_of_ast e typ_var typ_fun >>= fun expr ->
                                          type_expr typ_var typ_fun expr >>= fun _ ->
                                          OK (Eunop ((unop_of_tag t), expr))

    | Node (Tidentifier, [StringLeaf varname]) -> type_expr typ_var typ_fun (Evar varname) >>= fun _ ->
                                                  OK (Evar varname)

    | Node (Tint, [IntLeaf value]) -> OK (Eint value)

    | Node (Tchar, [CharLeaf value]) -> OK (Echar value)

    | Node (Tfuncall, [ Node (Tfunname, [ Node (Tidentifier, [StringLeaf funname]) ]);
                        Node (Tfunargs, args) ]) -> exprs_of_args args typ_var typ_fun >>= fun args_exprs ->
                                                    funcall_check_signature funname args_exprs typ_var typ_fun >>= fun _ ->
                                                    OK (Efuncall (funname, args_exprs))


    | Node (Taddress, [Node (Tderef, [subnode])]) -> make_eexpr_of_ast subnode typ_var typ_fun

    | Node (Taddress, [subnode]) -> make_eexpr_of_ast subnode typ_var typ_fun >>= fun e ->
                                    begin match e with
                                    | Evar v -> OK (Eaddrof v)
                                    | _ -> Error "Cannot take address of something else than a variable\n"
                                    end

    | Node (Tderef, [subnode]) -> make_eexpr_of_ast subnode typ_var typ_fun >>= fun e ->
                                  OK (Eload e)

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

    | Node (Tassign, [lvalue; rvalue]) ->
        (* Get E expression and type for right hand value *)
        make_eexpr_of_ast rvalue typ_var typ_fun >>= fun re ->
        type_expr typ_var typ_fun re >>= fun re_t ->

        begin match lvalue with

        (* e.g. *a = b; *)
        | Node (Tderef, [subnode]) ->
            (* get expression and type for a *)
            make_eexpr_of_ast subnode typ_var typ_fun >>= fun le ->
            type_expr typ_var typ_fun le >>= fun le_t ->
            (* check types (is of type pointer to type on b?) *)
            if is_type_compat (Tptr re_t) le_t then
              OK (Istore (le, re))
            else
              Error (Printf.sprintf "Trying to store value of type %s inside memory space of type %s\n"
              (string_of_type re_t) (string_of_type le_t))

        (* e.g. a = b; *)
        | Node (Tidentifier, [StringLeaf v]) ->
            (* get type for a *)
            begin match Hashtbl.find_option typ_var v with
                            (* check types (are a and b of same type?) *)
            | Some le_t ->  if is_type_compat re_t le_t then
                              OK (Iassign (v, re))
                            else
                              Error (Printf.sprintf "Trying to store value of type %s inside memory space of type %s\n"
                              (string_of_type re_t) (string_of_type le_t))
            | None -> Error (Printf.sprintf "Unkown variable %s\n" v)
            end

        (* e.g. int **a = b; *)
        | Node (Tdeclaration, [subnode; Node (Tidentifier, [StringLeaf v])]) ->
            (* Decompose in two parts : declaration and assignment *)
            make_einstr_of_ast lvalue typ_var typ_fun >>= fun decl_instr ->
            make_einstr_of_ast (Node (Tassign, [Node (Tidentifier, [StringLeaf v]); rvalue])) typ_var typ_fun >>= fun assign_instr ->
            OK (Iblock ([decl_instr; assign_instr]))

        | _ -> Error (Printf.sprintf "In make_einstr_of_ast : unacceptable ast %s\n" (string_of_ast lvalue))
        end

    | Node (Tdeclaration, [subnode; Node (Tidentifier, [StringLeaf varname])]) ->
      let rec aux (n: tree) : ((instr * typ) res) =
        begin match n with
        | Node (Ttype, [StringLeaf t]) -> 
            type_of_string t >>= fun t ->
            (* We should not be able to declare a void variable *)
            if t = Tvoid then
              Error (Printf.sprintf "Cannot declare variable %s of type void\n" varname)
            else
              (* We should not redeclare a variable *)
              if is_declared typ_var varname then
                Error (Printf.sprintf "Redifinition of variable %s\n" varname)
              else
                OK (Ideclaration varname, t)
        | Node (Tderef, [n']) ->
            aux n' >>= fun (instr, t) ->
            OK (instr, Tptr t)
        | _ -> Error (Printf.sprintf "Unacceptable ast in make_einstr_of_ast in aux : %s\n" (string_of_ast n))
        end
      in
      aux subnode >>= fun (instr, t) ->
      Hashtbl.replace typ_var varname t;
      OK (instr)

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

(* Returns the set of variables which addresses are taken in instruction [i] (with & operator) *)
let addr_taken_instr (i: instr) : string Set.t =
  let rec aux (i: instr) (acc: string Set.t) =
    match i with
    | Iassign (v, e) -> Set.union acc (addr_taken_expr e)
    | Iif (e, i1, i2) -> let acc = aux i1 acc in
                         let acc = aux i2 acc in
                         Set.union acc (addr_taken_expr e)
    | Iwhile (e, i) -> Set.union (aux i acc) (addr_taken_expr e)
    | Iblock l -> List.fold_left (fun acc' elem -> aux elem acc') acc l
    | Ireturn e -> Set.union acc (addr_taken_expr e)
    | Ifuncall (fname, args) -> List.fold_left (fun acc' elem -> Set.union (addr_taken_expr elem) acc') acc args
    | Ideclaration v -> acc
    | Istore (addr, value) -> Set.union acc (Set.union (addr_taken_expr addr) (addr_taken_expr value))
  in
  aux i Set.empty

(* Get type of arguments, given as a list of AST *)
let rec get_args_types (args_nodes : tree list) : (string * typ) list res =
  let rec pointerize (n: tree) =
    match n with
    | Node (Ttype, [StringLeaf t]) -> type_of_string t >>= fun t' ->
                                      OK (t')
    | Node (Tderef, [subnode]) -> pointerize subnode >>= fun t ->
                                    OK (Tptr t)
    | _ -> Error (Printf.sprintf "Unacceptable ast in make_args_of_ast_list in pointerize : %s\n" (string_of_ast n))
  in
  match args_nodes with
  | (Node (Tdeclaration, [node; Node (Tidentifier, [StringLeaf varname])]))::tail ->
    pointerize node >>= fun t ->
    get_args_types tail >>= fun tail_t ->
    OK ((varname, t)::tail_t)
  | [] -> OK []
  | head::tail -> Error (Printf.sprintf "Unacceptable ast in make_args_of_ast_list : %s\n" (string_of_ast head))

(* This function orders conveniently stack variables so that padding is ensured.
   Returns the tuple (funvarinmem, funstksz),
   where [funvarinmem] is a hashtable giving the offset in the stack of a given variable
   and [funstksz] is the size of the stack to be allocated (must be a multiple of the architecture word) *)
let tweak_padding (stack_vars: string Set.t) typ_var : ((string, int) Hashtbl.t * int) res =
  let h = Hashtbl.create (Set.cardinal stack_vars) in
  (* Sort from biggest to lowest (decreasing order) *)
  let stack_vars_unsorted = Set.to_list stack_vars in
  let stack_vars_size = List.map (fun elem ->  let t = Hashtbl.find typ_var elem in
                                                  size_type t >>= fun t' -> OK (t')) stack_vars_unsorted in
  let stack_vars_size = List.fold_left (fun acc elem -> match acc with
                                                        | Error e -> acc
                                                        | OK l -> begin match elem with
                                                                  | Error e -> acc
                                                                  | OK elem' -> OK (l@[elem'])
                                                                  end) (OK []) stack_vars_size in
  stack_vars_size >>= fun stack_vars_size ->
  (* this is the list of (size, varname) *)
  let stack_vars_unsorted = List.mapi (fun index elem -> (List.nth stack_vars_size index, elem)) stack_vars_unsorted in
  let stack_vars_sorted = List.sort (fun (s1, v1) (s2, v2) -> s2 - s1) stack_vars_unsorted in
  let stack_vars_sorted = List.map snd stack_vars_sorted in
  (* Add elements to the stack *)
  let fold_f (acc : int res ) (elem : string) =
    acc >>= fun acc' ->
    let t = Hashtbl.find typ_var elem in
    size_type t >>= fun t' ->
    Hashtbl.replace h elem acc';
    OK (acc' + t')
  in
  List.fold_left fold_f (OK 0) stack_vars_sorted >>= fun stack_size ->
  let locations = (stack_size + Archi.wordsize() - 1) / (Archi.wordsize ()) in
  OK (h, locations * (Archi.wordsize()))

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
    (* Adding current function to known function signatures *)
    Hashtbl.replace typ_fun fname ((List.map snd funargs), funrettype);
    (* Putting arguments in local variables *)
    List.iter (fun (varname, t) -> Hashtbl.replace typ_var varname t) funargs;
    make_einstr_of_ast fbody typ_var typ_fun >>= fun fbody ->
    (* Computing function stack *)
    let stack_vars = addr_taken_instr fbody in
    tweak_padding stack_vars typ_var >>= fun (funvarinmem, funstksz) ->
    OK(fname, {funargs = funargs; funbody = fbody; funvartype = typ_var; funrettype = funrettype;
               funvarinmem=funvarinmem; funstksz = funstksz})
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

