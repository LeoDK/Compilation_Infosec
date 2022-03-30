open Batteries
open BatList
open Elang
open Cfg
open Elang_run
open Cfg_run
open Rtl
open Rtl_print
open Utils
open Builtins
open Prog

type state = {
  mem: Mem.t;
  regs: (reg, int) Hashtbl.t;
}

let init_state memsize =
  {
    mem = Mem.init memsize;
    regs = Hashtbl.create 17
  }

let eval_rtl_cmp = function
    Rcle -> (<=)
  | Rclt -> (<)
  | Rcge -> (>=)
  | Rcgt -> (>)
  | Rceq -> (=)
  | Rcne -> (<>)

let rec exec_rtl_instr oc (st: state) (sp: int) (rp: rtl_fun prog) rtlfunname (rf: rtl_fun) (i: rtl_instr) : (int option * state) res =
  match i with
  | Rbinop (b, rd, rs1, rs2) ->
    begin match Hashtbl.find_option st.regs rs1,
                Hashtbl.find_option st.regs rs2 with
    | Some v1, Some v2 ->
      Hashtbl.replace st.regs rd (eval_binop b v1 v2);
      OK (None, st)
    | _, _ -> Error (Printf.sprintf "Binop applied on undefined registers (%s and %s)" (print_reg rs1) (print_reg rs2))
    end

  | Runop (u, rd, rs) ->
    begin match Hashtbl.find_option st.regs rs with
    | Some v ->
      Hashtbl.replace st.regs rd (eval_unop u v);
      OK (None, st)
    | _ -> Error (Printf.sprintf "Unop applied on undefined register %s" (print_reg rs))
    end

  | Rconst (rd, i) ->
    Hashtbl.replace st.regs rd i;
    OK (None, st)

  | Rbranch (cmp, r1, r2, s1) ->
    begin match Hashtbl.find_option st.regs r1,
                Hashtbl.find_option st.regs r2 with
    | Some v1, Some v2 ->
      (if eval_rtl_cmp cmp v1 v2 then exec_rtl_instr_at oc st sp rp rtlfunname rf s1 else OK (None, st))
    | _, _ -> Error (Printf.sprintf "Branching on undefined registers (%s and %s)" (print_reg r1) (print_reg r2))
    end

  | Rjmp s -> exec_rtl_instr_at oc st sp rp rtlfunname rf s

  | Rmov (rd, rs) ->
    begin match Hashtbl.find_option st.regs rs with
    | Some s ->
      Hashtbl.replace st.regs rd s;
      OK (None, st)
    | _ -> Error (Printf.sprintf "Mov on undefined register (%s)" (print_reg rs))
    end

  | Rret r ->
    begin match Hashtbl.find_option st.regs r with
      | Some s -> OK (Some s, st)
      | _ -> Error (Printf.sprintf "Ret on undefined register (%s)" (print_reg r))
    end

  | Rlabel n -> OK (None, st)

  | Rcall (ord, fname, rargs) ->
    let args = List.map (fun elem -> Hashtbl.find st.regs elem) rargs in
    begin match find_function rp fname with
    | OK f -> begin match ord with
              | Some rd -> exec_rtl_fun oc st sp rp fname f args >>= fun (v, st) ->
                            begin match v with
                              | Some v' -> Hashtbl.replace st.regs rd v'; OK (None, st)
                              | None -> Error (Printf.sprintf "Call function %s does not have a return value" fname)
                            end
              | None -> exec_rtl_fun oc st sp rp fname f args >>= fun (v, st) -> OK (None, st)
              end
    | Error e -> do_builtin oc st.mem fname args >>= fun ret ->
                  begin match (ord, ret) with
                    | Some rd, Some ret' -> Hashtbl.replace st.regs rd ret'
                    | _ -> ()
                  end;
                  OK (None, st)
    end

  | Rstk (rd, offset) ->
    Hashtbl.replace st.regs rd (sp + offset);
    OK (None, st)

  | Rload (rd, rs, size) ->
    begin match Hashtbl.find_option st.regs rs with
    | Some address -> Mem.read_bytes_as_int st.mem address size >>= fun value ->
                      Hashtbl.replace st.regs rd value;
                      OK (None, st)
    | None -> Error (Printf.sprintf "Could not find value of register rs %d in RTL load instruction\n" rs)
    end

  | Rstore (rd, rs, size) ->
    begin match Hashtbl.find_option st.regs rs with
    | Some value -> begin match Hashtbl.find_option st.regs rd with
                    | Some address -> Mem.write_bytes st.mem address (split_bytes size value) >>= fun _ -> OK (None, st)
                    | None -> Error (Printf.sprintf "Store value in address contained in undefined register rd %d\n" rd)
                    end
    | None -> Error (Printf.sprintf "Store value contained in unkown register rs %d\n" rs)
    end

and exec_rtl_instr_at oc st sp rp rtlfunname rf index =
  match Hashtbl.find_option rf.rtlfunbody index with
  | Some l -> exec_rtl_instrs oc st sp rp rtlfunname rf l
  | None -> Error (Printf.sprintf "Jump to undefined label (%s_%d)" rtlfunname index)

and exec_rtl_instrs oc st sp rp rtlfunname rf l : (int option * state) res =
  List.fold_left (fun acc i ->
      match acc with
      | Error _ -> acc
      | OK (Some v, st) -> OK (Some v, st)
      | OK (None, st) -> exec_rtl_instr oc st sp rp rtlfunname rf i
    ) (OK (None, st)) l

and exec_rtl_fun oc st sp rp rtlfunname rf params : (int option * state) res =
  let regs' = Hashtbl.create 17 in
  match List.iter2 (fun n v -> Hashtbl.replace regs' n v) rf.rtlfunargs params with
  | exception Invalid_argument _ ->
    Error (Format.sprintf "RTL: Called function %s with %d arguments, expected %d\n"
             rtlfunname
             (List.length params)
             (List.length rf.rtlfunargs)
          )
  | _ ->
    match Hashtbl.find_option rf.rtlfunbody rf.rtlfunentry with
    | None ->
      Error (Printf.sprintf "Unknown node (%s_%d)" rtlfunname rf.rtlfunentry)
    | Some l ->
      let regs_save = Hashtbl.copy st.regs in
      let st' = {st with regs = regs'; } in
      exec_rtl_instrs oc st' (sp - rf.rtlfunstksz) rp rtlfunname rf l >>= fun (v, st) ->
      OK(v, {st with regs = regs_save })

and exec_rtl_prog oc rp memsize params =
  let st = init_state memsize in
  find_function rp "main" >>= fun rf ->
  let n = List.length rf.rtlfunargs in
  let params = take n params in
  exec_rtl_fun oc st memsize rp "main" rf params >>= fun (v, st) ->
  OK v
