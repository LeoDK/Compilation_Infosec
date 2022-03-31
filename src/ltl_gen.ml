open Batteries
open Rtl
open Linear
open Ltl
open Ltl_print
open Prog
open Utils
open Regalloc
open Linear_liveness
open Report
open Options

(* list of registers used to store arguments. [a0-a7] *)
let arg_registers =
  range ~start:starting_arg_register 8

(* Helpers to build pseudo-instructions.
 ** [push x] is compiled into [sub sp, sp, 8; sd r, 0(sp)]
 ** [pop x] is compiled into [ld r, 0(sp); add sp, sp, 8]
*)

let make_push r =
  [LSubi(reg_sp, reg_sp, (Archi.wordsize ()));
   LStore(reg_sp, 0, r, (archi_mas ()))]

let make_pop r =
  [LLoad(r, reg_sp, 0, (archi_mas ()));
   LAddi(reg_sp, reg_sp, (Archi.wordsize ()))]

let make_sp_sub v =
  [LSubi(reg_sp, reg_sp, v)]

let make_sp_add v =
  [LAddi(reg_sp, reg_sp, v)]

(* Moving between locations. [src] and [dst] are locations. [make_loc_mov src
   dst] generates instructions so that the value in [src] ends up in [dst],
   where [src] and [dst] can be registers [Reg r] or stack offsets [Stk o].
*)
let make_loc_mov src dst =
  match src, dst with
  | Stk osrc , Stk odst ->
    let rtmp = reg_tmp1 in
    [LLoad(rtmp, reg_fp, (Archi.wordsize ()) * osrc, (archi_mas ()));
     LStore(reg_fp, (Archi.wordsize ()) * odst, rtmp, (archi_mas ()))]
  | Stk osrc, Reg rdst ->
    [LLoad(rdst, reg_fp, (Archi.wordsize ()) * osrc, (archi_mas ()))]
  | Reg rsrc, Stk ofst ->
    [LStore(reg_fp, (Archi.wordsize ()) * ofst, rsrc, (archi_mas ()))]
  | Reg rsrc, Reg rdst ->
    [LMov(rdst,rsrc)]

(* load_loc tmp allocation r = (l, r'). Loads the equivalent of RTL register r
   in a LTL register r'. tmpis used if necessary. *)
let load_loc tmp allocation r =
  match Hashtbl.find_option allocation r with
  | None ->
    Error (Format.sprintf "Unable to allocate RTL register r%d." r)
  | Some (Stk o) -> OK ([LLoad(tmp, reg_fp, (Archi.wordsize ()) * o, (archi_mas ()))], tmp)
  | Some (Reg r) -> OK ([], r)

(* store_loc tmp allocation r = (l, r'). I want to write in RTL register r.
   Tells me that I just have to write to LTL register r' and execute l. *)
let store_loc tmp allocation r =
  match Hashtbl.find_option allocation r with
  | None ->
    Error (Format.sprintf "Unable to allocate RTL register r%d." r)
  | Some (Stk o) -> OK ([LStore(reg_fp, (Archi.wordsize ()) * o, tmp, (archi_mas ()))], tmp)
  | Some (Reg r) -> OK ([], r)

(* saves registers in [to_save] on the stack at offsets [sp + 8 * o, sp + 8 * (o
   + 1), sp + 8 * (o + 2)...]. Returns:

   - an association list [(reg,ofs)] (meaning register reg is saved at [sp+ofs])
   - the list of store instructions - the next offset to be written. *)
let save_caller_save to_save ofs =
  List.fold_left (fun (instrs, arg_saved, ofs) reg ->
      (instrs @ [LStore(reg_sp, (Archi.wordsize ()) * ofs, reg, (archi_mas ()))],
       (reg,ofs)::arg_saved, ofs + 1)
    ) ([], [], ofs) to_save

(* Given a list [(reg,ofs)], loads [sp+ofs] into [reg]. *)
let restore_caller_save arg_saved =
  List.map
    (fun (reg, ofs) -> LLoad(reg, reg_sp, (Archi.wordsize ()) * ofs, (archi_mas ())))
    arg_saved

let num_parameters_passed_on_stack regs =
  let r = List.length regs - number_of_arguments_passed_in_registers in
  Stdlib.max 0 r


(* Given a list or RTL registers [rargs], we want to load their values in LTL
   argument registers a0-7. But while writing these registers, we may overwrite
   the value of some registers before we actually read them.

   For example if [r1 -> a1] and [r2 -> a0], and we want to load [r1] in [a0]
   and [r2] in [a1] (because a function call f(r1,r2) occurs), the following
   would happen :

   mv a0, a1
   mv a1, a0

   But the value in [a1] will not be the value that was originally in RTL reg
   [r2].

   Hence, we keep track of the registers like [a1] that are going to be written
   before being read, and those will be saved on the stack.
*)
let overwritten_args rargs allocation =

  (* [ltl_args] contains the locations of RTL args after allocation. *)
    list_map_res (fun r -> match Hashtbl.find_option allocation r with
        | None -> Error (Format.sprintf
                              "overwritten_args: Couldn't allocate register r%d."
                              r)
        | Some loc -> OK loc
      ) rargs >>= fun ltl_args ->

  let (overwritten, read_overwritten) =
    List.fold_lefti (fun (overwritten, read_overwritten) i (src: loc) ->
        (* [overwritten] contains the list of registers that have been written
           to.

           [read_overwritten] contains the list of registers that have been read
           after being written to. *)
        let read_overwritten =
          match src with
          | Reg rs -> if Set.mem rs overwritten
            then Set.add rs read_overwritten
            else read_overwritten
          | Stk _ -> read_overwritten
        in
        let overwritten =
          if i < number_of_arguments_passed_in_registers
          then Set.add (starting_arg_register + i) overwritten
          else overwritten
        in (overwritten, read_overwritten)
      ) (Set.empty,Set.empty) ltl_args in
  OK read_overwritten



(* [pass_parameters rargs allocation arg_saved ofs] generates code to pass
   parameters in RTL registers rargs. [allocation] maps RTL registers to LTL
   locations, [arg_saved] contains saved registers, and [ofs] says where,
   relative to reg_fp we may save more registers if needed. *)
let pass_parameters rargs allocation arg_saved =
  (* LTL locations corresponding to RTL arguments.  *)
  list_map_res (fun r -> match Hashtbl.find_option allocation r with
      | None ->
        Error (Format.sprintf
                 "pass_parameters: Couldn't allocate register r%d." r)
      | Some loc -> OK loc
    ) rargs >>= fun ltl_args ->

  (* Relocation of arguments may be necessary if, e.g. a1 must be passed as
     first argument (in a0) and a0 must be passed as second argument (in a1). In
     that situation, a temporary must be used. These registers (a0 and a1) would
     have been saved before on the stack and the relocation information is
     available in arg_saved. *)
  let reloc_loc overwritten loc =
    match loc with
    | Stk o -> OK loc
    | Reg r -> if List.mem r overwritten
      then match List.assoc_opt r arg_saved with
        | None -> Error (Format.sprintf "Register %s has been overwritten, \
                                         yet it has not been saved."
                           (print_reg r))
        | Some newloc -> OK (Stk newloc)
      else OK loc
  in
  (* Iterates over the list of LTL arguments. Generates 4 things:

     - [overwritten] is the set of registers that are overwritten during
       parameter passing. If a register has been overwritten, then we use its copy
       on the stack; otherwise we can use it directly.

     - [instrs] is a list of instructions for the arguments passed in registers.

     - [pushes] is a list of push pseudo-instructions for every additional
       argument. The two lists are built separately so that we can build [pushes]
       backwards so that e.g. the 9th argument is at the top of the stack at the
       end, and e.g. the 15th at higher addresses.

     - [npush] is the number of arguments that were pushed to the stack. *)

  List.fold_lefti (fun acc i (src: loc) ->
      acc >>= fun (overwritten, instrs, pushes, npush) ->
      reloc_loc overwritten src >>= fun src ->
      let (overwritten, l,pushes, npush) =
        if i < number_of_arguments_passed_in_registers
        then let rd = starting_arg_register + i in
          begin match src with
            | Reg rs ->  (rd::overwritten, [LMov(rd, rs)],[], npush)
            | Stk o -> (rd::overwritten,
                        [LLoad(rd, reg_sp, (Archi.wordsize ()) * o, (archi_mas ()))],
                        [], npush)
          end else
          begin match src with
            | Reg rs -> (overwritten, [], make_push rs@pushes, npush+1)
            | Stk o ->  (overwritten, [],
                         LLoad(reg_tmp1, reg_sp, (Archi.wordsize ()) * o, (archi_mas ()))
                         ::make_push reg_tmp1 @ pushes,
                         npush+1)
          end
      in
      OK (overwritten, instrs@l, pushes, npush)
    ) (OK ([], [], [], 0)) ltl_args >>=
  fun (overwritten, instrs, pushes, npush) ->
  OK (instrs@pushes, npush)

let written_rtl_regs_instr (i: rtl_instr) =
  match i with
  | Rbinop (_, rd, _, _)
  | Runop (_, rd, _)
  | Rconst (rd, _)
  | Rstk (rd, _)
  | Rload (rd, _, _)
  | Rstore (rd, _, _)
  | Rmov (rd, _) -> Set.singleton rd
  | Rret _
  | Rlabel _
  | Rbranch (_, _, _, _)
  | Rjmp _ -> Set.empty
  | Rcall (ord, fname, rargs) ->  begin match ord with
                                  | Some rd -> Set.singleton rd
                                  | None -> Set.empty
                                  end

let read_rtl_regs_instr (i: rtl_instr) =
  match i with
  | Rbinop (_, _, rs1, rs2)
  | Rbranch (_, rs1, rs2, _) -> Set.of_list [rs1; rs2]
  | Runop (_, _, rs)
  | Rmov (_, rs)
  | Rload (_, rs, _)
  | Rstore (_, rs, _)
  | Rret rs -> Set.singleton rs
  | Rlabel _
  | Rconst (_, _)
  | Rstk (_, _)
  | Rjmp _ -> Set.empty
  | Rcall (ord, fname, rargs) -> List.fold_left (fun acc elem -> Set.add elem acc) Set.empty rargs

let read_rtl_regs (l: rtl_instr list) =
  List.fold_left (fun acc i -> Set.union acc (read_rtl_regs_instr i))
    Set.empty l

let written_rtl_regs (l: rtl_instr list) =
  List.fold_left (fun acc i -> Set.union acc (written_rtl_regs_instr i))
    Set.empty l

let rtl_to_ltl_registers allocation l =
  Set.filter_map (fun rtlreg ->
      match Hashtbl.find_option allocation rtlreg with
      | Some (Stk ofs) -> None
      | None -> None
      | Some (Reg r) -> Some r) l

(* Take the RTL registers used by RTL instructions in [l], apply allocation to
   them. This gives a list of machine registers used by the LTL function. We
   need to add also the registers that will be used for argument passing. *)

let written_ltl_regs fname l allocation =
  written_rtl_regs l |> rtl_to_ltl_registers allocation

let caller_save live_out allocation rargs =
  let live_after = live_out in
  let live_after_ltl = live_after |> rtl_to_ltl_registers allocation in
  overwritten_args rargs allocation >>= fun overwritten_args_tosave ->
  let l = Set.union live_after_ltl overwritten_args_tosave in
  OK (Set.intersect l (Set.of_list (arg_registers @ reg_tmp)))

(* This generates LTL instructions for a given Linear/RTL instruction. In most
   cases, the transformation amounts to 'loading' RTL registers in LTL locations
   and emitting the straightforward corresponding LTL instructions. This uses
   load_loc and store_loc, described above, a lot. The most interesting case is
   call instructions. Indeed, in that case, we emit code for saving and
   restoring caller-save registers before and after the call, respectively. The
   registers to be saved are computed as the set of Risc-V registers marked as
   caller-save (a0-a7,t0-t6) intersected with the registers that are read in the
   code of the caller. (The rationale being, if we don't read this variable,
   then we don't need its value to be preserved across function calls.) These
   registers are saved at [fp - 8 * (curstackslot + 1)] *)
let ltl_instrs_of_linear_instr fname live_out allocation numspilled epilogue_label numlocals ins =
  let res =
  match ins with
  | Rbinop (b, rd, rs1, rs2) ->
    load_loc reg_tmp1 allocation rs1 >>= fun (ltl_load_1, ltl_rs1) ->
    load_loc reg_tmp2 allocation rs2 >>= fun (ltl_load_2, ltl_rs2) ->
    store_loc reg_tmp1 allocation rd >>= fun (ltl_store, ltl_rd) ->
    OK (ltl_load_1 @ ltl_load_2 @ LBinop(b, ltl_rd, ltl_rs1, ltl_rs2) :: ltl_store)

  | Runop (u, rd, rs) ->
    load_loc reg_tmp1 allocation rs >>= fun (ltl_load, ltl_rs) ->
    store_loc reg_tmp1 allocation rd >>= fun (ltl_store, ltl_rd) ->
    OK (ltl_load @ LUnop(u, ltl_rd, ltl_rs) :: ltl_store)

  | Rconst (rd, i) ->
    store_loc reg_tmp1 allocation rd >>= fun (ltl_store, ltl_rd) ->
    OK (LConst(ltl_rd, i) :: ltl_store)

  | Rbranch (cmp, rs1, rs2, s1) ->
    load_loc reg_tmp1 allocation rs1 >>= fun (ltl_load_1, ltl_rs1) ->
    load_loc reg_tmp2 allocation rs2 >>= fun (ltl_load_2, ltl_rs2) ->
    OK (ltl_load_1 @ ltl_load_2 @ [LBranch(cmp, ltl_rs1, ltl_rs2, Format.sprintf "%s_%d" fname s1)])

  | Rjmp s -> OK [LJmp (Format.sprintf "%s_%d" fname s)]

  | Rmov (rd, rs) ->
    load_loc reg_tmp1 allocation rs >>= fun (ltl_load, ltl_rs) ->
    store_loc reg_tmp1 allocation rd >>= fun (ltl_store, ltl_rd) ->
    OK (ltl_load @ LMov(ltl_rd, ltl_rs) :: ltl_load)

  | Rret rs ->
    load_loc reg_tmp1 allocation rs >>= fun (ltl_load, ltl_rs) ->
    OK (ltl_load @ [LMov (reg_ret, ltl_rs) ; LJmp epilogue_label])

  | Rlabel l -> OK [LLabel (Format.sprintf "%s_%d" fname l)]

  | Rcall (ord, fname, rargs) ->  
    (* Get registers to save on the stack (temporary registers that are alive after, and arguments *)
    caller_save live_out allocation rargs >>= fun to_save ->
    let to_save = Set.fold (fun elem acc -> acc @ [elem]) to_save [] in
    (* Decrease stack pointer, and execute all instructions to save previous registers on stack *)
    let instrs, arg_saved, ofs = save_caller_save to_save 0 in
    let instrs = (LAddi (reg_sp, reg_sp, - ofs * (Archi.wordsize())))::instrs in
    (* Pass parameters (some of them on the stack) *)
    pass_parameters rargs allocation arg_saved >>= fun (parameter_passing_instructions, npush) ->
    let instrs = instrs @ parameter_passing_instructions in
    (* Call function *)
    let instrs = instrs @ [LCall fname] in
    (* Put the result in rd if needed *)
    begin match ord with
    (* get the real location associated with RTL register [rd] *)
    | Some rd ->  begin match Hashtbl.find_option allocation rd with
                  | Some rd_alloc ->
                    let instrs = instrs @ (make_loc_mov (Reg reg_a0) rd_alloc) in
                    (* Prevent [rd] from being restored *)
                    let arg_saved = begin match rd_alloc with
                                    | Reg r -> List.filter (fun (reg, ofs) -> r <> reg) arg_saved
                                    | Stk offset -> arg_saved
                                    end in
                    OK (instrs, arg_saved)
                  | None -> Error (Format.sprintf "Could not find allocation for RTL register %d\n" rd)
                  end
    | None -> OK (instrs, arg_saved)
    end >>= fun (instrs, arg_saved) ->
    (* Restore registers stored on stack *)
    let restore = restore_caller_save arg_saved in
    (* Finally pop arguments and saved registers off the stack *)
    OK (instrs @ restore @ [LAddi (reg_sp, reg_sp, (ofs + npush) * (Archi.wordsize()))])

  | Rstk (rd, offset) ->
    store_loc reg_tmp1 allocation rd >>= fun (ltl_store, ltl_rd) ->
    OK (LAddi (ltl_rd, reg_fp, - ((numspilled+1) * (Archi.wordsize()) + offset)) :: ltl_store)

  | Rload (rd, rs, size) ->
    load_loc reg_tmp1 allocation rs >>= fun (ltl_load, ltl_rs) ->
    store_loc reg_tmp2 allocation rd >>= fun (ltl_store, ltl_rd) ->
    mas_of_size size >>= fun mas ->
    OK (ltl_load @ (LLoad (ltl_rd, ltl_rs, 0, mas) :: ltl_store))

  | Rstore (rd, rs, size) ->
    load_loc reg_tmp1 allocation rs >>= fun (ltl_load, ltl_rs) ->
    store_loc reg_tmp2 allocation rd >>= fun (ltl_store, ltl_rd) ->
    mas_of_size size >>= fun mas ->
    OK (ltl_load @ (LStore (ltl_rd, 0, ltl_rs, mas)) :: ltl_store)

  in
  res >>= fun l ->
  OK (LComment (Format.asprintf "#<span style=\"background: pink;\"><b>Linear instr</b>: %a #</span>" (Rtl_print.dump_rtl_instr fname (None, None)) ins)::l)

(** Retrieves the location of the n-th argument (in the callee). The first 8 are
   passed in a0-a7, the next are passed on the stack. *)
let retrieve_nth_arg n numcalleesave =
  let thr = number_of_arguments_passed_in_registers in
  if n < thr
  then Reg (n + starting_arg_register)
  else Stk ((numcalleesave + n-thr))

(* This function creates a LTL function out of a Linear function. In addition to
   using machine registers instead of ideal registers, it deals with saving and
   restoring callee-save registers. The function prologue consists of saving
   these callee-save registers, making the frame pointer to sp, and saving space
   on the stack for the variables that would reside on the stack (i.e. spilled -
   they go from [s0] to [s0+curstackslot] (curstackslot is negative, and
   returned by the register allocation)). The function epilogue restores sp to
   the value stored in s0 (fp), restore all the callee-save registers and jumps
   back to [ra]. *)
let ltl_fun_of_linear_fun linprog (lf: linear_fun) fname (live_in,live_out) (allocation, numspilled) =
  List.iteri (fun i pr ->
      Hashtbl.replace allocation pr (retrieve_nth_arg i 0)
    ) lf.linearfunargs;
  Printf.printf "%s Fun stack size : %d\n" fname lf.linearfunstksz;
  let numlocals = (lf.linearfunstksz + (Archi.wordsize()) - 1) / (Archi.wordsize()) in
  let written_regs = Set.add reg_ra
      (Set.add reg_fp
         (written_ltl_regs fname lf.linearfunbody allocation)) in
  let callee_saved_regs =
    Set.intersect (Set.of_list callee_saved) written_regs in
  List.iteri (fun i pr ->
      Hashtbl.replace allocation pr
        (retrieve_nth_arg i (Set.cardinal callee_saved_regs))
    ) lf.linearfunargs;

  let max_label =
    List.fold_left (fun acc i ->
        match i with
          Rlabel l -> Stdlib.max l acc
        | _ -> acc)
      0 lf.linearfunbody in
  let epilogue_label = Format.sprintf "%s_%d" fname (max_label + 1) in
  let prologue =
    List.concat (List.map make_push (Set.to_list callee_saved_regs)) @
    LMov (reg_fp, reg_sp) ::
    make_sp_sub ((numspilled+numlocals)* (Archi.wordsize ())) @
    [LComment "end prologue"] in
  let epilogue = LLabel epilogue_label ::
                 LMov(reg_sp, reg_fp) ::
                 List.concat (List.map make_pop
                                (List.rev (Set.to_list callee_saved_regs))) @
                 [LJmpr reg_ra] in
  list_map_resi (fun i ->
      ltl_instrs_of_linear_instr fname (Hashtbl.find_default live_out i Set.empty)
        allocation numspilled epilogue_label numlocals) lf.linearfunbody
  >>= fun l ->
  let instrs = List.concat l 
  in
  OK {
    ltlfunargs = List.length lf.linearfunargs;
    ltlfunbody = prologue @ instrs @ epilogue;
    ltlfuninfo = lf.linearfuninfo;
    ltlregalloc = Hashtbl.bindings allocation;
  }


let allocable_registers = Set.of_list [
  reg_s1; reg_s2; reg_s3; reg_s4; reg_s5;
  reg_s6; reg_s7; reg_s8; reg_s9; reg_s10; reg_s11;
  reg_t2; reg_t3; reg_t4; reg_t5; reg_t6;
]

let ltl_prog_of_linear lp =
  let lives = liveness_linear_prog lp in
  let allocations = regalloc lp lives allocable_registers in
  let prog = list_map_res (function
        (fname, Gfun f) ->
        let f_alloc =
          match Hashtbl.find_option allocations fname with
          | None -> (Hashtbl.create 0, 0)
          | Some (rig, allocation, next_stack_slot) -> (allocation, - next_stack_slot - 1)
        in
        let f_lives =
          match Hashtbl.find_option lives fname with
          | None -> (Hashtbl.create 0, Hashtbl.create 0)
          | Some x -> x
        in
        ltl_fun_of_linear_fun lp f fname f_lives f_alloc >>= fun f ->
        OK (fname, Gfun f)
    ) lp in
  prog

let pass_ltl_gen linear =
  match ltl_prog_of_linear linear with
  | Error msg -> record_compile_result ~error:(Some msg) "LTL"; Error msg
  | OK ltl ->
    record_compile_result "LTL";
    dump !ltl_dump dump_ltl_prog ltl
      (fun file () -> add_to_report "ltl" "LTL" (Code (file_contents file)));
    OK ltl
