(** Wasm typing rules **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)
From Coq Require Import NArith.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Import operations.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 




Definition convert_helper (sxo : option sx) (t1 t2 : number_type) : bool :=
  (sxo == None) ==
  ((is_float_t t1 && is_float_t t2) || (is_int_t t1 && is_int_t t2 && (length_tnum t1 < length_tnum t2))).

Definition convert_cond t1 t2 (sxo : option sx) : bool :=
  (t1 != t2) && convert_helper sxo t1 t2.


Definition upd_label C lab :=
  Build_t_context
    (tc_types_t C)
    (tc_func_t C)
    (tc_global C)
    (tc_table C)
    (tc_memory C)
    (tc_local C)
    lab
    (tc_return C)
    (tc_refs C)
    (tc_tags_t C).

Definition plop2 C i ts :=
  List.nth_error (tc_label C) i == Some ts.

Inductive result_typing : store_record -> result -> list value_type -> Prop :=
| result_typing_values : forall vs C ts, map (typeof C) vs = map Some ts ->
                                    result_typing C (result_values vs) ts
| result_typing_trap : forall ts C, result_typing C result_trap ts
  .

Inductive unop_type_agree: number_type -> unop -> Prop :=
  | Unop_i32_agree: forall op, unop_type_agree T_i32 (Unop_i op)
  | Unop_i64_agree: forall op, unop_type_agree T_i64 (Unop_i op)
  | Unop_f32_agree: forall op, unop_type_agree T_f32 (Unop_f op)
  | Unop_f64_agree: forall op, unop_type_agree T_f64 (Unop_f op)
  .
   
Inductive binop_type_agree: number_type -> binop -> Prop :=
  | Binop_i32_agree: forall op, binop_type_agree T_i32 (Binop_i op)
  | Binop_i64_agree: forall op, binop_type_agree T_i64 (Binop_i op)
  | Binop_f32_agree: forall op, binop_type_agree T_f32 (Binop_f op)
  | Binop_f64_agree: forall op, binop_type_agree T_f64 (Binop_f op)
  .
  
Inductive relop_type_agree: number_type -> relop -> Prop :=
  | Relop_i32_agree: forall op, relop_type_agree T_i32 (Relop_i op)
  | Relop_i64_agree: forall op, relop_type_agree T_i64 (Relop_i op)
  | Relop_f32_agree: forall op, relop_type_agree T_f32 (Relop_f op)
  | Relop_f64_agree: forall op, relop_type_agree T_f64 (Relop_f op)
  .


  
Inductive exception_clause_identifier_typing : t_context -> exception_clause_identifier -> Prop :=
| ect_catch : forall C x l (ts: list value_type),
    List.nth_error (tc_tags_t C) x = Some (Tf ts [::]) ->
    List.nth_error (tc_label C) l = Some ts ->
    exception_clause_identifier_typing C (HE_catch (Mk_tagident x) l) 
| ect_catch_ref : forall C x l ts,
    List.nth_error (tc_tags_t C) x = Some (Tf ts [::]) ->
    List.nth_error (tc_label C) l = Some (ts ++ [:: T_ref T_exnref]) ->
    exception_clause_identifier_typing C (HE_catch_ref (Mk_tagident x) l)
| ect_catch_all : forall C l,
    List.nth_error (tc_label C) l = Some [::] ->
    exception_clause_identifier_typing C (HE_catch_all l)
| ect_catch_all_ref: forall C l,
    List.nth_error (tc_label C) l = Some [:: T_ref T_exnref] ->
    exception_clause_identifier_typing C (HE_catch_all_ref l)
  .

  Inductive continuation_clause_identifier_typing : t_context -> continuation_clause_identifier -> list value_type -> Prop :=
  | cct_clause : forall C x l t1s' t2s' t2s,
      List.nth_error (tc_tags_t C) x = Some (Tf t1s' t2s') ->
      List.nth_error (tc_label C) l = Some (t1s' ++ [::T_ref (T_contref (Tf t2s' t2s))]) ->
      continuation_clause_identifier_typing C (HC_catch (Mk_tagident x) l) t2s
  | cct_switch : forall C x t2s,
      List.nth_error (tc_tags_t C) x = Some (Tf [::] t2s) ->
      continuation_clause_identifier_typing C (HC_switch (Mk_tagident x)) t2s
  .

  (*
  Inductive clause_typing : t_context -> handler_clauses -> list value_type -> Prop :=
  | ct_exception : forall C hs ts,
      List.Forall (exception_clause_typing C) hs ->
      clause_typing C (H_exception hs) ts
  | ct_continuation : forall C hs ts,
      List.Forall (fun hc => continuation_clause_typing C hc ts) hs ->
      clause_typing C (H_continuation hs) ts
.
*)

Definition get_type C i :=
  match i with
  | Type_lookup i => List.nth_error (tc_types_t C) i
  | Type_explicit t => Some t
  end. 

Definition get_tag C i :=
  match i with
  | Mk_tagident i => List.nth_error (tc_tags_t C) i
  end. 
(*  | Tag_explicit _ tf => Some tf
  end *)  



Inductive be_typing : t_context -> seq basic_instruction -> function_type -> Prop :=
| bet_const : forall C v, be_typing C [::BI_const v] (Tf [::] [:: T_num (typeof_num v)])
| bet_unop : forall C t op,
    unop_type_agree t op -> be_typing C [::BI_unop t op] (Tf [::T_num t] [::T_num t])
| bet_binop : forall C t op,
    binop_type_agree t op -> be_typing C [::BI_binop t op] (Tf [::T_num t; T_num t] [::T_num t])
| bet_testop : forall C t op, is_int_t t -> be_typing C [::BI_testop t op] (Tf [::T_num t] [::T_num T_i32])
| bet_relop: forall C t op,
    relop_type_agree t op -> be_typing C [::BI_relop t op] (Tf [::T_num t; T_num t] [::T_num T_i32])
| bet_convert : forall C t1 t2 sx, t1 <> t2 -> convert_helper sx t1 t2 ->
  be_typing C [::BI_cvtop t1 CVO_convert t2 sx] (Tf [::T_num t2] [::T_num t1]) 
| bet_reinterpret : forall C t1 t2, t1 <> t2 -> Nat.eqb (length_tnum t1) (length_tnum t2) ->
  be_typing C [::BI_cvtop t1 CVO_reinterpret t2 None] (Tf [::T_num t2] [::T_num t1])
| bet_unreachable : forall C ts ts',
  be_typing C [::BI_unreachable] (Tf ts ts')
| bet_nop : forall C, be_typing C [::BI_nop] (Tf [::] [::])
| bet_drop : forall C t, be_typing C [::BI_drop] (Tf [::t] [::])
| bet_select : forall C t, be_typing C [::BI_select] (Tf [::t; t; T_num T_i32] [::t])

| bet_ref_null: forall C t, be_typing C [::BI_ref_null t] (Tf [::] [::T_ref t])
| bet_ref_is_null: forall C t, be_typing C [::BI_ref_is_null] (Tf [::T_ref t] [::T_num T_i32])
| bet_ref_func: forall C t x,
    x < length (tc_func_t C) ->
    List.nth_error (tc_func_t C) x = Some t ->
(*    List.In x (tc_refs C) ->  *)
    be_typing C [::BI_ref_func x] (Tf [::] [::T_ref (T_funcref t)])
| bet_call_reference: forall C i tf t1s t2s,
    get_type C i = Some tf ->
    tf = Tf t1s t2s ->
    be_typing C [::BI_call_reference i] (Tf (t1s ++ [::T_ref (T_funcref tf)]) t2s)
| bet_throw: forall C x t1s t2s ts,
    List.nth_error (tc_tags_t C) x = Some (Tf ts [::]) ->
    be_typing C [::BI_throw x] (Tf (t1s ++ ts) t2s)
| bet_throw_ref : forall C t1s t2s,
    be_typing C [::BI_throw_ref] (Tf (t1s ++ [:: T_ref T_exnref]) t2s)


| bet_contnew : forall C i tf,
    get_type C i = Some tf ->
    be_typing C [::BI_contnew i] (Tf [::T_ref (T_funcref tf)]
                                   [:: T_ref (T_contref tf)])
 | bet_resume : forall C i t1s t2s hs,
    get_type C i = Some (Tf t1s t2s) ->
    List.Forall (fun h => continuation_clause_identifier_typing C h t2s) hs ->
    be_typing C [:: BI_resume i hs] (Tf (t1s ++ [:: T_ref (T_contref (Tf t1s t2s))]) t2s)
| bet_suspend : forall C x tf,
    get_tag C x = Some tf ->
    be_typing C [::BI_suspend x] tf
| bet_switch : forall C i x ts tf tf' t1s t2s,
    get_tag C x = Some (Tf [::] ts) ->
    get_type C i = Some tf ->
    tf = Tf (t1s ++ [::T_ref (T_contref (Tf t2s ts))]) ts ->
    tf' = Tf (t1s ++ [:: T_ref (T_contref tf)]) t2s ->
    be_typing C [::BI_switch i x] tf' 
| bet_contbind : forall C i i' ft ft' ts t1s t2s,
    get_type C i = Some ft ->
    get_type C i' = Some ft' ->
    ft = Tf (ts ++ t1s) t2s ->
    ft' = Tf t1s t2s ->
    be_typing C [:: BI_contbind i i'] (Tf (ts ++ [:: T_ref (T_contref ft)]) [:: T_ref (T_contref ft')])
| bet_resume_throw : forall C i x hs ts t1s t2s,
    get_type C i = Some (Tf t1s t2s) ->
    List.nth_error (tc_tags_t C) x = Some (Tf ts [::]) ->
    List.Forall (fun h => continuation_clause_identifier_typing C h t2s) hs ->
    be_typing C [:: BI_resume_throw i x hs] (Tf (ts ++ [:: T_ref (T_contref (Tf t1s t2s))]) t2s)
              

| bet_try_table: forall C C' t1s t2s cs es i,
    get_type C i = Some (Tf t1s t2s) ->
    List.Forall (fun c => exception_clause_identifier_typing C c) cs ->
    C' = upd_label C ([::t2s] ++ tc_label C) ->
    be_typing C' es (Tf t1s t2s) ->
    be_typing C [:: BI_try_table i cs es] (Tf t1s t2s)


                                
| bet_block : forall C tn tm es,
  let tf := Tf tn tm in
  be_typing (upd_label C (app [::tm] (tc_label C))) es (Tf tn tm) ->
  be_typing C [::BI_block tf es] (Tf tn tm)
| bet_loop : forall C tn tm es,
  be_typing (upd_label C (app [::tn] (tc_label C))) es (Tf tn tm) ->
  be_typing C [::BI_loop (Tf tn tm) es] (Tf tn tm)
| bet_if_wasm : forall C tn tm es1 es2,
  be_typing (upd_label C (app [::tm] (tc_label C))) es1 (Tf tn tm) ->
  be_typing (upd_label C (app [::tm] (tc_label C))) es2 (Tf tn tm) ->
  be_typing C [::BI_if (Tf tn tm) es1 es2] (Tf (app tn [::T_num T_i32]) tm)
| bet_br : forall C i t1s ts t2s,
  i < length (tc_label C) ->
  plop2 C i ts ->
  be_typing C [::BI_br i] (Tf (app t1s ts) t2s)
| bet_br_if : forall C i ts,
  i < length (tc_label C) ->
  plop2 C i ts ->
  be_typing C [::BI_br_if i] (Tf (app ts [::T_num T_i32]) ts)
| bet_br_table : forall C i ins ts t1s t2s,
  all (fun i => (i < length (tc_label C)) && (plop2 C i ts)) (app ins [::i])  ->
  be_typing C [::BI_br_table ins i] (Tf (app t1s (app ts [::T_num T_i32])) t2s)
| bet_return : forall C ts t1s t2s,
  tc_return C = Some ts ->
  be_typing C [::BI_return] (Tf (app t1s ts) t2s)
| bet_call : forall C i t1s t2s,
  i < length (tc_func_t C) ->
  List.nth_error (tc_func_t C) i = Some (Tf t1s t2s) ->
  be_typing C [::BI_call i] (Tf t1s t2s)
| bet_call_indirect : forall C i t1s t2s,
  get_type C i = Some (Tf t1s t2s) ->
  tc_table C <> nil ->
  be_typing C [::BI_call_indirect i] (Tf (app t1s [::T_num T_i32]) t2s)
| bet_get_local : forall C i t,
  i < length (tc_local C) ->
  List.nth_error (tc_local C) i = Some t ->
  be_typing C [::BI_get_local i] (Tf [::] [::t])
| bet_set_local : forall C i t,
  i < length (tc_local C) ->
  List.nth_error (tc_local C) i = Some t ->
  be_typing C [::BI_set_local i] (Tf [::t] [::])
| bet_tee_local : forall C i t,
  i < length (tc_local C) ->
  List.nth_error (tc_local C) i = Some t ->
  be_typing C [::BI_tee_local i] (Tf [::t] [::t])
| bet_get_global : forall C i t,
  i < length (tc_global C) ->
  option_map tg_t (List.nth_error (tc_global C) i) = Some t ->
  be_typing C [::BI_get_global i] (Tf [::] [::T_num t])
| bet_set_global : forall C i g t,
  i < length (tc_global C) ->
  List.nth_error (tc_global C) i = Some g ->  
  tg_t g = t ->
  is_mut g ->
  be_typing C [::BI_set_global i] (Tf [::T_num t] [::])
| bet_load : forall C a off tp_sx t,
  tc_memory C <> nil ->
  load_store_t_bounds a (option_projl tp_sx) t ->
  be_typing C [::BI_load t tp_sx a off] (Tf [::T_num T_i32] [::T_num t])
| bet_store : forall C a off tp t,
  tc_memory C <> nil ->
  load_store_t_bounds a tp t ->
  be_typing C [::BI_store t tp a off] (Tf [::T_num T_i32; T_num t] [::])
| bet_current_memory : forall C,
  tc_memory C <> nil ->
  be_typing C [::BI_current_memory] (Tf [::] [::T_num T_i32])
| bet_grow_memory : forall C,
  tc_memory C <> nil ->
  be_typing C [::BI_grow_memory] (Tf [::T_num T_i32] [::T_num T_i32])
| bet_empty : forall C,
  be_typing C [::] (Tf [::] [::])
| bet_composition : forall C es e t1s t2s t3s,
  be_typing C es (Tf t1s t2s) ->
  be_typing C [::e] (Tf t2s t3s) ->
  be_typing C (app es [::e]) (Tf t1s t3s)
| bet_weakening : forall C es ts t1s t2s,
  be_typing C es (Tf t1s t2s) ->
  be_typing C es (Tf (app ts t1s) (app ts t2s))
.

Definition upd_refs C refs :=
  Build_t_context
    (tc_types_t C)
    (tc_func_t C)
    (tc_global C)
    (tc_table C)
    (tc_memory C)
    (tc_local C)
    (tc_label C)
    (tc_return C)
    refs
    (tc_tags_t C)
.
Definition upd_tags C tags :=
  Build_t_context
    (tc_types_t C)
    (tc_func_t C)
    (tc_global C)
    (tc_table C)
    (tc_memory C)
    (tc_local C)
    (tc_label C)
    (tc_return C)
    (tc_refs C)
    tags
.

Definition upd_local C loc :=
  Build_t_context
    (tc_types_t C)
    (tc_func_t C)
    (tc_global C)
    (tc_table C)
    (tc_memory C)
    loc
    (tc_label C)
    (tc_return C)
    (tc_refs C)
        (tc_tags_t C)
.

Definition upd_return C ret :=
  Build_t_context
    (tc_types_t C)
    (tc_func_t C)
    (tc_global C)
    (tc_table C)
    (tc_memory C)
    (tc_local C)
    (tc_label C)
    ret
    (tc_refs C)
    (tc_tags_t C)
.

Definition upd_local_return C loc ret :=
  Build_t_context
    (tc_types_t C)
    (tc_func_t C)
    (tc_global C)
    (tc_table C)
    (tc_memory C)
    loc
    (tc_label C)
    ret
    (tc_refs C)
    (tc_tags_t C).

Definition upd_local_label_return C loc lab ret :=
  Build_t_context
    (tc_types_t C)
    (tc_func_t C)
    (tc_global C)
    (tc_table C)
    (tc_memory C)
    loc
    lab
    ret
    (tc_refs C)
    (tc_tags_t C).

(**
 g_mut says whether the global is mutable; then it has another field g_val
   specifying the value (with type).
 **)

Definition global_agree (g : global) (tg : global_type) : bool :=
  (tg_mut tg == g_mut g) && ((tg_t tg) == typeof_num (g_val g)). 


(* || ((typeof C (g_val g) == T_ref T_corruptref) && (match tg_t tg with | T_ref _ => true | _ => false end))). (* references are allowed to be corrupt *) *)

Definition globals_agree (gs : seq global) (n : nat) (tg : global_type) : bool :=
  (n < length gs) && (option_map (fun g => global_agree g tg) (List.nth_error gs n) == Some true).


Definition mem_typing (m : memory) (m_t : memory_type) : bool :=
  (N.leb m_t.(lim_min) (mem_size m)) &&
  (m.(mem_max_opt) == m_t.(lim_max)) (* TODO: mismatch *).

Definition memi_agree (ms : list memory) (n : nat) (mem_t : memory_type) : bool :=
  (n < length ms) &&
  match List.nth_error ms n with
  | Some mem => mem_typing mem mem_t
  | None => false
  end.

Definition functions_agree (fs : seq function_closure) (n : nat) (f : function_type) : bool :=
  (n < length fs) && (option_map cl_type (List.nth_error fs n) == Some f).
Definition tab_typing (t : tableinst) (tt : table_type) : bool :=
  (tt.(tt_limits).(lim_min) <= tab_size t) &&
  (t.(table_max_opt) <= tt.(tt_limits).(lim_max)).

Definition tabi_agree ts (n : nat) (tab_t : table_type) : bool :=
  (* (n < List.length ts) && *)
  match List.nth_error ts n with
  | None => false
  | Some x => tab_typing x tab_t
  end.
Definition tag_agree (tags: list function_type) n tagt :=
  match List.nth_error tags n with
  | None => false
  | Some x => x == tagt
  end. 


Definition inst_typing (s : store_record) (inst : instance) (C : t_context) : bool :=
  let '{| inst_types := ts;
         inst_funcs := fs;
         inst_tab := tbs;
         inst_memory := ms;
         inst_globs := gs;
         inst_tags := tag_ids;
       |} := inst in
  match C with
  | {| tc_types_t := ts';
      tc_func_t := tfs;
      tc_global := tgs;
      tc_table := tabs_t;
      tc_memory := mems_t;
      tc_local := nil;
      tc_label := nil;
      tc_return := None;
      tc_tags_t := tags;
    |} =>
      (ts == ts') &&
    (all2 (functions_agree s.(s_funcs)) fs tfs) &&
    (all2 (globals_agree s.(s_globals)) gs tgs) &&
    (all2 (tabi_agree s.(s_tables)) tbs tabs_t) &&
        (all2 (memi_agree s.(s_mems)) ms mems_t) &&
        (all2 (tag_agree s.(s_tags)) tag_ids tags)
  | _ => false
  end.

Lemma inst_typing_tags s i C :
  inst_typing s i C -> all2 (tag_agree (s_tags s)) (inst_tags i) (tc_tags_t C).
Proof.
  unfold inst_typing. destruct i => //. destruct C => //.
  destruct tc_local, tc_label, tc_return => //.
  intros H. move/andP in H. destruct H => //.
(*  move/eqP in H0. done. *)
Qed.

Lemma inst_typing_types s i C :
  inst_typing s i C -> tc_types_t C = inst_types i.
Proof.
  unfold inst_typing. destruct i => //. destruct C => //.
  destruct tc_local, tc_label, tc_return => //.
  intros H.
  repeat (move/andP in H; destruct H as [H ?]).
  move/eqP in H. done.
Qed. 



Lemma functions_agree_injective: forall s i t t',
  functions_agree s i t ->
  functions_agree s i t' ->
  t = t'.
Proof.
  move => s i t t' H1 H2.
  unfold functions_agree in H1. unfold functions_agree in H2.
  move/andP: H1 => [_ H1].
  move/andP: H2 => [_ H3].
  move/eqP in H1. move/eqP in H3.
  rewrite H3 in H1 => {H3}.
  by move: H1 => [H1].
Qed.


Inductive cl_typing : store_record -> function_closure -> function_type -> Prop :=
  | cl_typing_native : forall i s C C' ts t1s t2s es tf,
    inst_typing s i C ->
    tf = Tf t1s t2s ->
    C' = upd_local_label_return C (tc_local C ++ t1s ++ ts) ([::t2s] ++ tc_label C) (Some t2s) ->
    be_typing C' es (Tf [::] t2s) ->
    cl_typing s (FC_func_native i tf ts es) (Tf t1s t2s)
  | cl_typing_host : forall s tf h,
    cl_typing s (FC_func_host tf h) tf
.

Definition strip C :=
  Build_t_context
    (tc_types_t C)
    (tc_func_t C)
    (tc_global C)
    (tc_table C)
    (tc_memory C)
    [::]
    [::]
    None
    (tc_refs C)
    (tc_tags_t C).

Definition empty_context :=
  Build_t_context [::] [::] [::] [::] [::] [::] [::] None [::] [::].


Inductive exception_clause_typing : store_record -> t_context -> exception_clause -> Prop :=
| edt_catch : forall s C x l (ts: list value_type),
    List.nth_error (s_tags s) x = Some (Tf ts [::]) ->
    List.nth_error (tc_label C) l = Some ts ->
    exception_clause_typing s C (DE_catch (Mk_tagidx x) l) 
| edt_catch_ref : forall s C x l ts,
    List.nth_error (s_tags s) x = Some (Tf ts [::]) ->
    List.nth_error (tc_label C) l = Some (ts ++ [:: T_ref T_exnref]) ->
    exception_clause_typing s C (DE_catch_ref (Mk_tagidx x) l)
| edt_catch_all : forall s C l,
    List.nth_error (tc_label C) l = Some [::] ->
    exception_clause_typing s C (DE_catch_all l)
| edt_catch_all_ref: forall s C l,
    List.nth_error (tc_label C) l = Some [:: T_ref T_exnref] ->
    exception_clause_typing s C (DE_catch_all_ref l)
  .

  Inductive continuation_clause_typing : store_record -> t_context -> continuation_clause -> list value_type -> Prop :=
  | cdt_clause : forall s C x l t1s' t2s' t2s,
      List.nth_error (s_tags s) x = Some (Tf t1s' t2s') ->
      List.nth_error (tc_label C) l = Some (t1s' ++ [::T_ref (T_contref (Tf t2s' t2s))]) ->
      continuation_clause_typing s C (DC_catch (Mk_tagidx x) l) t2s
  | cdt_switch : forall s C x t2s,
      List.nth_error (s_tags s) x = Some (Tf [::] t2s) ->
      continuation_clause_typing s C (DC_switch (Mk_tagidx x)) t2s
  .


Inductive frame_typing: store_record -> frame -> t_context -> Prop :=
| mk_frame_typing: forall s i tvs C f,
    inst_typing s i C ->
    f.(f_inst) = i ->
    List.Forall2 (fun v t => e_typing s empty_context [:: AI_const v] (Tf [::] [::t]))
                 (f_locs f) tvs ->
    (* map (typeof s) f.(f_locs) = map Some tvs -> *)
    frame_typing s f (upd_local C (tc_local C ++ tvs))
  

with e_typing : store_record -> t_context -> seq administrative_instruction -> function_type -> Prop :=
  (* removed all usages of store_record that do more than just read types *)
| ety_a : forall s C bes tf,
  be_typing C bes tf -> e_typing s C (to_e_list bes) tf
| ety_composition : forall s C es e t1s t2s t3s,
  e_typing s C es (Tf t1s t2s) ->
  e_typing s C [::e] (Tf t2s t3s) ->
  e_typing s C (es ++ [::e]) (Tf t1s t3s)
| ety_weakening : forall s C es ts t1s t2s,
  e_typing s C es (Tf t1s t2s) ->
  e_typing s C es (Tf (ts ++ t1s) (ts ++ t2s))
| ety_trap : forall s C tf,
  e_typing s C [::AI_trap] tf
| ety_local : forall s C n f es ts,
  s_typing s (Some ts) f es ts ->
  length ts = n ->
  e_typing s C [::AI_frame n f es] (Tf [::] ts)
| ety_ref : forall s C a tf cl,
    List.nth_error s.(s_funcs) a = Some cl ->
    cl_type cl = tf -> (* trying cl_type instead of cl_typing *)
    e_typing s C [::AI_ref a] (Tf [::] [::T_ref (T_funcref tf)])

| ety_ref_cont : forall s C k cont tf,
    List.nth_error s.(s_conts) k = Some cont ->
(*    c_typing s (* C *) cont -> *)
    typeof_cont cont = tf ->
    e_typing s C [::AI_ref_cont k] (Tf [::] [::T_ref (T_contref tf)])
| ety_ref_exn : forall s C k i exn , (* Guessing the rule here *) 
    List.nth_error (s_exns s) k = Some exn ->
    e_tag exn = i ->
    e_typing s C [:: AI_ref_exn k i] (Tf [::] [::T_ref T_exnref])
| ety_suspend_desugared : forall s C x vs t1s t2s,
    List.nth_error (s_tags s) x = Some (Tf t1s t2s) ->
    e_typing s C (v_to_e_list vs) (Tf [::] t1s) ->
    e_typing s C [::AI_suspend_desugared vs (Mk_tagidx x)] (Tf [::] t2s)
| ety_switch_desugared : forall s C vs k tf x ts t1s t2s cont,
    List.nth_error (s_tags s) x = Some (Tf [::] ts) ->
    tf = Tf (t1s ++ [::T_ref (T_contref (Tf t2s ts))]) ts ->
    List.nth_error (s_conts s) k = Some cont ->
    typeof_cont cont = tf ->
    e_typing s C (v_to_e_list vs) (Tf [::] t1s) ->
    e_typing s C [::AI_switch_desugared vs k tf (Mk_tagidx x)] (Tf [::] t2s)
| ety_throw_ref_desugared : forall s C vs a i tf exn,
    List.nth_error (s_exns s) a = Some exn ->
    i = e_tag exn ->
    vs = e_fields exn ->
    e_typing s C [::AI_throw_ref_desugared vs a i] tf

| ety_prompt : forall s C hs es ts,
    List.Forall (fun h => continuation_clause_typing s C h ts) hs ->
    e_typing s empty_context es (Tf [::] ts) -> 
    e_typing s C [:: AI_prompt ts hs es] (Tf [::] ts) (* enforcing the type to be same as annotation *)
| ety_handler : forall s C hs es ts,
    List.Forall (fun h => exception_clause_typing s C h) hs ->
    e_typing s C es (Tf [::] ts) -> 
    e_typing s C [:: AI_handler hs es] (Tf [::] ts) 
             
             
| ety_invoke : forall s a C cl tf,
  List.nth_error s.(s_funcs) a = Some cl ->
  cl_type cl = tf -> 
  e_typing s C [::AI_invoke a] tf
| ety_label : forall s C e0s es ts t2s n,
  e_typing s C e0s (Tf ts t2s) ->
  e_typing s (upd_label C ([::ts] ++ tc_label C)) es (Tf [::] t2s) ->
  length ts = n ->
  e_typing s C [::AI_label n e0s es] (Tf [::] t2s)
| ety_call_host : forall s C t1s t2s h vs,
    length vs = length t1s ->
    e_typing s C [::AI_call_host (Tf t1s t2s) h vs] (Tf [::] t2s) 

with s_typing : store_record -> option (seq value_type) -> frame -> seq administrative_instruction -> seq value_type -> Prop :=
| mk_s_typing : forall s f es rs ts C C0,
  frame_typing s f C0 ->
  C = upd_return C0 rs ->
  e_typing s C es (Tf [::] ts) ->
  (rs = Some ts \/ rs = None) ->
  s_typing s rs f es ts

.

Inductive c_typing : store_record -> (* t_context -> *) continuation -> Prop :=
| ct_dagger : forall tf s (* C *), c_typing s (* C *) (Cont_dagger tf)
| ct_hh : forall s (* C *) t1s t2s hh es LI,
    const_list es -> (* else can pick es to be BI_unreachable *)
    e_typing s empty_context es (Tf [::] t1s) -> 
    hfilled No_var hh es LI ->
    e_typing s empty_context LI (Tf [::] t2s) ->
    c_typing s (Cont_hh (Tf t1s t2s) hh)
.


Scheme e_typing_ind' := Induction for e_typing Sort Prop
    with s_typing_ind' := Induction for s_typing Sort Prop.




Definition cl_typing_self (s : store_record) (fc : function_closure) : Prop :=
  cl_typing s fc (cl_type fc).

Lemma cl_typing_unique : forall s cl tf, cl_typing s cl tf -> tf = cl_type cl.
Proof.
  move=> s + tf. case.
  - move => i ts bes t H /=; by inversion H.
  - move => f h H; by inversion H.
Qed.

Definition cl_type_check_single (s:store_record) (f:function_closure):=
  exists tf, cl_typing s f tf.

Definition tabcl_agree (s : store_record) (tcl_index : option nat) : Prop :=
  match tcl_index with
  | None => True
  | Some n => n < size s.(s_funcs)
  end.

Definition tabsize_agree (t: tableinst) : Prop :=
  match table_max_opt t with
  | None => True
  | Some n => tab_size t <= n
  end.

Definition tab_agree (s: store_record) (t: tableinst): Prop :=
  List.Forall (tabcl_agree s) (t.(table_data)) /\
  tabsize_agree t.

Definition mem_agree (m : memory) : Prop :=
  match (mem_max_opt m) with
  | None => True
  | Some n => N.le (mem_size m) n
  end.


Definition glob_sound s g :=
  exists t, e_typing s empty_context [:: AI_basic (BI_const (g_val g))] (Tf [::] [:: t]).
(*  typeof s (g_val g) <> None.   *)

Definition exn_sound s e :=
  exists ts,
    e_typing s empty_context (v_to_e_list (e_fields e)) (Tf [::] ts) /\
      match (e_tag e) with 
        Mk_tagidx x => List.nth_error (s_tags s) x = Some (Tf ts [::])
      end .
        


Definition store_typing (s : store_record) : Prop :=
  match s with
  | Build_store_record fs tclss mss tgs gs exns conts =>
    List.Forall (cl_type_check_single s) fs /\
      List.Forall (tab_agree s) tclss /\
      List.Forall mem_agree mss /\
      List.Forall (glob_sound s) gs /\
      List.Forall (c_typing s) conts /\
      List.Forall (exn_sound s) exns
  end.

Inductive config_typing : store_record -> frame -> seq administrative_instruction -> seq value_type -> Prop :=
| mk_config_typing :
  forall s f es ts,
  store_typing s ->
  s_typing s None f es ts ->
  config_typing s f es ts.




