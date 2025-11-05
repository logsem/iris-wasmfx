(** Wasm operational semantics **)
(** The interpreter in the [interpreter] module is an executable version of this operational semantics. **)

From Stdlib Require Import ZArith.BinInt.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
Require Export operations (* host *).

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Host.

Inductive reduce_simple : seq administrative_instruction -> seq administrative_instruction -> Prop :=

(** unop **)
  | rs_unop : forall v op t,
    reduce_simple [::AI_basic (BI_const v); AI_basic (BI_unop t op)] [::AI_basic (BI_const (@app_unop op v))]
                   
(** binop **)
  | rs_binop_success : forall v1 v2 v op t,
    app_binop op v1 v2 = Some v ->
    reduce_simple [::AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_binop t op)] [::AI_basic (BI_const v)]
  | rs_binop_failure : forall v1 v2 op t,
    app_binop op v1 v2 = None ->
    reduce_simple [::AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_binop t op)] [::AI_trap]
                  
  (** testops **)
  | rs_testop_i32 :
    forall c testop,
    reduce_simple [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_testop T_i32 testop)] [::AI_basic (BI_const (VAL_int32 (wasm_bool (@app_testop_i i32t testop c))))]
  | rs_testop_i64 :
    forall c testop,
    reduce_simple [::AI_basic (BI_const (VAL_int64 c)); AI_basic (BI_testop T_i64 testop)] [::AI_basic (BI_const (VAL_int32 (wasm_bool (@app_testop_i i64t testop c))))]

  (** relops **)
  | rs_relop: forall v1 v2 t op,
    reduce_simple [::AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_relop t op)] [::AI_basic (BI_const (VAL_int32 (wasm_bool (app_relop op v1 v2))))]
                    
  (** convert and reinterpret **)
  | rs_convert_success :
    forall t1 t2 v v' sx,
    types_num_agree t1 v ->
    cvt t2 sx v = Some v' ->
    reduce_simple [::AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_convert t1 sx)] [::AI_basic (BI_const v')]
  | rs_convert_failure :
    forall t1 t2 v sx,
    types_num_agree t1 v ->
    cvt t2 sx v = None ->
    reduce_simple [::AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_convert t1 sx)] [::AI_trap]
  | rs_reinterpret :
    forall t1 t2 v,
    types_num_agree t1 v ->
    reduce_simple [::AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_reinterpret t1 None)] [::AI_basic (BI_const (wasm_deserialise (bits v) t2))]

 (** reference operations **)
  | rs_ref_is_null_true:
    forall t,
    reduce_simple [:: AI_const (VAL_ref (VAL_ref_null t)); AI_basic BI_ref_is_null] [::AI_const (VAL_num (VAL_int32 Wasm_int.Int32.one))]
  (* This formulation might cause some difficulty in the proofs, but it's the most faithful to the spec *)
  | rs_ref_is_null_false:
    forall ref,
    (forall t, ref <> VAL_ref_null t) ->
    reduce_simple [:: AI_const (VAL_ref ref); AI_basic BI_ref_is_null] [::AI_const (VAL_num (VAL_int32 Wasm_int.Int32.zero))]

(** Exception handling *)
| rs_throw_ref_null:
  forall tf, reduce_simple [:: AI_basic (BI_ref_null tf) ; AI_basic BI_throw_ref] [::AI_trap]
                  
(** Effect handler operations (rules not using the store of frame) **)

| rs_call_reference_null :
  forall t i,
    reduce_simple [:: AI_basic (BI_ref_null t) ; AI_basic (BI_call_reference i)] [:: AI_trap]

| rs_contnew_failure :
  forall rt i,
    reduce_simple [:: AI_basic (BI_ref_null rt); AI_basic (BI_contnew i)] [::AI_trap]
| rs_contbind_failure :
  forall rt i i',
    reduce_simple [::AI_basic (BI_ref_null rt); AI_basic (BI_contbind i i')] [::AI_trap]
| rs_resume_failure :
  forall rt i hs,
    reduce_simple [::AI_basic (BI_ref_null rt); AI_basic (BI_resume i hs)] [::AI_trap]
| rs_resume_throw_failure:
  forall rt i j hs,
    reduce_simple [::AI_basic (BI_ref_null rt); AI_basic (BI_resume_throw i j hs)] [::AI_trap]
| rs_switch_failure :
  forall rt tf x,
    reduce_simple [:: AI_basic (BI_ref_null rt); AI_basic (BI_switch tf x)] [::AI_trap]
| rs_prompt_const :
  forall ts hs vs,
    const_list vs ->
    reduce_simple [::AI_prompt ts hs vs] vs
| rs_handler_const :
  forall hs vs,
    const_list vs ->
    reduce_simple [::AI_handler hs vs] vs
| rs_handler_trap :
  forall hs,
    reduce_simple [::AI_handler hs [::AI_trap]] [:: AI_trap]
| rs_prompt_trap :
  forall ts hs,
    reduce_simple [::AI_prompt ts hs [::AI_trap]] [::AI_trap]
(* | rs_handle_suspend :
  forall x hs hh LI,
    List.Forall (fun '(H_on y _) => x <> y) hs ->
    hfilled x hh [:: AI_basic (BI_suspend x)] LI ->
    reduce_simple [::AI_handler hs LI] [::AI_trap] *)


  (** control-flow operations **)
  | rs_unreachable :
    reduce_simple [::AI_basic BI_unreachable] [::AI_trap]
  | rs_nop :
    reduce_simple [::AI_basic BI_nop] [::]
  | rs_drop :
    forall v,
    reduce_simple [::AI_const v; AI_basic BI_drop] [::]
  | rs_select_false :
    forall n v1 v2,
    n = Wasm_int.int_zero i32m ->
    reduce_simple [::AI_const v1; AI_const v2; AI_basic (BI_const (VAL_int32 n)); AI_basic BI_select] [::AI_const v2]
  | rs_select_true :
    forall n v1 v2,
    n <> Wasm_int.int_zero i32m ->
    reduce_simple [::AI_const v1; AI_const v2; AI_basic (BI_const (VAL_int32 n)); AI_basic BI_select] [::AI_const v1]
  | rs_block :
      forall vs es n m t1s t2s,
        const_list vs ->
        length vs = n ->
        length t1s = n ->
        length t2s = m ->
        reduce_simple (vs ++ [::AI_basic (BI_block (Tf t1s t2s) es)]) [::AI_label m [::] (vs ++ to_e_list es)]
  | rs_loop :
      forall vs es n m t1s t2s,
        const_list vs ->
        length vs = n ->
        length t1s = n ->
        length t2s = m ->
        reduce_simple (vs ++ [::AI_basic (BI_loop (Tf t1s t2s) es)]) [::AI_label n [::AI_basic (BI_loop (Tf t1s t2s) es)] (vs ++ to_e_list es)]
  | rs_if_false :
      forall n tf e1s e2s,
        n = Wasm_int.int_zero i32m ->
        reduce_simple ([::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_if tf e1s e2s)]) [::AI_basic (BI_block tf e2s)]
  | rs_if_true :
      forall n tf e1s e2s,
        n <> Wasm_int.int_zero i32m ->
        reduce_simple ([::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_if tf e1s e2s)]) [::AI_basic (BI_block tf e1s)]

  | rs_label_const :
      forall n es vs,
        const_list vs ->
        reduce_simple [::AI_label n es vs] vs
  | rs_label_trap :
      forall n es,
        reduce_simple [::AI_label n es [::AI_trap]] [::AI_trap]
  | rs_br :
      forall n vs es i LI lh,
        const_list vs ->
        length vs = n ->
        lfilled i lh (vs ++ [::AI_basic (BI_br i)]) LI ->
        reduce_simple [::AI_label n es LI] (vs ++ es)
  | rs_br_if_false :
      forall n i,
        n = Wasm_int.int_zero i32m ->
        reduce_simple [::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_br_if i)] [::]
  | rs_br_if_true :
      forall n i,
        n <> Wasm_int.int_zero i32m ->
        reduce_simple [::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_br_if i)] [::AI_basic (BI_br i)]
  | rs_br_table : (* ??? *)
      forall iss c i j,
        length iss > Wasm_int.nat_of_uint i32m c ->
        List.nth_error iss (Wasm_int.nat_of_uint i32m c) = Some j ->
        reduce_simple [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_br_table iss i)] [::AI_basic (BI_br j)]
  | rs_br_table_length :
      forall iss c i,
        length iss <= (Wasm_int.nat_of_uint i32m c) ->
        reduce_simple [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_br_table iss i)] [::AI_basic (BI_br i)]
  | rs_local_const :
      forall es n f,
        const_list es ->
        length es = n ->
        reduce_simple [::AI_frame n f es] es
  | rs_local_trap :
      forall n f,
        reduce_simple [::AI_frame n f [::AI_trap]] [::AI_trap]
  | rs_return : (* ??? *)
      forall n i vs es lh f,
        const_list vs ->
        length vs = n ->
        lfilled i lh (vs ++ [::AI_basic BI_return]) es ->
        reduce_simple [::AI_frame n f es] vs
                      
  | rs_tee_local :
      forall i v,
        is_const v ->
        reduce_simple [::v; AI_basic (BI_tee_local i)] [::v; v; AI_basic (BI_set_local i)]
  | rs_trap :
      forall es lh,
        es <> [::AI_trap] ->
        lfilled 0 lh [::AI_trap] es ->
        reduce_simple es [::AI_trap]
  .

Inductive reduce : store_record -> frame -> list administrative_instruction ->
                   store_record -> frame -> list administrative_instruction -> Prop :=
  | r_simple :
      forall e e' s f,
        reduce_simple e e' ->
        reduce s f e s f e'

| r_ref_func:
    forall s f addr x,
      List.nth_error f.(f_inst).(inst_funcs) x = Some addr ->
      reduce s f [::AI_basic (BI_ref_func x)] s f [::AI_ref addr]

  (** calling operations **)
  | r_call :
      forall s f i a,
        List.nth_error f.(f_inst).(inst_funcs) i = Some a ->
        reduce s f [::AI_basic (BI_call i)] s f [::AI_invoke a]
  | r_call_indirect_success :
      forall s f i a cl c ,
        stab_addr s f (Wasm_int.nat_of_uint i32m c) = Some a ->
        List.nth_error s.(s_funcs) a = Some cl ->
        stypes f.(f_inst) i = Some (cl_type cl) ->
        reduce s f [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i)] s f [::AI_invoke a]
  | r_call_indirect_failure1 :
      forall s f i a cl c,
        stab_addr s f (Wasm_int.nat_of_uint i32m c) = Some a ->
        List.nth_error s.(s_funcs) a = Some cl ->
        stypes f.(f_inst) i <> Some (cl_type cl) ->
        reduce s f [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i)] s f [::AI_trap]
  | r_call_indirect_failure2 :
      forall s f i c,
        stab_addr s f (Wasm_int.nat_of_uint i32m c) = None ->
        reduce s f [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i)] s f [::AI_trap]

| r_call_reference :
  (*  forall s f x i vcs ves t1s t2s n m f' cl i0 ts es zs, *)
  forall x cl i s f,
    List.nth_error s.(s_funcs) x = Some cl ->
    stypes f.(f_inst) i = Some (cl_type cl) ->
(*    cl = FC_func_native i (Tf t1s t2s) ts es ->
    ves = v_to_e_list vcs ->
    length vcs = n ->
    length t1s = n ->
    length t2s = m ->
    default_vals ts = Some zs ->
    f'.(f_inst) = i ->
    f'.(f_locs) = vcs ++ zs ->  *)
    reduce s f ((* ves ++ *) [:: AI_ref x; AI_basic (BI_call_reference i)]) s f [:: AI_invoke x] (* [:: AI_frame m f' [::AI_basic (BI_block (Tf [::] t2s) es)]] *)
| r_invoke_native :
  forall a cl t1s t2s ts es ves vcs n m k zs s f f' i,
    List.nth_error s.(s_funcs) a = Some cl ->
    cl = FC_func_native i (Tf t1s t2s) ts es ->
    ves = v_to_e_list vcs ->
    length vcs = n ->
    length ts = k ->
    length t1s = n ->
    length t2s = m ->
    default_vals ts = zs ->
    f'.(f_inst) = i ->
    f'.(f_locs) = vcs ++ zs ->
    reduce s f (ves ++ [::AI_invoke a]) s f [::AI_frame m f' [::AI_basic (BI_block (Tf [::] t2s) es)]]
| r_invoke_host :
  forall a cl h t1s t2s ves vcs m n s f,
    List.nth_error s.(s_funcs) a = Some cl ->
    cl = FC_func_host (Tf t1s t2s) h ->
    ves = v_to_e_list vcs ->
    length vcs = n ->
    length t1s = n ->
    length t2s = m ->
    reduce s f (ves ++ [::AI_invoke a]) s f [:: AI_call_host (Tf t1s t2s) h vcs]

(** Exception handling *)
| r_try_table :
  forall s f vs t1s t2s cs csd es n i,
    stypes (f_inst f) i = Some (Tf t1s t2s) ->
    n = length t2s ->
    const_list vs -> 
    length vs = length t1s ->
    map (desugar_exception_clause (f_inst f)) cs = map Some csd ->
(*    List.Forall (clause_addr_defined (f_inst f)) cs -> *)
    reduce s f (vs ++ [::AI_basic (BI_try_table i cs es)])
      s f [::AI_handler csd [:: AI_label n [::] (vs ++ to_e_list es)]]
   
| r_throw: forall s f ves vcs x s' a ts,
    List.nth_error f.(f_inst).(inst_tags) x = Some a ->
    List.nth_error s.(s_tags) a = Some (Tf ts [::]) ->
    ves = v_to_e_list vcs ->
    length ves = length ts ->
    s' = add_exn s {| e_tag := Mk_tagidx a ; e_fields := vcs |} ->
    reduce s f (ves ++ [:: AI_basic (BI_throw x)]) s' f [::AI_ref_exn (length s.(s_exns)) (Mk_tagidx a) ; AI_basic (BI_throw_ref)]
| r_throw_ref_desugar s f a i exn vs:
  List.nth_error (s_exns s) a = Some exn ->
  i = e_tag exn ->
  vs = e_fields exn ->
  reduce s f [:: AI_ref_exn a i; AI_basic BI_throw_ref] s f [:: AI_throw_ref_desugared vs a i]
| r_throw_ref: forall s f vs a i hh l hs LI,
    hfilled (Var_handler i) hh [:: AI_throw_ref_desugared vs a i] LI ->
    firstx_exception hs i = Clause_label l ->
    reduce s f [:: AI_handler hs LI ] s f (v_to_e_list vs ++ [:: AI_basic (BI_br l)])
| r_throw_ref_ref: forall s f vs a i hh l hs LI,
    hfilled (Var_handler i) hh [:: AI_throw_ref_desugared vs a i] LI ->
    firstx_exception hs i = Clause_label_ref l ->
    reduce s f [:: AI_handler hs LI ] s f (v_to_e_list vs ++ [:: AI_ref_exn a i; AI_basic (BI_br l)])

           
(** Effect handler operations **)

| r_contnew :
  forall s f x i tf hh,
    stypes (f_inst f) i = Some tf ->
    hh = HH_base [::] [::AI_ref x; AI_basic (BI_call_reference (Type_explicit tf))] ->
    reduce s f [:: AI_ref x; AI_basic (BI_contnew i)] (new_cont s (Cont_hh tf hh)) f [:: AI_ref_cont (length (s_conts s))]
 | r_resume :
   forall s f k hh vs i hs hsd t1s t2s LI,
     const_list vs ->
     stypes (f_inst f) i = Some (Tf t1s t2s) ->
     length vs = length t1s ->
     List.nth_error (s_conts s) k = Some (Cont_hh (Tf t1s t2s) hh) ->
     hfilled No_var hh vs LI ->
     map (desugar_continuation_clause (f_inst f)) hs = map Some hsd ->
     reduce s f (vs ++ [:: AI_ref_cont k; AI_basic (BI_resume i hs)]) (upd_s_cont s k (Cont_dagger (Tf t1s t2s))) f [:: AI_prompt t2s hsd LI]
| r_resume_failure :
  forall s f k i hs tf,
    List.nth_error (s_conts s) k = Some (Cont_dagger tf) ->
    reduce s f [:: AI_ref_cont k; AI_basic (BI_resume i hs)] s f [::AI_trap]
| r_suspend_desugar :
  forall s f x a t1s t2s vs,
    List.nth_error f.(f_inst).(inst_tags) x = Some a ->
    List.nth_error s.(s_tags) a = Some (Tf t1s t2s) ->
    length vs = length t1s ->
    reduce s f (v_to_e_list vs ++ [:: AI_basic (BI_suspend (Mk_tagident x))]) s f [:: AI_suspend_desugared vs (Mk_tagidx a)]
| r_switch_desugar :
  forall s f i x a tf tf' k cont t1s t2s vs,
    stypes (f_inst f) i = Some tf ->
    List.nth_error f.(f_inst).(inst_tags) x = Some a ->
    List.nth_error s.(s_tags) a = Some tf' ->
    List.nth_error s.(s_conts) k = Some cont ->
    typeof_cont cont = Tf t1s t2s ->
    S (length vs) = length t1s ->
    reduce s f (v_to_e_list vs ++ [:: AI_ref_cont k; AI_basic (BI_switch i (Mk_tagident x))]) s f [:: AI_switch_desugared vs k tf (Mk_tagidx a)]
| r_suspend :
  forall s f hs ts hh vs x a l t1s t2s LI,
    x = Mk_tagidx a ->
    List.nth_error (s_tags s) a = Some (Tf t1s t2s) ->
    firstx_continuation_suspend hs x = Some l ->
    hfilled (Var_prompt_suspend x) hh [:: AI_suspend_desugared vs x] LI ->
    reduce s f [:: AI_prompt ts hs LI ] (new_cont s (Cont_hh (Tf t2s ts) hh)) f (v_to_e_list vs ++ [:: AI_ref_cont (length (s_conts s)); AI_basic (BI_br l)])
| r_switch :
  forall s f ts hs LI tf'' tf' hh LI' x tf t1s t2s k vs hh',
    firstx_continuation_switch hs x = true ->
    tf = Tf (t1s ++ [:: T_ref (T_contref tf')]) t2s ->
    List.nth_error (s_conts s) k = Some (Cont_hh tf'' hh') ->
    hfilled (Var_prompt_switch x) hh [::AI_switch_desugared vs k tf x] LI ->
    hfilled No_var hh' (v_to_e_list vs ++ [:: AI_ref_cont (length (s_conts s))]) LI' ->
    reduce s f [:: AI_prompt ts hs LI ] (new_cont (upd_s_cont s k (Cont_dagger tf'')) (Cont_hh tf' hh)) f [:: AI_prompt ts hs LI']
| r_switch_failure :
  forall s f k tf x tf' vs,
    List.nth_error (s_conts s) k = Some (Cont_dagger tf') ->
    reduce s f [:: AI_switch_desugared vs k tf x] s f [:: AI_trap]
| r_contbind :
  forall s f k hh vs i i' ts t1s t2s,
    const_list vs ->
    stypes (f_inst f) i = Some (Tf (ts ++ t1s) t2s) ->
    stypes (f_inst f) i' = Some (Tf t1s t2s) ->
    length ts = length vs ->
    List.nth_error (s_conts s) k = Some (Cont_hh (Tf (ts ++ t1s) t2s) hh) ->
    reduce s f (vs ++ [:: AI_ref_cont k; AI_basic (BI_contbind i i')]) (new_cont (upd_s_cont s k (Cont_dagger (Tf (ts ++ t1s) t2s))) (Cont_hh (Tf t1s t2s) (hhplug vs hh))) f [:: AI_ref_cont (length (s_conts s))]
| r_contbind_failure :
  forall s f k i i' tf,
  List.nth_error (s_conts s) k = Some (Cont_dagger tf) ->
  reduce s f [:: AI_ref_cont k; AI_basic (BI_contbind i i')] s f [::AI_trap]
| r_resume_throw :
  forall s s' s'' f k hh ves vcs i t1s t2s x a hs hsd LI ts,
    List.nth_error f.(f_inst).(inst_tags) x = Some a ->
    List.nth_error (s_tags s) a = Some (Tf ts [::]) ->
     ves = v_to_e_list vcs ->
    length ves = length ts ->
    s' = add_exn s {| e_tag := Mk_tagidx a ; e_fields := vcs |} ->
    s'' = upd_s_cont s' k (Cont_dagger (Tf t1s t2s)) ->
    List.nth_error (s_conts s) k = Some (Cont_hh (Tf t1s t2s) hh) ->
    stypes (f_inst f) i = Some (Tf t1s t2s) ->
    map (desugar_continuation_clause (f_inst f)) hs = map Some hsd ->
    hfilled No_var hh ([:: AI_ref_exn (List.length (s_exns s)) (Mk_tagidx a) ; AI_basic BI_throw_ref]) LI -> 
    reduce s f (ves ++ [:: AI_ref_cont k; AI_basic (BI_resume_throw i x hs)]) s'' f [:: AI_prompt t2s hsd LI]
| r_resume_throw_failure :
  forall s f k i x hs tf,
    List.nth_error (s_conts s) k = Some (Cont_dagger tf) ->
    reduce s f [::AI_ref_cont k; AI_basic (BI_resume_throw i x hs)] s f [::AI_trap]
            
    
               



  (** get, set, load, and store operations **)
  | r_get_local :
      forall f v j s,
        List.nth_error f.(f_locs) j = Some v ->
        reduce s f [::AI_basic (BI_get_local j)] s f [:: AI_const v]
  | r_set_local :
      forall f f' i v s vd,
        f'.(f_inst) = f.(f_inst) ->
        i < length f.(f_locs) ->
        f'.(f_locs) = set_nth vd f.(f_locs) i v ->
        reduce s f [::AI_const v; AI_basic (BI_set_local i)] s f' [::]
  | r_get_global :
      forall s f i v,
        sglob_val s f.(f_inst) i = Some v ->
        reduce s f [::AI_basic (BI_get_global i)] s f [::AI_basic (BI_const v)]
  | r_set_global :
      forall s f i v s',
        supdate_glob s f.(f_inst) i v = Some s' ->
        reduce s f [::AI_basic (BI_const v); AI_basic (BI_set_global i)] s' f [::]
  | r_load_success :
    forall s i f t bs k a off m,
      smem_ind s f.(f_inst) = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      load m (Wasm_int.N_of_uint i32m k) off (length_tnum t) = Some bs ->
      reduce s f [::AI_basic (BI_const (VAL_int32 k)); AI_basic (BI_load t None a off)] s f [::AI_basic (BI_const (wasm_deserialise bs t))]
  | r_load_failure :
    forall s i f t k a off m,
      smem_ind s f.(f_inst) = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      load m (Wasm_int.N_of_uint i32m k) off (length_tnum t) = None ->
      reduce s f [::AI_basic (BI_const (VAL_int32 k)); AI_basic (BI_load t None a off)] s f [::AI_trap]
  | r_load_packed_success :
    forall s i f t tp k a off m bs sx,
      smem_ind s f.(f_inst) = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      load_packed sx m (Wasm_int.N_of_uint i32m k) off (length_tp tp) (length_tnum t) = Some bs ->
      reduce s f [::AI_basic (BI_const (VAL_int32 k)); AI_basic (BI_load t (Some (tp, sx)) a off)] s f [::AI_basic (BI_const (wasm_deserialise bs t))]
  | r_load_packed_failure :
    forall s i f t tp k a off m sx,
      smem_ind s f.(f_inst) = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      load_packed sx m (Wasm_int.N_of_uint i32m k) off (length_tp tp) (length_tnum t) = None ->
      reduce s f [::AI_basic (BI_const (VAL_int32 k)); AI_basic (BI_load t (Some (tp, sx)) a off)] s f [::AI_trap]
  | r_store_success :
    forall t v s i f mem' k a off m,
      types_num_agree t v ->
      smem_ind s f.(f_inst) = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      store m (Wasm_int.N_of_uint i32m k) off (bits v) (length_tnum t) = Some mem' ->
      reduce s f [::AI_basic (BI_const (VAL_int32 k)); AI_basic (BI_const v); AI_basic (BI_store t None a off)] (upd_s_mem s (update_list_at s.(s_mems) i mem')) f [::]
  | r_store_failure :
    forall t v s i f m k off a,
      types_num_agree t v ->
      smem_ind s f.(f_inst) = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      store m (Wasm_int.N_of_uint i32m k) off (bits v) (length_tnum t) = None ->
      reduce s f [::AI_basic (BI_const (VAL_int32 k)); AI_basic (BI_const v); AI_basic (BI_store t None a off)] s f [::AI_trap]
  | r_store_packed_success :
    forall t v s i f m k off a mem' tp,
      types_num_agree t v ->
      smem_ind s f.(f_inst) = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      store_packed m (Wasm_int.N_of_uint i32m k) off (bits v) (length_tp tp) = Some mem' ->
      reduce s f [::AI_basic (BI_const (VAL_int32 k)); AI_basic (BI_const v); AI_basic (BI_store t (Some tp) a off)] (upd_s_mem s (update_list_at s.(s_mems) i mem')) f [::]
  | r_store_packed_failure :
    forall t v s i f m k off a tp,
      types_num_agree t v ->
      smem_ind s f.(f_inst) = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      store_packed m (Wasm_int.N_of_uint i32m k) off (bits v) (length_tp tp) = None ->
      reduce s f [::AI_basic (BI_const (VAL_int32 k)); AI_basic (BI_const v); AI_basic (BI_store t (Some tp) a off)] s f [::AI_trap]

  (** memory **)
  | r_current_memory :
      forall i f m n s,
        smem_ind s f.(f_inst) = Some i ->
        List.nth_error s.(s_mems) i = Some m ->
        mem_size m = n ->
        reduce s f [::AI_basic (BI_current_memory)] s f [::AI_basic (BI_const (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat n))))]
  | r_grow_memory_success :
    forall s i f m n mem' c,
      smem_ind s f.(f_inst) = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      mem_size m = n ->
      mem_grow m (Wasm_int.N_of_uint i32m c) = Some mem' ->
      reduce s f [::AI_basic (BI_const (VAL_int32 c)); AI_basic BI_grow_memory] (upd_s_mem s (update_list_at s.(s_mems) i mem')) f [::AI_basic (BI_const (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat n))))]
  | r_grow_memory_failure :
      forall i f m n s c,
        smem_ind s f.(f_inst) = Some i ->
        List.nth_error s.(s_mems) i = Some m ->
        mem_size m = n ->
        reduce s f [::AI_basic (BI_const (VAL_int32 c)); AI_basic BI_grow_memory] s f [::AI_basic (BI_const (VAL_int32 int32_minus_one))]

  (** label and local **)
  | r_label :
      forall s f es les s' f' es' les' k lh,
        reduce s f es s' f' es' ->
        lfilled k lh es les ->
        lfilled k lh es' les' ->
        reduce s f les s' f' les'
  | r_local :
      forall s f es s' f' es' n f0,
        reduce s f es s' f' es' ->
        reduce s f0 [::AI_frame n f es] s' f0 [::AI_frame n f' es']
  .

Definition reduce_tuple s_f_es s'_f'_es' : Prop :=
  let '(s, f, es) := s_f_es in
  let '(s', f', es') := s'_f'_es' in
  reduce s f es s' f' es'.
      
Definition reduce_trans :
    store_record * frame * seq administrative_instruction ->
    store_record * frame * seq administrative_instruction -> Prop :=
  Relations.Relation_Operators.clos_refl_trans _ reduce_tuple.

End Host.

