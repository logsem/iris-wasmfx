From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
From Wasm.iris.helpers.prelude Require Export iris_reduce_properties first_instr.
From Wasm.iris.helpers.reduce_det Require Export reduce_det_invoke_native reduce_det_unop reduce_det_binop reduce_det_drop
        reduce_det_testop reduce_det_relop reduce_det_cvtop reduce_det_select
        reduce_det_block reduce_det_loop reduce_det_return reduce_det_label reduce_det_local
        reduce_det_ref_is_null reduce_det_throw_ref reduce_det_call_reference
        reduce_det_contnew reduce_det_contbind reduce_det_resume
        reduce_det_resume_throw reduce_det_switch reduce_det_if
        reduce_det_local_const reduce_det_label_const reduce_det_handler_const
        reduce_det_prompt_const reduce_det_br reduce_det_tee_local
        reduce_det_trap reduce_det_call_indirect reduce_det_invoke_host
        reduce_det_try_table reduce_det_throw reduce_det_suspend
        reduce_det_set_local reduce_det_set_global reduce_det_load
        reduce_det_store
        
.

Set Bullet Behavior "Strict Subproofs".

Section determ.
  
  Let reducible := @iris.program_logic.language.reducible wasm_lang.

  Let expr := iris.expr.
  Let val := iris.val.
  Let to_val := iris.to_val.

  Ltac sapply x := apply reduce_det_strong_implies_goal; eapply x.

  Lemma reduce_det: forall (ws: store_record) (f: frame) es ws1 f1 es1 ws2 f2 es2,
      reduce ws f es ws1 f1 es1 ->
      reduce ws f es ws2 f2 es2 ->
      reduce_det_goal ws1 f1 es1 ws2 f2 es2 es.
  Proof.
    intros ws f es ws1 f1 es1 ws2 f2 es2 Hred1 Hred2.
    (* we perform an (strong) induction on the length_rec of es, i.e. its number of
     instructions, counting recursively under AI_frames and AI_labels *)
    cut (forall n, length_rec es < n -> reduce_det_goal ws1 f1 es1 ws2 f2 es2 es).
    (* the next few lines simply help put the induction into place *)
    { intro Hn ; apply (Hn (S (length_rec es))) ; lia. }
    intro nnn. generalize dependent es. generalize dependent es1.
    generalize dependent es2. generalize dependent f1. generalize dependent f2.
    generalize dependent f.
    induction nnn ; intros f f2 f1 es2 es1 es Hred1 Hred2 Hlen ; first lia.
    (* begining of the actual reasoning *)
    (* We have hypotheses [ Hred1 : es -> es1 ] and  [ Hred2 : es -> es2 ]. We perform
     a case analysis on Hred1 (induction because of the r_label case) *)
    induction Hred1.
    (* Most cases are dealt with using the [ only_one ] tactic. This tactic assumes that
     hypothesis Hred2 is of the form [ objs -> es2 ] where objs is an explicit list
     that [ only_one ] requires as an argument. It then performs a case analysis on
     Hred2 and exfalsos away as many cases as it can. See 2 commented examples below. 
     Most of the time, it exfalsos away all cases but one, so we are left with 
     reductions [ es -> es1 ] and [ es -> es2 ] being derived by the same rule, 
     so the leftmost disjunct of the conclusion holds. In some cases, 
     the tactic [only_one] will leave us with more than one case, and we will have to
     manually exfalso away some cases *)
    destruct H.
      - by sapply unop_det.
      - by sapply binop_det.
      - by sapply binop_none_det.
      - by sapply testop_i32_det.
      - by sapply testop_i64_det.
      - by sapply relop_det.
      - by sapply cvtop_convert_det.
      - by sapply cvtop_convert_none_det.
      - by sapply cvtop_reinterpret_det.
      - by sapply ref_is_null_det.
      - by sapply ref_is_not_null_det.
      - by sapply throw_ref_null_det.
      - by sapply call_reference_null_det.
      - by sapply contnew_null_det.
      - by sapply contbind_null_det.
      - by sapply resume_null_det.
      - by sapply resume_throw_null_det.
      - by sapply switch_null_det.
      - by sapply prompt_const_det.
      - by sapply handler_const_det.
      - by sapply handler_trap_det.
      - by sapply prompt_trap_det.
      - only_one. inversion H3; destruct vs, esnewest => //; empty_list_no_reduce.
      - only_one. inversion H3; destruct vs, esnewest => //; empty_list_no_reduce.
      - by sapply drop_det.
      - by sapply select_false_det.
      - by sapply select_true_det.
      - by sapply block_det.
      - by sapply loop_det.
      - by sapply if_false_det.
      - by sapply if_true_det.
      - by sapply label_const_det.
      - by sapply label_trap_det.
      - by sapply br_det.
      - by sapply br_if_false_det.
      - by sapply br_if_true_det.
      - by sapply br_if_table_det.
      - by sapply br_if_table_over_det.
      - by sapply local_const_det.
      - by sapply local_trap_det.
      - by sapply return_det.
      - by sapply tee_local_det.
      - by eapply filled_trap_det. 
      - only_one.
        inversion Heqesnew; subst. rewrite H0 in H. inversion H; subst.
        repeat split => //. by left. inversion H4; destruct vs, esnewest => //; empty_list_no_reduce.
      - only_one.
        inversion Heqesnew; subst. rewrite H0 in H. inversion H; subst.
        repeat split => //. by left. inversion H4; destruct vs, esnewest => //; empty_list_no_reduce.
      - by sapply call_indirect_det.
      - by sapply call_indirect_failure1_det.
      - by sapply call_indirect_failure2_det.
      - by sapply call_reference_det.
      - subst; eapply invoke_native_det in Hred2 => //.
        inversion Hred2; subst.
        repeat split => //. by left.
      - subst; eapply invoke_host_det in Hred2 => //.
        inversion Hred2; subst.
        repeat split => //. by left.
      - by sapply try_table_det.
      - by sapply throw_det.
      - by sapply throw_ref_desugar_det. 
      - by sapply throw_ref_det.
      - by sapply throw_ref_ref_det.
      - by sapply contnew_det.
      - by sapply resume_det.
      - by sapply resume_dagger_det.
      - by sapply suspend_desugar_det.
      - by sapply switch_desugar_det.
      - by sapply suspend_det.
      - by sapply switch_det.
      - only_one. inversion H4; destruct vs0, esnewest => //; empty_list_no_reduce.
      - by sapply contbind_det.
      - by sapply contbind_dagger_det.
      - by sapply resume_throw_det.
      - by sapply resume_throw_dagger_det.
      - only_one. inversion Heqesnew; subst. rewrite H in H0; inversion H0; subst; by repeat split => //; left. inversion H4; destruct vs, esnewest => //; empty_list_no_reduce.
      - by sapply set_local_det.
      - only_one. inversion Heqesnew; subst. rewrite H in H0; inversion H0; subst; by repeat split => //; left. inversion H4; destruct vs, esnewest => //; empty_list_no_reduce.
      - by sapply set_global_det.
      - by sapply load_det.
      - by sapply load_failure_det.
      - by sapply load_packed_det.
      - by sapply load_packed_failure_det.
      - by sapply store_det.
      - by sapply store_failure_det.
      - by sapply store_packed_det.
      - by sapply store_packed_failure_det.
      - only_one. inversion Heqesnew; subst. rewrite H2 in H; inversion H; subst.
        rewrite H3 in H0; inversion H0; subst. by repeat split => //; left.
        inversion H4; destruct vs, esnewest => //; empty_list_no_reduce.
    (* the following two cases are the r_grow_memory cases. We do not guarantee
       determinism in these cases, but the second disjunct of the conclusion holds *)
      - remember  [AI_basic (BI_const (VAL_int32 c)); AI_basic BI_grow_memory] as es.
        unfold reduce_det_goal.
        assert ( f = f2 /\ (first_instr es = Some (AI_basic BI_grow_memory, 0))).
        2:{ destruct H3 as (-> & ?).
            repeat split => //.
            right; left. exists 0. done. }
        clear -Hred2 Heqes.
        induction Hred2.
        inversion H.
        all: subst.
        all: try done.
        all: try by do 3 destruct vs => //.
        all: try by do 3 destruct vcs => //.
        move/lfilledP in H.
        inversion H.
        all: try by do 3 destruct vs => //.
        all: try by do 3 destruct bef => //.
        destruct vs.
        + destruct es; first empty_list_no_reduce.
          destruct es.
          * inversion H1; subst.
            exfalso. values_no_reduce.
          * inversion H1; subst.
            destruct es, es'0 => //.
            simpl.
            apply IHHred2 => //.
        + destruct vs.
          * destruct es; first empty_list_no_reduce.
            inversion H1; subst.
            destruct es, es'0 => //.
            clear - Hred2; exfalso.
            lazymatch goal with
            | _ : reduce _ _ ?esn _ _ _ |- _ => remember esn as ves
            end.
            induction Hred2 as [? ? ? ? H02 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ???????????? H02 H03 | ];
              first destruct H02 as [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ??? H01 ]; 
              try (by inversion Heqves);
              try (by destruct vs; try destruct vs; try destruct vs; try destruct vs; inversion Heqves);
              try (by destruct ves; try destruct ves; try destruct ves; try destruct ves; inversion Heqves);
              [ by move/lfilledP in H01; inversion H01; subst;
                try (by do 4 destruct vs => //);
                do 4 destruct bef => //
              | move/lfilledP in H02; inversion H02; subst;
                try (by do 4 destruct vs => //);
                try (by do 4 destruct bef => //) ;
                destruct vs;
                first (
                    do 4 try (destruct es; first by inversion H3; subst; apply values_no_reduce in Hred);
                    inversion H3; subst; 
                    destruct es => //; apply IHHred2 => //
                  )
              ].
            empty_list_no_reduce.
            inversion H3; subst.
            destruct es, es'0 => //.
            inversion H3 => //.
            destruct vs, es => //. empty_list_no_reduce.
          * inversion H1; subst.
            destruct vs, es => //.
      - remember  [AI_basic (BI_const (VAL_int32 c)); AI_basic BI_grow_memory] as es.
        unfold reduce_det_goal.
        assert ( f = f2 /\ (first_instr es = Some (AI_basic BI_grow_memory, 0))).
        2:{ destruct H2 as (-> & ?).
            repeat split => //.
            right; left. exists 0. done. }
        clear -Hred2 Heqes.
        induction Hred2.
        inversion H.
        all: subst.
        all: try done.
        all: try by do 3 destruct vs => //.
        all: try by do 3 destruct vcs => //.
        move/lfilledP in H.
        inversion H.
        all: try by do 3 destruct vs => //.
        all: try by do 3 destruct bef => //.
        destruct vs.
        + destruct es; first empty_list_no_reduce.
          destruct es.
          * inversion H1; subst.
            exfalso. values_no_reduce.
          * inversion H1; subst.
            destruct es, es'0 => //.
            simpl.
            apply IHHred2 => //.
        + destruct vs.
          * destruct es; first empty_list_no_reduce.
            inversion H1; subst.
            destruct es, es'0 => //.
            clear - Hred2; exfalso.
            lazymatch goal with
            | _ : reduce _ _ ?esn _ _ _ |- _ => remember esn as ves
            end.
            induction Hred2 as [? ? ? ? H02 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ???????????? H02 H03 | ];
              first destruct H02 as [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ??? H01 ]; 
              try (by inversion Heqves);
              try (by destruct vs; try destruct vs; try destruct vs; try destruct vs; inversion Heqves);
              try (by destruct ves; try destruct ves; try destruct ves; try destruct ves; inversion Heqves);
              [ by move/lfilledP in H01; inversion H01; subst;
                try (by do 4 destruct vs => //);
                do 4 destruct bef => //
              | move/lfilledP in H02; inversion H02; subst;
                try (by do 4 destruct vs => //);
                try (by do 4 destruct bef => //) ;
                destruct vs;
                first (
                    do 4 try (destruct es; first by inversion H3; subst; apply values_no_reduce in Hred);
                    inversion H3; subst; 
                    destruct es => //; apply IHHred2 => //
                  )
              ].
            empty_list_no_reduce.
            inversion H3; subst.
            destruct es, es'0 => //.
            inversion H3 => //.
            destruct vs, es => //. empty_list_no_reduce.
          * inversion H1; subst.
            destruct vs, es => //.
    - by eapply label_det.
    - by eapply local_det.
  Qed.



  Lemma reduce_in_local s f0 n f es s' f' es':
    reduce s f0 [AI_frame n f es] s' f' es' ->
    (exists f esf, es' = [AI_frame n f esf]) \/ const_list es' \/ es' = [AI_trap].
  Proof.
    intros Hred.
    remember [AI_frame n f es] as esi.
    induction Hred.
    inversion H.
    all: remember Heqesi as Heq; clear HeqHeq Heqesi.
    all: symmetry in Heq.
    all: subst.
    all: try by inversion Heq.
    all: try by do 2 (destruct vs => //).
    all: try by right; left.
    all: try by right; right.
    all: try by do 2 (destruct vcs => //).
    2: by inversion Heq; subst; left; eexists _,_.
    move/lfilledP in H.
    inversion H; subst.
    all: try by do 2 (destruct vs => //).
    all: try by do 2 (destruct bef => //).
    destruct vs.
    { destruct es0; first empty_list_no_reduce.
      inversion H1; subst.
      destruct es0, es'0 => //.
      move/lfilledP in H0; inversion H0; subst.
      repeat rewrite cats0 /=.
      apply IHHred => //. }
    inversion H1; subst.
    done.
  Qed.

  

  Lemma reduce_local_ignores_frame s f0 n f es s' f' es':
    reduce s f0 [AI_frame n f es] s' f' es' ->
    reduce s empty_frame [AI_frame n f es] s' empty_frame es'.
  Proof.
     intros Hred.
    remember [AI_frame n f es] as esi.
    induction Hred.
    inversion H.
    all: remember Heqesi as Heq; clear HeqHeq Heqesi.
    all: symmetry in Heq.
    all: subst.
    all: try by inversion Heq.
    all: try by do 2 (destruct vs => //).
    all: try by right; left.
    all: try by right; right.
    all: try by do 2 (destruct vcs => //).
    all: try by do 2 constructor.
    all: try by constructor.
    move/lfilledP in H.
    inversion H; subst.
    all: try by do 2 (destruct vs => //).
    all: try by do 2 (destruct bef => //).
    destruct vs.
    { destruct es0; first empty_list_no_reduce.
      inversion H1; subst.
      destruct es0, es'0 => //.
      move/lfilledP in H0; inversion H0; subst.
      repeat rewrite cats0 /=.
      apply IHHred => //. }
    inversion H1; subst.
    done.
  Qed. 
    
    
  Lemma reduce_call_ref_state_unchanged s f vs x s' f' es' :
    const_list vs ->
    reduce s f (vs ++ [AI_basic (BI_call_reference x)]) s' f' es' ->
    s = s'.
  Proof.
    intros Hvs Hred.
    remember (S (length vs)) as m.
    assert (length vs < m) as Hm; first lia.
    clear Heqm.
    generalize dependent vs. generalize dependent es'.
    induction m; first lia.
    intros.
    remember (vs ++ [AI_basic (BI_call_reference x)])%SEQ as es.
    induction Hred => //.
    all: try by apply concat_cancel_last in Heqes as [??]; subst; try apply v_to_e_is_const_list.
    all: try by do 2 (destruct vs => //).
    all: try by do 3 (destruct vs => //).
    all: try by do 4 (destruct vs => //).
    all: try by rewrite separate1 -cat_app catA in Heqes; apply concat_cancel_last in Heqes as [??]; subst; try apply const_list_concat; try apply v_to_e_is_const_list.
    move/lfilledP in H; inversion H; subst.
    all: try by apply first_values in H6 as (? & ? & ?).
    destruct vs0.
    { destruct es'0.
      { move/lfilledP in H0; inversion H0; subst.
        rewrite cats0 /= in H5 IHm.
        
        by apply IHHred. }
      destruct (separate_last (a :: es'0)) eqn:Hlast.
      2: by apply separate_last_None in Hlast.
      destruct p.
      apply separate_last_spec in Hlast.
      rewrite Hlast in H5.
      repeat rewrite -cat_app /= in H5.
      rewrite catA in H5.
      apply concat_cancel_last in H5 as [? ->].
      exfalso; values_no_reduce.
      rewrite -H2 in Hvs.
      apply const_list_split in Hvs as [??] => //. }
    destruct es'0.
    2:{  destruct (separate_last (a0 :: es'0)) eqn:Hlast.
      2: by apply separate_last_None in Hlast.
      destruct p.
      apply separate_last_spec in Hlast.
      rewrite Hlast in H5.
      repeat rewrite -cat_app /= in H5.
      rewrite separate1 -cat_app in H5.
      repeat rewrite catA in H5.
      apply concat_cancel_last in H5 as [? ->].
      exfalso; values_no_reduce.
      rewrite -H2 in Hvs.
      repeat apply const_list_split in Hvs as [ Hvs ?] => //. }
    destruct es; first empty_list_no_reduce.
    destruct (separate_last (a0 :: es)) eqn:Hlast.
    2: by apply separate_last_None in Hlast.
    destruct p.
    apply separate_last_spec in Hlast.
    rewrite Hlast in H5 Hred.
    rewrite cats0 in H5.
    rewrite separate1 in H5.
    repeat rewrite -cat_app in H5.
    repeat rewrite catA in H5.
    apply concat_cancel_last in H5 as [<- ->].
    rewrite -cat_app in Hred.
    eapply IHm.
    2: exact Hred.
    apply const_list_split in Hvs as [??] => //.
    repeat rewrite cat_app length_app /= in Hm.
    lia.
  Qed. 
    
    
   Lemma reduce_invoke_state_unchanged s f vs x s' f' es' :
    const_list vs ->
    reduce s f (vs ++ [AI_invoke x]) s' f' es' ->
    s = s'.
  Proof.
    intros Hvs Hred.
    remember (S (length vs)) as m.
    assert (length vs < m) as Hm; first lia.
    clear Heqm.
    generalize dependent vs. generalize dependent es'.
    induction m; first lia.
    intros.
    remember (vs ++ [AI_invoke x])%SEQ as es.
    induction Hred => //.
    all: try by apply concat_cancel_last in Heqes as [??]; subst; try apply v_to_e_is_const_list.
    all: try by do 2 (destruct vs => //).
    all: try by do 3 (destruct vs => //).
    all: try by do 4 (destruct vs => //).
    all: try by rewrite separate1 -cat_app catA in Heqes; apply concat_cancel_last in Heqes as [??]; subst; try apply const_list_concat; try apply v_to_e_is_const_list.
    move/lfilledP in H; inversion H; subst.
    all: try by apply first_values in H6 as (? & ? & ?).
    destruct vs0.
    { destruct es'0.
      { move/lfilledP in H0; inversion H0; subst.
        rewrite cats0 /= in H5 IHm.
        
        by apply IHHred. }
      destruct (separate_last (a :: es'0)) eqn:Hlast.
      2: by apply separate_last_None in Hlast.
      destruct p.
      apply separate_last_spec in Hlast.
      rewrite Hlast in H5.
      repeat rewrite -cat_app /= in H5.
      rewrite catA in H5.
      apply concat_cancel_last in H5 as [? ->].
      exfalso; values_no_reduce.
      rewrite -H2 in Hvs.
      apply const_list_split in Hvs as [??] => //. }
    destruct es'0.
    2:{  destruct (separate_last (a0 :: es'0)) eqn:Hlast.
      2: by apply separate_last_None in Hlast.
      destruct p.
      apply separate_last_spec in Hlast.
      rewrite Hlast in H5.
      repeat rewrite -cat_app /= in H5.
      rewrite separate1 -cat_app in H5.
      repeat rewrite catA in H5.
      apply concat_cancel_last in H5 as [? ->].
      exfalso; values_no_reduce.
      rewrite -H2 in Hvs.
      repeat apply const_list_split in Hvs as [ Hvs ?] => //. }
    destruct es; first empty_list_no_reduce.
    destruct (separate_last (a0 :: es)) eqn:Hlast.
    2: by apply separate_last_None in Hlast.
    destruct p.
    apply separate_last_spec in Hlast.
    rewrite Hlast in H5 Hred.
    rewrite cats0 in H5.
    rewrite separate1 in H5.
    repeat rewrite -cat_app in H5.
    repeat rewrite catA in H5.
    apply concat_cancel_last in H5 as [<- ->].
    rewrite -cat_app in Hred.
    eapply IHm.
    2: exact Hred.
    apply const_list_split in Hvs as [??] => //.
    repeat rewrite cat_app length_app /= in Hm.
    lia.
  Qed. 
  
End determ.

