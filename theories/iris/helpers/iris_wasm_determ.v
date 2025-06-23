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

  Lemma reduce_det: forall (ws: store_record) (f: frame) es ws1 f1 es1 ws2 f2 es2,
      reduce ws f es ws1 f1 es1 ->
      reduce ws f es ws2 f2 es2 ->
      reduce_det_goal ws1 f1 es1 ws2 f2 es2 es.
  Proof.
    intros ws f es ws1 f1 es1 ws2 f2 es2 Hred1 Hred2.
    (* we perform an (strong) induction on the length_rec of es, i.e. its number of
     instructions, counting recursively under AI_locals and AI_labels *)
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
      - by apply unop_det.
      - by apply binop_det.
      - by apply binop_none_det.
      - by apply testop_i32_det.
      - by apply testop_i64_det.
      - by apply relop_det.
      - by apply cvtop_convert_det.
      - by apply cvtop_convert_none_det.
      - by apply cvtop_reinterpret_det.
      - by apply ref_is_null_det.
      - by apply ref_is_not_null_det.
      - by apply throw_ref_null_det.
      - by apply call_reference_null_det.
      - by apply contnew_null_det.
      - by apply contbind_null_det.
      - by apply resume_null_det.
      - by apply resume_throw_null_det.
      - by apply switch_null_det.
      - by apply prompt_const_det.
      - by apply handler_const_det.
      - by apply handler_trap_det.
      - by apply prompt_trap_det.
      - only_one. inversion H3; destruct vs, esnewest => //; empty_list_no_reduce.
      - only_one. inversion H3; destruct vs, esnewest => //; empty_list_no_reduce.
      - by apply drop_det.
      - by apply select_false_det.
      - by apply select_true_det.
      - by eapply block_det.
      - by eapply loop_det.
      - by apply if_false_det.
      - by apply if_true_det.
      - by apply label_const_det.
      - by apply label_trap_det.
      - by eapply br_det.
      - by eapply br_if_false_det.
      - by eapply br_if_true_det.
      - by eapply br_if_table_det.
      - by eapply br_if_table_over_det.
      - by apply local_const_det.
      - by apply local_trap_det.
      - by eapply return_det.
      - by apply tee_local_det.
      - by eapply filled_trap_det. 
      - only_one.
        inversion Heqesnew; subst. rewrite H0 in H. inversion H; subst.
        repeat split => //. by left. inversion H4; destruct vs, esnewest => //; empty_list_no_reduce.
      - only_one.
        inversion Heqesnew; subst. rewrite H0 in H. inversion H; subst.
        repeat split => //. by left. inversion H4; destruct vs, esnewest => //; empty_list_no_reduce.
      - by eapply call_indirect_det.
      - by eapply call_indirect_failure1_det.
      - by eapply call_indirect_failure2_det.
      - by apply call_reference_det.
      - subst; eapply invoke_native_det in Hred2 => //.
        inversion Hred2; subst.
        repeat split => //. by left.
      - subst; eapply invoke_host_det in Hred2 => //.
        inversion Hred2; subst.
        repeat split => //. by left.
      - by eapply try_table_det.
      - by eapply throw_det.
      - by eapply throw_ref_desugar_det. 
      - by eapply throw_ref_det.
      - by eapply throw_ref_ref_det.
      - by eapply contnew_det.
      - by eapply resume_det.
      - by eapply resume_dagger_det.
      - by eapply suspend_desugar_det.
      - by eapply switch_desugar_det.
      - by eapply suspend_det.
      - by eapply switch_det.
      - only_one. inversion H4; destruct vs0, esnewest => //; empty_list_no_reduce.
      - by eapply contbind_det.
      - by eapply contbind_dagger_det.
      - by eapply resume_throw_det.
      - by eapply resume_throw_dagger_det.
      - only_one. inversion Heqesnew; subst. rewrite H in H0; inversion H0; subst; by repeat split => //; left. inversion H4; destruct vs, esnewest => //; empty_list_no_reduce.
      - by eapply set_local_det.
      - only_one. inversion Heqesnew; subst. rewrite H in H0; inversion H0; subst; by repeat split => //; left. inversion H4; destruct vs, esnewest => //; empty_list_no_reduce.
      - by eapply set_global_det.
      - by eapply load_det.
      - by eapply load_failure_det.
      - by eapply load_packed_det.
      - by eapply load_packed_failure_det.
      - by eapply store_det.
      - by eapply store_failure_det.
      - by eapply store_packed_det.
      - by eapply store_packed_failure_det.
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
  
End determ.

