From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
From Wasm.iris.language.iris Require Export iris.
From Wasm Require Export stdpp_aux.
Require Export iris_reduce_properties iris_split_reduce.

Set Bullet Behavior "Strict Subproofs".

Ltac first_not_const Hconst :=
  unfold const_list, forallb in Hconst ;
  subst ; simpl in Hconst ;
  repeat rewrite andb_false_r in Hconst ;
  false_assumption.


Section reduction_core.

  Let reducible := @iris.program_logic.language.reducible wasm_lang.
  
  Let expr := iris.expr.
  Let val := iris.val.
  Let to_val := iris.to_val.


  Lemma reduction_core bef0 es0 aft0 bef1 es1 aft1 es0' es1' s f s' f' s0 f0 :
    reduce s f es0 s0 f0 es0' ->
    reduce s f es1 s' f' es1' ->
    const_list bef0 ->
    const_list bef1 ->
    bef0 ++ es0 ++ aft0 = bef1 ++ es1 ++ aft1 ->
    (exists core bc0 ac0 bc1 ac1 core',
        const_list bc0 /\
          const_list bc1 /\
          es0 = bc0 ++ core ++ ac0 /\
          es1 = bc1 ++ core ++ ac1 /\
          bef0 ++ bc0 = bef1 ++ bc1 /\
          ac0 ++ aft0 = ac1 ++ aft1 /\
          reduce s f core s' f' core' /\
          bc1 ++ core' ++ ac1 = es1') \/
      exists lh0 lh1, lfilled 0 lh0 [AI_trap] es0 /\ lfilled 0 lh1 [AI_trap] es1 /\
                   (s,f) = (s', f').
  Proof.
    intros Hred0 Hred1 Hbef0 Hbef1 Heq.
    cut (forall nnnn, length es1 < nnnn ->
                 (∃ core bc0 ac0 bc1 ac1 core' : seq.seq administrative_instruction,
                     const_list bc0
                     ∧ const_list bc1
                     ∧ es0 = bc0 ++ core ++ ac0
                     ∧ es1 = bc1 ++ core ++ ac1
                     ∧ bef0 ++ bc0 = bef1 ++ bc1
                     ∧ ac0 ++ aft0 = ac1 ++ aft1
                     ∧ reduce s f core s' f' core' ∧ bc1 ++ core' ++ ac1 = es1')
                 ∨ (∃ lh0 lh1 : lholed, lfilled 0 lh0 [AI_trap] es0 ∧ lfilled 0 lh1 [AI_trap] es1 /\ (s,f) = (s',f'))).
    { intro Hn ; eapply (Hn (S (length es1))) ; lia. }
    intro nnnn.
    generalize dependent es1.
    generalize dependent es1'.
    generalize dependent es0.
    generalize dependent es0'.
    generalize dependent bef1.
    generalize dependent aft1.
    induction nnnn.
    intros ; lia.
    intros aft1 bef1 Hbef1 es0' es0 Hred0 es1' es1 Hred1 Heq Hlen.
    edestruct first_non_value_reduce as (vs0 & e0 & afte0 & Hvs0 & He0 & Heq0) ;
      try exact Hred0.
    rewrite Heq0 in Heq.
    induction Hred1.
    inversion H.
    all: try by left; subst;
      rewrite separate1 in Heq; do 3 rewrite app_assoc in Heq;
      do 2 rewrite -app_assoc in Heq;
      apply first_values in Heq as (<- & -> & <-); try done;
      try (by destruct He0 as [He0 | ->] ; last done;
           destruct e0 => //; destruct b => //);
      try (by apply const_list_concat; repeat rewrite /= cosnt_const);
      eexists _, vs0, afte0, [], [], _;
      repeat split; try done; try (by rewrite app_nil_r); try (by econstructor).
    all: subst.
    11: destruct ref.
    33: destruct v => //; first destruct b => //. 
    all: try lazymatch goal with
             (*    | _ : [_;_] = _ |- _ =>  *)
             | _ : _ = _ ++ [_;_] ++ _ |- _ =>
               left; subst; rewrite separate1 in Heq;
               do 3 rewrite app_assoc in Heq;
               rewrite -app_assoc in Heq; rewrite -app_assoc in Heq;
               symmetry in Heq;
               rewrite separate1 in Heq; do 2 rewrite app_assoc in Heq;
               rewrite -app_assoc in Heq;
               apply first_values in Heq as (Hbefs & <- & ->) ; try done;
               try (by destruct He0 as [He0 | ->] ; last done;
                    destruct e0 => //; destruct b => //);
               try (by apply const_list_concat; repeat rewrite /= const_const);
               separate_last vs0;
               last exfalso;
               first by rewrite app_assoc in Hbefs;
               apply concat_cancel_last in Hbefs as [-> <-];
               apply const_list_split in Hvs0 as [??];
               eexists _, l, afte0, [], [], _;
               repeat split ; try done; try (by rewrite app_nil_r); try (by econstructor);
               try rewrite -app_assoc //
           end .
     all: try lazymatch goal with
              (*   | _ : [_;_;_] = _ |- _ =>  *)
              | _ : _ = _ ++ [_;_;_] ++ _ |- _ =>
               left; subst; rewrite separate1 in Heq;
               do 3 rewrite app_assoc in Heq;
               rewrite -app_assoc in Heq; rewrite -app_assoc in Heq;
               symmetry in Heq;
               rewrite separate2 in Heq; do 2 rewrite app_assoc in Heq;
               rewrite -app_assoc in Heq;
               apply first_values in Heq as (Hbefs & <- & ->) ; try done;
               try (by destruct He0 as [He0 | ->] ; last done;
                    destruct e0 => //; destruct b => //);
               try (by apply const_list_concat; repeat rewrite /= const_const);
               separate_last vs0;
               last exfalso;
               first (
                   rewrite app_assoc separate1 app_assoc in Hbefs;
                   apply concat_cancel_last in Hbefs as [Hbefs <-];
                   separate_last l;
                   last exfalso;
                   first by rewrite app_assoc in Hbefs;
                   apply concat_cancel_last in Hbefs as [-> <-];
                   apply const_list_split in Hvs0 as [Hvs0 ?];
                   apply const_list_split in Hvs0 as [Hvs0 ?];
                   eexists _, l0, afte0, [], [], _;
                   repeat split ; try done; try (by rewrite app_nil_r); try (by econstructor);
               try rewrite -app_assoc -app_assoc //)
            end .

     all: try lazymatch goal with
              (*            | _ : [_;_;_;_] = _ |- _ =>  *)
              | _ : _ = _ ++ [_;_;_;_] ++ _ |- _ =>
               left; subst; rewrite separate1 in Heq;
               do 3 rewrite app_assoc in Heq;
               rewrite -app_assoc in Heq; rewrite -app_assoc in Heq;
               symmetry in Heq;
               rewrite separate3 in Heq; do 2 rewrite app_assoc in Heq;
               rewrite -app_assoc in Heq;
               apply first_values in Heq as (Hbefs & <- & ->) ; try done;
               try (by destruct He0 as [He0 | ->] ; last done;
                    destruct e0 => //; destruct b => //);
               try (by apply const_list_concat; repeat rewrite /= const_const);
               separate_last vs0;
               last exfalso;
               first (
                   rewrite app_assoc separate2 app_assoc in Hbefs;
                   apply concat_cancel_last in Hbefs as [Hbefs <-];
                   separate_last l;
                   last exfalso; 
                   first (
                       rewrite app_assoc separate1 app_assoc in Hbefs;
                       apply concat_cancel_last in Hbefs as [Hbefs <-];
                       separate_last l0;
                       last exfalso;
                       first by rewrite app_assoc in Hbefs;
                       apply concat_cancel_last in Hbefs as [-> <-];
                       apply const_list_split in Hvs0 as [Hvs0 ?];
                       apply const_list_split in Hvs0 as [Hvs0 ?];
                       apply const_list_split in Hvs0 as [Hvs0 ?];
                       eexists _, l, afte0, [], [], _;
                       repeat split ; try done; try (by rewrite app_nil_r); try (by econstructor);
               try rewrite -app_assoc -app_assoc -app_assoc //))
            end .
     32:{ (* Block *)
       left. subst. rewrite separate1 in Heq.
          do 3 rewrite app_assoc in Heq.
          do 2 rewrite - app_assoc in Heq.
          symmetry in Heq.
          rewrite cat_app app_assoc app_assoc -app_assoc in Heq.
          apply first_values in Heq as (Hbef & <- & ->); try done; try (by destruct He0 as [He0 | ->]; last done; destruct e0 => //; destruct b => //); try (by apply const_list_concat; subst ; try apply v_to_e_is_const_list).
          assert (exists vsp, vs0 = vsp ++ vs) as [vsp ->].
          { destruct (length vs0 <? length vs) eqn:Hlenvs.
            - apply Nat.ltb_lt in Hlenvs. rewrite - H2 in Hlenvs.
              exfalso. destruct f, f0.
              edestruct prim_step_split_reduce_r.
              2:{ unfold prim_step. instantiate (7 := (_, _,_)).
                  instantiate (6 := (_,_,_)) => /=.
                  rewrite separate1 in Hred0.
                  rewrite app_assoc in Hred0.
                  repeat split => //. }
              apply to_val_cat_None2 => //.
              2:{ destruct H1 as (n & m & lh & Htrap & Habs & Hσ).
                  move/lfilledP in Habs; inversion Habs; subst.
                  all: apply first_values in H1 as (_ & ? & _) => //. }
              destruct H1 as (esp & -> & Hred & _ & _).
              eapply block_not_enough_arguments_no_reduce => //.
            - apply Nat.ltb_ge in Hlenvs.
              exists (take (length vs0 - length vs) vs0).
              rewrite <- (take_drop (length vs0 - length vs) vs0) at 1.
              f_equal. 
              rewrite - (take_drop (length vs0 - length vs) vs0) in Hbef.
              rewrite app_assoc in Hbef.
              apply app_inj_2 in Hbef as [_ Hres] => //.
              rewrite length_drop. lia. }
          apply const_list_split in Hvs0 as [??].
          eexists _, vsp, afte0, [], [], _.
          repeat split => //. rewrite separate1.
          rewrite -app_assoc. rewrite (app_assoc vs). done.
          rewrite app_nil_r //.
          rewrite app_assoc in Hbef.
          apply app_inj_2 in Hbef as [-> _] => //.
          rewrite app_nil_r //.
          constructor. econstructor => //.
          rewrite app_nil_r //. }
     32:{ (* Loop *)
       left. subst. rewrite separate1 in Heq.
          do 3 rewrite app_assoc in Heq.
          do 2 rewrite - app_assoc in Heq.
          symmetry in Heq.
          rewrite cat_app app_assoc app_assoc -app_assoc in Heq.
          apply first_values in Heq as (Hbef & <- & ->); try done; try (by destruct He0 as [He0 | ->]; last done; destruct e0 => //; destruct b => //); try (by apply const_list_concat; subst ; try apply v_to_e_is_const_list).
          assert (exists vsp, vs0 = vsp ++ vs) as [vsp ->].
          { destruct (length vs0 <? length vs) eqn:Hlenvs.
            - apply Nat.ltb_lt in Hlenvs. rewrite - H2 in Hlenvs.
              exfalso. destruct f, f0.
              edestruct prim_step_split_reduce_r.
              2:{ unfold prim_step. instantiate (7 := (_, _,_)).
                  instantiate (6 := (_,_,_)) => /=.
                  rewrite separate1 in Hred0.
                  rewrite app_assoc in Hred0.
                  repeat split => //. }
              apply to_val_cat_None2 => //.
              2:{ destruct H1 as (n & m & lh & Htrap & Habs & Hσ).
                  move/lfilledP in Habs; inversion Habs; subst.
                  all: apply first_values in H1 as (_ & ? & _) => //. }
              destruct H1 as (esp & -> & Hred & _ & _).
              eapply loop_not_enough_arguments_no_reduce => //.
            - apply Nat.ltb_ge in Hlenvs.
              exists (take (length vs0 - length vs) vs0).
              rewrite <- (take_drop (length vs0 - length vs) vs0) at 1.
              f_equal. 
              rewrite - (take_drop (length vs0 - length vs) vs0) in Hbef.
              rewrite app_assoc in Hbef.
              apply app_inj_2 in Hbef as [_ Hres] => //.
              rewrite length_drop. lia. }
          apply const_list_split in Hvs0 as [??].
          eexists _, vsp, afte0, [], [], _.
          repeat split => //. rewrite separate1.
          rewrite -app_assoc. rewrite (app_assoc vs). done.
          rewrite app_nil_r //.
          rewrite app_assoc in Hbef.
          apply app_inj_2 in Hbef as [-> _] => //.
          rewrite app_nil_r //.
          constructor. econstructor => //.
          rewrite app_nil_r H2 //. }
     48:{ (* Invoke *)
       left. subst. rewrite separate1 in Heq.
          do 3 rewrite app_assoc in Heq.
          do 2 rewrite - app_assoc in Heq.
          symmetry in Heq.
          rewrite cat_app app_assoc app_assoc -app_assoc in Heq.
          apply first_values in Heq as (Hbef & <- & ->); try done; try (by destruct He0 as [He0 | ->]; last done; destruct e0 => //; destruct b => //); try (by apply const_list_concat; subst ; try apply v_to_e_is_const_list).
          assert (exists vsp, vs0 = v_to_e_list $ vsp ++ vcs) as [vsp ->].
           { destruct (length vs0 <? length vcs) eqn:Hlenvs.
            - apply Nat.ltb_lt in Hlenvs. rewrite -H4 in Hlenvs.
              exfalso. destruct f, f0.
              edestruct prim_step_split_reduce_r as [Hres | Hres].
              2:{ unfold prim_step. instantiate (7 := (_, _,_)).
                  instantiate (6 := (_,_,_)) => /=.
                  rewrite separate1 in Hred0.
                  rewrite app_assoc in Hred0.
                  repeat split => //. }
              apply to_val_cat_None2 => //.
              2:{ destruct Hres as (n & m & lh & Htrap & Habs & Hσ).
                  move/lfilledP in Habs; inversion Habs; subst.
                  all: apply first_values in H0 as (_ & ? & _) => //. }
              destruct Hres as (esp & -> & Hred & _ & _).
              eapply invoke_not_enough_arguments_no_reduce_native => //.
            - apply Nat.ltb_ge in Hlenvs.
              apply const_es_exists in Hvs0 as [vs' ->].
              exists (take (length vs' - length vcs) vs').
              rewrite <- (take_drop (length vs' - length vcs) vs') at 1.
              do 2 f_equal. 
              rewrite - (take_drop (length vs' - length vcs) vs') in Hbef.
              rewrite -cat_app -v_to_e_cat in Hbef.
              rewrite app_assoc in Hbef.
              apply app_inj_2 in Hbef as [_ Hres] => //.
              apply v_to_e_inj in Hres => //.
              repeat rewrite length_map.
              rewrite length_map in Hlenvs. rewrite length_drop. lia. }
          eexists _, (v_to_e_list vsp), afte0, [], [], _.
          repeat split => //. apply v_to_e_is_const_list. rewrite separate1.
          rewrite -v_to_e_cat. rewrite -app_assoc. rewrite (app_assoc (v_to_e_list vcs)). done.
          rewrite app_nil_r //.
          rewrite -v_to_e_cat app_assoc in Hbef.
          apply app_inj_2 in Hbef as [-> _] => //.
          rewrite app_nil_r //.
          eapply r_invoke_native => //.
          done. }
     48:{ (* Invoke *)
       left. subst. rewrite separate1 in Heq.
          do 3 rewrite app_assoc in Heq.
          do 2 rewrite - app_assoc in Heq.
          symmetry in Heq.
          rewrite cat_app app_assoc app_assoc -app_assoc in Heq.
          apply first_values in Heq as (Hbef & <- & ->); try done; try (by destruct He0 as [He0 | ->]; last done; destruct e0 => //; destruct b => //); try (by apply const_list_concat; subst ; try apply v_to_e_is_const_list).
          assert (exists vsp, vs0 = v_to_e_list $ vsp ++ vcs) as [vsp ->].
           { destruct (length vs0 <? length vcs) eqn:Hlenvs.
            - apply Nat.ltb_lt in Hlenvs. rewrite -H3 in Hlenvs.
              exfalso. destruct f, f0.
              edestruct prim_step_split_reduce_r as [Hres | Hres].
              2:{ unfold prim_step. instantiate (7 := (_, _,_)).
                  instantiate (6 := (_,_,_)) => /=.
                  rewrite separate1 in Hred0.
                  rewrite app_assoc in Hred0.
                  repeat split => //. }
              apply to_val_cat_None2 => //.
              2:{ destruct Hres as (n & m & lh & Htrap & Habs & Hσ).
                  move/lfilledP in Habs; inversion Habs; subst.
                  all: apply first_values in H0 as (_ & ? & _) => //. }
              destruct Hres as (esp & -> & Hred & _ & _).
              eapply invoke_not_enough_arguments_no_reduce_host => //.
            - apply Nat.ltb_ge in Hlenvs.
              apply const_es_exists in Hvs0 as [vs' ->].
              exists (take (length vs' - length vcs) vs').
              rewrite <- (take_drop (length vs' - length vcs) vs') at 1.
              do 2 f_equal. 
              rewrite - (take_drop (length vs' - length vcs) vs') in Hbef.
              rewrite -cat_app -v_to_e_cat in Hbef.
              rewrite app_assoc in Hbef.
              apply app_inj_2 in Hbef as [_ Hres] => //.
              apply v_to_e_inj in Hres => //.
              repeat rewrite length_map.
              rewrite length_map in Hlenvs. rewrite length_drop. lia. }
          eexists _, (v_to_e_list vsp), afte0, [], [], _.
          repeat split => //. apply v_to_e_is_const_list. rewrite separate1.
          rewrite -v_to_e_cat. rewrite -app_assoc. rewrite (app_assoc (v_to_e_list vcs)). done.
          rewrite app_nil_r //.
          rewrite -v_to_e_cat app_assoc in Hbef.
          apply app_inj_2 in Hbef as [-> _] => //.
          rewrite app_nil_r //.
          eapply r_invoke_host => //.
          done. }
     48:{ (* Try_table *)
       left. subst. rewrite separate1 in Heq.
          do 3 rewrite app_assoc in Heq.
          do 2 rewrite - app_assoc in Heq.
          symmetry in Heq.
          rewrite cat_app app_assoc app_assoc -app_assoc in Heq.
          apply first_values in Heq as (Hbef & <- & ->); try done; try (by destruct He0 as [He0 | ->]; last done; destruct e0 => //; destruct b => //); try (by apply const_list_concat; subst ; try apply v_to_e_is_const_list).
          assert (exists vsp, vs0 = vsp ++ vs) as [vsp ->].
          { destruct (length vs0 <? length vs) eqn:Hlenvs.
            - apply Nat.ltb_lt in Hlenvs. rewrite H2 in Hlenvs.
              exfalso. destruct f, f0.
              edestruct prim_step_split_reduce_r.
              2:{ unfold prim_step. instantiate (7 := (_, _,_)).
                  instantiate (6 := (_,_,_)) => /=.
                  rewrite separate1 in Hred0.
                  rewrite app_assoc in Hred0.
                  repeat split => //. }
              apply to_val_cat_None2 => //.
              2:{ destruct H0 as (n & m & lh & Htrap & Habs & Hσ).
                  move/lfilledP in Habs; inversion Habs; subst.
                  all: apply first_values in H0 as (_ & ? & _) => //. }
              destruct H0 as (esp & -> & Hred & _ & _).
              eapply try_table_not_enough_arguments_no_reduce => //.
            - apply Nat.ltb_ge in Hlenvs.
              exists (take (length vs0 - length vs) vs0).
              rewrite <- (take_drop (length vs0 - length vs) vs0) at 1.
              f_equal. 
              rewrite - (take_drop (length vs0 - length vs) vs0) in Hbef.
              rewrite app_assoc in Hbef.
              apply app_inj_2 in Hbef as [_ Hres] => //.
              rewrite length_drop. lia. }
          apply const_list_split in Hvs0 as [??].
          eexists _, vsp, afte0, [], [], _.
          repeat split => //. rewrite separate1.
          rewrite -app_assoc. rewrite (app_assoc vs). done.
          rewrite app_nil_r //.
          rewrite app_assoc in Hbef.
          apply app_inj_2 in Hbef as [-> _] => //.
          rewrite app_nil_r //.
          eapply r_try_table => //.
          rewrite app_nil_r //. }

     53:{ (* suspend *)
       left. subst. rewrite separate1 in Heq.
          do 3 rewrite app_assoc in Heq.
          do 2 rewrite - app_assoc in Heq.
          symmetry in Heq.
          rewrite cat_app app_assoc app_assoc -app_assoc in Heq.
          apply first_values in Heq as (Hbef & <- & ->); try done; try (by destruct He0 as [He0 | ->]; last done; destruct e0 => //; destruct b => //); try (by apply const_list_concat; subst ; try apply v_to_e_is_const_list).
          assert (exists vsp, vs0 = v_to_e_list $ vsp ++ vs) as [vsp ->].
          { destruct (length vs0 <? length vs) eqn:Hlenvs.
            - apply Nat.ltb_lt in Hlenvs. rewrite H1 in Hlenvs.
              exfalso. destruct f, f0.
              edestruct prim_step_split_reduce_r as [Hres | Hres].
              2:{ unfold prim_step. instantiate (7 := (_, _,_)).
                  instantiate (6 := (_,_,_)) => /=.
                  rewrite separate1 in Hred0.
                  rewrite app_assoc in Hred0.
                  repeat split => //. }
              apply to_val_cat_None2 => //.
              2:{ destruct Hres as (n & m & lh & Htrap & Habs & Hσ).
                  move/lfilledP in Habs; inversion Habs; subst.
                  all: apply first_values in H2 as (_ & ? & _) => //. }
              destruct Hres as (esp & -> & Hred & _ & _).
              eapply suspend_not_enough_arguments_no_reduce => //.
            - apply Nat.ltb_ge in Hlenvs.
              apply const_es_exists in Hvs0 as [vs' ->].
              exists (take (length vs' - length vs) vs').
              rewrite <- (take_drop (length vs' - length vs) vs') at 1.
              do 2 f_equal. 
              rewrite - (take_drop (length vs' - length vs) vs') in Hbef.
              rewrite -cat_app -v_to_e_cat in Hbef.
              rewrite app_assoc in Hbef.
              apply app_inj_2 in Hbef as [_ Hres] => //.
              apply v_to_e_inj in Hres => //.
              repeat rewrite length_map.
              rewrite length_map in Hlenvs. rewrite length_drop. lia. }
          eexists _, (v_to_e_list vsp), afte0, [], [], _.
          repeat split => //. apply v_to_e_is_const_list. rewrite separate1.
          rewrite -v_to_e_cat. rewrite -app_assoc. rewrite (app_assoc (v_to_e_list vs)). done.
          rewrite app_nil_r //.
          rewrite -v_to_e_cat app_assoc in Hbef.
          apply app_inj_2 in Hbef as [-> _] => //.
          rewrite app_nil_r //.
          eapply r_suspend_desugar => //.
          done. } 
  53:{ (* switch *)
       left. subst. rewrite separate1 in Heq.
          do 3 rewrite app_assoc in Heq.
          do 2 rewrite - app_assoc in Heq.
          symmetry in Heq.
          rewrite separate1 in Heq.
          rewrite cat_app in Heq.
          do 3 rewrite app_assoc in Heq.
          rewrite -app_assoc in Heq.
          apply first_values in Heq as (Hbef & <- & ->); try done; try (by destruct He0 as [He0 | ->]; last done; destruct e0 => //; destruct b => //); try (by apply const_list_concat; try apply const_list_concat; subst ; try apply v_to_e_is_const_list).
          separate_last vs0.
       - rewrite app_assoc in Hbef.
         apply concat_cancel_last in Hbef as [Hbef <-].
         apply const_list_split in Hvs0 as [??].
          assert (exists vsp, l = v_to_e_list $ vsp ++ vs) as [vsp ->].
          { destruct (length l <? length vs) eqn:Hlenvs.
            - apply Nat.ltb_lt in Hlenvs.
              assert (S $ length l < S $ length vs); first lia.
              rewrite H4 in H7.
              exfalso. destruct f, f0.
              edestruct prim_step_split_reduce_r as [Hres | Hres].
              2:{ unfold prim_step. instantiate (7 := (_, _,_)).
                  instantiate (6 := (_,_,_)) => /=.
                  rewrite (separate1 $ AI_basic _) in Hred0.
                  rewrite app_assoc in Hred0.
                  repeat split => //. }
              apply to_val_cat_None2 => //.
              apply const_list_concat => //. 
              2:{ destruct Hres as (n & m & lh & Htrap & Habs & Hσ).
                  move/lfilledP in Habs; inversion Habs; subst.
                  all: apply first_values in H8 as (_ & ? & _) => //.
                  all: by apply const_list_concat => //. 
              }
              destruct Hres as (esp & -> & Hred & _ & _).
              rewrite -app_assoc /= in Hred.
              eapply switch_not_enough_arguments_no_reduce => //.
            - apply Nat.ltb_ge in Hlenvs.
              apply const_es_exists in H5 as [vs' ->].
              exists (take (length vs' - length vs) vs').
              rewrite <- (take_drop (length vs' - length vs) vs') at 1.
              do 2 f_equal. 
              rewrite - (take_drop (length vs' - length vs) vs') in Hbef.
              rewrite -cat_app -v_to_e_cat in Hbef.
              rewrite app_assoc in Hbef.
              apply app_inj_2 in Hbef as [_ Hres] => //.
              apply v_to_e_inj in Hres => //.
              repeat rewrite length_map.
              rewrite length_map in Hlenvs. rewrite length_drop. lia. }
          eexists _, (v_to_e_list vsp), afte0, [], [], _.
          repeat split => //. apply v_to_e_is_const_list. rewrite (separate1 $ AI_basic _).
          rewrite -v_to_e_cat. do 2 rewrite -app_assoc.
          simpl. rewrite separate2. 
          rewrite (app_assoc (v_to_e_list vs)). done.
          rewrite app_nil_r //.
          rewrite -v_to_e_cat app_assoc in Hbef.
          apply app_inj_2 in Hbef as [-> _] => //.
          rewrite app_nil_r //.
          eapply r_switch_desugar => //.
          done.
       - clear - Hred0. exfalso. destruct f, f0. 
         edestruct prim_step_split_reduce_r as [Hres | Hres].
         2:{ unfold prim_step. instantiate (7 := (_,_,_)).
             instantiate (6 := (_,_,_)) => /=.
             rewrite /= separate1 in Hred0.
             repeat split => //. }
         done.
         2:{ destruct Hres as (n & m & lh & Htrap & Habs & Hσ).
             move/lfilledP in Habs; inversion Habs; subst.
             all: rewrite - (app_nil_l [_]) in H.
             all: apply first_values in H as (? & ? & ?) => //. }
         destruct Hres as (esp & -> & Hred & _ & _).
         clear - Hred.
         lazymatch goal with
         | _ : reduce _ _ ?es _ _ _ |- _ => remember es as ves
         end.
         induction Hred as [? ? ? ? H00 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ???????????? H00 H01 | ];
        first destruct H00 as [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ??? H01 ]; 
        try (by inversion Heqves);
        try (by destruct vs; try destruct vs; try destruct vs; try destruct vs; inversion Heqves);
        try (by destruct ves; try destruct ves; try destruct ves; try destruct ves; inversion Heqves);
        [ by move/lfilledP in H01; inversion H01; subst;
          try (by do 4 destruct vs => //);
          do 4 destruct bef => //
        | move/lfilledP in H00; inversion H00; subst;
          try (by do 4 destruct vs => //);
          try (by do 4 destruct bef => //);
          destruct vs;
          first (
              do 4 try (destruct es; first by inversion H3; subst; apply values_no_reduce in Hred);

              inversion H3; subst;
              destruct es => //; apply IHHred => //
        )].
         inversion H3; subst. destruct vs, es, es'0 => //. }
  48:{ (* Throw *)
     left. subst. rewrite separate1 in Heq.
          do 3 rewrite app_assoc in Heq.
          do 2 rewrite - app_assoc in Heq.
          symmetry in Heq.
          rewrite cat_app app_assoc app_assoc -app_assoc in Heq.
          apply first_values in Heq as (Hbef & <- & ->); try done; try (by destruct He0 as [He0 | ->]; last done; destruct e0 => //; destruct b => //); try (by apply const_list_concat; subst ; try apply v_to_e_is_const_list).
              assert (exists vsp, vs0 = v_to_e_list $ vsp ++ vcs) as [vsp ->].
           { destruct (length vs0 <? length vcs) eqn:Hlenvs.
             - apply Nat.ltb_lt in Hlenvs. rewrite length_map in H2.
               rewrite H2 in Hlenvs.
              exfalso. destruct f, f0.
              edestruct prim_step_split_reduce_r as [Hres | Hres].
              2:{ unfold prim_step. instantiate (7 := (_, _,_)).
                  instantiate (6 := (_,_,_)) => /=.
                  rewrite separate1 in Hred0.
                  rewrite app_assoc in Hred0.
                  repeat split => //. }
              apply to_val_cat_None2 => //.
              2:{ destruct Hres as (n & m & lh & Htrap & Habs & Hσ).
                  move/lfilledP in Habs; inversion Habs; subst.
                  all: apply first_values in H1 as (_ & ? & _) => //. }
              destruct Hres as (esp & -> & Hred & _ & _).
              eapply throw_not_enough_arguments_no_reduce => //.
            - apply Nat.ltb_ge in Hlenvs.
              apply const_es_exists in Hvs0 as [vs' ->].
              exists (take (length vs' - length vcs) vs').
              rewrite <- (take_drop (length vs' - length vcs) vs') at 1.
              do 2 f_equal. 
              rewrite - (take_drop (length vs' - length vcs) vs') in Hbef.
              rewrite -cat_app -v_to_e_cat in Hbef.
              rewrite app_assoc in Hbef.
              apply app_inj_2 in Hbef as [_ Hres] => //.
              apply v_to_e_inj in Hres => //.
              repeat rewrite length_map.
              rewrite length_map in Hlenvs. rewrite length_drop. lia. }
          eexists _, (v_to_e_list vsp), afte0, [], [], _.
          repeat split => //. apply v_to_e_is_const_list. rewrite separate1.
          rewrite -v_to_e_cat. rewrite -app_assoc. rewrite (app_assoc (v_to_e_list vcs)). done.
          rewrite app_nil_r //.
          rewrite -v_to_e_cat app_assoc in Hbef.
          apply app_inj_2 in Hbef as [-> _] => //.
          rewrite app_nil_r //.
          eapply r_throw => //.
          done. }
  50:{ (* Resume *)
     left. subst. rewrite separate1 in Heq.
          do 3 rewrite app_assoc in Heq.
          do 2 rewrite - app_assoc in Heq.
          symmetry in Heq.
          rewrite separate1 in Heq.
          rewrite cat_app in Heq.
          do 3 rewrite app_assoc in Heq.
          rewrite -app_assoc in Heq.
          apply first_values in Heq as (Hbef & <- & ->); try done; try (by destruct He0 as [He0 | ->]; last done; destruct e0 => //; destruct b => //); try (by apply const_list_concat; try apply const_list_concat; subst ; try apply v_to_e_is_const_list).
          separate_last vs0.
       - rewrite app_assoc in Hbef.
         apply concat_cancel_last in Hbef as [Hbef <-].
         apply const_list_split in Hvs0 as [??].
         assert (exists vsp, l = vsp ++ vs) as [vsp ->].
          { destruct (length l <? length vs) eqn:Hlenvs.
            - apply Nat.ltb_lt in Hlenvs.
              rewrite H1 in Hlenvs.
              exfalso. destruct f, f0.
              edestruct prim_step_split_reduce_r as [Hres | Hres].
              2:{ unfold prim_step. instantiate (7 := (_, _,_)).
                  instantiate (6 := (_,_,_)) => /=.
                  rewrite (separate1 $ AI_basic _) in Hred0.
                  rewrite app_assoc in Hred0.
                  repeat split => //. }
              apply to_val_cat_None2 => //.
              apply const_list_concat => //. 
              2:{ destruct Hres as (n & m & lh & Htrap & Habs & Hσ).
                  move/lfilledP in Habs; inversion Habs; subst.
                  all: apply first_values in H7 as (_ & ? & _) => //.
                  all: by apply const_list_concat => //. 
              }
              destruct Hres as (esp & -> & Hred & _ & _).
              rewrite -app_assoc /= in Hred.
              eapply resume_not_enough_arguments_no_reduce => //.
            - apply Nat.ltb_ge in Hlenvs.
              exists (take (length l - length vs) l).
              rewrite <- (take_drop (length l - length vs) l) at 1.
              do 2 f_equal. 
              rewrite - (take_drop (length l - length vs) l) in Hbef.
              rewrite app_assoc in Hbef.
              apply app_inj_2 in Hbef as [_ Hres] => //.
              rewrite length_drop. lia. }
          eexists _, vsp, afte0, [], [], _.
          repeat split => //. apply const_list_split in H5 as [??] => //.
          rewrite (separate1 $ AI_basic _).
          do 2 rewrite -app_assoc.
          simpl. rewrite separate2. 
          rewrite (app_assoc (vs)). done.
          rewrite app_nil_r //.
          rewrite app_assoc in Hbef.
          apply app_inj_2 in Hbef as [-> _] => //.
          rewrite app_nil_r //.
          eapply r_resume => //.
          done.
       - clear - Hred0. exfalso. destruct f, f0. 
         edestruct prim_step_split_reduce_r as [Hres | Hres].
         2:{ unfold prim_step. instantiate (7 := (_,_,_)).
             instantiate (6 := (_,_,_)) => /=.
             rewrite /= separate1 in Hred0.
             repeat split => //. }
         done.
         2:{ destruct Hres as (n & m & lh & Htrap & Habs & Hσ).
             move/lfilledP in Habs; inversion Habs; subst.
             all: rewrite - (app_nil_l [_]) in H.
             all: apply first_values in H as (? & ? & ?) => //. }
         destruct Hres as (esp & -> & Hred & _ & _).
         clear - Hred.
         lazymatch goal with
         | _ : reduce _ _ ?es _ _ _ |- _ => remember es as ves
         end.
         induction Hred as [? ? ? ? H00 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ???????????? H00 H01 | ];
        first destruct H00 as [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ??? H01 ]; 
        try (by inversion Heqves);
        try (by destruct vs; try destruct vs; try destruct vs; try destruct vs; inversion Heqves);
        try (by destruct ves; try destruct ves; try destruct ves; try destruct ves; inversion Heqves);
        [ by move/lfilledP in H01; inversion H01; subst;
          try (by do 4 destruct vs => //);
          do 4 destruct bef => //
        | move/lfilledP in H00; inversion H00; subst;
          try (by do 4 destruct vs => //);
          try (by do 4 destruct bef => //);
          destruct vs;
          first (
              do 4 try (destruct es; first by inversion H3; subst; apply values_no_reduce in Hred);

              inversion H3; subst;
              destruct es => //; apply IHHred => //
        )].
         inversion H3; subst. destruct vs, es, es'0 => //. }
  51:{ (* Contbind *)
     left. subst. rewrite separate1 in Heq.
          do 3 rewrite app_assoc in Heq.
          do 2 rewrite - app_assoc in Heq.
          symmetry in Heq.
          rewrite separate1 in Heq.
          rewrite cat_app in Heq.
          do 3 rewrite app_assoc in Heq.
          rewrite -app_assoc in Heq.
          apply first_values in Heq as (Hbef & <- & ->); try done; try (by destruct He0 as [He0 | ->]; last done; destruct e0 => //; destruct b => //); try (by apply const_list_concat; try apply const_list_concat; subst ; try apply v_to_e_is_const_list).
          separate_last vs0.
       - rewrite app_assoc in Hbef.
         apply concat_cancel_last in Hbef as [Hbef <-].
         apply const_list_split in Hvs0 as [??].
         assert (exists vsp, l = vsp ++ vs) as [vsp ->].
          { destruct (length l <? length vs) eqn:Hlenvs.
            - apply Nat.ltb_lt in Hlenvs.
              rewrite -H2 in Hlenvs.
              exfalso. destruct f, f0.
              edestruct prim_step_split_reduce_r as [Hres | Hres].
              2:{ unfold prim_step. instantiate (7 := (_, _,_)).
                  instantiate (6 := (_,_,_)) => /=.
                  rewrite (separate1 $ AI_basic _) in Hred0.
                  rewrite app_assoc in Hred0.
                  repeat split => //. }
              apply to_val_cat_None2 => //.
              apply const_list_concat => //. 
              2:{ destruct Hres as (n & m & lh & Htrap & Habs & Hσ).
                  move/lfilledP in Habs; inversion Habs; subst.
                  all: apply first_values in H6 as (_ & ? & _) => //.
                  all: by apply const_list_concat => //. 
              }
              destruct Hres as (esp & -> & Hred & _ & _).
              rewrite -app_assoc /= in Hred.
              eapply contbind_not_enough_arguments_no_reduce => //.
            - apply Nat.ltb_ge in Hlenvs.
              exists (take (length l - length vs) l).
              rewrite <- (take_drop (length l - length vs) l) at 1.
              do 2 f_equal. 
              rewrite - (take_drop (length l - length vs) l) in Hbef.
              rewrite app_assoc in Hbef.
              apply app_inj_2 in Hbef as [_ Hres] => //.
              rewrite length_drop. lia. }
          eexists _, vsp, afte0, [], [], _.
          repeat split => //. apply const_list_split in H4 as [??] => //.
          rewrite (separate1 $ AI_basic _).
          do 2 rewrite -app_assoc.
          simpl. rewrite separate2. 
          rewrite (app_assoc (vs)). done.
          rewrite app_nil_r //.
          rewrite app_assoc in Hbef.
          apply app_inj_2 in Hbef as [-> _] => //.
          rewrite app_nil_r //.
          eapply r_contbind => //.
          done.
       - clear - Hred0. exfalso. destruct f, f0. 
         edestruct prim_step_split_reduce_r as [Hres | Hres].
         2:{ unfold prim_step. instantiate (7 := (_,_,_)).
             instantiate (6 := (_,_,_)) => /=.
             rewrite /= separate1 in Hred0.
             repeat split => //. }
         done.
         2:{ destruct Hres as (n & m & lh & Htrap & Habs & Hσ).
             move/lfilledP in Habs; inversion Habs; subst.
             all: rewrite - (app_nil_l [_]) in H.
             all: apply first_values in H as (? & ? & ?) => //. }
         destruct Hres as (esp & -> & Hred & _ & _).
         clear - Hred.
         lazymatch goal with
         | _ : reduce _ _ ?es _ _ _ |- _ => remember es as ves
         end.
         induction Hred as [? ? ? ? H00 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ???????????? H00 H01 | ];
        first destruct H00 as [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ??? H01 ]; 
        try (by inversion Heqves);
        try (by destruct vs; try destruct vs; try destruct vs; try destruct vs; inversion Heqves);
        try (by destruct ves; try destruct ves; try destruct ves; try destruct ves; inversion Heqves);
        [ by move/lfilledP in H01; inversion H01; subst;
          try (by do 4 destruct vs => //);
          do 4 destruct bef => //
        | move/lfilledP in H00; inversion H00; subst;
          try (by do 4 destruct vs => //);
          try (by do 4 destruct bef => //);
          destruct vs;
          first (
              do 4 try (destruct es; first by inversion H3; subst; apply values_no_reduce in Hred);

              inversion H3; subst;
              destruct es => //; apply IHHred => //
        )].
         inversion H3; subst. destruct vs, es, es'0 => //. }
  52:{ (* Resume_throw *)
     left. subst. rewrite separate1 in Heq.
          do 3 rewrite app_assoc in Heq.
          do 2 rewrite - app_assoc in Heq.
          symmetry in Heq.
          rewrite separate1 in Heq.
          rewrite cat_app in Heq.
          do 3 rewrite app_assoc in Heq.
          rewrite -app_assoc in Heq.
          apply first_values in Heq as (Hbef & <- & ->); try done; try (by destruct He0 as [He0 | ->]; last done; destruct e0 => //; destruct b => //); try (by apply const_list_concat; try apply const_list_concat; subst ; try apply v_to_e_is_const_list).
          separate_last vs0.
       - rewrite app_assoc in Hbef.
         apply concat_cancel_last in Hbef as [Hbef <-].
         apply const_list_split in Hvs0 as [??].
         assert (exists vsp, l = v_to_e_list $ vsp ++ vcs) as [vsp ->].
          { destruct (length l <? length vcs) eqn:Hlenvs.
            - apply Nat.ltb_lt in Hlenvs.
              rewrite length_map in H2. rewrite H2 in Hlenvs.
              exfalso. destruct f, f0.
              edestruct prim_step_split_reduce_r as [Hres | Hres].
              2:{ unfold prim_step. instantiate (7 := (_, _,_)).
                  instantiate (6 := (_,_,_)) => /=.
                  rewrite (separate1 $ AI_basic _) in Hred0.
                  rewrite app_assoc in Hred0.
                  repeat split => //. }
              apply to_val_cat_None2 => //.
              apply const_list_concat => //. 
              2:{ destruct Hres as (n & m & lh & Htrap & Habs & Hσ).
                  move/lfilledP in Habs; inversion Habs; subst.
                  all: apply first_values in H4 as (_ & ? & _) => //.
                  all: by apply const_list_concat => //. 
              }
              destruct Hres as (esp & -> & Hred & _ & _).
              rewrite -app_assoc /= in Hred.
              eapply resume_throw_not_enough_arguments_no_reduce => //.
            - apply Nat.ltb_ge in Hlenvs.
              apply const_es_exists in H1 as [vs' ->].
              exists (take (length vs' - length vcs) vs').
              rewrite <- (take_drop (length vs' - length vcs) vs') at 1.
              do 2 f_equal. 
              rewrite - (take_drop (length vs' - length vcs) vs') in Hbef.
              rewrite -cat_app -v_to_e_cat in Hbef.
              rewrite app_assoc in Hbef.
              apply app_inj_2 in Hbef as [_ Hres] => //.
              apply v_to_e_inj in Hres => //.
              repeat rewrite length_map.
              rewrite length_map in Hlenvs. rewrite length_drop. lia. }
          eexists _, (v_to_e_list vsp), afte0, [], [], _.
          repeat split => //. apply v_to_e_is_const_list.
          rewrite (separate1 $ AI_basic _).
          rewrite -v_to_e_cat.
          do 2 rewrite -app_assoc.
          simpl. rewrite separate2. 
          rewrite (app_assoc (v_to_e_list vcs)). done.
          rewrite app_nil_r //.
          rewrite -v_to_e_cat app_assoc in Hbef.
          apply app_inj_2 in Hbef as [-> _] => //.
          rewrite app_nil_r //.
          eapply r_resume_throw => //.
          done.
       - clear - Hred0. exfalso. destruct f, f0. 
         edestruct prim_step_split_reduce_r as [Hres | Hres].
         2:{ unfold prim_step. instantiate (7 := (_,_,_)).
             instantiate (6 := (_,_,_)) => /=.
             rewrite /= separate1 in Hred0.
             repeat split => //. }
         done.
         2:{ destruct Hres as (n & m & lh & Htrap & Habs & Hσ).
             move/lfilledP in Habs; inversion Habs; subst.
             all: rewrite - (app_nil_l [_]) in H.
             all: apply first_values in H as (? & ? & ?) => //. }
         destruct Hres as (esp & -> & Hred & _ & _).
         clear - Hred.
         lazymatch goal with
         | _ : reduce _ _ ?es _ _ _ |- _ => remember es as ves
         end.
         induction Hred as [? ? ? ? H00 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ???????????? H00 H01 | ];
        first destruct H00 as [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ??? H01 ]; 
        try (by inversion Heqves);
        try (by destruct vs; try destruct vs; try destruct vs; try destruct vs; inversion Heqves);
        try (by destruct ves; try destruct ves; try destruct ves; try destruct ves; inversion Heqves);
        [ by move/lfilledP in H01; inversion H01; subst;
          try (by do 4 destruct vs => //);
          do 4 destruct bef => //
        | move/lfilledP in H00; inversion H00; subst;
          try (by do 4 destruct vs => //);
          try (by do 4 destruct bef => //);
          destruct vs;
          first (
              do 4 try (destruct es; first by inversion H3; subst; apply values_no_reduce in Hred);

              inversion H3; subst;
              destruct es => //; apply IHHred => //
        )].
         inversion H3; subst. destruct vs, es, es'0 => //. }
  43:{ remember H1 as H1'; clear HeqH1'.
       move/lfilledP in H1'; inversion H1'; subst.
       all: rewrite separate1 in Heq.
       all: do 3 rewrite app_assoc in Heq.
       all: do 2 rewrite -app_assoc in Heq.
       all: symmetry in Heq.
       all: repeat rewrite cat_app in Heq.
       all: do 3 rewrite app_assoc in Heq.
       all: do 2 rewrite -app_assoc in Heq.
       all: apply first_values in Heq as (Hbef & <- & Haft) => //.
       all: try by apply const_list_concat.
       all: try by destruct He0 as [? | ->] => //; destruct e0; try destruct b.
       all: right.
       all: repeat eexists => //.
       instantiate (1 := LH_base vs0 afte0); rewrite /lfilled /lfill /= Hvs0 //.
       instantiate (1 := LH_handler vs0 hs lh' afte0).
       apply/lfilledP; constructor => //.
       instantiate (1 := LH_prompt vs0 ts hs lh' afte0).
       apply/lfilledP; constructor => //. }
  68:{ move/lfilledP in H; inversion H; subst.
       all: move/lfilledP in H0; inversion H0; subst.
       - destruct vs.
         + destruct es'0.
           * repeat rewrite cats0 /=.
             rewrite cats0 /= in Hlen, Heq.
             eapply IHHred1 => //.
           * edestruct IHnnnn as [(core & bc0 & ac0 & bc1 & ac1 & core' & Hbc0 & Hbc1 &
                                     Hes0 & Hes & Hbefs & Hafts & Hredcore & Hcore') |
                                   (lh0 & lh1 & Hfill0 & Hfill1 & Hσ)].
             exact Hbef1.
             exact Hred0.
             exact Hred1.
             rewrite Heq /=.
             repeat rewrite app_assoc.
             rewrite - (app_assoc (_ ++ _)).
             done.
             rewrite /= length_app /= in Hlen.
             lia.
             left.
             eexists core,bc0,ac0,bc1,(ac1 ++ (a :: es'0)),core'.
             repeat split => //=.
             rewrite Hes.
             repeat rewrite app_assoc.
             done.
             by rewrite - app_assoc.
             repeat rewrite app_assoc.
             rewrite - (app_assoc bc1).
             rewrite Hcore'.
             done.
             right.
             edestruct lfilled_prepend_append as [lh' Hlh'].
             exact H1.
             exact Hfill1.
             eexists _,_; split => //.
         + edestruct IHnnnn as [(core & bc0 & ac0 & bc1 & ac1 & core' & Hbc0 & Hbc1 &
                                Hes0 & Hes & Hbefs & Hafts & Hredcore & Hcore') |
                              (lh0 & lh1 & Hfill0 & Hfill1 & Hσ)].
           instantiate (1 := (bef1 ++ a :: vs)).
           by apply const_list_concat.
           exact Hred0.
           exact Hred1.
           instantiate (1 := (es'0 ++ aft1)).
           rewrite Heq.
           simpl.
           repeat rewrite - app_assoc.
           done.
           repeat rewrite /= length_app /= in Hlen.
           lia.
           left.
           eexists core,bc0,ac0,(a :: vs ++ bc1),(ac1 ++ es'0),core'.
           repeat split => //.
           rewrite app_comm_cons.
           by const_list_app.
           rewrite Hes /=.
           repeat rewrite cat_app.
           repeat rewrite app_assoc.
           done.
           rewrite Hbefs.
           repeat rewrite - app_assoc.
           done.
           rewrite Hafts.
           by rewrite - app_assoc.
           rewrite app_comm_cons.
           repeat rewrite - app_assoc.
           rewrite (app_assoc bc1).
           rewrite (app_assoc (bc1 ++ core')).
           rewrite - (app_assoc bc1).
           rewrite Hcore'.
           done.
           right.
           edestruct lfilled_prepend_append as [lh' Hlh'].
           exact H1. exact Hfill1.
           eexists _,_ ; split => //=. 
       - repeat rewrite app_assoc in Heq.
         repeat rewrite - (app_assoc (_ ++ _)) in Heq.
         repeat rewrite - app_comm_cons in Heq.
         apply first_values in Heq as (Hbefs & -> & Hafts) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ; try (destruct He0 as [-> | ->]; by intros [? ?]);
        try by const_list_app.
         left ; eexists [AI_label n es'0 LI], vs0, afte0, _, _, _.
         repeat split => //=. 
         eapply r_label.
         exact Hred1.
         instantiate (1 := LH_rec [] n es'0 lh' []).
         instantiate (1 := S k0).
         rewrite - (app_nil_l [_]) - (app_nil_r [_]).
         apply/lfilledP. constructor => //.
         apply/lfilledP. constructor => //.
         done.
       - repeat rewrite app_assoc in Heq.
         repeat rewrite - (app_assoc (_ ++ _)) in Heq.
         repeat rewrite - app_comm_cons in Heq.
         apply first_values in Heq as (Hbefs & -> & Hafts) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ; try (destruct He0 as [-> | ->]; by intros [? ?]);
        try by const_list_app.
         left ; eexists [AI_handler hs LI], vs0, afte0, _, _, _.
         repeat split => //=. 
         eapply r_label.
         exact Hred1.
         instantiate (1 := LH_handler [] hs lh' []).
         instantiate (1 := k).
         rewrite - (app_nil_l [_]) - (app_nil_r [_]).
         apply/lfilledP. constructor => //.
         apply/lfilledP. constructor => //.
         done.
       - repeat rewrite app_assoc in Heq.
         repeat rewrite - (app_assoc (_ ++ _)) in Heq.
         repeat rewrite - app_comm_cons in Heq.
         apply first_values in Heq as (Hbefs & -> & Hafts) ; try done ; try (by destruct He0 ; destruct e0 => // ; destruct b => //) ; try (destruct He0 as [-> | ->]; by intros [? ?]);
        try by const_list_app.
         left ; eexists [AI_prompt ts hs LI], vs0, afte0, _, _, _.
         repeat split => //=. 
         eapply r_label.
         exact Hred1.
         instantiate (1 := LH_prompt [] ts hs lh' []).
         instantiate (1 := k).
         rewrite - (app_nil_l [_]) - (app_nil_r [_]).
         apply/lfilledP. constructor => //.
         apply/lfilledP. constructor => //.
         done.
  } 

  all: simpl in Hred0.
     all: clear - Hred0.
     all: lazymatch goal with
          | _ : reduce _ _ (_ :: _ :: _ :: _) _ _ _ |- _ =>
              rewrite separate3 in Hred0
          | _ : reduce _ _ (_ :: _ :: _) _ _ _ |- _ =>
              rewrite separate2 in Hred0
          | _ : reduce _ _ (_ :: _) _ _ _ |- _ =>
              rewrite separate1 in Hred0
          end.
     all: destruct f, f0.
     all: edestruct prim_step_split_reduce_r as [Hres | Hres].
     all: try by unfold prim_step; instantiate (7 := (_, _, _));
       instantiate (6 := (_,_,_)); simpl; repeat split.
     all: try done.
     51, 58: by destruct v2; try destruct v.
     all: try by destruct Hres as (? & ? & ? & _ & Habs & _);
       move/lfilledP in Habs; inversion Habs; subst;
       try (by repeat destruct vs => //);
       try (by repeat destruct bef => //).
     27, 31: by destruct Hres as (? & ? & ? & _ & Habs & _);
          move/lfilledP in Habs; inversion Habs; subst;
          destruct v2; try destruct v;
     try (by repeat destruct vs => //);
     try (by repeat destruct bef => //).
     all: destruct Hres as (esp & -> & Hred & _ & _).
     all: clear - Hred.
     all: lazymatch goal with
          | _ : reduce _ _ ?es _ _ _ |- _ => remember es as ves
          end.
 
          
     all: induction Hred as [? ? ? ? H00 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ???????????? H00 H01 | ];
        first destruct H00 as [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ??? H01 ]; 
        try (by inversion Heqves);
        try (by destruct vs; try destruct vs; try destruct vs; try destruct vs; inversion Heqves);
        try (by destruct ves; try destruct ves; try destruct ves; try destruct ves; inversion Heqves);
        [ by move/lfilledP in H01; inversion H01; subst;
          try (by try (destruct v2; try destruct v); do 4 destruct vs => //);
          try (destruct v2; try destruct v); do 4 destruct bef => //
        | move/lfilledP in H00; inversion H00; subst;
          try (by try (destruct v2; try destruct v); do 4 destruct vs => //);
          try (by try (destruct v2; try destruct v); do 4 destruct bef => //);
          destruct vs;
          first (
              do 4 try (destruct es; first by inversion H3; subst; apply values_no_reduce in Hred; try rewrite /= const_const);

              inversion H3; subst;
              destruct es => //; apply IHHred => //
        )].
     all: inversion H3; subst.
     all: try by destruct vs, es => //; empty_list_no_reduce.
     all: destruct vs; last ((by destruct vs, es => //; empty_list_no_reduce) + (destruct vs; last by destruct vs, es => //; empty_list_no_reduce)).
     all: destruct es; first empty_list_no_reduce.
     all: inversion H2; subst.
     all: destruct es; try done; try by inversion H4; subst; apply values_no_reduce in Hred.
     all: try inversion H4; subst.
     all: try destruct es => //.
     all: clear - Hred.
         all: lazymatch goal with
          | _ : reduce _ _ ?es _ _ _ |- _ => remember es as ves
          end.
 
          
     all: induction Hred as [? ? ? ? H00 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ???????????? H00 H01 | ];
        first destruct H00 as [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ??? H01 ]; 
        try (by inversion Heqves);
        try (by destruct vs; try destruct vs; try destruct vs; try destruct vs; inversion Heqves);
        try (by destruct ves; try destruct ves; try destruct ves; try destruct ves; inversion Heqves);
        [ by move/lfilledP in H01; inversion H01; subst;
          try (by try (destruct v2; try destruct v); do 4 destruct vs => //);
          try (destruct v2; try destruct v); do 4 destruct bef => //
        | move/lfilledP in H00; inversion H00; subst;
          try (by try (destruct v2; try destruct v); do 4 destruct vs => //);
          try (by try (destruct v2; try destruct v); do 4 destruct bef => //);
          destruct vs;
          first (
              do 4 try (destruct es; first by inversion H3; subst; apply values_no_reduce in Hred; try rewrite /= const_const);

              inversion H3; subst;
              destruct es => //; apply IHHred => //
        )].
     all: inversion H3; subst.
     all: try by destruct vs, es => //; empty_list_no_reduce.
     all: destruct vs; last by destruct vs, es => //; empty_list_no_reduce.
     all: destruct es; first empty_list_no_reduce.
     all: inversion H2; subst.
     all: destruct es => //.
     all: clear - Hred.
     all: lazymatch goal with
          | _ : reduce _ _ ?es _ _ _ |- _ => remember es as ves
          end.
     all: induction Hred as [? ? ? ? H00 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ???????????? H00 H01 | ];
        first destruct H00 as [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ??? H01 ]; 
        try (by inversion Heqves);
        try (by destruct vs; try destruct vs; try destruct vs; try destruct vs; inversion Heqves);
        try (by destruct ves; try destruct ves; try destruct ves; try destruct ves; inversion Heqves);
        [ by move/lfilledP in H01; inversion H01; subst;
          try (by try (destruct v2; try destruct v); do 4 destruct vs => //);
          try (destruct v2; try destruct v); do 4 destruct bef => //
        | move/lfilledP in H00; inversion H00; subst;
          try (by try (destruct v2; try destruct v); do 4 destruct vs => //);
          try (by try (destruct v2; try destruct v); do 4 destruct bef => //);
          destruct vs;
          first (
              do 4 try (destruct es; first by inversion H3; subst; apply values_no_reduce in Hred; try rewrite /= const_const);

              inversion H3; subst;
              destruct es => //; apply IHHred => //
        )].
     all: inversion H3; subst.
     all: try by destruct vs, es => //; empty_list_no_reduce.
  Qed. 

End reduction_core.

