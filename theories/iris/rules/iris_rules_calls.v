From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
Require Export iris_rules_structural.

Set Bullet Behavior "Strict Subproofs".
Section iris_rules_calls.
  
Context `{!wasmG Σ}.

  Lemma v_to_e_list_to_val es vs :
    iris.to_val es = Some (immV vs) ->
    v_to_e_list vs = es.
  Proof.
    revert vs. induction es.
    { intros vs Hval. destruct vs;inversion Hval. done. }
    { intros vs Hval.
      unfold to_val, iris.to_val in Hval.
      destruct a => // ; try destruct b => // ; simpl in Hval.
      all: try by rewrite merge_notval in Hval.
      - rewrite merge_br flatten_simplify in Hval => //.
      - rewrite merge_return flatten_simplify in Hval => //.
      - rewrite merge_prepend in Hval.
        unfold to_val, iris.to_val in IHes.
        destruct (merge_values _) => //.
        destruct v0 => //.
        specialize (IHes l Logic.eq_refl).
        simpl in Hval.
        inversion Hval ; subst => //=.
        destruct e => //.
      - rewrite merge_prepend in Hval.
        unfold to_val, iris.to_val in IHes.
        destruct (merge_values _) => //.
        destruct v => //.
        specialize (IHes l Logic.eq_refl).
        simpl in Hval.
        inversion Hval ; subst => //=.
        destruct e => //.
      - rewrite merge_trap flatten_simplify in Hval => //.
        destruct es => //.
      - rewrite merge_prepend in Hval.
        unfold to_val, iris.to_val in IHes.
        destruct (merge_values _) => //.
        destruct v => //.
        specialize (IHes l Logic.eq_refl).
        simpl in Hval.
        inversion Hval ; subst => //=.
        destruct e => //.
      - rewrite merge_prepend in Hval.
        unfold to_val, iris.to_val in IHes.
        destruct (merge_values _) => //.
        destruct v => //.
        specialize (IHes l Logic.eq_refl).
        simpl in Hval.
        inversion Hval ; subst => //=.
        destruct e0 => //.
      - rewrite merge_prepend in Hval.
        unfold to_val, iris.to_val in IHes.
        destruct (merge_values _) => //.
        destruct v => //.
        specialize (IHes l Logic.eq_refl).
        simpl in Hval.
        inversion Hval ; subst => //=.
        destruct e => //.
      - rewrite merge_throw in Hval => //.
      - rewrite merge_suspend in Hval => //.
      - rewrite merge_switch in Hval => //. 
      - destruct (merge_values (map _ l0)) => //.
        destruct v => //.
        all: try by rewrite merge_notval in Hval.
        rewrite merge_br flatten_simplify in Hval => //.
        rewrite merge_return flatten_simplify in Hval => //.
        rewrite merge_call_host flatten_simplify in Hval => //.
        destruct e => //.
        rewrite merge_suspend in Hval => //.
        rewrite merge_switch in Hval => //.
        destruct (exnelts_of_exception_clauses _ _) => //. 
        rewrite merge_throw in Hval => //.
        rewrite merge_notval in Hval => //.
      - destruct (merge_values (map _ _)) => //.
        destruct v => //.
        all: try by rewrite merge_notval in Hval.
        rewrite merge_br flatten_simplify in Hval => //.
        rewrite merge_return flatten_simplify in Hval => //.
        rewrite merge_call_host flatten_simplify in Hval => //.
        destruct e => //.
        destruct (suselts_of_continuation_clauses _ _) => //.
        rewrite merge_suspend in Hval => //.
        rewrite merge_notval in Hval => //.
        destruct (swelts_of_continuation_clauses _ _) => //. 
        rewrite merge_switch in Hval => //.
        rewrite merge_notval in Hval => //. 
        rewrite merge_throw in Hval => //.
      - destruct (merge_values (map _ _)) => //.
        destruct v => //.
        all: try by rewrite merge_notval in Hval.
        destruct i => //.
        2: destruct (vh_decrease _) => //.
        all: try by rewrite merge_notval in Hval.
        rewrite merge_br flatten_simplify in Hval => //.
        rewrite merge_return flatten_simplify in Hval => //.
        rewrite merge_call_host flatten_simplify in Hval => //.
        destruct e => //.
        rewrite merge_suspend in Hval => //.
        rewrite merge_switch in Hval => //.
        rewrite merge_throw in Hval => //.
        
      - destruct (merge_values $ map _ _) => //.
        destruct v => //.
        all: try by rewrite merge_notval in Hval.
        rewrite merge_call_host flatten_simplify in Hval => //.
        destruct e => //.
        rewrite merge_suspend in Hval => //.
        rewrite merge_switch in Hval => //.
        rewrite merge_throw in Hval => //. 
      - rewrite merge_call_host flatten_simplify in Hval => //.
    }
  Qed.

  (* -------------------------------------------------------------------------- *)
  (* ----------------------------- Native invocations ------------------------- *)
  (* -------------------------------------------------------------------------- *)

  Lemma ewp_invoke_native (E : coPset) Ψ (Φ : val -> iProp Σ) ves vcs t1s t2s ts a es i m f f' :
    iris.to_val ves = Some (immV vcs) ->
    length vcs = length t1s ->
    length t2s = m ->
    (N.of_nat a) ↦[wf] (FC_func_native i (Tf t1s t2s) ts es) -∗
     ▷ ((N.of_nat a) ↦[wf] (FC_func_native i (Tf t1s t2s) ts es) -∗
       EWP [::AI_local m (Build_frame (vcs ++ (default_vals ts)) i) [::AI_basic (BI_block (Tf [::] t2s) es)]] UNDER f @ E <| Ψ |> {{ v, Φ v ; f' }}) -∗
     EWP ves ++ [AI_invoke a] UNDER f @ E <| Ψ |> {{ v, Φ v ; f' }}.
  Proof.
    iIntros (Hparams Hlen Hret) "Hi HΦ".
    iApply ewp_lift_step.
    { apply to_val_const_list in Hparams. apply to_val_cat_None2; auto. }
    { apply to_eff_cat_None2 => //. apply to_val_const_list in Hparams => //. } 
    iIntros (σ) "(Hσ1&Hσ2&Hσ3&Hσ4&Hσ5&Hσ6)".
    iApply fupd_frame_l.
    iDestruct (gen_heap_valid with "Hσ1 Hi") as %Hlook.
    eassert (reduce _ {| f_locs := _; f_inst := _ |}
           (ves ++ [AI_invoke a])%list _ {| f_locs := _; f_inst := _ |}
           [AI_local m {| f_locs := vcs ++ default_vals ts; f_inst := i |} [AI_basic (BI_block (Tf [] t2s) es)]]) as Hred.
    { eapply r_invoke_native with (ts:=ts);eauto.
      { rewrite gmap_of_list_lookup Nat2N.id in Hlook. rewrite /= nth_error_lookup //. }
      { symmetry. apply v_to_e_list_to_val. auto. } }
    iSplit.
    - iPureIntro.
      unfold language.reducible, language.prim_step => /=.
      eexists [], _, (_,_,_), [].
      unfold iris.prim_step => /=.
      repeat split => //.
    - iApply fupd_mask_intro;[solve_ndisj|].
      iIntros "Hcls !>" (es1 ??? HStep).
      iMod "Hcls". iModIntro.
      destruct HStep as (H & _).
      assert (first_instr (ves ++ [AI_invoke a]) = Some (AI_invoke a,0)) as Hf.
      { apply first_instr_const. eapply to_val_const_list. eauto. }
      eapply reduce_det in H as HH;[|apply Hred].
      destruct HH as [Hf' [HH | [[? Hstart] |  (?&?&?&Hstart & Hstart1 & Hstart2 & Hσ)]]]; try done.
      inversion Hf'; subst.
      destruct HH as [<- <-].
      iFrame. 
      iSpecialize ("HΦ" with "[$]"). destruct f; iFrame.
      rewrite Hf in Hstart. done.
  Qed.

  (* -------------------------------------------------------------------------- *)
  (* ------------------------------ Host invocations -------------------------- *)
  (* -------------------------------------------------------------------------- *)

  
  
  Lemma ewp_invoke_host E ves vcs n t1s t2s a h f f' Ψ Φ :
    ves = v_to_e_list vcs ->
    length vcs = n ->
    length t1s = n ->
    (N.of_nat a) ↦[wf] (FC_func_host (Tf t1s t2s) h) -∗
        ▷ ((N.of_nat a) ↦[wf] (FC_func_host (Tf t1s t2s) h) -∗
      EWP [AI_call_host (Tf t1s t2s) h vcs] UNDER f @ E <| Ψ |> {{ Φ ; f' }}) -∗
     EWP ves ++ [AI_invoke a] UNDER f@ E <| Ψ |> {{ Φ ; f' }}.
Proof.
  iIntros (Hves Hvcs Ht1s) "Ha Hwp".
  iApply ewp_lift_step => //=.
  - apply to_val_cat_None2 => //.
    subst; apply v_to_e_is_const_list.
  - apply to_eff_cat_None2 => //.
    subst; apply v_to_e_is_const_list.

  - iIntros (σ) "Hσ".
    iApply fupd_mask_intro ; first by solve_ndisj.
    iIntros "Hfupd".
    iDestruct "Hσ" as "(Hσ1 & ? & ? & ? & ? & ?)".
    iDestruct (gen_heap_valid with "Hσ1 Ha") as %Hlook.
    iSplit.
    + iPureIntro.
      unfold reducible, language.prim_step => //=.
      eexists _,_,(_,_,_),_.
      repeat split => //=.
      eapply (r_invoke_host (t2s := t2s)) => //=.
      rewrite nth_error_lookup => //=.
      rewrite gmap_of_list_lookup Nat2N.id in Hlook.
      done.
    + iIntros "!>" (es ??? HStep).
      iMod "Hfupd".
      iModIntro.
      destruct HStep as [H _].
      eapply reduce_det in H as [? [? | [ [??] | (?&?&?&?&?&?&?)]]] ; last first.
      eapply (r_invoke_host (t2s := t2s)) => //.
      rewrite nth_error_lookup => //=.
      rewrite gmap_of_list_lookup Nat2N.id in Hlook => //.
      rewrite first_instr_const in H0.
      simpl in H0 => //.
      by subst ; apply v_to_e_is_const_list.
      rewrite first_instr_const in H0.
      simpl in H0 => //.
      by subst ; apply v_to_e_is_const_list.
      simplify_eq.
      iDestruct ("Hwp" with "Ha") as "Hwp".
      destruct H0 as [<- <-].
      destruct f; iFrame.
Qed.


  (* -------------------------------------------------------------------------- *)
  (* ---------------------------------- Calls --------------------------------- *)
  (* -------------------------------------------------------------------------- *)

  Lemma ewp_call_ctx (E : coPset) Ψ (Φ : val -> iProp Σ) f0 f' (i : nat) a j lh :
    (inst_funcs (f_inst f0)) !! i = Some a -> 
    ▷ EWP [AI_invoke a] UNDER f0 @ E CTX j; lh <| Ψ |> {{ v, Φ v ; f' }} -∗
     EWP [AI_basic (BI_call i)] UNDER f0 @ E CTX j; lh <| Ψ |> {{ v, Φ v ; f' }}.
  Proof.
    iIntros (Hfuncs) "HΦ".
    iIntros (LI Hfill).
    apply lfilled_swap with (es':=[AI_invoke a]) in Hfill as Hfill'.
    destruct Hfill' as [LI' Hfill'].
    iApply ewp_lift_step.
    { apply eq_None_not_Some.
      intros Hcontr.
      eapply lfilled_to_val in Hcontr;[|eauto].
      inversion Hcontr.
      done. }
    { apply eq_None_not_Some.
      intros Hcontr.
      eapply lfilled_to_eff in Hcontr; last eauto.
      destruct Hcontr => //. 
      inversion H.
      done. } 
    iIntros (?) "(Hσ1&Hσ2&Hσ3&Hσ4&?&?&Hσ5&Hσ6)".
    iApply fupd_frame_l.
    iSplit.
    - iPureIntro.
      unfold language.reducible, language.prim_step => /=.
      eexists [], _, (_,_,_), [].
      unfold iris.prim_step => /=.
      repeat split => //. eapply r_label.
      apply r_call. rewrite /= nth_error_lookup //. eauto. eauto.
    - iApply fupd_mask_intro;[solve_ndisj|].
      iIntros "Hcls !>" (es1 ??? HStep).
      iMod "Hcls". iModIntro.
      destruct HStep as (H & _).
      assert (first_instr LI = Some (AI_basic (BI_call i),0 + j)).
      { eapply starts_with_lfilled;eauto. auto. }
      eapply reduce_det in H as HH;[|eapply r_label;[|eauto..];apply r_call; rewrite /= nth_error_lookup //]. 
      destruct HH as [Hfeq [HH | [[? Hstart] | (?&?&? & Hstart & Hstart1 & Hstart2 & Hσ)  ]]]; try done; try congruence.
      inversion Hfeq; subst; destruct HH as [<- <-].
      destruct f0; iFrame.
      iApply ("HΦ" with "[]"). done. 
  Qed.
  Lemma ewp_call (E : coPset) Ψ (Φ : val -> iProp Σ) f0 f' (i : nat) a :
    (inst_funcs (f_inst f0)) !! i = Some a -> 
    ▷ (EWP [AI_invoke a] UNDER f0 @ E <| Ψ |> {{ v, Φ v ; f' }}) -∗
     EWP [AI_basic (BI_call i)] UNDER f0 @ E <| Ψ |> {{ v, Φ v ; f' }}.
  Proof.
    iIntros (Hfuncs) "HΦ".
    iApply ewp_wasm_empty_ctx.
    iApply ewp_call_ctx. eauto.
    iNext. 
    iApply ewp_wasm_empty_ctx.
    iApply "HΦ".
  Qed. 

  Lemma ewp_call_indirect_success_ctx (E : coPset) Ψ (Φ : val -> iProp Σ) (f0 : frame) f' i j a c cl d lh :
    stypes (f_inst f0) i = Some (cl_type cl) ->
    (inst_tab (f_inst f0)) !! 0 = Some j-> 
    (N.of_nat j) ↦[wt][N.of_nat (Wasm_int.nat_of_uint i32m c)] (Some a) -∗
    (N.of_nat a) ↦[wf] cl -∗
        ▷ ((N.of_nat j) ↦[wt][N.of_nat (Wasm_int.nat_of_uint i32m c)] (Some a)
             -∗ (N.of_nat a) ↦[wf] cl
                -∗ EWP [AI_invoke a] UNDER f0 @ E CTX d; lh <| Ψ |> {{ v, Φ v ; f' }}) -∗
    EWP [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i)] UNDER f0 @ E CTX d; lh <| Ψ |> {{ v, Φ v ; f' }}.
  Proof.
    iIntros (Htype Hc) "Ha Hcl Hcont".
    iIntros (LI Hfill).
    apply lfilled_swap with (es':=[AI_invoke a]) in Hfill as Hfill'.
    destruct Hfill' as [LI' Hfill'].
    iApply ewp_lift_step.
    { apply eq_None_not_Some.
      intros Hcontr.
      eapply lfilled_to_val in Hcontr;[|eauto].
      inversion Hcontr.
      done. }
    { apply eq_None_not_Some.
      intros Hcontr.
      eapply lfilled_to_eff in Hcontr => //.
      destruct Hcontr => //.
      inversion H => //. } 
    iIntros (?) "(Hσ1&?&?&Hσ2&Hσ3&Hσ4&Hσ5&Hσ6)".
    iApply fupd_frame_l.
    iDestruct (gen_heap_valid with "Hσ2 Ha") as %Hlook.
    iDestruct (gen_heap_valid with "Hσ1 Hcl") as %Hlook2.
    simplify_lookup.
    rewrite gmap_of_list_lookup Nat2N.id in Hlook2. 
    eassert (reduce _ {| f_locs := _; f_inst := _ |}
           [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i)] _ {| f_locs := _; f_inst := _ |}
           [AI_invoke a]) as Hred.
    { eapply r_call_indirect_success;eauto.
      - unfold stab_addr. simpl.
        destruct (inst_tab (f_inst f0)) => //.
        inversion Hc; subst t. 
        unfold stab_index. rewrite nth_error_lookup.
        apply list_lookup_fmap_inv in Heq as [ti [Hti Heq]].
        erewrite Heq. rewrite /= nth_error_lookup. subst.
        by rewrite Hlook /=. 
      - rewrite nth_error_lookup. eauto. }
    iSplit.
    - iPureIntro.
      unfold language.reducible, language.prim_step => /=.
      eexists [], _, (_,_,_), [].
      unfold iris.prim_step => /=.
      repeat split => //.
      eapply r_label;eauto.
    - iApply fupd_mask_intro;[solve_ndisj|].
      iIntros "Hcls !>" (es1 ??? HStep).
      iMod "Hcls". iModIntro.
      destruct HStep as (H & _).
      eassert (reduce _ {| f_locs := _; f_inst := _ |} LI _ {| f_locs := _; f_inst := _ |} LI') as Hred'.
      { eapply r_label. exact Hred. done. done. }
      eapply reduce_det in H as HH;[|apply Hred'].
      assert (first_instr LI = Some (AI_basic (BI_call_indirect i),0+d)).
      { eapply starts_with_lfilled;eauto. by cbn. }
      destruct HH as [Hfeq [HH | [[? Hstart] | (?&?&? & Hstart & Hstart1 & Hstart2 & Hσ)  ]]]; try done; try congruence.
      inversion Hfeq; subst; destruct HH as [<- <-]. iFrame.
      iSpecialize ("Hcont" with "[$] [$]").
      iSpecialize ("Hcont" $! _ Hfill'). destruct f0; iFrame.      
  Qed.
  
  Lemma ewp_call_indirect_success (E : coPset) Ψ (Φ : val -> iProp Σ) (f0 : frame) f' i j a c cl :
    stypes (f_inst f0) i = Some (cl_type cl) ->
    (inst_tab (f_inst f0)) !! 0 = Some j-> 
    (N.of_nat j) ↦[wt][N.of_nat (Wasm_int.nat_of_uint i32m c)] (Some a) -∗
    (N.of_nat a) ↦[wf] cl -∗
       ▷ ((N.of_nat j) ↦[wt][N.of_nat (Wasm_int.nat_of_uint i32m c)] (Some a)
          -∗ (N.of_nat a) ↦[wf] cl -∗
                                      EWP [AI_invoke a] UNDER f0 @ E <| Ψ |> {{ v, Φ v ; f'}}) -∗
    EWP [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i)] UNDER f0 @ E <| Ψ |> {{ v, Φ v ;f' }}.
  Proof.
    iIntros (? ?) "? ? H".
    iApply ewp_wasm_empty_ctx.
    iApply (ewp_call_indirect_success_ctx with "[$] [$]");eauto.
    iNext. iIntros "? ?".
    iApply ewp_wasm_empty_ctx.
    iApply ("H" with "[$] [$]").
  Qed.

  Lemma ewp_call_indirect_failure_types (E : coPset) Ψ (Φ : val -> iProp Σ) (f0 : frame) i j a c cl Φf:
    stypes (f_inst f0) i <> Some (cl_type cl) ->
    (inst_tab (f_inst f0)) !! 0 = Some j -> 
    (N.of_nat j) ↦[wt][N.of_nat (Wasm_int.nat_of_uint i32m c)] (Some a) -∗
    (N.of_nat a) ↦[wf] cl -∗
                             ▷ (Φ trapV) -∗ ▷ Φf f0 -∗
    EWP [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i)] UNDER f0 @ E <| Ψ |> {{ v, Φ v ∗ (N.of_nat j) ↦[wt][N.of_nat (Wasm_int.nat_of_uint i32m c)] (Some a)
                                                                                          ∗ (N.of_nat a) ↦[wf] cl ; Φf }}.
  Proof.
    iIntros (Htype Hc) "Ha Hcl Hcont Hf".
    iApply ewp_lift_atomic_step => //.
    iIntros (?) "(Hσ1&?&?&Hσ2&Hσ3&Hσ4&Hσ5&Hσ6)".
    iApply fupd_frame_l.
    iDestruct (gen_heap_valid with "Hσ2 Ha") as %Hlook.
    iDestruct (gen_heap_valid with "Hσ1 Hcl") as %Hlook2.
    simplify_lookup.
    rewrite gmap_of_list_lookup Nat2N.id in Hlook2. 
    eassert (reduce _ {| f_locs := _; f_inst := _ |}
           [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i)] _ {| f_locs := _; f_inst := _ |}
           [AI_trap]) as Hred.
    { eapply r_call_indirect_failure1.
      { unfold stab_addr. instantiate (1:=a). simpl. instantiate (2 := f_inst f0).
        destruct (inst_tab (f_inst f0)) => //. simpl in *. inversion Hc.
        unfold stab_index. rewrite nth_error_lookup.
        apply list_lookup_fmap_inv in Heq as [ti [Hti Heq]].
        erewrite Heq. rewrite /= nth_error_lookup. subst.
        by rewrite Hlook /=. }
      { rewrite nth_error_lookup. eauto. }
      { simpl in *. done. } } 
    iSplit.
    - iPureIntro.
      unfold language.reducible, language.prim_step => /=.
      eexists [], _, (_,_,_), [].
      unfold iris.prim_step => /=.
      repeat split => //.
    - iApply fupd_mask_intro;[solve_ndisj|].
      iIntros "Hcls !>" (es1 ??? HStep).
      iMod "Hcls". iModIntro.
      destruct HStep as (H & _).
      eapply reduce_det in H as HH;[|apply Hred].
      destruct HH as [Hfq [HH | [[? Hstart] |  (?&?&? & Hstart & Hstart1 & Hstart2 & Hσ) ]]]; try done; try congruence.
      inversion Hfq; subst; destruct HH as [<- <-].
      iFrame.  by destruct f0.
  Qed.


  Lemma ewp_call_indirect_failure_notable (E : coPset) Ψ (Φ : val -> iProp Σ) (f0 : frame) i c Φf :
    (inst_tab (f_inst f0)) !! 0 = None -> (* no function table *)
    
    ▷ (Φ trapV) -∗ ▷ Φf f0 -∗
    EWP [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i)] UNDER f0 @ E <| Ψ |> {{ v, Φ v ; Φf }}.
  Proof.
    iIntros (Hc) "Hcont Hf".
    iApply ewp_lift_atomic_step => //.
    iIntros (?) "Hσ".
    iApply fupd_frame_l.
    eassert (reduce _ {| f_locs := _; f_inst := _ |}
           [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i)] _ {| f_locs := _; f_inst := _ |}
           [AI_trap]) as Hred.
    { eapply r_call_indirect_failure2.
      unfold stab_addr. simpl. instantiate (2 := f_inst f0).
      destruct (inst_tab (f_inst f0));[done|]. inversion Hc. }
    iSplit.
    - iPureIntro.
      unfold language.reducible, language.prim_step => /=.
      eexists [], _, (_,_,_), [].
      unfold iris.prim_step => /=.
      repeat split => //.
    - iApply fupd_mask_intro;[solve_ndisj|].
      iIntros "Hcls !>" (es1 ??? HStep).
      iMod "Hcls". iModIntro.
      destruct HStep as (H & _).
      eapply reduce_det in H as HH;[|apply Hred].
      destruct HH as [Hfq [HH | [[? Hstart] | (?&?&? & Hstart & Hstart1 & Hstart2 & Hσ) ]]]; try done; try congruence.
      inversion Hfq; subst; destruct HH as [<- <-]. iFrame.  by destruct f0.
  Qed.

  Lemma ewp_call_indirect_failure_noindex (E : coPset) Ψ (Φ : val -> iProp Σ) (f0 : frame) i j c Φf:
    (inst_tab (f_inst f0)) !! 0 = Some j -> (* current frame points to correct table *)
    (N.of_nat j) ↦[wt][N.of_nat (Wasm_int.nat_of_uint i32m c)] None -∗ (* but no index i *)
    
    ▷ (Φ trapV) -∗ ▷ Φf f0 -∗
    EWP [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i)] UNDER f0 @ E <| Ψ |> {{ v, Φ v ∗ (N.of_nat j) ↦[wt][N.of_nat (Wasm_int.nat_of_uint i32m c)] None; Φf }}.
  Proof.
    iIntros (Hc) "Ha Hcont Hf".
    iApply ewp_lift_atomic_step => //.
    iIntros (?) "(Hσ1&?&?&Hσ2&Hσ3&Hσ4&Hσ5&Hσ6)".
    iApply fupd_frame_l.
    iDestruct (gen_heap_valid with "Hσ2 Ha") as %Hlook.
    simplify_lookup.
    eassert (reduce _ {| f_locs := _; f_inst := _ |}
           [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i)] _ {| f_locs := _; f_inst := _ |}
           [AI_trap]) as Hred.
    { eapply r_call_indirect_failure2.
      { unfold stab_addr. simpl. instantiate (2 := f_inst f0).
        destruct (inst_tab $ f_inst f0);[done|]. inversion Hc.
        unfold stab_index. rewrite nth_error_lookup.
        apply list_lookup_fmap_inv in Heq as [ti [Hti Heq]].
        erewrite Heq. rewrite /= nth_error_lookup. subst.
        by rewrite Hlook /=. } }
    iSplit.
    - iPureIntro.
      unfold language.reducible, language.prim_step => /=.
      eexists [], _, (_,_,_), [].
      unfold iris.prim_step => /=.
      repeat split => //.
    - iApply fupd_mask_intro;[solve_ndisj|].
      iIntros "Hcls !>" (es1 ??? HStep).
      iMod "Hcls". iModIntro.
      destruct HStep as (H & _).
      eapply reduce_det in H as HH;[|apply Hred].
      destruct HH as [Hfq [HH | [[? Hstart] | (?&?&? & Hstart & Hstart1 & Hstart2 & Hσ) ]]]; try done; try congruence.
      inversion Hfq; subst; destruct HH as [<- <-].
      iFrame. by destruct f0.
  Qed.

  Lemma ewp_call_indirect_failure_outofbounds (E : coPset) Ψ (Φ : val -> iProp Σ) (f0 : frame) i j c max Φf :
    (inst_tab (f_inst f0)) !! 0 = Some j -> (* current frame points to correct table *)
    max <= (Wasm_int.nat_of_uint i32m c) ->
    (N.of_nat j) ↪[wtsize] max -∗ (* but is out of bounds *)
        ▷ (Φ trapV) -∗ ▷ Φf f0 -∗
    EWP [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i)] UNDER f0 @ E <| Ψ |> {{ v, Φ v; Φf }}.
  Proof.
    iIntros (Hc Hge) "#Ha Hcont Hf".
    iApply ewp_lift_atomic_step => //.
    iIntros (?) "(Hσ1&?&?&Hσ2&Hσ3&Hσ4&Hσ5&Hσ6&Hσ7&Hσ8)".
    iApply fupd_frame_l.
    iDestruct (gen_heap_valid with "Hσ6 Ha") as %Hlook.
    rewrite gmap_of_list_lookup Nat2N.id in Hlook.
    rewrite list_lookup_fmap in Hlook.
    simplify_map_eq.
    apply fmap_Some_1 in Hlook as [tbli [Hlook Hsize]].
    simplify_eq.
    apply lookup_ge_None_2 in Hge.
    
    
    eassert (reduce _ {| f_locs := _; f_inst := _ |}
           [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i)] _ {| f_locs := _; f_inst := _ |}
           [AI_trap]) as Hred.
    { eapply r_call_indirect_failure2.
      { unfold stab_addr. simpl. instantiate (2 := f_inst f0).
        destruct (inst_tab $ f_inst f0) => //. inversion Hc; subst. 
        unfold stab_index. rewrite nth_error_lookup. simplify_eq.
        erewrite Hlook. simpl. rewrite nth_error_lookup Hge. done. } }
    iSplit.
    - iPureIntro.
      
      unfold language.reducible, language.prim_step => /=.
      eexists [], _, (_,_,_), [].
      unfold iris.prim_step => /=.
      repeat split => //.
    - iApply fupd_mask_intro;[solve_ndisj|].
      iIntros "Hcls !>" (es1 ??? HStep).
      iMod "Hcls". iModIntro.

      destruct HStep as (H & _).
      eapply reduce_det in H as HH;[|apply Hred].
      destruct HH as [Hfq [HH | [[? Hstart] | (?&?&? & Hstart & Hstart1 & Hstart2 & Hσ) ]]]; try done; try congruence.
      simplify_eq. destruct HH as [<- <-]. iFrame. destruct f0 => //. 
  Qed.


  Lemma ewp_ref_func f k i E Ψ Φ Φf:
    f.(f_inst).(inst_funcs) !! k = Some i ->
     ▷ Φ (immV [VAL_ref (VAL_ref_func i)]) ∗ ▷ Φf f 
      ⊢ EWP [AI_basic (BI_ref_func k)] UNDER f @ E <| Ψ |> {{ v, Φ v; Φf }}.
  Proof.
    iIntros (Hk) "[HΦ Hf]".
    iApply ewp_lift_atomic_step => //=.
    iIntros (σ) "Hσ".
    iModIntro.
    iSplit.
    { iPureIntro. eexists _,_,(_,_,_),_.
      repeat split => //.
      apply r_ref_func.
      rewrite nth_error_lookup => //. }
    iIntros "!>" (e2 ??? HStep).
    iModIntro.
    destruct HStep as (Hred & _).
    edestruct reduce_det.
    exact Hred. apply r_ref_func. rewrite nth_error_lookup //.
    destruct H0 as [[-> ->] | ?].
    - inversion H; subst. iFrame. by destruct f. 
    - rewrite /first_instr /= in H.
      destruct H0 as [[??] | (?&?&?&?&_)] => //.
  Qed.

    Lemma ewp_call_reference_ctx (E : coPset) Ψ (Φ : val -> iProp Σ) f f' i a j lh tf cl:
      stypes f.(f_inst) i = Some tf ->
      cl_type cl = tf ->
    N.of_nat a ↦[wf] cl -∗
     ▷ (N.of_nat a ↦[wf] cl -∗ EWP [AI_invoke a] UNDER f @ E CTX j; lh <| Ψ |> {{ v, Φ v ; f' }}) -∗
     EWP [AI_ref a; AI_basic (BI_call_reference i)] UNDER f @ E CTX j; lh <| Ψ |> {{ v, Φ v ; f'}}.
  Proof.
    iIntros (Hi Hcl) "Ha HΦ".
    iIntros (LI Hfill).
    apply lfilled_swap with (es':=[AI_invoke a]) in Hfill as Hfill'.
    destruct Hfill' as [LI' Hfill'].
    iApply ewp_lift_step.
    { apply eq_None_not_Some.
      intros Hcontr.
      eapply lfilled_to_val in Hcontr;[|eauto].
      inversion Hcontr.
      done. }
    { apply eq_None_not_Some.
      intros Hcontr.
      eapply lfilled_to_eff in Hcontr; last eauto.
      destruct Hcontr => //. 
      inversion H.
      done. } 
    iIntros (?) "(Hσ1&Hσ2&Hσ3&Hσ4&?&?&Hσ5&Hσ6)".
    iDestruct (gen_heap_valid with "Hσ1 Ha") as %Ha.
    rewrite gmap_of_list_lookup in Ha.
    rewrite -nth_error_lookup Nat2N.id in Ha.
    iApply fupd_frame_l.
    iSplit.
    - iPureIntro.
      unfold language.reducible, language.prim_step => /=.
      eexists [], _, (_,_,_), [].
      unfold iris.prim_step => /=.
      repeat split => //. eapply r_label.
      eapply r_call_reference. done. simpl. erewrite Hi. by subst tf. done. done. 
    - iApply fupd_mask_intro;[solve_ndisj|].
      iIntros "Hcls !>" (es1 ??? HStep).
      iMod "Hcls". iModIntro.
      destruct HStep as (H & _).
      assert (first_instr LI = Some (AI_basic (BI_call_reference i),0 + j)).
      { eapply starts_with_lfilled;eauto. auto. }
      eapply reduce_det in H as HH;[|eapply r_label;[|eauto..];eapply r_call_reference => //].
      destruct HH as [Hfq [HH | [[? Hstart] | (?&?&? & Hstart & Hstart1 & Hstart2 & Hσ)  ]]]; try done; try congruence.
      simplify_eq. destruct HH as [-> ->]. iFrame.
      destruct f;
        iApply ("HΦ" with "[$]"). auto.
      simpl. by subst.
  Qed.
  Lemma ewp_call_reference (E : coPset) Ψ (Φ : val -> iProp Σ) f f' i a tf cl:
      stypes f.(f_inst) i = Some tf ->
      cl_type cl = tf ->
    N.of_nat a ↦[wf] cl -∗
     ▷ (N.of_nat a ↦[wf] cl -∗ EWP [AI_invoke a] UNDER f @ E <| Ψ |> {{ v, Φ v ; f' }}) -∗
     EWP [AI_ref a; AI_basic (BI_call_reference i)] UNDER f @ E <| Ψ |> {{ v, Φ v ; f'}}.
  Proof.
    iIntros (Hi Hcl) "Ha HΦ".
    iApply ewp_wasm_empty_ctx.
    iApply (ewp_call_reference_ctx with "[$]"). eauto. eauto.
    iNext. iIntros "?".
    iApply ewp_wasm_empty_ctx.
    iApply ("HΦ" with "[$]").
  Qed.
  
  

End iris_rules_calls.
