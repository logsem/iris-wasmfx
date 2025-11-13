

(* This theory introduces the basic principles that allow reasoning in terms
   of [EWP]. The most important principles in this theory are the bind rule,
   which endorses modular reasoning about the evaluation context by allowing
   one to compose specifications; and the frame rule, which endorses modular
   reasoning about the state by allowing one to derive specifications with
   a larger footprint than their original statement. *)


From iris.proofmode Require Import base tactics classes.
From iris.program_logic Require Import weakestpre.
From Wasm.iris.language Require Import iris_ewp_ctx.
From Wasm.iris.helpers Require Import iris_properties.
From Wasm.iris.rules Require Import iris_rules_exceptions.
From stdpp Require Import base list.
From mathcomp Require Import ssreflect eqtype seq ssrbool.





Set Bullet Behavior "Strict Subproofs".
Close Scope byte_scope.

Section clause_triple.
  Context `{!wasmG Σ}.


  Definition is_empty_frame : frame -> iProp Σ :=
    λ f, ⌜ f = empty_frame ⌝%I.

  (* ts is the return type of the continuation *)
  Definition clause_triple E Ψ Φ dcc ts Ψ' Φ': iProp Σ :=
    match dcc with
    | DC_catch (Mk_tagidx taddr) ilab =>
        ∃ t1s t2s q,
    N.of_nat taddr ↦[tag]{q} Tf t1s t2s ∗
      ∀ vs kaddr h,
        N.of_nat taddr ↦[tag]{q} Tf t1s t2s -∗
        N.of_nat kaddr ↦[wcont] Live (Tf t2s ts) h -∗
        iProt_car (upcl $ get_suspend (Mk_tagidx taddr) Ψ) vs (λ w, ∃ LI, ⌜ is_true $ hfilled No_var (hholed_of_valid_hholed h) (v_to_e_list w) LI ⌝ ∗ ▷ (* no calling continuations in wasm, so adding this later to symbolise that step *) EWP LI UNDER empty_frame @ E <| Ψ |> {{ Φ }}) -∗
            EWP v_to_e_list vs ++ [AI_ref_cont kaddr; AI_basic (BI_br ilab)] UNDER empty_frame @ E <| Ψ' |> {{ Φ' }}
| DC_switch (Mk_tagidx taddr) =>
    ∃ q, N.of_nat taddr ↦[tag]{q} Tf [] ts ∗
       □
      ∀ vs kaddr h cont t1s tf',
      get_switch2 (Mk_tagidx taddr) Ψ cont -∗
      ⌜ tf' = Tf t1s ts ⌝ -∗
      (*N.of_nat taddr ↦[tag]{q} Tf [] ts -∗*)
      N.of_nat kaddr ↦[wcont] Live tf' h -∗
      iProt_car (upcl $ get_switch1 (Mk_tagidx taddr) Ψ) vs
      (λ w, ∃ LI,
        ⌜ is_true $ hfilled No_var (hholed_of_valid_hholed h) (v_to_e_list w) LI ⌝ ∗
        ▷ (* no calling continuations in wasm,
              so adding this later to symbolise that step *)
        EWP LI UNDER empty_frame @ E <| Ψ |> {{ Φ }}) -∗
        ∃ LI,
          ⌜ is_true $ hfilled No_var cont (v_to_e_list vs ++ [AI_ref_cont kaddr]) LI ⌝ ∗
            EWP LI UNDER empty_frame @ E <| Ψ |> {{ Φ }}
    end.

  

  Definition agree_on_uncaptured dccs (Ψ Ψ' : meta_protocol) : Prop :=
    (forall i, firstx_continuation_suspend dccs i = None ->
          get_suspend i Ψ = get_suspend i Ψ') /\
      (forall i, firstx_continuation_switch dccs i = false ->
            get_switch i Ψ = get_switch i Ψ') /\
      (forall i, get_throw i Ψ = get_throw i Ψ')
        .

End clause_triple.


(* ========================================================================== *)
(** * Reasoning Rules. *)

Section reasoning_rules.
  Context `{!wasmG Σ}.

  

  Lemma ewp_suspend_desugared vs i E Ψ Φ f:
    iProt_car (upcl (get_suspend i Ψ)) vs (λ v, ▷ Φ (immV v) f)
      ⊢ EWP [ AI_suspend_desugared vs i ] UNDER f @ E <| Ψ |> {{ v ; h , Φ v h }}.
  Proof.
    iIntros "HΨ".
    iApply ewp_effect_sus => //.
    iFrame.
    iApply (monotonic_prot with "[] HΨ").
    iIntros (w) "Hw".
    iSimpl.
    rewrite app_nil_r.
    replace (v_to_e_list w) with (of_val0 (immV w)) => //. 
    iApply ewp_value'.
    iFrame.
  Qed.

  Lemma ewp_switch_desugared vs k tf tf' t1s t2s ts i q E Ψ Φ f cont:
    is_true $ iris_lfilled_properties.constant_hholed (hholed_of_valid_hholed cont) ->
    tf' = Tf t1s ts ->
    tf = Tf (t1s ++ [T_ref (T_contref tf')]) t2s ->
    N.of_nat i ↦[tag]{q} Tf [] ts ∗
    N.of_nat k ↦[wcont] Live tf cont ∗
     get_switch2 (Mk_tagidx i) Ψ (hholed_of_valid_hholed cont) ∗
     (N.of_nat i ↦[tag]{q} Tf [] ts -∗ iProt_car (upcl (get_switch1 (Mk_tagidx i) Ψ)) vs (λ v, ▷ Φ (immV v) f))
      ⊢ EWP [ AI_switch_desugared vs k tf (Mk_tagidx i) ] UNDER f @ E <| Ψ |> {{ v ; h , Φ v h }}.
  Proof.
    iIntros (? -> ->) "(Htag & Hk & Hcont & HΨ)".
    iApply ewp_effect_sw => //.
    iFrame.
    iExists _,_,_.
    do 3 (iSplit; first done).
    iIntros "Htag".
    iPoseProof ("HΨ" with "Htag") as "HΨ".
    iApply (monotonic_prot with "[] HΨ").
    iIntros (w) "Hw".
    iSimpl.
    rewrite app_nil_r.
    replace (v_to_e_list w) with (of_val0 (immV w)) => //. 
    iApply ewp_value'.
    iFrame.
  Qed.

 

  Lemma ewp_suspend_desugar f ves vs i q x a t1s t2s E Ψ Φ:
    i = Mk_tagident x ->
    f.(f_inst).(inst_tags) !! x = Some a ->
    length vs = length t1s ->
    ves = v_to_e_list vs ->
    N.of_nat a ↦[tag]{q} Tf t1s t2s ∗
    ▷ (N.of_nat a ↦[tag]{q} Tf t1s t2s -∗ EWP [AI_suspend_desugared vs (Mk_tagidx a)] UNDER f @ E <| Ψ |> {{ v ; f , Φ v f }})
    ⊢ EWP ves ++ [AI_basic (BI_suspend i)] UNDER f @ E <| Ψ |> {{ v ; f , Φ v f }}.
  Proof.
    iIntros (-> Hx Hlen ->) "(Htag & H)".
    iApply ewp_lift_step.
    { rewrite to_val_cat_None2 => //.
      apply v_to_e_is_const_list. }
    { rewrite to_eff_cat_None2 => //.
      apply v_to_e_is_const_list. }
    iIntros (σ) "Hσ".
    iApply fupd_mask_intro; first solve_ndisj.
    iIntros "Hclose".

    iDestruct "Hσ" as "(Hfuncs & Hconts & Hexns & Htags & Hmems & Htabs & Hglobs & Hrest)".
    iDestruct (tag_valid with "Htags Htag") as "%Htag".
    rewrite gmap_of_list_lookup in Htag.
    rewrite Nat2N.id in Htag.
    iSplit.
    { iPureIntro.
      eexists _,(_,_),_,_.
      repeat split => //.
      eapply r_suspend_desugar => //.
      rewrite nth_error_lookup //.
      exact Hx.
      rewrite nth_error_lookup //.
      exact Htag.
      done.
    }
    iIntros "!>" (e2 ?? HStep).
    iMod "Hclose".
    iModIntro.

    destruct HStep as (Hred & _).
    edestruct reduce_det.
    exact Hred.
    eapply r_suspend_desugar => //; eauto.
    1-2: rewrite nth_error_lookup; eauto.
    destruct H0.
    - destruct H0 as [-> ->].
      destruct f; simpl in H; inversion H; subst. iFrame.
      iApply ("H" with "Htag").
    - destruct H0 as [[? H'] | (? & ? & ? & H' & _)].
      all: rewrite first_instr_const in H' => //.
      all: apply v_to_e_is_const_list.
  Qed.

   Lemma of_to_valid_hholed h h':
     valid_hholed_of_hholed h = Some h' -> hholed_of_valid_hholed h' = h.
   Proof.
     destruct h => //=.
     2:{ destruct l0 => //.
         destruct (e_to_v_list_opt l) eqn:Hl => //.
         intros H; inversion H; subst.
         simpl.
         apply v_to_e_e_to_v in Hl as ->.
         done. }
     destruct l0 => //.
     destruct a => //.
     destruct l0 => //.
     destruct a => //.
     destruct b => //.
     destruct t => //.
     destruct l0 => //.
     destruct (e_to_v_list_opt l) eqn:Hl => //.
     intros H; inversion H; subst.
     apply v_to_e_e_to_v in Hl as <-. 
     simpl. done.
   Qed.

  
     Lemma to_of_continuation_resource h h':
     resource_of_continuation h = Some h' -> continuation_of_resource h' = h.
   Proof.
     destruct h => //=.
     2: intros H; inversion H; subst => //.
     destruct (valid_hholed_of_hholed h) eqn:Hh => //.
     intros H; inversion H; subst.
     apply of_to_valid_hholed in Hh as <-.
     done.
   Qed.

     Lemma resources_of_s_cont_lookup conts l addr h:
      resources_of_s_cont conts = Some l ->
      nth_error l addr = Some h ->
      nth_error conts addr = Some (continuation_of_resource h).
   Proof.
     generalize dependent l. generalize dependent addr. 
     induction conts => //=.
     { rewrite /resources_of_s_cont /those /=. intros.
       inversion H; subst. 
       destruct addr => //. }
     intros addr l Hconts Hcont.
     unfold resources_of_s_cont in Hconts.
     simpl in Hconts.
     rewrite separate1 in Hconts.
     apply those_app_inv in Hconts as (l1 & l2 & Hl1 & Hl2 & <-).
     unfold those in Hl1. simpl in Hl1.
     destruct (resource_of_continuation a) eqn:Ha => //.
     simpl in Hl1. inversion Hl1; subst.
     destruct addr.
     { simpl in Hcont. inversion Hcont; subst.
       apply to_of_continuation_resource in Ha as ->.
       done. } 
     simpl. eapply IHconts => //. exact Hl2. exact Hcont.
   Qed.


  Lemma ewp_switch_desugar f ves vs k tf tf' i i' cont x a q t1s t2s E Ψ Φ:
    i = Mk_tagident x ->
    stypes (f_inst f) i' = Some tf ->
    f.(f_inst).(inst_tags) !! x = Some a ->
    typeof_cont (continuation_of_resource cont) = Tf t1s t2s ->
    S (length vs) = length t1s ->
    ves = v_to_e_list vs ->
    N.of_nat a ↦[tag]{q} tf' ∗
    N.of_nat k ↦[wcont] cont ∗
    ▷ ( N.of_nat a ↦[tag]{q} tf' -∗ N.of_nat k ↦[wcont] cont -∗ EWP [AI_switch_desugared vs k tf (Mk_tagidx a)] UNDER f @ E <| Ψ |> {{ v ; f , Φ v f }})
    ⊢ EWP ves ++ [AI_ref_cont k; AI_basic (BI_switch i' i)] UNDER f @ E <| Ψ |> {{ v ; f , Φ v f }}.
  Proof.
    iIntros (-> Hi' Hx Hcont Hlen ->) "(Htag & Hcont & H)".
    iApply ewp_lift_step.
    { rewrite to_val_cat_None2 => //.
      apply v_to_e_is_const_list. }
    { rewrite to_eff_cat_None2 => //.
      apply v_to_e_is_const_list. }
    iIntros (σ) "Hσ".
    iApply fupd_mask_intro; first solve_ndisj.
    iIntros "Hclose".

    iDestruct "Hσ" as "(Hfuncs & Hconts & Hexn & Htags & Hmems & Htabs & Hglobs & Hrest)".
    destruct (resources_of_s_cont (s_conts σ)) eqn:Hconts => //. 
    iDestruct (gen_heap_valid with "Hconts Hcont") as "%Hlook".
    rewrite gmap_of_list_lookup Nat2N.id in Hlook.
    rewrite - nth_error_lookup in Hlook.
    eapply resources_of_s_cont_lookup in Hlook as Hlook'; last exact Hconts.
    
    iDestruct (tag_valid with "Htags Htag") as "%Htag".
    rewrite gmap_of_list_lookup in Htag.
    rewrite Nat2N.id in Htag.
    iSplit.
    { iPureIntro.
      eexists _,(_,_),_,_.
      repeat split => //.
      eapply r_switch_desugar => //.
      exact Hi'. 
      rewrite nth_error_lookup //.
      exact Hx.
      rewrite nth_error_lookup //.
      exact Htag.
      exact Hlook'.
      exact Hcont. 
      done.
    }
    iIntros "!>" (e2 ?? HStep).
    iMod "Hclose".
    iModIntro.

    destruct HStep as (Hred & _).
    edestruct reduce_det.
    exact Hred.
    eapply r_switch_desugar => //; eauto.
    1-2: rewrite nth_error_lookup; eauto.
    destruct H0.
    - destruct H0 as [-> ->].
      destruct f; simpl in H; inversion H; subst. iFrame.
      rewrite Hconts. iFrame.
      iApply ("H" with "Htag Hcont").
    - destruct H0 as [[? H'] | (? & ? & ? & H' & _)].
      all: rewrite first_instr_const in H' => //.
      all: apply v_to_e_is_const_list.
  Qed.
 

  Lemma ewp_suspend f ves vs i q x a t1s t2s E Ψ Φ:
    i = Mk_tagident x ->
    f.(f_inst).(inst_tags) !! x = Some a ->
    length vs = length t1s ->
    ves = v_to_e_list vs ->
    N.of_nat a ↦[tag]{q} Tf t1s t2s ∗
    ▷ (N.of_nat a ↦[tag]{q} Tf t1s t2s -∗ iProt_car (upcl (get_suspend (Mk_tagidx a) Ψ)) vs (λ v, ▷ Φ (immV v) f))
    ⊢ EWP ves ++ [AI_basic (BI_suspend i)] UNDER f @ E <| Ψ |> {{ v ; f , Φ v f }}.
  Proof.
    iIntros (-> ?? ->) "(Htag & H)".
    iApply ewp_suspend_desugar => //; eauto.
    iFrame.
    iIntros "!> Htag".
    iApply ewp_suspend_desugared => //.
    iApply ("H" with "Htag").
  Qed.

   Lemma ewp_switch f ves vs i i' k x a q tf ts cont t1s t2s E Ψ Φ:
    i = Mk_tagident x ->
    tf = Tf t1s ts ->
    is_true $ iris_lfilled_properties.constant_hholed (hholed_of_valid_hholed cont) ->
    stypes (f_inst f) i' = Some (Tf (t1s ++ [T_ref (T_contref tf)]) t2s) ->
    f.(f_inst).(inst_tags) !! x = Some a ->
    length vs = length t1s ->
    ves = v_to_e_list vs ->
    N.of_nat a ↦[tag]{q} (Tf [] ts) ∗
    N.of_nat k ↦[wcont] Live (Tf (t1s ++ [T_ref (T_contref tf)]) t2s) cont ∗
    get_switch2 (Mk_tagidx a) Ψ (hholed_of_valid_hholed cont) ∗
    ▷ (N.of_nat a ↦[tag]{q} (Tf [] ts) -∗ iProt_car (upcl (get_switch1 (Mk_tagidx a) Ψ)) vs (λ v, ▷ Φ (immV v) f))
    ⊢ EWP ves ++ [AI_ref_cont k; AI_basic (BI_switch i' i)] UNDER f @ E <| Ψ |> {{ v ; f , Φ v f }}.
  Proof.
    iIntros (-> -> ???? ->) "(? & ? & ? & H)".
    iApply ewp_switch_desugar.
    7: iFrame.
    done. exact H0. exact H1.
    simpl. done.
    rewrite length_app //=.
    erewrite H2. lia.
    done.
    iIntros "!> Htag Hcont".
    iApply ewp_switch_desugared.
    exact H.
    3: iFrame.
    done. done.
  Qed.


  Lemma susE_first_instr es vs i sh :
    to_eff0 es = Some (susE vs i sh) ->
    exists k, first_instr es = Some (AI_suspend_desugared vs i, k).
  Proof.
    remember (S (length_rec es)) as m.
    assert (length_rec es < m); first by subst; lia.
    clear Heqm.
    generalize dependent sh.
    generalize dependent es.
    induction m => //.
    { intros es Hlen; lia. } 
    intros es Hlen sh.
    destruct es => //. 
    unfold to_eff0 => //=.
    rewrite merge_prepend.
    destruct (to_val_instr a) eqn:Ha => //.
    - destruct v => //=.
      + unfold to_eff0 in IHm.
        specialize (IHm es).
        destruct (merge_values _) => //.
        * destruct v => //. destruct l => //.
        * destruct e => //.
          intros H; inversion H; subst; clear H.
          edestruct IHm as [k Hes] => //.
          specialize (length_cons_rec a es). lia.
          unfold first_instr.
          simpl.
          unfold first_instr in Hes.
          rewrite Hes.
          destruct a => //=.
          destruct b => //=.
          all: try by eexists.
          all: simpl in Ha.
          all: destruct (merge_values _) => //.
          all: try by destruct v => //.
          all: try destruct e => //.
          destruct (exnelts_of_exception_clauses _ _) => //.
          destruct (suselts_of_continuation_clauses _ _) => //.
          destruct (swelts_of_continuation_clauses _ _) => //.
          destruct v => //.
          destruct i0 => //.
          destruct (vh_decrease _) => //.
      + destruct (expr_of_val_not_val _) => //.
    - destruct e => //.
      simpl.
      intros H; inversion H; subst; clear H.
      destruct a => //=.
      + destruct b => //=.
      + simpl in Ha. inversion Ha; subst. by eexists.
      + simpl in Ha.
        specialize (Logic.eq_refl (to_eff0 l0)) as Heq.
        unfold to_eff0 in Heq at 2.
        destruct (merge_values _) => //.
        destruct v => //.
        destruct e => //.
        2: destruct (exnelts_of_exception_clauses _ _) => //.
        inversion Ha; subst.
        apply IHm in Heq as [k Hk].
        unfold first_instr.
        unfold first_instr in Hk.
        simpl.
        rewrite Hk.
        by eexists.
        unfold length_rec in Hlen.
        unfold length_rec.
        simpl in Hlen. lia.
      + simpl in Ha.
        specialize (Logic.eq_refl (to_eff0 l1)) as Heq.
        unfold to_eff0 in Heq at 2.
        destruct (merge_values _) => //.
        destruct v => //.
        destruct e => //.
        destruct suselts_of_continuation_clauses => //.
        2: destruct (swelts_of_continuation_clauses _ _) => //.
        inversion Ha; subst.
        apply IHm in Heq as [k Hk].
        unfold first_instr.
        unfold first_instr in Hk.
        simpl.
        rewrite Hk.
        by eexists.
        unfold length_rec in Hlen.
        unfold length_rec.
        simpl in Hlen. lia.
      + simpl in Ha.
        specialize (Logic.eq_refl (to_eff0 l0)) as Heq.
        unfold to_eff0 in Heq at 2.
        destruct (merge_values _) => //.
        destruct v => //.
        2: destruct e => //.
        destruct i0 => //.
        destruct (vh_decrease _) => //. 
        inversion Ha; subst.
        apply IHm in Heq as [k Hk].
        unfold first_instr.
        unfold first_instr in Hk.
        simpl.
        rewrite Hk.
        by eexists.
        unfold length_rec in Hlen.
        unfold length_rec.
        simpl in Hlen. lia.
      + simpl in Ha.
        specialize (Logic.eq_refl (to_eff0 l)) as Heq.
        unfold to_eff0 in Heq at 2.
        destruct (merge_values _) => //.
        destruct v => //.
        destruct e => //.
        inversion Ha; subst.
        apply IHm in Heq as [k Hk].
        unfold first_instr.
        unfold first_instr in Hk.
        simpl.
        rewrite Hk.
        by eexists.
        unfold length_rec in Hlen.
        unfold length_rec.
        simpl in Hlen. lia.
  Qed.

  Lemma swE_first_instr es vs k tf i sh :
    to_eff0 es = Some (swE vs k tf i sh) ->
    exists k', first_instr es = Some (AI_switch_desugared vs k tf i, k').
  Proof.
    remember (S (length_rec es)) as m.
    assert (length_rec es < m); first by subst; lia.
    clear Heqm.
    generalize dependent sh.
    generalize dependent es.
    induction m => //.
    { intros es Hlen; lia. } 
    intros es Hlen sh.
    destruct es => //. 
    unfold to_eff0 => //=.
    rewrite merge_prepend.
    destruct (to_val_instr a) eqn:Ha => //.
    - destruct v => //=.
      + unfold to_eff0 in IHm.
        specialize (IHm es).
        destruct (merge_values _) => //.
        * destruct v => //. destruct l => //.
        * destruct e => //.
          intros H; inversion H; subst; clear H.
          edestruct IHm as [k0 Hes] => //.
          specialize (length_cons_rec a es). lia.
          unfold first_instr.
          simpl.
          unfold first_instr in Hes.
          rewrite Hes.
          destruct a => //=.
          destruct b => //=.
          all: try by eexists.
          all: simpl in Ha.
          all: destruct (merge_values _) => //.
          all: try by destruct v => //.
          all: try destruct e => //.
          destruct (exnelts_of_exception_clauses _ _) => //.
          destruct (suselts_of_continuation_clauses _ _) => //.
          destruct (swelts_of_continuation_clauses _ _) => //.
          destruct v => //.
          destruct i0 => //.
          destruct (vh_decrease _) => //.
      + destruct (expr_of_val_not_val _) => //.
    - destruct e => //.
      simpl.
      intros H; inversion H; subst; clear H.
      destruct a => //=.
      + destruct b => //=.
      + simpl in Ha. inversion Ha; subst. by eexists.
      + simpl in Ha.
        specialize (Logic.eq_refl (to_eff0 l0)) as Heq.
        unfold to_eff0 in Heq at 2.
        destruct (merge_values _) => //.
        destruct v => //.
        destruct e => //.
        2: destruct (exnelts_of_exception_clauses _ _) => //.
        inversion Ha; subst.
        apply IHm in Heq as [k0 Hk].
        unfold first_instr.
        unfold first_instr in Hk.
        simpl.
        rewrite Hk.
        by eexists.
        unfold length_rec in Hlen.
        unfold length_rec.
        simpl in Hlen. lia.
      + simpl in Ha.
        specialize (Logic.eq_refl (to_eff0 l1)) as Heq.
        unfold to_eff0 in Heq at 2.
        destruct (merge_values _) => //.
        destruct v => //.
        destruct e => //.
        destruct suselts_of_continuation_clauses => //.
        destruct (swelts_of_continuation_clauses _ _) => //.
        inversion Ha; subst.
        apply IHm in Heq as [k0 Hk].
        unfold first_instr.
        unfold first_instr in Hk.
        simpl.
        rewrite Hk.
        by eexists.
        unfold length_rec in Hlen.
        unfold length_rec.
        simpl in Hlen. lia.
      + simpl in Ha.
        specialize (Logic.eq_refl (to_eff0 l0)) as Heq.
        unfold to_eff0 in Heq at 2.
        destruct (merge_values _) => //.
        destruct v => //.
        2: destruct e => //.
        destruct i0 => //.
        destruct (vh_decrease _) => //. 
        inversion Ha; subst.
        apply IHm in Heq as [k0 Hk].
        unfold first_instr.
        unfold first_instr in Hk.
        simpl.
        rewrite Hk.
        by eexists.
        unfold length_rec in Hlen.
        unfold length_rec.
        simpl in Hlen. lia.
      + simpl in Ha.
        specialize (Logic.eq_refl (to_eff0 l)) as Heq.
        unfold to_eff0 in Heq at 2.
        destruct (merge_values _) => //.
        destruct v => //.
        destruct e => //.
        inversion Ha; subst.
        apply IHm in Heq as [k0 Hk].
        unfold first_instr.
        unfold first_instr in Hk.
        simpl.
        rewrite Hk.
        by eexists.
        unfold length_rec in Hlen.
        unfold length_rec.
        simpl in Hlen. lia.
  Qed.

  

  Lemma desugar_exception_clauses_empty_frame cs csd f:
    seq.map (desugar_exception_clause (f_inst empty_frame)) cs = seq.map Some csd ->
    seq.map (desugar_exception_clause (f_inst f)) cs = seq.map Some csd.
  Proof.
    generalize dependent csd.
    induction cs => //=.
    destruct a => //=.
    - destruct t => //=.
      destruct i0, csd => //=.
    - destruct t => //=.
      destruct i0, csd => //.
    - destruct csd => //=.
      intros H; inversion H.
      rewrite H2.
      erewrite IHcs => //. 
    - destruct csd => //=.
      intros H; inversion H.
      rewrite H2.
      erewrite IHcs => //.
  Qed.

    Lemma desugar_continuation_clauses_empty_frame cs csd f:
    seq.map (desugar_continuation_clause (f_inst empty_frame)) cs = seq.map Some csd ->
    seq.map (desugar_continuation_clause (f_inst f)) cs = seq.map Some csd.
  Proof.
    generalize dependent csd.
    induction cs => //=.
    destruct a => //=.
    - destruct t => //=.
      destruct i0, csd => //=.
    - destruct t => //.
      destruct i, csd => //. 
  Qed.

  Lemma reduce_stays_empty_frame s es s' f' es':
    reduce s empty_frame es s' f' es' -> f' = empty_frame.
  Proof.
    intros H.
    remember empty_frame as f.
    induction H.
    all: try done.
    all: subst. destruct i => //.
    by apply IHreduce.
  Qed.


  Definition continuation_expr es : Prop :=
    (exists vs i tf, es = v_to_e_list vs ++ [ AI_ref i; AI_basic (BI_call_reference (Type_explicit tf))]) \/
      (exists vs i , es = v_to_e_list vs ++ [ AI_invoke i ] ) \/
      (exists vs n f es0, es = v_to_e_list vs ++ [AI_frame n f es0]) \/
      (exists vs, es = v_to_e_list vs ++ [AI_trap]) \/
      is_true (const_list es) \/
      (exists vs vs' k tf, es = v_to_e_list vs ++ [AI_call_host vs' k tf])       
  .


  Lemma continuation_expr_prepend vs es :
    is_true (const_list vs) -> continuation_expr es -> continuation_expr (vs ++ es).
  Proof.
    intros Hvs Hes.
    apply const_es_exists in Hvs as Hvs'.
    destruct Hvs' as [vs'' ->].
    destruct Hes as [(vs' & i & tf & ->) | [(vs' & i & ->) | [(vs' & n & f0 & es0 & ->) | [(vs' & ->) | [Hes | (vs & vs' & k & tf & ->)]]]]].  
    1-4,6: rewrite catA.
    1-5: rewrite v_to_e_cat.
    by left; repeat eexists.
    by right; left; repeat eexists.
    by right; right; left; repeat eexists.
    by right; right; right; left; repeat eexists.
    by right; right; right; right; right; repeat eexists.
    by right; right; right; right; left; apply const_list_concat => //.
  Qed. 
    

  Lemma continuation_preservation s f es s' f' es' :
    reduce s f es s' f' es' ->
    continuation_expr es ->
    continuation_expr es'.
  Proof.
    intros Hred Hes.
    destruct Hes as [(vs & i & tf & ->) | [(vs & i & ->) | [(vs & n & f0 & es0 & ->) | [(vs & ->) | [Hes |  (vs & vs' & k & tf & ->)]]]]].  
    - remember (S $ length vs) as m.
      assert (length vs < m) as Hm; first lia.
      clear Heqm.
      generalize dependent vs; generalize dependent es'.
      induction m; first lia.
      intros.
      rewrite separate1 cat_app app_assoc in Hred.
      remember ((v_to_e_list vs ++ [AI_ref i]) ++
                  [AI_basic (BI_call_reference (Type_explicit tf))])%list as es.
 
      
      induction Hred.
      inversion H.
      all: remember Heqes as Heq; clear HeqHeq Heqes.
      all: subst.
      all: try by do 2 (destruct vs => //). 
      all: try by rewrite separate1 in Heq; apply concat_cancel_last in Heq as [??]; try apply const_list_concat.
      all: try by rewrite separate2 in Heq; apply concat_cancel_last in Heq as [??]; try apply const_list_concat.
      all: try by rewrite separate3 in Heq; apply concat_cancel_last in Heq as [??]; try apply const_list_concat.
      all: try by right; right; right; left; eexists [].
      all: try by repeat right.
      right; left; exists [], x => //.
      all: try by rewrite separate1 cat_app app_assoc in Heq; apply concat_cancel_last in Heq as [??]; try apply const_list_concat.
      move/lfilledP in H.
      inversion H; subst.
      all: try by apply first_values in H1 as (? & ? & ?) => //; try apply const_list_concat; try apply v_to_e_is_const_list.
      destruct es'0.
      2:{ destruct (separate_last (a :: es'0)) as [[??]|] eqn:Hlast.
          2: by apply separate_last_None in Hlast.
          apply separate_last_spec in Hlast.
          rewrite Hlast in H1.
          rewrite -cat_app in H1.
          do 2 rewrite catA in H1.
          apply concat_cancel_last in H1 as [Heq ->].
          exfalso; values_no_reduce.
          exact Hred.
          assert (is_true (const_list (v_to_e_list vs ++ [:: AI_ref i])%list)).
          by apply const_list_concat; try apply v_to_e_is_const_list => //.
          rewrite -Heq in H1. apply const_list_split in H1 as [H1 _].
          apply const_list_split in H1 as [_ H1] => //. }
      rewrite cats0 in H1.
      destruct vs0.
      { move/lfilledP in H0; inversion H0; subst.
        rewrite cats0 /=.
        apply IHHred => //. }
      destruct es; first by empty_list_no_reduce.
      destruct (separate_last (a0 :: es)) as [[??]|] eqn:Hlast .
      2: by apply separate_last_None in Hlast.
      apply separate_last_spec in Hlast.
      rewrite Hlast in H1 Hred.
      rewrite -cat_app catA in H1.
      apply concat_cancel_last in H1 as [H1 ->].
      destruct l.
      { clear -Hred. exfalso.
        simpl in Hred.
        remember [:: _] as es.
        induction Hred.
        inversion H.
        all: remember Heqes as Heq ; clear HeqHeq Heqes.
        all: subst.
        all: try by inversion Heq.
        all: try by do 2 (destruct vs => //).
        move/lfilledP in H1; inversion H1; subst.
        all: try by do 2 (destruct vs => //).
        all: try by do 2 (destruct bef => //).
        all: try by do 2 (destruct vcs => //).
        apply filled_singleton in H as (-> & -> & ->) => //.
        by intros ->; empty_list_no_reduce. }
      destruct (separate_last (a1 :: l)) as [[??]|] eqn:Hlast'.
      2: by apply separate_last_None in Hlast'.
      apply separate_last_spec in Hlast'.
      rewrite Hlast' in H1 Hred.
      rewrite -cat_app catA in H1.
      apply concat_cancel_last in H1 as [H1 ->].
      rewrite -app_assoc /= in Hred.
      assert (is_true $ const_list (v_to_e_list vs)); first by apply v_to_e_is_const_list.
      rewrite -H1 in H2.
      apply const_list_split in H2 as [??].
      apply const_es_exists in H3 as [vs' ->].
      eapply IHm in Hred.
      move/lfilledP in H0; inversion H0; subst.
      rewrite cats0.
      apply continuation_expr_prepend => //.
      specialize (f_equal length H1) as Hlen.
      rewrite cat_app length_app /= in Hlen.
      do 2 rewrite v_to_e_length in Hlen.
      lia.
    - remember (S $ length vs) as m.
      assert (length vs < m) as Hm; first lia.
      clear Heqm.
      generalize dependent vs; generalize dependent es'.
      induction m; first lia.
      intros.
      remember (_ ++ [_]) as es.
      induction Hred.
      inversion H.
      all: remember Heqes as Heq; clear HeqHeq Heqes.
      all: subst.
      all: try by do 2 (destruct vs => //). 
      all: try by rewrite separate1 in Heq; apply concat_cancel_last in Heq as [??]; try apply const_list_concat.
      all: try by rewrite separate2 in Heq; apply concat_cancel_last in Heq as [??]; try apply const_list_concat.
      all: try by rewrite separate3 in Heq; apply concat_cancel_last in Heq as [??]; try apply const_list_concat.
      all: try by right; right; right; left; eexists [].
      all: try by right; right; right; right; left.
      right; right; left; eexists [], _,_,_ => //.
      all: try by rewrite separate1 cat_app app_assoc in Heq; apply concat_cancel_last in Heq as [??]; try apply const_list_concat.
      right; right ; right; right; right; eexists [], _,_,_ => //. 
      move/lfilledP in H.
      inversion H; subst.
      all: try by apply first_values in H1 as (? & ? & ?) => //; try apply const_list_concat; try apply v_to_e_is_const_list.
      destruct es'0.
      2:{ destruct (separate_last (a :: es'0)) as [[??]|] eqn:Hlast.
          2: by apply separate_last_None in Hlast.
          apply separate_last_spec in Hlast.
          rewrite Hlast in H1.
          rewrite -cat_app in H1.
          do 2 rewrite catA in H1.
          apply concat_cancel_last in H1 as [Heq ->].
          exfalso; values_no_reduce.
          exact Hred.
          assert (is_true (const_list (v_to_e_list vs ++ [:: AI_ref i])%list)).
          by apply const_list_concat; try apply v_to_e_is_const_list => //.
          rewrite -Heq in H1. apply const_list_split in H1 as [H1 _].
          apply const_list_split in H1 as [H1 _] => //.
          apply const_list_split in H1 as [_ H1] => //. 
      }
      rewrite cats0 in H1.
      destruct vs0.
      { move/lfilledP in H0; inversion H0; subst.
        rewrite cats0 /=.
        apply IHHred => //. }
      destruct es; first by empty_list_no_reduce.
      destruct (separate_last (a0 :: es)) as [[??]|] eqn:Hlast .
      2: by apply separate_last_None in Hlast.
      apply separate_last_spec in Hlast.
      rewrite Hlast in H1 Hred.
      rewrite -cat_app catA in H1.
      apply concat_cancel_last in H1 as [H1 ->].
      assert (is_true $ const_list (v_to_e_list vs)); first by apply v_to_e_is_const_list.
      rewrite -H1 in H2.
      apply const_list_split in H2 as [??].
      apply const_es_exists in H3 as [vs' ->].
      eapply IHm in Hred.
      move/lfilledP in H0; inversion H0; subst.
      rewrite cats0.
      apply continuation_expr_prepend => //.
      specialize (f_equal length H1) as Hlen.
      rewrite cat_app length_app /= in Hlen.
      do 2 rewrite v_to_e_length in Hlen.
      lia.
    - remember (S $ length vs) as m.
      assert (length vs < m) as Hm; first lia.
      clear Heqm.
      generalize dependent vs; generalize dependent es'.
      induction m; first lia.
      intros.
      remember (_ ++ [_]) as es.
      induction Hred.
      inversion H.
      all: remember Heqes as Heq; clear HeqHeq Heqes.
      all: subst.
      all: try by do 2 (destruct vs => //). 
      all: try by rewrite separate1 in Heq; apply concat_cancel_last in Heq as [??]; try apply const_list_concat.
      all: try by rewrite separate2 in Heq; apply concat_cancel_last in Heq as [??]; try apply const_list_concat.
      all: try by rewrite separate3 in Heq; apply concat_cancel_last in Heq as [??]; try apply const_list_concat.
      all: try by right; right; right; left; eexists [].
      all: try by right; right; right; right; left.
      all: try by rewrite separate1 cat_app app_assoc in Heq; apply concat_cancel_last in Heq as [??]; try apply const_list_concat.
      2: right; right; left; eexists [], _,_,_ => //.
      move/lfilledP in H.
      inversion H; subst.
      all: try by apply first_values in H1 as (? & ? & ?) => //; try apply const_list_concat; try apply v_to_e_is_const_list.
      destruct es'0.
      2:{ destruct (separate_last (a :: es'0)) as [[??]|] eqn:Hlast.
          2: by apply separate_last_None in Hlast.
          apply separate_last_spec in Hlast.
          rewrite Hlast in H1.
          rewrite -cat_app in H1.
          do 2 rewrite catA in H1.
          apply concat_cancel_last in H1 as [Heq ->].
          exfalso; values_no_reduce.
          exact Hred.
          assert (is_true (const_list (v_to_e_list vs)%list)).
          by apply v_to_e_is_const_list => //.
          rewrite -Heq in H1. apply const_list_split in H1 as [H1 _].
          apply const_list_split in H1 as [_ H1] => //. 
      }
      rewrite cats0 in H1.
      destruct vs0.
      { move/lfilledP in H0; inversion H0; subst.
        rewrite cats0 /=.
        apply IHHred => //. }
      destruct es; first by empty_list_no_reduce.
      destruct (separate_last (a0 :: es)) as [[??]|] eqn:Hlast .
      2: by apply separate_last_None in Hlast.
      apply separate_last_spec in Hlast.
      rewrite Hlast in H1 Hred.
      rewrite -cat_app catA in H1.
      apply concat_cancel_last in H1 as [H1 ->].
      assert (is_true $ const_list (v_to_e_list vs)); first by apply v_to_e_is_const_list.
      rewrite -H1 in H2.
      apply const_list_split in H2 as [??].
      apply const_es_exists in H3 as [vs' ->].
      eapply IHm in Hred.
      move/lfilledP in H0; inversion H0; subst.
      rewrite cats0.
      apply continuation_expr_prepend => //.
      specialize (f_equal length H1) as Hlen.
      rewrite cat_app length_app /= in Hlen.
      do 2 rewrite v_to_e_length in Hlen.
      lia.
    - remember (S $ length vs) as m.
      assert (length vs < m) as Hm; first lia.
      clear Heqm.
      generalize dependent vs; generalize dependent es'.
      induction m; first lia.
      intros.
      remember (_ ++ [_]) as es.
      induction Hred.
      inversion H.
      all: remember Heqes as Heq; clear HeqHeq Heqes.
      all: subst.
      all: try by do 2 (destruct vs => //). 
      all: try by rewrite separate1 in Heq; apply concat_cancel_last in Heq as [??]; try apply const_list_concat.
      all: try by rewrite separate2 in Heq; apply concat_cancel_last in Heq as [??]; try apply const_list_concat.
      all: try by rewrite separate3 in Heq; apply concat_cancel_last in Heq as [??]; try apply const_list_concat.
      all: try by right; right; right; left; eexists [].
      all: try by right; right; right; right; left.
      all: try by rewrite separate1 cat_app app_assoc in Heq; apply concat_cancel_last in Heq as [??]; try apply const_list_concat.
      move/lfilledP in H.
      inversion H; subst.
      all: try by apply first_values in H1 as (? & ? & ?) => //; try apply const_list_concat; try apply v_to_e_is_const_list.
      destruct es'0.
      2:{ destruct (separate_last (a :: es'0)) as [[??]|] eqn:Hlast.
          2: by apply separate_last_None in Hlast.
          apply separate_last_spec in Hlast.
          rewrite Hlast in H1.
          rewrite -cat_app in H1.
          do 2 rewrite catA in H1.
          apply concat_cancel_last in H1 as [Heq ->].
          exfalso; values_no_reduce.
          exact Hred.
          assert (is_true (const_list (v_to_e_list vs)%list)).
          by apply v_to_e_is_const_list => //.
          rewrite -Heq in H1. apply const_list_split in H1 as [H1 _].
          apply const_list_split in H1 as [_ H1] => //. 
      }
      rewrite cats0 in H1.
      destruct vs0.
      { move/lfilledP in H0; inversion H0; subst.
        rewrite cats0 /=.
        apply IHHred => //. }
      destruct es; first by empty_list_no_reduce.
      destruct (separate_last (a0 :: es)) as [[??]|] eqn:Hlast .
      2: by apply separate_last_None in Hlast.
      apply separate_last_spec in Hlast.
      rewrite Hlast in H1 Hred.
      rewrite -cat_app catA in H1.
      apply concat_cancel_last in H1 as [H1 ->].
      assert (is_true $ const_list (v_to_e_list vs)); first by apply v_to_e_is_const_list.
      rewrite -H1 in H2.
      apply const_list_split in H2 as [??].
      apply const_es_exists in H3 as [vs' ->].
      eapply IHm in Hred.
      move/lfilledP in H0; inversion H0; subst.
      rewrite cats0.
      apply continuation_expr_prepend => //.
      specialize (f_equal length H1) as Hlen.
      rewrite cat_app length_app /= in Hlen.
      do 2 rewrite v_to_e_length in Hlen.
      lia.
    - exfalso; values_no_reduce; eauto.
    - apply val_head_stuck_reduce in Hred.
      rewrite /to_val0 map_app merge_app in Hred.
      assert (is_true (const_list (v_to_e_list vs))); first apply v_to_e_is_const_list.
      apply const_list_to_val in H as (vs'' & Htv & Heq).
      unfold to_val0 in Htv.
      destruct (merge_values _) => //.
      simpl in Hred.
      destruct v => //.
  Qed. 

  Lemma hfilled_to_susfill a hh vs es:
    is_true (hfilled (Var_prompt_suspend a) hh [:: AI_suspend_desugared vs a] es) ->
    exists sh, to_eff0 es = Some (susE vs a sh) /\ hh = hh_of_sush a sh.
  Proof.
    intros H.
    move/hfilledP in H.
    remember (_ a) as v.
    remember [_] as es0.
    induction H; subst.
    all: apply const_list_to_val in H as (? & H & ?).
    all: rewrite /to_val0 in H.
    all: rewrite /to_eff0 map_app merge_app.
    all: destruct (merge_values _) => //.
    all: inversion H; subst.
    all: simpl.
    { eexists. rewrite merge_suspend. split => //. simpl.
      rewrite flatten_simplify cats0 //. } 
    all: destruct IHhfilledInd as (sh & IH & ?) => //.
    all: unfold to_eff0 in IH.
    all: destruct (merge_values _) => //.
    all: inversion IH; subst.
    all: try by eexists; rewrite merge_suspend; split;
      try rewrite flatten_simplify /= cats0 //.
    destruct (suselts_of_continuation_clauses _ _) eqn:Hclauses => //.
    2:{ apply suselts_of_continuation_clauses_None in Hclauses as [??].
        rewrite H0 in H2.
        done. } 
    eexists; rewrite merge_suspend; split => //. 
    rewrite flatten_simplify /= cats0 //.
    replace (List.map (continuation_clause_of_suselt a) l) with hs; first done.
    clear - Hclauses.
    generalize dependent l.
    induction hs; intros.
    simpl in Hclauses. inversion Hclauses; subst => //.
    simpl in Hclauses.
    destruct (suselt_of_continuation_clause _ _) eqn:Helt => //.
    destruct (suselts_of_continuation_clauses _ _) => //.
    inversion Hclauses; subst.
    simpl. erewrite IHhs; last done.
    f_equal.
    unfold suselt_of_continuation_clause in Helt.
    destruct a.
    destruct a0 => //.
    destruct t => //.
    destruct (n0 <? n) eqn:Hn => //=.
    inversion Helt; subst. rewrite Hn. done.
    destruct (n0 =? n) eqn:Hn' => //=.
    inversion Helt; subst.
    apply Nat.ltb_ge in Hn.
    apply Nat.eqb_neq in Hn'.
    assert (n0 - 1 >= n); first lia.
    apply Nat.ltb_ge in H.
    rewrite H.
    f_equal. f_equal. lia.
    inversion Helt; subst => //.
  Qed. 

    Lemma hfilled_to_swfill k tf hh vs es a:
    is_true (hfilled (Var_prompt_switch a) hh [:: AI_switch_desugared vs k tf a] es) ->
    exists sh, to_eff0 es = Some (swE vs k tf a sh) /\ hh = hh_of_swh a sh.
  Proof.
    intros H.
    move/hfilledP in H.
    remember (_ a) as v.
    remember [_] as es0.
    induction H; subst.
    all: apply const_list_to_val in H as (? & H & ?).
    all: rewrite /to_val0 in H.
    all: rewrite /to_eff0 map_app merge_app.
    all: destruct (merge_values _) => //.
    all: inversion H; subst.
    all: simpl.
    { eexists. rewrite merge_switch. split => //. simpl.
      rewrite flatten_simplify cats0 //. } 
    all: destruct IHhfilledInd as (sh & IH & ?) => //.
    all: unfold to_eff0 in IH.
    all: destruct (merge_values _) => //.
    all: inversion IH; subst.
    all: try by eexists; rewrite merge_switch; split;
      try rewrite flatten_simplify /= cats0 //.
    destruct (swelts_of_continuation_clauses _ _) eqn:Hclauses => //.
    2:{ apply swelts_of_continuation_clauses_None in Hclauses.
        rewrite H0 in Hclauses.
        done. } 
    eexists; rewrite merge_switch; split => //. 
    rewrite flatten_simplify /= cats0 //.
    replace (List.map (continuation_clause_of_swelt a) l) with hs; first done.
    clear - Hclauses.
    generalize dependent l.
    induction hs; intros.
    simpl in Hclauses. inversion Hclauses; subst => //.
    simpl in Hclauses.
    destruct (swelt_of_continuation_clause _ _) eqn:Helt => //.
    destruct (swelts_of_continuation_clauses _ _) => //.
    inversion Hclauses; subst.
    simpl. erewrite IHhs; last done.
    f_equal.
    unfold swelt_of_continuation_clause in Helt.
    destruct a.
    destruct a0 => //.
    inversion Helt; subst => //. 
    destruct t => //.
    destruct (n0 <? n) eqn:Hn => //=.
    inversion Helt; subst. rewrite Hn. done.
    destruct (n0 =? n) eqn:Hn' => //=.
    inversion Helt; subst.
    apply Nat.ltb_ge in Hn.
    apply Nat.eqb_neq in Hn'.
    assert (n0 - 1 >= n); first lia.
    apply Nat.ltb_ge in H.
    rewrite H.
    f_equal. f_equal. lia.

  Qed. 

  
  Lemma reduce_in_prompt s f ts dccs es s' f' es' :
    reduce s f [AI_prompt ts dccs es] s' f' es' ->
    (exists esf, reduce s f es s' f' esf /\ es' = [AI_prompt ts dccs esf]) \/
      (es = es' /\ is_true (const_list es) /\ f = f' /\ s = s') \/
      (exists lh, lfilled 0 lh [AI_trap] es /\ es' = [AI_trap] /\ f = f' /\ s = s') \/
      (exists vs a sh l t1s t2s, to_eff0 es = Some (susE vs (Mk_tagidx a) sh) /\ firstx_continuation_suspend dccs (Mk_tagidx a) = Some l /\ nth_error (s_tags s) a = Some (Tf t1s t2s) /\ es' = v_to_e_list vs  ++ [:: AI_ref_cont (length (s_conts s)); AI_basic (BI_br l)] /\ f = f' /\ s' = new_cont s (Cont_hh (Tf t2s ts) (hh_of_sush (Mk_tagidx a) sh))) \/
      (exists vs k tf'' t1s' t2s' hh' tf' i sh LI,
          to_eff0 es =
            Some (swE vs k (Tf (t1s' ++ [:: T_ref (T_contref tf')]) t2s') i sh) /\
            nth_error (s_conts s) k = Some (Cont_hh tf'' hh') /\
            firstx_continuation_switch dccs i = true /\
            is_true (hfilled No_var hh' (v_to_e_list vs ++
                                           [:: AI_ref_cont (length (s_conts s))])
                       LI) /\
            es' = [AI_prompt ts dccs LI] /\
            f = f' /\
            s' =  new_cont (upd_s_cont s k (Cont_dagger tf''))
                    (Cont_hh tf' (hh_of_swh i sh)) ).
  Proof.
    intros Hred.
    remember [_] as es0.
    induction Hred.
    inversion H.
    all: remember Heqes0 as Heq; clear HeqHeq Heqes0.
    all: subst.
    all: try by inversion Heq.
    all: try by do 2 (destruct vs => //).
    all: try by do 2 (destruct vcs => //).
    - inversion Heq; subst. right; left. done.
    - inversion Heq; subst. right; right; left.
      exists (LH_base [] []). split; last done.
      rewrite /lfilled /lfill //.
    - move/lfilledP in H1; inversion H1; subst.
      all: try by do 2 (destruct vs => //).
      all: try by do 2 (destruct bef => //).
      destruct bef; last by do 2 (destruct bef => //).
      inversion H2; subst.
      move/lfilledP in H7.
      right; right; left. eauto.
    - inversion Heq; subst.
      right; right; right; left.
      apply hfilled_to_susfill in H2 as (sh & Htf & ->).
      repeat eexists => //. exact Htf. exact H1. exact H0.
    - inversion Heq; subst.
      right; right; right; right.
      apply hfilled_to_swfill in H2 as (sh & Htf & ->).
      do 10 eexists.
      split; first exact Htf.
      split; first exact H1.
      repeat split => //. 
      done. 
    - move/lfilledP in H.
      inversion H; subst.
      all: try by do 2 (destruct vs => //).
      all: try by do 2 (destruct bef => //).
      + destruct vs.
        * destruct es0; first by empty_list_no_reduce.
          inversion H1; subst.
          destruct es0, es'0 => //.
          move/lfilledP in H0; inversion H0; subst.
          simpl. rewrite cats0.
          apply IHHred => //.
        * inversion H1; subst.
          done.
      + destruct bef; last by do 2 (destruct bef => //).
        inversion H1; subst.
        move/lfilledP in H0; inversion H0; subst.
        move/lfilledP in H13.
        move/lfilledP in H6.
        left.
        eexists. split; last done.
        eapply r_label.
        exact Hred.
        exact H6.
        exact H13.
  Qed. 
          
    Lemma continuation_ignores_frame fany s f es s' f' es':
    reduce s f es s' f' es' ->
    continuation_expr es ->
    (reduce s fany es s' fany es' /\ f = f').
  Proof.
    intros Hred Hes.
    destruct Hes as [(vs & i & tf & ->) | [(vs & i & ->) | [(vs & n & f0 & es0 & ->) | [(vs & ->) | [Hes | (vs & vs' & k & tf & ->)]]]]].
     - remember (S $ length vs) as m.
      assert (length vs < m) as Hm; first lia.
      clear Heqm.
      generalize dependent vs; generalize dependent es'.
      induction m; first lia.
      intros.
      rewrite separate1 cat_app app_assoc in Hred.
      remember ((v_to_e_list vs ++ [AI_ref i]) ++
                  [AI_basic (BI_call_reference (Type_explicit tf))])%list as es.
 
      
      induction Hred.
      inversion H.
      all: remember Heqes as Heq; clear HeqHeq Heqes.
      all: subst.
      all: try by do 3 (destruct vs => //). 
      all: try by rewrite separate1 in Heq; apply concat_cancel_last in Heq as [??]; try apply const_list_concat.
      all: try by rewrite separate2 in Heq; apply concat_cancel_last in Heq as [??]; try apply const_list_concat.
      all: try by rewrite separate3 in Heq; apply concat_cancel_last in Heq as [??]; try apply const_list_concat.
      move/lfilledP in H1; inversion H1; subst.
      all: try by apply first_values in H2 as (? & ? & ?) ; try apply const_list_concat; try apply v_to_e_is_const_list.
      destruct vs; last by do 2 (destruct vs => //).
      split; last done.
      inversion Heq; subst; by eapply r_call_reference. 
      all: try by rewrite separate1 cat_app app_assoc in Heq; apply concat_cancel_last in Heq as [??]; try apply const_list_concat.
      move/lfilledP in H.
      inversion H; subst.
      all: try by apply first_values in H1 as (? & ? & ?) => //; try apply const_list_concat; try apply v_to_e_is_const_list.
      destruct es'0.
      2:{ destruct (separate_last (a :: es'0)) as [[??]|] eqn:Hlast.
          2: by apply separate_last_None in Hlast.
          apply separate_last_spec in Hlast.
          rewrite Hlast in H1.
          rewrite -cat_app in H1.
          do 2 rewrite catA in H1.
          apply concat_cancel_last in H1 as [Heq ->].
          exfalso; values_no_reduce.
          exact Hred.
          assert (is_true (const_list (v_to_e_list vs ++ [:: AI_ref i])%list)).
          by apply const_list_concat; try apply v_to_e_is_const_list => //.
          rewrite -Heq in H1. apply const_list_split in H1 as [H1 _].
          apply const_list_split in H1 as [_ H1] => //. }
      rewrite cats0 in H1.
      destruct vs0.
      { move/lfilledP in H0; inversion H0; subst.
        rewrite cats0 /=.
        apply IHHred => //. }
      destruct es; first by empty_list_no_reduce.
      destruct (separate_last (a0 :: es)) as [[??]|] eqn:Hlast .
      2: by apply separate_last_None in Hlast.
      apply separate_last_spec in Hlast.
      rewrite Hlast in H1 Hred.
      rewrite -cat_app catA in H1.
      apply concat_cancel_last in H1 as [H1 ->].
      destruct l.
      { clear -Hred. exfalso.
        simpl in Hred.
        remember [:: _] as es.
        induction Hred.
        inversion H.
        all: remember Heqes as Heq ; clear HeqHeq Heqes.
        all: subst.
        all: try by inversion Heq.
        all: try by do 2 (destruct vs0 => //).
        move/lfilledP in H1; inversion H1; subst.
        all: try by do 2 (destruct vs0 => //).
        all: try by do 2 (destruct bef => //).
        all: try by do 2 (destruct vcs => //).
        apply filled_singleton in H as (-> & -> & ->) => //.
        by intros ->; empty_list_no_reduce. }
      destruct (separate_last (a1 :: l)) as [[??]|] eqn:Hlast'.
      2: by apply separate_last_None in Hlast'.
      apply separate_last_spec in Hlast'.
      rewrite Hlast' in H1 Hred.
      rewrite -cat_app catA in H1.
      apply concat_cancel_last in H1 as [H1 ->].
      rewrite -app_assoc /= in Hred.
      assert (is_true $ const_list (v_to_e_list vs)); first by apply v_to_e_is_const_list.
      rewrite -H1 in H2.
      apply const_list_split in H2 as [??].
      apply const_es_exists in H3 as [vs' ->].
      eapply IHm in Hred.
      move/lfilledP in H0; inversion H0; subst.
      rewrite cats0.
      destruct Hred as [Hred ->]; split; last done.
      eapply r_label.
      exact Hred.
      instantiate (1 := LH_base (a :: vs0) [::]).
      instantiate (1 := 0).
      rewrite /lfilled /lfill H6 app_nil_r.
      rewrite app_assoc.
      repeat rewrite -cat_app.
      rewrite H1. done.
      rewrite /lfilled /lfill H6 app_nil_r //.
      specialize (f_equal length H1) as Hlen.
      rewrite cat_app length_app /= in Hlen.
      do 2 rewrite v_to_e_length in Hlen.
      lia.
    - remember (S $ length vs) as m.
      assert (length vs < m) as Hm; first lia.
      clear Heqm.
      generalize dependent vs; generalize dependent es'.
      induction m; first lia.
      intros.
      remember (_ ++ [_]) as es.
      induction Hred.
      inversion H.
      all: remember Heqes as Heq; clear HeqHeq Heqes.
      all: subst.
      all: try by do 2 (destruct vs => //). 
      all: try by rewrite separate1 in Heq; apply concat_cancel_last in Heq as [??]; try apply const_list_concat.
      all: try by rewrite separate2 in Heq; apply concat_cancel_last in Heq as [??]; try apply const_list_concat.
      all: try by rewrite separate3 in Heq; apply concat_cancel_last in Heq as [??]; try apply const_list_concat.
      move/lfilledP in H1; inversion H1; subst.
      all: try by apply first_values in H2 as (? & ? & ?) ; try apply const_list_concat; try apply v_to_e_is_const_list.
      apply concat_cancel_last in Heq as [Heq Heq'].
      apply v_to_e_inj in Heq as ->.
      inversion Heq'; subst.
      split; last done.
      eapply r_invoke_native; eauto.
      apply concat_cancel_last in Heq as [Heq Heq'].
      apply v_to_e_inj in Heq as ->.
      inversion Heq'; subst.
      split; last done.
      eapply r_invoke_host; eauto. 
      all: try by rewrite separate1 cat_app app_assoc in Heq; apply concat_cancel_last in Heq as [??]; try apply const_list_concat.
      move/lfilledP in H.
      inversion H; subst.
      all: try by apply first_values in H1 as (? & ? & ?) => //; try apply const_list_concat; try apply v_to_e_is_const_list.
      destruct es'0.
      2:{ destruct (separate_last (a :: es'0)) as [[??]|] eqn:Hlast.
          2: by apply separate_last_None in Hlast.
          apply separate_last_spec in Hlast.
          rewrite Hlast in H1.
          rewrite -cat_app in H1.
          do 2 rewrite catA in H1.
          apply concat_cancel_last in H1 as [Heq ->].
          exfalso; values_no_reduce.
          exact Hred.
          assert (is_true (const_list (v_to_e_list vs ++ [:: AI_ref i])%list)).
          by apply const_list_concat; try apply v_to_e_is_const_list => //.
          rewrite -Heq in H1. apply const_list_split in H1 as [H1 _].
          apply const_list_split in H1 as [H1 _] => //.
          apply const_list_split in H1 as [_ H1] => //. 
      }
      rewrite cats0 in H1.
      destruct vs0.
      { move/lfilledP in H0; inversion H0; subst.
        repeat rewrite cats0 /=.
        apply IHHred => //. }
      destruct es; first by empty_list_no_reduce.
      destruct (separate_last (a0 :: es)) as [[??]|] eqn:Hlast .
      2: by apply separate_last_None in Hlast.
      apply separate_last_spec in Hlast.
      rewrite Hlast in H1 Hred.
      rewrite -cat_app catA in H1.
      apply concat_cancel_last in H1 as [H1 ->].
      assert (is_true $ const_list (v_to_e_list vs)); first by apply v_to_e_is_const_list.
      rewrite -H1 in H2.
      apply const_list_split in H2 as [??].
      apply const_es_exists in H3 as [vs' ->].
      eapply IHm in Hred.
      move/lfilledP in H0; inversion H0; subst.
      repeat rewrite cats0.
      rewrite Hlast.
      destruct Hred as [Hred ->]; split; last done.
      eapply r_label.
      exact Hred.
      instantiate (1 := LH_base (a :: vs0) []).
      instantiate (1 := 0).
      rewrite /lfilled /lfill H6 app_nil_r //.
      rewrite /lfilled /lfill H6 app_nil_r //. 

      specialize (f_equal length H1) as Hlen.
      rewrite cat_app length_app /= in Hlen.
      do 2 rewrite v_to_e_length in Hlen.
      lia.
    - remember (S $ length vs) as m.
      assert (length vs < m) as Hm; first lia.
      clear Heqm.
      generalize dependent vs; generalize dependent es'.
      induction m; first lia.
      intros.
      remember (_ ++ [_]) as es.
      induction Hred.
      inversion H.
      all: remember Heqes as Heq; clear HeqHeq Heqes.
      all: subst.
      all: try by do 3 (destruct vs => //). 
      all: try by rewrite separate1 in Heq; apply concat_cancel_last in Heq as [??]; try apply const_list_concat.
      all: try by rewrite separate2 in Heq; apply concat_cancel_last in Heq as [??]; try apply const_list_concat.
      all: try by rewrite separate3 in Heq; apply concat_cancel_last in Heq as [??]; try apply const_list_concat.
      all: try by do 2 econstructor.
      all: try by rewrite separate1 cat_app app_assoc in Heq; apply concat_cancel_last in Heq as [??]; try apply const_list_concat.
      move/lfilledP in H.
      inversion H; subst.
      all: try by apply first_values in H1 as (? & ? & ?) => //; try apply const_list_concat; try apply v_to_e_is_const_list.
      destruct es'0.
      2:{ destruct (separate_last (a :: es'0)) as [[??]|] eqn:Hlast.
          2: by apply separate_last_None in Hlast.
          apply separate_last_spec in Hlast.
          rewrite Hlast in H1.
          rewrite -cat_app in H1.
          do 2 rewrite catA in H1.
          apply concat_cancel_last in H1 as [Heq ->].
          exfalso; values_no_reduce.
          exact Hred.
          assert (is_true (const_list (v_to_e_list vs)%list)).
          by apply v_to_e_is_const_list => //.
          rewrite -Heq in H1. apply const_list_split in H1 as [H1 _].
          apply const_list_split in H1 as [_ H1] => //. 
      }
      rewrite cats0 in H1.
      destruct vs0.
      { move/lfilledP in H0; inversion H0; subst.
        repeat rewrite cats0 /=.
        apply IHHred => //. }
      destruct es; first by empty_list_no_reduce.
      destruct (separate_last (a0 :: es)) as [[??]|] eqn:Hlast .
      2: by apply separate_last_None in Hlast.
      apply separate_last_spec in Hlast.
      rewrite Hlast in H1 Hred.
      rewrite -cat_app catA in H1.
      apply concat_cancel_last in H1 as [H1 ->].
      assert (is_true $ const_list (v_to_e_list vs)); first by apply v_to_e_is_const_list.
      rewrite -H1 in H2.
      apply const_list_split in H2 as [??].
      apply const_es_exists in H3 as [vs' ->].
      eapply IHm in Hred.
      move/lfilledP in H0; inversion H0; subst.
      repeat rewrite cats0.
      rewrite Hlast.
      destruct Hred as [Hred ->]; split; last done.
      eapply r_label.
      exact Hred.
      instantiate (1 := LH_base (a :: vs0) []).
      instantiate (1 := 0).
      rewrite /lfilled /lfill H6 app_nil_r //.
      rewrite /lfilled /lfill H6 app_nil_r //. 

      specialize (f_equal length H1) as Hlen.
      rewrite cat_app length_app /= in Hlen.
      do 2 rewrite v_to_e_length in Hlen.
      lia.
    - remember (S $ length vs) as m.
      assert (length vs < m) as Hm; first lia.
      clear Heqm.
      generalize dependent vs; generalize dependent es'.
      induction m; first lia.
      intros.
      remember (_ ++ [_]) as es.
      induction Hred.
      inversion H.
      all: remember Heqes as Heq; clear HeqHeq Heqes.
      all: subst.
      all: try by do 3 (destruct vs => //). 
      all: try by rewrite separate1 in Heq; apply concat_cancel_last in Heq as [??]; try apply const_list_concat.
      all: try by rewrite separate2 in Heq; apply concat_cancel_last in Heq as [??]; try apply const_list_concat.
      all: try by rewrite separate3 in Heq; apply concat_cancel_last in Heq as [??]; try apply const_list_concat.
      all: try by do 2 econstructor.
      all: try by rewrite separate1 cat_app app_assoc in Heq; apply concat_cancel_last in Heq as [??]; try apply const_list_concat.
      move/lfilledP in H.
      inversion H; subst.
      all: try by apply first_values in H1 as (? & ? & ?) => //; try apply const_list_concat; try apply v_to_e_is_const_list.
      destruct es'0.
      2:{ destruct (separate_last (a :: es'0)) as [[??]|] eqn:Hlast.
          2: by apply separate_last_None in Hlast.
          apply separate_last_spec in Hlast.
          rewrite Hlast in H1.
          rewrite -cat_app in H1.
          do 2 rewrite catA in H1.
          apply concat_cancel_last in H1 as [Heq ->].
          exfalso; values_no_reduce.
          exact Hred.
          assert (is_true (const_list (v_to_e_list vs)%list)).
          by apply v_to_e_is_const_list => //.
          rewrite -Heq in H1. apply const_list_split in H1 as [H1 _].
          apply const_list_split in H1 as [_ H1] => //. 
      }
      rewrite cats0 in H1.
      destruct vs0.
      { move/lfilledP in H0; inversion H0; subst.
        repeat rewrite cats0 /=.
        apply IHHred => //. }
      destruct es; first by empty_list_no_reduce.
      destruct (separate_last (a0 :: es)) as [[??]|] eqn:Hlast .
      2: by apply separate_last_None in Hlast.
      apply separate_last_spec in Hlast.
      rewrite Hlast in H1 Hred.
      rewrite -cat_app catA in H1.
      apply concat_cancel_last in H1 as [H1 ->].
      assert (is_true $ const_list (v_to_e_list vs)); first by apply v_to_e_is_const_list.
      rewrite -H1 in H2.
      apply const_list_split in H2 as [??].
      apply const_es_exists in H3 as [vs' ->].
      eapply IHm in Hred.
      move/lfilledP in H0; inversion H0; subst.
      repeat rewrite cats0. rewrite Hlast.
      destruct Hred as [Hred ->]; split; last done.
      eapply r_label.
      exact Hred.
      instantiate (1 := LH_base (a :: vs0) []).
      instantiate (1 := 0).
      rewrite /lfilled /lfill H6 app_nil_r //.
      rewrite /lfilled /lfill H6 app_nil_r //.

      specialize (f_equal length H1) as Hlen.
      rewrite cat_app length_app /= in Hlen.
      do 2 rewrite v_to_e_length in Hlen.
      lia.
    - exfalso; values_no_reduce; eauto.
    - apply val_head_stuck_reduce in Hred.
      rewrite /to_val0 map_app merge_app in Hred.
      assert (is_true (const_list (v_to_e_list vs))); first apply v_to_e_is_const_list.
      apply const_list_to_val in H as (vs'' & Htv & Heq).
      unfold to_val0 in Htv.
      destruct (merge_values _) => //.
      simpl in Hred.
      destruct v => //.
  Qed.

      

  Lemma continuation_prompt_ignores_frame fany s f ts dccs es s' f' es' :
    reduce s f [AI_prompt ts dccs es] s' f' es' ->
    continuation_expr es ->
    reduce s fany [AI_prompt ts dccs es] s' fany es' /\ f = f'.
  Proof.
    intros Hred Hes.
    apply reduce_in_prompt in Hred as [(esf & Hred & ->) | [(-> & Hconst & -> & ->) | [(lh & Htrap & -> & -> & ->) | [(vs & i & sh & l & t1s & t2s & Htf & Hsus & Htag & -> & -> & -> ) | (vs & k & t1s & t1s' & t2s' & hh' & tf & i & sh & LI & Htf & Hk & Hsw & Hfill & -> & -> & -> )]]]].
    all: try (split; last done).
    - eapply continuation_ignores_frame in Hred as [Hred ->] => //.
      split => //.
      eapply r_label.
      exact Hred.
      instantiate (1 := LH_prompt [] ts dccs (LH_base [] []) []).
      instantiate (1 := 0).
      rewrite /lfilled /lfill /=.
      by rewrite app_nil_r.
      rewrite /lfilled /lfill /=.
      by rewrite app_nil_r.
    - constructor. constructor. done.
    - constructor. econstructor.
      done. instantiate (1 := LH_prompt [::] ts dccs lh [::]).
      unfold lfilled, lfill; fold lfill. simpl.
      unfold lfilled in Htrap.
      destruct (lfill _ _ _) => //.
      destruct (es == l) eqn:Heq => //.
      move/eqP in Heq. subst. done.
    - econstructor. done. exact Htag. exact Hsus.
      specialize (susfill_to_hfilled (Mk_tagidx i) sh [::AI_suspend_desugared vs (Mk_tagidx i)]) as H.

      apply of_to_eff0 in Htf.
      unfold of_eff0 in Htf.
      rewrite Htf in H.
      done.
    - econstructor. exact Hsw. done.
      3: exact Hfill.
      exact Hk. 
      specialize (swfill_to_hfilled i sh [:: AI_switch_desugared vs k (Tf (t1s' ++ [::T_ref (T_contref tf)]) t2s') i]) as H.
      apply of_to_eff0 in Htf.
      rewrite /of_eff0 in Htf.  rewrite Htf in H. exact H.
  Qed. 


  

  Lemma continuation_expr_to_eff es e:
    to_eff0 es = Some e ->
    continuation_expr es ->
    exists vs n f es',  es = v_to_e_list vs ++ [AI_frame n f es'].
  Proof.
    intros Htf Hes.
    destruct Hes as [(vs & i & tf & ->) | [(vs & i & ->) | [(vs & n & f0 & es0 & ->) | [(vs & ->) | [Hes | (vs & vs' & k & tf & ->)]]]]].
    all: try specialize (v_to_e_is_const_list vs) as Hvs.
    - unfold to_eff0 in Htf.
      rewrite map_app merge_app in Htf.
      apply const_list_to_val in Hvs as (?&?&?).
      unfold to_val0 in H.
      destruct (merge_values _) => //.
      inversion H; subst v.
      simpl in Htf.
      done.
    - unfold to_eff0 in Htf.
      rewrite map_app merge_app in Htf.
      apply const_list_to_val in Hvs as (?&?&?).
      unfold to_val0 in H.
      destruct (merge_values _) => //.
      inversion H; subst v.
      simpl in Htf.
      done.
    - eauto.
    - unfold to_eff0 in Htf.
      rewrite map_app merge_app in Htf.
      apply const_list_to_val in Hvs as (?&?&?).
      unfold to_val0 in H.
      destruct (merge_values _) => //.
      inversion H; subst v.
      simpl in Htf.
      destruct x => //. 
    - apply const_list_to_val in Hes as (?&?&?).
      exfalso; eapply to_val_to_eff; eauto.
    - unfold to_eff0 in Htf.
      rewrite map_app merge_app in Htf.
      apply const_list_to_val in Hvs as (?&?&?).
      unfold to_val0 in H.
      destruct (merge_values _) => //.
      inversion H; subst v.
      simpl in Htf.
      done.
  Qed.

  Lemma hfilled_continuation_expression x h vs LI:
     is_true (const_list vs) ->
     is_true (hfilled x (hholed_of_valid_hholed h) vs LI) ->
     continuation_expr LI.
   Proof.
     destruct h => //=.
     all: intros Hvs Hfill.
     all: move/hfilledP in Hfill; inversion Hfill; subst.
     { rewrite catA. apply const_es_exists in Hvs as [? ->].
       rewrite v_to_e_cat. left. repeat eexists. }
     right; right; left. eauto.
   Qed.

   Lemma those_map_is_Some {A B} f (l : list A) (l' : list B) k x:
     those (map f l) = Some l' ->
     nth_error l k = Some x ->
     exists x', f x = Some x'.
   Proof.
     generalize dependent l'. generalize dependent k. 
     induction l; intros.
     simpl in H. inversion H; subst.
     destruct k => //.
     destruct k => //=.
     simpl in H0.
     inversion H0; subst.
     simpl in H.
     rewrite separate1 in H.
     apply those_app_inv in H as (? & ? & ? & ? & ?).
     rewrite /those /= in H.
     destruct (f x) => //.
     by eexists.
     simpl in H0.
     rewrite /= separate1 in H.
     apply those_app_inv in H as (? & ? & ? & ? & ?).
     eapply IHl.
     exact H1.
     exact H0.
   Qed.


   Lemma to_of_valid_hholed h:
     valid_hholed_of_hholed (hholed_of_valid_hholed h) = Some h.
   Proof.
     destruct h => //=.
     all: rewrite e_to_v_v_to_e => //.
   Qed.


   Lemma hhplug_vhh_plug vs vhh:
    hhplug (v_to_e_list vs) (hholed_of_valid_hholed vhh) =
    hholed_of_valid_hholed $ vhh_plug vs vhh.
   Proof.
     destruct vhh => //=.
     by rewrite v_to_e_cat.
   Qed.

   Lemma of_to_continuation_resource h:
     resource_of_continuation (continuation_of_resource h) = Some h.
   Proof.
     destruct h => //=.
     rewrite to_of_valid_hholed //.
   Qed.


   

   
  
   Lemma ewp_empty_frame ts dccs es f E Ψ Φ :
    continuation_expr es ->
    EWP [AI_prompt ts dccs es] UNDER empty_frame @ E <| Ψ |> {{ v ; _ , Φ v }}
      ⊢ EWP [AI_prompt ts dccs es] UNDER f @ E <| Ψ |> {{ v ; f' , Φ v ∗ ⌜ f' = f ⌝  }}.
  Proof.
    iLöb as "IH" forall (es ts dccs E Ψ Φ f).
    iIntros (Hes) "Hes".
    Opaque upcl.
    do 2 rewrite ewp_unfold /ewp_pre /=.
    
    destruct (to_val0 [AI_prompt ts dccs es]) eqn:Htv.
    { iMod "Hes" as "Hv".
      iModIntro. iSplit; done. } 
    destruct (to_eff0 [AI_prompt ts dccs es]) eqn:Htf.
    { rewrite /to_eff0 /= in Htf.
      destruct (merge_values (List.map _ es)) eqn:Htf' => //.
      destruct v => //.
      destruct e0 => //.
      destruct (suselts_of_continuation_clauses _ _) => //.
      2: destruct (swelts_of_continuation_clauses _ _) => //.
      all: simpl in Htf.
      all: inversion Htf; subst.
      3: done.
      all: eapply continuation_expr_to_eff in Hes as (vs' & n & f' & es' & ->);
        last by rewrite /to_eff0 Htf'.
      2: destruct i. 
      2: iDestruct "Hes" as (cont t1s t2s tf' ts0 q) "(? & Htag & Hcont & -> & -> & HΨ & Hes)"; iFrame.
      2: iExists _,_,_; iSplit; first done.
      2: iSplit; first done.
      2: iIntros "Htag".
      2: iPoseProof ("Hes" with "Htag") as "Hes".
      all: iApply (monotonic_prot with "[-Hes] Hes").
      all: iIntros (w) "H".
      all: iNext.
      all: simpl.
      all: iApply "IH".
      all: iFrame.
      all: rewrite map_app merge_app in Htf'.
      all: specialize (v_to_e_is_const_list vs') as Hvs.
      all: apply const_list_to_val in Hvs as (? & Hvs & ?).
      all: rewrite /to_val0 in Hvs.
      all: destruct (merge_values _) => //.
      all: inversion Hvs; subst.
      all: simpl in Htf'.
      all: destruct (merge_values (List.map _ es')) => //.
      all: try by destruct v.
      all: destruct e => //.
      all: simpl in Htf'.
      all: inversion Htf'; subst. 
      all: iPureIntro; right; right; left; eauto.
    }

    iIntros (s) "Hs".
    iDestruct "Hs" as "(Hf & Hc & Hrest)".
    destruct (resources_of_s_cont _) eqn:Hconts => //.
    iSpecialize ("Hes" with "[Hf Hc Hrest]").
    { instantiate (1 := s).
      iFrame. rewrite Hconts; iFrame. } 
    iMod "Hes" as "[%Hred Hes]".
    iModIntro.
    
    iSplit.
    { iPureIntro.
      destruct Hred as (obs & [es' f'] & σ' & efs & Hred & -> & ->).
      eapply continuation_prompt_ignores_frame in Hred as [Hred <-]; last done.
      eexists [], (_,_), _, [].
      split; last done.
      exact Hred. } 
    iIntros ([es2 f2] s2 Hstep).
    destruct Hstep as [Hstep _].
    eapply continuation_prompt_ignores_frame in Hstep as [Hstep ->]; last done.
    iMod ("Hes" with "[]") as "Hes".
    iPureIntro.
    instantiate (2 := (_,_)).
    repeat split => //.
    
    exact Hstep.
    iModIntro.
    iNext.
    iMod "Hes".
    iModIntro.
    iMod "Hes" as "[Hs2 Hes2]".
    iModIntro.
    iFrame.
    apply reduce_in_prompt in Hstep as [(esf & Hstep & ->) | [ (-> & Hconst & _ & ->) | [ (lh & Htrap & -> & _ & ->) | [ (vs & i & sh & l' & t1s & t2s & Htf' & Hclauses & Htags & -> & _ & ->) | (vs & k & t1s & t2s & t1s' & hh' & tf & i & sh & LI & Htf' & Hk & Hclauses & Hfill & -> & _ & ->)]]]].
    - iApply "IH".
      2: iFrame.
      iPureIntro.
      eapply continuation_preservation.
      exact Hstep. exact Hes.
    - apply const_list_to_val in Hconst as (? & Htv' & ?).
      do 2 rewrite ewp_unfold /ewp_pre /= Htv'.
      iMod "Hes2". iFrame. done.
    - do 2 rewrite ewp_unfold /ewp_pre /=.
      iMod "Hes2". iFrame. done.
    - do 2 rewrite ewp_unfold /ewp_pre /= /to_val0 /to_eff0 map_app merge_app.
      specialize (v_to_e_is_const_list vs) as Hvs.
      apply const_list_to_val in Hvs as (? & Hvs & ?).
      unfold to_val0 in Hvs.
      destruct (merge_values _) => //.
      inversion Hvs; subst; simpl.
      iMod "Hes2".
      iFrame. done.
    - iApply "IH".
      2: iFrame.
      iPureIntro.
      eapply those_map_is_Some in Hconts.
      2: exact Hk.
      destruct Hconts as [rh Hcont].
      apply to_of_continuation_resource in Hcont.
      destruct rh => //.
      inversion Hcont; subst.
      
      eapply hfilled_continuation_expression.
      2: exact Hfill.
      apply const_list_concat => //.
      apply v_to_e_is_const_list.
  Qed. 




     Lemma resources_of_s_cont_update σ l h h' addr :
     resources_of_s_cont (s_conts σ) = Some l ->
     resource_of_continuation h = Some h' ->
     addr < length (s_conts σ) ->
     resources_of_s_cont
       (s_conts (upd_s_cont σ addr h)) = Some (update_list_at l addr h').
   Proof.
     generalize dependent addr. generalize dependent l.
     unfold upd_s_cont. simpl.
     remember (s_conts σ) as conts.
     clear Heqconts.
     induction conts; first by simpl; lia.
     intros l addr Hconts Hcont Haddr.
     rewrite /resources_of_s_cont /= in Hconts.
     rewrite separate1 in Hconts.
     apply those_app_inv in Hconts as (l1 & l2 & Hl1 & Hl2 & <-).
     rewrite /those /= in Hl1.
     destruct (resource_of_continuation a) eqn:Ha => //.
     inversion Hl1; subst; clear Hl1.

     destruct addr.
     { unfold replace_nth_cont.
       simpl. rewrite drop0.
       rewrite /update_list_at /=. rewrite drop_0.
       rewrite /resources_of_s_cont /=.
       rewrite separate1 (separate1 h').
       apply those_app.
       rewrite Hcont. done.
       done. }
     simpl.
     rewrite /replace_nth_cont /=.
     rewrite /update_list_at /=.
     rewrite /resources_of_s_cont /= Ha.
     rewrite (separate1 (Some c)) (separate1 c).
     apply those_app => //.
     apply IHconts => //.
     simpl in Haddr. lia.
   Qed.

   Lemma resources_of_s_cont_new σ l h h' :
     resources_of_s_cont (s_conts σ) = Some l ->
     resource_of_continuation h = Some h' ->
     resources_of_s_cont
       (s_conts (new_cont σ h)) = Some (l ++ [h']).
   Proof.
     intros Hconts Hcont.
     rewrite /new_cont /=.
     rewrite /resources_of_s_cont map_app /= Hcont.
     apply those_app => //. 
   Qed.

   Lemma resources_of_s_cont_length conts l :
     resources_of_s_cont conts = Some l ->
     length conts = length l.
   Proof.
     apply length_those.
   Qed.
 


  
  Lemma ewp_prompt_empty_frame ts dccs es E Ψ Ψ' Φ Φ' :
    agree_on_uncaptured dccs Ψ Ψ' ->
     continuation_expr es ->
    (    (∀ f, ¬ Φ trapV f) ∗ EWP es UNDER empty_frame @ E <| Ψ |> {{ Φ }} ∗
      (∀ w, Φ w empty_frame -∗ EWP [AI_prompt ts dccs (of_val0 w)] UNDER empty_frame @ E <| Ψ' |> {{ Φ' }}) ∗
      [∗ list] dcc ∈ dccs, clause_triple E Ψ Φ dcc ts Ψ' Φ')%I
      ⊢ EWP [AI_prompt ts dccs es] UNDER empty_frame @ E <| Ψ' |> {{ Φ' }}.
  Proof.
    iLöb as "IH" forall (ts dccs es E Ψ Ψ' Φ Φ').
    iIntros (HΨ Hes) "(Hntrap & Hes & HΦ & Hclauses)".
    destruct (to_val0 es) eqn:Htv.
    { iDestruct ewp_value_fupd as "[H _]";
        last iDestruct ("H" with "Hes") as "Hes".
      exact Htv.

      iApply fupd_ewp.
      unfold to_eff0. simpl.
      unfold to_val0 in Htv.
      destruct (merge_values _) => //.
      destruct v0 => //.
      iMod "Hes" as "Hes".
      iDestruct ("HΦ" with "Hes") as "Hres".
      iModIntro.
      erewrite of_to_val0 => //.
    }
    destruct (to_eff0 es) eqn:Htf.
    { eapply continuation_expr_to_eff in Hes as Heq.  
      2: exact Htf.
      destruct Heq as (vs & n & f & LI & Heqes).
        

      destruct e.
      - iDestruct (ewp_effect_sus with "Hes") as "Hes" ; eauto.
        remember (Logic.eq_refl (to_eff0 [AI_prompt ts dccs es])) as Htf'; clear HeqHtf'.
        unfold to_eff0 in Htf' at 2.
        simpl in Htf'.
        remember Htf as Htf0; clear HeqHtf0.
        unfold to_eff0 in Htf.
        destruct (merge_values _) => //.
        inversion Htf; subst e.
        destruct (suselts_of_continuation_clauses dccs i) eqn:Helts.
        + simpl in Htf'.
          subst.
          iApply ewp_effect_sus; eauto.
          remember HΨ as HΨ'; clear HeqHΨ'.
          destruct HΨ as [HΨ _].
          rewrite -HΨ.
          2: by eapply suselts_firstx.
          iApply (monotonic_prot with "[-Hes] Hes").
          iIntros (w) "Hw".
          iNext. iSimpl.
          erewrite suselts_of_continuation_clauses_inj => //.
          unfold to_eff0 in Htf'.
          simpl in Htf'.
          specialize (v_to_e_is_const_list vs) as Hvs.
          apply const_list_to_val in Hvs as (? & Hvs & ?).
          unfold to_val0 in Hvs.
          rewrite map_app merge_app in Htf'.
          destruct (merge_values (List.map _ (_ vs))) => //.
          inversion Hvs; subst.
          simpl in Htf'.
          destruct (merge_values (List.map _ LI)) eqn:HLI => //.
          destruct v => //.
          destruct e => //.
          2:{ simpl in Htf' => //.
              destruct (swelts_of_continuation_clauses _ _) => //. } 
          simpl in Htf' => //.
          destruct (suselts_of_continuation_clauses _ i0) eqn:Helts' => //.
          simpl in Htf'.
          inversion Htf'; subst.
          iApply "IH".
          done.
          iPureIntro; right; right; left. eauto.
          iFrame.
          done.
        + simpl in Htf'.
          apply suselts_of_continuation_clauses_None in Helts as [x Hfirst].
          iApply ewp_lift_step => //.
          apply to_val_None_prompt => //.
          iIntros (σ) "Hσ".
          iApply fupd_mask_intro; first solve_ndisj.
          iIntros "Hclose".
          destruct i.
          apply firstx_suspend_lookup in Hfirst as Hfirst'.
          destruct Hfirst' as [k Hk].
          iDestruct (big_sepL_lookup with "Hclauses") as "Hclause".
          exact Hk.
          iDestruct "Hclause" as (t1s t2s q) "[Hclres Hclause]".
          iDestruct "Hσ" as "(Hfuncs & Hconts & Hexns & Htags & Hrest)".
          iDestruct (gen_heap_valid with "Htags Hclres") as %Htag.
          rewrite gmap_of_list_lookup in Htag.
          rewrite -nth_error_lookup in Htag.
          eassert (reduce σ _ [AI_prompt ts dccs es] _ _ _).
          { eapply r_suspend.
            done.
            eauto.
            rewrite Nat2N.id.
            exact Hfirst.
            apply of_to_eff0 in Htf0.
            unfold of_eff in Htf0.

            rewrite Nat2N.id.
            rewrite -Htf0. apply susfill_to_hfilled. }
          iSplit.
          { iPureIntro.
            unfold reducible.
            eexists _, (_, _) , _, _.
            repeat split => //. eauto. }
            
          iIntros (es2 σ2 ? Hstep).
          destruct Hstep as (Hstep & _ & _).
          
          edestruct reduce_det. 
          exact Hstep. exact H.
          subst.
          destruct H1 as [(-> & ->) | Habs].
          * iFrame.
            rewrite /to_eff0 /= in Htf0.
            specialize (v_to_e_is_const_list vs) as Hvs.
          apply const_list_to_val in Hvs as (? & Hvs & ?).
          unfold to_val0 in Hvs.
          rewrite map_app merge_app in Htf0.
          destruct (merge_values (List.map _ (_ vs))) => //.
          inversion Hvs; subst.
          simpl in Htf0.
            destruct (merge_values (List.map _ LI)) eqn:HLI => //.
            destruct v => //.
            destruct e => //.
            simpl in Htf0.
            inversion Htf0; subst.

            iModIntro.
            iMod "Hclose".
            destruct (resources_of_s_cont (s_conts σ)) eqn:Hσ; last done. 
          
            iMod (gen_heap_alloc with "Hconts") as "(Hconts & Hcont & Htok)";
              last first.
            iModIntro.

            iFrame.
            iSplitL "Hconts".
            { unfold new_cont. simpl.
              instantiate (2 := N.of_nat (length (s_conts σ))).
              unfold resources_of_s_cont.
              rewrite map_app.
              erewrite those_app.
              2: exact Hσ.
              2:{ simpl. rewrite e_to_v_v_to_e. done. } 
              simpl.
              apply length_those in Hσ as Hlen.
              rewrite Hlen.
              rewrite -gmap_of_list_append.
              iExact "Hconts". }
            2:{ rewrite gmap_of_list_lookup.
                rewrite Nat2N.id.
                apply lookup_ge_None_2.
                apply length_those in Hσ.
                lia. }
            iApply ("Hclause" with "Hclres Hcont").
            iApply (monotonic_prot with "[-Hes] Hes").
            iIntros (w) "Hw".
            specialize (susfill_to_hfilled (Mk_tagidx n0) sh0 (v_to_e_list w)) as Hfilled.
            iExists _.
            iSplit; first iPureIntro.
            apply hfilled_forget_avoiding in Hfilled.
            simpl. unfold hfilled, hfill; fold hfill.
            rewrite v_to_e_is_const_list.
            simpl.
            unfold hfilled in Hfilled.
            destruct (hfill _ _ _) => //.
            apply b2p in Hfilled.
            rewrite -Hfilled cats0.
            specialize ( (@eqtype.eq_refl
                            (seq.Datatypes_list__canonical__eqtype_Equality
                               administrative_instruction_eqType)
                            (v_to_e_list x0 ++ [AI_frame n f (susfill (Mk_tagidx n0) sh0 (v_to_e_list w))]))) as Hres.
            instantiate (1 := v_to_e_list x0 ++ [AI_frame n f (susfill (Mk_tagidx n0) sh0 (v_to_e_list w))]).
            destruct (eqtype.eq_op _ _) => //. 


            iNext.
            rewrite cats0. iExact "Hw".
          * apply susE_first_instr in Htf0 as [k' Htf0].
            
            rewrite first_instr_const in Habs; last by apply v_to_e_is_const_list.
            unfold first_instr in Habs.
            unfold first_instr in Htf0.
            simpl in Habs.
            simpl in Htf0.
            
            destruct (find_first_some (List.map _ (_ ++ [_]))) => //.
            destruct p.
            exfalso.
            destruct Habs as [(? & Habs) | (? & ? & ? & Habs & _)] => //.
            all: inversion Htf0; inversion Habs; subst => //. 
      - destruct i. iDestruct (ewp_effect_sw with "Hes") as "Hes" ; eauto.
        remember (Logic.eq_refl (to_eff0 [AI_prompt ts dccs es])) as Htf'; clear HeqHtf'.
        unfold to_eff0 in Htf' at 2.
        simpl in Htf'.
        remember Htf as Htf0; clear HeqHtf0.
        unfold to_eff0 in Htf.
        destruct (merge_values _) => //.
        inversion Htf; subst.
        destruct (swelts_of_continuation_clauses dccs (Mk_tagidx _)) eqn:Helts.
        + simpl in Htf'.
          iApply ewp_effect_sw; eauto.
          remember HΨ as HΨ'; clear HeqHΨ'.
          destruct HΨ as (_ & HΨ & _).
  iDestruct "Hes" as (cont t1s t2s tf' ts0 q0) "(? & Htag & Hk & -> & -> & Hcont & Hes)".
          iFrame. iExists _,_,_. iSplit; first done.
          iSplit; first done.
          unfold get_switch2, get_switch1.
          rewrite -HΨ.
          iFrame.
          2: by eapply swelts_firstx.
          
          iIntros "Htag".
          iPoseProof ("Hes" with "Htag") as "Hes".
          iApply (monotonic_prot with "[-Hes] Hes").
          iIntros (w) "Hw".
          iNext. Opaque continuation_clause_of_swelt.
          iSimpl.
          erewrite swelts_of_continuation_clauses_inj => //.
          unfold to_eff0 in Htf'.
          simpl in Htf'.
          specialize (v_to_e_is_const_list vs) as Hvs.
          apply const_list_to_val in Hvs as (? & Hvs & ?).
          unfold to_val0 in Hvs.
          rewrite map_app merge_app in Htf'.
          destruct (merge_values (List.map _ (_ vs))) => //.
          inversion Hvs; subst.
          simpl in Htf'.
          destruct (merge_values (List.map _ LI)) eqn:HLI => //.
          destruct v => //.
          destruct e => //.
          simpl in Htf' => //.
          destruct (suselts_of_continuation_clauses _ _) => //. 
          simpl in Htf' => //.
          destruct (swelts_of_continuation_clauses _ i) eqn:Helts' => //.
          simpl in Htf'.
          inversion Htf'; subst.
          iApply "IH".
          done.
          iPureIntro.
          right; right; left. eauto.

          iFrame.
          done.

        + simpl in Htf'.
          apply swelts_of_continuation_clauses_None in Helts as Hfirst.
          iApply ewp_lift_step => //.
          apply to_val_None_prompt => //.
          iIntros (σ) "Hσ".
          iApply fupd_mask_intro; first solve_ndisj.
          iIntros "Hclose".
          apply firstx_switch_lookup in Hfirst as Hfirst'.
          destruct Hfirst' as [k' Hk].
          iDestruct (big_sepL_lookup_acc with "Hclauses") as "[Hclause Hrefill]".
          exact Hk.
          iDestruct "Hclause" as "(%q & Hclres & #Hclause)".
          iDestruct "Hσ" as "(Hfuncs & Hconts & Hexns & Htags & Hrest)".
          iDestruct (gen_heap_valid with "Htags Hclres") as %Htag.
          rewrite gmap_of_list_lookup in Htag.
          rewrite -nth_error_lookup in Htag.
          iDestruct "Hes" as (cont t1s' t2s' tf' ts0 q0) "(%Hconst & Htag & Hk & -> & -> & Hcont & Hes)".
          iDestruct (pointsto_agree with "Hclres Htag") as %Heq.
          inversion Heq; subst ts0. 
          destruct (resources_of_s_cont _) eqn:Hconts => //. 
          iDestruct (gen_heap_valid with "Hconts Hk") as %Hcont.
          rewrite gmap_of_list_lookup -nth_error_lookup in Hcont.
          eapply resources_of_s_cont_lookup in Hcont; last exact Hconts.
          rewrite Nat2N.id in Hcont. 
          assert (exists LI', is_true $ hfilled No_var (hholed_of_valid_hholed cont)
    (v_to_e_list vs0 ++ [:: AI_ref_cont (length (s_conts σ))]) 
    LI') as [? Hassump].
          { by apply iris_lfilled_properties.fillable_constant_hholed. } 
          eassert (reduce σ (Build_frame _ _) [AI_prompt _ dccs _] _ _ _).
          { eapply r_switch.
            exact Hfirst.
            done.
            exact Hcont. 
            apply swfill_to_hfilled.
            exact Hassump. 
          }
          iSplit.
          { iPureIntro.
            unfold reducible.
            eexists _, (_,_), _, _.
            repeat split => //.
            apply of_to_eff0 in Htf0.
            unfold of_eff0 in Htf0.
            rewrite -Htf0.
            exact H. 
          } 

            assert (k < length (s_conts σ) /\ k < length l) as [Hlen1 Hlen2].
            { rewrite nth_error_lookup in Hcont.
              apply lookup_lt_Some in Hcont.
              split; first done.
              apply resources_of_s_cont_length in Hconts.
              rewrite Hconts in Hcont. done. } 

          
          iIntros "!>" (es2 f2 σ2 Hstep).
          destruct Hstep as (Hstep & _ & _).
          
          edestruct reduce_det. 
          { exact Hstep. } 
          { apply of_to_eff0 in Htf0.
            unfold of_eff0 in Htf0.
            rewrite -Htf0.
            exact H. } 
          subst f2.
          destruct H1 as [(-> & ->) | Habs].
          * iFrame.
            rewrite /to_eff0 /= in Htf0.
            specialize (v_to_e_is_const_list vs) as Hvs.
            apply const_list_to_val in Hvs as (? & Hvs & ?).
            unfold to_val0 in Hvs.
            rewrite map_app merge_app in Htf0.
            destruct (merge_values (List.map _ (_ vs))) => //.
            inversion Hvs; subst.
            simpl in Htf0.
            destruct (merge_values (List.map _ LI)) eqn:HLI => //.
            destruct v => //.
            destruct e => //.
            simpl in Htf0.
            inversion Htf0; subst.
            erewrite resources_of_s_cont_new.
            2:{ apply resources_of_s_cont_update.
                exact Hconts. done. done. } 
            2:{ simpl. rewrite e_to_v_v_to_e. done. }  
            iMod (gen_heap_update with "Hconts Hk") as "[Hconts Hk]".
            iMod (gen_heap_alloc with "Hconts") as "(Hconts & Hk' & Htok)".
            { instantiate (2 := N.of_nat (length l)).
              rewrite lookup_insert_ne; last lia.
              rewrite gmap_of_list_lookup.
              rewrite Nat2N.id.
              apply lookup_ge_None.
              lia. } 
            rewrite -gmap_of_list_insert.
            2:{ rewrite Nat2N.id. done. }
            rewrite Nat2N.id.
            eassert (length l = length (<[ k := _ ]> l)) as Hlenl.
            { rewrite length_insert. done. }
            rewrite Hlenl.
            erewrite <- gmap_of_list_append.
            rewrite -Hlenl.
            rewrite update_list_at_insert; last done.
            iFrame.
            iDestruct ("Hclause" with "Hcont [] Hk' [Hes Htag]") as (?) "(%Hfill & H)".
            { done. }
            { iPoseProof ("Hes" with "Htag") as "Hes".
              iApply (monotonic_prot with "[] Hes").
              iIntros (w) "H".
              iExists _.
              iSplit; last first.
              iNext. iExact "H".
              iPureIntro.
              simpl.
              apply/hfilledP.
              constructor.
              rewrite cats0. apply v_to_e_is_const_list.
              apply/hfilledP.
              eapply hfilled_forget_avoiding.
              apply swfill_to_hfilled. }

            apply resources_of_s_cont_length in Hconts.
            rewrite -Hconts in Hfill.
            eapply hfilled_inj in Hfill.
            2: exact Hassump.
            subst x.
            iMod "Hclose" as "_".
            iModIntro.
            iApply "IH"; last first.
            -- iFrame.
               iApply "Hrefill".
               iFrame "#".
               iFrame.
            -- iPureIntro.
               eapply hfilled_continuation_expression; eauto.
               apply const_list_concat => //.
               apply v_to_e_is_const_list.
            -- iPureIntro. done.
          * apply swE_first_instr in Htf0 as [k0 Htf0].
            unfold first_instr in Habs.
            unfold first_instr in Htf0.
            simpl in Habs.
            rewrite Htf0 in Habs.
            exfalso.
            destruct Habs as [(? & Habs) | (? & ? & ? & Habs & _)] => //. 
      - iDestruct (ewp_effect_thr with "Hes") as "Hes" ; eauto. 
        remember (Logic.eq_refl (to_eff0 [AI_prompt ts dccs es])) as Htf'; clear HeqHtf'.
        unfold to_eff0 in Htf' at 2.
        simpl in Htf'.
        remember Htf as Htf0; clear HeqHtf0.
        unfold to_eff0 in Htf.
        destruct (merge_values _) => //.
        inversion Htf; subst.
        simpl in Htf'.
        iApply ewp_effect_thr ; eauto.
        iFrame.
        remember HΨ as HΨ'; clear HeqHΨ'.
        destruct HΨ as (_ & _ & HΨ).
        rewrite -HΨ.
        iExact "Hes".
    }
    iApply ewp_unfold.
    rewrite /ewp_pre /= to_val_None_prompt // to_eff_None_prompt //.
    iIntros (σ) "Hσ".

    
    rewrite ewp_unfold /ewp_pre.
    rewrite /= Htv Htf.
    iMod ("Hes" with "Hσ") as "[%Hred Hes]".
    iModIntro.
    iSplit.
    { iPureIntro.
      destruct Hred as (obs & [es' f'] & σ' & efs & Hred & -> & ->).
      eassert _ as Hred'.
      { eapply r_label.
        exact Hred.
        instantiate (2 := LH_prompt [] ts dccs (LH_base [] []) []).
        instantiate (2 := 0).
        rewrite /lfilled /lfill /= app_nil_r //.
        rewrite /lfilled /lfill /= app_nil_r //. } 
      eapply continuation_prompt_ignores_frame in Hred' as [Hred' <-]; last done.
      eexists [], (_,_), _, [].
      split; last done.
      exact Hred'. } 
    iIntros ([es2 f2] σ2 Hstep).
    eapply lfilled_prim_step_split_reduce_r in Hstep as Hstep0.
    2:{ instantiate (1 := []).
        instantiate (1 := es).
        instantiate (1 := LH_prompt [] ts dccs (LH_base [] []) []).
        instantiate (1 := 0).
        unfold lfilled, lfill => //=.
        repeat rewrite app_nil_r.
        rewrite eqtype.eq_refl => //. }
    2:{ destruct Hred as (obs & [es' f'] & σ' & efs & Hred & -> & ->).
        eapply continuation_ignores_frame in Hred as [Hred <-]; last done.
        eexists [], (_,_), _, [].
        split; last done.
        exact Hred. } 

    destruct Hstep as [Hstep _].
    apply reduce_stays_empty_frame in Hstep as Hf2.
    subst.
    destruct Hstep0 as [(e' & Hstep' & Hfill') | ([lh Htrap] & Hσ)].
    - iDestruct ("Hes" $! (_,_) _ Hstep') as "Hes".
      iSimpl.
      iMod "Hes".
      repeat iModIntro.
      repeat iMod "Hes".
      iModIntro.
      iDestruct "Hes" as "(Hσ & He')".

      iFrame.
      unfold lfilled, lfill in Hfill'.
      simpl in Hfill'.
      rewrite app_nil_r in Hfill'.
      rewrite cat_app app_nil_r in Hfill'.
      apply b2p in Hfill' as ->.
      iApply ("IH" with "[] [] [-]"). done.
      iPureIntro. eapply continuation_preservation.
      destruct Hstep' as [Hred' _]. exact Hred'.
      done.
      iFrame. 
    - inversion Hσ; subst σ.
      assert (prim_step (es, empty_frame) σ2 [] ([AI_trap], empty_frame) σ2 []).
      { repeat split => //.
        constructor. econstructor. 2: exact Htrap.
        intros ->; by simpl in Htv. } 
      iDestruct ("Hes" $! (_,_) _ H) as "Hes".
      iMod "Hes".
      repeat iModIntro.
      repeat iMod "Hes".
      iDestruct "Hes" as "(Hσ & Hes)".
      iDestruct ewp_value_fupd as "[H _]".
      instantiate (1 := trapV) => //.
      instantiate (1 := [AI_trap]) => //.
      
      iMod ("H" with "Hes") as "Habs".
      iDestruct ("Hntrap" with "Habs") as "Habs" => //.
  Qed.


   Lemma ewp_prompt ts dccs es E Ψ Ψ' Φ Φ' f:
     agree_on_uncaptured dccs Ψ Ψ' ->
     continuation_expr es ->
    ((∀ f, ¬ Φ trapV f) ∗ ¬ Φ' trapV ∗ EWP es UNDER empty_frame @ E <| Ψ |> {{ Φ }} ∗
      (∀ w, Φ w empty_frame -∗ EWP [AI_prompt ts dccs (of_val0 w)] UNDER empty_frame @ E <| Ψ' |> {{ v ; _ , Φ' v }}) ∗
      [∗ list] dcc ∈ dccs, clause_triple E Ψ Φ dcc ts Ψ' (λ v _, Φ' v) )%I
      ⊢ EWP [AI_prompt ts dccs es] UNDER f @ E <| Ψ' |> {{ v; f', Φ' v ∗ ⌜ f' = f ⌝ }}.
   Proof.
     iIntros (HΨ Hes) "(HΦ & HΦ' & Hes & Hnext & Htriples)".
     iApply ewp_empty_frame.
     done.
     iApply ewp_prompt_empty_frame.
     exact HΨ.
     done.
     instantiate (1 := Φ).
     iFrame.
   Qed.









 
  Lemma ewp_resume vs addr i ccs dccs LI E Ψ Ψ' Φ Φ' t1s t2s h f:
    is_true (const_list vs) ->
    stypes f.(f_inst) i = Some (Tf t1s t2s) ->
    length vs = length t1s ->
    map (desugar_continuation_clause (f_inst f)) ccs = map Some dccs ->
    agree_on_uncaptured dccs Ψ Ψ' ->
    is_true (hfilled No_var (hholed_of_valid_hholed h) vs LI) ->

 
    (N.of_nat addr ↦[wcont] Live (Tf t1s t2s) h ∗
       (∀ f, ¬ Φ trapV f) ∗ ¬ Φ' trapV ∗
       ▷ EWP LI UNDER empty_frame @ E <| Ψ |> {{ Φ }} ∗
       ▷ (∀ w, Φ w empty_frame -∗ EWP [AI_prompt t2s dccs (of_val0 w)] UNDER empty_frame @ E <| Ψ' |> {{ v; _ , Φ' v }}) ∗
       ▷ [∗ list] dcc ∈ dccs, clause_triple E Ψ Φ dcc t2s Ψ' (λ v _, Φ' v)
        )%I
      ⊢ EWP vs ++ [AI_ref_cont addr ; AI_basic $ BI_resume i ccs] UNDER f @ E <| Ψ' |> {{ v ; f', Φ' v ∗ ⌜ f' = f ⌝ }}.
  Proof.
    iIntros (Hvs Hi Hlen Hclauses HΨ HLI) "(Hcont & Hntrap & Hntrap' & HΦ & Hnext & Hclauses)".
    iApply ewp_lift_step => //.
    { rewrite to_val_cat_None2 => //. } 
    { rewrite to_eff_cat_None2 => //. } 
    iIntros (σ) "Hσ".
    iApply fupd_frame_l.
    iDestruct "Hσ" as "(Hfuncs & Hconts & Htags & Htables & Hmems & Hglobals & Hframe & Hrest)".
    destruct (resources_of_s_cont (s_conts σ)) eqn:Hconts => //. 
    iDestruct (gen_heap_valid with "Hconts Hcont") as "%Hlook".
    rewrite gmap_of_list_lookup Nat2N.id in Hlook.
    rewrite - nth_error_lookup in Hlook.
    eapply resources_of_s_cont_lookup in Hlook as Hlook'; last exact Hconts.


    
    assert (reduce σ f
              (vs ++ [AI_ref_cont addr; AI_basic (BI_resume i ccs)])
              (upd_s_cont σ addr (Cont_dagger (Tf t1s t2s))) f
              [AI_prompt t2s dccs LI]
           ) as Hred2.
    { eapply r_resume => //.
      destruct (const_list vs) => //.
      exact Hlook'.
      exact HLI.
    }
    iSplit.
    - iPureIntro.
      unfold language.reducible, language.prim_step => /=.
      eexists [], (_, _), _, [].
      repeat split => //.
      exact Hred2.

    - iApply fupd_mask_intro; first solve_ndisj.
      iIntros "Hclose !>" (es σ2 ? HStep).
      destruct HStep as (H & _).
      edestruct reduce_det.
      exact H. exact Hred2.
      subst.
      destruct H1 as [[-> ->] | H0].
      2:{ destruct H0.
          destruct H0 as (? & Habs).
          by rewrite first_instr_const in Habs.
          destruct H0 as (? & ? & ? & Habs & _).
          rewrite first_instr_const in Habs => //.
      }
      iMod (gen_heap_update with "Hconts Hcont") as "[Hconts Hcont]".
      iMod "Hclose". iModIntro.
      iFrame.
      erewrite resources_of_s_cont_update.
      2: exact Hconts.
      2: done.
      2:{ apply nth_error_Some.
          by rewrite Hlook'. }
      iSplitL "Hconts".
      { unfold update_list_at. simpl.
        unfold replace_nth_cont.
        rewrite - gmap_of_list_insert.
        rewrite insert_take_drop.
        rewrite firstn_is_take_n.
        repeat rewrite -cat_app.
        rewrite Nat2N.id.
        replace (ssrnat.addn addr 1) with (S addr); last lias.
        done.
        all: rewrite Nat2N.id.
        all: rewrite nth_error_lookup in Hlook.
        all: apply lookup_lt_Some in Hlook.
        all: done. }
      destruct f. iApply ewp_prompt.
      exact HΨ.
      eapply hfilled_continuation_expression; eauto.
      iFrame.
  Qed.



  
  Lemma ewp_contnew addr i E Ψ ft f:
    stypes (f_inst f) i = Some ft ->
     ⊢ EWP [AI_ref addr; AI_basic $ BI_contnew i] UNDER f @ E <| Ψ |> {{ w ; f' , ∃ kaddr, ⌜ w = immV [VAL_ref $ VAL_ref_cont kaddr] ⌝ ∗ ⌜ f' = f ⌝ ∗ N.of_nat kaddr ↦[wcont] Live ft (Initial [::] addr ft) }}.
  Proof.
    iIntros (Hi).
    iApply ewp_lift_atomic_step => //=.
    iIntros (σ) "Hσ".
    iDestruct "Hσ" as "(Hfuncs & Hconts & Htags & Htabs & Hmem & Hglobs & Hframe & Hrest)".
    eassert (prim_step ([AI_ref addr; AI_basic (BI_contnew i)],_) _ [] (_,_) _ []).
    { repeat split => //=.
      apply r_contnew.
      exact Hi. done. }
    destruct (resources_of_s_cont _) eqn:Hconts => //.
    iMod (gen_heap_alloc with "Hconts") as "(Hconts & Hcont & Htok)"; last first.
    iModIntro.
    iSplit.
    { iPureIntro. repeat eexists. exact H. }
    iIntros "!>" (e2 σ2 ? HStep).
    destruct H as [H _].
    destruct HStep as [HStep _].
    edestruct reduce_det.
    exact H. exact HStep.
    subst.
    destruct H1 as [[<- <-] | H0].
    - iModIntro. iFrame.
      erewrite resources_of_s_cont_new.
      2: eauto. 2: eauto.
      iSplitL.
      erewrite <- gmap_of_list_append.
      iExact "Hconts".
      apply resources_of_s_cont_length in Hconts as ->.
      done.
    - unfold first_instr in H0.
      simpl in H0.
      destruct H0 as [(? & ?) | (? & ? & ? & ? & _)] => //.
    - rewrite gmap_of_list_lookup.
      rewrite Nat2N.id.
      apply lookup_ge_None_2.
      lia.
  Qed.

  Lemma ewp_contbind f kaddr vhh i i' vs ves ts t1s t2s Ψ :
    stypes (f_inst f) i = Some (Tf (ts ++ t1s) t2s) ->
    stypes (f_inst f) i' = Some (Tf t1s t2s) ->
    length ves = length ts ->
    ves = v_to_e_list vs ->

    N.of_nat kaddr ↦[wcont] Live (Tf (ts ++ t1s) t2s) vhh
      ⊢ EWP ves ++ [AI_ref_cont kaddr; AI_basic $ BI_contbind i i'] UNDER f
      <| Ψ |>
      {{ v; f', ∃ kaddr',
        ⌜ v = immV [VAL_ref $ VAL_ref_cont kaddr'] ⌝ ∗
        ⌜ f' = f ⌝ ∗
        N.of_nat kaddr' ↦[wcont] Live (Tf t1s t2s) (vhh_plug vs vhh)
      }}.
  Proof.
    iIntros (Htype_bef Htype_aft Hlength Hves) "Hcont_old".
    iApply ewp_lift_atomic_step => //.
    { rewrite to_val_cat_None2 => //. rewrite Hves. apply v_to_e_is_const_list. }
    { rewrite to_eff_cat_None2 => //. rewrite Hves. apply v_to_e_is_const_list. }
    iIntros (σ) "Hσ".
    iApply fupd_frame_l.
    iDestruct "Hσ" as "(Hfuncs & Hconts & Htags & Htables & Hmems & Hglobals & Hframe & Hrest)".
    destruct (resources_of_s_cont (s_conts σ)) eqn:Hconts => //.
    iDestruct (gen_heap_valid with "Hconts Hcont_old") as "%Hlook".
    rewrite gmap_of_list_lookup Nat2N.id in Hlook.
    rewrite - nth_error_lookup in Hlook.
    eapply resources_of_s_cont_lookup in Hlook as Hlook'; last exact Hconts.
    eassert (prim_step (ves ++ [AI_ref_cont kaddr; AI_basic (BI_contbind i i')],_) _ [] (_,_) _ []) as HStep.
    { repeat split => //=.
      apply r_contbind.
      rewrite Hves. apply v_to_e_is_const_list.
      exact Htype_bef.
      exact Htype_aft.
      done.
      exact Hlook'.
    }
    iSplit.
    { iPureIntro. repeat eexists. exact HStep. }

    iApply fupd_mask_intro; first solve_ndisj.
    iIntros "Hclose !>" (es σ2 ? HStep').

    destruct HStep as [Hred _].
    destruct HStep' as [Hred' _].
    edestruct reduce_det as [Hf H].
    exact Hred. exact Hred'.
    subst.

    destruct H as [[<- <-] | H].
    2 : {
      rewrite first_instr_const in H; last apply v_to_e_is_const_list.
      by destruct H as [(? & Hcontra) | (? & ? & ? & Hcontra & _)].
    }
    iFrame.

    assert (kaddr < length l) as Hkaddr_l_length.
    { apply nth_error_Some. by rewrite Hlook. }
    apply resources_of_s_cont_length in Hconts as Hl_length.

    iMod (gen_heap_update with "Hconts Hcont_old") as "[Hconts Hcont_old_dead]".
    iMod (gen_heap_alloc with "Hconts") as "(Hconts & Hcont_new & Htok)"; last first.
    iModIntro.
    iFrame "Hcont_new".
    iSplit; last done.
    erewrite resources_of_s_cont_new.
    2: {
      apply resources_of_s_cont_update.
      eauto.
      done.
      lias.
    }
    2: {
      simpl.
      rewrite hhplug_vhh_plug.
      by rewrite to_of_valid_hholed.
    }
    2: {
      rewrite Hl_length.
      rewrite -gmap_of_list_insert; last by rewrite Nat2N.id.
      rewrite gmap_of_list_lookup.
      do 2 rewrite Nat2N.id.
      apply lookup_ge_None_2.
      by rewrite length_insert.
    }
    rewrite gmap_of_list_append.
    rewrite Hl_length.
    rewrite length_update; last done.
    rewrite update_list_at_insert; last done.
    replace (kaddr) with (N.to_nat $ N.of_nat kaddr); last apply Nat2N.id.
    rewrite gmap_of_list_insert; rewrite Nat2N.id; last done.
    iApply "Hconts".
  Qed.


  Lemma ewp_resume_throw ves vcs addr i ccs dccs E Ψ Ψ' Φ Φ' t1s t2s ts h f x a:
    List.nth_error f.(f_inst).(inst_tags) x = Some a ->
    stypes f.(f_inst) i = Some (Tf t1s t2s) ->
    ves = v_to_e_list vcs ->
    length ves = length ts ->
    map (desugar_continuation_clause (f_inst f)) ccs = map Some dccs ->
    agree_on_uncaptured dccs Ψ Ψ' ->
    is_true $ iris_lfilled_properties.constant_hholed (hholed_of_valid_hholed h) ->

 
    (N.of_nat a ↦[tag] Tf ts [] ∗
       N.of_nat addr ↦[wcont] Live (Tf t1s t2s) h ∗
       (∀ f, ¬ Φ trapV f) ∗ ¬ Φ' trapV ∗
       ▷ (∀ k LI, N.of_nat k ↦[we] {| e_tag := Mk_tagidx a ; e_fields := vcs |} -∗
               ⌜ is_true (hfilled No_var (hholed_of_valid_hholed h) [AI_throw_ref_desugared vcs k (Mk_tagidx a)] LI) ⌝ -∗
                EWP LI UNDER empty_frame @ E <| Ψ |> {{ Φ }}) ∗
       ▷ (∀ w, Φ w empty_frame -∗ EWP [AI_prompt t2s dccs (of_val0 w)] UNDER empty_frame @ E <| Ψ' |> {{ v; _ , Φ' v }}) ∗
       ▷ [∗ list] dcc ∈ dccs, clause_triple E Ψ Φ dcc t2s Ψ' (λ v _, Φ' v)
        )%I
      ⊢ EWP ves ++ [AI_ref_cont addr ; AI_basic $ BI_resume_throw i x ccs] UNDER f @ E <| Ψ' |> {{ v ; f', Φ' v ∗ ⌜ f' = f ⌝ }}.
  Proof.
    iIntros (Hx Hi -> Hlen Hclauses HΨ Hconst) "(Htag & Hcont & Hntrap & Hntrap' & HΦ & Hnext & Hclauses)".
    iApply ewp_lift_step => //.
    { rewrite to_val_cat_None2 => //. apply v_to_e_is_const_list. } 
    { rewrite to_eff_cat_None2 => //. apply v_to_e_is_const_list. } 
    iIntros (σ) "Hσ".
    iApply fupd_frame_l.
    iDestruct "Hσ" as "(Hfuncs & Hconts & Hexns & Htags & Htables & Hmems & Hglobals & Hframe & Hrest)".
    iDestruct (gen_heap_valid with "Htags Htag") as %Htag.
    rewrite gmap_of_list_lookup Nat2N.id in Htag.
    rewrite - nth_error_lookup in Htag. 
    destruct (resources_of_s_cont (s_conts σ)) eqn:Hconts => //. 
    iDestruct (gen_heap_valid with "Hconts Hcont") as "%Hlook".
    rewrite gmap_of_list_lookup Nat2N.id in Hlook.
    rewrite - nth_error_lookup in Hlook.
    eapply resources_of_s_cont_lookup in Hlook as Hlook'; last exact Hconts.
    eapply iris_lfilled_properties.fillable_constant_hholed in Hconst as [??].


    
    eassert (reduce σ f
              (_ ++ [AI_ref_cont addr; AI_basic (BI_resume_throw i x ccs)])
              _ f
              [AI_prompt t2s dccs _]
           ) as Hred2.
    { eapply r_resume_throw => //.
      exact Hx. exact Htag. exact Hlen.
      exact Hlook'. exact Hi. exact H.
    }
    iSplit.
    - iPureIntro.
      unfold language.reducible, language.prim_step => /=.
      eexists [], (_, _), _, [].
      repeat split => //.
      exact Hred2.

    - iApply fupd_mask_intro; first solve_ndisj.
      iIntros "Hclose !>" (es σ2 ? HStep).
      destruct HStep as (H' & _).
      edestruct reduce_det.
      exact H'. exact Hred2.
      subst.
      destruct H1 as [[-> ->] | H0].
      2:{ destruct H0.
          destruct H0 as (? & Habs).
          by rewrite first_instr_const in Habs; try apply v_to_e_is_const_list.
          destruct H0 as (? & ? & ? & Habs & _).
          rewrite first_instr_const in Habs => //.
          apply v_to_e_is_const_list. 
      }
      iMod (gen_heap_update with "Hconts Hcont") as "[Hconts Hcont]".
      iMod (gen_heap_alloc with "Hexns") as "(Hexns & Hexn & Htok)"; last first. 
      iMod "Hclose". iModIntro.
      iFrame "Hfuncs Htags Htables Hmems Hglobals Hframe Hrest".
      erewrite resources_of_s_cont_update.
      2: exact Hconts.
      2: done.
      2:{ apply nth_error_Some.
          by rewrite Hlook'. }
      iSplitL "Hconts Hexns".
      2:{ destruct h.
          - iDestruct ("HΦ" with "Hexn []") as "HΦ".
            done.
            move/hfilledP in H; inversion H; subst.
            edestruct const_list_to_val as (? & ? & ?).
            exact H5.
                          
            iDestruct (ewp_effect_thr with "HΦ") as "HΨ".
            { rewrite /to_eff0 /=.
              rewrite map_app merge_app.
              rewrite /to_val0 /= in H0.
              destruct (merge_values _) => //.
              inversion H0; subst v.
              simpl. done. }
            iApply ewp_effect_thr.
            { rewrite /to_eff0 /=.
              rewrite map_app merge_app.
              rewrite /to_val0 /= in H0.
              destruct (merge_values _) => //.
              inversion H0; subst v.
              simpl. done. }
            destruct HΨ as (_ & _ & HΨ).
            rewrite HΨ. iFrame.
          - iApply ewp_prompt.
            exact HΨ.
            move/hfilledP in H; inversion H; subst.
            right; right; left.
            repeat eexists. 
            iFrame.
            iApply ("HΦ" with "Hexn").
            done. }
      { iSplitL "Hconts".
        - unfold update_list_at. simpl.
          unfold replace_nth_cont.
          rewrite - gmap_of_list_insert.
          rewrite insert_take_drop.
          rewrite firstn_is_take_n.
          repeat rewrite -cat_app.
          rewrite Nat2N.id.
          replace (ssrnat.addn addr 1) with (S addr); last lias.
          done.
          all: rewrite Nat2N.id.
          all: rewrite nth_error_lookup in Hlook.
          all: apply lookup_lt_Some in Hlook.
          all: done.
        - unfold add_exn. simpl.
          rewrite -gmap_of_list_append.
          iFrame.
      }
      rewrite gmap_of_list_lookup Nat2N.id.
      apply lookup_ge_None_2.
      lia.
  Qed.

End reasoning_rules.

