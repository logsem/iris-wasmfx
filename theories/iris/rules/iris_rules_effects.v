(* basic_reasoning_rules.v *)

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
        ∃ t1s t2s,
    N.of_nat taddr ↦[tag] Tf t1s t2s ∗
      ∀ vs kaddr h,
        N.of_nat taddr ↦[tag] Tf t1s t2s -∗
        N.of_nat kaddr ↦[wcont] Live (Tf t2s ts) h -∗
        iProt_car (upcl $ get_suspend (Mk_tagidx taddr) Ψ) vs (λ w, ∃ LI, ⌜ is_true $ hfilled No_var (hholed_of_valid_hholed h) (v_to_e_list w) LI ⌝ ∗ ▷ (* no calling continuations in wasm, so adding this later to symbolise that step *) EWP LI UNDER empty_frame @ E <| Ψ |> {{ Φ }}) -∗
            EWP v_to_e_list vs ++ [AI_ref_cont kaddr; AI_basic (BI_br ilab)] UNDER empty_frame @ E <| Ψ' |> {{ Φ' }}
| DC_switch (Mk_tagidx taddr) =>
    N.of_nat taddr ↦[tag] Tf [] ts ∗
      (* hmmm is this persistent modality necessary? *)   □
      ∀ vs kaddr h cont t1s tf',
      get_switch2 (Mk_tagidx taddr) Ψ cont -∗
      ⌜ tf' = Tf t1s ts ⌝ -∗
      N.of_nat taddr ↦[tag] Tf [] ts -∗
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

  (* No longer true due to persistent modality above *)
(*  Lemma monotonic_clause_triple E Ψ1 Ψ2 Φ1 Φ2 dcc ts Ψ'1 Ψ'2 Φ'1 Φ'2 :
    meta_leq Ψ2 Ψ1 -∗ 
        (∀ v f , Φ2 v f ={E}=∗ Φ1 v f) -∗
        meta_leq Ψ'1 Ψ'2 -∗
        (∀ v f, Φ'1 v f ={E}=∗ Φ'2 v f) -∗
    clause_triple E Ψ1 Φ1 dcc ts Ψ'1 Φ'1 -∗
        clause_triple E Ψ2 Φ2 dcc ts Ψ'2 Φ'2.
  Proof.
    iIntros "#HΨ HΦ #HΨ' HΦ' Htrip".
    destruct dcc => //.
    - destruct t.
      iDestruct "Htrip" as (t1s t2s) "[#Htag Htrip]".
      iExists t1s, t2s.
      iFrame "Htag".
      iIntros (vs kaddr h) "Hcont Hprot".
      iDestruct ("Htrip" $! vs kaddr h with "Hcont [HΦ Hprot]") as "Htrip".
      + iApply (monotonic_prot with "[HΦ] [Hprot]"); last first.
        * iDestruct "Hprot" as (Ψ') "[H Hnext]".
          iExists Ψ'.
          iFrame "Hnext".
          iDestruct "HΨ" as "[HΨ _]".
          iApply ("HΨ" with "H").
        * iIntros (w) "(%LI & %HLI & Hewp)".
          iExists LI; iSplit; first done.
          iNext.
          iApply (ewp_strong_mono with "Hewp [] HΦ").
          done. done.
      + iApply (ewp_strong_mono with "Htrip [] HΦ'").
        done. done.
    - destruct t.
      iDestruct "Htrip" as "[#Htag Htrip]".
      iFrame "Htag".
      iIntros (vs kaddr h cont t1s tf') "Hcont -> Hk H".
      iDestruct ("Htrip" with "[Hcont] [] Hk [H HΦ]") as "Htrip".
      + iDestruct "HΨ" as "(_ & _ & HΨ & _)". by iApply "HΨ".
      + done.
      + iDestruct "H" as (Ξ) "[HΞ H]".
        iExists Ξ. iSplitL "HΞ"; first by iDestruct "HΨ" as "(_ & HΨ & _)"; iApply "HΨ".
        iIntros (w) "Hw".
        iDestruct ("H" with "Hw") as (LI) "[%HLI H]".
        iExists LI; iSplit; first done.
        iNext.
        iApply (ewp_strong_mono with "H [] HΦ").
        done. done.
      + iDestruct "Htrip" as (LI) "(%HLI & H)".
        iExists LI; iSplit; first done.
        iApply (ewp_strong_mono with "H [] []").
        done. done. iIntros (??) "H". iExact "H".
        iIntros (??) "H".
        iDestruct ("HΦ" with "H") as "H". 
        iApply (ewp_strong_mono with "H [] HΦ'").
        done. done.
  Qed. *)

        
(*  Definition clause_resources dccs :=
    ([∗ list] dcc ∈ dccs,
      match dcc with
      | DC_catch (Mk_tagidx addr) _
      | DC_switch (Mk_tagidx addr) =>
          ∃ t1s t2s, N.of_nat addr ↦□[tag] Tf t1s t2s
  end)%I . *)
                            
    
  

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

  Lemma ewp_switch_desugared vs k tf tf' t1s t2s ts i E Ψ Φ f cont:
    is_true $ iris_lfilled_properties.constant_hholed (hholed_of_valid_hholed cont) ->
    tf' = Tf t1s ts ->
    tf = Tf (t1s ++ [T_ref (T_contref tf')]) t2s ->
    N.of_nat i ↦[tag] Tf [] ts ∗
    N.of_nat k ↦[wcont] Live tf cont ∗
      get_switch2 (Mk_tagidx i) Ψ (hholed_of_valid_hholed cont) ∗
     iProt_car (upcl (get_switch1 (Mk_tagidx i) Ψ)) vs (λ v, ▷ Φ (immV v) f) 
      ⊢ EWP [ AI_switch_desugared vs k tf (Mk_tagidx i) ] UNDER f @ E <| Ψ |> {{ v ; h , Φ v h }}.
  Proof.
    iIntros (? -> ->) "(Htag & Hk & Hcont & HΨ)".
    iApply ewp_effect_sw => //.
    iFrame.
    iExists _,_,_.
    do 3 (iSplit; first done).
    iApply (monotonic_prot with "[] HΨ").
    iIntros (w) "Hw".
    iSimpl.
    rewrite app_nil_r.
    replace (v_to_e_list w) with (of_val0 (immV w)) => //. 
    iApply ewp_value'.
    iFrame.
  Qed.

 

  Lemma ewp_suspend_desugar f ves vs i x a t1s t2s E Ψ Φ:
    i = Mk_tagident x ->
    f.(f_inst).(inst_tags) !! x = Some a ->
    length vs = length t1s ->
    ves = v_to_e_list vs ->
    N.of_nat a ↦[tag] Tf t1s t2s ∗
      ▷ EWP [AI_suspend_desugared vs (Mk_tagidx a)] UNDER f @ E <| Ψ |> {{ v ; f , Φ v f }}
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


  Lemma ewp_switch_desugar f ves vs k tf tf' i i' cont x a t1s t2s E Ψ Φ:
    i = Mk_tagident x ->
    stypes (f_inst f) i' = Some tf ->
    f.(f_inst).(inst_tags) !! x = Some a ->
    typeof_cont (continuation_of_resource cont) = Tf t1s t2s ->
    S (length vs) = length t1s ->
    ves = v_to_e_list vs ->
    N.of_nat a ↦[tag] tf' ∗
             N.of_nat k ↦[wcont] cont ∗
             ▷ ( N.of_nat a ↦[tag] tf' -∗ N.of_nat k ↦[wcont] cont -∗ EWP [AI_switch_desugared vs k tf (Mk_tagidx a)] UNDER f @ E <| Ψ |> {{ v ; f , Φ v f }})
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
  

  Lemma ewp_suspend f ves vs i x a t1s t2s E Ψ Φ:
    i = Mk_tagident x ->
    f.(f_inst).(inst_tags) !! x = Some a ->
    length vs = length t1s ->
    ves = v_to_e_list vs ->
    N.of_nat a ↦[tag] Tf t1s t2s ∗
      ▷ iProt_car (upcl (get_suspend (Mk_tagidx a) Ψ)) vs (λ v, ▷ Φ (immV v) f)  
    ⊢ EWP ves ++ [AI_basic (BI_suspend i)] UNDER f @ E <| Ψ |> {{ v ; f , Φ v f }}.
  Proof.
    iIntros (-> ?? ->) "(? & ?)".
    iApply ewp_suspend_desugar => //; eauto.
    iFrame.
    iApply ewp_suspend_desugared => //.
  Qed.

   Lemma ewp_switch f ves vs i i' k x a tf ts cont t1s t2s E Ψ Φ:
    i = Mk_tagident x ->
    tf = Tf t1s ts ->
    is_true $ iris_lfilled_properties.constant_hholed (hholed_of_valid_hholed cont) ->
    stypes (f_inst f) i' = Some (Tf (t1s ++ [T_ref (T_contref tf)]) t2s) ->
    f.(f_inst).(inst_tags) !! x = Some a ->
    length vs = length t1s ->
    ves = v_to_e_list vs ->
    N.of_nat a ↦[tag] (Tf [] ts) ∗
    N.of_nat k ↦[wcont] Live (Tf (t1s ++ [T_ref (T_contref tf)]) t2s) cont ∗
    get_switch2 (Mk_tagidx a) Ψ (hholed_of_valid_hholed cont) ∗
    ▷ iProt_car (upcl (get_switch1 (Mk_tagidx a) Ψ)) vs (λ v, ▷ Φ (immV v) f)
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
    iFrame "#". iIntros "!> ??".
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

  (*
  Lemma ewp_adequacy_trans s f es s' f' esv vs Φ Φf Ψ E:
    reduce_trans (s, f, es) (s', f', esv) ->
    to_val esv = Some vs ->
    state_interp s ∗ EWP es UNDER f @ E <| Ψ |> {{ Φ; Φf }} ⊢ |={E}=> Φ vs ∗ Φf f ∗ state_interp s'.
  Proof.
    intros Hred Hes.
    remember (s, f, es) as x.
    remember (s', f', esv) as y.
    generalize dependent s. generalize dependent f. generalize dependent es.
    generalize dependent s'. generalize dependent f'. generalize dependent esv.
    induction Hred; intros; subst.
    - iIntros "[Hs Hwp]".
      destruct f, f'.
      rewrite ewp_unfold /ewp_pre.
      erewrite val_head_stuck_reduce => //.
      edestruct eff_head_stuck_reduce.
      exact H.
      2:{ a dmit. (* weird behaviour of switch *) }
      rewrite H0.
      iMod ("Hwp" with "Hs") as "[%Hred Hes]".
      iMod ("Hes" with "[]") as "Hes".
   *)
(*
  Lemma reduce_trans_ind σ σ' (P: (store_record * frame * list administrative_instruction) -> Prop) :
    P σ ->
    reduce_trans σ σ' ->
    (forall σ σ', P σ -> reduce_tuple σ σ' -> P σ') ->
    P σ'.
  Proof.
    intros Hσ Hred HI.
    induction Hred.
    - eapply HI. exact Hσ. exact H.
    - exact Hσ.
    - apply IHHred2.
      apply IHHred1.
      exact Hσ.
  Qed. 
  
(*
  
  Lemma ewp_trans_trap s f es s' f' Φ Ψ E:
    reduce_trans (s, f, es) (s', f', [AI_trap]) ->
(*    es <> [AI_trap] -> *)
    ((∀ f, ¬ Φ trapV f) ∗  ∀ (e₂ : iris.expr) (s0 : store_record) (inst0 : instance) 
            (locs0 : list value),
            ⌜prim_step es (s, f_locs f, f_inst f) [] e₂
               (s0, locs0, inst0) []⌝ ={∅}▷=∗
            |={∅,E}=> state_interp s0 ∗
              EWP e₂
              UNDER {| f_locs := locs0; f_inst := inst0 |} @ E <|Ψ|> {{ v ; f ,
                                                                        Φ v f }})%I
      ⊢ |={∅}▷=> |={∅, E}=> False.
  Proof.
    intros Hred.
    eapply reduce_trans_ind in Hred.
    2: exact Hred.
    remember (s, f, es) as x.
    remember (s', f', [AI_trap]) as y.
    induction Hred; subst.
    - iIntros "[HΦ Hes]".
      destruct f, f'.
      iMod ("Hes" with "[]") as "Hes".
      iPureIntro. repeat split => //.
      iModIntro. iNext.
      iMod "Hes".
      iModIntro.
      iMod "Hes" as "[Hs Hewp]".
      rewrite ewp_unfold /ewp_pre.
      simpl.
      iMod "Hewp" as "Habs".
      iSpecialize ("HΦ" with "Habs").
      done.
    - inversion Heqy; subst.
      done.
    - 
      erewrite val_head_stuck_reduce; last done.
      edestruct eff_head_stuck_reduce. exact H.
      + rewrite H0.
      erewrite eff_head_stuck_reduce.
    iLöb as "IH" forall (es). *)



  
  
  Lemma reduce_empty_frame s f es s' f' es' :
    reduce s f es s' f' es' ->
    iris_resources.reducible ((es, empty_frame) : iris.expr) s ->
    f = f' /\ reduce s empty_frame es s' empty_frame es' \/
      reduce_trans (s, empty_frame, es) (s, empty_frame, [AI_trap]).
  Proof.
    intros Hred1 Hred2.
    destruct Hred2 as (l & [es'' f''] & s'' & l' & Hred2 & -> & ->).
    remember empty_frame as f0.
    generalize dependent es'.
    induction Hred2.
    inversion H.
    all: intros.
    all: subst.
    all: try by right; constructor; try econstructor; try constructor.
    all: try by destruct i.
    all: try by destruct x.
    all: try by destruct j.
    all: try (destruct i; first by clear Hred1; destruct i).
    1-40: edestruct reduce_det as [Hf [Hres | Hresabs]] ; first exact Hred1.
    all: try by econstructor.
    all: try destruct Hres as [??] ; subst.
    all: try by left; split => //; try constructor; try constructor. 
    all: try destruct Hresabs as [(? & Habs) | (? & ? & ? & Habs & Hes' & Habs' & Hσ)] => //.
    all: subst.
    all: try by destruct ref.
    all: try by rewrite /first_instr /= in Habs;
      specialize (first_instr_const _ [] H0) as He';
      rewrite seq.cats0 /first_instr in He';
      rewrite He' /= // in Habs.
    all: try by rewrite separate1 -cat_app first_instr_const in Habs;
      [done | rewrite /= const_const //].
    all: try by rewrite separate2 -cat_app first_instr_const in Habs;
      [done | repeat rewrite /= const_const //].
    all: try by rewrite first_instr_const in Habs.
    
    all: try by eapply starts_with_lfilled in H2; last (by rewrite first_instr_const);
      rewrite /first_instr /= in Habs;
      rewrite /first_instr in H2;
      rewrite H2 in Habs.
(*    all: try by eapply starts_with_lfilled in H1; last done;
      rewrite /first_instr /= in Habs;
      rewrite /first_instr in H1;
      rewrite H1 in Habs. *)
    all: try by rewrite separate1 -cat_app first_instr_const in Habs;
      [done | rewrite /= H0 //].
    
(*    all: try by right; try econstructor; try econstructor. *)
  (*  13:{ destruct i.
         2: eapply r_resume => //.
         2: apply desugar_continuation_clauses_empty_frame.
         2: done.
         by destruct i. } *)
    all: try by rewrite first_instr_const in Habs; try rewrite v_to_e_is_const_list.
    all: try by eapply starts_with_hfilled in H; last done;
      destruct H as (i' & Hi' & HLI);
      rewrite /first_instr /= in Habs;
      rewrite /first_instr in HLI;
      rewrite HLI in Habs.
    all: try by eapply starts_with_hfilled in H2; last done;
      destruct H2 as (i' & Hi' & HLI);
      rewrite /first_instr /= in Habs;
      rewrite /first_instr in HLI;
      rewrite HLI in Habs.
       all: try by eapply starts_with_hfilled in H1; last done;
      destruct H1 as (i' & Hi' & HLI);
      rewrite /first_instr /= in Habs;
      rewrite /first_instr in HLI;
      rewrite HLI in Habs.
    all: try (left; split; first done).
    all: try by econstructor.
    - eapply r_try_table => //.
      apply desugar_exception_clauses_empty_frame.
      done. 
    - subst. 
      eapply r_try_table => //. 
    - eapply r_resume => //.
      apply desugar_continuation_clauses_empty_frame.
      done. 
    - subst. 
      eapply r_resume => //.

    - destruct i'. clear Hred1; destruct i => //.
      eapply r_contbind => //. 
    - subst. 
      eapply r_contbind => //.
    - destruct f'0, f, f'.
      edestruct lfilled_reduce.
      + exact H.
      + apply reducible_empty_frame.
        eexists _,(_,_),_,_.
        repeat split => //.
      + repeat split => //.
      + destruct H1 as (es'' & (Hes & _) & Hes'').
        simpl in Hes.
        apply IHHred2 in Hes as H'=> //.
        destruct H' as [[Hf Hred]| Hred].
        * left; split => //.
          eapply r_label.
          exact Hred.
          exact H.
          exact Hes''.
        * right.
          edestruct lfilled_swap as [LI HLI].
          exact H.
          econstructor 3.
          -- eapply r_label_trans.
             exact Hred.
             exact H.
             exact HLI.
          -- eapply lfilled_trap_reduce.
             exact HLI.
      + destruct H1 as (lh0 & Hest & Hσ).
        inversion Hσ; subst.
        edestruct lfilled_trans.
        exact Hest. exact H.
        right.
        eapply lfilled_trap_reduce.
        exact H1.
    - apply reduce_det_local in Hred1.
      2: by apply val_head_stuck_reduce in Hred2.
      destruct Hred1 as (es2' & f2 & -> & -> & Hred).
      left. split => //.
      constructor. exact Hred. 
  Qed.
*)
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
  (*
    
(*
  Lemma reduce_empty_frame s f es s' f' es' s'' f'' es'':
    reduce s f es s' f' es' ->
    reduce s empty_frame es s'' f'' es'' ->
    es'' = [AI_trap] \/ s' = s'' /\ f'' = empty_frame /\ f = f' /\ es' = es''.
  Proof.
    intros Hred1 Hred2.
    remember empty_frame as f0.
    induction Hred2.
    inversion H.
    all: try by left; reflexivity.
    1-58, 60: right.
    1-58: subst.
    all: edestruct reduce_det as [Hres | Hres]; first exact Hred1.
    all: try by econstructor.
    all: try by inversion Hres; subst.
    all: try destruct Hres as [(? & Habs) | (? & ? & ? & Habs & _)] => //.
    all: try by destruct ref.
    all: try by rewrite /first_instr /= in Habs;
      specialize (first_instr_const _ [] H0) as He';
      rewrite seq.cats0 /first_instr in He';
      rewrite He' /= // in Habs.
    all: try by rewrite separate1 -cat_app first_instr_const in Habs;
      [done | rewrite /= const_const //].
    all: try by rewrite separate2 -cat_app first_instr_const in Habs;
      [done | repeat rewrite /= const_const //].
    all: try by rewrite first_instr_const in Habs.
    
    all: try by eapply starts_with_lfilled in H2; last (by rewrite first_instr_const);
      rewrite /first_instr /= in Habs;
      rewrite /first_instr in H2;
      rewrite H2 in Habs.
    all: try by rewrite separate1 -cat_app first_instr_const in Habs;
      [done | rewrite /= H0 //].
    all: try by destruct x.
    all: try by destruct i.

    all: try (destruct i; first by destruct i).
    { eapply r_call_reference => //. }
    all: try by rewrite first_instr_const in Habs ; try apply v_to_e_is_const_list.
    { eapply r_try_table => //.
      apply desugar_exception_clauses_empty_frame => //. }
    Search "hfilled_first_instr".
    Search first_instr.

(*     all: try by edestruct reduce_det as [Hres | Hres]; first exact Hred1;
      try (by econstructor);
      try (by inversion Hres; subst);
      try destruct ref;
      try by destruct Hres as [(? & Habs) | (? & ? & ? & Habs & _)]. *)
    
    all: induction Hred1.
    all: subst.


  Lemma reduce_empty_frame s es s' f' es' :
    reduce s empty_frame es s' f' es' ->
    f' = empty_frame /\ (es' = [AI_trap] \/ forall f, reduce s f es s' f es').
  Proof.
  A dmitted. 
(*    intros Hred.
    remember empty_frame as f.
    induction Hred; subst.
    inversion H; subst.
    all: try by split; first done; right; intros ?; repeat constructor.
    all: try by destruct x.
    all: try by destruct i.
    all: try by split; last by left.
    { destruct i => //.
      destruct i => //.
      split => //.
      right. intros ?.
      eapply r_call_reference => //. }
    by split; first done; right; intros ?; eapply r_invoke_native.
    by split; first done; right; intros ?; eapply r_invoke_host.
    destruct i; first (by destruct i); split; first done; right; intros ?; eapply r_try_table => //.
    
    unfold stab_addr in H.
    simpl in H. 
 *) 

  Lemma reduce_empty_frame_inv s f es s' f' es' :
    reduce s f es s' f' es' ->
    iris_resources.reducible es (s, f_locs empty_frame, f_inst empty_frame) ->
    reduce s empty_frame es s' empty_frame es' \/ reduce s empty_frame es s' empty_frame [AI_trap].
  Proof.
    intros H Hred.
    induction H.
    inversion H.
    all: try by left; constructor; econstructor.
    all: try by left; econstructor.
    
 *)

  Lemma reduce_trans_step σ σ' :
    reduce_trans σ σ' -> σ = σ' \/ exists σ'', reduce_tuple σ σ'' /\ reduce_trans σ'' σ'.
  Proof.
    intros Hred.
    induction Hred.
    - right. eexists. split; first exact H. by constructor.
    - by left.
    - destruct IHHred1 as [-> | (σ'' & Hred & Hred')].
      + exact IHHred2.
      + right. eexists. split; first exact Hred.
        by econstructor.
  Qed.

  Lemma reduce_trans_ind' σ σ' (P : (store_record * frame * list administrative_instruction) -> Prop):
    reduce_trans σ σ' ->
    P σ' ->
    (forall σ σ'', reduce_tuple σ σ'' -> (* reduce_trans σ'' σ' -> *) P σ'' -> P σ) ->
    P σ.
  Proof.
    intros Hred Hσ' Hind.
    induction Hred.
    - eapply Hind.
      exact H.
(*      by constructor. *)
      exact Hσ'.
    - exact Hσ'.
    - eapply IHHred1.
      eapply IHHred2.
      exact Hσ'.
  Qed. 
      
      

  (*
  Lemma reduce_trans_trap s f es s' f' E Ψ Φ :
    reduce_trans (s, f, es) (s', f', [AI_trap]) ->
    ((∀ f, ¬ Φ trapV f) ∗ state_interp s ∗ EWP es UNDER f @ E <| Ψ |> {{ Φ }}
       ⊢ |={E}=> False)%I.
  Proof.
    iIntros (Hred) "(HΦ & Hs & Hewp)".
    apply (reduce_trans_ind' (s, f, es) (s', f', [AI_trap]) (fun '(s, f, es) => _)).
    done.
    { rewrite ewp_unfold /ewp_pre /=.
      iMod "Hewp".
      iDestruct ("HΦ" with "Hewp") as "Habs".
      done. }
    intros [[s1 f1] es1] [[s2 f2] es2] Hred' IH.
    apply val_head_stuck_reduce in Hred' as Htv.
    apply eff_head_stuck_reduce in Hred' as Htf.
    destruct Htf as [Htf | Htf].
    2:{ a dmit.  (* might need to fix definition of swE *) }
    rewrite ewp_unfold /ewp_pre /= Htv Htf /=.
    iSpecialize ("Hewp" with "Hs").
    iMod "Hewp".
    iDestruct "Hewp" as "[%Hreducible Hewp]".
    destruct f1, f2. simpl. 
    iSpecialize ("Hewp" $! _ _ _ _  with "[]").
    iPureIntro. repeat split => //.
    iMod "Hewp".
    
    *)
    
    
  Lemma reduce_trans_nstep a b :
    reduce_trans a b -> exists n, nsteps reduce_tuple n a b.
  Proof.
    intros H; induction H => //=.
    exists 1. econstructor => //. constructor => //.
    exists 0. constructor => //.
    destruct IHclos_refl_trans1 as [n1 Hn1].
    destruct IHclos_refl_trans2 as [n2 Hn2].
    exists (n1 + n2).
    eapply nsteps_trans => //.
  Qed. 
    

  Lemma ewp_empty_frame es f E Ψ Φ :
(*    (forall ll, llfill [AI_trap] es  *)
     ¬ Φ trapV ∗ EWP es UNDER empty_frame @ E <| Ψ |> {{ v ; _ , Φ v }}
      ⊢ EWP es UNDER f @ E <| Ψ |> {{ v ; f' , Φ v ∗ ⌜ f' = f ⌝  }}.
  Proof.
    iLöb as "IH" forall (es E Ψ Φ f).
    iIntros "(Htrap & Hes)".
    Opaque upcl.
    do 2 rewrite ewp_unfold /ewp_pre /=.
    
    destruct (to_val0 es) eqn:Htv.
    { iMod "Hes" as "Hv".
      iModIntro. iSplit; done. } 
    destruct (to_eff0 es) eqn:Htf.
    { destruct e.
      all: iApply (monotonic_prot with "[-Hes] Hes").
      all: iIntros (w) "H".
      3: done.
      all: iNext.
      all: iApply "IH".
      all: iFrame. }
    iIntros (s) "Hs".
    iSpecialize ("Hes" with "Hs").
    iMod "Hes" as "[%Hred Hes]".
    iModIntro.
    iSplit.
    { iPureIntro. apply reducible_empty_frame. done. }
    iIntros ([es2 f2] s2 Hstep).
    destruct Hstep as [Hstep _].
    apply reduce_empty_frame in Hstep; last done.
    destruct Hstep as [[Hf Hstep] | Hstep].
    - iMod ("Hes" with "[]") as "Hes".
      iPureIntro.
      instantiate (2 := (_,_)).
      repeat split => //.
      iModIntro.
      iNext.
      iMod "Hes".
      iModIntro.
      iMod "Hes" as "[Hs2 Hes2]".
      iModIntro.
      iFrame.
      subst.
      iApply "IH".
      iFrame.

    - apply reduce_trans_step in Hstep as [Habs | ([[??]?] & Hred1 & Hred2)].
      { inversion Habs; subst. rewrite /to_val //= in Htv. }

      iMod ("Hes" with "[]") as "Hes".
      iPureIntro.
      instantiate (2 := (_,_)).
      repeat split => //.
      iModIntro.
      iNext.
      iMod "Hes".
      iModIntro.
      iMod "Hes" as "[Hs Hewp]".
      iModIntro.

      apply reduce_trans_nstep in Hred2 as [n Hstep].
      eapply ewp_strong_adequacy in Hstep.

      Search rtc.
      unfold reduce_trans in Hred2.
      apply rtc_nsteps_1 in Hred2.
(*      exact Hred1. *)
  A dmitted. 
(*      iModIntro.
      iNext.
      iMod "Hes".
      iModIntro.
      iMod "Hes" as "[Hs2 Hes2]".
      rewrite -> ewp_unfold at 1.
      rewrite /ewp_pre /=.
      iMod "Hes2" as "[Habs Hf']".
      iSpecialize ("Htrap" with "Habs").
      done.
  Qed.  *)

   *)



  Definition continuation_expr es : Prop :=
    (exists vs i tf, es = v_to_e_list vs ++ [ AI_ref i; AI_basic (BI_call_reference (Type_explicit tf))]) \/
      (exists vs i , es = v_to_e_list vs ++ [ AI_invoke i ] ) \/
      (exists vs n f es0, es = v_to_e_list vs ++ [AI_frame n f es0]) \/
      (exists vs, es = v_to_e_list vs ++ [AI_trap]) \/
      is_true (const_list es) \/
      (exists vs vs' k tf, es = v_to_e_list vs ++ [AI_call_host vs' k tf]) (* \/
      (exists vs a b i tf, es = v_to_e_list vs ++ [AI_ref_exn a b; AI_basic BI_throw_ref; AI_ref i; AI_basic (BI_call_reference (Type_explicit tf))])  \/
      (exists vs a b c i tf, es = v_to_e_list vs ++ [AI_throw_ref_desugared a b c; AI_ref i; AI_basic (BI_call_reference (Type_explicit tf))])  *)
      
  .


  Lemma continuation_expr_prepend vs es :
    is_true (const_list vs) -> continuation_expr es -> continuation_expr (vs ++ es).
  Proof.
    intros Hvs Hes.
    apply const_es_exists in Hvs as Hvs'.
    destruct Hvs' as [vs'' ->].
    destruct Hes as [(vs' & i & tf & ->) | [(vs' & i & ->) | [(vs' & n & f0 & es0 & ->) | [(vs' & ->) | [Hes | (vs & vs' & k & tf & ->)]]]]].  (* | [ (vs & a & b & i & tf & ->) | (vs & a & b & c & i & tf & ->)] ]]]]]]. *)
    1-4,6: rewrite catA.
    1-5: rewrite v_to_e_cat.
    by left; repeat eexists.
    by right; left; repeat eexists.
    by right; right; left; repeat eexists.
    by right; right; right; left; repeat eexists.
    by right; right; right; right; right; repeat eexists.
(*    by right; right; right; right; right; right; left; repeat eexists.
    by right; right; right; right; right; right; right;  repeat eexists.  *)
    by right; right; right; right; left; apply const_list_concat => //.
  Qed. 
    

  Lemma continuation_preservation s f es s' f' es' :
    reduce s f es s' f' es' ->
    continuation_expr es ->
    continuation_expr es'.
  Proof.
    intros Hred Hes.
    destruct Hes as [(vs & i & tf & ->) | [(vs & i & ->) | [(vs & n & f0 & es0 & ->) | [(vs & ->) | [Hes |  (vs & vs' & k & tf & ->)]]]]].  (* | [ (vs & a & b & i & tf & ->) | (vs & a & b & c & i & tf & ->)] ]]]]]].  *)
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
      (* apply const_es_exists in H6 as [? Heq]. *)
      
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
(*      2: by split; try eapply r_local.  *)
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
(*     apply const_es_exists in Hvs as [? ->].
     left. repeat eexists. *)
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


   
(*  Lemma reducible_empty_frame ts dccs es s f:
    continuation_expr es ->
    reducible (([AI_prompt ts dccs es], empty_frame) : iris.expr) s ->
    reducible (([AI_prompt ts dccs es], f): iris.expr) s.
  Proof.
    intros Hes Hred.
    destruct Hred as (os & [es' f'] & σ & efs & Hred & -> & ->).
    remember [_] as es0.
    remember empty_frame as f0.
    induction Hred.
    inversion H.
    all: subst.
    all: try done.
    all: try by do 2 (destruct vs => //).
    all: try by do 2 (destruct vcs => //).
    all: try by eexists [], (_,_), _, []; split; try econstructor; try econstructor.
    move/lfilledP in H. inversion H; subst.
    all: try by do 2 (destruct vs => //).
    all: try by do 2 (destruct bef => //).
    - destruct vs.
      + destruct es0; first by empty_list_no_reduce.
        inversion H1; subst.
        destruct es0, es'0 => //.
        move/lfilledP in H0; inversion H0; subst.
        apply IHHred => //.
      + inversion H1; subst.
        done.
    - destruct bef; last by (do 2 destruct bef => //).
      inversion H1; subst.
      eexists [], (_,_), _, []. split; last done.
      eapply r_label.
      exact Hred.

    
    all: try by destruct x.
    all: try by destruct i.
    - destruct (stab_addr s f (Wasm_int.nat_of_uint i32m c)) eqn:Hsol.
      destruct (nth_error (s_funcs s) n) eqn:Hf.
      destruct (stypes (f_inst f) i == Some (cl_type f0)) eqn:Htypes.
      move/eqP in Htypes.
      all: eexists [], (_,_), _, [].
      all: split; last done.
      eapply r_call_indirect_success; eauto.
      eapply r_call_indirect_failure1; eauto.
      intros Habs; rewrite Habs in Htypes. by rewrite eq_refl in Htypes.
      a dmit.
      eapply r_call_indirect_failure2; eauto.
    - eexists [], (_,_), _, []. split; last done.
      eapply r_try_table; eauto.
      destruct cs => //=. 
      eapply r_call_reference; eauto.
    - destruct i; first
      
    all: try by econstructor.
    all: try by econstructor; econstructor.
    *)

   
  
   Lemma ewp_empty_frame ts dccs es f E Ψ Φ :
    (*     ¬ Φ trapV ∗  *)
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
      2: iDestruct "Hes" as (cont t1s t2s tf' ts0) "(? & Htag & Hcont & -> & -> & HΨ & Hes)"; iFrame.
      2: iExists _,_,_; iSplit; first done.
      2: iSplit; first done.
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
(*    destruct Hred as (? & ? & ? & ? & ?).
    destruct x0.
    destruct H as (Hred0 & -> & ->). *)
    
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


(*
  Lemma ewp_empty_frame es f E Ψ Φ :
    (*     ¬ Φ trapV ∗  *)
    continuation_expr es ->
    EWP es UNDER empty_frame @ E <| Ψ |> {{ v ; _ , Φ v }}
      ⊢ EWP es UNDER f @ E <| Ψ |> {{ v ; f' , Φ v ∗ ⌜ f' = f ⌝  }}.
  Proof.
    iLöb as "IH" forall (es E Ψ Φ f).
    iIntros (Hes) "Hes".
    Opaque upcl.
    do 2 rewrite ewp_unfold /ewp_pre /=.
    
    destruct (to_val0 es) eqn:Htv.
    { iMod "Hes" as "Hv".
      iModIntro. iSplit; done. } 
    destruct (to_eff0 es) eqn:Htf.
    { eapply continuation_expr_to_eff in Hes as (vs & n & f' & es' & ->).
      2: exact Htf.
      destruct e.
      all: iApply (monotonic_prot with "[-Hes] Hes").
      all: iIntros (w) "H".
      3: done.
      all: iNext.
      all: iApply "IH".
      all: iFrame.
      all: rewrite /to_eff0 /= map_app merge_app in Htf.
      all: specialize (v_to_e_is_const_list vs) as Hvs.
      all: apply const_list_to_val in Hvs as (? & Hvs & ?).
      all: rewrite /to_val0 in Hvs.
      all: destruct (merge_values _) => //.
      all: inversion Hvs; subst.
      all: simpl in Htf.
      all: destruct (merge_values (List.map _ es')) => //.
      all: try by destruct v.
      all: destruct e => //.
      all: simpl in Htf.
      all: inversion Htf; subst.
      all: iPureIntro; right; right; left; eauto.
    }

    iIntros (s) "Hs".
    iSpecialize ("Hes" with "Hs").
    iMod "Hes" as "[%Hred Hes]".
    iModIntro.
(*    destruct Hred as (? & ? & ? & ? & ?).
    destruct x0.
    destruct H as (Hred0 & -> & ->). *)
    
    iSplit.
    { iPureIntro. apply reducible_empty_frame. done. }
    iIntros ([es2 f2] s2 Hstep).
    destruct Hstep as [Hstep _].
    apply continuation_ignores_frame in Hstep as [Hstep ->]; last done.
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
    subst.
    iApply "IH".
    2: iFrame.
    iPureIntro.
    eapply continuation_preservation.
    exact Hstep. exact Hes.
  Qed. 

  *)
(*  

  Definition continuation_expr es : Prop :=
    (exists vs hh, const_list vs /\ hfilled No_var (hholed_of_resource hh) vs es) \/
      (exists vs a, const_list vs /\ es = vs ++ [AI_invoke a]).

  Lemma continuation_preservation s f es s' f' es' :
    reduce s f es s' f' es' ->
    continuation_expr es ->
    continuation_expr es' \/
      exists vs, const_list vs /\ es' = vs ++ [AI_trap].
  Proof.
    intros Hred Hes.
    destruct Hes as [(vs & hh & Hvs & Hfill) | (vs & a & Hvs & ->)].
    - destruct hh.
      + assert (is_true (hfilled No_var (hholed_of_resource (Initial i f0)) vs es));
          first by destruct (hfilled No_var (hholed_of_resource (Initial i f0)) vs es).
        unfold hfilled, hfill in H; simpl in H. apply b2p in H.
        rewrite separate1 in H.
        rewrite -cat_app seq.catA in H.
        remember (S (length es)) as m.
        assert (length es < m); first lia.
        clear Heqm.
        generalize dependent es.
        induction m; first lia.
        intros. 
        induction Hred.
        inversion H1.
        all: remember H as Hnew; clear HeqHnew H.
        all: subst.
        all: try by right; exists []; split.
        all: try by rewrite separate1 in Hnew; apply concat_cancel_last in Hnew as [??].
        all: try by rewrite separate2 in Hnew; apply concat_cancel_last in Hnew as [??].
        all: try by rewrite separate3 in Hnew; apply concat_cancel_last in Hnew as [??].
        all: try by rewrite - (app_nil_l [_]) in Hnew; apply concat_cancel_last in Hnew as [??].
        left; right. exists [], x. split => //.
        all: try by rewrite separate1 -cat_app seq.catA in Hnew; apply concat_cancel_last in Hnew as [??].
        edestruct lfilled_Ind_Equivalent as [Heq _].
        apply Heq in H1. inversion H1; subst.
        2-4: apply first_values in H as (? & ? & ?) => //; apply const_list_concat => //; by destruct (const_list _).
        destruct vs0.
        { destruct es'0.
          { rewrite seq.cats0 /= in H.
            rewrite /lfilled /lfill /= app_nil_r in H2.
            apply b2p in H2.
            subst.
            apply IHHred => //. }
          destruct (separate_last (a :: es'0)) as [[??] | ] eqn:Habs.
          2:{ apply separate_last_None in Habs => //. }
          apply separate_last_spec in Habs.
          rewrite Habs in H.
          simpl in H.
          rewrite -cat_app seq.catA in H. 
          apply concat_cancel_last in H as [??].
          exfalso; values_no_reduce.
          assert (is_true (const_list (seq.cat es l))).
          rewrite H. apply const_list_concat => //. by destruct (const_list _).
          apply const_list_split in H4 as [??]. done. }
        edestruct IHm as [
        
          apply const_list_split.
            apply IHm. 
        move/lfilledP in H1; inversion H1; subst.
        all: try by apply concat_cancel_last in Hnew as [??].
        done.

        all: try by exfalso; destruct vs. 
        
        
        edestruct reduce_det as (? & [[? ?] | [[??] | (? & ? & ? & ? & ? & ? & ?)]]).
        exact Hred.
        
*)

(*
   Lemma ewp_prompt ts dccs es E Ψ Ψ' Φ Φ' f:
     agree_on_uncaptured dccs Ψ Ψ' ->
     continuation_expr es ->
    ((∀ f, ¬ Φ trapV f) ∗ ¬ Φ' trapV ∗ EWP es UNDER empty_frame @ E <| Ψ |> {{ Φ }} ∗
      (∀ w, Φ w empty_frame -∗ EWP [AI_prompt ts dccs (of_val0 w)] UNDER empty_frame @ E <| Ψ' |> {{ v ; _ , Φ' v }}) ∗
      [∗ list] dcc ∈ dccs, clause_triple E Ψ Φ dcc ts Ψ' (λ v _, Φ' v) )%I
      ⊢ EWP [AI_prompt ts dccs es] UNDER f @ E <| Ψ' |> {{ v; f', Φ' v ∗ ⌜ f' = f ⌝ }}.
   Proof.
     iLöb as "IH" forall (ts dccs es E Ψ Ψ' Φ Φ').
    iIntros (HΨ Hes) "(Hntrap & Hntrap' & Hes & HΦ & Hclauses)".
    destruct (to_val0 es) eqn:Htv.
    { iDestruct ewp_value_fupd as "[H _]";
        last iDestruct ("H" with "Hes") as "Hes".
      apply of_to_val0 in Htv. symmetry. exact Htv.
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
(*          iFrame. *)
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
(*          iDestruct (big_sepL_lookup with "Hclres") as "Hclres".
          exact Hk. *)
          iDestruct "Hclause" as (t1s t2s) "[#Hclres Hclause]".
          iDestruct "Hσ" as "(Hfuncs & Hconts & Htags & Hrest)".
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
            iApply ("Hclause" with "Hcont").
(*            iDestruct ("Hes" with "[$]") as "Hes". *)
(*            iDestruct "Hes" as (Ξ) "[HΞ Hes]".
            iExists Ξ. iFrame.
            iIntros (w) "HΞ".
            iIntros (LI HLI). 
            iDestruct ("Hes" with "HΞ") as "Hes". *)
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

(*            eapply hfilled_inj in Hfilled.
            2:{ instantiate (1 := LI).
                instantiate (1 := No_var).
                destruct (hfilled No_var _ _) => //. }
            rewrite Hfilled. *)
            iNext.
            rewrite cats0. iExact "Hw".
          * apply susE_first_instr in Htf0 as [k' Htf0].
            
            rewrite first_instr_const in Habs; last by apply v_to_e_is_const_list.
            unfold first_instr in Habs.
            unfold first_instr in Htf0.
            simpl in Habs.
            simpl in Htf0.
(*            repeat rewrite map_app in Habs.
            specialize (v_to_e_is_const_list vs) as Hvs.
            specialize (first_instr_const (v_to_e_list vs) [] Hvs) as Hvs'.
            rewrite cats0 /first_instr /= in Hvs'.
            rewrite Hvs' in Habs. *)
            
            destruct (find_first_some (List.map _ (_ ++ [_]))) => //.
            destruct p.
            exfalso.
            destruct Habs as [(? & Habs) | (? & ? & ? & Habs & _)] => //.
            all: inversion Htf0; inversion Habs; subst => //. 
      - iDestruct (ewp_effect_sw with "Hes") as "Hes" ; eauto.
        remember (Logic.eq_refl (to_eff0 [AI_prompt ts dccs es])) as Htf'; clear HeqHtf'.
        unfold to_eff0 in Htf' at 2.
        simpl in Htf'.
        remember Htf as Htf0; clear HeqHtf0.
        unfold to_eff0 in Htf.
        destruct (merge_values _) => //.
        inversion Htf; subst.
        destruct (swelts_of_continuation_clauses dccs i) eqn:Helts.
        + simpl in Htf'.
          iApply ewp_effect_sw; eauto.
          iFrame.
          remember HΨ as HΨ'; clear HeqHΨ'.
          destruct HΨ as (_ & HΨ & _).
          rewrite -HΨ.
          2: by eapply swelts_firstx.
          iApply (monotonic_prot with "[-Hes] Hes").
          iIntros (w) "Hw".
          iNext. iSimpl.
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
          destruct (swelts_of_continuation_clauses _ i0) eqn:Helts' => //.
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
          destruct i.
          apply firstx_switch_lookup in Hfirst as Hfirst'.
          destruct Hfirst' as [k' Hk].
          iDestruct (big_sepL_lookup with "Hclauses") as "Hclause".
          exact Hk.
(*          iDestruct (big_sepL_lookup with "Hclres") as "Hclres".
          exact Hk. *)
          done.
(*          iDestruct "Hclause" as (t1s t2s) "[#Hclres Hclause]".
          iDestruct "Hσ" as "(Hfuncs & Hconts & Htags & Hrest)".
          iDestruct (gen_heap_valid with "Htags Hclres") as %Htag.
          rewrite gmap_of_list_lookup in Htag.
          rewrite -nth_error_lookup in Htag.
          eassert (reduce σ (Build_frame _ _) [AI_prompt ts dccs es] _ _ _).
          { eapply r_suspend.
            done.
            done.
            rewrite Nat2N.id.
            exact Hfirst.
            apply of_to_eff in Htf0.
            unfold of_eff in Htf0.
            subst es.
            rewrite Nat2N.id.
            apply susfill_to_hfilled. }
          iSplit.
          { iPureIntro.
            unfold reducible.
            eexists _, _, (_,_,_), _.
            repeat split => //. } 
            
          iIntros (es2 σ2 ?? Hstep).
          destruct Hstep as (Hstep & _ & _).
          
          edestruct reduce_det. 
          exact Hstep. exact H.
          inversion H0; subst.
          destruct H1 as [(-> & ->) | Habs].
          * inversion H0; subst.
            iFrame.

            iModIntro.
            iMod "Hclose".
          
            iMod (gen_heap_alloc with "Hconts") as "(Hconts & Hcont & Htok)";
              last first.
            iModIntro.

            iFrame.
            iSplitL "Hconts".
            { unfold new_cont. simpl.
              instantiate (2 := N.of_nat (length (s_conts σ))).
              rewrite -gmap_of_list_append.
              iExact "Hconts". }
            2:{ rewrite gmap_of_list_lookup.
                rewrite Nat2N.id.
                apply lookup_ge_None_2.
                lia. }
            iApply ("Hclause" with "Hcont").
(*            iDestruct ("Hes" with "[$]") as "Hes". *)
(*            iDestruct "Hes" as (Ξ) "[HΞ Hes]".
            iExists Ξ. iFrame.
            iIntros (w) "HΞ".
            iIntros (LI HLI). 
            iDestruct ("Hes" with "HΞ") as "Hes". *)
            iApply (monotonic_prot with "[-Hes] Hes").
            iIntros (w) "Hw".
            specialize (susfill_to_hfilled (Mk_tagidx n) sh (of_val w)) as Hfilled.
            iExists _.
            iSplit; first iPureIntro.
            apply hfilled_forget_avoiding in Hfilled.
            instantiate (1 := susfill (Mk_tagidx n) sh (of_val w)).
            by destruct (hfilled _ _ _ _) => //. 
(*            eapply hfilled_inj in Hfilled.
            2:{ instantiate (1 := LI).
                instantiate (1 := No_var).
                destruct (hfilled No_var _ _) => //. }
            rewrite Hfilled. *)
            iNext.
            iExact "Hw".
          * apply susE_first_instr in Htf0 as [k' Htf0].
            unfold first_instr in Habs.
            unfold first_instr in Htf0.
            simpl in Habs.
            rewrite Htf0 in Habs.
            exfalso.
            destruct Habs as [(? & Habs) | (? & ? & ? & Habs & _)] => //. *)
      - iDestruct (ewp_effect_thr with "Hes") as "Hes" ; eauto. 
(*        iDestruct "Hes" as (f) "[Hf Hes]".  *)
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
        (* iIntros (?) "Hf". 
        iDestruct ("Hes" with "Hf") as "Hes". *)
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
      apply reducible_empty_frame.
      destruct Hred as (obs & [es' f'] & σ' & efs & Hred).

      destruct Hred as (Hred & -> & ->).
      eexists _, (_, _), _, _.
      repeat split => //.
      eapply r_label.
      exact Hred.
      instantiate (1 := LH_prompt [] ts dccs (LH_base [] []) []).
      instantiate (1 := 0).
      all: unfold lfilled, lfill => //=.
      rewrite app_nil_r //. }
    iIntros ([es2 f2] σ2 Hstep).
    eapply lfilled_prim_step_split_reduce_r in Hstep as Hstep0.
    2:{ instantiate (1 := []).
        instantiate (1 := es).
        instantiate (1 := LH_prompt [] ts dccs (LH_base [] []) []).
        instantiate (1 := 0).
        unfold lfilled, lfill => //=.
        repeat rewrite app_nil_r.
        rewrite eqtype.eq_refl => //. }
    2: apply reducible_empty_frame; exact Hred.

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
(*      iIntros "Hf".
      iDestruct ("He'" with "Hf") as "He'". *)
      
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
      (* iDestruct ("Hes" with "Hf") as "Hes". *)
      iDestruct ewp_value_fupd as "[H _]".
      instantiate (1 := trapV) => //.
      
      iMod ("H" with "Hes") as "Habs".
      iDestruct ("Hntrap" with "Habs") as "Habs" => //.
  Qed. 
 *)

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
      (* clause_resources dccs ∗ *)
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
(*          iFrame. *)
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
(*          iDestruct (big_sepL_lookup with "Hclres") as "Hclres".
          exact Hk. *)
          iDestruct "Hclause" as (t1s t2s) "[Hclres Hclause]".
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
(*            iDestruct ("Hes" with "[$]") as "Hes". *)
(*            iDestruct "Hes" as (Ξ) "[HΞ Hes]".
            iExists Ξ. iFrame.
            iIntros (w) "HΞ".
            iIntros (LI HLI). 
            iDestruct ("Hes" with "HΞ") as "Hes". *)
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

(*            eapply hfilled_inj in Hfilled.
            2:{ instantiate (1 := LI).
                instantiate (1 := No_var).
                destruct (hfilled No_var _ _) => //. }
            rewrite Hfilled. *)
            iNext.
            rewrite cats0. iExact "Hw".
          * apply susE_first_instr in Htf0 as [k' Htf0].
            
            rewrite first_instr_const in Habs; last by apply v_to_e_is_const_list.
            unfold first_instr in Habs.
            unfold first_instr in Htf0.
            simpl in Habs.
            simpl in Htf0.
(*            repeat rewrite map_app in Habs.
            specialize (v_to_e_is_const_list vs) as Hvs.
            specialize (first_instr_const (v_to_e_list vs) [] Hvs) as Hvs'.
            rewrite cats0 /first_instr /= in Hvs'.
            rewrite Hvs' in Habs. *)
            
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
          iDestruct "Hes" as (cont t1s t2s tf' ts0) "(? & Htag & Hk & -> & -> & Hcont & Hes)".
          iFrame. iExists _,_,_. iSplit; first done.
          iSplit; first done.
          unfold get_switch2, get_switch1.
          rewrite -HΨ.
          iFrame.
          2: by eapply swelts_firstx.
          
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
          iDestruct "Hclause" as "[Hclres #Hclause]".
          iDestruct "Hσ" as "(Hfuncs & Hconts & Hexns & Htags & Hrest)".
          iDestruct (gen_heap_valid with "Htags Hclres") as %Htag.
          rewrite gmap_of_list_lookup in Htag.
          rewrite -nth_error_lookup in Htag.
          iDestruct "Hes" as (cont t1s' t2s' tf' ts0) "(%Hconst & Htag & Hk & -> & -> & Hcont & Hes)".
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
            iDestruct ("Hclause" with "Hcont [] Hclres Hk' [Hes]") as (?) "(%Hfill & H)".
            { done. } 
            { iApply (monotonic_prot with "[] Hes").
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
(*        iDestruct "Hes" as (f) "[Hf Hes]".  *)
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
        (* iIntros (?) "Hf". 
        iDestruct ("Hes" with "Hf") as "Hes". *)
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
(*      iIntros "Hf".
      iDestruct ("He'" with "Hf") as "He'". *)
      
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
      (* iDestruct ("Hes" with "Hf") as "Hes". *)
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
       (* clause_resources dccs ∗ *)
       ▷ EWP LI UNDER empty_frame @ E <| Ψ |> {{ Φ }} ∗
       ▷ (∀ w, Φ w empty_frame -∗ EWP [AI_prompt t2s dccs (of_val0 w)] UNDER empty_frame @ E <| Ψ' |> {{ v; _ , Φ' v }}) ∗
       ▷ [∗ list] dcc ∈ dccs, clause_triple E Ψ Φ dcc t2s Ψ' (λ v _, Φ' v)
        )%I
      ⊢ EWP vs ++ [AI_ref_cont addr ; AI_basic $ BI_resume i ccs] UNDER f @ E <| Ψ' |> {{ v ; f', Φ' v ∗ ⌜ f' = f ⌝ }}.
  Proof.
    iIntros (Hvs Hi Hlen Hclauses HΨ HLI) "(Hcont & Hntrap & Hntrap' & HΦ & Hnext & Hclauses)".
(*    iApply (ewp_wand with "[-]"). *)
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
          (* rewrite -cat_app in Habs. *)
          by rewrite first_instr_const in Habs.
          destruct H0 as (? & ? & ? & Habs & _).
          rewrite (* -cat_app *) first_instr_const in Habs => //.
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
       (* clause_resources dccs ∗ *)
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
          (* rewrite -cat_app in Habs. *)
          by rewrite first_instr_const in Habs; try apply v_to_e_is_const_list.
          destruct H0 as (? & ? & ? & Habs & _).
          rewrite (* -cat_app *) first_instr_const in Habs => //.
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

