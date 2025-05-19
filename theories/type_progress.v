(** Proof of progress **)
From Coq Require Import Program.Equality NArith.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.

From Wasm Require Export operations typing datatypes_properties typing opsem properties type_preservation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Definition terminal_form (es: seq administrative_instruction) :=
  const_list es \/ es = [::AI_trap] \/
    (exists hh vs a i,
        hfilled (Var_handler i) hh [:: AI_throw_ref_desugared vs a i] es) \/
    (exists vs x hh,
        hfilled (Var_prompt_suspend x) hh [:: AI_suspend_desugared vs x] es) \/
    (exists vs k tf x hh,
        hfilled (Var_prompt_switch x) hh [:: AI_switch_desugared vs k tf x] es)
.


Lemma reduce_trap_left: forall vs,
    const_list vs ->
    vs <> [::] ->
    reduce_simple (vs ++ [::AI_trap]) [::AI_trap].
Proof.
  move => vs HConst H.
  destruct vs => //=; eapply rs_trap; try by destruct vs => //=.
  assert (LF : lfilledInd 0 (LH_base (a::vs) [::]) [::AI_trap] (a::vs++[::AI_trap])).
  { by apply LfilledBase. }
  apply/lfilledP.
  by apply LF.
Qed.

Lemma v_e_trap: forall vs es,
    const_list vs ->
    vs ++ es = [::AI_trap] ->
    vs = [::] /\ es = [::AI_trap].
Proof.
  move => vs es HConst H.
  destruct vs => //=.
  destruct vs => //=. destruct es => //=.
  simpl in H. inversion H. by subst.
Qed.

Lemma cat_split: forall {X:Type} (l l1 l2: seq X),
    l = l1 ++ l2 ->
    l1 = take (size l1) l /\
    l2 = drop (size l1) l.
Proof.
  move => X l l1.
  generalize dependent l.
  induction l1 => //=; move => l l2 HCat; subst => //=.
  - split. by rewrite take0. by rewrite drop0.
  - edestruct IHl1.
    instantiate (1 := l2). eauto.
    split => //.
    by f_equal.
Qed.

Lemma reduce_composition: forall s cs f es es0 s' f' es',
    const_list cs ->
    reduce s f es s' f' es' ->
    reduce s f (cs ++ es ++ es0) s' f' (cs ++ es' ++ es0).
Proof.
  move => s cs f es es0 s' f' es' HConst HReduce.
  eapply r_label; eauto; apply/lfilledP.
  - instantiate (1 := (LH_base cs es0)). instantiate (1 := 0).
    by apply LfilledBase.
  - by apply LfilledBase.
Qed.

Lemma reduce_composition_right: forall s f es es0 s' f' es',
    reduce s f es s' f' es' ->
    reduce s f (es ++ es0) s' f' (es' ++ es0).
Proof.
  move => s f es es0 s' f' es' HReduce.
  eapply reduce_composition in HReduce.
  instantiate (1 := es0) in HReduce.
  instantiate (1 := [::]) in HReduce.
  by simpl in HReduce.
  by [].
Qed.

Lemma reduce_composition_left: forall s cs f es s' f' es',
    const_list cs ->
    reduce s f es s' f' es' ->
    reduce s f (cs ++ es) s' f' (cs ++ es').
Proof.
  move => s f es es0 s' f' es' HConst HReduce.
  eapply reduce_composition in HReduce; eauto.
  instantiate (1 := [::]) in HReduce.
  by repeat rewrite cats0 in HReduce.
Qed.

Lemma lfilled0_empty: forall es,
    lfilled 0 (LH_base [::] [::]) es es.
Proof.
  move => es.
  apply/lfilledP.
  assert (LF : lfilledInd 0 (LH_base [::] [::]) es ([::] ++ es ++ [::])); first by apply LfilledBase.
  by rewrite cats0 in LF.
Qed.

Lemma label_lfilled1: forall n es es0,
    lfilled 1 (LH_rec [::] n es0 (LH_base [::] [::]) [::]) es [::AI_label n es0 es].
Proof.
  move => n es es0.
  apply/lfilledP.
  replace [:: AI_label n es0 es] with ([::] ++ [::AI_label n es0 es] ++ [::]) => //.
  apply LfilledRec => //.
  assert (LF : lfilledInd 0 (LH_base [::] [::]) es ([::] ++ es ++ [::])); first by apply LfilledBase.
  simpl in LF. by rewrite cats0 in LF.
Qed.


Lemma const_prefix vs e es vs' es':
  const_list vs ->
  const_list vs' ->
  (is_const e -> False) ->
  vs ++ e :: es = vs' ++ es' ->
  exists vsf, vs = vs' ++ vsf.
Proof.
  generalize dependent vs.
  induction vs'.
  - intros. exists vs. done.
  - intros vs Hvs Hvs' He Hl.
    simpl in Hvs'. remove_bools_options.
    destruct vs.
    { inversion Hl; subst. exfalso; apply He. done. }
    simpl in Hvs. remove_bools_options.
    simpl in Hl.
    inversion Hl; subst a0.
    destruct (IHvs' vs) as (vsf & ->) => //.
    exists vsf. done.
Qed. 
    

(*
Lemma terminal_form_v_e: forall vs es s i,
    const_list vs ->
    terminal_form s i (vs ++ es) ->
    terminal_form s i es.
Proof.
  move => vs es s i HConst HTerm.
  unfold terminal_form in HTerm.
  repeat destruct HTerm as [? | HTerm].
  - unfold terminal_form. left.
    apply const_list_split in H. by destruct H.
  - destruct vs => //=.
    + simpl in H. subst. unfold terminal_form. by right; left.
    + destruct vs => //=. destruct es => //=.
      simpl in H. inversion H. by subst.
  - destruct H as (hh & a & exn & Hexn & Hfill).
    right; right; left.
    destruct hh.
    * move/hfilledP in Hfill.
      inversion Hfill; subst.
      rewrite separate1 in H4.
      rewrite - cat_app in H4. rewrite catA in H4.
      apply const_prefix in H4 as (vsf & Hl) => //.





      exists (HH_base (vs ++ l) l0), a, exn.
      split => //.
      apply/hfilledP.
      move/hfilledP in Hfill.
      inversion Hfill; subst.
      apply HfilledBase.

Qed. *)

Lemma terminal_trap : terminal_form [::AI_trap].
Proof.
  unfold terminal_form. by right; left.
Qed.

Lemma e_b_inverse: forall es,
    es_is_basic es ->
    to_e_list (to_b_list es) = es.
Proof.
  move => es HAI_basic.
  by erewrite e_b_elim; eauto.
Qed.

Lemma typeof_append: forall ts s t vs,
    map (typeof s) vs = ts ++ [::t] ->
    exists v,
      vs = take (size ts) vs ++ [::v] /\
      map (typeof s) (take (size ts) vs) = ts /\
      typeof s v = t.
Proof.
  move => ts s t vs HMapType.
  apply cat_split in HMapType.
  destruct HMapType.
  rewrite -map_take in H.
  rewrite -map_drop in H0.
  destruct (drop (size ts) vs) eqn:HDrop => //=.
  destruct l => //=.
  inversion H0. subst.
  exists v.
  split => //.
  rewrite -HDrop. by rewrite cat_take_drop.
Qed.

Global Hint Constructors reduce_simple : core.
Global Hint Constructors opsem.reduce_simple : core.

Ltac invert_typeof_vcs :=
  lazymatch goal with
  | H: map (typeof _) ?vcs = [::_; _; _] |- _ =>
    destruct vcs => //=; destruct vcs => //=; destruct vcs => //=; destruct vcs => //=;
    simpl in H; inversion H; subst; clear H
  | H: map (typeof _) ?vcs = [::_; _] |- _ =>
    destruct vcs => //=; destruct vcs => //=; destruct vcs => //=;
    simpl in H; inversion H; subst; clear H
  | H: map (typeof _) ?vcs = [::_] |- _ =>
    destruct vcs => //=; destruct vcs => //=;
    simpl in H; inversion H; subst; clear H
  | H: map (typeof _) ?vcs = [::] |- _ =>
    destruct vcs => //=;
    simpl in H; inversion H; subst; clear H
  end.

Lemma nth_error_map: forall {X Y:Type} (l: seq X) n f {fx: Y},
    List.nth_error (map f l) n = Some fx ->
    exists x, List.nth_error l n = Some x /\
    f x = fx.
Proof.
  move => X Y l n.
  generalize dependent l.
  induction n => //; move => l f fx HN.
  - destruct l => //=.
    simpl in HN. inversion HN. subst. by eauto.
  - destruct l => //=.
    simpl in HN. by apply IHn.
Qed.

Lemma map_nth_error: forall {X Y:Type} l n (f: X -> Y) x,
    List.nth_error l n = Some x ->
    List.nth_error (map f l) n = Some (f x).
Proof.
  intros.
  generalize dependent l.
  induction n => //; intros l Hx.
  - destruct l => //=. inversion Hx; subst. done.
  - destruct l => //=. simpl in Hx.
    by apply IHn.
Qed. 

Lemma func_context_store: forall s i C j x,
    inst_typing s i C ->
    j < length (tc_func_t C) ->
    List.nth_error (tc_func_t C) j = Some x ->
    exists a, List.nth_error i.(inst_funcs) j = Some a.
Proof.
  move => s i C j x HIT HLength HN.
  unfold sfunc. unfold operations.sfunc. unfold option_bind.
  unfold sfunc_ind.
  unfold inst_typing, typing.inst_typing in HIT.
  destruct i => //=. destruct C => //=.
  destruct tc_local => //=. destruct tc_label => //=. destruct tc_return => //=.
  remove_bools_options.
  remember H4 as H4'. clear HeqH4'.
  apply all2_size in H4.
  repeat rewrite -length_is_size in H4.
  simpl in HLength.
  rewrite -H4 in HLength.
  move/ltP in HLength.
  apply List.nth_error_Some in HLength.
  destruct (List.nth_error inst_funcs j) eqn:HN1 => //=.
  by eexists.
Qed.

Lemma glob_context_store: forall s i C j g,
    inst_typing s i C ->
    j < length (tc_global C) ->
    List.nth_error (tc_global C) j = Some g ->
    sglob s i j <> None.
Proof.
  move => s i C j g HIT HLength HN.
  unfold sglob. unfold operations.sglob. unfold option_bind.
  unfold sglob_ind.
  unfold inst_typing, typing.inst_typing in HIT.
  destruct i => //=. destruct C => //=.
  destruct tc_local => //=. destruct tc_label => //=. destruct tc_return => //=.
  remove_bools_options.
  remember H3 as H4'. clear HeqH4'.
  apply all2_size in H3.
  repeat rewrite -length_is_size in H3.
  simpl in HLength.
  rewrite -H3 in HLength.
  move/ltP in HLength.
  apply List.nth_error_Some in HLength.
  destruct (List.nth_error inst_globs j) eqn:HN1 => //=.
  apply List.nth_error_Some.
  unfold globals_agree in H4'.
  eapply all2_projection in H4'; eauto.
  remove_bools_options.
  by move/ltP in H5.
Qed.

Lemma mem_context_store: forall s i C,
    inst_typing s i C ->
    tc_memory C <> [::] ->
    exists n, smem_ind s i = Some n /\
              List.nth_error (s_mems s) n <> None.
Proof.
  move => s i C HIT HMemory.
  unfold inst_typing, typing.inst_typing in HIT.
  destruct i => //=. destruct C => //=.
  destruct tc_local => //=. destruct tc_label => //=. destruct tc_return => //=.
  remove_bools_options.
  simpl in HMemory. unfold smem_ind. simpl.
  remember H1 as H4'. clear HeqH4'.
  apply all2_size in H1.
  destruct inst_memory => //=; first by destruct tc_memory.
  exists m. split => //.
  destruct tc_memory => //.
  simpl in H4'.
  unfold memi_agree in H4'.
  by remove_bools_options.
Qed.

Lemma store_typing_stabaddr: forall s f C c a,
  stab_addr s f c = Some a ->
  inst_typing s f.(f_inst) C ->
  store_typing s ->
  exists cl, List.nth_error s.(s_funcs) a = Some cl.
Proof.
  move => s f C c a HStab HIT HST.
  unfold inst_typing, typing.inst_typing in HIT.
  unfold store_typing, tab_agree, tabcl_agree in HST.
  unfold stab_addr in HStab.
  destruct s => //=. destruct f => //=. destruct f_inst. destruct f_inst. destruct C => //=.
  destruct tc_local => //=. destruct tc_label => //=. destruct tc_return => //=.
  remove_bools_options.
  simpl in *. destruct inst_tab0 => //=.
  unfold stab_index in HStab. unfold option_bind in HStab.
  remove_bools_options.
  subst. simpl in *.
  destruct tc_table => //=.
  remove_bools_options.
  destruct HST.
  destruct H6.
  rewrite -> List.Forall_forall in H6.
  assert (HIN1: List.In t0 s_tables).
  { by apply List.nth_error_In in Hoption0. }
  apply H6 in HIN1. destruct HIN1 as [HIN1 _].
  rewrite -> List.Forall_forall in HIN1.
  assert (HIN2: List.In (Some a) (table_data t0)).
  { by apply List.nth_error_In in Hoption. }
  apply HIN1 in HIN2.
  move/ltP in HIN2.
  apply List.nth_error_Some in HIN2.
  destruct (List.nth_error s_funcs a) eqn:HNth => //.
  by eexists.
Qed.

(*
  Except [::BI_br i] or [::Return], and the new [::Throw_ref_desugared] and [::Suspend_desugared] and [::Switch_desugared], every other basic instruction can be
    prepended by several consts to be reduceable to something else.

  Although we only actually need bes to be not Return or BI_br, we have to state an
    entire lfilled proposition as a condition due to composition.
 *)

Definition not_lf_br (es: seq administrative_instruction) (n: nat) :=
  forall k lh, ~ lfilled n lh [::AI_basic (BI_br k)] es.

Definition not_lf_return (es: seq administrative_instruction) (n: nat) :=
  forall lh, ~ lfilled n lh [::AI_basic BI_return] es.

Definition not_lf_throw_ref (es: seq administrative_instruction) := 
  forall bef vs a i aft, ~ (const_list bef /\ bef ++ [::AI_throw_ref_desugared vs a i] ++ aft = es).

(*
Definition not_lf_suspend es := (* n :=
  forall i tf lh, ~ lfilled n lh [::AI_basic (BI_suspend (Tag_explicit i tf))] es. *)
  forall i bef aft, ~ (const_list bef /\ bef ++ [::AI_suspend_desugared i] ++ aft = es).
*)

Lemma lf_composition: forall es es2 e0 lh n,
    lfilled n lh e0 es ->
    exists lh', lfilled n lh' e0 (es ++ es2).
Proof.
  move => es es2 e0 lh n HLF.
  move/lfilledP in HLF.
  inversion HLF; subst.
  - exists (LH_base vs (es' ++ es2)).
    apply/lfilledP.
    repeat rewrite -catA.
    by apply LfilledBase.
  - exists (LH_rec vs n0 es' lh' (es'' ++ es2)).
    apply/lfilledP.
    repeat rewrite -catA.
    by apply LfilledRec.
  - exists (LH_handler bef hs lh' (aft ++ es2)).
    apply/lfilledP.
    repeat rewrite -catA.
    by apply LfilledHandler.
  - exists (LH_prompt bef ts hs lh' (aft ++ es2)).
    apply/lfilledP.
    repeat rewrite -catA.
    by apply LfilledPrompt.
Qed.

Lemma lf_composition_left: forall cs es e0 lh n,
    const_list cs ->
    lfilled n lh e0 es ->
    exists lh', lfilled n lh' e0 (cs ++ es).
Proof.
  move => cs es e0 lh n HConst HLF.
  move/lfilledP in HLF.
  inversion HLF; subst.
  - exists (LH_base (cs ++ vs) es').
    apply/lfilledP.
    rewrite (catA cs vs).
    apply LfilledBase.
    by apply const_list_concat.
  - exists (LH_rec (cs ++ vs) n0 es' lh' es'').
    apply/lfilledP.
    rewrite (catA cs vs).
    apply LfilledRec => //.
    by apply const_list_concat.
  - exists (LH_handler (cs ++ bef) hs lh' aft).
    apply/lfilledP.
    rewrite (catA cs bef).
    apply LfilledHandler => //.
    by apply const_list_concat.
  - exists (LH_prompt (cs ++ bef) ts hs lh' aft).
    apply/lfilledP.
    rewrite (catA cs bef).
    apply LfilledPrompt => //.
    by apply const_list_concat.
Qed.

Lemma nlfbr_right: forall es n es',
    not_lf_br (es ++ es') n ->
    not_lf_br es n.
Proof.
  unfold not_lf_br.
  move => es n es' HNLF k lh HContra.
  eapply lf_composition in HContra.
  instantiate (1 := es') in HContra.
  destruct HContra.
  by eapply HNLF; eauto.
Qed.

Lemma nlfret_right: forall es n es',
    not_lf_return (es ++ es') n ->
    not_lf_return es n.
Proof.
  unfold not_lf_return.
  move => es n es' HNLF lh HContra.
  eapply lf_composition in HContra.
  instantiate (1 := es') in HContra.
  destruct HContra.
  by eapply HNLF; eauto.
Qed.

(*
Lemma nlfsus_right: forall es es',
    not_lf_suspend (es ++ es') ->
    not_lf_suspend es.
Proof.
  unfold not_lf_br.
  move => es es' HNLF k bef aft HContra.
  unfold not_lf_suspend in HNLF.
  apply (HNLF k bef (aft ++ es')).
  repeat rewrite catA. repeat rewrite catA in HContra.
  destruct HContra as [Hbef ->].
  done.
(*  eapply lf_composition in HContra.
  instantiate (1 := es') in HContra.
  destruct HContra.
  by eapply HNLF; eauto. *)
Qed.
*)

Lemma nlfthr_right: forall es es',
    not_lf_throw_ref (es ++ es') ->
    not_lf_throw_ref es.
Proof.
  unfold not_lf_return.
  move => es es' HNLF bef vs a i aft HContra.
  eapply (HNLF bef vs a i (aft ++ es')).
  repeat rewrite catA in HContra.
  repeat rewrite catA.
  destruct HContra as [Hbef ->].
  done.
(*  eapply lf_composition in HContra.
  instantiate (1 := es') in HContra.
  destruct HContra.
  by eapply HNLF; eauto. *)
Qed.

Lemma nlfbr_left: forall es n cs,
    const_list cs ->
    not_lf_br (cs ++ es) n ->
    not_lf_br es n.
Proof.
  unfold not_lf_return.
  move => es n cs HConst HNLF k lh HContra.
  eapply lf_composition_left in HContra => //.
  {
    instantiate (1 := cs) in HContra.
    destruct HContra.
    by eapply HNLF; eauto.
  }
  by [].
Qed.

Lemma nlfret_left: forall es n cs,
    const_list cs ->
    not_lf_return (cs ++ es) n ->
    not_lf_return es n.
Proof.
  unfold not_lf_return.
  move => es n cs HConst HNLF lh HContra.
  eapply lf_composition_left in HContra => //.
  {
    instantiate (1 := cs) in HContra.
    destruct HContra.
    by eapply HNLF; eauto.
  }
  by [].
Qed.

(*
Lemma nlfsus_left: forall es cs,
    const_list cs ->
    not_lf_suspend (cs ++ es) ->
    not_lf_suspend es.
Proof.
  unfold not_lf_return.
  move => es cs HConst HNLF k bef aft [Hbef Hes].
  apply (HNLF k (cs ++ bef) aft).
  repeat rewrite - catA. rewrite Hes. split => //.
  by apply const_list_concat.
(*  eapply lf_composition_left in HContra => //.
  {
    instantiate (1 := cs) in HContra.
    destruct HContra.
    by eapply HNLF; eauto.
  }
  by []. *)
Qed.
*)

Lemma nlfthr_left: forall es cs,
    const_list cs ->
    not_lf_throw_ref (cs ++ es) ->
    not_lf_throw_ref es.
Proof.
  unfold not_lf_return.
  move => es cs HConst HNLF bef vs a i aft [Hbef Hes].
  apply (HNLF (cs ++ bef) vs a i aft).
  repeat rewrite - catA. rewrite Hes. split => //.
  by apply const_list_concat.
(*  eapply lf_composition_left in HContra => //.
  {
    instantiate (1 := cs) in HContra.
    destruct HContra.
    by eapply HNLF; eauto.
  }
  by []. *)
Qed.

(*
Lemma to_e_list_cat: forall l1 l2,
    to_e_list (l1 ++ l2) = to_e_list l1 ++ to_e_list l2.
Proof.
    by apply properties.to_e_list_cat.
Qed.
*)

Ltac split_et_composition:=
  lazymatch goal with
  | H: e_typing _ _ (_ ++ _) _ |- _ =>
    let ts := fresh "ts" in
    let t1s := fresh "t1s" in
    let t2s := fresh "t2s" in
    let t3s := fresh "t3s" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply e_composition_typing in H;
    destruct H as [ts [t1s [t2s [t3s [H1 [H2 [H3 H4]]]]]]]; subst
  | H: typing.e_typing _ _ (_ ++ _) _ |- _ =>
    let ts := fresh "ts" in
    let t1s := fresh "t1s" in
    let t2s := fresh "t2s" in
    let t3s := fresh "t3s" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply e_composition_typing in H;
    destruct H as [ts [t1s [t2s [t3s [H1 [H2 [H3 H4]]]]]]]; subst
  end.

Ltac invert_e_typing:=
  repeat lazymatch goal with
    | H: e_typing _ _ (_ ++ _) _ |- _ =>
        split_et_composition
    | H: typing.e_typing _ _ (_ ++ _) _ |- _ =>
        split_et_composition
    | H: e_typing _ _ [::AI_label _ _ _] _ |- _ =>
        let ts := fresh "ts" in
        let t1s := fresh "t1s" in
        let H1 := fresh "H1" in
        let H2 := fresh "H2" in
        let H3 := fresh "H3" in
        let H4 := fresh "H4" in
        apply Label_typing in H;
        destruct H as [ts [t1s [H1 [H2 [H3 H4]]]]]; subst
    | H: typing.e_typing _ _ [::AI_label _ _ _] _ |- _ =>
        let ts := fresh "ts" in
        let t1s := fresh "t1s" in
        let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    eapply Label_typing in H; eauto;
    destruct H as [ts [t1s [H1 [H2 [H3 H4]]]]]; subst
    | H: e_typing _ _ [::AI_handler _ _] _ |- _ =>
    let ts := fresh "ts" in
    let H1 := fresh "Hclauses" in
    let H2 := fresh "Hbody" in
    apply Handler_typing in H as (ts & -> & H1 & H2)
    | H: typing.e_typing _ _ [::AI_handler _ _] _ |- _ =>
    let ts := fresh "ts" in
    let H1 := fresh "Hclauses" in
    let H2 := fresh "Hbody" in
    apply Handler_typing in H as (ts & -> & H1 & H2)
    | H: e_typing _ _ [::AI_prompt _ _ _] _ |- _ =>
    let H1 := fresh "Hclauses" in
    let H2 := fresh "Hbody" in
    apply Prompt_typing in H as (-> & H1 & H2)
    | H: typing.e_typing _ _ [::AI_prompt _ _ _] _ |- _ =>
    let H1 := fresh "Hclauses" in
    let H2 := fresh "Hbody" in
    apply Prompt_typing in H as (-> & H1 & H2)
  
    end.

Ltac auto_basic :=
  repeat lazymatch goal with
    | |- es_is_basic [::AI_basic _; AI_basic _; AI_basic _; AI_basic _] =>
        repeat (constructor => //)
    | |- es_is_basic [::AI_basic _; AI_basic _; AI_basic _] =>
        repeat (constructor => //)

    | |- es_is_basic [::AI_basic _; AI_basic _] =>
        repeat (constructor => //)

    | |- es_is_basic [::AI_basic _] =>
        repeat (constructor => //)

    | |- e_is_basic (AI_basic ?e) =>
        repeat (constructor => //)
    end.


(** A common scheme in the progress proof, with a continuation. **)
Ltac solve_progress_cont cont :=
  repeat eexists;
  solve [
      apply r_simple; solve [ eauto | constructor; eauto | cont; eauto ]
    | cont ].

(** The same, but without continuation. **)
Ltac solve_progress :=
  solve_progress_cont ltac:(fail).

Ltac ignore_first_values :=
  eapply r_label;
  [ | instantiate (3 := 0);
    instantiate (2 := LH_base (v_to_e_list _) [::]);
    unfold lfilled, lfill;
    rewrite v_to_e_is_const_list List.app_nil_r;
    done | 
    unfold lfilled, lfill;
    rewrite v_to_e_is_const_list;
    done
  ].

Lemma map_is_cat {A B} (f : A -> B) l res1 res2 :
  map f l = res1 ++ res2 ->
  exists l1 l2, l = l1 ++ l2 /\ map f l1 = res1 /\ map f l2 = res2.
Proof.
  generalize dependent l.
  induction res1 => //=.
  - intros l H; exists [::], l.
    done. 
  - destruct l => //. intros H; inversion H; subst.
    apply IHres1 in H2 as (l1 & l2 & -> & <- & <-).
    exists (a0 :: l1), l2. done.
Qed.

Lemma typed_cont_hfilled tf hh es s:
  c_typing s (Cont_hh tf hh) ->
  exists LI, hfilled No_var hh es LI.
Proof.
  intros Htyp.
  inversion Htyp; subst.
  eapply hfilled_change. exact H4. by left.
Qed. 

Lemma exception_clause_typing_desugar s i C cs:
  (inst_typing s i (strip C) \/ upd_label C [::] = empty_context) ->
  List.Forall (exception_clause_identifier_typing C) cs ->
  exists csd, map (desugar_exception_clause i) cs = map Some csd.
Proof.
  induction cs; first by eexists [::].
  intros HIT H.
  inversion H; subst.
  apply IHcs in H3 as (csd & Hcsd) => //.
  inversion H2; subst.
  1-2: destruct HIT as [HIT | Habs]; last by destruct C; inversion Habs; subst; destruct x.
  1-2: apply inst_typing_tags in HIT as Htags.
  1-2: apply all2_Forall2 in Htags.
  1-2: apply List.Forall2_flip in Htags.
  1-2: eapply Forall2_nth_error in Htags as (v & Hv & Hvag).
  2,4: try exact H0.
  all: eexists (_ :: csd).
  all: simpl.
  all: rewrite Hcsd.
  1-2: rewrite Hv.
  all: done.
Qed. 

Lemma continuation_clause_typing_desugar s i C cs ts:
  (inst_typing s i (strip C) \/ upd_label C [::] = empty_context) ->
  List.Forall (fun h => continuation_clause_identifier_typing C h ts) cs ->
  exists csd, map (desugar_continuation_clause i) cs = map Some csd.
Proof.
  induction cs; first by eexists [::].
  intros HIT H.
  inversion H; subst.
  apply IHcs in H3 as (csd & Hcsd) => //.
  inversion H2; subst.
  all: destruct HIT as [HIT | Habs]; last by destruct C; inversion Habs; subst; destruct x.
  all: apply inst_typing_tags in HIT as Htags.
  all: apply all2_Forall2 in Htags.
  all: apply List.Forall2_flip in Htags.
  all: eapply Forall2_nth_error in Htags as (v & Hv & Hvag);
    try exact H0.
  all: eexists (_ :: csd).
  all: simpl.
  all: rewrite Hcsd Hv.
  all: done.
Qed. 


Lemma t_progress_be: forall C bes ts1 ts2 vcs ts lab ret s f,
    store_typing s ->
    inst_typing s f.(f_inst) C ->
    map (typeof s) f.(f_locs) = map Some ts ->
    be_typing (upd_label (upd_local_return C ts ret) lab) bes (Tf ts1 ts2) ->
    map (typeof s) vcs = map Some ts1 ->
    not_lf_br (to_e_list bes) 0 ->
    not_lf_return (to_e_list bes) 0 ->
    not_lf_throw_ref (to_e_list bes) ->
    const_list (to_e_list bes) \/ 
    exists s' f' es', reduce s f (v_to_e_list vcs ++ to_e_list bes) s' f' es'.
Proof.
  move => C bes ts1 ts2 vcs ts lab ret s f HST HIT Hlocs HType HConstType HNBI_br HNRet HNThr (* HNSus *) .
  generalize dependent vcs.
  gen_ind HType; try by left.
  - (* Unop *)
    right; invert_typeof_vcs.
    destruct v => //=.
    + destruct v; solve_progress.
    + simpl in H7. destruct (typeof_ref s v) => //. 
  - (* Binop *)
    right; invert_typeof_vcs.
    rewrite H7 in H8.
    destruct v; last by simpl in H7; destruct (typeof_ref s v).
    destruct v0; last by simpl in H8; destruct (typeof_ref s v0).
    by destruct (app_binop op v v0) eqn:HBinary; solve_progress.
  - (* testop *)
    right; invert_typeof_vcs.
    destruct v; last by simpl in H7; destruct (typeof_ref s v).
    by destruct v,t => //=; solve_progress.
  - (* relop_i *)
    right. invert_typeof_vcs.
    rewrite H7 in H8.
    destruct v; last by simpl in H7; destruct (typeof_ref s v).
    destruct v0; last by simpl in H8; destruct (typeof_ref s v0).
    by destruct v => //=; destruct v0 => //=; solve_progress.
  - (* cvtop *)
    right. invert_typeof_vcs.
    destruct v; last by simpl in H8; destruct (typeof_ref s v).
    destruct (cvt t1 sx v) eqn:HConvert; destruct v,t2 => //=; solve_progress.
  - (* reinterpret *)
    right. invert_typeof_vcs.
    destruct v; last by simpl in H8; destruct (typeof_ref s v).
    by destruct v,t2 => //=; solve_progress_cont ltac:(apply rs_reinterpret).
  - (* Unreachable *)
    right.
    exists s, f, (v_to_e_list vcs ++ [::AI_trap]).
    apply reduce_composition_left; first by apply v_to_e_is_const_list.
    apply r_simple. by constructor.
  - (* Nop *)
    right.
    exists s, f, (v_to_e_list vcs ++ [::]).
    apply reduce_composition_left; first by apply v_to_e_is_const_list.
    apply r_simple. by constructor.
  - (* Drop *)
    right. invert_typeof_vcs. solve_progress.
  - (* Select *)
    right. invert_typeof_vcs.
    rewrite H6 in H7.
    destruct v1; last by simpl in H8; destruct (typeof_ref s v1).
    destruct v1 => //=.
    by destruct (s0 == Wasm_int.int_zero i32m) eqn:Heq0; move/eqP in Heq0; solve_progress.
  - (* Ref_is_null *)
    right.
    invert_typeof_vcs.
    destruct v => //.
    destruct v => //; solve_progress.
  - (* Ref_func *)
    right. invert_typeof_vcs.
    eapply func_context_store in HIT as [??].
    2: exact H. 2: exact H0.
    repeat eexists. 
    apply r_ref_func. exact H4.
  - (* Call_reference *)
    right.
    rewrite map_cat in H7. simpl in H7.
    apply typeof_append in H7 as (v & -> & Hvcst & Hv).
    destruct v => //.
    unfold v_to_e_list. rewrite map_cat.
    rewrite - catA.
    destruct v => //.
    + repeat eexists.
      ignore_first_values.
      simpl. constructor. apply rs_call_reference_null.
    + repeat eexists.
      ignore_first_values.
      simpl. simpl in Hv.
      destruct (List.nth_error (s_funcs s) f0) eqn:Hf0 => //.
      eapply r_call_reference.
      exact Hf0. simpl in Hv.
      unfold stypes. unfold get_type in H.
      inversion Hv. subst tf. rewrite H7.
      apply inst_typing_types in HIT. subst C.
      rewrite HIT in H. done.
    + simpl in Hv. destruct (List.nth_error _ f0) => //.
    + simpl in Hv. destruct (List.nth_error _ e) => //.
      destruct (_ == t) => //. 
  - (* Throw *)
    subst.
    right.
    apply inst_typing_tags in HIT as Htags.
    apply all2_Forall2 in Htags.
    apply List.Forall2_flip in Htags.
    eapply Forall2_nth_error in Htags.
    2: exact H.
    destruct Htags as (itag & Hitag & Htags).
    unfold tag_agree in Htags.
    destruct (List.nth_error _ itag) eqn:Hitags => //. 
    move/eqP in Htags; subst f0.
    rewrite map_cat in H6.
    apply map_is_cat in H6 as (vcs1 & vcs2 & -> & Hvcs1 & Hvcs2).
    unfold v_to_e_list. rewrite map_cat. rewrite - catA.
    repeat eexists.
    ignore_first_values.
    eapply r_throw.
    exact Hitag.
    exact Hitags.
    done.
    do 2 rewrite length_is_size.
    rewrite size_map.
    rewrite - (size_map Some ts) -Hvcs2 size_map. done.
    done.
  - (* Throw_ref *)
    subst. rewrite map_cat in H5.
    apply typeof_append in H5 as (v & Hvcs & Ht1s & Hv).
    destruct v => //.
    destruct v => //.
    2:{ simpl in Hv. destruct (List.nth_error _ f0) => //. }
    2:{ simpl in Hv. destruct (List.nth_error _ f0) => //. }
    + destruct r => //.
      right. rewrite Hvcs.
      rewrite /v_to_e_list map_cat.
      rewrite - catA.
      repeat eexists.
      ignore_first_values.
      constructor. constructor.
    + simpl in Hv. destruct (List.nth_error _ e) eqn:He => //.
      destruct (_ == _) eqn:Htag => //.
      move/eqP in Htag.
      right.
      rewrite Hvcs.
      rewrite -v_to_e_cat -catA.
      repeat eexists.
      ignore_first_values.
      simpl.
      eapply r_throw_ref_desugar.
      exact He. done. done.
(*  - (* Throw_ref_desugared *)
    exfalso.
    unfold not_lf_throw_ref in HNThr.
    apply (HNThr [::] vs a i [::]).
    subst bes.
    done. *)
  - (* Contnew *)
    right. invert_typeof_vcs.
    destruct v => //.
    destruct v => //.
    + solve_progress.
    + repeat eexists.
      apply r_contnew.
      apply inst_typing_types in HIT.
      unfold get_type in H. rewrite HIT in H.
      unfold stypes.
      exact H. done.
    + simpl in H7. destruct (List.nth_error _ f0) => //.
    + simpl in H7. destruct (List.nth_error _ e) => //.
      destruct (_ == t) => //. 
  - (* Resume *)
    rewrite map_cat in H7. right.
    apply typeof_append in H7 as (v & Hvcs & Ht1s & Hv).
    unfold v_to_e_list; rewrite Hvcs map_cat. rewrite -catA.
    destruct v => //.
    destruct v => //.
    + repeat eexists.
      ignore_first_values.
      constructor. constructor.
    + simpl in Hv. destruct (List.nth_error _ f0) => //.
    + simpl in Hv.
      destruct (List.nth_error _ f0) eqn:Hf0 => //.
      inversion Hv. destruct c; simpl in H7; subst f1 ts2.
      * destruct s.
        destruct HST as (_ & _ & _ & _ & Hconts & _).
        simpl in Hf0.
        rewrite List.Forall_forall in Hconts.
        apply List.nth_error_In in Hf0 as Hf0'.
        apply Hconts in Hf0'.
        apply (typed_cont_hfilled (v_to_e_list (take (size [seq Some i | i <- t1s]) vcs))) in Hf0' as [LI HLI].
        eapply continuation_clause_typing_desugar in H0 as [csd Hcsd].
        2:{ left. subst C. rewrite strip_upd_label.
            rewrite strip_upd_local_return.
            apply inst_typing_strip.
            exact HIT. } 
        repeat eexists. eapply r_resume.
        apply v_to_e_is_const_list.
        subst C. apply inst_typing_types in HIT.
        unfold get_type in H. 
        rewrite HIT in H.
        exact H.
        do 2 rewrite length_is_size.
        rewrite size_map.
        rewrite - (size_map Some t1s) -Ht1s size_map.
        assert (size [seq Some i | i <- t1s] <= size vcs).
        { rewrite - (size_map (typeof  {|
                        s_funcs := s_funcs;
                        s_tables := s_tables;
                        s_mems := s_mems;
                        s_tags := s_tags;
                        s_globals := s_globals;
                        s_exns := s_exns;
                        s_conts := s_conts
                      |}) vcs) HConstType size_map.
          rewrite size_map. rewrite size_cat. lias. } 
        repeat rewrite size_takel => //.
        exact Hf0.
        exact HLI.
        exact Hcsd.
      * repeat eexists.
        ignore_first_values.
        simpl.
        eapply r_resume_failure.
        exact Hf0.
    + simpl in Hv. destruct (List.nth_error _ e) => //.
      destruct (_ == t) => //. 
  - (* Suspend *)
    subst.
    right.
    apply inst_typing_tags in HIT.
    apply all2_Forall2 in HIT.
    apply List.Forall2_flip in HIT.
    unfold get_tag in H. destruct x.
    eapply Forall2_nth_error in HIT.
    2: exact H.
    destruct HIT as (tag & Htag & Htagt).
    repeat eexists.
    eapply r_suspend_desugar.
    exact Htag.
    unfold tag_agree in Htagt.
    destruct (List.nth_error _ tag) => //.
    move/eqP in Htagt. by subst.
    apply (f_equal length) in H5.
    do 2 rewrite List.length_map in H5.
    done.
  - (* Switch *)
    right.
    destruct x.
    apply inst_typing_tags in HIT as Htags.
    apply all2_Forall2 in Htags.
    apply List.Forall2_flip in Htags.
    unfold get_tag in H. 
    eapply Forall2_nth_error in Htags.
    2: subst C; exact H.
    destruct Htags as (tag & Htag & Htagt).
    subst. inversion H6; subst.
    rewrite map_cat in H8.
    apply typeof_append in H8 as (v & Hvcs & Hts & Hv).
    rewrite Hvcs.
    rewrite -v_to_e_cat -catA.
    simpl.
    destruct v => //=.
    destruct v => //=.
    + repeat eexists. ignore_first_values.
      constructor. constructor.
    + simpl in Hv. destruct (List.nth_error _ f0) => //.
    + simpl in Hv. destruct (List.nth_error _ f0) eqn:Hf0 => //.
      inversion Hv.
      repeat eexists.
      eapply r_switch_desugar.
      * apply inst_typing_types in HIT.
        eapply stypes_get_type in HIT.
        erewrite HIT.
        exact H0.
      * exact Htag.
      * unfold tag_agree in Htagt.
        destruct (List.nth_error _ tag) => //.
        move/eqP in Htagt. subst f1.
        done.
      * exact Hf0.
      * exact H2.
      * repeat rewrite length_is_size.
        rewrite size_cat.
        rewrite size_takel.
        rewrite size_map.
        simpl. lias.
        apply (f_equal size) in HConstType.
        rewrite map_cat size_cat size_map size_map /= in HConstType.
        rewrite size_map.
        lias.
        

    + simpl in Hv. destruct (List.nth_error _ e) => //.
      destruct (_ == _) => //. 

  - (* Contbind *)
    right. rewrite map_cat in H9.
    apply typeof_append in H9 as (v & Hvcs & Hts & Hv).
    rewrite Hvcs. rewrite /v_to_e_list map_cat -catA.
    destruct v => //.
    destruct v => //.
    + repeat eexists.
      ignore_first_values.
      simpl. constructor; constructor.
    + simpl in Hv. destruct (List.nth_error _ f0) => //.
    + simpl in Hv. destruct (List.nth_error _ f0) eqn:Hf0 => //.
      destruct c.
      * inversion Hv; subst f1.
        apply inst_typing_types in HIT. subst C.
        repeat eexists.
        apply r_contbind.
        apply v_to_e_is_const_list.
        unfold get_type in H.
        rewrite HIT in H. subst ft. exact H.
        unfold get_type in H0.
        rewrite HIT in H0. subst ft'. exact H0.
        do 2 rewrite length_is_size.
        rewrite size_map - (size_map Some ts) - Hts size_map.
        assert ( size [seq Some i | i <- ts] <= size vcs).
        { rewrite size_map - (size_map (typeof s) vcs) HConstType size_map size_cat. lias. } 
        repeat rewrite size_takel => //.
        subst ft. exact Hf0.
      * repeat eexists.
        ignore_first_values.
        eapply r_contbind_failure.
        exact Hf0.
    + simpl in Hv. destruct (List.nth_error _ e) => //.
      destruct (_ == t) => //. 
  - (* Resume_throw *)
    right. rewrite map_cat in H8.
    apply typeof_append in H8 as (v & Hvcs & Hts & Hv).
    rewrite Hvcs /v_to_e_list map_cat -catA.
    destruct v => //.
    apply inst_typing_tags in HIT as Htags.
    apply all2_Forall2 in Htags.
    apply List.Forall2_flip in Htags.
    eapply Forall2_nth_error in Htags.
    2: subst C; exact H0.
    destruct Htags as (itag & Hitag & Htags).
    unfold tag_agree in Htags.
    destruct (List.nth_error _ itag) eqn:Hitags => //. 
    move/eqP in Htags; subst f0.
    destruct v => //.
    + repeat eexists.
      ignore_first_values. constructor; constructor.
    + simpl in Hv. destruct (List.nth_error _ f0) => //.
    + simpl in Hv. destruct (List.nth_error _ f0) eqn:Hf0 => //.
      destruct c => //. 
      * inversion Hv; subst f1.
         destruct s.
        destruct HST as (_ & _ & _ & _ & Hconts & _).
        simpl in Hf0.
        rewrite List.Forall_forall in Hconts.
        apply List.nth_error_In in Hf0 as Hf0'.
        apply Hconts in Hf0'.
        apply (typed_cont_hfilled  [:: AI_ref_exn (length s_exns) (Mk_tagidx itag); AI_basic BI_throw_ref] ) in Hf0' as [LI HLI].
        eapply continuation_clause_typing_desugar in H1 as [csd Hcsd].
        2:{ subst C. rewrite strip_upd_label.
            rewrite strip_upd_local_return.
            left.
            apply inst_typing_strip.
            exact HIT. }        
        repeat eexists.
        eapply r_resume_throw.
        exact Hitag. exact Hitags.
        done.
        do 2 rewrite length_is_size.
        rewrite size_map - (size_map Some ts) - Hts size_map.
        assert ( size [seq Some i | i <- ts] <= size vcs).
        { rewrite size_map - (size_map (typeof  {|
                  s_funcs := s_funcs;
                  s_tables := s_tables;
                  s_mems := s_mems;
                  s_tags := s_tags;
                  s_globals := s_globals;
                  s_exns := s_exns;
                  s_conts := s_conts
                |}) vcs) HConstType size_map size_cat. lias. } 
        repeat rewrite size_takel => //.
        done. done.
        exact Hf0.
        subst ts2.
        apply inst_typing_types in HIT.
        unfold get_type in H.
        subst C; rewrite HIT in H.
        exact H.
        exact Hcsd.
        simpl. exact HLI.
      * repeat eexists.
        ignore_first_values.
        eapply r_resume_throw_failure.
        exact Hf0.
    + simpl in Hv. destruct (List.nth_error _ e) => //.
      destruct (_ == t) => //.
  - (* Try_table *)
    subst.
    right.
    eapply exception_clause_typing_desugar in H0 as [csd Hcsd].
    2:{ rewrite strip_upd_label strip_upd_local_return.
        left.
        apply inst_typing_strip.
        exact HIT. } 
    repeat eexists.
    eapply r_try_table.
    erewrite stypes_get_type.
    exact H. apply inst_typing_types in HIT => //.
    done.
    apply v_to_e_is_const_list.
    do 2 rewrite length_is_size.
    rewrite size_map - (size_map Some ts1) - H8 size_map => //.
    exact Hcsd.
                             
  - (* Block *)
    right.
    exists s, f, [::AI_label (length tm) [::] (v_to_e_list vcs ++ to_e_list es)].
    apply r_simple. eapply rs_block; eauto.
    + by apply v_to_e_is_const_list.
    + repeat rewrite length_is_size.
      rewrite v_to_e_size.
      subst.
      rewrite -(size_map Some ts1) -H5 size_map.
      done.
  - (* Loop *)
    right.
    exists s, f, [::AI_label (length vcs) [::AI_basic (BI_loop (Tf ts1 ts2) es)] (v_to_e_list vcs ++ to_e_list es)].
    apply r_simple. (* rewrite HConstType. *)
    eapply rs_loop; eauto; repeat rewrite length_is_size.
    + by apply v_to_e_is_const_list.
    + by rewrite v_to_e_size.
    + rewrite -(size_map Some ts1) -H5 size_map => //. 
  - (* if *)
    right.
    rewrite map_cat in H5. simpl in H5.
    apply typeof_append in H5 as [v [Ha [Hb Hc]]].
    rewrite Ha. rewrite -v_to_e_cat.
    rewrite -catA.
    destruct v; last by simpl in Hc; destruct (typeof_ref s v).
    destruct v => //=. 
    destruct (s0 == Wasm_int.int_zero i32m) eqn:Heq0; move/eqP in Heq0.
    + exists s, f, (v_to_e_list (take (size tn) vcs) ++ [::AI_basic (BI_block (Tf tn ts2) es2)]).
      rewrite size_map.
      apply reduce_composition_left ; first by apply v_to_e_is_const_list.
      apply r_simple. by eapply rs_if_false.
    + exists s, f, (v_to_e_list (take (size tn) vcs) ++ [::AI_basic (BI_block (Tf tn ts2) es1)]).
      rewrite size_map.
      apply reduce_composition_left; first by apply v_to_e_is_const_list.
      by apply r_simple; eauto.
  - (* BI_br *)
    subst.
    exfalso.
    unfold not_lf_br in HNBI_br.
    apply (HNBI_br i (LH_base [::] [::])).
    by apply lfilled0_empty. 
  - (* BI_br_if *)
    right. rewrite map_cat in HConstType.
    apply typeof_append in HConstType.
    destruct HConstType as [v [Ha [Hb Hc]]].
    rewrite Ha. rewrite -v_to_e_cat.
    rewrite -catA.
    destruct v; last by simpl in Hc; destruct (typeof_ref s v).
    destruct v => //=.
    destruct (s0 == Wasm_int.int_zero i32m) eqn:Heq0; move/eqP in Heq0.
    + exists s, f, (v_to_e_list (take (size ts2) vcs) ++ [::]).
      rewrite size_map.
      apply reduce_composition_left; first by apply v_to_e_is_const_list.
      by apply r_simple; eauto.
    + exists s, f, (v_to_e_list (take (size ts2) vcs) ++ [::AI_basic (BI_br i)]).
      rewrite size_map.
      apply reduce_composition_left; first by apply v_to_e_is_const_list.
      by apply r_simple; eauto.
  - (* BI_br_table *)
    right.
    rewrite map_cat in HConstType.
    apply cat_split in HConstType. destruct HConstType.
    assert (Evcs : vcs = take (size t1s) vcs ++ drop (size t1s) vcs); first by rewrite cat_take_drop.
    rewrite Evcs.
    symmetry in H7. rewrite -map_drop in H7.
    rewrite map_cat in H7. apply typeof_append in H7.
    destruct H7 as [v [Ha [Hb Hc]]].
    destruct v; last by simpl in Hc; destruct (typeof_ref s v).
    destruct v => //=.
    rewrite size_map in Ha. rewrite Ha.
    repeat rewrite -v_to_e_cat.
    repeat rewrite -catA. rewrite catA.
    destruct (length ins > Wasm_int.nat_of_uint i32m s0) eqn:HLength; move/ltP in HLength.
    + remember HLength as H8. clear HeqH8.
      apply List.nth_error_Some in H8.
      destruct (List.nth_error ins (Wasm_int.nat_of_uint i32m s0)) eqn:HN => //=.
      exists s, f, ((v_to_e_list (take (size t1s) vcs) ++ v_to_e_list (take (size ts) (drop (size t1s) vcs))) ++ [::AI_basic (BI_br n)]).
      rewrite size_map. apply reduce_composition_left.
      { by apply const_list_concat; apply v_to_e_is_const_list. }
      apply r_simple. apply rs_br_table => //.
      by lias.
    + assert (Inf : length ins <= Wasm_int.nat_of_uint i32m s0); first by lias.
      move/leP in Inf.
      remember Inf as Inf'. clear HeqInf'.
      apply List.nth_error_None in Inf.
      exists s, f, ((v_to_e_list (take (size t1s) vcs) ++ v_to_e_list (take (size ts) (drop (size t1s) vcs))) ++ [::AI_basic (BI_br i)]).
      rewrite size_map. apply reduce_composition_left.
      { by apply const_list_concat; apply v_to_e_is_const_list. }
      apply r_simple. apply rs_br_table_length => //.
      by lias.
  - (* Return *)
    subst.
    exfalso.
    unfold not_lf_return in HNRet.
    apply (HNRet (LH_base [::] [::])).
    by apply lfilled0_empty.
  - (* Call *)
    right. subst.
    simpl in *. (* clear H1 H2 H3 H4. *)
    eapply func_context_store in H; eauto. destruct H as [a H].
    exists s, f, (v_to_e_list vcs ++ [:: (AI_invoke a)]).
    apply reduce_composition_left; first by apply v_to_e_is_const_list.
    by apply r_call => //. 
  - (* Call_indirect *)
    right.
    simpl in *. rewrite map_cat in HConstType.
    apply typeof_append in HConstType. destruct HConstType as [v [Ha [Hb Hc]]].
    destruct v; last by simpl in Hc; destruct (typeof_ref s v).
    destruct v => //=.
    rewrite Ha. rewrite -v_to_e_cat. rewrite -catA. subst.
    exists s, f.
    destruct (stab_addr s f (Wasm_int.nat_of_uint i32m s0)) as [a|] eqn:Hstabaddr.
    + (* Some a *)
      remember Hstabaddr as Hstabaddr2. clear HeqHstabaddr2.
      eapply store_typing_stabaddr in Hstabaddr; eauto.
      destruct Hstabaddr as [cl Hstabaddr].
      destruct (stypes f.(f_inst) i == Some (cl_type cl)) eqn:Hclt; move/eqP in Hclt.
      * exists (v_to_e_list (take (size t1s) vcs) ++ [::AI_invoke a]).
        rewrite size_map.
        apply reduce_composition_left; first by apply v_to_e_is_const_list.
        simpl.
        by eapply r_call_indirect_success; eauto.
      * exists (v_to_e_list (take (size t1s) vcs) ++ [::AI_trap]).
        rewrite size_map. apply reduce_composition_left; first by apply v_to_e_is_const_list.
        by eapply r_call_indirect_failure1; eauto.
    + (* None *)
      exists (v_to_e_list (take (size t1s) vcs) ++ [::AI_trap]).
      rewrite size_map.
      apply reduce_composition_left; first by apply v_to_e_is_const_list.
      by apply r_call_indirect_failure2.

  - (* Get_local *)
    right. invert_typeof_vcs.
    simpl in H. simpl in H0.
    apply (map_nth_error Some) in H0.
    rewrite -H2 in H0.
    apply nth_error_map in H0.
    destruct H0 as [x' [HN HType]]. 
(*    rewrite length_is_size in H.
    rewrite size_map in H. *)
    exists s, f, [::AI_const x'].
    by apply r_get_local.
      
  - (* Set_local *)
    right. invert_typeof_vcs.
    simpl in H.
    rewrite length_is_size in H.
    (* rewrite size_map in H. rewrite -length_is_size in H. *)
    exists s, (Build_frame (set_nth v f.(f_locs) i v) f.(f_inst)), [::].
    eapply r_set_local; eauto.
    rewrite length_is_size.
    rewrite - (size_map Some ts) -H2 size_map in H. done.

  - (* Tee_local *)
    right. invert_typeof_vcs.
    exists s, f, [::AI_const v; AI_const v; AI_basic (BI_set_local i)].
    apply r_simple; apply rs_tee_local.
    apply const_const.

  - (* Get_global *)
    right. invert_typeof_vcs.
    simpl in H. simpl in H0.
    unfold option_map in H0.
    destruct (List.nth_error (tc_global C0) i) eqn:HN => //=.
    eapply glob_context_store in HN; eauto.
    assert (D : sglob_val s f.(f_inst) i <> None).
    { unfold sglob_val. unfold option_map.
      by destruct (operations.sglob s f.(f_inst) i). }
    destruct (sglob_val s f.(f_inst) i) eqn:Hglobval => //=.
    exists s, f, [::AI_const v].
    by apply r_get_global.

  - (* Set_global *)
    right. invert_typeof_vcs.
    destruct (supdate_glob s f.(f_inst) i v) eqn:Hs.
    + exists s0, f, [::].
      by apply r_set_global.
    + unfold supdate_glob in Hs. unfold option_bind in Hs.
      simpl in H. simpl in H0.
      eapply glob_context_store in H0; eauto.
      unfold sglob in H0. unfold operations.sglob in H0. unfold option_bind in H0.
      destruct (sglob_ind s f.(f_inst) i) eqn:Hglob => //.
      unfold supdate_glob_s in Hs. unfold option_map in Hs.
      destruct (List.nth_error (s_globals s) n) => //.

  - (* Load *)
    right. subst.
    simpl in H.
    exists s, f.
    invert_typeof_vcs.
    destruct v; last by simpl in H5; destruct (typeof_ref s v).
    destruct v => //=.
    eapply mem_context_store in H; eauto.
    destruct H as [n [HMenInd HMem]].
    destruct (List.nth_error (s_mems s) n) eqn:HN => //=.
    destruct tp_sx.
    + (* Load Some *)
      destruct p as [tp sx].
      simpl in H0. remove_bools_options.
      destruct (load_packed sx m (Wasm_int.N_of_uint i32m s0) off (length_tp tp) (length_tnum t)) eqn:HLoadResult.
      * exists [::AI_basic (BI_const (wasm_deserialise b t))].
        by eapply r_load_packed_success; eauto.
      * exists [::AI_trap].
        by eapply r_load_packed_failure; eauto.
    + (* Load None *)
      simpl in H0.
      destruct (load m (Wasm_int.N_of_uint i32m s0) off (length_tnum t)) eqn:HLoadResult.
      * exists [::AI_basic (BI_const (wasm_deserialise b t))].
        by eapply r_load_success; eauto.
      * exists [::AI_trap].
        by eapply r_load_failure; eauto.

  - (* Store *)
    right. subst.
    simpl in H.
    invert_typeof_vcs.
    destruct v; last by simpl in H5; destruct (typeof_ref s v).
    destruct v0; last by simpl in H6; destruct (typeof_ref s v0).
    inversion H6; subst t.
    destruct v => //=.
    eapply mem_context_store in H; eauto.
    destruct H as [n [HMenInd HMem]].
    destruct (List.nth_error (s_mems s) n) eqn:HN => //=.
    destruct tp as [tp |].
    + (* Store Some *)
      simpl in H0. remove_bools_options.
      destruct (store_packed m (Wasm_int.N_of_uint i32m s0) off (bits v0) (length_tp tp)) eqn:HStoreResult.
      * exists (upd_s_mem s (update_list_at s.(s_mems) n m0)), f, [::].
        eapply r_store_packed_success; eauto.
        by unfold types_num_agree; apply/eqP.
      * exists s, f, [::AI_trap].
        eapply r_store_packed_failure; eauto.
        by unfold types_num_agree; apply/eqP.
    + (* Store None *)
      simpl in H0.
      destruct (store m (Wasm_int.N_of_uint i32m s0) off (bits v0) (length_tnum (typeof_num v0))) eqn:HStoreResult.
      * exists (upd_s_mem s (update_list_at s.(s_mems) n m0)), f, [::].
        eapply r_store_success; eauto.
        by unfold types_agree; apply/eqP.
      * exists s, f, [::AI_trap].
        eapply r_store_failure; eauto.
        by unfold types_agree; apply/eqP.

  - (* Current_memory *)
    right. invert_typeof_vcs.
    simpl in H.
    eapply mem_context_store in H; eauto.
    destruct H as [n [HMemInd HMem]].
    destruct (List.nth_error (s_mems s) n) eqn:HN => //=. 
    exists s, f, [::AI_basic (BI_const (VAL_int32 (Wasm_int.int_of_Z i32m (BinInt.Z.of_nat (mem_size m)))))].
    by eapply r_current_memory; eauto.

  - (* Grow_memory *)
    right. invert_typeof_vcs.
    simpl in H.
    eapply mem_context_store in H; eauto.
    destruct H as [n [HMemInd HMem]].
    destruct (List.nth_error (s_mems s) n) eqn:HN => //=.
    destruct v; last by simpl in H7; destruct (typeof_ref s v).
    destruct v => //=.
    (* Similarly, for this proof we can just use trap and use the failure case. *)
    exists s, f, [::AI_basic (BI_const (VAL_int32 int32_minus_one))].
    by eapply r_grow_memory_failure; eauto.

  - (* Composition *)
    subst.
    rewrite to_e_list_cat in HNBI_br.
    rewrite to_e_list_cat in HNRet.
    rewrite to_e_list_cat in HNThr.
(*    rewrite to_e_list_cat in HNSus. *)
    clear H.
    edestruct IHHType1; eauto.
    { by eapply nlfbr_right; eauto. }
    { by eapply nlfret_right; eauto. }
    { by eapply nlfthr_right; eauto. }
(*    { by eapply nlfsus_right; eauto. }  *)
    + (* Const *)
      apply const_es_exists in H. destruct H as [cs HConst].
      apply b_e_elim in HConst. destruct HConst. subst.
      rewrite e_b_inverse in HNRet; last exact H2. 
      rewrite e_b_inverse in HNBI_br; last exact H2.
      rewrite e_b_inverse in HNThr; last exact H2.
(*      rewrite e_b_inverse in HNSus; last exact H2. *)
      assert (e_typing s (upd_label (upd_local_return C0 ts ret) lab) (v_to_e_list cs) (Tf ts1 t2s)) as HType1'.
      { apply ety_a'. exact H2. exact HType1. } 
      apply Const_list_typing in HType1' as (tsv & Hcs & -> & Hconst).
      edestruct IHHType2; eauto.
      { by eapply nlfbr_left; try apply v_to_e_is_const_list; eauto. }
      { by eapply nlfret_left; try apply v_to_e_is_const_list; eauto. }
      { by eapply nlfthr_left; try apply v_to_e_is_const_list; eauto. }
(*      { by eapply nlfsus_left; try apply v_to_e_is_const_list; eauto. }  *)
      { instantiate (1 := vcs ++ cs).
        do 2 rewrite map_cat. rewrite H5 Hcs. done.
      } 
      * left. rewrite to_e_list_cat. apply const_list_concat => //.
        by rewrite e_b_inverse => //; apply v_to_e_is_const_list.
      * destruct H as [es' HReduce].
        right.
        rewrite to_e_list_cat.
        rewrite e_b_inverse; last exact H2. 
        exists es'.
        rewrite catA.
        by rewrite v_to_e_cat.
    + (* reduce *)
      destruct H as [s' [vs' [es' HReduce]]].
      right.
      rewrite to_e_list_cat.
      exists s', vs', (es' ++ to_e_list [::e]).
      rewrite catA.
      by apply reduce_composition_right.

  - (* Weakening *)
    rewrite map_cat in HConstType.
    apply cat_split in HConstType.
    destruct HConstType.
    rewrite -map_take in H2. rewrite -map_drop in H6.
    subst.
    edestruct IHHType; eauto.
    right.
    destruct H3 as [s' [f' [es' HReduce]]].
    replace vcs with (take (size ts) vcs ++ drop (size ts) vcs); last by apply cat_take_drop.
    rewrite -v_to_e_cat. rewrite -catA.
    exists s', f', (v_to_e_list (take (size ts) vcs) ++ es').
    apply reduce_composition_left => //.
    by apply v_to_e_is_const_list.
    rewrite size_map in HReduce. done.
Qed.




Lemma t_progress_be_empty: forall C bes ts1 ts2 vcs s f,
    store_typing s ->
    upd_label C [::] = empty_context ->
    be_typing C bes (Tf ts1 ts2) ->
    map (typeof s) vcs = map Some ts1 ->
    not_lf_br (to_e_list bes) 0 ->
    not_lf_return (to_e_list bes) 0 ->
    not_lf_throw_ref (to_e_list bes) ->
    const_list (to_e_list bes) \/ 
    exists s' f' es', reduce s f (v_to_e_list vcs ++ to_e_list bes) s' f' es'.
Proof.
  move => C bes ts1 ts2 vcs s f HST HIT HType HConstType HNBI_br HNRet HNThr.
  generalize dependent vcs.
  gen_ind HType; try by left.
  all: subst C0.
  all: destruct C; simpl in *; subst; simpl in *.
  all: try done.
  all: try by (try destruct x as [x]); destruct x.
  - (* Unop *)
    right; invert_typeof_vcs.
    destruct v => //=.
    + destruct v; solve_progress.
    + simpl in H2. destruct (typeof_ref s v) => //. 
  - (* Binop *)
    right; invert_typeof_vcs.
    rewrite H2 in H3.
    destruct v; last by simpl in H2; destruct (typeof_ref s v).
    destruct v0; last by simpl in H3; destruct (typeof_ref s v0).
    by destruct (app_binop op v v0) eqn:HBinary; solve_progress.
  - (* testop *)
    right; invert_typeof_vcs.
    destruct v; last by simpl in H2; destruct (typeof_ref s v).
    by destruct v,t => //=; solve_progress.
  - (* relop_i *)
    right. invert_typeof_vcs.
    rewrite H2 in H3.
    destruct v; last by simpl in H2; destruct (typeof_ref s v).
    destruct v0; last by simpl in H3; destruct (typeof_ref s v0).
    by destruct v => //=; destruct v0 => //=; solve_progress.
  - (* cvtop *)
    right. invert_typeof_vcs.
    destruct v; last by simpl in H3; destruct (typeof_ref s v).
    destruct (cvt t1 sx v) eqn:HConvert; destruct v,t2 => //=; solve_progress.
  - (* reinterpret *)
    right. invert_typeof_vcs.
    destruct v; last by simpl in H3; destruct (typeof_ref s v).
    by destruct v,t2 => //=; solve_progress_cont ltac:(apply rs_reinterpret).
  - (* Unreachable *)
    right.
    exists s, f, (v_to_e_list vcs ++ [::AI_trap]).
    apply reduce_composition_left; first by apply v_to_e_is_const_list.
    apply r_simple. by constructor.
  - (* Nop *)
    right.
    exists s, f, (v_to_e_list vcs ++ [::]).
    apply reduce_composition_left; first by apply v_to_e_is_const_list.
    apply r_simple. by constructor.
  - (* Drop *)
    right. invert_typeof_vcs. solve_progress.
  - (* Select *)
    right. invert_typeof_vcs.
    rewrite H1 in H2.
    destruct v1; last by simpl in H3; destruct (typeof_ref s v1).
    destruct v1 => //=.
    by destruct (s0 == Wasm_int.int_zero i32m) eqn:Heq0; move/eqP in Heq0; solve_progress.
  - (* Ref_is_null *)
    right.
    invert_typeof_vcs.
    destruct v => //.
    destruct v => //; solve_progress.
  - (* Call_reference *)
    right.
    rewrite map_cat in H15. simpl in H15.
    apply typeof_append in H15 as (v & -> & Hvcst & Hv).
    destruct v => //.
    unfold v_to_e_list. rewrite map_cat.
    rewrite - catA.
    destruct v => //.
    + repeat eexists.
      ignore_first_values.
      simpl. constructor. apply rs_call_reference_null.
    + repeat eexists.
      ignore_first_values.
      simpl. simpl in Hv.
      destruct (List.nth_error (s_funcs s) f0) eqn:Hf0 => //.
      eapply r_call_reference.
      exact Hf0. simpl in Hv.
      unfold stypes. unfold get_type in H.
      inversion Hv. rewrite H2.
      destruct i; first by destruct i.
      done.
    + simpl in Hv. destruct (List.nth_error _ f0) => //.
    + simpl in Hv. destruct (List.nth_error _ e) => //.
      destruct (_ == t) => //. 
  - (* Throw_ref *)
    subst. rewrite map_cat in H13.
    apply typeof_append in H13 as (v & Hvcs & Ht1s & Hv).
    destruct v => //.
    destruct v => //.
    2:{ simpl in Hv. destruct (List.nth_error _ f0) => //. }
    2:{ simpl in Hv. destruct (List.nth_error _ f0) => //. }
    + destruct r => //.
      right. rewrite Hvcs.
      rewrite /v_to_e_list map_cat.
      rewrite - catA.
      repeat eexists.
      ignore_first_values.
      constructor. constructor.
    + simpl in Hv. destruct (List.nth_error _ e) eqn:He => //.
      destruct (_ == _) eqn:Htag => //.
      move/eqP in Htag.
      right.
      rewrite Hvcs.
      rewrite -v_to_e_cat -catA.
      repeat eexists.
      ignore_first_values.
      simpl.
      eapply r_throw_ref_desugar.
      exact He. done. done. 
 - (* Contnew *)
    right. invert_typeof_vcs.
    destruct v => //.
    destruct v => //.
    + solve_progress.
    + destruct i; first by destruct i.
      repeat eexists.
      apply r_contnew.
      simpl. done. done.
    + simpl in H2. destruct (List.nth_error _ f0) => //.
    + simpl in H2. destruct (List.nth_error _ e) => //.
      destruct (_ == t) => //. 
  - (* Resume *)
    rewrite map_cat in H15. right.
    apply typeof_append in H15 as (v & Hvcs & Ht1s & Hv).
    unfold v_to_e_list; rewrite Hvcs map_cat. rewrite -catA.
    destruct v => //.
    destruct v => //.
    + repeat eexists.
      ignore_first_values.
      constructor. constructor.
    + simpl in Hv. destruct (List.nth_error _ f0) => //.
    + simpl in Hv.
      destruct (List.nth_error _ f0) eqn:Hf0 => //.
      inversion Hv. destruct c; simpl in H3. subst f1.
      * remember s as s'. clear Heqs'.
        destruct s'.
        destruct HST as (_ & _ & _ & _ & Hconts & _).
        simpl in Hf0.
        rewrite List.Forall_forall in Hconts.
        apply List.nth_error_In in Hf0 as Hf0'.
        apply Hconts in Hf0'.
        apply (typed_cont_hfilled (v_to_e_list (take (size [seq Some i | i <- t1s]) vcs))) in Hf0' as [LI HLI].
        destruct i; first by destruct i. destruct f1.
        simpl in H. inversion H; subst.

        eapply continuation_clause_typing_desugar in H0 as [csd Hcsd]; last by instantiate (2 := s); right.
        repeat eexists. eapply r_resume.
        apply v_to_e_is_const_list.
        simpl. done.
        do 2 rewrite length_is_size.
        rewrite size_map.

        rewrite - (size_map Some t1s) -Ht1s size_map.
        assert (size [seq Some i | i <- t1s] <= size vcs).
        { rewrite - (size_map (typeof  {|
                        s_funcs := s_funcs;
                        s_tables := s_tables;
                        s_mems := s_mems;
                        s_tags := s_tags;
                        s_globals := s_globals;
                        s_exns := s_exns;
                        s_conts := s_conts
                      |}) vcs) HConstType size_map.
          rewrite size_map. rewrite size_cat. lias. } 
        repeat rewrite size_takel => //.
        simpl. exact Hf0.
        exact HLI.
        exact Hcsd.
      * repeat eexists.
        ignore_first_values.
        simpl.
        eapply r_resume_failure.
        exact Hf0.
    + simpl in Hv. destruct (List.nth_error _ e) => //.
      destruct (_ == t) => //. 
  - (* Contbind *)
    right. rewrite map_cat in H17.
    apply typeof_append in H17 as (v & Hvcs & Hts & Hv).
    rewrite Hvcs. rewrite /v_to_e_list map_cat -catA.
    destruct v => //.
    destruct v => //.
    + repeat eexists.
      ignore_first_values.
      simpl. constructor; constructor.
    + simpl in Hv. destruct (List.nth_error _ f0) => //.
    + simpl in Hv. destruct (List.nth_error _ f0) eqn:Hf0 => //.
      destruct c.
      * inversion Hv; subst f1.
        destruct i; first by destruct i.
        destruct i'; first by destruct i.
        simpl in H0, H. inversion H0; inversion H; subst f1 f2.
        repeat eexists.
        apply r_contbind.
        apply v_to_e_is_const_list.
        unfold get_type in H.
        done. done.
        do 2 rewrite length_is_size.
        rewrite size_map - (size_map Some ts) - Hts size_map.
        assert ( size [seq Some i | i <- ts] <= size vcs).
        { rewrite size_map - (size_map (typeof s) vcs) HConstType size_map size_cat. lias. } 
        repeat rewrite size_takel => //.
        exact Hf0.
      * repeat eexists.
        ignore_first_values.
        eapply r_contbind_failure.
        exact Hf0.
    + simpl in Hv. destruct (List.nth_error _ e) => //.
      destruct (_ == t) => //. 
  - (* Try_table *)
    right.
    destruct i as [i | [t1s t2s]]; first by destruct i.
    inversion H; subst.

    eapply exception_clause_typing_desugar in H0 as [csd Hcsd]; last by instantiate (2 := s); right.
    repeat eexists.
    eapply r_try_table.
    done.
    done. apply v_to_e_is_const_list.
    do 2 rewrite length_is_size.
    rewrite size_map - (size_map Some ts1) - H16 size_map => //.
    exact Hcsd.
                             
  - (* Block *)
    right.
    eexists s, f, [::AI_label (length _) [::] (v_to_e_list vcs ++ to_e_list es)].
    apply r_simple. eapply rs_block; eauto.
    + by apply v_to_e_is_const_list.
    + repeat rewrite length_is_size.
      rewrite v_to_e_size.
      subst.
      rewrite -(size_map Some ts1) -H13 size_map.
      done.
  - (* Loop *)
    right.
    exists s, f, [::AI_label (length vcs) [::AI_basic (BI_loop (Tf ts1 ts2) es)] (v_to_e_list vcs ++ to_e_list es)].
    apply r_simple. (* rewrite HConstType. *)
    eapply rs_loop; eauto; repeat rewrite length_is_size.
    + by apply v_to_e_is_const_list.
    + by rewrite v_to_e_size.
    + rewrite -(size_map Some ts1) -H13 size_map => //. 
  - (* if *)
    right.
    rewrite map_cat in H13. simpl in H13.
    apply typeof_append in H13 as [v [Ha [Hb Hc]]].
    rewrite Ha. rewrite -v_to_e_cat.
    rewrite -catA.
    destruct v; last by simpl in Hc; destruct (typeof_ref s v).
    destruct v => //=. 
    destruct (s0 == Wasm_int.int_zero i32m) eqn:Heq0; move/eqP in Heq0.
    + exists s, f, (v_to_e_list (take (size tn) vcs) ++ [::AI_basic (BI_block (Tf tn ts2) es2)]).
      rewrite size_map.
      apply reduce_composition_left ; first by apply v_to_e_is_const_list.
      apply r_simple. by eapply rs_if_false.
    + exists s, f, (v_to_e_list (take (size tn) vcs) ++ [::AI_basic (BI_block (Tf tn ts2) es1)]).
      rewrite size_map.
      apply reduce_composition_left; first by apply v_to_e_is_const_list.
      by apply r_simple; eauto.
  - (* BI_br *)
    subst.
    exfalso.
    unfold not_lf_br in HNBI_br.
    apply (HNBI_br i (LH_base [::] [::])).
    by apply lfilled0_empty. 
  - (* BI_br_if *)
    right. rewrite map_cat in HConstType.
    apply typeof_append in HConstType.
    destruct HConstType as [v [Ha [Hb Hc]]].
    rewrite Ha. rewrite -v_to_e_cat.
    rewrite -catA.
    destruct v; last by simpl in Hc; destruct (typeof_ref s v).
    destruct v => //=.
    destruct (s0 == Wasm_int.int_zero i32m) eqn:Heq0; move/eqP in Heq0.
    + exists s, f, (v_to_e_list (take (size ts2) vcs) ++ [::]).
      rewrite size_map.
      apply reduce_composition_left; first by apply v_to_e_is_const_list.
      by apply r_simple; eauto.
    + exists s, f, (v_to_e_list (take (size ts2) vcs) ++ [::AI_basic (BI_br i)]).
      rewrite size_map.
      apply reduce_composition_left; first by apply v_to_e_is_const_list.
      by apply r_simple; eauto.
  - (* BI_br_table *)
    right.
    rewrite map_cat in HConstType.
    apply cat_split in HConstType. destruct HConstType.
    assert (Evcs : vcs = take (size t1s) vcs ++ drop (size t1s) vcs); first by rewrite cat_take_drop.
    rewrite Evcs.
    symmetry in H2. rewrite -map_drop in H2.
    rewrite map_cat in H2. apply typeof_append in H2.
    destruct H2 as [v [Ha [Hb Hc]]].
    destruct v; last by simpl in Hc; destruct (typeof_ref s v).
    destruct v => //=.
    rewrite size_map in Ha. rewrite Ha.
    repeat rewrite -v_to_e_cat.
    repeat rewrite -catA. rewrite catA.
    destruct (length ins > Wasm_int.nat_of_uint i32m s0) eqn:HLength; move/ltP in HLength.
    + remember HLength as H8. clear HeqH8.
      apply List.nth_error_Some in H8.
      destruct (List.nth_error ins (Wasm_int.nat_of_uint i32m s0)) eqn:HN => //=.
      exists s, f, ((v_to_e_list (take (size t1s) vcs) ++ v_to_e_list (take (size ts) (drop (size t1s) vcs))) ++ [::AI_basic (BI_br n)]).
      rewrite size_map. apply reduce_composition_left.
      { by apply const_list_concat; apply v_to_e_is_const_list. }
      apply r_simple. apply rs_br_table => //.
      by lias.
    + assert (Inf : length ins <= Wasm_int.nat_of_uint i32m s0); first by lias.
      move/leP in Inf.
      remember Inf as Inf'. clear HeqInf'.
      apply List.nth_error_None in Inf.
      exists s, f, ((v_to_e_list (take (size t1s) vcs) ++ v_to_e_list (take (size ts) (drop (size t1s) vcs))) ++ [::AI_basic (BI_br i)]).
      rewrite size_map. apply reduce_composition_left.
      { by apply const_list_concat; apply v_to_e_is_const_list. }
      apply r_simple. apply rs_br_table_length => //.
      by lias.
  - (* Composition *)
    subst.
    rewrite to_e_list_cat in HNBI_br.
    rewrite to_e_list_cat in HNRet.
    rewrite to_e_list_cat in HNThr.
(*    rewrite to_e_list_cat in HNSus. *)
    clear H.
    edestruct IHHType1; eauto.
    { by eapply nlfbr_right; eauto. }
    { by eapply nlfret_right; eauto. }
    { by eapply nlfthr_right; eauto. }
(*    { by eapply nlfsus_right; eauto. }  *)
    + (* Const *)
      apply const_es_exists in H. destruct H as [cs HConst].
      apply b_e_elim in HConst. destruct HConst. subst.
      rewrite e_b_inverse in HNRet; last exact H0. 
      rewrite e_b_inverse in HNBI_br; last exact H0.
      rewrite e_b_inverse in HNThr; last exact H0.
(*      rewrite e_b_inverse in HNSus; last exact H2. *)
      assert (e_typing s  {|
        tc_types_t := [::];
        tc_func_t := [::];
        tc_global := [::];
        tc_table := [::];
        tc_memory := [::];
        tc_local := [::];
        tc_label := tc_label;
        tc_return := None;
        tc_refs := [::];
        tc_tags_t := [::]
      |} (v_to_e_list cs) (Tf ts1 t2s)) as HType1'.
      { apply ety_a'. exact H0. exact HType1. } 
      apply Const_list_typing in HType1' as (tsv & Hcs & -> & Hconst).
      edestruct IHHType2; eauto.
      { by eapply nlfbr_left; try apply v_to_e_is_const_list; eauto. }
      { by eapply nlfret_left; try apply v_to_e_is_const_list; eauto. }
      { by eapply nlfthr_left; try apply v_to_e_is_const_list; eauto. }
(*      { by eapply nlfsus_left; try apply v_to_e_is_const_list; eauto. }  *)
      { instantiate (1 := vcs ++ cs).
        do 2 rewrite map_cat. rewrite H13 Hcs. done.
      } 
      * left. rewrite to_e_list_cat. apply const_list_concat => //.
        by rewrite e_b_inverse => //; apply v_to_e_is_const_list.
      * destruct H as [es' HReduce].
        right.
        rewrite to_e_list_cat.
        rewrite e_b_inverse; last by eauto. 
        exists es'.
        rewrite catA.
        by rewrite v_to_e_cat.
    + (* reduce *)
      destruct H as [s' [vs' [es' HReduce]]].
      right.
      rewrite to_e_list_cat.
      exists s', vs', (es' ++ to_e_list [::e]).
      rewrite catA.
      by apply reduce_composition_right.

  - (* Weakening *)
    rewrite map_cat in HConstType.
    apply cat_split in HConstType.
    destruct HConstType.
    rewrite -map_take in H0. rewrite -map_drop in H1.
    subst.
    edestruct IHHType; eauto.
    right.
    destruct H2 as [s' [f' [es' HReduce]]].
    replace vcs with (take (size ts) vcs ++ drop (size ts) vcs); last by apply cat_take_drop.
    rewrite -v_to_e_cat. rewrite -catA.
    exists s', f', (v_to_e_list (take (size ts) vcs) ++ es').
    apply reduce_composition_left => //.
    by apply v_to_e_is_const_list.
    rewrite size_map in HReduce. done.
Qed. 

Definition br_reduce (es: seq administrative_instruction) :=
  exists n lh, lfilled n lh [::AI_basic (BI_br n)] es.

Definition return_reduce (es: seq administrative_instruction) :=
  exists n lh, lfilled n lh [::AI_basic BI_return] es.
(*
Definition throw_ref_reduce es i s :=
  exists hh a exn,
    List.nth_error (s_exns s) a = Some exn /\
      hfilled (Var_handler (e_tag exn) i) hh [::AI_ref_exn a; AI_basic BI_throw_ref] es.

Definition suspend_reduce es i :=
  exists x tf hh, hfilled (Var_prompt x i) hh [::AI_basic (BI_suspend (Tag_explicit x tf))] es.
*)
(** [br_reduce] is decidable. **)
Lemma br_reduce_decidable : forall es, decidable (br_reduce es).
Proof.
  move=> es. apply: pickable_decidable. apply: pickable2_weaken.
  apply lfilled_pickable_rec_gen => // es' lh lh' n.
  by apply: lfilled_decidable_base.
Defined.

(** [return_reduce] is decidable. **)
Lemma return_reduce_decidable : forall es, decidable (return_reduce es).
Proof.
  move=> es. apply: pickable_decidable. apply: pickable2_weaken.
  apply lfilled_pickable_rec => // es'.
  by apply: lfilled_decidable_base.
Defined.



Lemma lf_throw_ref_decidable : forall es, pickable5 (fun bef vs a i aft => const_list bef /\ bef ++ [:: AI_throw_ref_desugared vs a i] ++ aft = es).
Proof.
  move => es.
  induction es.
  { right. intros (bef & vs & a & i & aft & _ & Habs). destruct bef => //. }
  destruct a.
  destruct b.
  all: try by right; intros (bef & ? & ? & ? & aft & Hbef & Habs);
      destruct bef as [| a101 ?] ; try done;
    inversion Habs; subst a101; simpl in Hbef.
  - destruct IHes as [([[[[bef vs] a] i'] aft] & Hbef & <-) |] => //.
    + left. exists (AI_basic (BI_const v) :: bef, vs, a, i', aft).
      split => //=. 
    + right. intros (bef & vs & a & i & aft & Hbef & Habs).
      destruct bef => //.
      inversion Habs; subst. simpl in Hbef.
      apply n. exists bef, vs, a, i, aft. split => //. 
  - destruct IHes as [([[[[bef vs] a] i] aft] & Hbef & <-) |] => //.
    + left. exists (AI_basic (BI_ref_null r) :: bef, vs, a, i, aft).
      split => //=. 
    + right. intros (bef & vs & a & i & aft & Hbef & Habs).
      destruct bef => //. inversion Habs; subst. simpl in Hbef.
      apply n. exists bef, vs, a, i, aft. split => //.
  - destruct IHes as [([[[[bef vs] a] i] aft] & Hbef & <-) |] => //.
    + left. exists (AI_ref f :: bef, vs, a, i, aft).
      split => //=. 
    + right. intros (bef & vs & a & i & aft & Hbef & Habs).
      destruct bef => //. inversion Habs; subst. simpl in Hbef.
      apply n. exists bef, vs, a, i, aft. split => //.
  - destruct IHes as [([[[[bef vs] a] i] aft] & Hbef & <-) |] => //.
    + left. eexists (AI_ref_exn e _ :: bef, vs, a, i, aft).
      split => //=. 
    + right. intros (bef & vs & a & i & aft & Hbef & Habs).
      destruct bef => //. inversion Habs; subst. simpl in Hbef.
      apply n. exists bef, vs, a, i, aft. split => //.
  - destruct IHes as [([[[[bef vs] a] i] aft] & Hbef & <-) |] => //.
    + left. exists (AI_ref_cont f :: bef, vs, a, i, aft).
      split => //=. 
    + right. intros (bef & vs & a & i & aft & Hbef & Habs).
      destruct bef => //. inversion Habs; subst. simpl in Hbef.
      apply n. exists bef, vs, a, i, aft. split => //.
  - left. eexists ([::], _, _, _, es).
    split => //.

Qed. 

(*
Lemma lf_suspend_decidable : forall es, pickable4 (fun i tf bef aft => const_list bef /\ bef ++ [:: AI_basic (BI_suspend (Tag_explicit i tf))] ++ aft = es).
Proof.
    move => es.
  induction es.
  { right. intros (i & tf & bef & aft & _ & Habs). destruct bef => //. }
  destruct a.
  destruct b.
  all: try by right; intros (? & ? & bef & aft & Hbef & Habs);
      destruct bef as [| a101 ?] ; try done;
    inversion Habs; subst a101; simpl in Hbef.
  - destruct IHes as [([[[i tf] bef] aft] & Hbef & <-) |] => //.
    + left. exists (i, tf, AI_basic (BI_const v) :: bef, aft).
      split => //=. 
    + right. intros (i & tf & bef & aft & Hbef & Habs).
      destruct bef => //.
      inversion Habs; subst. simpl in Hbef.
      apply n. exists i, tf, bef, aft. split => //.
  - destruct IHes as [([[[i tf] bef] aft] & Hbef & <-) |] => //.
    + left. exists (i, tf, AI_basic (BI_ref_null r) :: bef, aft).
      split => //=. 
    + right. intros (i & tf & bef & aft & Hbef & Habs).
      destruct bef => //.
      inversion Habs; subst. simpl in Hbef.
      apply n. exists i, tf, bef, aft. split => //.
  - destruct t.
    + right. intros (i' & tf & bef & aft & Hbef & Habs).
      destruct bef => //. inversion Habs; subst a; simpl in Hbef; done.
    + left. exists (i, f, [::], es). split => //.
  - destruct IHes as [([[[i tf] bef] aft] & Hbef & <-) |] => //.
    + left. exists (i, tf, AI_ref f :: bef, aft).
      split => //=. 
    + right. intros (i & tf & bef & aft & Hbef & Habs).
      destruct bef => //.
      inversion Habs; subst. simpl in Hbef.
      apply n. exists i, tf, bef, aft. split => //.
  - destruct IHes as [([[[i tf] bef] aft] & Hbef & <-) |] => //.
    + left. exists (i, tf, AI_ref_exn e :: bef, aft).
      split => //=. 
    + right. intros (i & tf & bef & aft & Hbef & Habs).
      destruct bef => //.
      inversion Habs; subst. simpl in Hbef.
      apply n. exists i, tf, bef, aft. split => //.
  - destruct IHes as [([[[i tf] bef] aft] & Hbef & <-) |] => //.
    + left. exists (i, tf, AI_ref_cont f :: bef, aft).
      split => //=. 
    + right. intros (i & tf & bef & aft & Hbef & Habs).
      destruct bef => //.
      inversion Habs; subst. simpl in Hbef.
      apply n. exists i, tf, bef, aft. split => //. 
Qed.  *)

(*

Lemma lf_throw_ref_decidable : forall es, pickable (fun lh => lfilled 0 lh [:: AI_basic BI_throw_ref] es).
Proof.
  move => es.
  assert (pickable2 (fun n lh => lfilled n lh [:: AI_basic BI_throw_ref] es)).
  { apply lfilled_pickable_rec.
    by apply: lfilled_decidable_base. }
  destruct X as [[[n lh] H] | ].
  - destruct n.
    + left. exists lh. exact H. 
    + right. intros [lh' Habs].
      move/lfilledP in H.
      move/lfilledP in Habs.
      remember 0 as z.
      remember [:: AI_basic BI_throw_ref] as es0.
      generalize dependent lh.
      induction Habs; try by inversion Heqz.
      all: intros lh Hlh.
      all: inversion Hlh; subst.
      all: try by apply first_values in H1 as (_ & ? & _).
      all: try by apply first_values in H0 as (_ & ? & _).
      * apply first_values in H0 as (-> & Hhandlers & ->) => //.
        inversion Hhandlers; subst hs0 LI0.
        eapply IHHabs => //. exact H5.
      * apply first_values in H0 as (-> & Hprompts & ->) => //.
        inversion Hprompts; subst ts0 hs0 LI0.
        eapply IHHabs => //. exact H5.
  - right. intros [lh Habs].
    apply n. do 2 eexists. exact Habs.
Qed. 


Lemma lf_suspend_decidable : forall es, pickable3 (fun i tf lh => lfilled 0 lh [:: AI_basic (BI_suspend (Tag_explicit i tf))] es).
Proof.
  assert (forall n es,
             lfilled_pickable_rec_gen_measure es < n ->
             pickable3
    (fun (i : immediate) (tf : function_type)
       (lh : lholed) =>
     lfilled 0 lh
       [:: AI_basic (BI_suspend (Tag_explicit i tf))] es)).
  2:{ intros es; apply (X (S (lfilled_pickable_rec_gen_measure es))). lias. } 
  move => n.
  induction n.
  { intros es Hn => //. }
  intros es Hn.
  induction es.
  { right. intros (i & tf & lh & Habs).
    move/lfilledP in Habs.
    inversion Habs; subst. destruct vs => //.
    destruct bef => //. destruct bef => //. }
  destruct a => //=.
  destruct b => //=. 
  all: try by right; intros (? & ? & ? & Habs);
      move/lfilledP in Habs; inversion Habs; subst;
    (destruct vs as [|a101 ?] + destruct bef as [|a101 ?]); try done;
    inversion H; subst a101; simpl in H0.
  - destruct IHes as [[[[i tf] lh] H] |] => //.
    + left. 
      destruct lh.
      * exists (i, tf, LH_base (AI_basic (BI_const v) :: l) l0).
        unfold lfilled, lfill. simpl.
        unfold lfilled, lfill in H.
        destruct (const_list l) => //.
        move/eqP in H; subst es.
        done.
      * unfold lfilled, lfill in H. done.
      * exists (i, tf, LH_handler (AI_basic (BI_const v) :: l) l0 lh l1).
        unfold lfilled, lfill; fold lfill.
        simpl. unfold lfilled, lfill in H; fold lfill in H.
        destruct (const_list l) => //.
        destruct (lfill _ _ _) => //.
        move/eqP in H. subst es; done.
      * exists (i, tf, LH_prompt (AI_basic (BI_const v) :: l) l0 l1 lh l2).
        unfold lfilled, lfill; fold lfill; simpl.
        unfold lfilled, lfill in H; fold lfill in H.
        destruct (const_list l) => //.
        destruct (lfill _ _ _) => //.
        move/eqP in H. subst es; done.
    + right. intros (i & tf & lh & Habs).
      apply n0.
      move/lfilledP in Habs. inversion Habs; subst.
      * destruct vs => //.
        inversion H; subst a.
        exists i, tf, (LH_base vs es').
        apply/lfilledP. constructor.
        simpl in H0. done.
      * destruct bef => //.
        inversion H; subst a. simpl in H0.
        exists i, tf, (LH_handler bef hs lh' aft).
        apply/lfilledP. constructor. done.
        done.
      * destruct bef => //.
        inversion H; subst a. simpl in H0.
        exists i, tf, (LH_prompt bef ts hs lh' aft).
        apply/lfilledP. constructor => //.
  - destruct IHes as [[[[i tf] lh] H] |] => //.
    + left. 
      destruct lh.
      * exists (i, tf, LH_base (AI_basic (BI_ref_null r) :: l) l0).
        unfold lfilled, lfill. simpl.
        unfold lfilled, lfill in H.
        destruct (const_list l) => //.
        move/eqP in H; subst es.
        done.
      * unfold lfilled, lfill in H. done.
      * exists (i, tf, LH_handler (AI_basic (BI_ref_null r) :: l) l0 lh l1).
        unfold lfilled, lfill; fold lfill.
        simpl. unfold lfilled, lfill in H; fold lfill in H.
        destruct (const_list l) => //.
        destruct (lfill _ _ _) => //.
        move/eqP in H. subst es; done.
      * exists (i, tf, LH_prompt (AI_basic (BI_ref_null r) :: l) l0 l1 lh l2).
        unfold lfilled, lfill; fold lfill; simpl.
        unfold lfilled, lfill in H; fold lfill in H.
        destruct (const_list l) => //.
        destruct (lfill _ _ _) => //.
        move/eqP in H. subst es; done.
    + right. intros (i & tf & lh & Habs).
      apply n0.
      move/lfilledP in Habs. inversion Habs; subst.
      * destruct vs => //.
        inversion H; subst a.
        exists i, tf, (LH_base vs es').
        apply/lfilledP. constructor.
        simpl in H0. done.
      * destruct bef => //.
        inversion H; subst a. simpl in H0.
        exists i, tf, (LH_handler bef hs lh' aft).
        apply/lfilledP. constructor. done.
        done.
      * destruct bef => //.
        inversion H; subst a. simpl in H0.
        exists i, tf, (LH_prompt bef ts hs lh' aft).
        apply/lfilledP. constructor => //.
  - destruct t.
    + right.
      intros (? & tf & lh & Habs).
      move/lfilledP in Habs. inversion Habs; subst.
      destruct vs => //. inversion H; subst; simpl in H0 => //.
      destruct bef => //. inversion H; subst; simpl in H0 => //.
      destruct bef => //. inversion H; subst; simpl in H0 => //.
    + left. exists (i, f, LH_base [::] es).
      unfold lfilled, lfill => //=.
  - destruct IHes as [[[[i tf] lh] H] |] => //.
    + left. 
      destruct lh.
      * exists (i, tf, LH_base (AI_ref f :: l) l0).
        unfold lfilled, lfill. simpl.
        unfold lfilled, lfill in H.
        destruct (const_list l) => //.
        move/eqP in H; subst es.
        done.
      * unfold lfilled, lfill in H. done.
      * exists (i, tf, LH_handler (AI_ref f :: l) l0 lh l1).
        unfold lfilled, lfill; fold lfill.
        simpl. unfold lfilled, lfill in H; fold lfill in H.
        destruct (const_list l) => //.
        destruct (lfill _ _ _) => //.
        move/eqP in H. subst es; done.
      * exists (i, tf, LH_prompt (AI_ref f :: l) l0 l1 lh l2).
        unfold lfilled, lfill; fold lfill; simpl.
        unfold lfilled, lfill in H; fold lfill in H.
        destruct (const_list l) => //.
        destruct (lfill _ _ _) => //.
        move/eqP in H. subst es; done.
    + right. intros (i & tf & lh & Habs).
      apply n0.
      move/lfilledP in Habs. inversion Habs; subst.
      * destruct vs => //.
        inversion H; subst a.
        exists i, tf, (LH_base vs es').
        apply/lfilledP. constructor.
        simpl in H0. done.
      * destruct bef => //.
        inversion H; subst a. simpl in H0.
        exists i, tf, (LH_handler bef hs lh' aft).
        apply/lfilledP. constructor. done.
        done.
      * destruct bef => //.
        inversion H; subst a. simpl in H0.
        exists i, tf, (LH_prompt bef ts hs lh' aft).
        apply/lfilledP. constructor => //.
  - destruct IHes as [[[[i tf] lh] H] |] => //.
    + left. 
      destruct lh.
      * exists (i, tf, LH_base (AI_ref_exn e :: l) l0).
        unfold lfilled, lfill. simpl.
        unfold lfilled, lfill in H.
        destruct (const_list l) => //.
        move/eqP in H; subst es.
        done.
      * unfold lfilled, lfill in H. done.
      * exists (i, tf, LH_handler (AI_ref_exn e :: l) l0 lh l1).
        unfold lfilled, lfill; fold lfill.
        simpl. unfold lfilled, lfill in H; fold lfill in H.
        destruct (const_list l) => //.
        destruct (lfill _ _ _) => //.
        move/eqP in H. subst es; done.
      * exists (i, tf, LH_prompt (AI_ref_exn e :: l) l0 l1 lh l2).
        unfold lfilled, lfill; fold lfill; simpl.
        unfold lfilled, lfill in H; fold lfill in H.
        destruct (const_list l) => //.
        destruct (lfill _ _ _) => //.
        move/eqP in H. subst es; done.
    + right. intros (i & tf & lh & Habs).
      apply n0.
      move/lfilledP in Habs. inversion Habs; subst.
      * destruct vs => //.
        inversion H; subst a.
        exists i, tf, (LH_base vs es').
        apply/lfilledP. constructor.
        simpl in H0. done.
      * destruct bef => //.
        inversion H; subst a. simpl in H0.
        exists i, tf, (LH_handler bef hs lh' aft).
        apply/lfilledP. constructor. done.
        done.
      * destruct bef => //.
        inversion H; subst a. simpl in H0.
        exists i, tf, (LH_prompt bef ts hs lh' aft).
        apply/lfilledP. constructor => //.
  - destruct IHes as [[[[i tf] lh] H] |] => //.
    + left. 
      destruct lh.
      * exists (i, tf, LH_base (AI_ref_cont f :: l) l0).
        unfold lfilled, lfill. simpl.
        unfold lfilled, lfill in H.
        destruct (const_list l) => //.
        move/eqP in H; subst es.
        done.
      * unfold lfilled, lfill in H. done.
      * exists (i, tf, LH_handler (AI_ref_cont f :: l) l0 lh l1).
        unfold lfilled, lfill; fold lfill.
        simpl. unfold lfilled, lfill in H; fold lfill in H.
        destruct (const_list l) => //.
        destruct (lfill _ _ _) => //.
        move/eqP in H. subst es; done.
      * exists (i, tf, LH_prompt (AI_ref_cont f :: l) l0 l1 lh l2).
        unfold lfilled, lfill; fold lfill; simpl.
        unfold lfilled, lfill in H; fold lfill in H.
        destruct (const_list l) => //.
        destruct (lfill _ _ _) => //.
        move/eqP in H. subst es; done.
    + right. intros (i & tf & lh & Habs).
      apply n0.
      move/lfilledP in Habs. inversion Habs; subst.
      * destruct vs => //.
        inversion H; subst a.
        exists i, tf, (LH_base vs es').
        apply/lfilledP. constructor.
        simpl in H0. done.
      * destruct bef => //.
        inversion H; subst a. simpl in H0.
        exists i, tf, (LH_handler bef hs lh' aft).
        apply/lfilledP. constructor. done.
        done.
      * destruct bef => //.
        inversion H; subst a. simpl in H0.
        exists i, tf, (LH_prompt bef ts hs lh' aft).
        apply/lfilledP. constructor => //.
  -  destruct (IHn l0) as [[[[i tf] lh] H] |] => //.
     + specialize (lfilled_pickable_rec_gen_measure_handler_r l l0 es) as Hm.
       clear -Hn Hm. lias.
     + left.
       exists (i, tf, LH_handler [::] l lh es).
       apply/lfilledP.
       rewrite - (cat0s (AI_handler _ _ :: _)).
       constructor. done. by move/lfilledP in H.
    + right. intros (i & tf & lh & Habs).
      apply n0.
      move/lfilledP in Habs. inversion Habs; subst.
      * destruct vs => //.
        inversion H; subst a.
        simpl in H0. done.
      * destruct bef => //.
        2:{ inversion H; subst a. simpl in H0. done. } 
        inversion H; subst l l0 es. 
        exists i, tf, lh'.
        apply/lfilledP. done. 
      * destruct bef => //.
        inversion H; subst a. simpl in H0.
        done.
  - destruct (IHn l1) as [[[[i tf] lh] H] |] => //.
     + specialize (lfilled_pickable_rec_gen_measure_prompt_r l l0 l1 es) as Hm.
       clear -Hn Hm. lias.
     + left.
       exists (i, tf, LH_prompt [::] l l0 lh es).
       apply/lfilledP.
       rewrite - (cat0s (AI_prompt _ _ _ :: _)).
       constructor. done. by move/lfilledP in H.
    + right. intros (i & tf & lh & Habs).
      apply n0.
      move/lfilledP in Habs. inversion Habs; subst.
      * destruct vs => //.
        inversion H; subst a.
        simpl in H0. done.
      * destruct bef => //.
        inversion H; subst a. simpl in H0.
        done.
      * destruct bef => //.
        2:{ inversion H; subst a. simpl in H0. done. } 
        inversion H; subst l l0 l1 es. 
        exists i, tf, lh'.
        apply/lfilledP. done. 
Qed. *)

(** [suspend_reduce] is decidable. **)
(*
Lemma suspend_reduce_decidable : forall es i, decidable (suspend_reduce es i).
Proof.
A dmitted. 
(*
  move=> es i. apply: pickable_decidable. apply: pickable2_weaken.
  apply: pickable3_weaken.
  apply hfilled_pickable_rec_gen => // es' lh lh' n.
  by apply: lfilled_decidable_base.
Defined.
*)

(** [throw_ref_reduce] is decidable. **)
Lemma throw_ref_reduce_decidable : forall es i s, decidable (throw_ref_reduce es i s).
Proof.
A dmitted. *)
(*  move=> es i s. apply: pickable_decidable.
  apply: pickable2_weaken.
  apply: pickable3_weaken.
  
  apply hfilled_pickable_rec => // es'.
  by apply: lfilled_decidable_base.
Defined. *)

Local Lemma cat_abcd_a_bc_d: forall {X:Type} (a b c d: seq X),
    a ++ b ++ c ++ d = a ++ (b ++ c) ++ d.
Proof.
  move => X a b c d.
  f_equal. by rewrite catA.
Qed.

Lemma br_reduce_label_length: forall n k lh es s C ts2,
    lfilled n lh [::AI_basic (BI_br (n + k))] es ->
    e_typing s C es (Tf [::] ts2) ->
    length (tc_label C) > k.
Proof.
  move => n k lh es s C ts2 HLF.
  generalize dependent ts2. generalize dependent C.
  generalize dependent s.
  move/lfilledP in HLF.
  dependent induction HLF; move => s C ts2 HType.
  - invert_e_typing.
    destruct ts => //=; destruct t1s => //=; clear H1.
    rewrite add0n in H5.
    apply et_to_bet in H5; auto_basic.
    simpl in H5. eapply Break_typing in H5; eauto.
    destruct H5 as [ts [ts2 [H7 [H8 H9]]]].
    unfold plop2 in H8. move/eqP in H8.
    apply/ltP.
    apply List.nth_error_Some. by rewrite H8.
  - invert_e_typing.
    destruct ts => //=; destruct t1s => //=; clear H1.
    assert (Inf : k+1 < length (tc_label (upd_label C ([::ts1] ++ tc_label C)))).
    { eapply IHHLF; eauto.
      repeat (f_equal; try by lias). }
    simpl in Inf. by lias.
  - invert_e_typing.
    destruct ts, t1s => //.
    eapply IHHLF. done.
    exact Hbody. 
  - invert_e_typing.
    destruct ts0, t1s => //.
    eapply IHHLF. done.
    eapply typing_leq.
    exact Hbody. apply empty_context_leq.
Qed.

Lemma return_reduce_return_some: forall n lh es s C ts2,
    lfilled n lh [::AI_basic BI_return] es ->
    e_typing s C es (Tf [::] ts2) ->
    tc_return C <> None.
Proof.
  move => n lh es s C ts2 HLF.
  generalize dependent s. generalize dependent C. generalize dependent ts2.
  move/lfilledP in HLF.
  dependent induction HLF; subst; move => ts2 C s HType.
  - invert_e_typing.
    destruct ts; destruct t1s => //=; clear H1.
    apply et_to_bet in H5; auto_basic.
    simpl in H5. eapply Return_typing in H5; eauto.
    destruct H5 as [ts [ts' [H7 H8]]]. subst.
    by rewrite H8.
  - invert_e_typing.
    assert (R : tc_return (upd_label C ([::ts1] ++ tc_label C)) <> None).
    { by eapply IHHLF; eauto. }
    by simpl in R.
  - invert_e_typing.
    destruct ts, t1s => //.
    eapply IHHLF. done. exact Hbody.
  - invert_e_typing.
    destruct ts0, t1s => //.
    eapply IHHLF. done.
    eapply typing_leq.
    exact Hbody. apply empty_context_leq.
Qed.

(*
Lemma br_typing_empty_context k lh j LI s tf:
  lfilled k lh [::AI_basic (BI_br j)] LI ->
  e_typing s empty_context LI tf ->
  False.
Proof.
  intros Hfill Htyp. destruct tf.
  move/lfilledP in Hfill.
  remember [:: AI_basic (BI_br j)] as esbr.
  induction Hfill; subst; invert_e_typing => //.
  - clear -H0. convert_et_to_bet.
    apply Break_typing in H0 as (? & ? & ? & _).
    done.
  - apply IHHfill => //.
*)

Lemma br_reduce_extract_vs: forall n k lh es s C ts ts2,
    lfilled n lh [::AI_basic (BI_br (n + k))] es ->
    e_typing s C es (Tf [::] ts2) ->
    List.nth_error (tc_label C) k = Some ts ->
    exists vs lh', const_list vs /\
      lfilled n lh' (vs ++ [::AI_basic (BI_br (n + k))]) es /\
      length vs = length ts.
Proof.
  move => n k lh es s C ts ts2 HLF.
  move/lfilledP in HLF.
  generalize dependent ts. generalize dependent ts2.
  generalize dependent C. generalize dependent s.
  dependent induction HLF; subst; move => s C ts2 ts' HType HN.
  - invert_e_typing.
    destruct ts; destruct t1s => //; clear H1.
    rewrite add0n in H5.
    apply et_to_bet in H5; auto_basic.
    simpl in H5.
    eapply Break_typing in H5; eauto.
    destruct H5 as [ts3 [ts3' [H7 [H8 H9]]]]. subst.
    unfold plop2 in H8. move/eqP in H8.
    rewrite HN in H8. inversion H8. subst.
    apply const_es_exists in H.
    destruct H as [vs' H]. subst.
    apply Const_list_typing in H3. simpl in H3.
    rewrite catA in H3.
    destruct H3 as (tsv & Htsv & H3 & Hconst). symmetry in H3.
    apply cat_split in H3. destruct H3.
    replace vs' with (take (size (ts0 ++ ts3')) vs' ++ drop (size (ts0 ++ ts3')) vs'); last by apply cat_take_drop.
    exists (v_to_e_list (drop (size (ts0 ++ ts3')) vs')), (LH_base (v_to_e_list (take (size (ts0 ++ ts3')) vs')) es').
    repeat split.
    + by apply v_to_e_is_const_list.
    + apply/lfilledP.
      rewrite -v_to_e_cat. rewrite -catA.
      rewrite cat_abcd_a_bc_d.
      by apply LfilledBase; apply v_to_e_is_const_list.
    + rewrite H0.
      repeat rewrite length_is_size.
      rewrite v_to_e_size.
      do 2 rewrite size_drop.
      rewrite - (size_map Some tsv) - Htsv size_map.
      done.
  - invert_e_typing.
    destruct ts; destruct t1s => //; clear H1.
    edestruct IHHLF; eauto.
    { instantiate (1 := k.+1).
      repeat (f_equal; try by lias). }
    {  simpl. by eauto. }
    destruct H0 as [lh2 [HConst [HLF2 HLength]]].
    replace (k0.+1+k) with (k0+k.+1); last by lias.
    repeat eexists. repeat split => //; eauto.
    move/lfilledP in HLF2. apply/lfilledP.
    instantiate (1 := (LH_rec vs (length ts1) es' lh2 es'')).
    apply LfilledRec => //.
    by apply HLength.
  - invert_e_typing.
    destruct ts, t1s => //.
    edestruct IHHLF as (vs & lhres & Hvs & Hfill & Hlen); eauto.
    do 2 eexists.
    repeat split; eauto. 
    instantiate (1 := LH_handler bef hs lhres aft).
    move/lfilledP in Hfill. apply/lfilledP.
    apply LfilledHandler => //.
  - invert_e_typing.
    eapply br_reduce_label_length in Hbody.
    2: apply/lfilledP; exact HLF.
    done.
Qed.


Lemma return_reduce_extract_vs: forall n lh es s C ts ts2,
    lfilled n lh [::AI_basic BI_return] es ->
    e_typing s C es (Tf [::] ts2) ->
    tc_return C = Some ts ->
    exists vs lh', const_list vs /\
      lfilled n lh' (vs ++ [::AI_basic BI_return]) es /\
      length vs = length ts.
Proof.
  move => n lh es s C ts ts2 HLF.
  move/lfilledP in HLF.
  generalize dependent ts. generalize dependent ts2.
  generalize dependent C. generalize dependent s.
  dependent induction HLF; subst; move => s C ts2 ts' HType HN.
  - invert_e_typing.
    destruct ts; destruct t1s => //; clear H1.
    apply et_to_bet in H5; auto_basic.
    simpl in H5.
    eapply Return_typing in H5; eauto.
    destruct H5 as [ts2 [ts2' [H7 H8]]]. subst.
    rewrite HN in H8. inversion H8. subst.
    apply const_es_exists in H.
    destruct H as [vs' H]. subst.
    apply Const_list_typing in H3. simpl in H3.
    rewrite catA in H3.
    destruct H3 as (tsv & Htsv & H3 & Hconst).
    symmetry in H3.
    apply cat_split in H3. destruct H3.
    replace vs' with (take (size (ts0 ++ ts2')) vs' ++ drop (size (ts0 ++ ts2')) vs'); last by apply cat_take_drop.
    exists (v_to_e_list (drop (size (ts0 ++ ts2')) vs')), (LH_base (v_to_e_list (take (size (ts0 ++ ts2')) vs')) es').
    repeat split.
    + by apply v_to_e_is_const_list.
    + apply/lfilledP.
      rewrite -v_to_e_cat. rewrite -catA.
      rewrite cat_abcd_a_bc_d.
      by apply LfilledBase; apply v_to_e_is_const_list.
    + rewrite H0.
      repeat rewrite length_is_size.
      rewrite v_to_e_size.
      do 2 rewrite size_drop.
      rewrite - (size_map Some tsv) -Htsv size_map => //. 
  - invert_e_typing.
    destruct ts; destruct t1s => //; clear H1.
    edestruct IHHLF; eauto.
    destruct H0 as [lh2 [HConst [HLF2 HLength]]].
    repeat eexists. repeat split => //; eauto.
    move/lfilledP in HLF2. apply/lfilledP.
    instantiate (1 := (LH_rec vs (length ts1) es' lh2 es'')).
    apply LfilledRec => //.
    by apply HLength.
  - invert_e_typing.
    destruct ts, t1s => //.
    edestruct IHHLF as (vs & lhres & Hvs & Hfill & Hlen); eauto.
    do 2 eexists.
    repeat split; eauto. 
    instantiate (1 := LH_handler bef hs lhres aft).
    move/lfilledP in Hfill. apply/lfilledP.
    apply LfilledHandler => //.
  - invert_e_typing.
    eapply return_reduce_return_some in Hbody.
    2: apply/lfilledP; exact HLF.
    done.
Qed.

Lemma le_add: forall n m,
    n <= m ->
    exists k, m = n+k.
Proof.
  move => n m. move: m n.
  elim => [|m].
  - move => n Hn. exists 0.
    case: n Hn => //=.
  - move => IHm.
    case => [|n] Hn.
    + by exists (m.+1).
    + move: (IHm n Hn) => [k Hk].
      exists k.
      by lias.
Qed.

(*
  These two guarantees that the extra conditions we put in progress_e are true -- the second
    being true only if the function doesn't return anything (so we are not in the middle of some
    Local functions).
*)
Lemma s_typing_lf_br: forall s rs f es ts,
    s_typing s rs f es ts ->
    (forall n lh k, lfilled n lh [::AI_basic (BI_br k)] es -> k < n).
Proof.
  move => s rs f es ts HType n lh k HLF.
  inversion HType. inversion H. subst.
  destruct (k<n) eqn: H3 => //=.
  move/ltP in H3.
  assert (Inf : n <= k); first by lias.
  apply le_add in Inf.
  destruct Inf as [j Inf]. subst.
  clear H3.
  eapply br_reduce_label_length in H1; eauto.
  simpl in H1.
  assert (E : tc_label C1 = [::]); first by eapply inst_t_context_label_empty; eauto.
  by rewrite E in H1.
Qed.

Lemma s_typing_lf_return: forall s f es ts,
    s_typing s None f es ts ->
    (forall n, not_lf_return es n).
Proof.
  unfold not_lf_return.
  move => s f es ts HType n lh HContra.
  inversion HType; subst.
  by eapply return_reduce_return_some in H1; eauto.
Qed.



Fixpoint find_first_some {A : Type} (l : seq.seq (option A)) :=
  match l with
  | [::] => None
  | Some e :: q => Some e
  | None :: q => find_first_some q end.

Fixpoint first_instr_instr e :=
  match e with
  | AI_basic (BI_const _) => None
  | AI_basic (BI_ref_null _) => None
  | AI_ref _ => None
  | AI_ref_cont _ => None
  | AI_ref_exn _ _ => None
  | AI_label n es LI =>
      match find_first_some (List.map first_instr_instr LI)
      with Some (e',i) => Some (e',S i) | None => Some (e,0) end
  | AI_local n es LI =>
      match find_first_some (List.map first_instr_instr LI)
      with Some (e',i) => Some (e',S i) | None => Some (e,0) end
  | AI_handler hs LI =>
      match find_first_some (List.map first_instr_instr LI)
      with Some (e', i) => Some (e', i) | None => Some (e, 0) end
  | AI_prompt ts hs LI =>
      match find_first_some (List.map first_instr_instr LI)
      with Some (e', i) => Some (e', i) | None => Some (e, 0) end
  | _ => Some (e,0) end.

Definition first_instr es :=
  find_first_some (List.map first_instr_instr es).

Lemma first_instr_const vs es :
  const_list vs -> first_instr (vs ++ es) = first_instr es.
Proof.
  intro Hvs.
  induction vs => //=.
  destruct a ; try by inversion Hvs.
  destruct b ; try by inversion Hvs.
  all: simpl in Hvs.
  all: rewrite <- (IHvs Hvs).
  all: by unfold first_instr.
Qed.

Lemma starts_with_lfilled e i es k lh les :
  first_instr es = Some (e,i) ->
  lfilled k lh es les ->
  first_instr les = Some (e,i + k).
Proof.
  generalize dependent es. generalize dependent k. generalize dependent les.
  induction lh ; intros les k es Hstart Hfill ; unfold lfilled, lfill in Hfill; fold lfill in Hfill.
  - destruct k => //. 
    remember (const_list l) as b eqn:Hl ; destruct b => //. 
    move/eqP in Hfill. rewrite Hfill ; clear Hfill.
    rewrite (first_instr_const (es ++ l0) (Logic.eq_sym Hl)). 
    induction es ; first by inversion Hstart. unfold addn.
    rewrite PeanoNat.Nat.add_0_r.
    destruct a ; unfold first_instr ;
      simpl ; unfold first_instr in Hstart ;
      simpl in Hstart ; try done.
    destruct b ; unfold first_instr ; simpl ;
        unfold first_instr in Hstart ;
        simpl in Hstart ; eauto; try done.
    all: unfold addn in IHes ; rewrite PeanoNat.Nat.add_0_r in IHes.
    all: unfold first_instr in IHes.
    all: eauto. 
    all: destruct (find_first_some _) => //=.
    all: destruct p; try done. 
  - destruct k => //. 
    remember (const_list l) as b eqn:Hl ; destruct b => //. 
    remember (lfill k lh es) as fill ; destruct fill => //. 
    move/eqP in Hfill.
    assert (lfilled k lh es l2) ; first by unfold lfilled ; rewrite <- Heqfill.
    subst. rewrite (first_instr_const _ (Logic.eq_sym Hl)). 
    unfold first_instr => //=.
    unfold first_instr in IHlh.
    eapply IHlh in H;eauto.
    rewrite H => //=.
    rewrite - addnS. done.
  - remember (const_list l) as b eqn:Hl ; destruct b => //. 
    remember (lfill k lh es) as fill ; destruct fill => //. 
    move/eqP in Hfill.
    assert (lfilled k lh es l2) ; first by unfold lfilled ; rewrite <- Heqfill.
    subst. rewrite (first_instr_const _ (Logic.eq_sym Hl)). 
    unfold first_instr => //=.
    unfold first_instr in IHlh.
    eapply IHlh in H;eauto.
    rewrite H => //=.
  - remember (const_list l) as b eqn:Hl ; destruct b => //. 
    remember (lfill k lh es) as fill ; destruct fill => //. 
    move/eqP in Hfill.
    assert (lfilled k lh es l3) ; first by unfold lfilled ; rewrite <- Heqfill.
    subst. rewrite (first_instr_const _ (Logic.eq_sym Hl)). 
    unfold first_instr => //=.
    unfold first_instr in IHlh.
    eapply IHlh in H;eauto.
    rewrite H => //=.
Qed.

Lemma lfilled_implies_starts k lh e es :
  (forall n es' LI, e <> AI_label n es' LI) ->
  (forall n es' LI, e <> AI_local n es' LI) ->
  (forall hs LI, e <> AI_handler hs LI) ->
  (forall ts hs LI, e <> AI_prompt ts hs LI) ->
  (is_const e -> False) ->
  lfilled k lh [::e] es ->
  first_instr es = Some (e,k).
Proof.
  generalize dependent es. generalize dependent k.
  induction lh ; intros k es Hlabel Hlocal Hhandler Hprompt Hconst Hfill ; unfold lfilled, lfill in Hfill; fold lfill in Hfill.
  - destruct k => //.
    destruct (const_list l) eqn:Hl => //.
    move/eqP in Hfill.
    destruct e ; subst ;
      rewrite (first_instr_const _ Hl) ; try by unfold first_instr.
    destruct b ; try by unfold first_instr.
    all: try by exfalso ; apply Hconst.
    by exfalso; eapply Hhandler.
    by exfalso; eapply Hprompt.
    by exfalso ; eapply Hlabel.
    by exfalso ; eapply Hlocal. 
  - destruct k => //.
    destruct (const_list l) eqn:Hl => //.
    remember (lfill _ _ _) as fill ; destruct fill => //. 
    move/eqP in Hfill.
    subst. rewrite (first_instr_const _ Hl).
    unfold first_instr => //=. unfold first_instr in IHlh.
    assert (lfilled k lh [::e] l2) ; first by unfold lfilled ; rewrite <- Heqfill.
    eapply IHlh in H => //=. rewrite H => //=.
  - destruct (const_list l) eqn:Hl => //.
    destruct (lfill _ _ _) eqn:Hfill' => //.
    move/eqP in Hfill; subst.
    rewrite (first_instr_const _ Hl).
    unfold first_instr => //=. unfold first_instr in IHlh.
    assert (lfilled k lh [::e] l2); first by unfold lfilled; rewrite Hfill'.
    eapply IHlh in H => //=. rewrite H => //.
  - destruct (const_list l) eqn:Hl => //.
    destruct (lfill _ _ _) eqn:Hfill' => //.
    move/eqP in Hfill; subst.
    rewrite (first_instr_const _ Hl).
    unfold first_instr => //=. unfold first_instr in IHlh.
    assert (lfilled k lh [::e] l3); first by unfold lfilled; rewrite Hfill'.
    eapply IHlh in H => //=. rewrite H => //. 
Qed.


Lemma first_instr_app e :
  forall a es', first_instr e = Some a -> first_instr (e ++ es') = Some a.
Proof.
  induction e; intros a0 es';try done.
  cbn. destruct (first_instr_instr a) eqn:Ha;auto.
  intros Hf. eapply IHe with (es':=es') in Hf. auto.
Qed.


(*  Fixpoint hholed_of_lholed lh :=
    match lh with
    | LH_base bef aft => HH_base bef aft
    | LH_rec bef n es lh aft => HH_label bef n es (hholed_of_lholed lh) aft
    | LH_handler bef hs lh aft => HH_handler bef hs (hholed_of_lholed lh) aft
    | LH_prompt bef ts hs lh aft => HH_prompt bef ts hs (hholed_of_lholed lh) aft
    end.
 *)

Lemma list_last {A} (x : A) l : exists x' l', x :: l = l' ++ [:: x'].
Proof.
  generalize dependent x.
  induction l => //=.
  - intros x. exists x, [::] => //.
  - intros x.
    destruct (IHl a) as (x' & l' & ->).
    exists x', (x :: l'). done.
Qed. 

Definition hholed_append hh es :=
  match hh with
  | HH_base bef aft => HH_base bef (aft ++ es)
  | HH_label bef n es' hh aft => HH_label bef n es' hh (aft ++ es)
  | HH_local bef n f hh aft => HH_local bef n f hh (aft ++ es)
  | HH_handler bef hs hh aft => HH_handler bef hs hh (aft ++ es)
  | HH_prompt bef ts hs hh aft => HH_prompt bef ts hs hh (aft ++ es)
  end.

Lemma app_app_r {A} (l1 l2 l3 l4: list A):
  l1 ++ l2 = l3 ++ l4 -> length l2 = length l4 ->
  l1 = l3 /\ l2 = l4.
Proof.
  generalize dependent l1.
  generalize dependent l3.
  generalize dependent l4.
  induction l2; intros l4 l3 l1.
  - destruct l4 => //. do 2 rewrite cats0. done.
  - destruct l4 => //.
    intros Hl Hlen.
    rewrite separate1 in Hl.
    rewrite (separate1 a0) in Hl.
    do 2 rewrite - cat_app in Hl.
    do 2 rewrite catA in Hl.
    simpl in Hlen.
    apply IHl2 in Hl as [Hl ->]; last lias.
    apply concat_cancel_last in Hl as [-> ->].
    done.
Qed.



Lemma hfilled_append x hh es LI es' :
  hfilled x hh es LI <-> hfilled x (hholed_append hh es') es (LI ++ es').
Proof.
  split.
  - intros H.
    move/hfilledP in H.
    apply/hfilledP.
    inversion H; subst;
      repeat rewrite -catA;
      econstructor => //.
  - intros H.
    move/hfilledP in H.
    apply/hfilledP.
    destruct hh; 
      inversion H; subst.
    + repeat rewrite catA in H5.
      rewrite -(catA l _ l0) in H5.
      apply app_app_r in H5 as [<- _] => //.
      constructor => //.
    + rewrite separate1 -cat_app in H8.
      repeat rewrite catA in H8.
      rewrite -(catA l _ l1) in H8.
      apply app_app_r in H8 as [<- _] => //.
      constructor => //.
    + rewrite separate1 -cat_app in H8.
      repeat rewrite catA in H8.
      rewrite -(catA l _ l0) in H8.
      apply app_app_r in H8 as [<- _] => //.
      econstructor => //.
    + rewrite separate1 -cat_app in H7.
      repeat rewrite catA in H7.
      rewrite -(catA l _ l1) in H7.
      apply app_app_r in H7 as [<- _] => //.
      constructor => //.
    + rewrite separate1 -cat_app in H8.
      repeat rewrite catA in H8.
      rewrite -(catA l _ l2) in H8.
      apply app_app_r in H8 as [<- _] => //.
      constructor => //.
Qed.

Definition hholed_prepend hh es :=
  match hh with
  | HH_base bef aft => HH_base (es ++ bef) aft
  | HH_label bef n es' hh aft => HH_label (es ++ bef) n es' hh aft
  | HH_local bef n f hh aft => HH_local (es ++ bef) n f hh aft
  | HH_handler bef hs hh aft => HH_handler (es ++ bef) hs hh aft
  | HH_prompt bef ts hs hh aft => HH_prompt (es ++ bef) ts hs hh aft
  end.


Lemma hfilled_prepend x hh es LI es' :
  (const_list es' /\
     hfilled x hh es LI) <-> hfilled x (hholed_prepend hh es') es (es' ++ LI).
Proof.
  split.
  - intros [Hes' H].
    move/hfilledP in H.
    apply/hfilledP.
    inversion H; subst;
      repeat rewrite catA;
      rewrite -(catA (_ ++ _));
      econstructor => //. 
    all: by apply const_list_concat.

  - intros H.
    move/hfilledP in H.
    destruct hh; 
      inversion H; subst.
    + repeat rewrite - catA in H5.
      apply app_app in H5 => //. inversion H5; subst.
      apply const_list_split in H4 as [??].
      split => //. apply/hfilledP; constructor => //.
    + repeat rewrite - catA in H8.
      apply app_app in H8 => //.
      inversion H8; subst.
      apply const_list_split in H7 as [??].
      split => //. apply/hfilledP; constructor => //.
    + repeat rewrite - catA in H8.
      apply app_app in H8 => //.
      inversion H8; subst.
      apply const_list_split in H7 as [??].
      split => //. apply/hfilledP; econstructor => //.
    + repeat rewrite - catA in H7.
      apply app_app in H7 => //.
      inversion H7; subst.
      apply const_list_split in H6 as [??].
      split => //. apply/hfilledP; constructor => //.
    + repeat rewrite - catA in H8.
      apply app_app in H8 => //.
      inversion H8; subst.
      apply const_list_split in H7 as [??].
      split => //. apply/hfilledP; constructor => //.
  Qed.

Lemma hfilled_const x hh es LI :
  hfilled x hh es LI -> const_list LI -> const_list es.
Proof.
  intros Hfill HLI.
  move/hfilledP in Hfill.
  inversion Hfill; subst.
  all: apply const_list_split in HLI as [_ HLI].
  all: apply const_list_split in HLI as [HLI _] => //.
Qed.

(* No longer necessary *)
(*
Lemma hfilled_suspend_values x hh n i LI s C ts:
  e_typing s C LI (Tf [::] ts) ->
  hfilled x hh [:: AI_suspend_desugared n (Mk_tagidx i)] LI ->
  exists vs hh' t1s t2s,
    List.nth_error (s_tags s) i = Some (Tf t1s t2s) /\
      n = length t1s /\ 
      const_list vs /\
      length vs = length t1s /\
      hfilled x hh' (vs ++ [:: AI_suspend_desugared n (Mk_tagidx i)]) LI.
Proof.
  intros Htype Hfill.
  move/hfilledP in Hfill.
  remember [:: _] as es.
  generalize dependent C. generalize dependent ts.
  induction Hfill; subst es.
  all: intros tse C Htype.
  all: apply e_composition_typing in Htype as (t0s & t1s & t2s & t3s & Hempty & -> & Hbef & Hmidaft).
  all: destruct t0s => //.
  all: destruct t1s => //. 
  all: apply e_composition_typing in Hmidaft as (t0s' & t1s' & t2s' & t3s' & -> & -> & Hmid & Haft).
  - apply const_es_exists in H as [vvs ->].
    apply Const_list_typing in Hbef as (tsv & Htsv & Htypes & Hconst).
    apply AI_suspend_desugared_typing in Hmid as (ts & t1s'' & t2s'' & -> & -> & -> & Htags).
    exists (drop (size tsv - size t1s'') (v_to_e_list vvs)),
      (HH_base (take (size tsv - size t1s'') (v_to_e_list vvs)) es'), t1s'', t2s''.
    repeat split => //.
    + rewrite - map_drop. apply v_to_e_is_const_list.
    + do 2 rewrite length_is_size.
      rewrite size_drop.
      rewrite size_map -(size_map (typeof s) vvs) Htsv size_map.
      assert (size (t0s' ++ ts ++ t1s'') = size tsv) as Hsize;
        first by rewrite Htypes.
      repeat rewrite size_cat in Hsize.
      lias.
    + unfold hfilled, hfill.
      rewrite - map_take. rewrite v_to_e_is_const_list.
      rewrite map_take. repeat rewrite catA.
      rewrite cat_take_drop. done.
  - apply Label_typing in Hmid as (ts & t2s & -> & Hes' & HLI & Hn).
    apply IHHfill in HLI as (vss & hhs & t1s & t2ss & Htags & Hlen & Hconst & Hvss & Hfills) => //.
    exists vss, (HH_label vs n0 es' hhs es''), t1s, t2ss.
    repeat split => //.
    apply/hfilledP. constructor => //.
    apply/hfilledP. exact Hfills.
  - apply Local_typing in Hmid as (ts & -> & HLI & Hn).
    inversion HLI; subst.
    apply IHHfill in H2 as (vss & hhs & t1s & t2ss & Htags & Hlen & Hconst & Hvss & Hfills) => //.
    exists vss, (HH_local vs (length ts) f hhs es''), t1s, t2ss.
    repeat split => //.
    apply/hfilledP. econstructor => //.
    apply/hfilledP. exact Hfills.
  - apply Prompt_typing in Hmid as (-> & Hhs & HLI).
    apply IHHfill in HLI as (vss & hhs & t1s & t2ss & Htags & Hlen & Hconst & Hvss & Hfills) => //.
    exists vss, (HH_prompt bef ts hs hhs aft), t1s, t2ss.
    repeat split => //.
    apply/hfilledP. constructor => //.
    apply/hfilledP. exact Hfills.
  - apply Handler_typing in Hmid as (ts & -> & Hhs & HLI).
    apply IHHfill in HLI as (vss & hhs & t1s & t2ss & Htags & Hlen & Hconst &  Hvss & Hfills) => //.
    exists vss, (HH_handler bef hs hhs aft), t1s, t2ss.
    repeat split => //.
    apply/hfilledP. constructor => //.
    apply/hfilledP. exact Hfills.
Qed.


Lemma hfilled_switch_values x n tf hh i LI s C ts:
  e_typing s C LI (Tf [::] ts) ->
  hfilled x hh [:: AI_switch_desugared n tf (Mk_tagidx i)] LI ->
  (exists vs hh' k cont t1s t2s tf',
    List.nth_error (s_conts s) k = Some cont /\
      typeof_cont cont = tf /\
      tf = Tf (t1s ++ [:: T_ref (T_contref tf')]) t2s /\
      const_list vs /\ length vs = n /\
      length vs = length t1s /\
      hfilled x hh' (vs ++ [:: AI_ref_cont k; AI_switch_desugared n tf (Mk_tagidx i)]) LI)
  \/ exists rt hh', hfilled x hh' [:: AI_basic (BI_ref_null rt) ; AI_switch_desugared n tf (Mk_tagidx i)] LI.
Proof.
  intros Htype Hfill.
  move/hfilledP in Hfill.
  remember [:: _] as es.
  generalize dependent C. generalize dependent ts.
  induction Hfill; subst es.
  all: intros tse C Htype.
  all: apply e_composition_typing in Htype as (t0s & t1s & t2s & t3s & Hempty & -> & Hbef & Hmidaft).
  all: destruct t0s => //.
  all: destruct t1s => //. 
  all: apply e_composition_typing in Hmidaft as (t0s' & t1s' & t2s' & t3s' & -> & -> & Hmid & Haft).
  - apply const_es_exists in H as [vvs ->].
    apply Const_list_typing in Hbef as (tsv & Htsv & Htypes & Hconst).
    apply AI_switch_desugared_typing in Hmid as (ts & t1s'' & t2s'' & tpref & Htags & Htf & -> & ->).
    simpl in Htypes. remember Htsv as Htsv'; clear HeqHtsv'.
    rewrite - Htypes in Htsv.
    repeat rewrite catA in Htsv.
    rewrite map_cat in Htsv.
    apply typeof_append in Htsv as (v & Hvvs & Htsv & Hv).
    destruct v => //.
    destruct v => //.
    + right.
      exists r, (HH_base (v_to_e_list (take (size [seq Some i | i <- (t0s' ++ tpref) ++ t1s'']) vvs)) es').
      unfold hfilled, hfill. rewrite v_to_e_is_const_list.
      rewrite -> Hvvs at 1.
      rewrite -v_to_e_cat.
      simpl. repeat rewrite - catA. done.
    + simpl in Hv. destruct (List.nth_error _ f) => //. 
    + simpl in Hv. destruct (List.nth_error _ f) eqn:Hf => //.
      simpl in Hv. inversion Hv. 
      left.
      eexists (drop (size tsv - size t1s'' - 1) (take (size vvs - 1) (v_to_e_list vvs))),
        (HH_base (take (size tsv - size t1s'' - 1) (v_to_e_list vvs)) es'), f, c, _,_,_.
      repeat split => //.
      * rewrite H0. exact Htf.
      * rewrite - map_take. rewrite - map_drop.
        apply v_to_e_is_const_list.
      * admit.
      * do 2 rewrite length_is_size.
        rewrite size_drop.
        rewrite size_takel; last by rewrite size_map; lias.
        rewrite -(size_map (typeof s) vvs) Htsv' size_map.
        assert (size t1s'' < size tsv).
        { rewrite -Htypes. repeat rewrite size_cat.
          simpl. lias. }
        clear - H. lias.
      * unfold hfilled, hfill.
        assert (size vvs = size tsv) as Hvvstsv.
        { rewrite - (size_map (typeof s) vvs) Htsv' size_map.
          done. } 
        assert (S (size ((t0s' ++ tpref) ++ t1s'')) = size vvs) as Hsizevvs.
        { rewrite Hvvstsv.
          rewrite -Htypes.
          repeat rewrite catA.
          rewrite (size_cat _ [:: _]).
          simpl. lias. } 
        rewrite - map_take. rewrite v_to_e_is_const_list.
        rewrite map_take.
        erewrite <- take_takel.
        repeat rewrite catA.
        erewrite cat_take_drop.
        2:{ rewrite Hvvstsv. lias. } 
        rewrite (separate1 (AI_ref_cont f)).
        rewrite -cat_app.
        repeat rewrite catA.
        replace [:: AI_ref_cont f] with (drop (size vvs - 1) (v_to_e_list vvs)).
        rewrite cat_take_drop.
        done.
        rewrite -> Hvvs at 2.
        rewrite -v_to_e_cat.
        rewrite drop_size_cat. done.
        repeat rewrite size_map.
        rewrite size_takel; last lias.
        lias.
    + simpl in Hv. destruct (List.nth_error _ e) => //.
      destruct (_ == t) => //. 
  - apply Label_typing in Hmid as (ts & t2s & -> & Hes' & HLI & Hn).
    apply IHHfill in HLI as [(vss & hhs & k & cont & t1s & t2ss & tf' & Hconts & Htcont & Hft & Hconst & Hlen & Hvss & Hfills) | (rt & hhs & Hfills)] => //.
    + left.
      exists vss, (HH_label vs n0 es' hhs es''), k, cont, t1s, t2ss, tf'.
      repeat split => //.
      apply/hfilledP. constructor => //.
      apply/hfilledP. exact Hfills.
    + right.
      exists rt, (HH_label vs n0 es' hhs es'').
      apply/hfilledP. constructor => //.
      apply/hfilledP. exact Hfills.
  - apply Local_typing in Hmid as (ts & -> & HLI & Hn).
    inversion HLI; subst.
    apply IHHfill in H2 as [(vss & hhs & k & cont & t1s & t2ss & tf' & Hconts & Htcont & Hft & Hconst & Hlen & Hvss & Hfills) | (rt & hhs & Hfills)] => //.
    + left.
      exists vss, (HH_local vs (length ts) f hhs es''), k, cont, t1s, t2ss, tf'.
      repeat split => //.
      apply/hfilledP. econstructor => //.
      apply/hfilledP. exact Hfills.
    + right.
      exists rt, (HH_local vs (length ts) f hhs es'').
      apply/hfilledP. constructor => //.
      apply/hfilledP. exact Hfills.
  - apply Prompt_typing in Hmid as (-> & Hhs & HLI).
    apply IHHfill in HLI as [(vss & hhs & k & cont & t1s & t2ss & tf' & Hconts & Htcont & Hft & Hconst & Hlen & Hvss & Hfills) | (rt & hhs & Hfills)] => //.
    + left.
      exists vss, (HH_prompt bef ts hs hhs aft), k, cont, t1s, t2ss, tf'.
      repeat split => //.
      apply/hfilledP. constructor => //.
      apply/hfilledP. exact Hfills.
    + right.
      exists rt, (HH_prompt bef ts hs hhs aft).
      apply/hfilledP. constructor => //.
      apply/hfilledP. exact Hfills.
  - apply Handler_typing in Hmid as (ts & -> & Hhs & HLI).
    apply IHHfill in HLI as [(vss & hhs & k & cont & t1s & t2ss & tf' & Hconts & Htcont & Hft & Hconst & Hlen & Hvss & Hfills) | (rt & hhs & Hfills)] => //.
    + left.
      exists vss, (HH_handler bef hs hhs aft), k, cont, t1s, t2ss, tf'.
      repeat split => //.
      apply/hfilledP. constructor => //.
      apply/hfilledP. exact Hfills.
    + right.
      exists rt, (HH_handler bef hs hhs aft).
      apply/hfilledP. constructor => //.
      apply/hfilledP. exact Hfills.
A dmitted.

(*
Lemma t_progress_e_empty_context: forall s C f vcs es tf ts1 ts2,
    e_typing s C es tf ->
    tf = Tf ts1 ts2 ->
    upd_label C [::] = empty_context ->
    map (typeof s) vcs = map Some ts1 ->
    store_typing s ->
    (forall n lh k, lfilled n lh [::AI_basic (BI_br k)] es -> k < n) ->
    (forall n, not_lf_return es n) ->
    (forall tf h vcs n, first_instr es = Some (AI_call_host tf h vcs,n) -> False) ->
    terminal_form s (f_inst f) (v_to_e_list vcs ++ es) \/
      exists s' f' es', reduce s f (v_to_e_list vcs ++ es) s' f' es'.
Proof.
  intros s C f vcs es tf t1s t2s Htype Htf HC Hvcs HST Hbr Hret Hcallhost.
  generalize dependent t2s. generalize dependent t1s.
  generalize dependent vcs.
  induction Htype; intros vcs tx Hvcs ty Htf.
  - subst tf.
    destruct (lf_throw_ref_decidable (to_e_list bes)) as [([bef aft] & Hbef & Habs) | HNThr].
    { (* left. right. right. left. *)
      symmetry in Habs.
      apply map_is_cat in Habs as (befb & restb & -> & Hbefb & Hrestb).
      apply map_is_cat in Hrestb as (midb & aftb & -> & Hmidb & Haftb).
      destruct midb => //.
      destruct midb => //.
      inversion Hmidb; subst b.
      apply composition_typing in H as (ts0 & t1s' & t2s' & t3s & -> & -> & Hbefbt & Hrestt).
      apply composition_typing in Hrestt as (ts0' & t1s'' & t2s'' & t3s' & -> & -> & Hthrowt & Haftbt).
      apply Throw_ref_typing in Hthrowt as (ts' & ->).
      apply (ety_a s) in Hbefbt.
      unfold to_e_list in Hbefbt.
      rewrite Hbefb in Hbefbt.
      apply const_es_exists in Hbef as [vs ->].
      apply Const_list_typing in Hbefbt as (tsv & Htsv & Htypes & Hconst).
      destruct tsv.
      - destruct vs => //. destruct befb => //=.
        rewrite cats0 in Htypes; subst t1s'.
        repeat rewrite map_cat in Hvcs.
        repeat rewrite catA in Hvcs.
        apply typeof_append in Hvcs as (v & Hvcs & Hfirsts & Hv).
        destruct v => //. destruct v => //.
        + destruct r => //. right.
          rewrite Hvcs.
          repeat eexists.
          rewrite -v_to_e_cat.
          rewrite (separate1 (AI_basic BI_throw_ref)).
          rewrite -cat_app. rewrite -catA. rewrite (catA _ [:: _] (to_e_list aftb)).
          eapply r_label.
          2:{
            instantiate (3 := 0).
            instantiate (2 := LH_base (v_to_e_list _) _).
            unfold lfilled, lfill.
            rewrite v_to_e_is_const_list. done. }
          2:{ unfold lfilled, lfill.
              rewrite v_to_e_is_const_list.
              done. }
          constructor. constructor.
        + simpl in Hv. destruct (List.nth_error _ f0) => //.
        + simpl in Hv. destruct (List.nth_error _ f0) => //.
        + simpl in Hv. destruct (List.nth_error _ e) eqn:He => //.
          rewrite Hvcs. left. right. right. left.
          eexists (HH_base (v_to_e_list _) _), e, e0.
          split => //.
          unfold hfilled, hfill. rewrite v_to_e_is_const_list.
          unfold v_to_e_list. rewrite map_cat.
          simpl. repeat rewrite - catA.
          simpl. done.
      - rewrite to_e_list_cat.
        unfold to_e_list. rewrite Hbefb.
        destruct (list_last v tsv) as (v' & tsv' & Htsv').
        rewrite Htsv' in Htypes Htsv.
        do 2 rewrite catA in Htypes.
        apply concat_cancel_last in Htypes as [Htypes <-].
        rewrite map_cat in Htsv.
        apply typeof_append in Htsv as (v' & Hvs & Htsvt' & Hv').
        destruct v' => //.
        destruct v0 => //.
        + destruct r => //.
          rewrite Hvs. right. repeat eexists.
          rewrite -v_to_e_cat.
          simpl. rewrite (separate1 (AI_basic BI_throw_ref)).
          rewrite -cat_app. rewrite -catA. rewrite (catA _ [:: _] (to_e_list aftb)).
          simpl. rewrite catA. rewrite v_to_e_cat. rewrite separate2.
          eapply r_label.
          2:{ instantiate (3 := 0). instantiate (2 := LH_base (v_to_e_list _) _).
              unfold lfilled, lfill. rewrite v_to_e_is_const_list. done. }
          2:{ unfold lfilled, lfill. rewrite v_to_e_is_const_list. done. }
          constructor. constructor.
        + simpl in Hv'. destruct (List.nth_error _ f0) => //.
        + simpl in Hv'. destruct (List.nth_error _ f0) => //.
        + simpl in Hv'. destruct (List.nth_error _ e) eqn:He => //.
          rewrite Hvs. left. right. right. left.
          eexists (HH_base (v_to_e_list _) _), e, e0.
          split => //.  unfold hfilled, hfill. rewrite v_to_e_is_const_list.
          unfold v_to_e_list. rewrite map_cat. simpl. repeat rewrite - catA.
          simpl. rewrite catA. rewrite - map_cat. done. } 
      
    eapply t_progress_be_empty in H; try instantiate (1 := vs) in HType; try by eauto.
    destruct H as [HType | [s' [vs' [es' HType]]]].
    + left.
      unfold terminal_form; left.
      apply const_list_concat => //. by apply v_to_e_is_const_list.
    + right. 
      repeat eexists. by apply HType.
    + unfold not_lf_br. move => k lh HContra.
      by apply Hbr in HContra.
    + intros bef aft [Hbef Habs].
      apply HNThr. exists bef, aft. split => //.
  - (* Composition *)
    inversion Htf; subst.
    edestruct IHHtype1; eauto.
    + move => n lh k HLF.
      eapply lf_composition in HLF.
      destruct HLF as [lh' HLF].
      instantiate (1 := [::e]) in HLF.
      eapply Hbr.
      by apply HLF. 
    + move => n.
      eapply nlfret_right. by apply Hret.
    + move => tf h vcs0 n HLF.
      eapply Hcallhost.
      eapply first_instr_app.
      exact HLF. 
    + (* Terminal *)
      unfold terminal_form in H. destruct H as [H | [H | [H | H]]].
      * (* Const *)
        apply const_list_split in H. destruct H as [HC1 HC2].
        apply const_es_exists in HC2.
        destruct HC2 as [esv HC2]. subst.
        apply Const_list_typing in Htype1 as (tsesv & Htsesv & -> & Hconst).
        edestruct IHHtype2.
        7: done. eauto. eauto.
        (* should generalize on something *) 
(*        -- instantiate (1 := vcs ++ esv).
           do 2 rewrite map_cat.
           rewrite Htsesv HConstType.
           done. *)
        -- move => n lh k HLF.
           eapply lf_composition_left in HLF.
           instantiate (1 := v_to_e_list esv) in HLF.
           destruct HLF as [lh' HLF].
           eapply Hbr; eauto.
           by apply v_to_e_is_const_list. 
        -- move => n.
           eapply nlfret_left.
           instantiate (1 := v_to_e_list esv); first by apply v_to_e_is_const_list.
           by apply Hret.
(*        -- intros n.
           eapply nlfthr_left.
           instantiate (1 := v_to_e_list _).
           by apply v_to_e_is_const_list.
           by apply HNthr.
        -- intros n.
           eapply nlfsus_left.
           instantiate (1 := v_to_e_list _).
           by apply v_to_e_is_const_list.
           by apply HNSus. *)
        -- move => tf h vcs0 n HLF.
           eapply Hcallhost.
           eapply starts_with_lfilled.
           exact HLF.
           instantiate (2 := 0).
           instantiate (1 := LH_base (v_to_e_list esv) [::]).
           unfold lfilled, lfill => /=.
           rewrite v_to_e_is_const_list.
           done.
        -- instantiate (1 := vcs ++ esv).
           do 2 rewrite map_cat.
           rewrite Htsesv Hvcs.
           done.
        -- (* Terminal *)
          left. rewrite catA v_to_e_cat. done.
(*          unfold terminal_form in H. destruct H as [H | [H | [H | H]]].
          ++ left. unfold terminal_form. left.
             rewrite -v_to_e_cat in H.
             by rewrite catA.
          ++ apply extract_list1 in H. destruct H.
             rewrite -v_to_e_cat in H.
             destruct vcs => //=.
             destruct esv => //=.
             left. subst. by apply terminal_trap.
          ++ left. destruct H as (hh & a & exn & Ha & Hfill).
             right. right. left.
             exists hh, a, exn. split => //.
             rewrite catA v_to_e_cat. done.
          ++  *)
        -- (* reduce *)
          rewrite -v_to_e_cat in H.
          rewrite -catA in H.
          right.
          by eapply H.
      * (* AI_trap *)
        destruct vcs => //=.
        2:{ simpl in H. destruct v => //. destruct v => //. }
        destruct es => //=; destruct es => //=.
        simpl in H. inversion H. subst.
        right.
        exists s, f, [::AI_trap].
        apply r_simple.
        eapply rs_trap => //.
        instantiate (1 := (LH_base [::] [::e])).
        apply/lfilledP.
        by apply LfilledBase => //=; apply v_to_e_is_const_list.
      * destruct H as (hh & a & exn & Ha & Hfill).
        left. right. right. left.
        exists (hholed_append hh [:: e]), a, exn.
        split => //.
        rewrite catA.
        apply hfilled_append. done.
      * destruct H as (i & hh & Hfill).
        left. right. right. right.
        exists i, (hholed_append hh [:: e]).
        rewrite catA. apply hfilled_append => //. 
        
    + (* reduce *)
      destruct H as [s' [f' [es' HReduce]]].
      right.
      exists s', f', (es' ++ [::e]).
      eapply r_label; eauto; try apply/lfilledP.
      * assert (LF : lfilledInd 0 (LH_base [::] [::e]) (v_to_e_list vcs ++ es) ([::] ++ (v_to_e_list vcs ++ es) ++ [::e]));
          first by apply LfilledBase.
        simpl in LF. rewrite -catA in LF. by apply LF.
      * by apply LfilledBase.
  - (* Weakening *)
    inversion Htf; subst.
    rewrite map_cat in Hvcs.
    apply cat_split in Hvcs as [HCT1 HCT2].
    rewrite - map_take in HCT1.
    rewrite - map_drop in HCT2. 
    assert (Evcs : vcs = take (size ts) vcs ++ drop (size ts) vcs).
    { symmetry. by apply cat_take_drop. }
    rewrite Evcs. rewrite - v_to_e_cat.
    edestruct IHHtype; eauto.
    + (* Terminal *)
      unfold terminal_form in H.
      destruct H as [H | [H | [H | H]]] => //=.
      * (* Const *)
        left. rewrite size_map in H. unfold terminal_form. left.
        rewrite -catA. apply const_list_concat => //.
        by apply v_to_e_is_const_list.
      * (* AI_trap *)
        apply v_e_trap in H; last by apply v_to_e_is_const_list.
        destruct H. rewrite size_map in H. subst.
        rewrite H.
        destruct (drop (size ts) vcs) eqn:HDrop => //=.
        clear H. rewrite cats0 in Evcs. rewrite -Evcs.
        rewrite cats0.
        destruct vcs => //.
        -- left. by apply terminal_trap.
        -- right.
           exists s, f, [::AI_trap].
           apply r_simple.
           apply reduce_trap_left => //.
           by apply v_to_e_is_const_list.
      * destruct H as (hh & a & exn & Hexn & Hfill).
        left. right. right. left.
        eexists (hholed_prepend hh _), a, exn.
        split => //.
        rewrite -catA.
        apply hfilled_prepend.
        split; first by apply v_to_e_is_const_list.
        rewrite size_map in Hfill. done.
      * destruct H as (i & hh & Hfill).
        left. right. right. right.
        eexists i, (hholed_prepend hh _).
        rewrite -catA.
        apply hfilled_prepend.
        split; first by apply v_to_e_is_const_list.
        rewrite size_map in Hfill. done.
    + (* reduce *)
      destruct H as [s' [f' [es' HReduce]]].
      right.
      exists s', f', (v_to_e_list (take (size ts) vcs) ++ es').
      rewrite -catA. rewrite size_map in HReduce.
      apply reduce_composition_left => //; first by apply v_to_e_is_const_list.
      
  - (* AI_trap *)
    destruct vcs => //; first by left; apply terminal_trap.
    right.
    exists s, f, [::AI_trap].
    apply r_simple.
    apply reduce_trap_left => //.
    by apply v_to_e_is_const_list.
  - (* Local *)
    inversion Htf; subst; clear Htf.
    destruct vcs => //. 

    destruct (return_reduce_decidable es) as [HEMT | HEMF].
    { inversion H; subst.
      unfold return_reduce in HEMT.
      destruct HEMT as [n [lh HLF]].
      eapply return_reduce_extract_vs in HLF; eauto.
      destruct HLF as [cs [lh' [HConst [HLF2 HLength]]]].
      right.
      repeat eexists.
      apply r_simple.
      eapply rs_return; eauto.
    }
(*    edestruct IHHType as [[ Hconst | [ Htrap | [ Hthr | Hsus]]] | Hreduce ]; eauto. *)
    edestruct IHHtype as [[[ Hconst | [ Htrap | [ Hthr | Hsus]]] Htypconst ]| Hreduce ]; eauto. 
    {
      move => n lh k HLF.
      by eapply s_typing_lf_br in HLF; eauto.
    }
    { unfold return_reduce in HEMF. unfold not_lf_return.
      move => n lh HContra.
      apply HEMF. by eauto.
    }
    { move => tf h vcs n HLF.  
      eapply HCallHost.
      unfold first_instr => /=.
      unfold first_instr in HLF.
      rewrite HLF.
      done. } 
    + (* Const *)
      right. exists s, f, es.
      apply r_simple.
      apply rs_local_const => //.
      specialize (Htypconst Hconst).
      apply const_es_exists in Hconst as [vs ->].
      done.
(*      apply Const_list_typing in Htypconst as (tsv & Htsv & -> & _).
      rewrite length_is_size length_is_size size_map /=.
      rewrite - (size_map Some tsv) - Htsv size_map => //.  *)
    + (* AI_trap *)
      subst.
      right. exists s, f, [::AI_trap].
      apply r_simple.
      by apply rs_local_trap.
    + (* throw_ref *)
      left. right. right. left.
      destruct Hthr as (hh & a & exn & Hexn & Hfill).
      exists (HH_local [::] (length ts2) f0 hh [::]), a, exn.
      split => //. 
      unfold hfilled, hfill; fold hfill. simpl.
      unfold hfilled in Hfill.
      destruct (hfill _ _ _) => //.
      move/eqP in Hfill. subst. done.
    + (* Suspend *)
      left. right. right. right.
      destruct Hsus as (i & hh & Hfill).
      exists i, (HH_local [::] (length ts2) f0 hh [::]).
      unfold hfilled, hfill; fold hfill. simpl.
      unfold hfilled in Hfill.
      destruct (hfill _ _ _) => //.
      move/eqP in Hfill. subst. done.
    + (* reduce *)
      destruct Hreduce as [s' [f0' [es' HReduce]]].
      right. exists s', f, [::AI_local (length ts2) f0' es'].
      by apply r_local; apply HReduce.
  - (* Ref *)
    left.
    left.
    apply const_list_concat => //. apply v_to_e_is_const_list.
  - (* Ref_cont *)
    left. left. apply const_list_concat => //.
    apply v_to_e_is_const_list.
  - (* Ref_exn *)
    left. left. apply const_list_concat => //.
    apply v_to_e_is_const_list.
  - (* Suspend_desugared *)
    intros s C x tf Htags f C' vcs ts1 ts2 lab ret ts -> Hlocs HC HIT Hvcs HST HBI_brDepth HNRet HCallHost.
    left. right. right. right.
    exists x, (HH_base (v_to_e_list vcs) [::]).
    apply/hfilledP. constructor.
    apply v_to_e_is_const_list.
    
  - (* Prompt *)
    move => s C hs es ts Hclauses Hes IH.
    move => f C' vcs ts1 ts2 lab ret ts0 HTF Hts0 HContext HInst HConstType HST HBI_brDepth HNRet HCallHost.
    inversion HTF; subst.
    destruct vcs => //.
    edestruct IH; eauto.
    { admit. }
    { 
      move => n lh k HLF.
      eapply HBI_brDepth.
      move/lfilledP in HLF.
      apply/lfilledP.
      instantiate (1 := LH_prompt [::] ts2 hs lh [::]).
      rewrite - (cat0s [:: AI_prompt _ _ _]) - (cats0 [:: AI_prompt _ _ _]).
      constructor => //. } 
    { unfold not_lf_return.
      move => n lh HContra.
      unfold not_lf_return in HNRet.
      eapply HNRet.
      move/lfilledP in HContra.
      apply/lfilledP.
      instantiate (1 := LH_prompt [::] ts2 hs lh [::]).
      rewrite - (cat0s [:: AI_prompt _ _ _]) - (cats0 [:: AI_prompt _ _ _]).
      constructor => //.
      exact HContra.
    } 
    { move => tf h vcs n HLF.
      eapply HCallHost.
      unfold first_instr => /=.
      unfold first_instr in HLF.
      rewrite HLF.
      done. } 
    + (* Terminal *)
      simpl. simpl in H. destruct H as [H | [H | [H | H]]].
      * (* Const *)
        right.
        exists s, f, es.
        apply r_simple.
        by apply rs_prompt_const.
      * (* AI_trap *)
        right. subst.
        exists s, f, [::AI_trap].
        apply r_simple.
        by apply rs_prompt_trap.
      * (* Throw_ref *)
        left. right. right. left.
        destruct H as (hh & a & exn & Hexn & Hfill).
        exists (HH_prompt [::] ts2 hs hh [::]), a, exn.
        split => //.
        apply/hfilledP.
        rewrite -(cat0s [::AI_prompt _ _ _]) -(cats0 [::AI_prompt _ _ _]).
        constructor => //.
        apply/hfilledP. done.
      * (* Suspend *)
        destruct H as (i & hh & Hfill).
        destruct (firstx_continuation hs (f_inst f) i) eqn:Hfirst.
        -- right.
           eapply hfilled_suspend_values in Hes as (vs & hh' & t1s & t2s & Htags & Hconst & Hvs & Hfill');
             last exact Hfill.
           repeat eexists.
           eapply r_suspend.
           exact Hconst.
           exact Htags.
           exact Hvs.
           exact Hfirst.
           exact Hfill'.
        -- left. right. right. right.
           exists i, (HH_prompt [::] ts2 hs hh [::]).
           apply/hfilledP.
           rewrite -(cat0s [::AI_prompt _ _ _]) - (cats0 [:: AI_prompt _ _ _]).
           constructor => //.
           apply/hfilledP. exact Hfill.
    + (* reduce *)
      destruct H as [s' [f' [es' HReduce]]].
      right.
      simpl in HReduce.
      exists s', f', [::AI_prompt ts2 hs es'].
      eapply r_label; eauto.
      instantiate (1 := LH_prompt [::] ts2 hs (LH_base [::] [::]) [::]).
      instantiate (1 := 0).
      unfold lfilled, lfill => //=.
      by rewrite List.app_nil_r.
      unfold lfilled, lfill => /=.
      by rewrite List.app_nil_r.

  - (* Handler *)
    move => s C hs es ts Hclauses Hes IH.
    move => f C' vcs ts1 ts2 lab ret ts0 HTF Hts0 HContext HInst HConstType HST HBI_brDepth HNRet HCallHost.
    inversion HTF; subst.
    destruct vcs => //.
    simpl. 
    (*
    destruct (br_reduce_decidable es) as [HEMT | HEMF].
    { unfold br_reduce in HEMT.
      destruct HEMT as [n [lh HLF]].
      right. 
      assert (LF : lfilled n lh [::AI_basic (BI_br (n+0))] es); first by rewrite addn0.
      eapply br_reduce_extract_vs in LF => //; eauto.
      instantiate (1 := ts) in LF. 
      destruct LF as [cs [lh' [HConst [HLF2 HLength]]]].
      rewrite addn0 in HLF2.
      repeat eexists.
      apply r_simple.
      eapply rs_br; eauto.
      by [].
    } *)
    edestruct IH; eauto.
(*    { rewrite upd_label_overwrite. simpl. eauto. } *)
    { 
      move => n lh k HLF.
      eapply HBI_brDepth.
      move/lfilledP in HLF.
      apply/lfilledP.
      instantiate (1 := LH_handler [::] hs lh [::]).
      rewrite - (cat0s [:: AI_handler hs es]).
      rewrite - (cats0 [:: AI_handler hs es]).
      constructor. done. done. }
    { unfold not_lf_return.
      move => n lh HContra.
      unfold not_lf_return in HNRet.
      eapply HNRet.
      move/lfilledP in HContra.
      apply/lfilledP.
      instantiate (1 := LH_handler [::] hs lh [::]).
      rewrite - (cat0s [:: AI_handler hs es]).
      rewrite - (cats0 [:: AI_handler hs es]).
      constructor => //.
      exact HContra.
    }
    { move => tf h vcs n HLF.
      eapply HCallHost.
      unfold first_instr => /=.
      unfold first_instr in HLF.
      rewrite HLF.
      done. } 
    + (* Terminal *)
      simpl in H.
(*      apply terminal_form_v_e in H.
      unfold terminal_form in H. *)
      destruct H as [H | [H | [H | H]]].
      * (* Const *)
        right.
        exists s, f, es.
        apply r_simple.
        by apply rs_handler_const.
      * (* AI_trap *)
        right. subst.
        exists s, f, [::AI_trap].
        apply r_simple.
        by apply rs_handler_trap.
      * (* Throw_ref *)
        destruct H as (hh & a & exn & Hexn & Hfill).
        destruct (firstx_exception hs (f_inst f) (e_tag exn)) eqn:Hfirst.
        -- right. 
           repeat eexists.
           eapply r_throw_ref.
           exact Hexn. exact Hfill. exact Hfirst.
        -- right.
           repeat eexists.
           eapply r_throw_ref_ref.
           exact Hexn. exact Hfill. exact Hfirst.
        -- left. right. right. left.
           exists (HH_handler [::] hs hh [::]), a, exn.
           split => //.
           apply/hfilledP.
           rewrite - (cat0s [:: AI_handler _ _]) - (cats0 [:: AI_handler _ _]).
           constructor. done. done.
           apply/hfilledP. done.
      * (* Suspend *)
        destruct H as (i & hh & Hfill).
        left. right. right. right.
        exists i, (HH_handler [::] hs hh [::]).
        apply/hfilledP.
        rewrite - (cat0s [:: AI_handler _ _]) - (cats0 [:: AI_handler _ _]).
        constructor. done. done.
        apply/hfilledP. done.


    + (* reduce *)
      destruct H as [s' [f' [es' HReduce]]].
      right.
      simpl in HReduce.
      exists s', f', [::AI_handler hs es'].
      eapply r_label; eauto.
      instantiate (1 := LH_handler [::] hs (LH_base [::] [::]) [::]).
      instantiate (1 := 0).
      unfold lfilled, lfill => //=.
      by rewrite List.app_nil_r.
      unfold lfilled, lfill => //=.
      by rewrite List.app_nil_r.



    
  - (* Invoke *)
    move => s a C cl tf HNth HType.
    move => f C' vcs ts1 ts2 lab ret ts HTF Hts HContext HInst HConstType HST HBI_brDepth HNRet HNCallhost.
    subst.
    destruct cl.
    + (* Native *)
      right. destruct f0.
      simpl in HTF. inversion HTF; subst.
      exists s, f, [:: AI_local (length ts2) (Build_frame (vcs ++ default_vals l) i) [::AI_basic (BI_block (Tf [::] ts2) l0)]].
      eapply r_invoke_native; eauto.
      do 2 rewrite length_is_size.
      rewrite - (size_map Some ts1) - HConstType size_map => //.
    + (* Host *)
      right. simpl in HTF. inversion HTF; subst.
      exists s, f, [:: AI_call_host (Tf ts1 ts2) h vcs].
      eapply r_invoke_host; eauto.
      repeat rewrite length_is_size.
      by rewrite - (size_map Some ts1) - HConstType size_map.
  - (* AI_label *)
    move => s C e0s es ts t2s n HType1 IHHType1 HType2 IHHType2 HLength.
    move => f C' vcs ts1 ts2 lab ret ts0 HTF Hts0 HContext HInst HConstType HST HBI_brDepth HNRet HCallHost.
    inversion HTF; subst.
    destruct vcs => //. 
    rewrite upd_label_overwrite in HType2. simpl in HType2.
    destruct (br_reduce_decidable es) as [HEMT | HEMF].
    { unfold br_reduce in HEMT.
      destruct HEMT as [n [lh HLF]].
      right. 
      assert (LF : lfilled n lh [::AI_basic (BI_br (n+0))] es); first by rewrite addn0.
      eapply br_reduce_extract_vs in LF => //; eauto.
      destruct LF as [cs [lh' [HConst [HLF2 HLength]]]].
      rewrite addn0 in HLF2.
      repeat eexists.
      apply r_simple.
      eapply rs_br; eauto.
    }
    edestruct IHHType2; eauto.
(*    { rewrite upd_label_overwrite. simpl. eauto. } *)
    { unfold br_reduce in HEMF.
      move => n lh k HLF.
      assert (Inf : k < n.+1).
      { eapply HBI_brDepth.
      move/lfilledP in HLF.
      apply/lfilledP.
      assert (LF : lfilledInd (n.+1) (LH_rec [::] (length ts) e0s lh [::]) [::AI_basic (BI_br k)] ([::] ++ [::AI_label (length ts) e0s es] ++ [::]));
        first by apply LfilledRec.
      rewrite cats0 in LF. simpl in LF.
      by apply LF. }
      rewrite ltnS in Inf.
      rewrite leq_eqVlt in Inf.
      remove_bools_options => //.
      subst.
      exfalso.
      apply HEMF. repeat eexists. by apply HLF.
    }
    { unfold not_lf_return.
      move => n lh HContra.
      unfold not_lf_return in HNRet.
      eapply HNRet.
      move/lfilledP in HContra.
      apply/lfilledP.
      assert (LF : lfilledInd (n.+1) (LH_rec [::] (length ts) e0s lh [::]) [::AI_basic BI_return] ([::] ++ [::AI_label (length ts) e0s es] ++ [::]));
        first by apply LfilledRec.
      by apply LF.
    }
(*    { unfold not_lf_throw_ref.
      move => n lh HContra.
      unfold not_lf_throw_ref in HNThr.
      eapply HNThr.
      move/lfilledP in HContra.
      apply/lfilledP.
      assert (LF: lfilledInd (n.+1) (LH_rec [::] (length ts) e0s lh [::]) [::AI_basic BI_throw_ref] ([::] ++ [::AI_label (length ts) e0s es] ++ [::]));
        first by apply LfilledRec.
      by apply LF.
    }
    { unfold not_lf_suspend.
      move => n i lh HContra.
      unfold not_lf_suspend in HNSus.
      eapply HNSus.
      move/lfilledP in HContra.
      apply/lfilledP.
      assert (LF: lfilledInd (n.+1) (LH_rec [::] (length ts) e0s lh [::]) [::AI_basic (BI_suspend i)] ([::] ++ [::AI_label (length ts) e0s es] ++ [::]));
        first by apply LfilledRec.
      by apply LF.
    } *)
    { move => tf h vcs n HLF.
      eapply HCallHost.
      unfold first_instr => /=.
      unfold first_instr in HLF.
      rewrite HLF.
      done. } 
    + (* Terminal *)
(*      apply terminal_form_v_e in H.
      unfold terminal_form in H. *)
      destruct H as [H | [H | [H | H]]].
      * (* Const *)
        right.
        exists s, f, es.
        apply r_simple.
        by apply rs_label_const.
      * (* AI_trap *)
        right. simpl in H. subst.
        exists s, f, [::AI_trap].
        apply r_simple.
        by apply rs_label_trap.
      * destruct H as (hh & a & exn & Hexn & Hfill).
        left. right. right. left.
        exists (HH_label [::] (length ts) e0s hh [::]), a, exn.
        split => //.
        unfold hfilled, hfill; fold hfill.
        simpl.
        unfold hfilled in Hfill.
        destruct (hfill _ _ _) => //.
        move/eqP in Hfill. subst. done.
      * destruct H as (i & hh & Hfill).
        left. right. right. right.
        exists i, (HH_label [::] (length ts) e0s hh [::]).
        unfold hfilled, hfill; fold hfill.
        simpl. unfold hfilled in Hfill.
        destruct (hfill _ _ _) => //.
        move/eqP in Hfill. by subst.
    + (* reduce *)
      destruct H as [s' [f' [es' HReduce]]].
      right.
      simpl in HReduce.
      exists s', f', [::AI_label (length ts) e0s es'].
      by eapply r_label; eauto; apply label_lfilled1.
  - move => s C t1s t2s h vs Hlen f C' vcs ts1 ts2 lab ret ts HTF Hts HC HType Hts1 HSType HBr HRet HCallHost.
    inversion HTF ; subst.
    destruct vcs => //. 
    left.
    exfalso. eapply HCallHost.
    unfold first_instr => /=.
    done.
  - (* s_typing *)
    move => s f es rs ts C C0 HFT HContext HType IHHType HRetType HST HBI_brDepth HNRet HCallHost.
    inversion HFT.
    subst.
    edestruct IHHType; eauto.
    { apply forall_values_type in H1.
      instantiate (1 := tvs).
      apply Const_list_typing in H1 as (tslocs & Htslocs & -> & _).
      exact Htslocs. }
    { (* Context *)
      assert (E : tc_local C1 = [::]).
      { by eapply inst_t_context_local_empty; eauto. }
      rewrite E. simpl.
      by fold_upd_context. }
    { by instantiate (1 := [::]). }
    + left. split; first exact H0.
      intros Hes.
      apply const_es_exists in Hes as [vs ->].
      apply Const_list_typing in HType as (ts' & Hts' & -> & _).
      repeat rewrite length_is_size. simpl.
      rewrite v_to_e_size.
      rewrite - (size_map Some ts') - Hts' size_map => //. 
    + (* reduce *)
      simpl in H0. right.  by eauto.
  - done.
A dmitted.
*) *)

Lemma hfilled_reduce x hh es LI es' LI' s f s':
  (forall f, reduce s f es s' f es') ->
  hfilled x hh es LI ->
  hfilled x hh es' LI' ->
  reduce s f LI s' f LI'.
Proof.
  intros Hred HLI HLI'.
  move/hfilledP in HLI.
  move/hfilledP in HLI'.
  generalize dependent LI. generalize dependent LI'.
  generalize dependent f.
  induction hh; intros f0 LI' HLI' LI HLI.
  all: inversion HLI; inversion HLI'; subst.
  1,2,4,5: eapply r_label.
  (* all: try apply/lfilledP. *)
  apply Hred.
  instantiate (1 := LH_base l l0).
  instantiate (1 := 0).
  1-2: apply/lfilledP.
  1-2: constructor => //.
  1,4,7: instantiate (1 := LI1).
  1-3: instantiate (1 := LI0).
  1-3: by apply IHhh.
  instantiate (1 := LH_rec l n l0 (LH_base [::] [::]) l1).
  instantiate (1 := 1).
  3: instantiate (1 := LH_handler l l0 (LH_base [::] [::]) l1).
  3: instantiate (1 := 0).
  5: instantiate (1 := LH_prompt l l0 l1 (LH_base [::] [::]) l2).
  5: instantiate (1 := 0).
  1-6: unfold lfilled, lfill => //=.
  1-6: assert (const_list l) as H; [done | rewrite H].
  1-6: by rewrite List.app_nil_r.
  eapply r_label.
  instantiate (1 := [::AI_local n f LI1]).
  instantiate (1 := [::AI_local n f LI0]).
  2: instantiate (1 := LH_base l l0).
  2: instantiate (1 := 0).
  2-3: apply/lfilledP.
  2-3: constructor => //.
  apply r_local.
  apply IHhh => //.
Qed. 
  
Lemma hfilled_no_var x hh es LI:
  hfilled x hh es LI ->
  hfilled No_var hh es LI.
Proof.
  intros H.
  apply/hfilledP.
  move/hfilledP in H.
  induction H; constructor => //.
Qed. 
  

Lemma t_progress_e: forall s C es tf,
    e_typing s C es tf ->
    
    (forall C' f vcs ts1 ts2 lab ret ts,
        tf = Tf ts1 ts2 ->
        map (typeof s) (f_locs f) = map Some ts ->
        C = (upd_label (upd_local_return C' ts ret) lab) ->
        inst_typing s f.(f_inst) C' ->
        map (typeof s) vcs = map Some ts1 ->
        store_typing s ->
        (forall n lh k, lfilled n lh [::AI_basic (BI_br k)] es -> k < n) ->
        (forall n, not_lf_return es n) ->
        (forall tf h vcs n, first_instr es = Some (AI_call_host tf h vcs,n) -> False) ->
        terminal_form (v_to_e_list vcs ++ es) \/
          exists s' f' es', reduce s f (v_to_e_list vcs ++ es) s' f' es')
    /\
      (forall f vcs ts1 ts2,
          tf = Tf ts1 ts2 ->
          upd_label C [::] = empty_context ->
          map (typeof s) vcs = map Some ts1 ->
          store_typing s ->
          (forall n lh k, lfilled n lh [::AI_basic (BI_br k)] es -> k < n) ->
          (forall n, not_lf_return es n) ->
          (forall tf h vcs n, first_instr es = Some (AI_call_host tf h vcs,n) -> False) ->
          terminal_form (v_to_e_list vcs ++ es) \/
            exists s' f' es', reduce s f (v_to_e_list vcs ++ es) s' f' es')
.
Proof.
  (* e_typing *)
  move => s C es tf HType.
  apply e_typing_ind' with 
    (P := fun s C es tf (_ : e_typing s C es tf) =>
            (forall C' f vcs ts1 ts2 lab ret ts,
                tf = Tf ts1 ts2 ->
                map (typeof s) (f_locs f) = map Some ts ->
                C = (upd_label (upd_local_return C' ts ret) lab) ->
                inst_typing s f.(f_inst) C' ->
                map (typeof s) vcs = map Some ts1 ->
                store_typing s ->
                (forall n lh k, lfilled n lh [::AI_basic (BI_br k)] es -> k < n) ->
                (forall n, not_lf_return es n) ->
                (forall tf h vcs n, first_instr es = Some (AI_call_host tf h vcs,n) -> False) ->
                terminal_form (v_to_e_list vcs ++ es) \/
                  exists s' f' es', reduce s f (v_to_e_list vcs ++ es) s' f' es')
            /\
              (forall f vcs ts1 ts2,
                  tf = Tf ts1 ts2 ->
                  upd_label C [::] = empty_context ->
                  map (typeof s) vcs = map Some ts1 ->
                  store_typing s ->
                  (forall n lh k, lfilled n lh [::AI_basic (BI_br k)] es -> k < n) ->
                  (forall n, not_lf_return es n) ->
                  (forall tf h vcs n, first_instr es = Some (AI_call_host tf h vcs,n) -> False) ->
                  terminal_form (v_to_e_list vcs ++ es) \/
                    exists s' f' es', reduce s f (v_to_e_list vcs ++ es) s' f' es'))
    (P0 := fun s rs f es ts (_ : s_typing s rs f es ts) =>
             store_typing s ->
             (forall n lh k, lfilled n lh [::AI_basic (BI_br k)] es -> k < n) ->
             (forall n, not_lf_return es n) ->
             (forall tf h vcs n, first_instr es = Some (AI_call_host tf h vcs,n) -> False) ->
             terminal_form es /\
               (const_list es -> length es = length ts)
             (*              (const_list es /\ length es = length ts) \/
              es = [::AI_trap] *) \/
               exists s' f' es', reduce s f es s' f' es') ; try clear HType s C es tf.
  (*  apply e_typing_ind' with 
    (P := fun s C es tf (_ : e_typing s C es tf) => forall f C' vcs ts1 ts2 lab ret ts,
              tf = Tf ts1 ts2 ->
              map (typeof s) (f_locs f) = map Some ts ->
              C = (upd_label (upd_local_return C' ts ret) lab) ->
                 inst_typing s f.(f_inst) C' ->
              map (typeof s) vcs = map Some ts1 ->
              store_typing s ->
              (forall n lh k, lfilled n lh [::AI_basic (BI_br k)] es -> k < n) ->
              (forall n, not_lf_return es n) ->
              (forall tf h vcs n, first_instr es = Some (AI_call_host tf h vcs,n) -> False) ->
              terminal_form s (f_inst f) (v_to_e_list vcs ++ es) \/
              exists s' f' es', reduce s f (v_to_e_list vcs ++ es) s' f' es')
    (P0 := fun s rs f es ts (_ : s_typing s rs f es ts) =>
              store_typing s ->
              (forall n lh k, lfilled n lh [::AI_basic (BI_br k)] es -> k < n) ->
              (forall n, not_lf_return es n) ->
              (forall tf h vcs n, first_instr es = Some (AI_call_host tf h vcs,n) -> False) ->
              terminal_form s (f_inst f) es /\
                (const_list es -> length es = length ts)
(*              (const_list es /\ length es = length ts) \/
              es = [::AI_trap] *) \/
              exists s' f' es', reduce s f es s' f' es') ; try clear HType s C es tf. *)
  - (* AI_basic *)
    move => s C bes tf HType.
    split.
    + move => f C' vcs ts1 ts2 lab ret ts
               HTF Hts HContext HInst HConstType HST HBI_brDepth HNRet HCallhost.
      subst.
(*      destruct (lf_throw_ref_decidable (to_e_list bes)) as [([[[[bef vs] a] i] aft] & Hbef & Habs) | HNThr].
      { symmetry in Habs.
        apply map_is_cat in Habs as (befb & restb & -> & Hbefb & Hrestb).
        apply map_is_cat in Hrestb as (midb & aftb & -> & Hmidb & Haftb).
        destruct midb => //. 
        destruct midb => //.
        inversion Hmidb; subst b.
        apply composition_typing in HType as (ts0 & t1s' & t2s' & t3s & -> & -> & Hbefbt & Hrestt).
        apply composition_typing in Hrestt as (ts0' & t1s'' & t2s'' & t3s' & -> & -> & Hthrowt & Haftbt).
        apply Throw_ref_typing in Hthrowt as (ts' & ->).
        apply (ety_a s) in Hbefbt.
        unfold to_e_list in Hbefbt.
        rewrite Hbefb in Hbefbt.
        apply const_es_exists in Hbef as [vs ->].
        apply Const_list_typing in Hbefbt as (tsv & Htsv & Htypes & Hconst).
        destruct tsv.
        - destruct vs => //. destruct befb => //=.
          rewrite cats0 in Htypes; subst t1s'.
          repeat rewrite map_cat in HConstType.
          repeat rewrite catA in HConstType.
          apply typeof_append in HConstType as (v & Hvcs & Hfirsts & Hv).
          destruct v => //. destruct v => //.
          + destruct r => //. right.
            rewrite Hvcs.
            repeat eexists.
            rewrite -v_to_e_cat.
            rewrite (separate1 (AI_basic BI_throw_ref)).
            rewrite -cat_app. rewrite -catA. rewrite (catA _ [:: _] (to_e_list aftb)).
            eapply r_label.
            2:{
              instantiate (3 := 0).
              instantiate (2 := LH_base (v_to_e_list _) _).
              unfold lfilled, lfill.
              rewrite v_to_e_is_const_list. done. }
            2:{ unfold lfilled, lfill.
                rewrite v_to_e_is_const_list.
                done. }
            constructor. constructor.
          + simpl in Hv. destruct (List.nth_error _ f0) => //.
          + simpl in Hv. destruct (List.nth_error _ f0) => //.
          + simpl in Hv. destruct (List.nth_error _ e) eqn:He => //.
            rewrite Hvcs. left. right. right. left.
            eexists (HH_base (v_to_e_list _) _), _, e, _.
            unfold hfilled, hfill.
            rewrite v_to_e_is_const_list.
            unfold v_to_e_list. rewrite map_cat.
            simpl. repeat rewrite - catA.
            simpl. done.
        - rewrite to_e_list_cat.
          unfold to_e_list. rewrite Hbefb.
          destruct (list_last v tsv) as (v' & tsv' & Htsv').
          rewrite Htsv' in Htypes Htsv.
          do 2 rewrite catA in Htypes.
          apply concat_cancel_last in Htypes as [Htypes <-].
          rewrite map_cat in Htsv.
          apply typeof_append in Htsv as (v' & Hvs & Htsvt' & Hv').
          destruct v' => //.
          destruct v0 => //.
          + destruct r => //.
            rewrite Hvs. right. repeat eexists.
            rewrite -v_to_e_cat.
            simpl. rewrite (separate1 (AI_basic BI_throw_ref)).
            rewrite -cat_app. rewrite -catA. rewrite (catA _ [:: _] (to_e_list aftb)).
            simpl. rewrite catA. rewrite v_to_e_cat. rewrite separate2.
            eapply r_label.
            2:{ instantiate (3 := 0). instantiate (2 := LH_base (v_to_e_list _) _).
                unfold lfilled, lfill. rewrite v_to_e_is_const_list. done. }
            2:{ unfold lfilled, lfill. rewrite v_to_e_is_const_list. done. }
            constructor. constructor.
          + simpl in Hv'. destruct (List.nth_error _ f0) => //.
          + simpl in Hv'. destruct (List.nth_error _ f0) => //.
          + simpl in Hv'. destruct (List.nth_error _ e) eqn:He => //.
            rewrite Hvs. left. right. right. left.
            eexists (HH_base (v_to_e_list _) _), e, _.
            unfold hfilled, hfill. rewrite v_to_e_is_const_list.
            unfold v_to_e_list. rewrite map_cat. simpl. repeat rewrite - catA.
            simpl. rewrite catA. rewrite - map_cat. done. }  *)
      
      eapply t_progress_be in HType; try instantiate (1 := vs) in HType; try by eauto.
      destruct HType as [HType | [s' [vs' [es' HType]]]].
      * left.
        unfold terminal_form; left.
        apply const_list_concat => //. by apply v_to_e_is_const_list.
      * right. 
        repeat eexists. by apply HType.
      * unfold not_lf_br. move => k lh HContra.
        by apply HBI_brDepth in HContra.
      * intros bef vs a i aft [Hbef Habs].
        symmetry in Habs.
        apply map_is_cat in Habs as (befb & restb & -> & Hbefb & Hrestb).
        apply map_is_cat in Hrestb as (midb & aftb & -> & Hmidb & Haftb).
        destruct midb => //. 
    + move => f vcs ts1 ts2 
               HTF HContext HConstType HST HBI_brDepth HNRet HCallhost.
      subst.
(*      destruct (lf_throw_ref_decidable (to_e_list bes)) as [([[[[bef vs] a] i] aft] & Hbef & Habs) | HNThr].
      { symmetry in Habs.
        apply map_is_cat in Habs as (befb & restb & -> & Hbefb & Hrestb).
        apply map_is_cat in Hrestb as (midb & aftb & -> & Hmidb & Haftb).
        destruct midb => // .
        destruct midb => //.
        inversion Hmidb; subst b.
        apply composition_typing in HType as (ts0 & t1s' & t2s' & t3s & -> & -> & Hbefbt & Hrestt).
        apply composition_typing in Hrestt as (ts0' & t1s'' & t2s'' & t3s' & -> & -> & Hthrowt & Haftbt).
        apply Throw_ref_typing in Hthrowt as (ts' & ->).
        apply (ety_a s) in Hbefbt.
        unfold to_e_list in Hbefbt.
        rewrite Hbefb in Hbefbt.
        apply const_es_exists in Hbef as [vs ->].
        apply Const_list_typing in Hbefbt as (tsv & Htsv & Htypes & Hconst).
        destruct tsv.
        - destruct vs => //. destruct befb => //=.
          rewrite cats0 in Htypes; subst t1s'.
          repeat rewrite map_cat in HConstType.
          repeat rewrite catA in HConstType.
          apply typeof_append in HConstType as (v & Hvcs & Hfirsts & Hv).
          destruct v => //. destruct v => //.
          + destruct r => //. right.
            rewrite Hvcs.
            repeat eexists.
            rewrite -v_to_e_cat.
            rewrite (separate1 (AI_basic BI_throw_ref)).
            rewrite -cat_app. rewrite -catA. rewrite (catA _ [:: _] (to_e_list aftb)).
            eapply r_label.
            2:{
              instantiate (3 := 0).
              instantiate (2 := LH_base (v_to_e_list _) _).
              unfold lfilled, lfill.
              rewrite v_to_e_is_const_list. done. }
            2:{ unfold lfilled, lfill.
                rewrite v_to_e_is_const_list.
                done. }
            constructor. constructor.
          + simpl in Hv. destruct (List.nth_error _ f0) => //.
          + simpl in Hv. destruct (List.nth_error _ f0) => //.
          + simpl in Hv. destruct (List.nth_error _ e) eqn:He => //.
            rewrite Hvcs. left. right. right. left.
            eexists (HH_base (v_to_e_list _) _), e, _.
            unfold hfilled, hfill. rewrite v_to_e_is_const_list.
            unfold v_to_e_list. rewrite map_cat.
            simpl. repeat rewrite - catA.
            simpl. done.
        - rewrite to_e_list_cat.
          unfold to_e_list. rewrite Hbefb.
          destruct (list_last v tsv) as (v' & tsv' & Htsv').
          rewrite Htsv' in Htypes Htsv.
          do 2 rewrite catA in Htypes.
          apply concat_cancel_last in Htypes as [Htypes <-].
          rewrite map_cat in Htsv.
          apply typeof_append in Htsv as (v' & Hvs & Htsvt' & Hv').
          destruct v' => //.
          destruct v0 => //.
          + destruct r => //.
            rewrite Hvs. right. repeat eexists.
            rewrite -v_to_e_cat.
            simpl. rewrite (separate1 (AI_basic BI_throw_ref)).
            rewrite -cat_app. rewrite -catA. rewrite (catA _ [:: _] (to_e_list aftb)).
            simpl. rewrite catA. rewrite v_to_e_cat. rewrite separate2.
            eapply r_label.
            2:{ instantiate (3 := 0). instantiate (2 := LH_base (v_to_e_list _) _).
                unfold lfilled, lfill. rewrite v_to_e_is_const_list. done. }
            2:{ unfold lfilled, lfill. rewrite v_to_e_is_const_list. done. }
            constructor. constructor.
          + simpl in Hv'. destruct (List.nth_error _ f0) => //.
          + simpl in Hv'. destruct (List.nth_error _ f0) => //.
          + simpl in Hv'. destruct (List.nth_error _ e) eqn:He => //.
            rewrite Hvs. left. right. right. left.
            eexists (HH_base (v_to_e_list _) _), e, _.
            unfold hfilled, hfill. rewrite v_to_e_is_const_list.
            unfold v_to_e_list. rewrite map_cat. simpl. repeat rewrite - catA.
            simpl. rewrite catA. rewrite - map_cat. done. } *)
      
      eapply t_progress_be_empty in HType; try instantiate (1 := vs) in HType; try by eauto.
      destruct HType as [HType | [s' [vs' [es' HType]]]].
      * left.
        unfold terminal_form; left.
        apply const_list_concat => //. by apply v_to_e_is_const_list.
      * right. 
        repeat eexists. by apply HType.
      * unfold not_lf_br. move => k lh HContra.
        by apply HBI_brDepth in HContra.
      * intros bef vs a i aft [Hbef Habs].
        symmetry in Habs.
        apply map_is_cat in Habs as (befb & restb & -> & Hbefb & Hrestb).
        apply map_is_cat in Hrestb as (midb & aftb & -> & Hmidb & Haftb).
        destruct midb => // .

  - (* Composition *)
    move => s C es e t1s t2s t3s HType1 IHHType1 HType2 IHHType2.
    split.
    { move => C' f vcs ts1 ts2 lab ret ts HTF Hts HContext HInst HConstType HST HBI_brDepth HNRet HCallHost.
      inversion HTF; subst.
      edestruct IHHType1 as [IH _]; eauto.
      edestruct IH; eauto.
      + move => n lh k HLF.
        eapply lf_composition in HLF.
        destruct HLF as [lh' HLF].
        instantiate (1 := [::e]) in HLF.
        eapply HBI_brDepth.
        by apply HLF. 
      + move => n.
        eapply nlfret_right. by apply HNRet.
      + move => tf h vcs0 n HLF.
        eapply HCallHost.
        eapply first_instr_app.
        exact HLF. 
      + (* Terminal *)
        unfold terminal_form in H. destruct H as [H | [H | [H | [H | H]]]].
        * (* Const *)
          apply const_list_split in H. destruct H as [HC1 HC2].
          apply const_es_exists in HC2.
          destruct HC2 as [esv HC2]. subst.
          apply Const_list_typing in HType1 as (tsesv & Htsesv & -> & Hconst).
          edestruct IHHType2 as [IH' _]; eauto.
          edestruct IH'; eauto.
          -- instantiate (1 := vcs ++ esv).
             do 2 rewrite map_cat.
             rewrite Htsesv HConstType.
             done.
          -- move => n lh k HLF.
             eapply lf_composition_left in HLF.
             instantiate (1 := v_to_e_list esv) in HLF.
             destruct HLF as [lh' HLF].
             eapply HBI_brDepth; eauto.
             by apply v_to_e_is_const_list. 
          -- move => n.
             eapply nlfret_left.
             instantiate (1 := v_to_e_list esv); first by apply v_to_e_is_const_list.
             by apply HNRet.
          -- move => tf h vcs0 n HLF.
             eapply HCallHost.
             eapply starts_with_lfilled.
             exact HLF.
             instantiate (2 := 0).
             instantiate (1 := LH_base (v_to_e_list esv) [::]).
             unfold lfilled, lfill => /=.
             rewrite v_to_e_is_const_list.
             done. 
          -- (* Terminal *)
            left. rewrite catA v_to_e_cat. done.
          -- (* reduce *)
            rewrite -v_to_e_cat in H.
            rewrite -catA in H.
            right.
            by eapply H.
        * (* AI_trap *)
          destruct vcs => //=.
          2:{ simpl in H. destruct v => //. destruct v => //. }
          destruct es => //=; destruct es => //=.
          simpl in H. inversion H. subst.
          right.
          exists s, f, [::AI_trap].
          apply r_simple.
          eapply rs_trap => //.
          instantiate (1 := (LH_base [::] [::e])).
          apply/lfilledP.
          by apply LfilledBase => //=; apply v_to_e_is_const_list.
        * destruct H as (hh & vs & a & t & Hfill).
          left. right. right. left.
          eexists (hholed_append hh [:: e]), vs, a, _.
          rewrite catA.
          apply hfilled_append. exact Hfill. 
        * destruct H as (vs & i & hh & Hfill).
          left. right. right. right. left.
          exists vs, i, (hholed_append hh [:: e]).
          rewrite catA. apply hfilled_append => //.
        * destruct H as (vs & k & tf & i & hh & Hfill).
          left. right. right. right. right.
          exists vs, k, tf, i, (hholed_append hh [:: e]).
          rewrite catA. apply hfilled_append => //. 
          
      + (* reduce *)
        destruct H as [s' [f' [es' HReduce]]].
        right.
        exists s', f', (es' ++ [::e]).
        eapply r_label; eauto; try apply/lfilledP.
        * assert (LF : lfilledInd 0 (LH_base [::] [::e]) (v_to_e_list vcs ++ es) ([::] ++ (v_to_e_list vcs ++ es) ++ [::e]));
            first by apply LfilledBase.
          simpl in LF. rewrite -catA in LF. by apply LF.
        * by apply LfilledBase. }
    move => f vcs ts1 ts2 HTF HContext HConstType HST HBI_brDepth HNRet HCallHost.
    inversion HTF; subst.
    edestruct IHHType1 as [_ IH]; eauto.
    edestruct IH; eauto.
    + move => n lh k HLF.
      eapply lf_composition in HLF.
      destruct HLF as [lh' HLF].
      instantiate (1 := [::e]) in HLF.
      eapply HBI_brDepth.
      by apply HLF. 
    + move => n.
      eapply nlfret_right. by apply HNRet.
    + move => tf h vcs0 n HLF.
      eapply HCallHost.
      eapply first_instr_app.
      exact HLF. 
    + (* Terminal *)
      unfold terminal_form in H. destruct H as [H | [H | [H | [H | H]]]].
      * (* Const *)
        apply const_list_split in H. destruct H as [HC1 HC2].
        apply const_es_exists in HC2.
        destruct HC2 as [esv HC2]. subst.
        apply Const_list_typing in HType1 as (tsesv & Htsesv & -> & Hconst).
        edestruct IHHType2 as [_ IH']; eauto.
        edestruct IH'; eauto.
        -- instantiate (1 := vcs ++ esv).
           do 2 rewrite map_cat.
           rewrite Htsesv HConstType.
           done.
        -- move => n lh k HLF.
           eapply lf_composition_left in HLF.
           instantiate (1 := v_to_e_list esv) in HLF.
           destruct HLF as [lh' HLF].
           eapply HBI_brDepth; eauto.
           by apply v_to_e_is_const_list. 
        -- move => n.
           eapply nlfret_left.
           instantiate (1 := v_to_e_list esv); first by apply v_to_e_is_const_list.
           by apply HNRet.
        -- move => tf h vcs0 n HLF.
           eapply HCallHost.
           eapply starts_with_lfilled.
           exact HLF.
           instantiate (2 := 0).
           instantiate (1 := LH_base (v_to_e_list esv) [::]).
           unfold lfilled, lfill => /=.
           rewrite v_to_e_is_const_list.
           done. 
        -- (* Terminal *)
          left. rewrite catA v_to_e_cat. exact H. 
        -- (* reduce *)
          rewrite -v_to_e_cat in H.
          rewrite -catA in H.
          right.
          by eapply H.
      * (* AI_trap *)
        destruct vcs => //=.
        2:{ simpl in H. destruct v => //. destruct v => //. }
        destruct es => //=; destruct es => //=.
        simpl in H. inversion H. subst.
        right.
        exists s, f, [::AI_trap].
        apply r_simple.
        eapply rs_trap => //.
        instantiate (1 := (LH_base [::] [::e])).
        apply/lfilledP.
        by apply LfilledBase => //=; apply v_to_e_is_const_list.
      * destruct H as (hh & vs & a & t & Hfill).
        left. right. right. left.
        exists (hholed_append hh [:: e]), vs, a, t.
        rewrite catA.
        apply hfilled_append. exact Hfill. 
      * destruct H as (n & i & hh & Hfill).
        left. right. right. right. left.
        exists n, i, (hholed_append hh [:: e]).
        rewrite catA. apply hfilled_append => //.
      * destruct H as (n & k & tf & i & hh & Hfill).
        left. right. right. right. right.
        exists n, k, tf, i, (hholed_append hh [:: e]).
        rewrite catA. apply hfilled_append => //. 
        
    + (* reduce *)
      destruct H as [s' [f' [es' HReduce]]].
      right.
      exists s', f', (es' ++ [::e]).
      eapply r_label; eauto; try apply/lfilledP.
      * assert (LF : lfilledInd 0 (LH_base [::] [::e]) (v_to_e_list vcs ++ es) ([::] ++ (v_to_e_list vcs ++ es) ++ [::e]));
          first by apply LfilledBase.
        simpl in LF. rewrite -catA in LF. by apply LF.
      * by apply LfilledBase. 
        
  - (* Weakening *)
    move => s C es ts t1s t2s HType IHHType.
    split.
    { move => C' f vcs ts1 ts2 lab ret ts0 HTF Hts0 HContext HInst HConstType HST HBI_brDepth HNRet HCallHost.
      inversion HTF; subst.
      rewrite map_cat in HConstType.
      apply cat_split in HConstType as [HCT1 HCT2].
      rewrite - map_take in HCT1.
      rewrite - map_drop in HCT2. 
      assert (Evcs : vcs = take (size ts) vcs ++ drop (size ts) vcs).
      { symmetry. by apply cat_take_drop. }
      rewrite Evcs. rewrite - v_to_e_cat.
      edestruct IHHType as [IH _]; eauto.
      edestruct IH; eauto.
      + (* Terminal *)
        unfold terminal_form in H.
        destruct H as [H | [H | [H | [H | H]]]] => //=.
        * (* Const *)
          left. rewrite size_map in H. unfold terminal_form. left.
          rewrite -catA. apply const_list_concat => //.
          by apply v_to_e_is_const_list.
        * (* AI_trap *)
          apply v_e_trap in H; last by apply v_to_e_is_const_list.
          destruct H. rewrite size_map in H. subst.
          rewrite H.
          destruct (drop (size ts) vcs) eqn:HDrop => //=.
          clear H. rewrite cats0 in Evcs. rewrite -Evcs.
          rewrite cats0.
          destruct vcs => //.
          -- left. by apply terminal_trap.
          -- right.
             exists s, f, [::AI_trap].
             apply r_simple.
             apply reduce_trap_left => //.
             by apply v_to_e_is_const_list.
        * destruct H as (hh & vs & a & t & Hfill).
          left. right. right. left.
          eexists (hholed_prepend hh _), vs, a, t. 
          rewrite -catA.
          apply hfilled_prepend.
          split; first by apply v_to_e_is_const_list.
          rewrite size_map in Hfill. done.
        * destruct H as (n & i & hh & Hfill).
          left. right. right. right. left.
          eexists n, i, (hholed_prepend hh _).
          rewrite -catA.
          apply hfilled_prepend.
          split; first by apply v_to_e_is_const_list.
          rewrite size_map in Hfill. done.
        * destruct H as (n & k & tf & i & hh & Hfill).
          left. right. right. right. right.
          eexists n, k, tf, i, (hholed_prepend hh _).
          rewrite -catA.
          apply hfilled_prepend.
          split; first by apply v_to_e_is_const_list.
          rewrite size_map in Hfill. done.
      + (* reduce *)
        destruct H as [s' [f' [es' HReduce]]].
        right.
        exists s', f', (v_to_e_list (take (size ts) vcs) ++ es').
        rewrite -catA. rewrite size_map in HReduce.
        apply reduce_composition_left => //; first by apply v_to_e_is_const_list. }
    move => f vcs ts1 ts2 HTF HContext HConstType HST HBI_brDepth HNRet HCallHost.
    inversion HTF; subst.
    rewrite map_cat in HConstType.
    apply cat_split in HConstType as [HCT1 HCT2].
    rewrite - map_take in HCT1.
    rewrite - map_drop in HCT2. 
    assert (Evcs : vcs = take (size ts) vcs ++ drop (size ts) vcs).
    { symmetry. by apply cat_take_drop. }
    rewrite Evcs. rewrite - v_to_e_cat.
    edestruct IHHType as [_ IH]; eauto.
    edestruct IH; eauto.
    + (* Terminal *)
      unfold terminal_form in H.
      destruct H as [H | [H | [H | [H | H]]]] => //=.
      * (* Const *)
        left. rewrite size_map in H. unfold terminal_form. left.
        rewrite -catA. apply const_list_concat => //.
        by apply v_to_e_is_const_list.
      * (* AI_trap *)
        apply v_e_trap in H; last by apply v_to_e_is_const_list.
        destruct H. rewrite size_map in H. subst.
        rewrite H.
        destruct (drop (size ts) vcs) eqn:HDrop => //=.
        clear H. rewrite cats0 in Evcs. rewrite -Evcs.
        rewrite cats0.
        destruct vcs => //.
        -- left. by apply terminal_trap.
        -- right.
           exists s, f, [::AI_trap].
           apply r_simple.
           apply reduce_trap_left => //.
           by apply v_to_e_is_const_list.
      * destruct H as (hh & vs & a & t & Hfill).
        left. right. right. left.
        eexists (hholed_prepend hh _), vs, a, t.
        rewrite -catA.
        apply hfilled_prepend.
        split; first by apply v_to_e_is_const_list.
        rewrite size_map in Hfill. exact Hfill.
      * destruct H as (n & i & hh & Hfill).
        left. right. right. right. left.
        eexists n, i, (hholed_prepend hh _).
        rewrite -catA.
        apply hfilled_prepend.
        split; first by apply v_to_e_is_const_list.
        rewrite size_map in Hfill. done.
      * destruct H as (n & k & tf & i & hh & Hfill).
        left. right. right. right. right.
        eexists n, k, tf, i, (hholed_prepend hh _).
        rewrite -catA.
        apply hfilled_prepend.
        split; first by apply v_to_e_is_const_list.
        rewrite size_map in Hfill. done.
    + (* reduce *)
      destruct H as [s' [f' [es' HReduce]]].
      right.
      exists s', f', (v_to_e_list (take (size ts) vcs) ++ es').
      rewrite -catA. rewrite size_map in HReduce.
      apply reduce_composition_left => //;
                                        first by apply v_to_e_is_const_list.
      exact HReduce.
      
  - (* AI_trap *)
    intros s C tf.
    split. 
    { destruct vcs => //; first by left; apply terminal_trap.
      right.
      exists s, f, [::AI_trap].
      apply r_simple.
      apply reduce_trap_left => //.
      by apply v_to_e_is_const_list. }
    destruct vcs => //; first by left; apply terminal_trap.
    right.
    exists s, f, [::AI_trap].
    apply r_simple.
    apply reduce_trap_left => //.
    by apply v_to_e_is_const_list.
  - (* Local *)
    move => s C n f0 es ts HType IHHType HLength.
    split.
    { move => C' f vcs ts1 ts2 lab ret ts0 HTF Hts0 HContext HInst HConstType HST HBI_brDepth HNRet HCallHost.
      inversion HTF; subst; clear HTF.
      destruct vcs => //. 

      destruct (return_reduce_decidable es) as [HEMT | HEMF].
      { inversion HType; subst.
        unfold return_reduce in HEMT.
        destruct HEMT as [n [lh HLF]].
        eapply return_reduce_extract_vs in HLF; eauto.
        destruct HLF as [cs [lh' [HConst [HLF2 HLength]]]].
        right.
        repeat eexists.
        apply r_simple.
        eapply rs_return; eauto.
      }

      edestruct IHHType as [[[ Hconst | [ Htrap | [ Hthr | [Hsus | Hswitch]]]] Htypconst ]| Hreduce ]; eauto. 
      {
        move => n lh k HLF.
        by eapply s_typing_lf_br in HLF; eauto.
      }
      { unfold return_reduce in HEMF. unfold not_lf_return.
        move => n lh HContra.
        apply HEMF. by eauto.
      }
      { move => tf h vcs n HLF.  
        eapply HCallHost.
        unfold first_instr => /=.
        unfold first_instr in HLF.
        rewrite HLF.
        done. } 
      + (* Const *)
        right. exists s, f, es.
        apply r_simple.
        apply rs_local_const => //.
        specialize (Htypconst Hconst).
        apply const_es_exists in Hconst as [vs ->].
        done.

      + (* AI_trap *)
        subst.
        right. exists s, f, [::AI_trap].
        apply r_simple.
        by apply rs_local_trap.
      + (* throw_ref *)
        left. right. right. left.
        destruct Hthr as (hh & vs & a & t & Hfill).
        exists (HH_local [::] (length ts2) f0 hh [::]), vs, a, t.
        unfold hfilled, hfill; fold hfill. simpl.
        unfold hfilled in Hfill.
        destruct (hfill _ _ _) => //.
        move/eqP in Hfill. subst. done.
      + (* Suspend *)
        left. right. right. right. left.
        destruct Hsus as (n & i & hh & Hfill).
        exists n, i, (HH_local [::] (length ts2) f0 hh [::]).
        unfold hfilled, hfill; fold hfill. simpl.
        unfold hfilled in Hfill.
        destruct (hfill _ _ _) => //.
        move/eqP in Hfill. subst. done.
      + (* Switch *)
        left. right. right. right. right.
        destruct Hswitch as (n & k & tf & i & hh & Hfill).
        exists n, k, tf, i, (HH_local [::] (length ts2) f0 hh [::]).
        unfold hfilled, hfill; fold hfill. simpl.
        unfold hfilled in Hfill.
        destruct (hfill _ _ _) => //.
        move/eqP in Hfill. subst. done.
      + (* reduce *)
        destruct Hreduce as [s' [f0' [es' HReduce]]].
        right. exists s', f, [::AI_local (length ts2) f0' es'].
        by apply r_local; apply HReduce. }
    move => f vcs ts1 ts2 HTF HContext HConstType HST HBI_brDepth HNRet HCallHost.
    inversion HTF; subst; clear HTF.
    destruct vcs => //. 

    destruct (return_reduce_decidable es) as [HEMT | HEMF].
    { inversion HType; subst.
      unfold return_reduce in HEMT.
      destruct HEMT as [n [lh HLF]].
      eapply return_reduce_extract_vs in HLF; eauto.
      destruct HLF as [cs [lh' [HConst [HLF2 HLength]]]].
      right.
      repeat eexists.
      apply r_simple.
      eapply rs_return; eauto.
    }

    edestruct IHHType as [[[ Hconst | [ Htrap | [ Hthr | [Hsus | Hswitch]]]] Htypconst ]| Hreduce ]; eauto. 
    {
      move => n lh k HLF.
      by eapply s_typing_lf_br in HLF; eauto.
    }
    { unfold return_reduce in HEMF. unfold not_lf_return.
      move => n lh HContra.
      apply HEMF. by eauto.
    }
    { move => tf h vcs n HLF.  
      eapply HCallHost.
      unfold first_instr => /=.
      unfold first_instr in HLF.
      rewrite HLF.
      done. } 
    + (* Const *)
      right. exists s, f, es.
      apply r_simple.
      apply rs_local_const => //.
      specialize (Htypconst Hconst).
      apply const_es_exists in Hconst as [vs ->].
      done.

    + (* AI_trap *)
      subst.
      right. exists s, f, [::AI_trap].
      apply r_simple.
      by apply rs_local_trap.
    + (* throw_ref *)
      left. right. right. left.
      destruct Hthr as (hh & vs & a & t & Hfill).
      exists (HH_local [::] (length ts2) f0 hh [::]), vs, a, t.
      unfold hfilled, hfill; fold hfill. simpl.
      unfold hfilled in Hfill.
      destruct (hfill _ _ _) => //.
      move/eqP in Hfill. subst. done.
    + (* Suspend *)
      left. right. right. right. left.
      destruct Hsus as (n & i & hh & Hfill).
      exists n, i, (HH_local [::] (length ts2) f0 hh [::]).
      unfold hfilled, hfill; fold hfill. simpl.
      unfold hfilled in Hfill.
      destruct (hfill _ _ _) => //.
      move/eqP in Hfill. subst. done.
    + (* Switch *)
      left. right. right. right. right.
      destruct Hswitch as (n & k & tf & i & hh & Hfill).
      exists n, k, tf, i, (HH_local [::] (length ts2) f0 hh [::]).
      unfold hfilled, hfill; fold hfill. simpl.
      unfold hfilled in Hfill.
      destruct (hfill _ _ _) => //.
      move/eqP in Hfill. subst. done.
    + (* reduce *)
      destruct Hreduce as [s' [f0' [es' HReduce]]].
      right. exists s', f, [::AI_local (length ts2) f0' es'].
      by apply r_local; apply HReduce. 
  - (* Ref *)
    split.
    all: left.
    all: left.
    all: apply const_list_concat => //.
    all: apply v_to_e_is_const_list.
  - (* Ref_cont *)
    split.
    all: left.
    all: left.
    all: apply const_list_concat => //.
    all: apply v_to_e_is_const_list.
  - (* Ref_exn *)
    split.
    all: left.
    all: left.
    all: apply const_list_concat => //.
    all: apply v_to_e_is_const_list.
  - (* Suspend_desugared *)
    intros s C x n t1s t2s Htags Hn.
    split.
    { intros C' f vcs ts1 ts2 lab ret ts Htf Hlocs HC HIT Hvcs HST HBI_brDepth HNRet HCallHost.
      inversion Htf; subst ts1 ts2.
      left. right. right. right. left.
      exists n, (Mk_tagidx x), (HH_base (v_to_e_list vcs) [::]).
      apply/hfilledP. constructor.
      apply v_to_e_is_const_list. }
    intros f vcs ts1 ts2 Htf HC Hvcs HST HBI_brDepth HNRet HCallHost.
    inversion Htf; subst ts1 ts2.
    left. right. right. right. left.
    exists n, (Mk_tagidx x), (HH_base (v_to_e_list vcs) [::]).
    apply/hfilledP. constructor.
    apply v_to_e_is_const_list.
  - (* Switch_desugared *)
    intros s C vs k tf x ts t1s t2s cont Htags Htf Hk Hcont Hconst.
    split.
    + intros C' f vcs ts1 ts2 lab ret ts' Htfeq Hlocs HC HIT Hvcs HST HBI_brDepth HNRet HCallHost.
      left. right. right. right. right.
      exists vs, k, tf, (Mk_tagidx x), (HH_base (v_to_e_list vcs) [::]).
      apply/hfilledP.
      constructor. apply v_to_e_is_const_list.
    + intros f vcs ts1 ts2 Htfeq HC Hvcs HST HBI_brDepth HNRet HCallHost.
      left. right. right. right. right.
      exists vs, k, tf, (Mk_tagidx x), (HH_base (v_to_e_list vcs) [::]).
      apply/hfilledP. constructor.
      apply v_to_e_is_const_list.
  - (* Throw_ref_desugared *)
    intros s C vs a i tf exn Hexn Hi Hvs.
    split.
    + intros C' f vcs ts1 ts2 lab ret ts Htf Hlocs HC HIT Hvcs HST HBI_brDepth HNRet HCallHost.
      left. right. right. left.
      exists (HH_base (v_to_e_list vcs) [::]), vs, a, i.
      apply/hfilledP. constructor.
      apply v_to_e_is_const_list.
    + intros f vcs ts1 ts2 Htf HC Hvcs HST HBI_brDepth HNRet HCallHost.
      left. right. right. left.
      exists (HH_base (v_to_e_list vcs) [::]), vs, a, i.
      apply/hfilledP. constructor.
      apply v_to_e_is_const_list.
    
  - (* Prompt *)
    move => s C hs es ts Hclauses Hes IH.
    split.
    { move => C' f vcs ts1 ts2 lab ret ts0 HTF Hts0 HContext HInst HConstType HST HBI_brDepth HNRet HCallHost.
      inversion HTF; subst.
      destruct vcs => //.
      edestruct IH as [_ IH']; eauto.
      edestruct IH'; eauto.
      { 
      move => n lh k HLF.
      eapply HBI_brDepth.
      move/lfilledP in HLF.
      apply/lfilledP.
      instantiate (1 := LH_prompt [::] ts2 hs lh [::]).
      rewrite - (cat0s [:: AI_prompt _ _ _]) - (cats0 [:: AI_prompt _ _ _]).
      constructor => //. } 
    { unfold not_lf_return.
      move => n lh HContra.
      unfold not_lf_return in HNRet.
      eapply HNRet.
      move/lfilledP in HContra.
      apply/lfilledP.
      instantiate (1 := LH_prompt [::] ts2 hs lh [::]).
      rewrite - (cat0s [:: AI_prompt _ _ _]) - (cats0 [:: AI_prompt _ _ _]).
      constructor => //.
      exact HContra.
    } 
    { move => tf h vcs n HLF.
      eapply HCallHost.
      unfold first_instr => /=.
      unfold first_instr in HLF.
      rewrite HLF.
      done. } 
    + (* Terminal *)
      simpl. simpl in H. destruct H as [H | [H | [H | [H | H]]]].
      * (* Const *)
        right.
        exists s, f, es.
        apply r_simple.
        by apply rs_prompt_const.
      * (* AI_trap *)
        right. subst.
        exists s, f, [::AI_trap].
        apply r_simple.
        by apply rs_prompt_trap.
      * (* Throw_ref *)
        left. right. right. left.
        destruct H as (hh & vs & a & t & Hfill).
        exists (HH_prompt [::] ts2 hs hh [::]), vs, a, t.
        apply/hfilledP.
        rewrite -(cat0s [::AI_prompt _ _ _]) -(cats0 [::AI_prompt _ _ _]).
        constructor => //.
        apply/hfilledP. exact Hfill. 
      * (* Suspend *)
        destruct H as (n & i & hh & Hfill).
        destruct (firstx_continuation_suspend hs i) eqn:Hfirst.
        -- right.
           destruct i.
           eapply hfilled_typing in Hes as (tf' & C'' & Hsuspend & Hfillback).
           2: exact Hfill.
           destruct tf'.
           apply AI_suspend_desugared_typing in Hsuspend as (t1s' & t2s' & -> & Hn & Htags).
(*           eapply hfilled_suspend_values in Hes as (vs & hh' & t1s & t2s & Htags & Hn & Hconst & Hvs & Hfill');
             last exact Hfill. *)
           repeat eexists.
           eapply r_suspend.
           done.
           exact Htags.
           exact Hfirst.
           exact Hfill.
        -- left. right. right. right. left.
           exists n, i, (HH_prompt [::] ts2 hs hh [::]).
           apply/hfilledP.
           rewrite -(cat0s [::AI_prompt _ _ _]) - (cats0 [:: AI_prompt _ _ _]).
           constructor => //.
           apply/hfilledP. exact Hfill.
      * (* Switch *)
        destruct H as (vs & k & tf & i & hh & Hfill).
        destruct (firstx_continuation_switch hs i) eqn:Hfirst.
        -- right.
           destruct i.
           eapply hfilled_typing in Hes as ([??] & C'' & Hswitch & Hfillback).
           2: exact Hfill.
           apply AI_switch_desugared_typing in Hswitch as (ts & t1s' & t2s' & cont & Htags & Hconts & Hcont & Hvs & Htf & ->).
           destruct cont.
           ++ simpl in Hcont; subst f0.
              subst.
              destruct s.
              destruct HST as (_ & _ & _ & _ & Hcontt & _).
              rewrite List.Forall_forall in Hcontt.
              apply List.nth_error_In in Hconts as Hin.
              apply Hcontt in Hin.
              inversion Hin; subst.
              apply (hfilled_change (v_to_e_list vs ++ [:: AI_ref_cont (length s_conts)]) (y := No_var)) in H5 as [LI' HLI'].
              2: by left.
              repeat eexists.
              eapply r_switch.
              exact Hfirst.
              done.
              exact Hconts.
              exact Hfill.
              exact HLI'.
           ++ assert (hfilled No_var hh [::AI_switch_desugared vs k tf (Mk_tagidx n)] es) as Hfillnew.
              { eapply hfilled_no_var.
                exact Hfill. }
              apply (hfilled_change [::AI_trap] (y := No_var)) in Hfillnew as HLI'; last by left.
              destruct HLI' as [LI' HLI'].
              repeat eexists.
              eapply hfilled_reduce.
              2: instantiate (2 := HH_prompt [::] ts2 hs hh [::]).
              2: instantiate (2 := No_var).
              2-3: unfold hfilled, hfill; fold hfill.
              2-3: simpl.
              2: unfold hfilled in Hfillnew; destruct (hfill _ _ _) eqn:Hfilll => //; erewrite Hfilll.
              2: move/eqP in Hfillnew; subst => //.
              2: unfold hfilled in HLI'; destruct (hfill _ _ _) eqn:Hfilll => //; erewrite Hfilll.
              2: move/eqP in HLI'; subst => //.
              intros f1.
              eapply r_switch_failure.
              exact Hconts.
(*           ++ apply hfilled_no_var in Hfills.
              apply (hfilled_change [::AI_trap] (y := No_var)) in Hfills as HLI'; last by left.
              destruct HLI' as [LI' HLI'].
              repeat eexists.
              eapply hfilled_reduce.
              2: instantiate (2 := HH_prompt [::] ts2 hs hhs [::]).
              2: instantiate (2 := No_var).
              2-3: unfold hfilled, hfill; fold hfill.
              2-3: simpl.
              2: unfold hfilled in Hfills; destruct (hfill _ _ _) eqn:Hfilll => //; erewrite Hfilll.
              2: move/eqP in Hfills; subst => //.
              2: unfold hfilled in HLI'; destruct (hfill _ _ _) eqn:Hfilll => //; erewrite Hfilll.
              2: move/eqP in HLI'; subst => //.
              intros f1.
              constructor.
              constructor. *)
        -- left. right. right. right. right.
           exists vs, k, tf, i, (HH_prompt [::] ts2 hs hh [::]).
           apply/hfilledP.
           rewrite -(cat0s [::AI_prompt _ _ _]) - (cats0 [:: AI_prompt _ _ _]).
           constructor => //.
           apply/hfilledP. exact Hfill.
    + (* reduce *)
      destruct H as [s' [f' [es' HReduce]]].
      right.
      simpl in HReduce.
      exists s', f', [::AI_prompt ts2 hs es'].
      eapply r_label; eauto.
      instantiate (1 := LH_prompt [::] ts2 hs (LH_base [::] [::]) [::]).
      instantiate (1 := 0).
      unfold lfilled, lfill => //=.
      by rewrite List.app_nil_r.
      unfold lfilled, lfill => /=.
      by rewrite List.app_nil_r. }
    move => f vcs ts1 ts2 HTF HContext HConstType HST HBI_brDepth HNRet HCallHost.
    inversion HTF; subst.
    destruct vcs => //.
    edestruct IH as [_ IH']; eauto.
    edestruct IH'; eauto.
    { 
      move => n lh k HLF.
      eapply HBI_brDepth.
      move/lfilledP in HLF.
      apply/lfilledP.
      instantiate (1 := LH_prompt [::] ts2 hs lh [::]).
      rewrite - (cat0s [:: AI_prompt _ _ _]) - (cats0 [:: AI_prompt _ _ _]).
      constructor => //. } 
    { unfold not_lf_return.
      move => n lh HContra.
      unfold not_lf_return in HNRet.
      eapply HNRet.
      move/lfilledP in HContra.
      apply/lfilledP.
      instantiate (1 := LH_prompt [::] ts2 hs lh [::]).
      rewrite - (cat0s [:: AI_prompt _ _ _]) - (cats0 [:: AI_prompt _ _ _]).
      constructor => //.
      exact HContra.
    } 
    { move => tf h vcs n HLF.
      eapply HCallHost.
      unfold first_instr => /=.
      unfold first_instr in HLF.
      rewrite HLF.
      done. } 
    + (* Terminal *)
      simpl. simpl in H. destruct H as [H | [H | [H | [H | H]]]].
      * (* Const *)
        right.
        exists s, f, es.
        apply r_simple.
        by apply rs_prompt_const.
      * (* AI_trap *)
        right. subst.
        exists s, f, [::AI_trap].
        apply r_simple.
        by apply rs_prompt_trap.
      * (* Throw_ref *)
        left. right. right. left.
        destruct H as (hh & vs & a & t & Hfill).
        exists (HH_prompt [::] ts2 hs hh [::]), vs, a, t.
        apply/hfilledP.
        rewrite -(cat0s [::AI_prompt _ _ _]) -(cats0 [::AI_prompt _ _ _]).
        constructor => //.
        apply/hfilledP. exact Hfill. 
      * (* Suspend *)
        destruct H as (vs & i & hh & Hfill).
        destruct (firstx_continuation_suspend hs i) eqn:Hfirst.
        -- right.
           destruct i.
           eapply hfilled_typing in Hes as (tf' & C'' & Hsuspend & Hfillback).
           2: exact Hfill.
           destruct tf'.
           apply AI_suspend_desugared_typing in Hsuspend as (t1s' & t2s' & -> & Hn & Htags).
           repeat eexists.
           eapply r_suspend.
           done.
           exact Htags.
           exact Hfirst.
           exact Hfill.
        -- left. right. right. right. left.
           exists vs, i, (HH_prompt [::] ts2 hs hh [::]).
           apply/hfilledP.
           rewrite -(cat0s [::AI_prompt _ _ _]) - (cats0 [:: AI_prompt _ _ _]).
           constructor => //.
           apply/hfilledP. exact Hfill.
      * (* Switch *)
        destruct H as (vs & k & tf & i & hh & Hfill).
        destruct (firstx_continuation_switch hs i) eqn:Hfirst.
        -- right.
           destruct i.
           eapply hfilled_typing in Hes as ([??] & C'' & Hswitch & Hfillback).
           2: exact Hfill.
           apply AI_switch_desugared_typing in Hswitch as (ts & t1s' & t2s' & cont & Htags & Hconts & Hcont & Hvs & Htf & ->).
           destruct cont.
           ++ simpl in Hcont; subst f0 tf. destruct s.
              destruct HST as (_ & _ & _ & _ & Hcontt & _).
              rewrite List.Forall_forall in Hcontt.
              apply List.nth_error_In in Hconts as Hin.
              apply Hcontt in Hin.
              inversion Hin; subst.
              apply (hfilled_change (v_to_e_list vs ++ [:: AI_ref_cont (length s_conts)]) (y := No_var)) in H5 as [LI' HLI'].
              2: by left.
              repeat eexists.
              eapply r_switch.
              exact Hfirst.
              done.
              exact Hconts.
              exact Hfill.
              exact HLI'.
           ++ assert (hfilled No_var hh [::AI_switch_desugared vs k tf (Mk_tagidx n)] es) as Hfillnew.
              { eapply hfilled_no_var.
                exact Hfill. }
              apply (hfilled_change [::AI_trap] (y := No_var)) in Hfillnew as HLI'; last by left.
              destruct HLI' as [LI' HLI'].
              repeat eexists.
              eapply hfilled_reduce.
              2: instantiate (2 := HH_prompt [::] ts2 hs hh [::]).
              2: instantiate (2 := No_var).
              2-3: unfold hfilled, hfill; fold hfill.
              2-3: simpl.
              2: unfold hfilled in Hfillnew; destruct (hfill _ _ _) eqn:Hfilll => //; erewrite Hfilll.
              2: move/eqP in Hfillnew; subst => //.
              2: unfold hfilled in HLI'; destruct (hfill _ _ _) eqn:Hfilll => //; erewrite Hfilll.
              2: move/eqP in HLI'; subst => //.
              intros f1.
              eapply r_switch_failure.
              exact Hconts.
(*           ++ apply hfilled_no_var in Hfills.
              apply (hfilled_change [::AI_trap] (y := No_var)) in Hfills as HLI'; last by left.
              destruct HLI' as [LI' HLI'].
              repeat eexists.
              eapply hfilled_reduce.
              2: instantiate (2 := HH_prompt [::] ts2 hs hhs [::]).
              2: instantiate (2 := No_var).
              2-3: unfold hfilled, hfill; fold hfill.
              2-3: simpl.
              2: unfold hfilled in Hfills; destruct (hfill _ _ _) eqn:Hfilll => //; erewrite Hfilll.
              2: move/eqP in Hfills; subst => //.
              2: unfold hfilled in HLI'; destruct (hfill _ _ _) eqn:Hfilll => //; erewrite Hfilll.
              2: move/eqP in HLI'; subst => //.
              intros f1.
              constructor.
              constructor. *)
        -- left. right. right. right. right.
           exists vs, k, tf, i, (HH_prompt [::] ts2 hs hh [::]).
           apply/hfilledP.
           rewrite -(cat0s [::AI_prompt _ _ _]) - (cats0 [:: AI_prompt _ _ _]).
           constructor => //.
           apply/hfilledP. exact Hfill.
    + (* reduce *)
      destruct H as [s' [f' [es' HReduce]]].
      right.
      simpl in HReduce.
      exists s', f', [::AI_prompt ts2 hs es'].
      eapply r_label; eauto.
      instantiate (1 := LH_prompt [::] ts2 hs (LH_base [::] [::]) [::]).
      instantiate (1 := 0).
      unfold lfilled, lfill => //=.
      by rewrite List.app_nil_r.
      unfold lfilled, lfill => /=.
      by rewrite List.app_nil_r.  

  - (* Handler *)
    move => s C hs es ts Hclauses Hes IH.
    split.
    { move => C' f vcs ts1 ts2 lab ret ts0 HTF Hts0 HContext HInst HConstType HST HBI_brDepth HNRet HCallHost.
      inversion HTF; subst.
    destruct vcs => //.
    simpl. 
    edestruct IH as [IH' _]; eauto.
    edestruct IH'; eauto.
    { 
      move => n lh k HLF.
      eapply HBI_brDepth.
      move/lfilledP in HLF.
      apply/lfilledP.
      instantiate (1 := LH_handler [::] hs lh [::]).
      rewrite - (cat0s [:: AI_handler hs es]).
      rewrite - (cats0 [:: AI_handler hs es]).
      constructor. done. done. }
    { unfold not_lf_return.
      move => n lh HContra.
      unfold not_lf_return in HNRet.
      eapply HNRet.
      move/lfilledP in HContra.
      apply/lfilledP.
      instantiate (1 := LH_handler [::] hs lh [::]).
      rewrite - (cat0s [:: AI_handler hs es]).
      rewrite - (cats0 [:: AI_handler hs es]).
      constructor => //.
      exact HContra.
    }
    { move => tf h vcs n HLF.
      eapply HCallHost.
      unfold first_instr => /=.
      unfold first_instr in HLF.
      rewrite HLF.
      done. } 
    + (* Terminal *)
      simpl in H.
(*      apply terminal_form_v_e in H.
      unfold terminal_form in H. *)
      destruct H as [H | [H | [H | [H | H]]]].
      * (* Const *)
        right.
        exists s, f, es.
        apply r_simple.
        by apply rs_handler_const.
      * (* AI_trap *)
        right. subst.
        exists s, f, [::AI_trap].
        apply r_simple.
        by apply rs_handler_trap.
      * (* Throw_ref *)
        destruct H as (hh & vs & a & t & Hfill).
        destruct (firstx_exception hs t) eqn:Hfirst.
        -- right.
           eapply hfilled_typing in Hfill as Hfill'.
           destruct Hfill' as ([tx ty] & C1 & Hexnthr & Hrebuild).
           2: exact Hes.
           apply AI_throw_ref_desugared_typing in Hexnthr as (exn & Hexn & -> & ->).
           repeat eexists.
           eapply r_throw_ref.
           exact Hfill. exact Hfirst.
        -- right.
           eapply hfilled_typing in Hfill as Hfill'.
           destruct Hfill' as ([tx ty] & C1 & Hexnthr & Hrebuild).
           2: exact Hes.
           apply AI_throw_ref_desugared_typing in Hexnthr as (exn & Hexn & -> & ->).
           repeat eexists.
           eapply r_throw_ref_ref.
           exact Hfill. exact Hfirst.
        -- left. right. right. left.
           exists (HH_handler [::] hs hh [::]), vs, a, t.
           apply/hfilledP.
           rewrite - (cat0s [:: AI_handler _ _]) - (cats0 [:: AI_handler _ _]).
           constructor. done. done.
           apply/hfilledP. done.
      * (* Suspend *)
        destruct H as (vs & i & hh & Hfill).
        left. right. right. right. left.
        exists vs, i, (HH_handler [::] hs hh [::]).
        apply/hfilledP.
        rewrite - (cat0s [:: AI_handler _ _]) - (cats0 [:: AI_handler _ _]).
        constructor. done. done.
        apply/hfilledP. done.
      * (* Switch *)
        destruct H as (vs & k & tf & i & hh & Hfill).
        left. right. right. right. right.
        exists vs, k, tf, i, (HH_handler [::] hs hh [::]).
        apply/hfilledP.
        rewrite - (cat0s [:: AI_handler _ _]) - (cats0 [:: AI_handler _ _]).
        constructor. done. done.
        apply/hfilledP. done.

    + (* reduce *)
      destruct H as [s' [f' [es' HReduce]]].
      right.
      simpl in HReduce.
      exists s', f', [::AI_handler hs es'].
      eapply r_label; eauto.
      instantiate (1 := LH_handler [::] hs (LH_base [::] [::]) [::]).
      instantiate (1 := 0).
      unfold lfilled, lfill => //=.
      by rewrite List.app_nil_r.
      unfold lfilled, lfill => //=.
      by rewrite List.app_nil_r. }
    move => f vcs ts1 ts2 HTF HContext HConstType HST HBI_brDepth HNRet HCallHost.
      inversion HTF; subst.
    destruct vcs => //.
    simpl. 
    edestruct IH as [_ IH']; eauto.
    edestruct IH'; eauto.
    { 
      move => n lh k HLF.
      eapply HBI_brDepth.
      move/lfilledP in HLF.
      apply/lfilledP.
      instantiate (1 := LH_handler [::] hs lh [::]).
      rewrite - (cat0s [:: AI_handler hs es]).
      rewrite - (cats0 [:: AI_handler hs es]).
      constructor. done. done. }
    { unfold not_lf_return.
      move => n lh HContra.
      unfold not_lf_return in HNRet.
      eapply HNRet.
      move/lfilledP in HContra.
      apply/lfilledP.
      instantiate (1 := LH_handler [::] hs lh [::]).
      rewrite - (cat0s [:: AI_handler hs es]).
      rewrite - (cats0 [:: AI_handler hs es]).
      constructor => //.
      exact HContra.
    }
    { move => tf h vcs n HLF.
      eapply HCallHost.
      unfold first_instr => /=.
      unfold first_instr in HLF.
      rewrite HLF.
      done. } 
    + (* Terminal *)
      simpl in H.
(*      apply terminal_form_v_e in H.
      unfold terminal_form in H. *)
      destruct H as [H | [H | [H | [H | H]]]].
      * (* Const *)
        right.
        exists s, f, es.
        apply r_simple.
        by apply rs_handler_const.
      * (* AI_trap *)
        right. subst.
        exists s, f, [::AI_trap].
        apply r_simple.
        by apply rs_handler_trap.
      * (* Throw_ref *)
        destruct H as (hh & vs & a & t & Hfill).
        destruct (firstx_exception hs t) eqn:Hfirst.
        -- right.
           eapply hfilled_typing in Hfill as Hfill'.
           destruct Hfill' as ([tx ty] & C1 & Hexnthr & Hrebuild).
           2: exact Hes.
           apply AI_throw_ref_desugared_typing in Hexnthr as (exn & Hexn & -> & ->).
           repeat eexists.
           eapply r_throw_ref.
           exact Hfill. exact Hfirst.
        -- right.
            eapply hfilled_typing in Hfill as Hfill'.
           destruct Hfill' as ([tx ty] & C1 & Hexnthr & Hrebuild).
           2: exact Hes.
           apply AI_throw_ref_desugared_typing in Hexnthr as (exn & Hexn & -> & ->).
           repeat eexists.
           eapply r_throw_ref_ref.
           exact Hfill. exact Hfirst.
        -- left. right. right. left.
           exists (HH_handler [::] hs hh [::]), vs, a, t.
           apply/hfilledP.
           rewrite - (cat0s [:: AI_handler _ _]) - (cats0 [:: AI_handler _ _]).
           constructor. done. done.
           apply/hfilledP. done.
      * (* Suspend *)
        destruct H as (vs & i & hh & Hfill).
        left. right. right. right. left.
        exists vs, i, (HH_handler [::] hs hh [::]).
        apply/hfilledP.
        rewrite - (cat0s [:: AI_handler _ _]) - (cats0 [:: AI_handler _ _]).
        constructor. done. done.
        apply/hfilledP. done.
      * (* Switch *)
        destruct H as (vs & k & tf & i & hh & Hfill).
        left. right. right. right. right.
        exists vs, k, tf, i, (HH_handler [::] hs hh [::]).
        apply/hfilledP.
        rewrite - (cat0s [:: AI_handler _ _]) - (cats0 [:: AI_handler _ _]).
        constructor. done. done.
        apply/hfilledP. done.

    + (* reduce *)
      destruct H as [s' [f' [es' HReduce]]].
      right.
      simpl in HReduce.
      exists s', f', [::AI_handler hs es'].
      eapply r_label; eauto.
      instantiate (1 := LH_handler [::] hs (LH_base [::] [::]) [::]).
      instantiate (1 := 0).
      unfold lfilled, lfill => //=.
      by rewrite List.app_nil_r.
      unfold lfilled, lfill => //=.
      by rewrite List.app_nil_r. 



    
  - (* Invoke *)
    move => s a C cl tf HNth HType.
    split.
    { move => C' f vcs ts1 ts2 lab ret ts HTF Hts HContext HInst HConstType HST HBI_brDepth HNRet HNCallhost.
    subst.
    destruct cl.
    + (* Native *)
      right. destruct f0.
      simpl in HTF. inversion HTF; subst.
      exists s, f, [:: AI_local (length ts2) (Build_frame (vcs ++ default_vals l) i) [::AI_basic (BI_block (Tf [::] ts2) l0)]].
      eapply r_invoke_native; eauto.
      do 2 rewrite length_is_size.
      rewrite - (size_map Some ts1) - HConstType size_map => //.
    + (* Host *)
      right. simpl in HTF. inversion HTF; subst.
      exists s, f, [:: AI_call_host (Tf ts1 ts2) h vcs].
      eapply r_invoke_host; eauto.
      repeat rewrite length_is_size.
      by rewrite - (size_map Some ts1) - HConstType size_map. }
    move => f vcs ts1 ts2 HTF HContext HConstType HST HBI_brDepth HNRet HNCallhost.
    subst.
    destruct cl.
    + (* Native *)
      right. destruct f0.
      simpl in HTF. inversion HTF; subst.
      exists s, f, [:: AI_local (length ts2) (Build_frame (vcs ++ default_vals l) i) [::AI_basic (BI_block (Tf [::] ts2) l0)]].
      eapply r_invoke_native; eauto.
      do 2 rewrite length_is_size.
      rewrite - (size_map Some ts1) - HConstType size_map => //.
    + (* Host *)
      right. simpl in HTF. inversion HTF; subst.
      exists s, f, [:: AI_call_host (Tf ts1 ts2) h vcs].
      eapply r_invoke_host; eauto.
      repeat rewrite length_is_size.
      by rewrite - (size_map Some ts1) - HConstType size_map.
  - (* AI_label *)
    move => s C e0s es ts t2s n HType1 IHHType1 HType2 IHHType2 HLength.
    split. 
    { move => C' f vcs ts1 ts2 lab ret ts0 HTF Hts0 HContext HInst HConstType HST HBI_brDepth HNRet HCallHost.
    inversion HTF; subst.
    destruct vcs => //. 
    rewrite upd_label_overwrite in HType2. simpl in HType2.
    destruct (br_reduce_decidable es) as [HEMT | HEMF].
    { unfold br_reduce in HEMT.
      destruct HEMT as [n [lh HLF]].
      right. 
      assert (LF : lfilled n lh [::AI_basic (BI_br (n+0))] es); first by rewrite addn0.
      eapply br_reduce_extract_vs in LF => //; eauto.
      destruct LF as [cs [lh' [HConst [HLF2 HLength]]]].
      rewrite addn0 in HLF2.
      repeat eexists.
      apply r_simple.
      eapply rs_br; eauto.
    }
    edestruct IHHType2 as [IH _]; eauto.
    edestruct IH; eauto.

    { unfold br_reduce in HEMF.
      move => n lh k HLF.
      assert (Inf : k < n.+1).
      { eapply HBI_brDepth.
      move/lfilledP in HLF.
      apply/lfilledP.
      assert (LF : lfilledInd (n.+1) (LH_rec [::] (length ts) e0s lh [::]) [::AI_basic (BI_br k)] ([::] ++ [::AI_label (length ts) e0s es] ++ [::]));
        first by apply LfilledRec.
      rewrite cats0 in LF. simpl in LF.
      by apply LF. }
      rewrite ltnS in Inf.
      rewrite leq_eqVlt in Inf.
      remove_bools_options => //.
      subst.
      exfalso.
      apply HEMF. repeat eexists. by apply HLF.
    }
    { unfold not_lf_return.
      move => n lh HContra.
      unfold not_lf_return in HNRet.
      eapply HNRet.
      move/lfilledP in HContra.
      apply/lfilledP.
      assert (LF : lfilledInd (n.+1) (LH_rec [::] (length ts) e0s lh [::]) [::AI_basic BI_return] ([::] ++ [::AI_label (length ts) e0s es] ++ [::]));
        first by apply LfilledRec.
      by apply LF.
    }

    { move => tf h vcs n HLF.
      eapply HCallHost.
      unfold first_instr => /=.
      unfold first_instr in HLF.
      rewrite HLF.
      done. } 
    + (* Terminal *)
      destruct H as [H | [H | [H | [H | H]]]].
      * (* Const *)
        right.
        exists s, f, es.
        apply r_simple.
        by apply rs_label_const.
      * (* AI_trap *)
        right. simpl in H. subst.
        exists s, f, [::AI_trap].
        apply r_simple.
        by apply rs_label_trap.
      * destruct H as (hh & vs & a & t & Hfill).
        left. right. right. left.
        exists (HH_label [::] (length ts) e0s hh [::]), vs, a, t.
        unfold hfilled, hfill; fold hfill.
        simpl.
        unfold hfilled in Hfill.
        destruct (hfill _ _ _) => //.
        move/eqP in Hfill. subst. done.
      * destruct H as (vs & i & hh & Hfill).
        left. right. right. right. left.
        exists vs, i, (HH_label [::] (length ts) e0s hh [::]).
        unfold hfilled, hfill; fold hfill.
        simpl. unfold hfilled in Hfill.
        destruct (hfill _ _ _) => //.
        move/eqP in Hfill. by subst.
      * destruct H as (vs & k & tf & i & hh & Hfill).
        left. right. right. right. right.
        exists vs, k, tf, i, (HH_label [::] (length ts) e0s hh [::]).
        unfold hfilled, hfill; fold hfill.
        simpl. unfold hfilled in Hfill.
        destruct (hfill _ _ _) => //.
        move/eqP in Hfill. by subst.
    + (* reduce *)
      destruct H as [s' [f' [es' HReduce]]].
      right.
      simpl in HReduce.
      exists s', f', [::AI_label (length ts) e0s es'].
      by eapply r_label; eauto; apply label_lfilled1. }
    move => f vcs ts1 ts2 HTF HContext HConstType HST HBI_brDepth HNRet HCallHost.
    inversion HTF; subst.
    destruct vcs => //. 

    destruct (br_reduce_decidable es) as [HEMT | HEMF].
    { unfold br_reduce in HEMT.
      destruct HEMT as [n [lh HLF]].
      right. 
      assert (LF : lfilled n lh [::AI_basic (BI_br (n+0))] es); first by rewrite addn0.
      eapply br_reduce_extract_vs in LF => //; eauto.
      destruct LF as [cs [lh' [HConst [HLF2 HLength]]]].
      rewrite addn0 in HLF2.
      repeat eexists.
      apply r_simple.
      eapply rs_br; eauto.
    }
    edestruct IHHType2 as [_ IH]; eauto.
    edestruct IH; eauto.

    { unfold br_reduce in HEMF.
      move => n lh k HLF.
      assert (Inf : k < n.+1).
      { eapply HBI_brDepth.
      move/lfilledP in HLF.
      apply/lfilledP.
      assert (LF : lfilledInd (n.+1) (LH_rec [::] (length ts) e0s lh [::]) [::AI_basic (BI_br k)] ([::] ++ [::AI_label (length ts) e0s es] ++ [::]));
        first by apply LfilledRec.
      rewrite cats0 in LF. simpl in LF.
      by apply LF. }
      rewrite ltnS in Inf.
      rewrite leq_eqVlt in Inf.
      remove_bools_options => //.
      subst.
      exfalso.
      apply HEMF. repeat eexists. by apply HLF.
    }
    { unfold not_lf_return.
      move => n lh HContra.
      unfold not_lf_return in HNRet.
      eapply HNRet.
      move/lfilledP in HContra.
      apply/lfilledP.
      assert (LF : lfilledInd (n.+1) (LH_rec [::] (length ts) e0s lh [::]) [::AI_basic BI_return] ([::] ++ [::AI_label (length ts) e0s es] ++ [::]));
        first by apply LfilledRec.
      by apply LF.
    }

    { move => tf h vcs n HLF.
      eapply HCallHost.
      unfold first_instr => /=.
      unfold first_instr in HLF.
      rewrite HLF.
      done. } 
    + (* Terminal *)
      destruct H as [H | [H | [H | [H | H]]]].
      * (* Const *)
        right.
        exists s, f, es.
        apply r_simple.
        by apply rs_label_const.
      * (* AI_trap *)
        right. simpl in H. subst.
        exists s, f, [::AI_trap].
        apply r_simple.
        by apply rs_label_trap.
      * destruct H as (hh & vs & a & t & Hfill).
        left. right. right. left.
        exists (HH_label [::] (length ts) e0s hh [::]), vs, a, t.
        unfold hfilled, hfill; fold hfill.
        simpl.
        unfold hfilled in Hfill.
        destruct (hfill _ _ _) => //.
        move/eqP in Hfill. subst. done.
      * destruct H as (vs & i & hh & Hfill).
        left. right. right. right. left.
        exists vs, i, (HH_label [::] (length ts) e0s hh [::]).
        unfold hfilled, hfill; fold hfill.
        simpl. unfold hfilled in Hfill.
        destruct (hfill _ _ _) => //.
        move/eqP in Hfill. by subst.
      * destruct H as (vs & k & tf & i & hh & Hfill).
        left. right. right. right. right.
        exists vs, k, tf, i, (HH_label [::] (length ts) e0s hh [::]).
        unfold hfilled, hfill; fold hfill.
        simpl. unfold hfilled in Hfill.
        destruct (hfill _ _ _) => //.
        move/eqP in Hfill. by subst.
    + (* reduce *)
      destruct H as [s' [f' [es' HReduce]]].
      right.
      simpl in HReduce.
      exists s', f', [::AI_label (length ts) e0s es'].
      by eapply r_label; eauto; apply label_lfilled1. 

  - move => s C t1s t2s h vs Hlen.
    split. 
    { intros C' f vcs ts1 ts2 lab ret ts HTF Hts HC HType Hts1 HSType HBr HRet HCallHost.
    inversion HTF ; subst.
    destruct vcs => //. 
    left.
    exfalso. eapply HCallHost.
    unfold first_instr => /=.
    done. }
    intros f vcs ts1 ts2 HTF HC Hts1 HSType HBr HRet HCallHost.
    inversion HTF ; subst.
    destruct vcs => //. 
    left.
    exfalso. eapply HCallHost.
    unfold first_instr => /=.
    done.
  - (* s_typing *)
    move => s f es rs ts C C0 HFT HContext HType IHHType HRetType HST HBI_brDepth HNRet HCallHost.
    inversion HFT.
    subst.
    destruct IHHType as [IH _].
    edestruct IH; eauto.
    { apply forall_values_type in H1.
      instantiate (1 := tvs).
      apply Const_list_typing in H1 as (tslocs & Htslocs & -> & _).
      exact Htslocs. }
    { (* Context *)
      assert (E : tc_local C1 = [::]).
      { by eapply inst_t_context_local_empty; eauto. }
      rewrite E. simpl.
      by fold_upd_context. }
    { by instantiate (1 := [::]). }
    + left. split; first exact H0.
      intros Hes.
      apply const_es_exists in Hes as [vs ->].
      apply Const_list_typing in HType as (ts' & Hts' & -> & _).
      repeat rewrite length_is_size. simpl.
      rewrite v_to_e_size.
      rewrite - (size_map Some ts') - Hts' size_map => //. 
    + (* reduce *)
      simpl in H0. right.  by eauto.
  - done.
Qed.

Theorem t_progress: forall s f es ts,
    config_typing s f es ts ->
    terminal_form es \/
      (exists tf h vcs n, first_instr es = Some (AI_call_host tf h vcs,n)) \/
                        exists s' f' es', reduce s f es s' f' es'.
Proof.
  move => s f es ts HType.
  inversion HType. inversion H0. inversion H5. subst.
  apply forall_values_type in H16.
  apply Const_list_typing in H16 as (tsv & Htsv & -> & Hflocs).
  destruct (first_instr es) eqn:Hes.
  destruct p.
  destruct a ; last first.
  right ; left.
  by repeat eexists.
  all: eapply t_progress_e with (vcs := [::]) (ret := None) (lab := [::]) in H7; eauto.
  all: try by destruct H7 ; [left | right ; right].
  all: try by rewrite Hes.
  all: try by eapply s_typing_lf_br; eauto.
  all: try by eapply s_typing_lf_return; eauto.
  all: assert (E : tc_local C1 = [::]); 
    first by eapply inst_t_context_local_empty; eauto. 
  all: rewrite E.
  all: simpl.
  all: fold_upd_context.
  all: assert (E' : tc_label (upd_local_return C1 tsv None) = [::]);
    first by simpl; eapply inst_t_context_label_empty; eauto.
  all: rewrite -E'.
  all: by destruct C1.
Qed.




