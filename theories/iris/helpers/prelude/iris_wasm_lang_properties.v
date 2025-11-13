From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From Wasm.iris.language.iris Require Export iris.
From Wasm Require Export stdpp_aux.
Require Export iris_lfilled_properties.

Set Bullet Behavior "Strict Subproofs".

Ltac false_assumption := exfalso ; apply ssrbool.not_false_is_true ; assumption.

Ltac const_list_app :=
   unfold const_list ; 
   rewrite forallb_app ;
   apply andb_true_iff ; split => //=.

Lemma last_inj {A : Type} (l1 l2 : list A) (a b : A) :
    l1 = l2 -> last l1 = Some a -> last l2 = Some b -> a = b.
Proof.
  intros Heq Hla1 Hla2.
  subst. rewrite Hla1 in Hla2. inversion Hla2. done.
Qed.

Ltac not_const e He :=
  let b := fresh "b" in
  destruct e as [b| | | | ] ; (try by (left + right)) ;
  destruct b ; (try by left) ;
    by exfalso ; apply He.

(* given a nonempty list x :: xs, gives user a hypothesis "Htail : x :: xs = ys ++ [y]" *)
Ltac get_tail x xs ys y Htail :=
  cut (exists ys y, x :: xs = ys ++ [y]) ;
  [ intro Htail ; destruct Htail as (ys & y & Htail) |
    exists (removelast (x :: xs)) ;
    exists (List.last (x :: xs) AI_trap) ;
    apply app_removelast_last ;
    apply not_eq_sym ; apply nil_cons ].


Lemma destruct_list_rev {A : Type} (l : list A) :
  l = [] ∨ ∃ a l', l = l' ++ [a].
Proof.
  destruct l using List.rev_ind; by [ left | right; eexists _, _].
Qed.

Section wasm_lang_properties.

  Let expr := iris.expr.
  Let val := iris.val.
  Let to_val := iris.to_val.

  Lemma v_to_e_is_fmap vs :
    v_to_e_list vs = (fun x => AI_const x) <$> vs.
  Proof. done. Qed.

    Lemma to_val_cat (es1 es2: list administrative_instruction) (vs: list value) :
    iris.to_val0 (es1 ++ es2) = Some (immV vs) ->
    iris.to_val0 es1 = Some (immV (take (length es1) vs)) /\
      iris.to_val0 es2 = Some (immV ((drop (length es1) vs))).
  Proof.
    move => H.
    apply iris.of_to_val0 in H.
    apply fmap_split in H; destruct H as [H1 H2].
    remember (length es1) as n1.
    remember (length es2) as n2.
    rewrite - H1.
    rewrite - H2.
    specialize (of_val_imm (take n1 vs)) as H.
    do 2 rewrite - v_to_e_is_fmap. 
    rewrite !of_val_imm.
    by repeat rewrite iris.to_of_val0.
  Qed.

  Lemma to_val_cat_inv (es1 es2: list administrative_instruction) (vs1 vs2: list value) :
    iris.to_val0 es1 = Some (immV vs1) ->
    iris.to_val0 es2 = Some (immV vs2) ->
    iris.to_val0 (es1 ++ es2) = Some (immV (vs1 ++ vs2)).
  Proof.
    move => Htv1 Htv2.
    apply to_val_is_immV in Htv1, Htv2; subst.
    repeat rewrite map_fmap.
    rewrite - fmap_app -to_of_val0; by f_equal => /=.
  Qed.

  Lemma to_val_cat_None1 (es1 es2: list administrative_instruction) :
    iris.to_val0 es1 = None ->
    iris.to_val0 (es1 ++ es2) = None.
  Proof.
    apply to_val_None_append.
  Qed.

  Lemma to_val_cat_None2 (es1 es2: list administrative_instruction) :
    const_list es1 ->
    iris.to_val0 es2 = None ->
    iris.to_val0 (es1 ++ es2) = None.
  Proof.
    apply to_val_None_prepend_const.
  Qed.

  Lemma app_to_val vs es es' :
    const_list vs ->
    is_Some (iris.to_val0 (vs ++ es ++ es')) ->
    is_Some (iris.to_val0 es).
  Proof.
    intros Hconst [x Hx].
    destruct (iris.to_val0 es) eqn:Hes;eauto.
    apply to_val_cat_None1 with _ es' in Hes.
    apply to_val_cat_None2 with vs _ in Hes;auto.
    congruence.
  Qed.
  
  Lemma to_eff_cat_None1 (es1 es2: list administrative_instruction) :
    (const_list es1 -> False) ->
    iris.to_eff0 es1 = None ->
    iris.to_eff0 (es1 ++ es2) = None.
  Proof.
    apply to_eff_None_append.
  Qed.

  Lemma to_eff_cat_None2 (es1 es2: list administrative_instruction) :
    const_list es1 ->
    iris.to_eff0 es2 = None ->
    iris.to_eff0 (es1 ++ es2) = None.
  Proof.
    apply to_eff_None_prepend_const.
  Qed.

  Lemma app_to_eff vs es es' :
    const_list vs ->
    (const_list es -> False) ->
    is_Some (iris.to_eff0 (vs ++ es ++ es')) ->
    is_Some (iris.to_eff0 es).
  Proof.
    intros Hconst Hnconst [x Hx].
    destruct (iris.to_eff0 es) eqn:Hes;eauto.
    apply to_eff_cat_None1 with _ es' in Hes.
    apply to_eff_cat_None2 with vs _ in Hes;auto.
    congruence. done.
  Qed.

    Lemma lfilled_to_val i  :
    ∀ lh es LI, is_Some (iris.to_val0 LI) ->
                lfilled i lh es LI ->
                is_Some (iris.to_val0 es).
  Proof.
    intros lh.
    generalize dependent i.
    induction lh.
    - intros k es LI [x Hsome] Hfill.
      apply lfilled_Ind_Equivalent in Hfill.
      inversion Hfill;subst.
      destruct (to_val0 es) eqn:Hnone;eauto.
      exfalso.
      apply (to_val_cat_None1 _ l0) in Hnone.
      apply (to_val_cat_None2 l) in Hnone.
      rewrite Hnone in Hsome. done. auto.
    - intros k es LI Hsome Hfill.
      apply lfilled_Ind_Equivalent in Hfill.
      inversion Hfill;simplify_eq.
      apply app_to_val in Hsome;auto.
      inversion Hsome.
      unfold iris.to_val0 in H ; simpl in H.
      destruct (merge_values $ map _ _) eqn:Hmerge => //.
      2: by destruct e.
      apply lfilled_Ind_Equivalent in H8.
      apply (IHlh k0 es LI0) => //.
      unfold iris.to_val0.
      by rewrite Hmerge.
    - intros k es LI Hsome Hfill.
      move/lfilledP in Hfill.
      inversion Hfill; subst.
      apply app_to_val in Hsome => //.
      destruct Hsome as [x H].
      unfold iris.to_val0 in H; simpl in H.
      destruct (merge_values $ map _ _) eqn:Hmerge => //.
      2:{ destruct e => //.
          destruct (exnelts_of_exception_clauses _ _) => //.  }
      move/lfilledP in H7.
      apply (IHlh k es LI0) => //.
      rewrite /iris.to_val0 Hmerge => //.
    - intros k es LI Hsome Hfill.
      move/lfilledP in Hfill.
      inversion Hfill; subst.
      apply app_to_val in Hsome => //.
      destruct Hsome as [x H].
      unfold iris.to_val0 in H; simpl in H.
      destruct (merge_values $ map _ _) eqn:Hmerge => //.
      2:{ destruct e => //.
          destruct (suselts_of_continuation_clauses _ _) => //.
          destruct (swelts_of_continuation_clauses _ _) => //. } 
      move/lfilledP in H8.
      apply (IHlh k es LI0) => //.
      rewrite /iris.to_val0 Hmerge => //.
  Qed.
  
  Lemma lfilled_to_eff i  :
    ∀ lh es LI, is_Some (iris.to_eff0 LI) ->
                lfilled i lh es LI ->
                is_Some (iris.to_eff0 es) \/ const_list es.
  Proof.
    intros lh.
    generalize dependent i.
    induction lh.
    - intros k es LI [x Hsome] Hfill.
      apply lfilled_Ind_Equivalent in Hfill.
      inversion Hfill;subst.
      destruct (to_eff0 es) eqn:Hnone;eauto.
      destruct (const_list es) eqn:Hes; try by right.
      apply (to_eff_cat_None1 _ l0) in Hnone.
      apply (to_eff_cat_None2 l) in Hnone.
      rewrite Hnone in Hsome. done. auto.
      by rewrite Hes.
    - intros k es LI Hsome Hfill.
      apply lfilled_Ind_Equivalent in Hfill.
      inversion Hfill;simplify_eq.
      apply app_to_eff in Hsome;auto.
      inversion Hsome.
      unfold iris.to_eff0 in H ; simpl in H.
      destruct (merge_values $ map _ _) eqn:Hmerge => //.
      + destruct v => //.
        destruct i => //.
        destruct (vh_decrease _) => //.
      + apply lfilled_Ind_Equivalent in H8.
        apply (IHlh k0 es LI0) => //.
        unfold iris.to_eff0.
        by rewrite Hmerge.
    - intros k es LI Hsome Hfill.
      move/lfilledP in Hfill.
      inversion Hfill; subst.
      apply app_to_eff in Hsome => //.
      destruct Hsome as [x H].
      unfold iris.to_eff0 in H; simpl in H.
      destruct (merge_values $ map _ _) eqn:Hmerge => //.
      destruct v => //. 
      move/lfilledP in H7.
      apply (IHlh k es LI0) => //.
      rewrite /iris.to_eff0 Hmerge => //.
    - intros k es LI Hsome Hfill.
      move/lfilledP in Hfill.
      inversion Hfill; subst.
      apply app_to_eff in Hsome => //.
      destruct Hsome as [x H].
      unfold iris.to_eff0 in H; simpl in H.
      destruct (merge_values $ map _ _) eqn:Hmerge => //.
      destruct v => //. 
      move/lfilledP in H8.
      apply (IHlh k es LI0) => //.
      rewrite /iris.to_eff0 Hmerge => //.
  Qed.

  Lemma lfilled_to_eff_sus i lh es LI vs k sh:
    iris.to_eff0 LI = Some (susE vs k sh) ->
    lfilled i lh es LI ->
    is_pure lh ->
    const_list es \/
    exists shin shout,
      iris.to_eff0 es = Some (susE vs k shin) /\
        susholed_of_lholed lh = Some shout /\
        sus_trans shout shin = sh.
  Proof.
    intros Heff Hfilled Hpure.
    generalize dependent LI.
    generalize dependent sh.
    generalize dependent i.
    induction Hpure.
    all: intros i sh LI Heff Hfill.
    all: apply lfilled_Ind_Equivalent in Hfill.
    all: inversion Hfill;subst.
    all: unfold to_eff0 in Heff.
    all: repeat rewrite cat_app in Heff.
    all: do 2 rewrite map_app in Heff.
    all: repeat rewrite -cat_app in Heff.
    all: do 2 rewrite merge_app in Heff.
    apply const_es_exists in H4 as [vsl ->].
    2: apply const_es_exists in H7 as [vsl ->].
    all: specialize (to_of_val0 (immV vsl)) as Hvsl.
    all: unfold iris.to_val0 in Hvsl.
    all: unfold of_val0 in Hvsl.
    all: destruct (merge_values (map _ (_ vsl))) => //.
    all: inversion Hvsl; subst.
    - destruct (merge_values (map _ es)) eqn:Hmergees => //.
      + destruct v => //=.
        * left. specialize (@of_to_val0 es) as Habs.
          unfold iris.to_val0 in Habs. rewrite Hmergees in Habs.
          specialize (Habs _ Logic.eq_refl).
          subst es. rewrite v_to_e_is_const_list //.
        * rewrite val_not_val_combine_assoc in Heff.
          simpl in Heff. destruct vsl => //.
          simpl in Heff.
          destruct (expr_of_val_not_val _) => //. 
      + destruct e => //=.
        simpl in Heff.
        inversion Heff; subst.
        right. do 2 eexists.
        rewrite /to_eff0 Hmergees e_to_v_v_to_e merge_to_val.
        repeat split => //=.
    - simpl in Heff.
      destruct (merge_values (map _ LI0)) eqn:Hmerge0 => //.
      + destruct v => //=.
        destruct i => //=.
        destruct (vh_decrease _) => //=.
      + destruct e => //=.
        simpl in Heff.
        inversion Heff; subst.
        unfold to_eff0 in IHHpure.
        move/lfilledP in H8.
        eapply IHHpure in H8.
        2: by rewrite Hmerge0.
        destruct H8 as [Hconst | (shin & shout & Hin & Hout & Htrans)]; first by left.
        right.
        do 2 eexists.
        split; first done.
        rewrite Hout e_to_v_v_to_e.
        split; first done.
        rewrite /= cats0 Htrans merge_to_val //.
  Qed.

  Lemma to_eff_sus_lfilled k lh es LI shin shout vs i:
    susholed_of_lholed lh = Some shout ->
    lfilled k lh es LI ->
    to_eff0 es = Some (susE vs i shin) ->
    to_eff0 LI = Some (susE vs i (sus_trans shout shin)).
  Proof.
    generalize dependent shout.
    generalize dependent k.
    generalize dependent LI.
    induction lh => //=.
    - destruct (e_to_v_list_opt l) eqn:Hl => //.
      intros LI k shout Heq Hfill Hes.
      simplify_eq.
      move/lfilledP in Hfill. inversion Hfill; subst.
      apply v_to_e_e_to_v in Hl as <-.
      apply const_list_to_val in H4 as (vs' & Htv & Hvs).
      apply v_to_e_inj in Hvs as ->.
      unfold iris.to_val0 in Htv.
      unfold to_eff0.
      unfold to_eff0 in Hes.
      do 2 rewrite map_app merge_app.
      destruct (merge_values _) => //.
      destruct (merge_values _) => //.
      simplify_eq.
      simpl.
      rewrite -merge_flatten.
      rewrite flatten_simplify. done.
    - destruct (susholed_of_lholed lh) => //.
      destruct (e_to_v_list_opt l) eqn:Hl => //.
      intros LI k shout Heq Hfill Hes.
      simplify_eq.
      move/lfilledP in Hfill.
      inversion Hfill; subst.
      move/lfilledP in H8.
      eapply IHlh in Hes.
      2: done. 2: done.
      apply v_to_e_e_to_v in Hl as <-.
      apply const_list_to_val in H7 as (vs' & Htv & Hvs).
      apply v_to_e_inj in Hvs as ->.
      unfold iris.to_val0 in Htv.
      unfold to_eff0.
      unfold to_eff0 in Hes.
      rewrite map_app merge_app /=.
      destruct (merge_values _) => //.
      destruct (merge_values _) => //.
      simplify_eq.
      simpl.
      rewrite merge_suspend.
      simpl.
      rewrite flatten_simplify cats0 //.
  Qed.

  Lemma to_eff_sw_lfilled k lh es LI shin shout vs k' tf i:
    swholed_of_lholed lh = Some shout ->
    lfilled k lh es LI ->
    to_eff0 es = Some (swE vs k' tf i shin) ->
    to_eff0 LI = Some (swE vs k' tf i (sw_trans shout shin)).
  Proof.
    generalize dependent shout.
    generalize dependent k.
    generalize dependent LI.
    induction lh => //=.
    - destruct (e_to_v_list_opt l) eqn:Hl => //.
      intros LI k shout Heq Hfill Hes.
      simplify_eq.
      move/lfilledP in Hfill. inversion Hfill; subst.
      apply v_to_e_e_to_v in Hl as <-.
      apply const_list_to_val in H4 as (vs' & Htv & Hvs).
      apply v_to_e_inj in Hvs as ->.
      unfold iris.to_val0 in Htv.
      unfold to_eff0.
      unfold to_eff0 in Hes.
      do 2 rewrite map_app merge_app.
      destruct (merge_values _) => //.
      destruct (merge_values _) => //.
      simplify_eq.
      simpl.
      rewrite -merge_flatten.
      rewrite flatten_simplify. done.
    - destruct (swholed_of_lholed lh) => //.
      destruct (e_to_v_list_opt l) eqn:Hl => //.
      intros LI k shout Heq Hfill Hes.
      simplify_eq.
      move/lfilledP in Hfill.
      inversion Hfill; subst.
      move/lfilledP in H8.
      eapply IHlh in Hes.
      2: done. 2: done.
      apply v_to_e_e_to_v in Hl as <-.
      apply const_list_to_val in H7 as (vs' & Htv & Hvs).
      apply v_to_e_inj in Hvs as ->.
      unfold iris.to_val0 in Htv.
      unfold to_eff0.
      unfold to_eff0 in Hes.
      rewrite map_app merge_app /=.
      destruct (merge_values _) => //.
      destruct (merge_values _) => //.
      simplify_eq.
      simpl.
      rewrite merge_switch.
      simpl.
      rewrite flatten_simplify cats0 //.
  Qed. 
                 


  Lemma to_eff_thr_lfilled k lh es LI shin shout vs a i:
    exnholed_of_lholed lh = Some shout ->
    lfilled k lh es LI ->
    to_eff0 es = Some (thrE vs a i shin) ->
    to_eff0 LI = Some (thrE vs a i (exn_trans shout shin)).
  Proof.
    generalize dependent shout.
    generalize dependent k.
    generalize dependent LI.
    induction lh => //=.
    - destruct (e_to_v_list_opt l) eqn:Hl => //.
      intros LI k shout Heq Hfill Hes.
      simplify_eq.
      move/lfilledP in Hfill. inversion Hfill; subst.
      apply v_to_e_e_to_v in Hl as <-.
      apply const_list_to_val in H4 as (vs' & Htv & Hvs).
      apply v_to_e_inj in Hvs as ->.
      unfold iris.to_val0 in Htv.
      unfold to_eff0.
      unfold to_eff0 in Hes.
      do 2 rewrite map_app merge_app.
      destruct (merge_values _) => //.
      destruct (merge_values _) => //.
      simplify_eq.
      simpl.
      rewrite -merge_flatten.
      rewrite flatten_simplify. done.
    - destruct (exnholed_of_lholed lh) => //.
      destruct (e_to_v_list_opt l) eqn:Hl => //.
      intros LI k shout Heq Hfill Hes.
      simplify_eq.
      move/lfilledP in Hfill.
      inversion Hfill; subst.
      move/lfilledP in H8.
      eapply IHlh in Hes.
      2: done. 2: done.
      apply v_to_e_e_to_v in Hl as <-.
      apply const_list_to_val in H7 as (vs' & Htv & Hvs).
      apply v_to_e_inj in Hvs as ->.
      unfold iris.to_val0 in Htv.
      unfold to_eff0.
      unfold to_eff0 in Hes.
      rewrite map_app merge_app /=.
      destruct (merge_values _) => //.
      destruct (merge_values _) => //.
      simplify_eq.
      simpl.
      rewrite merge_throw.
      simpl.
      rewrite flatten_simplify cats0 //.
  Qed.

  
Lemma lfilled_to_eff_sw i lh es LI vs k tf k' sh:
    iris.to_eff0 LI = Some (swE vs k tf k' sh) ->
    lfilled i lh es LI ->
    is_pure lh ->
    const_list es \/
    exists shin shout,
      iris.to_eff0 es = Some (swE vs k tf k' shin) /\
        swholed_of_lholed lh = Some shout /\
        sw_trans shout shin = sh.
  Proof.
    intros Heff Hfilled Hpure.
    generalize dependent LI.
    generalize dependent sh.
    generalize dependent i.
    induction Hpure.
    all: intros i sh LI Heff Hfill.
    all: apply lfilled_Ind_Equivalent in Hfill.
    all: inversion Hfill;subst.
    all: unfold to_eff0 in Heff.
    all: repeat rewrite cat_app in Heff.
    all: do 2 rewrite map_app in Heff.
    all: repeat rewrite -cat_app in Heff.
    all: do 2 rewrite merge_app in Heff.
    apply const_es_exists in H4 as [vsl ->].
    2: apply const_es_exists in H7 as [vsl ->].
    all: specialize (to_of_val0 (immV vsl)) as Hvsl.
    all: unfold iris.to_val0 in Hvsl.
    all: unfold of_val0 in Hvsl.
    all: destruct (merge_values (map _ (_ vsl))) => //.
    all: inversion Hvsl; subst.
    - destruct (merge_values (map _ es)) eqn:Hmergees => //.
      + destruct v => //=.
        * left. specialize (@of_to_val0 es) as Habs.
          unfold iris.to_val0 in Habs. rewrite Hmergees in Habs.
          specialize (Habs _ Logic.eq_refl).
          subst es. rewrite v_to_e_is_const_list //.
        * rewrite val_not_val_combine_assoc in Heff.
          simpl in Heff. destruct vsl => //.
          simpl in Heff.
          destruct (expr_of_val_not_val _) => //. 
      + destruct e => //=.
        simpl in Heff.
        inversion Heff; subst.
        right. do 2 eexists.
        rewrite /to_eff0 Hmergees e_to_v_v_to_e merge_to_val.
        repeat split => //=.
    - simpl in Heff.
      destruct (merge_values (map _ LI0)) eqn:Hmerge0 => //.
      + destruct v => //=.
        destruct i => //=.
        destruct (vh_decrease _) => //=.
      + destruct e => //=.
        simpl in Heff.
        inversion Heff; subst.
        unfold to_eff0 in IHHpure.
        move/lfilledP in H8.
        eapply IHHpure in H8.
        2: by rewrite Hmerge0.
        destruct H8 as [Hconst | (shin & shout & Hin & Hout & Htrans)]; first by left.
        right.
        do 2 eexists.
        split; first done.
        rewrite Hout e_to_v_v_to_e.
        split; first done.
        rewrite /= cats0 Htrans merge_to_val //.
  Qed.
  
  Lemma lfilled_to_eff_thr i lh es LI vs k k' sh:
    iris.to_eff0 LI = Some (thrE vs k k' sh) ->
    lfilled i lh es LI ->
    is_pure lh ->
    const_list es \/
    exists shin shout,
      iris.to_eff0 es = Some (thrE vs k k' shin) /\
        exnholed_of_lholed lh = Some shout /\
        exn_trans shout shin = sh.
  Proof.
    intros Heff Hfilled Hpure.
    generalize dependent LI.
    generalize dependent sh.
    generalize dependent i.
    induction Hpure.
    all: intros i sh LI Heff Hfill.
    all: apply lfilled_Ind_Equivalent in Hfill.
    all: inversion Hfill;subst.
    all: unfold to_eff0 in Heff.
    all: repeat rewrite cat_app in Heff.
    all: do 2 rewrite map_app in Heff.
    all: repeat rewrite -cat_app in Heff.
    all: do 2 rewrite merge_app in Heff.
    apply const_es_exists in H4 as [vsl ->].
    2: apply const_es_exists in H7 as [vsl ->].
    all: specialize (to_of_val0 (immV vsl)) as Hvsl.
    all: unfold iris.to_val0 in Hvsl.
    all: unfold of_val0 in Hvsl.
    all: destruct (merge_values (map _ (_ vsl))) => //.
    all: inversion Hvsl; subst.
    - destruct (merge_values (map _ es)) eqn:Hmergees => //.
      + destruct v => //=.
        * left. specialize (@of_to_val0 es) as Habs.
          unfold iris.to_val0 in Habs. rewrite Hmergees in Habs.
          specialize (Habs _ Logic.eq_refl).
          subst es. rewrite v_to_e_is_const_list //.
        * rewrite val_not_val_combine_assoc in Heff.
          simpl in Heff. destruct vsl => //.
          simpl in Heff.
          destruct (expr_of_val_not_val _) => //. 
      + destruct e => //=.
        simpl in Heff.
        inversion Heff; subst.
        right. do 2 eexists.
        rewrite /to_eff0 Hmergees e_to_v_v_to_e merge_to_val.
        repeat split => //=.
    - simpl in Heff.
      destruct (merge_values (map _ LI0)) eqn:Hmerge0 => //.
      + destruct v => //=.
        destruct i => //=.
        destruct (vh_decrease _) => //=.
      + destruct e => //=.
        simpl in Heff.
        inversion Heff; subst.
        unfold to_eff0 in IHHpure.
        move/lfilledP in H8.
        eapply IHHpure in H8.
        2: by rewrite Hmerge0.
        destruct H8 as [Hconst | (shin & shout & Hin & Hout & Htrans)]; first by left.
        right.
        do 2 eexists.
        split; first done.
        rewrite Hout e_to_v_v_to_e.
        split; first done.
        rewrite /= cats0 Htrans merge_to_val //.
  Qed.

  Lemma first_values_elem_of vs1 e1 es1 vs2 e2 es2 :
    (is_const e1 = false) ->
    (is_const e2 = false) ->
    e2 ∉ vs1 ->
    e1 ∉ vs2 ->
    vs1 ++ e1 :: es1 = vs2 ++ e2 :: es2 ->
    vs1 = vs2 /\ e1 = e2 /\ es1 = es2.
  Proof.
    intros He1 He2 Hvs1 Hvs2 Heq.
    generalize dependent vs2; induction vs1 ; intros.
    { destruct vs2 ; inversion Heq => //=. rewrite <- H0 in Hvs2.
      simpl in Hvs2. apply not_elem_of_cons in Hvs2 as [Hcontr _]. done. }
    destruct vs2 ; inversion Heq.
    { rewrite H0 in Hvs1.
      simpl in Hvs1. apply not_elem_of_cons in Hvs1 as [Hcontr _]. done. }
    assert (vs1 = vs2 /\ e1 = e2 /\ es1 = es2) as H ; last by destruct H ; subst.
    apply not_elem_of_cons in Hvs1 as [Hne Hvs1].
    apply not_elem_of_cons in Hvs2 as [Hne' Hvs2].
    apply IHvs1 => //=.
  Qed.
  
  Lemma const_list_elem_of e es :
    const_list es ->
    (is_const e = false) ->
    e ∉ es.
  Proof.
    intros Hes Hv.
    intro Hin.
    unfold const_list in Hes.
    edestruct forallb_forall.
    eapply H in Hes ; last first.
    by apply elem_of_list_In.
    rewrite Hes in Hv => //. 
  Qed.

  Lemma to_val_br_base es1 n l e :
    iris.to_val0 es1 = Some (brV (VH_base n l e)) ->
    es1 = (fmap (fun v => AI_const v) l) ++ [AI_basic (BI_br n)] ++ e.
  Proof.
    intro.
    apply of_to_val0 in H.
    simpl in H. by rewrite H.
  Qed.

  Lemma to_val_br_rec es1 n bef m es (vh : valid_holed n) aft :
    iris.to_val0 es1 = Some (brV (VH_rec bef m es vh aft)) ->
    exists LI, es1 = (fmap (fun v => AI_const v) bef) ++ [AI_label m es LI] ++ aft
          /\ iris.to_val0 LI = Some (brV (vh_increase vh)).
  Proof.
    intro.
    apply of_to_val0 in H.
    simpl in H.
    rewrite - H.
    eexists.
    split => //.
    rewrite - (to_of_val0 (brV (vh_increase vh))).
    unfold of_val0, iris.of_val0.
    by rewrite vfill_increase.
  Qed.

  Lemma to_val_br_prompt es1 n bef m es (vh : valid_holed n) aft :
    iris.to_val0 es1 = Some (brV (VH_prompt bef m es vh aft)) ->
    exists LI, es1 = (fmap (fun v => AI_const v) bef) ++ [AI_prompt m es LI] ++ aft
          /\ iris.to_val0 LI = Some (brV vh).
  Proof.
    intro.
    apply of_to_val0 in H.
    simpl in H.
    rewrite - H.
    eexists.
    split => //.
    rewrite - (to_of_val0 (brV vh)).
    unfold of_val, iris.of_val.
    done.
  Qed.

   Lemma to_val_br_handler es1 n bef es (vh : valid_holed n) aft :
    iris.to_val0 es1 = Some (brV (VH_handler bef es vh aft)) ->
    exists LI, es1 = (fmap (fun v => AI_const v) bef) ++ [AI_handler es LI] ++ aft
          /\ iris.to_val0 LI = Some (brV vh).
  Proof.
    intro.
    apply of_to_val0 in H.
    simpl in H.
    rewrite - H.
    eexists.
    split => //.
    rewrite - (to_of_val0 (brV vh)).
    unfold of_val, iris.of_val.
    done.
  Qed.

  Lemma to_val_ret_base es1 l e :
    iris.to_val0 es1 = Some (retV (SH_base l e)) ->
    es1 = (fmap (fun v => AI_const v) l) ++ [AI_basic BI_return] ++ e.
  Proof.
    intro.
    apply of_to_val0 in H.
    simpl in H. by rewrite H.
  Qed.

  Lemma to_val_call_host_base es1 l e tf h vcs:
    iris.to_val0 es1 = Some (callHostV tf h vcs (LL_base l e)) ->
    es1 = (fmap (fun v => AI_const v) l) ++ [AI_call_host tf h vcs] ++ e.
  Proof.
    intro.
    apply of_to_val0 in H.
    simpl in H. by rewrite H.
  Qed.

  Lemma to_val_ret_rec es1 bef m es sh aft :
    iris.to_val0 es1 = Some (retV (SH_rec bef m es sh aft)) ->
    exists LI, es1 = (fmap (fun v => AI_const v) bef) ++ [AI_label m es LI] ++ aft
          /\ iris.to_val0 LI = Some (retV sh).
  Proof.
    intro.
    apply of_to_val0 in H.
    simpl in H.
    rewrite - H.
    eexists.
    split => //.
    rewrite - (to_of_val0 (retV sh)).
    unfold of_val.
    done.
  Qed.

  Lemma to_val_ret_prompt es1 bef m es sh aft :
    iris.to_val0 es1 = Some (retV (SH_prompt bef m es sh aft)) ->
    exists LI, es1 = (fmap (fun v => AI_const v) bef) ++ [AI_prompt m es LI] ++ aft
          /\ iris.to_val0 LI = Some (retV sh).
  Proof.
    intro.
    apply of_to_val0 in H.
    simpl in H.
    rewrite - H.
    eexists.
    split => //.
    rewrite - (to_of_val0 (retV sh)).
    unfold of_val.
    done.
  Qed.

  Lemma to_val_ret_handler es1 bef es sh aft :
    iris.to_val0 es1 = Some (retV (SH_handler bef es sh aft)) ->
    exists LI, es1 = (fmap (fun v => AI_const v) bef) ++ [AI_handler es LI] ++ aft
          /\ iris.to_val0 LI = Some (retV sh).
  Proof.
    intro.
    apply of_to_val0 in H.
    simpl in H.
    rewrite - H.
    eexists.
    split => //.
    rewrite - (to_of_val0 (retV sh)).
    unfold of_val.
    done.
  Qed.

  Lemma to_val_call_host_rec_label es1 bef m es sh aft tf h vcs:
    iris.to_val0 es1 = Some (callHostV tf h vcs (LL_label bef m es sh aft)) ->
    exists LI, es1 = (fmap (fun v => AI_const v) bef) ++ [AI_label m es LI] ++ aft
          /\ iris.to_val0 LI = Some (callHostV tf h vcs sh).
  Proof.
    intro.
    apply of_to_val0 in H.
    simpl in H.
    rewrite - H.
    eexists.
    split => //.
    rewrite - (to_of_val0 (callHostV tf h vcs sh)).
    unfold of_val.
    done.
  Qed.

  Lemma to_val_call_host_rec_local es1 bef n f sh aft tf h vcs:
    iris.to_val0 es1 = Some (callHostV tf h vcs (LL_frame bef n f sh aft)) ->
    exists LI, es1 = (v_to_e_list bef) ++ [AI_frame n f LI] ++ aft /\
            iris.to_val0 LI = Some (callHostV tf h vcs sh).
  Proof.
    intro.
    apply of_to_val0 in H.
    simpl in H.
    rewrite - H.
    eexists.
    split => //.
    rewrite - (to_of_val0 (callHostV tf h vcs sh)).
    unfold of_val => //.
  Qed.

   Lemma to_val_call_host_rec_prompt es1 bef m es sh aft tf h vcs:
    iris.to_val0 es1 = Some (callHostV tf h vcs (LL_prompt bef m es sh aft)) ->
    exists LI, es1 = (fmap (fun v => AI_const v) bef) ++ [AI_prompt m es LI] ++ aft
          /\ iris.to_val0 LI = Some (callHostV tf h vcs sh).
  Proof.
    intro.
    apply of_to_val0 in H.
    simpl in H.
    rewrite - H.
    eexists.
    split => //.
    rewrite - (to_of_val0 (callHostV tf h vcs sh)).
    unfold of_val.
    done.
  Qed.

  Lemma to_val_call_host_rec_handler es1 bef es sh aft tf h vcs:
    iris.to_val0 es1 = Some (callHostV tf h vcs (LL_handler bef es sh aft)) ->
    exists LI, es1 = (fmap (fun v => AI_const v) bef) ++ [AI_handler es LI] ++ aft
          /\ iris.to_val0 LI = Some (callHostV tf h vcs sh).
  Proof.
    intro.
    apply of_to_val0 in H.
    simpl in H.
    rewrite - H.
    eexists.
    split => //.
    rewrite - (to_of_val0 (callHostV tf h vcs sh)).
    unfold of_val.
    done.
  Qed.


  Lemma to_eff_sus_base es1 vs i n l:
    iris.to_eff0 es1 = Some (susE vs i (SuBase n l)) ->
    es1 = (fmap (fun v => AI_const v) n) ++ [AI_suspend_desugared vs i] ++ l.
  Proof.
    intro.
    apply of_to_eff0 in H.
    simpl in H. by rewrite H.
  Qed.

  Lemma to_eff_sus_rec es1 vs i bef m es vh aft :
    iris.to_eff0 es1 = Some (susE vs i (SuLabel bef m es vh aft)) ->
    exists LI, es1 = (fmap (fun v => AI_const v) bef) ++ [AI_label m es LI] ++ aft
          /\ iris.to_eff0 LI = Some (susE vs i vh).
  Proof.
    intro.
    apply of_to_eff0 in H.
    simpl in H.
    rewrite - H.
    eexists.
    split => //.
    rewrite - (to_of_eff0 (susE vs i vh)).
    unfold of_eff0. done.
  Qed.

  Lemma to_eff_sus_local es1 vs i bef m es vh aft :
    iris.to_eff0 es1 = Some (susE vs i (SuFrame bef m es vh aft)) ->
    exists LI, es1 = (fmap (fun v => AI_const v) bef) ++ [AI_frame m es LI] ++ aft
          /\ iris.to_eff0 LI = Some (susE vs i vh).
  Proof.
    intro.
    apply of_to_eff0 in H.
    simpl in H.
    rewrite - H.
    eexists.
    split => //.
    rewrite - (to_of_eff0 (susE vs i vh)).
    unfold of_eff0. done.
  Qed.

  
  Lemma to_eff_sus_prompt es1 vs i bef m es vh aft :
    iris.to_eff0 es1 = Some (susE vs i (SuPrompt bef m es vh aft)) ->
    exists LI, es1 = (fmap (fun v => AI_const v) bef) ++ [AI_prompt m (map (continuation_clause_of_suselt i) es) LI] ++ aft
          /\ iris.to_eff0 LI = Some (susE vs i vh).
  Proof.
    intro.
    apply of_to_eff0 in H.
    simpl in H.
    rewrite - H.
    eexists.
    split => //.
    rewrite - (to_of_eff0 (susE vs i vh)).
    unfold of_eff0. 
    done.
  Qed.

   Lemma to_eff_sus_handler es1 vs i bef es vh aft :
    iris.to_eff0 es1 = Some (susE vs i (SuHandler bef es vh aft)) ->
    exists LI, es1 = (fmap (fun v => AI_const v) bef) ++ [AI_handler es LI] ++ aft
          /\ iris.to_eff0 LI = Some (susE vs i vh).
  Proof.
    intro.
    apply of_to_eff0 in H.
    simpl in H.
    rewrite - H.
    eexists.
    split => //.
    rewrite - (to_of_eff0 (susE vs i vh)).
    done.
  Qed.

    Lemma to_eff_sw_base es1 vs i n l tf x:
    iris.to_eff0 es1 = Some (swE vs i tf x (SwBase n l)) ->
    es1 = (fmap (fun v => AI_const v) n) ++ [AI_switch_desugared vs i tf x] ++ l.
  Proof.
    intro.
    apply of_to_eff0 in H.
    simpl in H. by rewrite H.
  Qed.

  Lemma to_eff_sw_rec es1 vs k tf i bef m es vh aft :
    iris.to_eff0 es1 = Some (swE vs k tf i (SwLabel bef m es vh aft)) ->
    exists LI, es1 = (fmap (fun v => AI_const v) bef) ++ [AI_label m es LI] ++ aft
          /\ iris.to_eff0 LI = Some (swE vs k tf i vh).
  Proof.
    intro.
    apply of_to_eff0 in H.
    simpl in H.
    rewrite - H.
    eexists.
    split => //.
    rewrite - (to_of_eff0 (swE vs k tf i vh)).
    unfold of_eff0. done.
  Qed.

    Lemma to_eff_sw_local es1 vs k tf i bef m es vh aft :
    iris.to_eff0 es1 = Some (swE vs k tf i (SwFrame bef m es vh aft)) ->
    exists LI, es1 = (fmap (fun v => AI_const v) bef) ++ [AI_frame m es LI] ++ aft
          /\ iris.to_eff0 LI = Some (swE vs k tf i vh).
  Proof.
    intro.
    apply of_to_eff0 in H.
    simpl in H.
    rewrite - H.
    eexists.
    split => //.
    rewrite - (to_of_eff0 (swE vs k tf i vh)).
    unfold of_eff0. done.
  Qed.

  
  Lemma to_eff_sw_prompt es1 vs k tf i bef m es vh aft :
    iris.to_eff0 es1 = Some (swE vs k tf i (SwPrompt bef m es vh aft)) ->
    exists LI, es1 = (fmap (fun v => AI_const v) bef) ++ [AI_prompt m (map (continuation_clause_of_swelt i) es) LI] ++ aft
          /\ iris.to_eff0 LI = Some (swE vs k tf i vh).
  Proof.
    intro.
    apply of_to_eff0 in H.
    simpl in H.
    rewrite - H.
    eexists.
    split => //.
    rewrite - (to_of_eff0 (swE vs k tf i vh)).
    unfold of_eff0. 
    done.
  Qed.

   Lemma to_eff_sw_handler es1 vs k tf i bef es vh aft :
    iris.to_eff0 es1 = Some (swE vs k tf i (SwHandler bef es vh aft)) ->
    exists LI, es1 = (fmap (fun v => AI_const v) bef) ++ [AI_handler es LI] ++ aft
          /\ iris.to_eff0 LI = Some (swE vs k tf i vh).
  Proof.
    intro.
    apply of_to_eff0 in H.
    simpl in H.
    rewrite - H.
    eexists.
    split => //.
    rewrite - (to_of_eff0 (swE vs k tf i vh)).
    done.
  Qed.
  
    Lemma to_eff_thr_base es1 vs k i n l:
    iris.to_eff0 es1 = Some (thrE vs k i (ExBase n l)) ->
    es1 = (fmap (fun v => AI_const v) n) ++ [AI_throw_ref_desugared vs k i] ++ l.
  Proof.
    intro.
    apply of_to_eff0 in H.
    simpl in H. by rewrite H.
  Qed.

  Lemma to_eff_thr_rec es1 vs k i bef m es vh aft :
    iris.to_eff0 es1 = Some (thrE vs k i (ExLabel bef m es vh aft)) ->
    exists LI, es1 = (fmap (fun v => AI_const v) bef) ++ [AI_label m es LI] ++ aft
          /\ iris.to_eff0 LI = Some (thrE vs k i vh).
  Proof.
    intro.
    apply of_to_eff0 in H.
    simpl in H.
    rewrite - H.
    eexists.
    split => //.
    rewrite - (to_of_eff0 (thrE vs k i vh)).
    unfold of_eff0. done.
  Qed.

    Lemma to_eff_thr_local es1 vs k i bef m es vh aft :
    iris.to_eff0 es1 = Some (thrE vs k i (ExFrame bef m es vh aft)) ->
    exists LI, es1 = (fmap (fun v => AI_const v) bef) ++ [AI_frame m es LI] ++ aft
          /\ iris.to_eff0 LI = Some (thrE vs k i vh).
  Proof.
    intro.
    apply of_to_eff0 in H.
    simpl in H.
    rewrite - H.
    eexists.
    split => //.
    rewrite - (to_of_eff0 (thrE vs k i vh)).
    unfold of_eff0. done.
  Qed.

  
  Lemma to_eff_thr_prompt es1 vs k i bef m es vh aft :
    iris.to_eff0 es1 = Some (thrE vs k i (ExPrompt bef m es vh aft)) ->
    exists LI, es1 = (fmap (fun v => AI_const v) bef) ++ [AI_prompt m es LI] ++ aft
          /\ iris.to_eff0 LI = Some (thrE vs k i vh).
  Proof.
    intro.
    apply of_to_eff0 in H.
    simpl in H.
    rewrite - H.
    eexists.
    split => //.
    rewrite - (to_of_eff0 (thrE vs k i vh)).
    unfold of_eff0. 
    done.
  Qed.

   Lemma to_eff_thr_handler es1 vs k i bef es vh aft :
    iris.to_eff0 es1 = Some (thrE vs k i (ExHandler bef es vh aft)) ->
    exists LI, es1 = (fmap (fun v => AI_const v) bef) ++ [AI_handler (map (exception_clause_of_exnelt i) es) LI] ++ aft
          /\ iris.to_eff0 LI = Some (thrE vs k i vh).
  Proof.
    intro.
    apply of_to_eff0 in H.
    simpl in H.
    rewrite - H.
    eexists.
    split => //.
    rewrite - (to_of_eff0 (thrE vs k i vh)).
    done.
  Qed.

  Lemma to_val_br_eq vs j es0 :
    iris.to_val0 (v_to_e_list vs ++ [AI_basic (BI_br j)] ++ es0) = Some (brV (VH_base j vs es0)).
  Proof.
    induction vs ; unfold iris.to_val0 => //=.
    - rewrite merge_br flatten_simplify => //.
    - rewrite merge_prepend.
      unfold iris.to_val0 in IHvs.
      destruct (merge_values $ map _ _ ) => //.
      inversion IHvs; subst => //=.
      destruct a => //=.
      destruct v => //=. 
  Qed.

  Lemma to_val_ret_eq vs es0 :
    iris.to_val0 (v_to_e_list vs ++ [AI_basic BI_return] ++ es0) = Some (retV (SH_base vs es0)).
  Proof.
    induction vs; unfold iris.to_val0 => /=.
    rewrite merge_return flatten_simplify => //.
    rewrite merge_prepend.
    unfold iris.to_val0 in IHvs.
    destruct (merge_values $ map _ _) => //=.
    inversion IHvs => //.
    destruct a => //=. destruct v0 => //=. 
  Qed.


  Lemma to_val_call_host_eq vs es0 tf h vcs:
    iris.to_val0 (v_to_e_list vs ++ [AI_call_host tf h vcs] ++ es0) = Some (callHostV tf h vcs ((LL_base vs es0))).
  Proof.
    induction vs; unfold iris.to_val0 => /=.
    rewrite merge_call_host flatten_simplify => //.
    rewrite merge_prepend.
    unfold iris.to_val0 in IHvs.
    destruct (merge_values $ map _ _) => //=.
    inversion IHvs => //.
    destruct a => //=. destruct v0 => //=. 
  Qed.

   Lemma to_eff_sus_eq bef vs i es0 :
    iris.to_eff0 (v_to_e_list bef ++ [AI_suspend_desugared vs i] ++ es0) = Some (susE vs i (SuBase bef es0)).
  Proof.
    induction bef ; unfold iris.to_eff0 => //=.
    - rewrite merge_suspend flatten_simplify => //.
    - rewrite merge_prepend.
      unfold iris.to_eff0 in IHbef.
      destruct (merge_values $ map _ _ ) => //.
      inversion IHbef; subst => //=.
      destruct a => //=.
      destruct v => //=. 
  Qed.

     Lemma to_eff_sw_eq bef vs k tf i es0 :
    iris.to_eff0 (v_to_e_list bef ++ [AI_switch_desugared vs k tf i] ++ es0) = Some (swE vs k tf i (SwBase bef es0)).
  Proof.
    induction bef ; unfold iris.to_eff0 => //=.
    - rewrite merge_switch flatten_simplify => //.
    - rewrite merge_prepend.
      unfold iris.to_eff0 in IHbef.
      destruct (merge_values $ map _ _ ) => //.
      inversion IHbef; subst => //=.
      destruct a => //=.
      destruct v => //=. 
  Qed.

     Lemma to_eff_thr_eq bef vs k i es0 :
    iris.to_eff0 (v_to_e_list bef ++ [AI_throw_ref_desugared vs k i] ++ es0) = Some (thrE vs k i (ExBase bef es0)).
  Proof.
    induction bef ; unfold iris.to_eff0 => //=.
    - rewrite merge_throw flatten_simplify => //.
    - rewrite merge_prepend.
      unfold iris.to_eff0 in IHbef.
      destruct (merge_values $ map _ _ ) => //.
      inversion IHbef; subst => //=.
      destruct a => //=.
      destruct v => //=. 
  Qed.

  Lemma first_effect es :
    is_Some $ iris.to_eff0 es ->
    exists vs e es', const_list vs /\ is_Some $ to_eff0 [e] /\ es = vs ++ e :: es'.
  Proof.
    induction es; intros [eff Hes]; first by inversion Hes.
    unfold to_eff0 in Hes.
    destruct a => //=; try by rewrite merge_notval in Hes.
    { destruct b => //=; try by rewrite merge_notval in Hes.
      { rewrite merge_br in Hes => //. } 
      { rewrite merge_return in Hes => //. } 
      all: rewrite merge_prepend in Hes.
      all: simpl in Hes.
      all: fold (map to_val_instr es) in Hes.
      all: destruct (merge_values _) eqn:Hmerge => //.
      by destruct v0 => //.
      2: by destruct v.
      all: edestruct IHes as (vs' & e' & es' & Hvs' & He' & Hes').
      1,3: by unfold to_eff0; rewrite Hmerge. 
      all: eexists (_ :: vs'), e', es'.
      all: repeat split => //=.
      2,4: by rewrite Hes'.
      all: done.
    }
    { rewrite merge_trap flatten_simplify in Hes => //.
      destruct es => //=. }
    1-3: rewrite merge_prepend in Hes.
    1-3: simpl in Hes.
    1-3: fold (map to_val_instr es) in Hes.
    1-3: destruct (merge_values _) eqn:Hmerge => //.
    1,3,5: by destruct v.
    1-3: edestruct IHes as (vs' & e' & es' & Hvs' & He' & Hes').
    1,3,5: by unfold to_eff0; rewrite Hmerge.
    1-3: eexists (_ :: vs'), e', es'.
    1-3: repeat split => //=.
    2,4,6: by rewrite Hes'.
    1-3: done.
    1-3: eexists [], _, es.
    1-3: repeat split => //=.
    1-3: done.
    5: rewrite merge_call_host in Hes => //.
    all: simpl in Hes.
    all: destruct (merge_values $ map _ _) eqn:Hmerge => //.
    1,4,7,10: destruct v => //=.
    all: try by rewrite merge_notval in Hes.
    all: try rewrite merge_br in Hes => //.
    all: try rewrite merge_return in Hes => //.
    all: try rewrite merge_call_host in Hes => //.
    destruct i => //.
    2: destruct (vh_decrease _) => //.
    all: try rewrite merge_notval in Hes => //.
    rewrite merge_br in Hes => //.
    all: eexists [], _, es.
    all: repeat split => //=.
    all: unfold to_eff0 => //=.
    all: rewrite Hmerge => //=. 
    all: destruct e => //=.
    destruct (exnelts_of_exception_clauses _ _) => //.
    all: try destruct (suselts_of_continuation_clauses _ _) => //.
    all: try destruct (swelts_of_continuation_clauses _ _) => //.
    all: by rewrite merge_notval in Hes.
Qed. 
    

  Lemma first_non_value es :
    iris.to_val0 es = None ->
    exists vs e es', const_list vs /\ (to_val0 [e] = None \/ e = AI_trap) /\ es = vs ++ e :: es'.
  Proof.
    intros Hes.
    induction es ; first by inversion Hes.
    remember a as a'.
    destruct a ; try by exists [], a', es ; repeat split => //= ; left ; rewrite Heqa'.
    { subst ; remember b as b'.
      destruct b ;
        try by exists [], (AI_basic b'), es ; repeat split => //= ; left ; rewrite Heqb'; simplify_eq.
      - unfold iris.to_val0 in Hes ; simpl in Hes.
        subst. rewrite merge_br flatten_simplify in Hes => //.
      - unfold iris.to_val0 in Hes ; simpl in Hes ; subst.
        by rewrite merge_return flatten_simplify in Hes.
      - subst. unfold iris.to_val0 in Hes ; simpl in Hes.
        rewrite merge_prepend in Hes.
        unfold iris.to_val0 in IHes.
        destruct (merge_values $ map _ _) eqn:Hmerge => //.
        + destruct v0 => //.
          assert (to_val0 es = Some trapV) ;
            first by unfold to_val, iris.to_val0 ; rewrite Hmerge.
          apply to_val_trap_is_singleton in H as ->.
          exists [AI_basic $ BI_const v], AI_trap, [] ; repeat split => //.
          by right.
        + assert (is_Some (to_eff0 es)); first by unfold to_eff0; rewrite Hmerge.
          apply first_effect in H as (vs & e' & es' & Hvs & [? Heff] & ->).
          exists (AI_basic (BI_const v) :: vs), e', es'.
          repeat split => //. left.
          unfold to_val, iris.to_val0. unfold to_eff0 in Heff.
          destruct (merge_values $ map _ [e']) => //.
        + destruct IHes as (vs & e0 & es' & Hvs & He & Hes0) => //.
          exists (AI_basic (BI_const v) :: vs), e0, es' ;
            repeat split => //.
          by rewrite Hes0.
      - subst. unfold iris.to_val0 in Hes ; simpl in Hes.
        rewrite merge_prepend in Hes.
        unfold iris.to_val0 in IHes.
        destruct (merge_values $ map _ _) eqn:Hmerge => //.
        + destruct v => //.
          assert (to_val0 es = Some trapV) ;
            first by unfold to_val, iris.to_val0 ; rewrite Hmerge.
          apply to_val_trap_is_singleton in H as ->.
          exists [AI_basic $ BI_ref_null r], AI_trap, [] ; repeat split => //.
          by right.
        + assert (is_Some (to_eff0 es)); first by unfold to_eff0; rewrite Hmerge.
          apply first_effect in H as (vs & e' & es' & Hvs & [? Heff] & ->).
          exists (AI_basic (BI_ref_null r) :: vs), e', es'.
          repeat split => //. left.
          unfold to_val, iris.to_val0. unfold to_eff0 in Heff.
          destruct (merge_values $ map _ [e']) => //.
        + destruct IHes as (vs & e0 & es' & Hvs & He & Hes0) => //.
          exists (AI_basic (BI_ref_null r) :: vs), e0, es' ;
            repeat split => //.
          by rewrite Hes0.
    }
    - subst. exists [], AI_trap, es. repeat split => //=. by right.
    - subst. unfold iris.to_val0 in Hes ; simpl in Hes.
      rewrite merge_prepend in Hes.
      unfold iris.to_val0 in IHes.
      destruct (merge_values $ map _ _) eqn:Hmerge => //.
      + destruct v => //.
        assert (to_val0 es = Some trapV) ;
          first by unfold to_val, iris.to_val0 ; rewrite Hmerge.
        apply to_val_trap_is_singleton in H as ->.
        eexists [_], AI_trap, [] ; repeat split => //.
        done. by right.
      + assert (is_Some (to_eff0 es)); first by unfold to_eff0; rewrite Hmerge.
        apply first_effect in H as (vs & e' & es' & Hvs & [? Heff] & ->).
        eexists (_ :: vs), e', es'.
        repeat split => //. done. left.
        unfold to_val, iris.to_val0. unfold to_eff0 in Heff.
        destruct (merge_values $ map _ [e']) => //.
      + destruct IHes as (vs & e0 & es' & Hvs & He & ->) => //.
        eexists (_ :: vs), e0, es' ;
          repeat split => //.
        done.
    - subst. unfold iris.to_val0 in Hes ; simpl in Hes.
      rewrite merge_prepend in Hes.
      unfold iris.to_val0 in IHes.
      destruct (merge_values $ map _ _) eqn:Hmerge => //.
      + destruct v => //.
        assert (to_val0 es = Some trapV) ;
          first by unfold to_val, iris.to_val0 ; rewrite Hmerge.
        apply to_val_trap_is_singleton in H as ->.
        eexists [_], AI_trap, [] ; repeat split => //.
        done. by right.
      + assert (is_Some (to_eff0 es)); first by unfold to_eff0; rewrite Hmerge.
        apply first_effect in H as (vs & e' & es' & Hvs & [? Heff] & ->).
        eexists (_ :: vs), e', es'.
        repeat split => //. done. left.
        unfold to_val, iris.to_val0. unfold to_eff0 in Heff.
        destruct (merge_values $ map _ [e']) => //.
      + destruct IHes as (vs & e00 & es' & Hvs & He & ->) => //.
        eexists (_ :: vs), e00, es' ;
          repeat split => //.
        done.
    - subst. unfold iris.to_val0 in Hes ; simpl in Hes.
      rewrite merge_prepend in Hes.
      unfold iris.to_val0 in IHes.
      destruct (merge_values $ map _ _) eqn:Hmerge => //.
      + destruct v => //.
        assert (to_val0 es = Some trapV) ;
          first by unfold to_val, iris.to_val0 ; rewrite Hmerge.
        apply to_val_trap_is_singleton in H as ->.
        eexists [_], AI_trap, [] ; repeat split => //.
        done. by right.
      + assert (is_Some (to_eff0 es)); first by unfold to_eff0; rewrite Hmerge.
        apply first_effect in H as (vs & e' & es' & Hvs & [? Heff] & ->).
        eexists (_ :: vs), e', es'.
        repeat split => //. done. left.
        unfold to_val, iris.to_val0. unfold to_eff0 in Heff.
        destruct (merge_values $ map _ [e']) => //.
      + destruct IHes as (vs & e0 & es' & Hvs & He & ->) => //.
        eexists (_ :: vs), e0, es' ;
          repeat split => //.
        done.
    - subst. exists [], (AI_handler l l0), es.
      repeat split => //=. left.
      unfold to_val, iris.to_val0 => /=.
      unfold iris.to_val0 in Hes; simpl in Hes.
      destruct (merge_values $ map _ _) eqn:Hmerge => //.
      + destruct v => //=.
        * rewrite merge_br in Hes => //.
        * rewrite merge_return in Hes => //.
        * rewrite merge_call_host in Hes => //.
      + destruct e => //=.
        destruct (exnelts_of_exception_clauses _ _) => //.
    - subst. eexists [], _, es.
      repeat split => //=. left.
      unfold to_val, iris.to_val0 => /=.
      unfold iris.to_val0 in Hes; simpl in Hes.
      destruct (merge_values $ map _ _) eqn:Hmerge => //.
      + destruct v => //=.
        * rewrite merge_br in Hes => //.
        * rewrite merge_return in Hes => //.
        * rewrite merge_call_host in Hes => //.
      + destruct e => //=.
        destruct (suselts_of_continuation_clauses _ _) => //.
        destruct (swelts_of_continuation_clauses _ _) => //.
    - subst. eexists [], _, es.
      repeat split => //=. left.
      unfold to_val, iris.to_val0 => /=.
      unfold iris.to_val0 in Hes; simpl in Hes.
      destruct (merge_values $ map _ _) eqn:Hmerge => //.
      + destruct v => //=.
        * destruct i => //.
          destruct (vh_decrease _) => //.
          rewrite merge_br in Hes => //.
        * rewrite merge_return in Hes => //.
        * rewrite merge_call_host in Hes => //.
      + destruct e => //=.
    - subst. eexists [], _, es.
      repeat split => //=. left.
      unfold to_val, iris.to_val0 => /=.
      unfold iris.to_val0 in Hes; simpl in Hes.
      destruct (merge_values $ map _ _) eqn:Hmerge => //.
      + destruct v => //=.
        rewrite merge_call_host in Hes => //.
      + destruct e => //=.  
    - subst.
      by rewrite /iris.to_val0 /= merge_call_host flatten_simplify in Hes.
  Qed.

  Lemma to_val_None_first_singleton es :
    (const_list es = false) ->
    (es <> [AI_trap]) ->
    ∃ vs e es', es = vs ++ [e] ++ es' ∧ const_list vs ∧
                  ((to_val0 ([e]) = None)
                   ∨ (e = AI_trap ∧ (vs ≠ [] ∨ es' ≠ []))
                   ∨ (∃ n, e = (AI_basic (BI_br n)))
                   ∨ (e = (AI_basic BI_return))
                   \/ (∃ tf h vcs, e = (AI_call_host tf h vcs))
                   \/ (exists n es LI, e = AI_label n es LI
                                 /\ ((exists i (vh: valid_holed i), to_val0 LI = Some (brV vh))
                                    \/ (exists sh, to_val0 LI = Some (retV sh))
                                    \/ (exists tf h vcs sh, to_val0 LI = Some (callHostV tf h vcs sh))))
                   \/ (exists n es LI, e = AI_prompt n es LI
                                 /\ ((exists i (vh: valid_holed i), to_val0 LI = Some (brV vh))
                                    \/ (exists sh, to_val0 LI = Some (retV sh))
                                    \/ (exists tf h vcs sh, to_val0 LI = Some (callHostV tf h vcs sh))))
                   \/ (exists es LI, e = AI_handler es LI
                                 /\ ((exists i (vh: valid_holed i), to_val0 LI = Some (brV vh))
                                    \/ (exists sh, to_val0 LI = Some (retV sh))
                                    \/ (exists tf h vcs sh, to_val0 LI = Some (callHostV tf h vcs sh))))
                  \/ (exists n f LI tf h vcs sh, e = AI_frame n f LI /\ to_val0 LI = Some (callHostV tf h vcs sh)))
                   .
  Proof.
    induction es;intros Hes1 Hes2.
    { exfalso. simpl in Hes1. eauto. }
    destruct (to_val0 [a]) eqn:Ha.
    - destruct v.
      + destruct (to_val0 es) eqn:Hes.
        * unfold to_val in Hes.
          unfold to_val in Ha.
          destruct v. 
          -- eapply to_val_cat_inv in Hes;[|apply Ha].
             rewrite -separate1 in Hes. unfold to_val in Hes1.
             exfalso. by erewrite to_val_const_list in Hes1. 
          -- apply to_val_trap_is_singleton in Hes as ->.
             apply to_val_const_list in Ha.
             exists [a],AI_trap,[]. cbn. repeat split;auto. 
          -- destruct lh.
             ++ apply to_val_br_base in Hes as ->.
                rewrite to_e_list_fmap.
                rewrite list_extra.cons_app app_assoc.
                apply to_val_const_list in Ha as [? ->]%const_es_exists.
                erewrite v_to_e_cat. eexists _,_,_. split;eauto.
                split;[apply v_to_e_is_const_list|]. right. right. left. eauto.
             ++ apply to_val_br_rec in Hes as (LI & -> & Htv).
                rewrite to_e_list_fmap.
                rewrite list_extra.cons_app app_assoc.
                apply to_val_const_list in Ha as [? ->]%const_es_exists.
                erewrite v_to_e_cat. eexists _,_,_. split ; eauto.
                split ; [apply v_to_e_is_const_list |].
                do 5 right. left. eexists _,_,_ ; split => //=.
                left. eauto.
             ++ apply to_val_br_prompt in Hes as (LI & -> & Htv).
                rewrite to_e_list_fmap.
                rewrite list_extra.cons_app app_assoc.
                apply to_val_const_list in Ha as [? ->]%const_es_exists.
                erewrite v_to_e_cat. eexists _,_,_. split; eauto.
                split; first apply v_to_e_is_const_list.
                do 6 right. left. eexists _,_,_. split => //=.
                left. eauto.
             ++ apply to_val_br_handler in Hes as (LI & -> & Htv).
                rewrite to_e_list_fmap.
                rewrite list_extra.cons_app app_assoc.
                apply to_val_const_list in Ha as [? ->]%const_es_exists.
                erewrite v_to_e_cat. eexists _,_,_. split; eauto.
                split; first apply v_to_e_is_const_list. 
                do 7 right. left. eexists _,_. split; eauto.
          -- destruct s.
             ++ apply to_val_ret_base in Hes as ->.
                rewrite to_e_list_fmap.
                rewrite list_extra.cons_app app_assoc.
                apply to_val_const_list in Ha as [? ->]%const_es_exists.
                erewrite v_to_e_cat.
                eexists _,_,_. split;eauto.
                split;[apply v_to_e_is_const_list|]. right. right. right. eauto.
             ++ apply to_val_ret_rec in Hes as (LI & -> & Htv).
                rewrite to_e_list_fmap.
                rewrite list_extra.cons_app app_assoc.
                apply to_val_const_list in Ha as [? ->]%const_es_exists.
                erewrite v_to_e_cat.
                eexists _,_,_. split ; eauto.
                split;[apply v_to_e_is_const_list|]. do 5 right.
                left.
                eexists _,_,_. split => //=.
                right. eauto.
             ++ apply to_val_ret_prompt in Hes as (LI & -> & Htv).
                rewrite to_e_list_fmap.
                rewrite list_extra.cons_app app_assoc.
                apply to_val_const_list in Ha as [? ->]%const_es_exists.
                erewrite v_to_e_cat.
                eexists _,_,_. split ; eauto.
                split;[apply v_to_e_is_const_list|]. do 6 right.
                left.
                eexists _,_,_. split => //=.
                right. eauto.
             ++ apply to_val_ret_handler in Hes as (LI & -> & Htv).
                rewrite to_e_list_fmap.
                rewrite list_extra.cons_app app_assoc.
                apply to_val_const_list in Ha as [? ->]%const_es_exists.
                erewrite v_to_e_cat.
                eexists _,_,_. split ; eauto.
                split;[apply v_to_e_is_const_list|]. do 7 right.
                left.
                eexists _,_. split => //=.
                right. eauto.
          -- destruct l1. 
             ++ apply to_val_call_host_base in Hes as ->.
                rewrite to_e_list_fmap.
                rewrite list_extra.cons_app app_assoc.
                apply to_val_const_list in Ha as [? ->]%const_es_exists.
                erewrite v_to_e_cat.
                eexists _,_,_. split;eauto.
                split;[apply v_to_e_is_const_list|]. right. right. right. right. left. eauto.
             ++ apply to_val_call_host_rec_label in Hes as (LI & -> & Htv).
                rewrite to_e_list_fmap.
                rewrite list_extra.cons_app app_assoc.
                apply to_val_const_list in Ha as [? ->]%const_es_exists.
                erewrite v_to_e_cat.
                eexists _,_,_. split ; eauto.
                split;[apply v_to_e_is_const_list|]. do 5 right.  left.
                eexists _,_,_. split => //=.
                right. right.  by repeat eexists.
             ++ apply to_val_call_host_rec_local in Hes as (LI & -> & Htv).
                rewrite list_extra.cons_app app_assoc.
                apply to_val_const_list in Ha as [? ->]%const_es_exists.
                erewrite v_to_e_cat. 
                eexists _,_,_. split ; eauto.
                split ; first apply v_to_e_is_const_list.
                do 8 right. eexists _,_,_,_,_,_,_. split => //=.
             ++ apply to_val_call_host_rec_prompt in Hes as (LI & -> & Htv).
                rewrite to_e_list_fmap.
                rewrite list_extra.cons_app app_assoc.
                apply to_val_const_list in Ha as [? ->]%const_es_exists.
                erewrite v_to_e_cat.
                eexists _,_,_. split ; eauto.
                split;[apply v_to_e_is_const_list|]. do 6 right.  left.
                eexists _,_,_. split => //=.
                right. right.  by repeat eexists.
             ++ apply to_val_call_host_rec_handler in Hes as (LI & -> & Htv).
                rewrite to_e_list_fmap.
                rewrite list_extra.cons_app app_assoc.
                apply to_val_const_list in Ha as [? ->]%const_es_exists.
                erewrite v_to_e_cat.
                eexists _,_,_. split ; eauto.
                split;[apply v_to_e_is_const_list|]. do 7 right.  left.
                eexists _,_. split => //=.
                right. right.  by repeat eexists.
        * destruct IHes as (vs & e & es' & Heq & Hconst & HH);auto.
          destruct (const_list es) eqn:Hconst => //.
          apply const_list_to_val in Hconst as (? & ? & ?).
          unfold to_val in Hes ; congruence.
          intro. rewrite H in Hes.
          unfold to_val, iris.to_val0 in Hes ; done.
          apply to_val_const_list in Ha.
          destruct HH as [Hnone | [[-> Hne] | [[? Hne] | Hne]]].
          -- exists (a::vs),e,es'. subst. split;auto. split;[|left;auto].
             rewrite separate1. apply const_list_app. auto. 
          -- exists (a::vs),AI_trap,es'. subst. split;auto.
             split;[|right;auto]. rewrite separate1.
             apply const_list_app. auto. 
          -- subst. rewrite separate1 app_assoc.
             eexists _,_,_. split;eauto.
             split;[apply const_list_app;auto|].
             right;right;left. eauto. 
          -- subst. rewrite separate1 app_assoc.
             eexists _,_,_. split;eauto. split;[apply const_list_app;auto|].
             right;right;right. eauto. 
      + unfold to_val in Ha.
        apply to_val_trap_is_singleton in Ha as Heq.
        simplify_eq.
        unfold to_val in Hes1.
        unfold to_val in Hes2.
        destruct es => //.
        exists [],AI_trap,(a :: es).
        repeat split;auto. 
      + destruct a;try done. destruct b;try done.
        * unfold to_val, iris.to_val0 in Ha ; simpl in Ha.
          inversion Ha.
          apply Eqdep.EqdepTheory.inj_pair2 in H1 ; subst.
          exists [], (AI_basic (BI_br i)), es.
          repeat split => //=.
          right ; right ; left. eauto.
        * unfold to_val, iris.to_val0 in Ha. simpl in Ha.
          destruct (merge_values $ map _ _) eqn:Hmerge => //.
          -- destruct v => //.
             inversion Ha.
             destruct H0.
             apply Eqdep.EqdepTheory.inj_pair2 in H1 ; subst.
             eexists [], _, es.
             repeat split => //.
             do 7 right. left.
             eexists _,_ ; split => //.
             left.
             unfold to_val, iris.to_val0.
             rewrite Hmerge. eauto.
          -- destruct e => //.
             destruct (exnelts_of_exception_clauses _ _) => //.
        * unfold to_val, iris.to_val0 in Ha. simpl in Ha.
          destruct (merge_values $ map _ _) eqn:Hmerge => //.
          -- destruct v => //.
             inversion Ha.
             destruct H0.
             apply Eqdep.EqdepTheory.inj_pair2 in H1 ; subst.
             eexists [], _, es.
             repeat split => //.
             do 6 right. left.
             eexists _,_,_ ; split => //.
             left.
             unfold to_val, iris.to_val0.
             rewrite Hmerge. eauto.
          -- destruct e => //.
             destruct (suselts_of_continuation_clauses _ _) => //.
             destruct (swelts_of_continuation_clauses _ _) => //. 
        * unfold to_val, iris.to_val0 in Ha. simpl in Ha.
          destruct (merge_values $ map _ _) eqn:Hmerge => //.
          -- destruct v => //.
             destruct i0 => //.
             destruct (vh_decrease _) => //. 
             inversion Ha.
             destruct H0.
             apply Eqdep.EqdepTheory.inj_pair2 in H1 ; subst.
             eexists [], _, es.
             repeat split => //.
             do 5 right. left.
             eexists _,_,_ ; split => //.
             left.
             unfold to_val, iris.to_val0.
             rewrite Hmerge. eauto.
          -- destruct e => //.   
        * unfold to_val, iris.to_val0 in Ha ; simpl in Ha.
          destruct (merge_values $ map _ _) => //.
          destruct v => //.
          destruct e => //. 
      + destruct a;try done. destruct b;try done.
        * unfold to_val, iris.to_val0 in Ha ; simpl in Ha.
          inversion Ha ; subst.
          exists [], (AI_basic BI_return), es.
          repeat split => //=.
          right; right; right ; left ; eauto.
        * unfold to_val, iris.to_val0 in Ha ; simpl in Ha.
          destruct (merge_values $ map _ _) eqn:Hmerge => //.
          -- destruct v => //.
             inversion Ha ; subst.
             eexists [], _, es.
             repeat split => //.
             do 7 right. left.
             repeat eexists => //=. 
             right.
             unfold to_val, iris.to_val0.
             rewrite Hmerge ; eauto.
          -- destruct e => //.
             destruct (exnelts_of_exception_clauses _ _) => //.
        * unfold to_val, iris.to_val0 in Ha ; simpl in Ha.
          destruct (merge_values $ map _ _) eqn:Hmerge => //.
          -- destruct v => //.
             inversion Ha ; subst.
             eexists [], _, es.
             repeat split => //.
             do 6 right. left.
             repeat eexists => //=. 
             right.
             unfold to_val, iris.to_val0.
             rewrite Hmerge ; eauto.
          -- destruct e => //.
             destruct (suselts_of_continuation_clauses _ _) => //.
             destruct (swelts_of_continuation_clauses _ _) => //.
        * unfold to_val, iris.to_val0 in Ha ; simpl in Ha.
          destruct (merge_values $ map _ _) eqn:Hmerge => //.
          -- destruct v => //.
             destruct i => //.
             destruct (vh_decrease _) => //. 
             inversion Ha ; subst.
             eexists [], _, es.
             repeat split => //.
             do 5 right. left.
             repeat eexists => //=. 
             right.
             unfold to_val, iris.to_val0.
             rewrite Hmerge ; eauto.
          -- destruct e => //.
        * unfold to_val, iris.to_val0 in Ha ; simpl in Ha.
          destruct (merge_values $ map _ _) => //.
          destruct v => //.
          destruct e => //. 
      + destruct a;try done. destruct b;try done.
        * unfold to_val, iris.to_val0 in Ha ; simpl in Ha.
          destruct (merge_values $ map _ _) eqn:Hmerge => //.
          -- destruct v => //.
             inversion Ha ; subst.
             eexists [], _, es.
             repeat split => //.
             do 7 right. left.
             repeat eexists => //=. 
             right. right.
             unfold to_val, iris.to_val0.
             rewrite Hmerge ; eauto.
          -- destruct e => //=.
             destruct (exnelts_of_exception_clauses _ _) => //.
        * unfold to_val, iris.to_val0 in Ha ; simpl in Ha.
          destruct (merge_values $ map _ _) eqn:Hmerge => //.
          -- destruct v => //.
             inversion Ha ; subst.
             eexists [], _, es.
             repeat split => //.
             do 6 right. left.
             repeat eexists => //=. 
             right. right.
             unfold to_val, iris.to_val0.
             rewrite Hmerge ; eauto.
          -- destruct e => //=.
             destruct (suselts_of_continuation_clauses _ _) => //.
             destruct (swelts_of_continuation_clauses _ _) => //.
        * unfold to_val, iris.to_val0 in Ha ; simpl in Ha.
          destruct (merge_values $ map _ _) eqn:Hmerge => //.
          -- destruct v => //.
             destruct i => //.
             destruct (vh_decrease _) => //.
             inversion Ha ; subst.
             eexists [], _, es.
             repeat split => //.
             do 5 right. left.
             repeat eexists => //=. 
             right. right.
             unfold to_val, iris.to_val0.
             rewrite Hmerge ; eauto.
          -- destruct e => //=.
        * unfold to_val, iris.to_val0 in Ha ; simpl in Ha.
          destruct (merge_values $ map _ _) eqn:Hmerge => //.
          destruct v => //.
          eexists [], (AI_frame _ _ _), es.
          repeat split => //.
          do 8 right => //=.
          repeat eexists.
          unfold to_val, iris.to_val0.
          rewrite Hmerge => //.
          destruct e => //. 
        * unfold to_val, iris.to_val0 in Ha ; simpl in Ha.
          inversion Ha ; subst.
          eexists [], (AI_call_host _ _ _), es.
          repeat split => //=.
          right; right; right ; right ; left ; eauto.
    - exists [],a,es. auto. 
  Qed.

  Lemma const_list_snoc_eq3 es'' :
    forall vs es ves e es',
      const_list ves ->
      const_list vs ->
      es ≠ [] ->
      (const_list es = false) ->
      (es <> [AI_trap]) ->
      (is_const e = false ) ->
      (vs ++ es ++ es')%SEQ = ves ++ [e] ++ es'' ->
      ∃ vs2 es2, ves = vs ++ vs2 ∧ es = vs2 ++ [e] ++ es2 ∧ es'' = es2 ++ es' ∧ const_list vs2.
  Proof.
    intros vs es ves e es' Hconst1 Hconst2 Hneq Hnval1 Hnval2 He Heq.
    apply to_val_None_first_singleton in Hnval2 as HH;auto.
    destruct HH as [vs' [e' [es2 [Heq' [Hconst HH]]]]].
    assert (Heqcopy:=Heq).
    rewrite Heq' in Heqcopy.
    assert (vs ++ (vs' ++ [e'] ++ es2)%list ++ es' = (vs ++ vs') ++ [e'] ++ (es2 ++ es'))%SEQ as Heq2.
    { rewrite !app_assoc. repeat erewrite app_assoc. auto. }
    rewrite Heq2 in Heqcopy. clear Heq2. unfold to_val in He. unfold to_val in HH.
    apply first_values in Heqcopy as [Heq1 [Heq2 Heq3]];auto.
    2:{ (destruct HH as [He' | [[-> _] | [[?  ->] | [-> | [ (?&?&?& ->) | [ (? & ? & ? & -> & [ (? & ? & HLI) | [[? HLI] | (?&?&?&?&HLI) ] ]) | [ (? & ? & ? & -> & [ (? & ? & HLI) | [[? HLI] | (? & ? & ? & ? & HLI) ]]) | [(? & ? & -> & [(? & ? & HLI) | [[? HLI] | (? & ? & ? & ? & HLI)]]) | (? & ? & ? & ? & ? & ? & ? & -> & HLI) ] ]]]]]]]) => //. destruct e' => //. destruct b => //. }
    2: by apply const_list_app. 
    subst e'.
    rewrite -Heq1 in Heq.
    rewrite -Heq3 in Heq.
    assert ((vs ++ vs')%SEQ ++ [e] ++ (es2 ++ es')%SEQ =
              (vs ++ (vs' ++ [e] ++ es2) ++ es')%SEQ) as Hassoc.
    { rewrite !app_assoc. repeat erewrite app_assoc. auto. }
    rewrite Hassoc in Heq;clear Hassoc.
    apply app_inv_head in Heq.
    apply app_inv_tail in Heq.
    eexists _,_. eauto.
  Qed.     

  Lemma const_list_l_snoc_eq3 es'' :
    forall vs es ves e es',
      const_list ves ->
      e ∉ vs ->
      es ≠ [] ->
      (const_list es = false) ->
      (es <> [AI_trap]) ->
      (is_const e = false ) ->
      (vs ++ es ++ es')%SEQ = ves ++ [e] ++ es'' ->
      ∃ vs2 es2, ves = vs ++ vs2 ∧ es = vs2 ++ [e] ++ es2 ∧ es'' = es2 ++ es' ∧ const_list vs2.
  Proof.
    intros vs es ves e es' Hconst1 Hnin Hneq Hnval1 Hnval2 He Heq.
    apply to_val_None_first_singleton in Hnval2 as HH;auto.
    destruct HH as [vs' [e' [es2 [Heq' [Hconst HH]]]]].
    assert (Heqcopy:=Heq).
    rewrite Heq' in Heqcopy.
    assert (vs ++ (vs' ++ [e'] ++ es2)%list ++ es' = (vs ++ vs') ++ [e'] ++ (es2 ++ es'))%SEQ as Heq2.
    { rewrite !app_assoc. repeat erewrite app_assoc. auto. }
    rewrite Heq2 in Heqcopy. clear Heq2. unfold to_val in He.
    apply first_values_elem_of in Heqcopy as [Heq1 [Heq2 Heq3]];auto.
    2:  (destruct HH as [He' | [[-> _] | [[?  ->] | [-> | [ (?&?&?& ->) | [ (? & ? & ? & -> & [ (? & ? & HLI) | [[? HLI] | (?&?&?&?&HLI) ] ]) | [ (? & ? & ? & -> & [ (? & ? & HLI) | [[? HLI] | (? & ? & ? & ? & HLI) ]]) | [(? & ? & -> & [(? & ? & HLI) | [[? HLI] | (? & ? & ? & ? & HLI)]]) | (? & ? & ? & ? & ? & ? & ? & -> & HLI) ] ]]]]]]]) => //. 
    2: destruct e' => //; destruct b => //.
    2: { apply not_elem_of_app. split;[|apply const_list_elem_of;auto]. auto. }
    2: apply const_list_elem_of;auto.
    2:  (destruct HH as [He' | [[-> _] | [[?  ->] | [-> | [ (?&?&?& ->) | [ (? & ? & ? & -> & [ (? & ? & HLI) | [[? HLI] | (?&?&?&?&HLI) ] ]) | [ (? & ? & ? & -> & [ (? & ? & HLI) | [[? HLI] | (? & ? & ? & ? & HLI) ]]) | [(? & ? & -> & [(? & ? & HLI) | [[? HLI] | (? & ? & ? & ? & HLI)]]) | (? & ? & ? & ? & ? & ? & ? & -> & HLI) ] ]]]]]]]) => //. 
    2: destruct e' => // ; destruct b => //.
    subst e'.
    rewrite -Heq1 in Heq.
    rewrite -Heq3 in Heq.
    assert ((vs ++ vs')%SEQ ++ [e] ++ (es2 ++ es')%SEQ =
              (vs ++ (vs' ++ [e] ++ es2) ++ es')%SEQ) as Hassoc.
    { rewrite !app_assoc. repeat erewrite app_assoc. auto. }
    rewrite Hassoc in Heq;clear Hassoc.
    apply app_inv_head in Heq.
    apply app_inv_tail in Heq.
    eexists _,_. eauto.    
  Qed.

  Lemma filled_is_val_imm : ∀ i lh es LI vals,
      iris.to_val0 LI = Some (immV vals) ->
      lfilled i lh es LI ->
      ∃ vs es', i = 0 ∧ lh = LH_base vs es' ∧ const_list vs ∧ const_list es'.
  Proof.
    move => i lh es LI vals Htv Hlf.
    apply to_val_const_list in Htv.
    specialize (lfilled_const _ _ _ _ Hlf Htv) as [-> Hconst].
    move/lfilledP in Hlf; inversion Hlf; subst; clear Hlf.
    - exists vs, es'.
      by do 2 apply const_list_app in Htv as [? Htv].
    - apply const_list_app in Htv as [? Habs] => //.
    - apply const_list_app in Htv as [? Habs] => //.
  Qed.
  
  Lemma filled_is_val_trap : ∀ i lh es LI,
      iris.to_val0 LI = Some trapV ->
      lfilled i lh es LI ->
      es ≠ [] ->
      i = 0 ∧ lh = LH_base [] [].
  Proof.
    intros i.
    destruct i;
      intros lh es LI Hval Hfill%lfilled_Ind_Equivalent Hne.
    - inversion Hfill;subst.
      all: apply to_val_trap_is_singleton in Hval.
      + destruct es,vs,es' => //=.
        destruct es => //=.
        destruct vs => //=.
        destruct vs => //=.
      + destruct bef => //=.  destruct bef => //=.
      + destruct bef => //=.  destruct bef => //=.
    - inversion Hfill;subst.
      all: apply to_val_trap_is_singleton in Hval.
      + repeat destruct vs => //=.
      + repeat destruct bef => //.
      + repeat destruct bef => //. 
  Qed.

  Lemma filled_is_val_br_base : ∀ i lh es LI j v1 e1 ,
      iris.to_val0 LI = Some (brV (VH_base j v1 e1)) ->
      lfilled i lh es LI ->
      es ≠ [] ->
      i = 0.
  Proof.
    intros i.
    destruct i;
      intros lh es LI j v1 v2 Hval Hfill%lfilled_Ind_Equivalent Hne.
    - inversion Hfill;subst;auto. 
    - inversion Hfill;subst.
      all: apply to_val_br_base in Hval.
      all: apply first_values in Hval as [? [? ?]];auto.
      all: try done.   
      all: apply v_to_e_is_const_list.
  Qed.


  Lemma filled_is_val_ret_base : ∀ i lh es LI v1 e1 ,
      iris.to_val0 LI = Some (retV (SH_base v1 e1)) ->
      lfilled i lh es LI ->
      es ≠ [] ->
      i = 0.
  Proof.
    intros i.
    destruct i;
      intros lh es LI v1 v2 Hval Hfill%lfilled_Ind_Equivalent Hne.
    - inversion Hfill;subst;auto. 
    - inversion Hfill;subst.
      all: apply to_val_ret_base in Hval.
      all: apply first_values in Hval as [? [? ?]];auto.
      all: try done.
      all: apply v_to_e_is_const_list.
  Qed.

  Lemma filled_is_val_call_host_base : ∀ i lh es LI v1 e1 tf h cvs,
      iris.to_val0 LI = Some (callHostV tf h cvs (LL_base v1 e1)) ->
      lfilled i lh es LI ->
      es ≠ [] ->
      i = 0.
  Proof.
    intros i.
    destruct i;
      intros lh es LI v1 v2 tf h cvs Hval Hfill%lfilled_Ind_Equivalent Hne.
    - inversion Hfill;subst;auto. 
    - inversion Hfill;subst.
      all: apply to_val_call_host_base in Hval.
      all: apply first_values in Hval as [? [? ?]];auto.
      all: try done. all: apply v_to_e_is_const_list.
  Qed.

   Lemma filled_is_eff_sus_base : ∀ i vs i' lh es LI bef aft ,
      iris.to_eff0 LI = Some (susE vs i' (SuBase bef aft)) ->
      lfilled i lh es LI ->
      es ≠ [] ->
      i = 0.
  Proof.
    intros i.
    destruct i;
      intros vs i' lh es LI bef aft Hval Hfill%lfilled_Ind_Equivalent Hne.
    - inversion Hfill;subst;auto. 
    - inversion Hfill;subst.
      all: apply to_eff_sus_base in Hval.
      all: apply first_values in Hval as [? [? ?]];auto.
      all: try done.   
      all: apply v_to_e_is_const_list.
  Qed.

   Lemma filled_is_eff_sw_base : ∀ i vs k tf i' lh es LI bef aft ,
      iris.to_eff0 LI = Some (swE vs k tf i' (SwBase bef aft)) ->
      lfilled i lh es LI ->
      es ≠ [] ->
      i = 0.
  Proof.
    intros i.
    destruct i;
      intros vs k tf i' lh es LI bef aft Hval Hfill%lfilled_Ind_Equivalent Hne.
    - inversion Hfill;subst;auto. 
    - inversion Hfill;subst.
      all: apply to_eff_sw_base in Hval.
      all: apply first_values in Hval as [? [? ?]];auto.
      all: try done.   
      all: apply v_to_e_is_const_list.
  Qed.

   Lemma filled_is_eff_thr_base : ∀ i vs k i' lh es LI bef aft ,
      iris.to_eff0 LI = Some (thrE vs k i' (ExBase bef aft)) ->
      lfilled i lh es LI ->
      es ≠ [] ->
      i = 0.
  Proof.
    intros i.
    destruct i;
      intros vs k i' lh es LI bef aft Hval Hfill%lfilled_Ind_Equivalent Hne.
    - inversion Hfill;subst;auto. 
    - inversion Hfill;subst.
      all: apply to_eff_thr_base in Hval.
      all: apply first_values in Hval as [? [? ?]];auto.
      all: try done.   
      all: apply v_to_e_is_const_list.
  Qed. 
  
  Lemma filled_is_val_trap_nil : ∀ i lh LI,
      iris.to_val0 LI = Some trapV ->
      lfilled i lh [] LI ->
      ∃ vs es, i = 0 ∧ lh = LH_base vs es ∧
                 ((vs = [] ∧ es = [::AI_trap])
                  ∨ (es = [] ∧ vs = [::AI_trap])).
  Proof.
    intros i.
    destruct i;
      intros lh LI Hval Hfill%lfilled_Ind_Equivalent.
    - inversion Hfill;subst.
      all: apply to_val_trap_is_singleton in Hval.
      + destruct vs,es' => //=.
        repeat destruct es' => //=.
        repeat erewrite app_nil_l in Hval. simplify_eq.
        eexists _,_. eauto.
        repeat destruct vs => //=.
        repeat erewrite app_nil_r in Hval. simplify_eq.
        eexists _,_. eauto.
        repeat destruct vs => //=.
      + destruct bef, aft => //=.
        repeat destruct aft => //=.
        repeat erewrite app_nil_l in Hval. simplify_eq.
        repeat destruct bef => //=.
        repeat erewrite app_nil_r in Hval. simplify_eq.
        repeat destruct bef => //=.
      + destruct bef, aft => //=.
        repeat destruct aft => //=.
        repeat erewrite app_nil_l in Hval. simplify_eq.
        repeat destruct bef => //=.
        repeat erewrite app_nil_r in Hval. simplify_eq.
        repeat destruct bef => //=. 
    - exfalso. inversion Hfill;subst.
      all: apply to_val_trap_is_singleton in Hval.
      repeat destruct vs => //=.
      all: repeat destruct bef => //. 
  Qed.

  Lemma to_val_nil : ∀ e,
      iris.to_val0 e = Some (immV []) -> e = [].
  Proof.
    move => e Htv.
    by apply to_val_is_immV in Htv.
  Qed.

  Lemma fill_val : ∀ l LI v1 v2 vs es' es,
      lfilled 0 (LH_base vs es') es LI ->
      iris.to_val0 LI = Some (immV l) ->
      iris.to_val0 vs = Some (immV v1) ->
      iris.to_val0 es' = Some (immV v2) ->
      ∃ vs, iris.to_val0 es = Some (immV vs) ∧ l = v1 ++ vs ++ v2.
  Proof.
    intros l LI v1 v2 vs es' es
           Hfill%lfilled_Ind_Equivalent
           HLI Hvs Hes'.
    inversion Hfill ; subst.
    specialize (to_val_const_list HLI) as Hconst.
    unfold const_list in Hconst.
    repeat rewrite forallb_app in Hconst.
    repeat apply andb_true_iff in Hconst as [? Hconst].
    apply const_list_to_val in H0 as (vs0 & Hes & _).
    eexists ; split => //.
    pose proof (to_val_cat_inv _ _ _ _ Hes Hes') as Hi.
    pose proof (to_val_cat_inv _ _ _ _ Hvs Hi) as Hl.
    inversion Hfill;subst. rewrite Hl in HLI. simplify_eq. eauto.
  Qed.

  Lemma lfilled_eq i1 i2 lh1 lh2 e1 e2 LI :
    lfilled i1 lh1 [e1] LI -> lfilled i2 lh2 [e2] LI ->
    ((is_const e1 = false ) /\ (forall a b c, e1 <> AI_label a b c) /\ (forall a b c, e1 <> AI_prompt a b c) /\ (forall a b, e1 <> AI_handler a b)) ->
    ((is_const e2 = false ) /\ (forall a b c, e2 <> AI_label a b c) /\ (forall a b c, e2 <> AI_prompt a b c) /\ (forall a b, e2 <> AI_handler a b)) ->
    i1 = i2 /\ lh1 = lh2 /\ e1 = e2.
  Proof.
    intros Hlf1 Hlf2 (Hnconst1 & Hnlab1 & Hnpr1 & Hnhan1) (Hnconst2 & Hnlab2 & Hnpr2 & Hnhan2).
    eapply (lfilled_first_values) with (vs := []) (vs' := []) in Hnconst1 => //.
    destruct Hnconst1 as (?&?&Hlheq).
    by destruct Hlheq.
  Qed.

  Lemma lfilled_trans2 : forall k lh es1 es1' es2 es2' k' lh' es3 es3',
      lfilled k lh es1 es2 -> lfilled k lh es1' es2' -> 
      lfilled k' lh' es2 es3 -> lfilled k' lh' es2' es3' ->
      exists lh'', lfilled (k+k') lh'' es1 es3 /\ lfilled (k+k') lh'' es1' es3'.
  Proof.
    intros k lh es1 es1' es2 es2' k' lh'; generalize dependent es2' ;
      generalize dependent es2 ; generalize dependent es1' ; generalize dependent es1 ;
      generalize dependent lh ; generalize dependent k ; generalize dependent k'; induction lh' ;
      intros k' k lh es1 es1' es2 es2' es3 es3' Hfill2 Hfill2' Hfill3 Hfill3'.
    all: unfold lfilled, lfill in Hfill3; fold lfill in Hfill3.
    all: unfold lfilled, lfill in Hfill3'; fold lfill in Hfill3'.
    1-2: destruct k' => //.
    all: destruct (const_list l) eqn:Hl => //.
    2-4: destruct (lfill _ _ _) eqn:Hfill => //.
    all: move/eqP in Hfill3; subst es3.
    2-4: destruct (lfill _ _ es2') eqn:Hfill' => //. 
    all: move/eqP in Hfill3'; subst es3'.
    - destruct lh; unfold lfilled, lfill in Hfill2; fold lfill in Hfill2.
      all: unfold lfilled, lfill in Hfill2'; fold lfill in Hfill2'.
      1-2: destruct k => //.
      all: destruct (const_list l1) eqn:Hl1 => //.
      2-4: destruct (lfill _ _ _) eqn:Hfill => //.
      2-4: destruct (lfill _ _ es1') eqn:Hfill' => //.
      all: move/eqP in Hfill2; subst es2.
      all: move/eqP in Hfill2'; subst es2'.
      + exists (LH_base (l ++ l1) (l2 ++ l0)) => //=.
        split; unfold lfilled, lfill; rewrite const_list_concat;
          repeat rewrite app_assoc ; done.
      + exists (LH_rec (l ++ l1) n l2 lh (l3 ++ l0)).
        rewrite Nat.add_0_r.
        unfold lfilled, lfill; fold lfill; rewrite const_list_concat => //.
        rewrite Hfill Hfill'. repeat rewrite app_assoc.
        split; by rewrite -app_assoc.
      + exists (LH_handler (l ++ l1) l2 lh (l3 ++ l0)).
        rewrite Nat.add_0_r.
        unfold lfilled, lfill; fold lfill; rewrite const_list_concat => //.
        rewrite Hfill Hfill'. repeat rewrite app_assoc.
        split; by rewrite -app_assoc.
      + exists (LH_prompt (l ++ l1) l2 l3 lh (l4 ++ l0)).
        rewrite Nat.add_0_r /lfilled /lfill; fold lfill.
        rewrite const_list_concat => //. rewrite Hfill Hfill'.
        repeat rewrite app_assoc.
        split; by rewrite -app_assoc.
    - edestruct IHlh' as (lh'' & Hfilln & Hfilln').
      exact Hfill2.
      exact Hfill2'.
      unfold lfilled; erewrite Hfill; done.
      unfold lfilled; erewrite Hfill'; done.
      exists (LH_rec l n l0 lh'' l1).
      rewrite Nat.add_comm => //=. rewrite Nat.add_comm.
      unfold lfilled, lfill ; fold lfill.
      rewrite Hl.
      unfold lfilled in Hfilln.
      destruct (lfill (k + k') lh'' es1) => //.
      unfold lfilled in Hfilln'.
      destruct (lfill (k+k') lh'' es1') => //.
      move/eqP in Hfilln ; move/eqP in Hfilln' ; by subst.
    - edestruct IHlh' as (lh'' & Hfilln & Hfilln').
      exact Hfill2.
      exact Hfill2'.
      unfold lfilled; erewrite Hfill; done.
      unfold lfilled; erewrite Hfill'; done.
      exists (LH_handler l l0 lh'' l1).
      rewrite Nat.add_comm => //=. rewrite Nat.add_comm.
      unfold lfilled, lfill ; fold lfill.
      rewrite Hl.
      unfold lfilled in Hfilln.
      destruct (lfill (k + k') lh'' es1) => //.
      unfold lfilled in Hfilln'.
      destruct (lfill (k+k') lh'' es1') => //.
      move/eqP in Hfilln ; move/eqP in Hfilln' ; by subst.
    - edestruct IHlh' as (lh'' & Hfilln & Hfilln').
      exact Hfill2.
      exact Hfill2'.
      unfold lfilled; erewrite Hfill; done.
      unfold lfilled; erewrite Hfill'; done.
      exists (LH_prompt l l0 l1 lh'' l2).
      rewrite Nat.add_comm => //=. rewrite Nat.add_comm.
      unfold lfilled, lfill ; fold lfill.
      rewrite Hl.
      unfold lfilled in Hfilln.
      destruct (lfill (k + k') lh'' es1) => //.
      unfold lfilled in Hfilln'.
      destruct (lfill (k+k') lh'' es1') => //.
      move/eqP in Hfilln ; move/eqP in Hfilln' ; by subst.
  Qed.

  Lemma assoc_list_seq {A} (a : list A) b c :
    (a ++ (b ++ c)%list)%SEQ = (a ++ b) ++ c.
  Proof. rewrite catA. done. Qed.

  Lemma const_list_singleton e :
    is_const e -> const_list [e].
  Proof. unfold const_list => //=. intros H ; rewrite H => //. Qed.

  Lemma const_list_In es e:
    In e es ->
    const_list es ->
    is_const e.
  Proof.
    elim: es => //=.
    move => e' es HIn [-> | HIn2] Hcontra; move/andP in Hcontra; destruct Hcontra as [He Hes] => //.
    by apply HIn => //.
  Qed.

  Lemma to_val_immV_inj es es' vs :
    iris.to_val0 es = Some (immV vs) ->
    iris.to_val0 es' = Some (immV vs) ->
    es = es'.
  Proof.
    intros. apply to_val_is_immV in H as ->.
    apply to_val_is_immV in H0 as -> => //.
  Qed. 

  Lemma const_list_snoc_eq vs :
    forall ves es es' e,
      const_list ves ->
      const_list vs ->
      es ≠ [] ->
      to_val0 es = None ->
      (vs ++ es ++ es')%SEQ = ves ++ [e] ->
      es' = [] ∧ ∃ vs2, ves = vs ++ vs2 ∧ es = vs2 ++ [e] ∧ const_list vs2.
  Proof.
    induction vs;
      intros ves es es' e Hconst1 Hconst2 Hneq Hnval Heq.
    - erewrite app_nil_l in Heq.
      apply app_eq_inv in Heq as [[k [Hk1 Hk2]] | [k [Hk1 Hk2]]].
      + destruct k.
        * rewrite app_nil_r in Hk1.
          rewrite app_nil_l in Hk2.
          simplify_eq.
          assert (is_Some (to_val0 (ves))) as [c Hc];[|congruence].
          unfold to_val in Hnval. unfold to_val.
          apply const_list_to_val in Hconst1 as (v & -> & _). eauto. 
        * destruct k,es' => //.
          rewrite app_nil_r in Hk2. simplify_eq.
          eauto. 
      + rewrite Hk1 in Hconst1.
        apply to_val_cat_None1 with (es2:=k) in Hnval.
        apply const_list_to_val in Hconst1 as (v & Hv & _).
        congruence. 
    - destruct ves.
      { destruct vs,es,es' => //. }
      inversion Heq;subst.
      simpl in Hconst1,Hconst2.
      apply andb_true_iff in Hconst1,Hconst2.
      destruct Hconst1 as [Ha0 Hconst1].
      destruct Hconst2 as [_ Hconst2].
      apply IHvs in H1;auto.
      destruct H1 as [Heqes' [vs2 [Heq1 Heq2]]].
      subst. eauto.
  Qed.
  Lemma length_to_val_immV v1 :
    forall vs1, to_val0 v1 = Some (immV vs1)
           -> length v1 = length vs1.
  Proof.
    induction v1;intros vs1 Hval.
    destruct vs1 => //.
    destruct vs1.
    apply to_val_nil in Hval. done.
    unfold to_val, iris.to_val0 in Hval.
    simpl in *.
    destruct a;try by rewrite merge_notval in Hval.  
    destruct b;try by rewrite merge_notval in Hval.
    - rewrite merge_br flatten_simplify in Hval ; inversion Hval.
    - rewrite merge_return flatten_simplify in Hval ; inversion Hval.
    - rewrite merge_prepend in Hval. unfold to_val, iris.to_val0 in IHv1.
      destruct (merge_values $ map _ _) => //.
      + destruct v2 => //.
        inversion Hval ; subst. by erewrite IHv1.
      + destruct e => //.
    - rewrite merge_prepend in Hval. unfold to_val, iris.to_val0 in IHv1.
      destruct (merge_values $ map _ _) => //.
      + destruct v0 => //.
        inversion Hval ; subst. by erewrite IHv1.
      + destruct e => //. 
    - rewrite merge_trap flatten_simplify in Hval.
      destruct v1 => //.
    - rewrite merge_prepend in Hval. unfold to_val, iris.to_val0 in IHv1.
      destruct (merge_values $ map _ _) => //.
      + destruct v0 => //.
        inversion Hval ; subst. by erewrite IHv1.
      + destruct e => //.
    - rewrite merge_prepend in Hval. unfold to_val, iris.to_val0 in IHv1.
      destruct (merge_values $ map _ _) => //.
      + destruct v0 => //.
        inversion Hval ; subst. by erewrite IHv1.
      + destruct e0 => //.
    - rewrite merge_prepend in Hval. unfold to_val, iris.to_val0 in IHv1.
      destruct (merge_values $ map _ _) => //.
      + destruct v0 => //.
        inversion Hval ; subst. by erewrite IHv1.
      + destruct e => //.
    - rewrite merge_throw in Hval => //.
    - rewrite merge_suspend in Hval => //.
    - rewrite merge_switch in Hval => //.
    - simpl in Hval.
      destruct (merge_values $ map _ _) eqn:Hmerge => //.
      + destruct v0 => //.
        all: try by rewrite merge_notval in Hval => //.
        * rewrite merge_br in Hval => //.
        * rewrite merge_return in Hval => //.
        * rewrite merge_call_host in Hval => //.
      + destruct e => //.
        * rewrite merge_suspend in Hval => //.
        * rewrite merge_switch in Hval => //.
        * destruct (exnelts_of_exception_clauses _ _) => //.
          rewrite merge_throw in Hval => //.
          rewrite merge_notval in Hval => //.
      + rewrite merge_notval in Hval => //.
    - simpl in Hval.
      destruct (merge_values $ map _ _) eqn:Hmerge => //.
      + destruct v0 => //.
        all: try by rewrite merge_notval in Hval => //.
        * rewrite merge_br in Hval => //.
        * rewrite merge_return in Hval => //.
        * rewrite merge_call_host in Hval => //.
      + destruct e => //.
        * destruct (suselts_of_continuation_clauses _ _) => //.
          rewrite merge_suspend in Hval => //.
          rewrite merge_notval in Hval => //. 
        * destruct (swelts_of_continuation_clauses _ _) => //.
          rewrite merge_switch in Hval => //.
          rewrite merge_notval in Hval => //. 
        * rewrite merge_throw in Hval => //.
      + rewrite merge_notval in Hval => //.
    - simpl in Hval.
      destruct (merge_values $ map _ _) eqn:Hmerge => //.
      + destruct v0 => //.
        all: try by rewrite merge_notval in Hval => //.
        * destruct i; last destruct (vh_decrease _).
          all: try by rewrite merge_notval in Hval.
          rewrite merge_br in Hval => //.
        * rewrite merge_return in Hval => //.
        * rewrite merge_call_host in Hval => //.
      + destruct e => //.
        * rewrite merge_suspend in Hval => //.
        * rewrite merge_switch in Hval => //.
        * rewrite merge_throw in Hval => //.
      + rewrite merge_notval in Hval => //.
    - simpl in Hval.
      destruct (merge_values $ map _ _) eqn:Hmerge => //.
      + destruct v0 => //.
        all: try by rewrite merge_notval in Hval => //.
        rewrite merge_call_host in Hval => //.
      + destruct e => //.
        * rewrite merge_suspend in Hval => //.
        * rewrite merge_switch in Hval => //.
        * rewrite merge_throw in Hval => //.
      + rewrite merge_notval in Hval => //.
    - rewrite merge_call_host in Hval => //. 
  Qed.
    

  Lemma lfilled_one_depth_trap k lh es vs n es' es'' :
    const_list vs ->
    lfilled k lh es (vs ++ [AI_label n es' [AI_trap]] ++ es'') ->
    k = 0 ∨ k = 1.
  Proof.
    revert lh es vs n es' es''.
    induction k;intros lh es vs n es' es'';auto.
    destruct k;auto.
    intros Hconst Hfill%lfilled_Ind_Equivalent.
    exfalso.
    inversion Hfill;subst.
    - apply first_values in H0 as [? [? ?]];auto.
      simplify_eq.
      inversion H4;subst.
      do 2 destruct vs0 => //.
      all: do 2 destruct bef => //.
    - apply first_values in H as (_ & ? & _) => //.
    - apply first_values in H as (_ & ? & _) => //.
  Qed.

  Lemma lfilled_trap_not_br i lh LI :
    lfilled i lh [AI_trap] LI ->
    (∀ i j lh vs0, const_list vs0 -> lfilled i lh (vs0 ++ [AI_basic (BI_br j)]) LI -> False).
  Proof.
    revert i LI.
    induction lh; intros i LI Hfill%lfilled_Ind_Equivalent.
    all: inversion Hfill;subst.
    all: intros i' j' lh' vs' Hconst Hfill'.
    all: apply lfilled_Ind_Equivalent in Hfill'.
    all: inversion Hfill'; subst.
    all: try by apply first_values in H as (_ & ? & _) => //.
    all: try by (repeat rewrite cat_app in H);
      (repeat rewrite app_assoc in H);
      rewrite - app_assoc in H;
      apply first_values in H as (_ & ? & _) => //;
      apply const_list_concat => //.
    - apply first_values in H as (_ & ? & _) => //.
      inversion H; subst.
      eapply IHlh. 
      apply/lfilledP. exact H8.
      2: apply/lfilledP; exact H4.
      done.
    - apply first_values in H as (_ & ? & _) => //.
      inversion H; subst.
      eapply IHlh. 
      apply/lfilledP. exact H7.
      2: apply/lfilledP; exact H4.
      done.
    - apply first_values in H as (_ & ? & _) => //.
      inversion H; subst.
      eapply IHlh. 
      apply/lfilledP. exact H8.
      2: apply/lfilledP; exact H4.
      done.
  Qed.

  Lemma lfilled_singleton (a : administrative_instruction) k lh es (les : list administrative_instruction) i lh'  :
    es ≠ [] ->
    (const_list es = false ) ->
    (es <> [AI_trap]) ->
    (is_const a = false ) ->
    (∀ n e1 e2, a ≠ AI_label n e1 e2) ->
    (∀ n e1 e2, a ≠ AI_prompt n e1 e2) ->
    (∀ e1 e2, a ≠ AI_handler e1 e2) ->
    lfilled k lh es les -> 
    lfilled i lh' [a] les ->
    ∃ j lh, lfilled j lh [a] es ∧ j + k = i.
  Proof.
    revert a k lh es les i.
    induction lh';intros a k lh es les i Hne Hnone1 Hnone2 Ha Hnlabel Hnprompt Hnhandler
                    Hfill1%lfilled_Ind_Equivalent Hfill2%lfilled_Ind_Equivalent.
    all: inversion Hfill2; inversion Hfill1; subst.
    - apply const_list_snoc_eq3 in H9 as (? & ? & ? & ? & ? & ?) => //.
      subst.  exists 0, (LH_base x x0). split; last lia.
      apply/lfilledP. constructor => //.
    - apply first_values in H10 as (? & ? & ?) => //.
      exfalso; eapply Hnlabel => //.
    - apply first_values in H10 as (? & ? & ?) => //.
      exfalso; eapply Hnhandler => //.
    - apply first_values in H10 as (? & ? & ?) => //.
      exfalso; eapply Hnprompt => //.
    - apply const_list_snoc_eq3 in H13 as (? & ? & ? & ? & ? & ?) => //.
      subst. exists (S k0), (LH_rec x n l0 lh' x0).
      split; last lia. apply/lfilledP. by constructor.
    - apply first_values in H14 as (? & ? & ?) => //.
      inversion H0; subst.
      edestruct IHlh' as (j & lh & Hfill & Hjki).
      8: apply/lfilledP; exact H10.
      8: apply/lfilledP; exact H8.
      all: try done.
      exists j, lh. split => //. lia.
    - apply first_values in H14 as (? & ? & ?) => //.
    - apply first_values in H14 as (? & ? & ?) => //.
    - apply const_list_snoc_eq3 in H12 as (? & ? & ? & ? & ? & ?) => //.
      subst. exists i, (LH_handler x l0 lh' x0).
      split; last lia. apply/lfilledP. constructor => //.
    - apply first_values in H13 as (? & ? & ?) => //.
    - apply first_values in H13 as (? & ? & ?) => //.
      inversion H0; subst.
      edestruct IHlh' as (j & lh & Hfill & Hjki).
      8: apply/lfilledP; exact H9.
      8: apply/lfilledP; exact H7.
      all: try done.
      exists j, lh. split => //.
    - apply first_values in H13 as (? & ? & ?) => //.
    - apply const_list_snoc_eq3 in H13 as (? & ? & ? & ? & ? & ?) => //.
      subst. exists i, (LH_prompt x l0 l1 lh' x0).
      split; last lia. apply/lfilledP; constructor => //.
    - apply first_values in H14 as (? & ? & ?) => //.
    - apply first_values in H14 as (? & ? & ?) => //.
    - apply first_values in H14 as (? & ? & ?) => //.
      inversion H0; subst.
      edestruct IHlh' as (j & lh & Hfill & Hjki).
      8: apply/lfilledP; exact H10.
      8: apply/lfilledP; exact H8.
      all: try done.
      exists j, lh. split => //.
  Qed. 


  Lemma filled_is_val_br_base_app_cases : ∀ i lh es1 es2 LI j v1 e1 ,
      iris.to_val0 LI = Some (brV (VH_base j v1 e1)) ->
      (es1 ++ es2) ≠ [] ->
      lfilled i lh (es1 ++ es2) LI ->
      i = 0 ∧ ∃ vs es, lh = LH_base vs es ∧ ((∃ es11 es12, es1 = es11 ++ (AI_basic (BI_br j)) :: es12 ∧ const_list es11) ∨
                                               (∃ es21 es22, es2 = es21 ++ (AI_basic (BI_br j)) :: es22 ∧ const_list es21 ∧ const_list es1) ∨
                                               (∃ es1' es2', es = es1' ++ (AI_basic (BI_br j)) :: es2' ∧ const_list es1 ∧ const_list es2 ∧ const_list es1')).
  Proof.
    assert (EqDecision administrative_instruction) as Heqa.
    { unfold EqDecision. apply administrative_instruction_eq_dec. }
    
    intros i lh es1 es2 LI j v1 e1 HLI Hnil Hfill.
    eapply filled_is_val_br_base in Hfill as Heq;eauto. subst.
    apply lfilled_Ind_Equivalent in Hfill.
    inversion Hfill.
    all: simplify_eq.
    all: split;auto.
    - exists vs,es'. split;auto.
      clear Hfill.
      apply to_val_br_base in HLI as Heq.
      repeat erewrite app_assoc in Heq.
      rewrite -!app_assoc in Heq.
      assert ((AI_basic (BI_br j)) ∈ (vs ++ es1 ++ es2 ++ es')) as Hin.
      { rewrite Heq. apply elem_of_app. right. constructor. }
      
      apply elem_of_app in Hin as [Hcontr | Hin].
      { apply elem_of_list_split in Hcontr as [l1 [l2 Hl]]. subst.
        apply const_list_app in H as [_ H]. done. }

      apply elem_of_app_l in Hin as [Hin | [Hin Hnin]].
      { left.
        eapply elem_of_list_split_l in Hin as [l1 [l2 [-> Hnin]]].
        rewrite (app_assoc _ es2) in Heq.
        apply const_list_l_snoc_eq3 in Heq;auto; try by intros [? ?].
        2: apply v_to_e_is_const_list.
        2: apply const_list_elem_of;auto;by intros [? ?].
        2:{ unfold const_list ; repeat rewrite forallb_app.
            simpl. rewrite andb_false_iff. left.
            by rewrite andb_false_iff ; right. } 
        2: do 2 destruct l1 => //.
        destruct Heq as [vs2 [es3 [Heq1 [Heq2 [Heq3 Hconst]]]]]. Unshelve.
        rewrite separate1 in Heq2. rewrite -!app_assoc in Heq2.
        apply const_list_l_snoc_eq3 in Heq2;auto;try by intros [? ?].
        destruct Heq2 as [vs3 [es4 [Heq21 [Heq22 [Heq23 Hconst']]]]].
        destruct vs3 =>//;[|destruct vs3 =>//].
        destruct es4 =>//. rewrite app_nil_l in Heq23.
        rewrite app_nil_l app_nil_r in Heq22.
        rewrite app_nil_r in Heq21. simplify_eq.
        exists l1,l2. split;auto. }
      apply elem_of_app_l in Hin as [Hin | [Hin Hnin2]].
      { right;left.
        eapply elem_of_list_split_l in Hin as [l1 [l2 [-> Hnin']]].
        rewrite separate1 in Heq. rewrite -!app_assoc in Heq.
        do 2 rewrite app_assoc in Heq. exists l1,l2. split;auto.
        apply const_list_l_snoc_eq3 in Heq;auto; try by intros [? ?].
        2: apply v_to_e_is_const_list.
        2: { apply not_elem_of_app;split;auto.
             apply not_elem_of_app;split;auto.
             apply const_list_elem_of;auto. }
        destruct Heq as [vs2 [es2 [Heq1 [Heq2 [Heq3 Hconst]]]]].
        simplify_eq.
        destruct vs2 => //;[|destruct vs2 => //].
        destruct es2 => //. rewrite app_nil_r in Heq1.
        pose proof (v_to_e_is_const_list v1) as Hc.
        rewrite -to_e_list_fmap Heq1 in Hc.
        apply const_list_app in Hc as [[? ?]%const_list_app ?]. auto. }
      { right;right.
        eapply elem_of_list_split_l in Hin as [l1 [l2 [-> Hnin']]].
        rewrite separate1 in Heq.
        do 3 rewrite app_assoc in Heq.
        exists l1,l2. split;auto.
        apply const_list_l_snoc_eq3 in Heq;auto; try by intros [? ?].
        2: apply v_to_e_is_const_list.
        2: { repeat (apply not_elem_of_app;split;auto).
             apply const_list_elem_of;auto. }
        destruct Heq as [vs2 [es3 [Heq1 [Heq2 [Heq3 Hconst]]]]].
        simplify_eq.
        destruct vs2 =>//;[|destruct vs2 =>//].
        destruct es3 =>//.
        rewrite app_nil_r in Heq1.
        pose proof (v_to_e_is_const_list v1) as Hc.
        rewrite -to_e_list_fmap Heq1 in Hc.
        apply const_list_app in Hc as [[[? ?]%const_list_app ?]%const_list_app ?]. auto.
      }
      all: auto.
    - unfold iris.to_val0 in HLI.
      rewrite map_app in HLI.
      rewrite merge_app in HLI.
      apply const_list_to_val in H as (vs & Hvs & Hvsbef).
      unfold iris.to_val0 in Hvs.
      destruct (merge_values _) => //.
      inversion Hvs; subst v.
      simpl in HLI.
      destruct (merge_values $ map _ _) => //.
      + destruct v => //=.
        all: try rewrite merge_notval in HLI => //.
        rewrite merge_br in HLI => //.
        rewrite merge_return in HLI => //.
        rewrite merge_call_host in HLI => //.
      + destruct e => //.
        rewrite merge_suspend in HLI => //.
        rewrite merge_switch in HLI => //.
        destruct (exnelts_of_exception_clauses _ _) => //.
        rewrite merge_throw in HLI => //.
        rewrite merge_notval in HLI => //.
      + rewrite merge_notval in HLI => //. 
    - unfold iris.to_val0 in HLI.
      rewrite map_app in HLI.
      rewrite merge_app in HLI.
      apply const_list_to_val in H as (vs & Hvs & Hvsbef).
      unfold iris.to_val0 in Hvs.
      destruct (merge_values _) => //.
      inversion Hvs; subst v.
      simpl in HLI.
      destruct (merge_values $ map _ _) => //.
      + destruct v => //=.
        all: try rewrite merge_notval in HLI => //.
        rewrite merge_br in HLI => //.
        rewrite merge_return in HLI => //.
        rewrite merge_call_host in HLI => //.
      + destruct e => //.
        destruct (suselts_of_continuation_clauses _ _) => //.
        rewrite merge_suspend in HLI => //.
        rewrite merge_notval in HLI => //.
        destruct (swelts_of_continuation_clauses _ _) => //. 
        rewrite merge_switch in HLI => //.
        rewrite merge_notval in HLI => //. 
        rewrite merge_throw in HLI => //.
      + rewrite merge_notval in HLI => //. 
  Qed. 

  Lemma filled_is_val_ret_base_app_cases : ∀ i lh es1 es2 LI v1 e1 ,
      iris.to_val0 LI = Some (retV (SH_base v1 e1)) ->
      (es1 ++ es2) ≠ [] ->
      lfilled i lh (es1 ++ es2) LI ->
      i = 0 ∧ ∃ vs es, lh = LH_base vs es ∧ ((∃ es11 es12, es1 = es11 ++ (AI_basic (BI_return)) :: es12 ∧ const_list es11) ∨
                                               (∃ es21 es22, es2 = es21 ++ (AI_basic (BI_return)) :: es22 ∧ const_list es21 ∧ const_list es1) ∨
                                               (∃ es1' es2', es = es1' ++ (AI_basic (BI_return)) :: es2' ∧ const_list es1 ∧ const_list es2 ∧ const_list es1')).
  Proof.
    assert (EqDecision administrative_instruction) as Heqa.
    { unfold EqDecision. apply administrative_instruction_eq_dec. }
    
    intros i lh es1 es2 LI v1 e1 HLI Hnil Hfill.
    eapply filled_is_val_ret_base in Hfill as Heq;eauto. subst.
    apply lfilled_Ind_Equivalent in Hfill.
    inversion Hfill.
    simplify_eq. split;auto.
    exists vs,es'. split;auto.
    clear Hfill.
    apply to_val_ret_base in HLI as Heq.
    repeat erewrite app_assoc in Heq.
    rewrite -!app_assoc in Heq.
    assert ((AI_basic (BI_return)) ∈ (vs ++ es1 ++ es2 ++ es')) as Hin.
    { rewrite Heq. apply elem_of_app. right. constructor. }
    
    apply elem_of_app in Hin as [Hcontr | Hin].
    { apply elem_of_list_split in Hcontr as [l1 [l2 Hl]]. subst.
      apply const_list_app in H as [_ H]. done. }

    apply elem_of_app_l in Hin as [Hin | [Hin Hnin]].
    { left.
      eapply elem_of_list_split_l in Hin as [l1 [l2 [-> Hnin]]].
      rewrite (app_assoc _ es2) in Heq.
      apply const_list_l_snoc_eq3 in Heq;auto; try by intros [? ?].
      2: apply v_to_e_is_const_list.
      2: apply const_list_elem_of;auto;by intros [? ?].
      2: unfold const_list ; repeat rewrite forallb_app ; simpl ; 
      apply andb_false_iff ; left ; apply andb_false_iff ; by right.
      2: do 2 destruct l1 => //.
      destruct Heq as [vs2 [es3 [Heq1 [Heq2 [Heq3 Hconst]]]]]. Unshelve.
      rewrite separate1 in Heq2. rewrite -!app_assoc in Heq2.
      apply const_list_l_snoc_eq3 in Heq2;auto;try by intros [? ?].
      destruct Heq2 as [vs3 [es4 [Heq21 [Heq22 [Heq23 Hconst']]]]].
      destruct vs3 =>//;[|destruct vs3 =>//].
      destruct es4 =>//. rewrite app_nil_l in Heq23.
      rewrite app_nil_l app_nil_r in Heq22.
      rewrite app_nil_r in Heq21. simplify_eq.
      exists l1,l2. split;auto. }
    apply elem_of_app_l in Hin as [Hin | [Hin Hnin2]].
    { right;left.
      eapply elem_of_list_split_l in Hin as [l1 [l2 [-> Hnin']]].
      rewrite separate1 in Heq. rewrite -!app_assoc in Heq.
      do 2 rewrite app_assoc in Heq. exists l1,l2. split;auto.
      apply const_list_l_snoc_eq3 in Heq;auto; try by intros [? ?].
      2: apply v_to_e_is_const_list.
      2: { apply not_elem_of_app;split;auto.
           apply not_elem_of_app;split;auto.
           apply const_list_elem_of;auto. }
      destruct Heq as [vs2 [es2 [Heq1 [Heq2 [Heq3 Hconst]]]]].
      simplify_eq.
      destruct vs2 =>//;[|destruct vs2 =>//].
      destruct es2 =>//. rewrite app_nil_r in Heq1.
      pose proof (v_to_e_is_const_list v1) as Hc.
      rewrite -to_e_list_fmap Heq1 in Hc.
      apply const_list_app in Hc as [[? ?]%const_list_app ?]. auto. }
    { right;right.
      eapply elem_of_list_split_l in Hin as [l1 [l2 [-> Hnin']]].
      rewrite separate1 in Heq.
      do 3 rewrite app_assoc in Heq.
      exists l1,l2. split;auto.
      apply const_list_l_snoc_eq3 in Heq;auto; try by intros [? ?].
      2: apply v_to_e_is_const_list.
      2: { repeat (apply not_elem_of_app;split;auto).
           apply const_list_elem_of;auto. }
      destruct Heq as [vs2 [es3 [Heq1 [Heq2 [Heq3 Hconst]]]]].
      simplify_eq.
      destruct vs2 =>//;[|destruct vs2 =>//].
      destruct es3 =>//.
      rewrite app_nil_r in Heq1.
      pose proof (v_to_e_is_const_list v1) as Hc.
      rewrite -to_e_list_fmap Heq1 in Hc.
      apply const_list_app in Hc as [[[? ?]%const_list_app ?]%const_list_app ?]. auto.
    }
    all: auto.
    - subst. unfold iris.to_val0 in HLI.
      rewrite map_app in HLI.
      rewrite merge_app in HLI.
      apply const_list_to_val in H as (vs & Hvs & Hvsbef).
      unfold iris.to_val0 in Hvs.
      destruct (merge_values _) => //.
      inversion Hvs; subst v.
      simpl in HLI.
      destruct (merge_values $ map _ _) => //.
      + destruct v => //=.
        all: try rewrite merge_notval in HLI => //.
        rewrite merge_br in HLI => //.
        rewrite merge_return in HLI => //.
        rewrite merge_call_host in HLI => //.
      + destruct e => //.
        rewrite merge_suspend in HLI => //.
        rewrite merge_switch in HLI => //.
        destruct (exnelts_of_exception_clauses _ _) => //.
        rewrite merge_throw in HLI => //.
        rewrite merge_notval in HLI => //.
      + rewrite merge_notval in HLI => //. 
    - subst. unfold iris.to_val0 in HLI.
      rewrite map_app in HLI.
      rewrite merge_app in HLI.
      apply const_list_to_val in H as (vs & Hvs & Hvsbef).
      unfold iris.to_val0 in Hvs.
      destruct (merge_values _) => //.
      inversion Hvs; subst v.
      simpl in HLI.
      destruct (merge_values $ map _ _) => //.
      + destruct v => //=.
        all: try rewrite merge_notval in HLI => //.
        rewrite merge_br in HLI => //.
        rewrite merge_return in HLI => //.
        rewrite merge_call_host in HLI => //.
      + destruct e => //.
        destruct (suselts_of_continuation_clauses _ _) => //.
        rewrite merge_suspend in HLI => //.
        rewrite merge_notval in HLI => //.
        destruct (swelts_of_continuation_clauses _ _) => //. 
        rewrite merge_switch in HLI => //.
        rewrite merge_notval in HLI => //. 
        rewrite merge_throw in HLI => //.
      + rewrite merge_notval in HLI => //.
  Qed.  


  Lemma filled_is_val_call_host_base_app_cases : ∀ i lh es1 es2 LI v1 e1 tf h cvs,
      iris.to_val0 LI = Some (callHostV tf h cvs ((LL_base v1 e1))) ->
      (es1 ++ es2) ≠ [] ->
      lfilled i lh (es1 ++ es2) LI ->
      i = 0 ∧ ∃ vs es, lh = LH_base vs es ∧ ((∃ es11 es12, es1 = es11 ++ (AI_call_host tf h cvs) :: es12 ∧ const_list es11) ∨
                                               (∃ es21 es22, es2 = es21 ++ (AI_call_host tf h cvs) :: es22 ∧ const_list es21 ∧ const_list es1) ∨
                                               (∃ es1' es2', es = es1' ++ (AI_call_host tf h cvs) :: es2' ∧ const_list es1 ∧ const_list es2 ∧ const_list es1')).
  Proof.
    assert (EqDecision administrative_instruction) as Heqa.
    { unfold EqDecision. apply administrative_instruction_eq_dec. }
    
    intros i lh es1 es2 LI v1 e1 tf h cvs HLI Hnil Hfill.
    eapply filled_is_val_call_host_base in Hfill as Heq;eauto. subst.
    apply lfilled_Ind_Equivalent in Hfill.
    inversion Hfill.
    simplify_eq. split;auto.
    exists vs,es'. split;auto.
    clear Hfill.
    apply to_val_call_host_base in HLI as Heq.
    repeat erewrite app_assoc in Heq.
    rewrite -!app_assoc in Heq.
    assert ((AI_call_host tf h cvs) ∈ (vs ++ es1 ++ es2 ++ es')) as Hin.
    { rewrite Heq. apply elem_of_app. right. constructor. }
    
    apply elem_of_app in Hin as [Hcontr | Hin].
    { apply elem_of_list_split in Hcontr as [l1 [l2 Hl]]. subst.
      apply const_list_app in H as [_ H]. done. }

    apply elem_of_app_l in Hin as [Hin | [Hin Hnin]].
    { left.
      eapply elem_of_list_split_l in Hin as [l1 [l2 [-> Hnin]]].
      rewrite (app_assoc _ es2) in Heq.
      apply const_list_l_snoc_eq3 in Heq;auto; try by intros [? ?].
      2: apply v_to_e_is_const_list.
      2: apply const_list_elem_of;auto;by intros [? ?].
      2: unfold const_list ; repeat rewrite forallb_app ; simpl ;
      apply andb_false_iff ; left ; apply andb_false_iff ; by right.      2: do 2 destruct l1 => //.
      destruct Heq as [vs2 [es3 [Heq1 [Heq2 [Heq3 Hconst]]]]]. Unshelve.
      rewrite separate1 in Heq2. rewrite -!app_assoc in Heq2.
      apply const_list_l_snoc_eq3 in Heq2;auto;try by intros [? ?].
      destruct Heq2 as [vs3 [es4 [Heq21 [Heq22 [Heq23 Hconst']]]]].
      destruct vs3 => //;[|destruct vs3 => //].
      destruct es4 => //. rewrite app_nil_l in Heq23.
      rewrite app_nil_l app_nil_r in Heq22.
      rewrite app_nil_r in Heq21. simplify_eq.
      exists l1,l2. split;auto. }
    apply elem_of_app_l in Hin as [Hin | [Hin Hnin2]].
    { right;left.
      eapply elem_of_list_split_l in Hin as [l1 [l2 [-> Hnin']]].
      rewrite separate1 in Heq. rewrite -!app_assoc in Heq.
      do 2 rewrite app_assoc in Heq. exists l1,l2. split;auto.
      apply const_list_l_snoc_eq3 in Heq;auto; try by intros [? ?].
      2: apply v_to_e_is_const_list.
      2: { apply not_elem_of_app;split;auto.
           apply not_elem_of_app;split;auto.
           apply const_list_elem_of;auto. }
      destruct Heq as [vs2 [es2 [Heq1 [Heq2 [Heq3 Hconst]]]]].
      simplify_eq.
      destruct vs2 =>//;[|destruct vs2 =>//].
      destruct es2 =>//. rewrite app_nil_r in Heq1.
      pose proof (v_to_e_is_const_list v1) as Hc.
      rewrite -to_e_list_fmap Heq1 in Hc.
      apply const_list_app in Hc as [[? ?]%const_list_app ?]. auto. }
    { right;right.
      eapply elem_of_list_split_l in Hin as [l1 [l2 [-> Hnin']]].
      rewrite separate1 in Heq.
      do 3 rewrite app_assoc in Heq.
      exists l1,l2. split;auto.
      apply const_list_l_snoc_eq3 in Heq;auto; try by intros [? ?].
      2: apply v_to_e_is_const_list.
      2: { repeat (apply not_elem_of_app;split;auto).
           apply const_list_elem_of;auto. }
      destruct Heq as [vs2 [es3 [Heq1 [Heq2 [Heq3 Hconst]]]]].
      simplify_eq.
      destruct vs2 =>//;[|destruct vs2 =>//].
      destruct es3 =>//.
      rewrite app_nil_r in Heq1.
      pose proof (v_to_e_is_const_list v1) as Hc.
      rewrite -to_e_list_fmap Heq1 in Hc.
      apply const_list_app in Hc as [[[? ?]%const_list_app ?]%const_list_app ?]. auto.
    }
    all: auto.
    all: subst.
        - unfold iris.to_val0 in HLI.
      rewrite map_app in HLI.
      rewrite merge_app in HLI.
      apply const_list_to_val in H as (vs & Hvs & Hvsbef).
      unfold iris.to_val0 in Hvs.
      destruct (merge_values _) => //.
      inversion Hvs; subst v.
      simpl in HLI.
      destruct (merge_values $ map _ _) => //.
      + destruct v => //=.
        all: try rewrite merge_notval in HLI => //.
        rewrite merge_br in HLI => //.
        rewrite merge_return in HLI => //.
        rewrite merge_call_host in HLI => //.
      + destruct e => //.
        rewrite merge_suspend in HLI => //.
        rewrite merge_switch in HLI => //.
        destruct (exnelts_of_exception_clauses _ _) => //.
        rewrite merge_throw in HLI => //.
        rewrite merge_notval in HLI => //.
      + rewrite merge_notval in HLI => //. 
    - unfold iris.to_val0 in HLI.
      rewrite map_app in HLI.
      rewrite merge_app in HLI.
      apply const_list_to_val in H as (vs & Hvs & Hvsbef).
      unfold iris.to_val0 in Hvs.
      destruct (merge_values _) => //.
      inversion Hvs; subst v.
      simpl in HLI.
      destruct (merge_values $ map _ _) => //.
      + destruct v => //=.
        all: try rewrite merge_notval in HLI => //.
        rewrite merge_br in HLI => //.
        rewrite merge_return in HLI => //.
        rewrite merge_call_host in HLI => //.
      + destruct e => //.
        destruct (suselts_of_continuation_clauses _ _) => //.
        rewrite merge_suspend in HLI => //.
        rewrite merge_notval in HLI => //.
        destruct (swelts_of_continuation_clauses _ _) => //. 
        rewrite merge_switch in HLI => //.
        rewrite merge_notval in HLI => //. 
        rewrite merge_throw in HLI => //.
      + rewrite merge_notval in HLI => //.
  Qed.

  
  Lemma filled_is_eff_sus_base_app_cases : ∀ i lh es1 es2 LI vs' i' bef aft,
      iris.to_eff0 LI = Some (susE vs' i' (SuBase bef aft)) ->
      (es1 ++ es2) ≠ [] ->
      lfilled i lh (es1 ++ es2) LI ->
      i = 0 ∧ ∃ vs es, lh = LH_base vs es ∧ ((∃ es11 es12, es1 = es11 ++ (AI_suspend_desugared vs' i') :: es12 ∧ const_list es11) ∨
                                               (∃ es21 es22, es2 = es21 ++ (AI_suspend_desugared vs' i') :: es22 ∧ const_list es21 ∧ const_list es1) ∨
                                               (∃ es1' es2', es = es1' ++ (AI_suspend_desugared vs' i') :: es2' ∧ const_list es1 ∧ const_list es2 ∧ const_list es1')).
  Proof.
    assert (EqDecision administrative_instruction) as Heqa.
    { unfold EqDecision. apply administrative_instruction_eq_dec. }
    
    intros i lh es1 es2 LI vs' i' bef aft HLI Hnil Hfill.
    eapply filled_is_eff_sus_base in Hfill as Heq;eauto. subst.
    apply lfilled_Ind_Equivalent in Hfill.
    inversion Hfill.
    all: simplify_eq.
    all: split;auto.
    - exists vs,es'. split;auto.
      clear Hfill.
      apply to_eff_sus_base in HLI as Heq.
      repeat erewrite app_assoc in Heq.
      rewrite -!app_assoc in Heq.
      assert ((AI_suspend_desugared vs' i') ∈ (vs ++ es1 ++ es2 ++ es')) as Hin.
      { rewrite Heq. apply elem_of_app. right. constructor. }
      
      apply elem_of_app in Hin as [Hcontr | Hin].
      { apply elem_of_list_split in Hcontr as [l1 [l2 Hl]]. subst.
        apply const_list_app in H as [_ H]. done. }

      apply elem_of_app_l in Hin as [Hin | [Hin Hnin]].
      { left.
        eapply elem_of_list_split_l in Hin as [l1 [l2 [-> Hnin]]].
        rewrite (app_assoc _ es2) in Heq.
        apply const_list_l_snoc_eq3 in Heq;auto; try by intros [? ?].
        2: apply v_to_e_is_const_list.
        2: apply const_list_elem_of;auto;by intros [? ?].
        2:{ unfold const_list ; repeat rewrite forallb_app.
            simpl. rewrite andb_false_iff. left.
            by rewrite andb_false_iff ; right. } 
        2: do 2 destruct l1 => //.
        destruct Heq as [vs2 [es3 [Heq1 [Heq2 [Heq3 Hconst]]]]]. Unshelve.
        rewrite separate1 in Heq2. rewrite -!app_assoc in Heq2.
        apply const_list_l_snoc_eq3 in Heq2;auto;try by intros [? ?].
        destruct Heq2 as [vs3 [es4 [Heq21 [Heq22 [Heq23 Hconst']]]]].
        destruct vs3 =>//;[|destruct vs3 =>//].
        destruct es4 =>//. rewrite app_nil_l in Heq23.
        rewrite app_nil_l app_nil_r in Heq22.
        rewrite app_nil_r in Heq21. simplify_eq.
        exists l1,l2. split;auto. }
      apply elem_of_app_l in Hin as [Hin | [Hin Hnin2]].
      { right;left.
        eapply elem_of_list_split_l in Hin as [l1 [l2 [-> Hnin']]].
        rewrite separate1 in Heq. rewrite -!app_assoc in Heq.
        do 2 rewrite app_assoc in Heq. exists l1,l2. split;auto.
        apply const_list_l_snoc_eq3 in Heq;auto; try by intros [? ?].
        2: apply v_to_e_is_const_list.
        2: { apply not_elem_of_app;split;auto.
             apply not_elem_of_app;split;auto.
             apply const_list_elem_of;auto. }
        destruct Heq as [vs2 [es2 [Heq1 [Heq2 [Heq3 Hconst]]]]].
        simplify_eq.
        destruct vs2 => //;[|destruct vs2 => //].
        destruct es2 => //. rewrite app_nil_r in Heq1.
        pose proof (v_to_e_is_const_list bef) as Hc.
        rewrite -to_e_list_fmap Heq1 in Hc.
        apply const_list_app in Hc as [[? ?]%const_list_app ?]. auto. }
      { right;right.
        eapply elem_of_list_split_l in Hin as [l1 [l2 [-> Hnin']]].
        rewrite separate1 in Heq.
        do 3 rewrite app_assoc in Heq.
        exists l1,l2. split;auto.
        apply const_list_l_snoc_eq3 in Heq;auto; try by intros [? ?].
        2: apply v_to_e_is_const_list.
        2: { repeat (apply not_elem_of_app;split;auto).
             apply const_list_elem_of;auto. }
        destruct Heq as [vs2 [es3 [Heq1 [Heq2 [Heq3 Hconst]]]]].
        simplify_eq.
        destruct vs2 => //;[|destruct vs2 => //].
        destruct es3 => //.
        rewrite app_nil_r in Heq1.
        pose proof (v_to_e_is_const_list bef) as Hc.
        rewrite -to_e_list_fmap Heq1 in Hc.
        apply const_list_app in Hc as [[[? ?]%const_list_app ?]%const_list_app ?]. auto.
      }
      all: auto.
    - unfold iris.to_eff0 in HLI.
      rewrite map_app in HLI.
      rewrite merge_app in HLI.
      apply const_list_to_val in H as (vs & Hvs & Hvsbef).
      unfold iris.to_val0 in Hvs.
      destruct (merge_values _) => //.
      inversion Hvs; subst v.
      simpl in HLI.
      destruct (merge_values $ map _ _) => //.
      + destruct v => //=.
        all: try rewrite merge_notval in HLI => //.
        rewrite merge_br in HLI => //.
        rewrite merge_return in HLI => //.
        rewrite merge_call_host in HLI => //.
      + destruct e => //.
        rewrite merge_suspend in HLI => //.
        rewrite merge_switch in HLI => //.
        destruct (exnelts_of_exception_clauses _ _) => //.
        rewrite merge_throw in HLI => //.
        rewrite merge_notval in HLI => //.
      + rewrite merge_notval in HLI => //. 
    - unfold iris.to_eff0 in HLI.
      rewrite map_app in HLI.
      rewrite merge_app in HLI.
      apply const_list_to_val in H as (vs & Hvs & Hvsbef).
      unfold iris.to_val0 in Hvs.
      destruct (merge_values _) => //.
      inversion Hvs; subst v.
      simpl in HLI.
      destruct (merge_values $ map _ _) => //.
      + destruct v => //=.
        all: try rewrite merge_notval in HLI => //.
        rewrite merge_br in HLI => //.
        rewrite merge_return in HLI => //.
        rewrite merge_call_host in HLI => //.
      + destruct e => //.
        destruct (suselts_of_continuation_clauses _ _) => //.
        rewrite merge_suspend in HLI => //.
        rewrite merge_notval in HLI => //.
        destruct (swelts_of_continuation_clauses _ _) => //. 
        rewrite merge_switch in HLI => //.
        rewrite merge_notval in HLI => //. 
        rewrite merge_throw in HLI => //.
      + rewrite merge_notval in HLI => //. 
  Qed.

    
  Lemma filled_is_eff_sw_base_app_cases : ∀ i lh es1 es2 LI vs' tf'' k' i' bef aft,
      iris.to_eff0 LI = Some (swE vs' tf'' k' i' (SwBase bef aft)) ->
      (es1 ++ es2) ≠ [] ->
      lfilled i lh (es1 ++ es2) LI ->
      i = 0 ∧ ∃ vs es, lh = LH_base vs es ∧ ((∃ es11 es12, es1 = es11 ++ (AI_switch_desugared vs' tf'' k' i') :: es12 ∧ const_list es11) ∨
                                               (∃ es21 es22, es2 = es21 ++ (AI_switch_desugared vs' tf'' k' i') :: es22 ∧ const_list es21 ∧ const_list es1) ∨
                                               (∃ es1' es2', es = es1' ++ (AI_switch_desugared vs' tf'' k' i') :: es2' ∧ const_list es1 ∧ const_list es2 ∧ const_list es1')).
  Proof.
    assert (EqDecision administrative_instruction) as Heqa.
    { unfold EqDecision. apply administrative_instruction_eq_dec. }
    
    intros i lh es1 es2 LI vs' tf'' k' i' bef aft HLI Hnil Hfill.
    eapply filled_is_eff_sw_base in Hfill as Heq;eauto. subst.
    apply lfilled_Ind_Equivalent in Hfill.
    inversion Hfill.
    all: simplify_eq.
    all: split;auto.
    - exists vs,es'. split;auto.
      clear Hfill.
      apply to_eff_sw_base in HLI as Heq.
      repeat erewrite app_assoc in Heq.
      rewrite -!app_assoc in Heq.
      assert ((AI_switch_desugared vs' tf'' k' i') ∈ (vs ++ es1 ++ es2 ++ es')) as Hin.
      { rewrite Heq. apply elem_of_app. right. constructor. }
      
      apply elem_of_app in Hin as [Hcontr | Hin].
      { apply elem_of_list_split in Hcontr as [l1 [l2 Hl]]. subst.
        apply const_list_app in H as [_ H]. done. }

      apply elem_of_app_l in Hin as [Hin | [Hin Hnin]].
      { left.
        eapply elem_of_list_split_l in Hin as [l1 [l2 [-> Hnin]]].
        rewrite (app_assoc _ es2) in Heq.
        apply const_list_l_snoc_eq3 in Heq;auto; try by intros [? ?].
        2: apply v_to_e_is_const_list.
        2: apply const_list_elem_of;auto;by intros [? ?].
        2:{ unfold const_list ; repeat rewrite forallb_app.
            simpl. rewrite andb_false_iff. left.
            by rewrite andb_false_iff ; right. } 
        2: do 2 destruct l1 => //.
        destruct Heq as [vs2 [es3 [Heq1 [Heq2 [Heq3 Hconst]]]]]. Unshelve.
        rewrite separate1 in Heq2. rewrite -!app_assoc in Heq2.
        apply const_list_l_snoc_eq3 in Heq2;auto;try by intros [? ?].
        destruct Heq2 as [vs3 [es4 [Heq21 [Heq22 [Heq23 Hconst']]]]].
        destruct vs3 =>//;[|destruct vs3 =>//].
        destruct es4 =>//. rewrite app_nil_l in Heq23.
        rewrite app_nil_l app_nil_r in Heq22.
        rewrite app_nil_r in Heq21. simplify_eq.
        exists l1,l2. split;auto. }
      apply elem_of_app_l in Hin as [Hin | [Hin Hnin2]].
      { right;left.
        eapply elem_of_list_split_l in Hin as [l1 [l2 [-> Hnin']]].
        rewrite separate1 in Heq. rewrite -!app_assoc in Heq.
        do 2 rewrite app_assoc in Heq. exists l1,l2. split;auto.
        apply const_list_l_snoc_eq3 in Heq;auto; try by intros [? ?].
        2: apply v_to_e_is_const_list.
        2: { apply not_elem_of_app;split;auto.
             apply not_elem_of_app;split;auto.
             apply const_list_elem_of;auto. }
        destruct Heq as [vs2 [es2 [Heq1 [Heq2 [Heq3 Hconst]]]]].
        simplify_eq.
        destruct vs2 => //;[|destruct vs2 => //].
        destruct es2 => //. rewrite app_nil_r in Heq1.
        pose proof (v_to_e_is_const_list bef) as Hc.
        rewrite -to_e_list_fmap Heq1 in Hc.
        apply const_list_app in Hc as [[? ?]%const_list_app ?]. auto. }
      { right;right.
        eapply elem_of_list_split_l in Hin as [l1 [l2 [-> Hnin']]].
        rewrite separate1 in Heq.
        do 3 rewrite app_assoc in Heq.
        exists l1,l2. split;auto.
        apply const_list_l_snoc_eq3 in Heq;auto; try by intros [? ?].
        2: apply v_to_e_is_const_list.
        2: { repeat (apply not_elem_of_app;split;auto).
             apply const_list_elem_of;auto. }
        destruct Heq as [vs2 [es3 [Heq1 [Heq2 [Heq3 Hconst]]]]].
        simplify_eq.
        destruct vs2 => //;[|destruct vs2 => //].
        destruct es3 => //.
        rewrite app_nil_r in Heq1.
        pose proof (v_to_e_is_const_list bef) as Hc.
        rewrite -to_e_list_fmap Heq1 in Hc.
        apply const_list_app in Hc as [[[? ?]%const_list_app ?]%const_list_app ?]. auto.
      }
      all: auto.
    - unfold iris.to_eff0 in HLI.
      rewrite map_app in HLI.
      rewrite merge_app in HLI.
      apply const_list_to_val in H as (vs & Hvs & Hvsbef).
      unfold iris.to_val0 in Hvs.
      destruct (merge_values _) => //.
      inversion Hvs; subst v.
      simpl in HLI.
      destruct (merge_values $ map _ _) => //.
      + destruct v => //=.
        all: try rewrite merge_notval in HLI => //.
        rewrite merge_br in HLI => //.
        rewrite merge_return in HLI => //.
        rewrite merge_call_host in HLI => //.
      + destruct e => //.
        rewrite merge_suspend in HLI => //.
        rewrite merge_switch in HLI => //.
        destruct (exnelts_of_exception_clauses _ _) => //.
        rewrite merge_throw in HLI => //.
        rewrite merge_notval in HLI => //.
      + rewrite merge_notval in HLI => //. 
    - unfold iris.to_eff0 in HLI.
      rewrite map_app in HLI.
      rewrite merge_app in HLI.
      apply const_list_to_val in H as (vs & Hvs & Hvsbef).
      unfold iris.to_val0 in Hvs.
      destruct (merge_values _) => //.
      inversion Hvs; subst v.
      simpl in HLI.
      destruct (merge_values $ map _ _) => //.
      + destruct v => //=.
        all: try rewrite merge_notval in HLI => //.
        rewrite merge_br in HLI => //.
        rewrite merge_return in HLI => //.
        rewrite merge_call_host in HLI => //.
      + destruct e => //.
        destruct (suselts_of_continuation_clauses _ _) => //.
        rewrite merge_suspend in HLI => //.
        rewrite merge_notval in HLI => //.
        destruct (swelts_of_continuation_clauses _ _) => //. 
        rewrite merge_switch in HLI => //.
        rewrite merge_notval in HLI => //. 
        rewrite merge_throw in HLI => //.
      + rewrite merge_notval in HLI => //. 
  Qed.

    
  Lemma filled_is_eff_thr_base_app_cases : ∀ i lh es1 es2 LI vs' k' i' bef aft,
      iris.to_eff0 LI = Some (thrE vs' k' i' (ExBase bef aft)) ->
      (es1 ++ es2) ≠ [] ->
      lfilled i lh (es1 ++ es2) LI ->
      i = 0 ∧ ∃ vs es, lh = LH_base vs es ∧ ((∃ es11 es12, es1 = es11 ++ (AI_throw_ref_desugared vs' k' i') :: es12 ∧ const_list es11) ∨
                                               (∃ es21 es22, es2 = es21 ++ (AI_throw_ref_desugared vs' k' i') :: es22 ∧ const_list es21 ∧ const_list es1) ∨
                                               (∃ es1' es2', es = es1' ++ (AI_throw_ref_desugared vs' k' i') :: es2' ∧ const_list es1 ∧ const_list es2 ∧ const_list es1')).
  Proof.
    assert (EqDecision administrative_instruction) as Heqa.
    { unfold EqDecision. apply administrative_instruction_eq_dec. }
    
    intros i lh es1 es2 LI vs' k' i' bef aft HLI Hnil Hfill.
    eapply filled_is_eff_thr_base in Hfill as Heq;eauto. subst.
    apply lfilled_Ind_Equivalent in Hfill.
    inversion Hfill.
    all: simplify_eq.
    all: split;auto.
    - exists vs,es'. split;auto.
      clear Hfill.
      apply to_eff_thr_base in HLI as Heq.
      repeat erewrite app_assoc in Heq.
      rewrite -!app_assoc in Heq.
      assert ((AI_throw_ref_desugared vs' k' i') ∈ (vs ++ es1 ++ es2 ++ es')) as Hin.
      { rewrite Heq. apply elem_of_app. right. constructor. }
      
      apply elem_of_app in Hin as [Hcontr | Hin].
      { apply elem_of_list_split in Hcontr as [l1 [l2 Hl]]. subst.
        apply const_list_app in H as [_ H]. done. }

      apply elem_of_app_l in Hin as [Hin | [Hin Hnin]].
      { left.
        eapply elem_of_list_split_l in Hin as [l1 [l2 [-> Hnin]]].
        rewrite (app_assoc _ es2) in Heq.
        apply const_list_l_snoc_eq3 in Heq;auto; try by intros [? ?].
        2: apply v_to_e_is_const_list.
        2: apply const_list_elem_of;auto;by intros [? ?].
        2:{ unfold const_list ; repeat rewrite forallb_app.
            simpl. rewrite andb_false_iff. left.
            by rewrite andb_false_iff ; right. } 
        2: do 2 destruct l1 => //.
        destruct Heq as [vs2 [es3 [Heq1 [Heq2 [Heq3 Hconst]]]]]. Unshelve.
        rewrite separate1 in Heq2. rewrite -!app_assoc in Heq2.
        apply const_list_l_snoc_eq3 in Heq2;auto;try by intros [? ?].
        destruct Heq2 as [vs3 [es4 [Heq21 [Heq22 [Heq23 Hconst']]]]].
        destruct vs3 =>//;[|destruct vs3 =>//].
        destruct es4 =>//. rewrite app_nil_l in Heq23.
        rewrite app_nil_l app_nil_r in Heq22.
        rewrite app_nil_r in Heq21. simplify_eq.
        exists l1,l2. split;auto. }
      apply elem_of_app_l in Hin as [Hin | [Hin Hnin2]].
      { right;left.
        eapply elem_of_list_split_l in Hin as [l1 [l2 [-> Hnin']]].
        rewrite separate1 in Heq. rewrite -!app_assoc in Heq.
        do 2 rewrite app_assoc in Heq. exists l1,l2. split;auto.
        apply const_list_l_snoc_eq3 in Heq;auto; try by intros [? ?].
        2: apply v_to_e_is_const_list.
        2: { apply not_elem_of_app;split;auto.
             apply not_elem_of_app;split;auto.
             apply const_list_elem_of;auto. }
        destruct Heq as [vs2 [es2 [Heq1 [Heq2 [Heq3 Hconst]]]]].
        simplify_eq.
        destruct vs2 => //;[|destruct vs2 => //].
        destruct es2 => //. rewrite app_nil_r in Heq1.
        pose proof (v_to_e_is_const_list bef) as Hc.
        rewrite -to_e_list_fmap Heq1 in Hc.
        apply const_list_app in Hc as [[? ?]%const_list_app ?]. auto. }
      { right;right.
        eapply elem_of_list_split_l in Hin as [l1 [l2 [-> Hnin']]].
        rewrite separate1 in Heq.
        do 3 rewrite app_assoc in Heq.
        exists l1,l2. split;auto.
        apply const_list_l_snoc_eq3 in Heq;auto; try by intros [? ?].
        2: apply v_to_e_is_const_list.
        2: { repeat (apply not_elem_of_app;split;auto).
             apply const_list_elem_of;auto. }
        destruct Heq as [vs2 [es3 [Heq1 [Heq2 [Heq3 Hconst]]]]].
        simplify_eq.
        destruct vs2 => //;[|destruct vs2 => //].
        destruct es3 => //.
        rewrite app_nil_r in Heq1.
        pose proof (v_to_e_is_const_list bef) as Hc.
        rewrite -to_e_list_fmap Heq1 in Hc.
        apply const_list_app in Hc as [[[? ?]%const_list_app ?]%const_list_app ?]. auto.
      }
      all: auto.
    - unfold iris.to_eff0 in HLI.
      rewrite map_app in HLI.
      rewrite merge_app in HLI.
      apply const_list_to_val in H as (vs & Hvs & Hvsbef).
      unfold iris.to_val0 in Hvs.
      destruct (merge_values _) => //.
      inversion Hvs; subst v.
      simpl in HLI.
      destruct (merge_values $ map _ _) => //.
      + destruct v => //=.
        all: try rewrite merge_notval in HLI => //.
        rewrite merge_br in HLI => //.
        rewrite merge_return in HLI => //.
        rewrite merge_call_host in HLI => //.
      + destruct e => //.
        rewrite merge_suspend in HLI => //.
        rewrite merge_switch in HLI => //.
        destruct (exnelts_of_exception_clauses _ _) => //.
        rewrite merge_throw in HLI => //.
        rewrite merge_notval in HLI => //.
      + rewrite merge_notval in HLI => //. 
    - unfold iris.to_eff0 in HLI.
      rewrite map_app in HLI.
      rewrite merge_app in HLI.
      apply const_list_to_val in H as (vs & Hvs & Hvsbef).
      unfold iris.to_val0 in Hvs.
      destruct (merge_values _) => //.
      inversion Hvs; subst v.
      simpl in HLI.
      destruct (merge_values $ map _ _) => //.
      + destruct v => //=.
        all: try rewrite merge_notval in HLI => //.
        rewrite merge_br in HLI => //.
        rewrite merge_return in HLI => //.
        rewrite merge_call_host in HLI => //.
      + destruct e => //.
        destruct (suselts_of_continuation_clauses _ _) => //.
        rewrite merge_suspend in HLI => //.
        rewrite merge_notval in HLI => //.
        destruct (swelts_of_continuation_clauses _ _) => //. 
        rewrite merge_switch in HLI => //.
        rewrite merge_notval in HLI => //. 
        rewrite merge_throw in HLI => //.
      + rewrite merge_notval in HLI => //. 
  Qed. 

  Lemma of_val_br_app_r n (vh : valid_holed n) es2 :
    of_val0 (brV vh) ++ es2 = of_val0 (brV (vh_append vh es2)).
  Proof.
    simpl. destruct vh => //= ; by rewrite app_comm_cons app_assoc. 
  Qed.

  Lemma of_val_ret_app_r sh es2 :
    of_val0 (retV sh) ++ es2 = of_val0 (retV (sh_append sh es2)).
  Proof.
    simpl. destruct sh => //= ; by rewrite app_comm_cons app_assoc.
  Qed.

  Lemma lfilled_to_val_app i lh es1 es2 LI vs :
    lfilled i lh (es1 ++ es2)%list LI ->
    to_val0 LI = Some vs ->
    (∃ vs', to_val0 es1 = Some vs' ∧ lfilled i lh ((iris.of_val0 vs') ++ es2) LI).
  Proof.
    intros Hfilled Hetov.
    destruct vs.
    - (* immV *)
      pose proof (filled_is_val_imm _ _ _ _ _ Hetov Hfilled) as
        [vs [es' [-> [-> [Hconst1 Hconst2]]]]].
      apply const_list_to_val in Hconst1 as (v1 & Hv1 & _).
      apply const_list_to_val in Hconst2 as (v2 & Hv2 & _).
      edestruct fill_val as [vs12 [Hvs12 Heql]];eauto.
      assert (Hvs12':=Hvs12). unfold to_val.
      apply to_val_cat in Hvs12' as [-> Hev2].
      apply iris.of_to_val0 in Hev2 as <-. eexists. split; eauto.
      rewrite -!of_val_imm.
      repeat rewrite v_to_e_is_fmap.
      erewrite <- fmap_app. rewrite take_drop.
      rewrite - v_to_e_is_fmap. rewrite of_val_imm.
      apply lfilled_Ind_Equivalent in Hfilled.
      inversion Hfilled;simplify_eq.
      erewrite of_to_val0;eauto.
      apply lfilled_Ind_Equivalent. constructor. auto. 
    - (* trapV *)
      apply to_val_trap_is_singleton in Hetov as Heq. subst.
      apply lfilled_Ind_Equivalent in Hfilled.
      inversion Hfilled.
      2: exfalso; do 2 destruct vs => //=.
      2-3: exfalso; do 2 destruct bef => //. 
      simplify_eq.
      apply app_eq_singleton in H as [[HH HH']|[HH HH']];subst.
      { exfalso. destruct es1,es2,es' => //=. }
      apply app_eq_singleton in HH' as [[HH HH']|[HH HH']];subst.
      { apply app_eq_singleton in HH as [[-> ->]|[-> ->]].
        simpl. eauto. eauto. }
      { apply app_nil in HH as [-> ->]. eauto. }
      
    - (* brV *)
      remember (length_rec LI) as n.
      assert (length_rec LI < S n) ; first lia.
      remember (S n) as m.
      clear Heqn Heqm n.
      generalize dependent i0. generalize dependent es1. generalize dependent lh.
      generalize dependent i.
      generalize dependent LI.
      induction m ; intros LI Hsize ; intros ; first lia.
      destruct es1 ; first eauto.
      unfold to_val, iris.to_val0 in Hetov ; simpl in Hetov.
      destruct LI ; first by inversion Hetov.
      destruct a0 ; try destruct b ; simpl in Hetov  => //.
      all: try by rewrite merge_notval in Hetov.
      + rewrite merge_br flatten_simplify in Hetov.
        inversion Hetov.
        apply Eqdep.EqdepTheory.inj_pair2 in H1 ; subst.
        eapply filled_is_val_br_base_app_cases in Hfilled as HH;[|eauto..].
        destruct HH as [-> [vs [es [-> HH]]]].
        destruct HH as [[es11 [es12 [Heq Hconst]]]
                       |[[es11 [es12 [Heq (Hconst & Hconst')]]]
                        |[es11 [es12 [Heq (Hconst&Hconst'&Hconst'')]]]]].
        * apply const_es_exists in Hconst as Hv.
          destruct Hv as [v Hv].
          exists (brV (VH_base i0 v es12)). rewrite -to_val_br_eq Heq -Hv.
          split;auto. rewrite Hv in Heq. erewrite of_to_val0. 2: apply to_val_br_eq.
          rewrite -Heq. auto. 
        * apply const_list_to_val in Hconst' as Hv.
          destruct Hv as (v & Hv & _).
          exists (immV v). split;auto. erewrite of_to_val0;eauto. 
        * apply const_list_to_val in Hconst as Hv.
          destruct Hv as (v & Hv & _).
          exists (immV v). split;auto. erewrite of_to_val0;eauto. 
        * unfold iris.to_val0 => /=.
          rewrite merge_br flatten_simplify => //=.
      + rewrite merge_return flatten_simplify in Hetov => //.
      + rewrite merge_prepend in Hetov.
        destruct (merge_values $ map _ _) eqn:Hmerge => //.
        2: destruct e => //.  
        destruct v0 => //.
        simpl in Hetov.
        rewrite - app_comm_cons in Hfilled.
        fold (AI_const (VAL_num v)) in Hfilled.
        apply lfilled_vLI in Hfilled as [(lh' & Hlh & Hfilled) | (-> & -> & aft & -> & <-)].
        * rewrite app_comm_cons in Hfilled.
          assert (length_rec LI < m) ;
            first by specialize (length_cons_rec (AI_basic $ BI_const v) LI) ; lia.
          specialize (IHm _ H _ _ _ Hfilled i1 lh1).
          unfold to_val0 in IHm at 1.
          unfold iris.to_val0 in IHm.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill).
          exists vs' ; split => //.
          subst ; by apply lfilled_prepend.
        * assert (lfilled 0 (LH_base [] aft) (es1 ++ es2) ((es1 ++ es2) ++ aft)).
          unfold lfilled, lfill => //=.
          assert (length_rec ((es1 ++ es2) ++ aft) < m).
          { specialize (length_cons_rec (AI_basic $ BI_const v)
                                        ((es1 ++ es2) ++ aft)) as H1.
            rewrite app_comm_cons in Hsize.
            repeat rewrite - cat_app in Hsize.
            rewrite app_comm_cons in H1.
            repeat rewrite - cat_app in H1.
            lia. }
          specialize (IHm _ H0 _ _ _ H i1 lh1).
          unfold to_val0 in IHm at 1.
          unfold iris.to_val0 in IHm.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill).
          remember (  match vs' with
                      | immV l' => (immV (VAL_num v :: l'))
                      | trapV => trapV
                      | @brV i vh => (brV (vh_push_const vh [VAL_num v]))
                      | retV lh => (retV (sh_push_const lh [VAL_num v]))
                      | callHostV tf h vcs lh => (callHostV tf h vcs (llh_push_const lh [VAL_num v]))
                      end ) as v'.
          exists  v'; split => //=.
          -- unfold to_val, iris.to_val0 => /=.
             rewrite merge_prepend.
             unfold to_val, iris.to_val0 in Htv.
             destruct (merge_values (map _ es1)) eqn:Hmerge1 => //=.
             inversion Htv; subst v0.
             destruct vs'; subst => //.
             assert (to_val0 es1 = Some trapV) ;
              first by unfold to_val, iris.to_val0 ; rewrite Hmerge1.
             apply to_val_trap_is_singleton in H1 as ->.
             simpl in Hmerge.
             rewrite merge_trap flatten_simplify in Hmerge.
             by destruct (es2 ++ aft).
          -- unfold lfilled, lfill => //=.
             unfold lfilled, lfill in Hfill ; simpl in Hfill.
             apply b2p in Hfill ; rewrite cat_app in Hfill. rewrite Hfill.
             subst v'. destruct vs' => //=.
             apply to_val_trap_is_singleton in Htv as ->.
             simpl in Hmerge.
             rewrite merge_trap flatten_simplify in Hmerge ; by destruct (es2 ++ aft).
             unfold iris.of_val. destruct lh => //.
             unfold iris.of_val. destruct s => //.
             unfold iris.of_val. destruct l0 => //. 
      + rewrite merge_prepend in Hetov.
        destruct (merge_values $ map _ _) eqn:Hmerge => //.
        2: destruct e => //.  
        destruct v => //.
        simpl in Hetov.
        rewrite - app_comm_cons in Hfilled.
        fold (AI_const (VAL_ref (VAL_ref_null r))) in Hfilled.
        apply lfilled_vLI in Hfilled as [(lh' & Hlh & Hfilled) | (-> & -> & aft & -> & <-)].
        * rewrite app_comm_cons in Hfilled.
          assert (length_rec LI < m) ;
            first by specialize (length_cons_rec (AI_basic $ BI_ref_null r) LI) ; lia.
          specialize (IHm _ H _ _ _ Hfilled i1 lh1).
          unfold to_val0 in IHm at 1.
          unfold iris.to_val0 in IHm.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill).
          exists vs' ; split => //.
          subst ; by apply lfilled_prepend.
        * assert (lfilled 0 (LH_base [] aft) (es1 ++ es2) ((es1 ++ es2) ++ aft)).
          unfold lfilled, lfill => //=.
          assert (length_rec ((es1 ++ es2) ++ aft) < m).
          { specialize (length_cons_rec (AI_basic $ BI_ref_null r)
                                        ((es1 ++ es2) ++ aft)) as H1.
            rewrite app_comm_cons in Hsize.
            repeat rewrite - cat_app in Hsize.
            rewrite app_comm_cons in H1.
            repeat rewrite - cat_app in H1.
            lia. }
          specialize (IHm _ H0 _ _ _ H i1 lh1).
          unfold to_val0 in IHm at 1.
          unfold iris.to_val0 in IHm.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill).
          remember (  match vs' with
                      | immV l' => (immV (VAL_ref (VAL_ref_null r) :: l'))
                      | trapV => trapV
                      | @brV i vh => (brV (vh_push_const vh [VAL_ref (VAL_ref_null r)]))
                      | retV lh => (retV (sh_push_const lh [VAL_ref (VAL_ref_null r)]))
                      | callHostV tf h vcs lh => (callHostV tf h vcs (llh_push_const lh [VAL_ref (VAL_ref_null r)]))
                      end ) as v'.
          exists  v'; split => //=.
          -- unfold to_val, iris.to_val0 => /=.
             rewrite merge_prepend.
             unfold to_val, iris.to_val0 in Htv.
             destruct (merge_values (map _ es1)) eqn:Hmerge1 => //=.
             inversion Htv; subst v.
             destruct vs'; subst => //.
             assert (to_val0 es1 = Some trapV) ;
              first by unfold to_val, iris.to_val0 ; rewrite Hmerge1.
             apply to_val_trap_is_singleton in H1 as ->.
             simpl in Hmerge.
             rewrite merge_trap flatten_simplify in Hmerge.
             by destruct (es2 ++ aft).
          -- unfold lfilled, lfill => //=.
             unfold lfilled, lfill in Hfill ; simpl in Hfill.
             apply b2p in Hfill ; rewrite cat_app in Hfill. rewrite Hfill.
             subst v'. destruct vs' => //=.
             apply to_val_trap_is_singleton in Htv as ->.
             simpl in Hmerge.
             rewrite merge_trap flatten_simplify in Hmerge ; by destruct (es2 ++ aft).
             unfold iris.of_val. destruct lh => //.
             unfold iris.of_val. destruct s => //.
             unfold iris.of_val. destruct l0 => //. 
            
           
      + rewrite merge_trap flatten_simplify in Hetov.
        by destruct LI.
      + rewrite merge_prepend in Hetov.
        destruct (merge_values $ map _ _) eqn:Hmerge => //.
        2: destruct e => //.  
        destruct v => //.
        simpl in Hetov.
        rewrite - app_comm_cons in Hfilled.
        fold (AI_const (VAL_ref (VAL_ref_func f))) in Hfilled.
        apply lfilled_vLI in Hfilled as [(lh' & Hlh & Hfilled) | (-> & -> & aft & -> & <-)].
        * rewrite app_comm_cons in Hfilled.
          assert (length_rec LI < m) ;
            first by specialize (length_cons_rec (AI_ref f) LI) ; lia.
          specialize (IHm _ H _ _ _ Hfilled i1 lh1).
          unfold to_val0 in IHm at 1.
          unfold iris.to_val0 in IHm.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill).
          exists vs' ; split => //.
          subst ; by apply lfilled_prepend.
        * assert (lfilled 0 (LH_base [] aft) (es1 ++ es2) ((es1 ++ es2) ++ aft)).
          unfold lfilled, lfill => //=.
          assert (length_rec ((es1 ++ es2) ++ aft) < m).
          { specialize (length_cons_rec (AI_ref f)
                                        ((es1 ++ es2) ++ aft)) as H1.
            rewrite app_comm_cons in Hsize.
            repeat rewrite - cat_app in Hsize.
            rewrite app_comm_cons in H1.
            repeat rewrite - cat_app in H1.
            lia. }
          specialize (IHm _ H0 _ _ _ H i1 lh1).
          unfold to_val0 in IHm at 1.
          unfold iris.to_val0 in IHm.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill).
          remember (  match vs' with
                      | immV l' => (immV (VAL_ref (VAL_ref_func f) :: l'))
                      | trapV => trapV
                      | @brV i vh => (brV (vh_push_const vh [VAL_ref (VAL_ref_func f)]))
                      | retV lh => (retV (sh_push_const lh [VAL_ref (VAL_ref_func f)]))
                      | callHostV tf h vcs lh => (callHostV tf h vcs (llh_push_const lh [VAL_ref (VAL_ref_func f)]))
                      end ) as v'.
          exists  v'; split => //=.
          -- unfold to_val, iris.to_val0 => /=.
             rewrite merge_prepend.
             unfold to_val, iris.to_val0 in Htv.
             destruct (merge_values (map _ es1)) eqn:Hmerge1 => //=.
             inversion Htv; subst v.
             destruct vs'; subst => //.
             assert (to_val0 es1 = Some trapV) ;
              first by unfold to_val, iris.to_val0 ; rewrite Hmerge1.
             apply to_val_trap_is_singleton in H1 as ->.
             simpl in Hmerge.
             rewrite merge_trap flatten_simplify in Hmerge.
             by destruct (es2 ++ aft).
          -- unfold lfilled, lfill => //=.
             unfold lfilled, lfill in Hfill ; simpl in Hfill.
             apply b2p in Hfill ; rewrite cat_app in Hfill. rewrite Hfill.
             subst v'. destruct vs' => //=.
             apply to_val_trap_is_singleton in Htv as ->.
             simpl in Hmerge.
             rewrite merge_trap flatten_simplify in Hmerge ; by destruct (es2 ++ aft).
             unfold iris.of_val. destruct lh => //.
             unfold iris.of_val. destruct s => //.
             unfold iris.of_val. destruct l0 => //.
      + rewrite merge_prepend in Hetov.
        destruct (merge_values $ map _ _) eqn:Hmerge => //.
        2: destruct e0 => //.  
        destruct v => //.
        simpl in Hetov.
        rewrite - app_comm_cons in Hfilled.
        fold (AI_const (VAL_ref (VAL_ref_exn e t))) in Hfilled.
        apply lfilled_vLI in Hfilled as [(lh' & Hlh & Hfilled) | (-> & -> & aft & -> & <-)].
        * rewrite app_comm_cons in Hfilled.
          assert (length_rec LI < m) ;
            first by specialize (length_cons_rec (AI_ref_exn e t) LI) ; lia.
          specialize (IHm _ H _ _ _ Hfilled i1 lh1).
          unfold to_val0 in IHm at 1.
          unfold iris.to_val0 in IHm.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill).
          exists vs' ; split => //.
          subst ; by apply lfilled_prepend.
        * assert (lfilled 0 (LH_base [] aft) (es1 ++ es2) ((es1 ++ es2) ++ aft)).
          unfold lfilled, lfill => //=.
          assert (length_rec ((es1 ++ es2) ++ aft) < m).
          { specialize (length_cons_rec (AI_ref_exn e t)
                                        ((es1 ++ es2) ++ aft)) as H1.
            rewrite app_comm_cons in Hsize.
            repeat rewrite - cat_app in Hsize.
            rewrite app_comm_cons in H1.
            repeat rewrite - cat_app in H1.
            lia. }
          specialize (IHm _ H0 _ _ _ H i1 lh1).
          unfold to_val0 in IHm at 1.
          unfold iris.to_val0 in IHm.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill).
          remember (  match vs' with
                      | immV l' => (immV (VAL_ref (VAL_ref_exn e t) :: l'))
                      | trapV => trapV
                      | @brV i vh => (brV (vh_push_const vh [VAL_ref (VAL_ref_exn e t)]))
                      | retV lh => (retV (sh_push_const lh [VAL_ref (VAL_ref_exn e t)]))
                      | callHostV tf h vcs lh => (callHostV tf h vcs (llh_push_const lh [VAL_ref (VAL_ref_exn e t)]))
                      end ) as v'.
          exists  v'; split => //=.
          -- unfold to_val, iris.to_val0 => /=.
             rewrite merge_prepend.
             unfold to_val, iris.to_val0 in Htv.
             destruct (merge_values (map _ es1)) eqn:Hmerge1 => //=.
             inversion Htv; subst v.
             destruct vs'; subst => //.
             assert (to_val0 es1 = Some trapV) ;
              first by unfold to_val, iris.to_val0 ; rewrite Hmerge1.
             apply to_val_trap_is_singleton in H1 as ->.
             simpl in Hmerge.
             rewrite merge_trap flatten_simplify in Hmerge.
             by destruct (es2 ++ aft).
          -- unfold lfilled, lfill => //=.
             unfold lfilled, lfill in Hfill ; simpl in Hfill.
             apply b2p in Hfill ; rewrite cat_app in Hfill. rewrite Hfill.
             subst v'. destruct vs' => //=.
             apply to_val_trap_is_singleton in Htv as ->.
             simpl in Hmerge.
             rewrite merge_trap flatten_simplify in Hmerge ; by destruct (es2 ++ aft).
             unfold iris.of_val. destruct lh => //.
             unfold iris.of_val. destruct s => //.
             unfold iris.of_val. destruct l0 => //.
      + rewrite merge_prepend in Hetov.
        destruct (merge_values $ map _ _) eqn:Hmerge => //.
        2: destruct e => //.  
        destruct v => //.
        simpl in Hetov.
        rewrite - app_comm_cons in Hfilled.
        fold (AI_const (VAL_ref (VAL_ref_cont f))) in Hfilled.
        apply lfilled_vLI in Hfilled as [(lh' & Hlh & Hfilled) | (-> & -> & aft & -> & <-)].
        * rewrite app_comm_cons in Hfilled.
          assert (length_rec LI < m) ;
            first by specialize (length_cons_rec (AI_ref_cont f) LI) ; lia.
          specialize (IHm _ H _ _ _ Hfilled i1 lh1).
          unfold to_val0 in IHm at 1.
          unfold iris.to_val0 in IHm.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill).
          exists vs' ; split => //.
          subst ; by apply lfilled_prepend.
        * assert (lfilled 0 (LH_base [] aft) (es1 ++ es2) ((es1 ++ es2) ++ aft)).
          unfold lfilled, lfill => //=.
          assert (length_rec ((es1 ++ es2) ++ aft) < m).
          { specialize (length_cons_rec (AI_ref_cont f)
                                        ((es1 ++ es2) ++ aft)) as H1.
            rewrite app_comm_cons in Hsize.
            repeat rewrite - cat_app in Hsize.
            rewrite app_comm_cons in H1.
            repeat rewrite - cat_app in H1.
            lia. }
          specialize (IHm _ H0 _ _ _ H i1 lh1).
          unfold to_val0 in IHm at 1.
          unfold iris.to_val0 in IHm.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill).
          remember (  match vs' with
                      | immV l' => (immV (VAL_ref (VAL_ref_cont f) :: l'))
                      | trapV => trapV
                      | @brV i vh => (brV (vh_push_const vh [VAL_ref (VAL_ref_cont f)]))
                      | retV lh => (retV (sh_push_const lh [VAL_ref (VAL_ref_cont f)]))
                      | callHostV tf h vcs lh => (callHostV tf h vcs (llh_push_const lh [VAL_ref (VAL_ref_cont f)]))
                      end ) as v'.
          exists  v'; split => //=.
          -- unfold to_val, iris.to_val0 => /=.
             rewrite merge_prepend.
             unfold to_val, iris.to_val0 in Htv.
             destruct (merge_values (map _ es1)) eqn:Hmerge1 => //=.
             inversion Htv; subst v.
             destruct vs'; subst => //.
             assert (to_val0 es1 = Some trapV) ;
              first by unfold to_val, iris.to_val0 ; rewrite Hmerge1.
             apply to_val_trap_is_singleton in H1 as ->.
             simpl in Hmerge.
             rewrite merge_trap flatten_simplify in Hmerge.
             by destruct (es2 ++ aft).
          -- unfold lfilled, lfill => //=.
             unfold lfilled, lfill in Hfill ; simpl in Hfill.
             apply b2p in Hfill ; rewrite cat_app in Hfill. rewrite Hfill.
             subst v'. destruct vs' => //=.
             apply to_val_trap_is_singleton in Htv as ->.
             simpl in Hmerge.
             rewrite merge_trap flatten_simplify in Hmerge ; by destruct (es2 ++ aft).
             unfold iris.of_val. destruct lh => //.
             unfold iris.of_val. destruct s => //.
             unfold iris.of_val. destruct l0 => //.
      + rewrite merge_throw in Hetov => //.
      + rewrite merge_suspend in Hetov => //.
      + rewrite merge_switch in Hetov => //. 
      + destruct (merge_values $ map _ _) eqn:Hmerge => //.
        * destruct v => // ;
                     (try by rewrite merge_notval in Hetov);
                     (try by rewrite merge_return flatten_simplify in Hetov) ;
                     try by rewrite merge_call_host flatten_simplify in Hetov.
          rewrite merge_br flatten_simplify in Hetov.
          inversion Hetov.
          destruct H0.
          apply Eqdep.EqdepTheory.inj_pair2 in H1 ; subst.
          assert (length_rec l0 < m).
          { unfold length_rec in Hsize ; simpl in Hsize. unfold length_rec. lia. }
          
          unfold lfilled, lfill in Hfilled ; 
            destruct lh ; fold lfill in Hfilled => //.
          1-2: destruct i => //.
          all: destruct (const_list l1) eqn:Hl1 => //.
          2-4: destruct (lfill _ _ _) eqn:Hfill => //.
          all: move/eqP in Hfilled.
          all: destruct l1 ; inversion Hfilled ; subst ; 
               last by unfold const_list in Hl1; inversion Hl1.
          -- eexists. split.
             ++ unfold to_val, iris.to_val0 => /=.
                rewrite Hmerge merge_br flatten_simplify => //.
             ++ unfold lfilled, lfill => //=.
                apply/eqP. repeat f_equal.
                assert (iris.to_val0 l0 = Some (brV lh1)) ;
                  first by unfold iris.to_val0 ; rewrite Hmerge.          
                apply iris.of_to_val0 in H0 as <-.
                unfold iris.of_val. 
                done.
          -- assert (lfilled i lh ((a :: es1) ++ es2) l4); 
               first by unfold lfilled ; rewrite Hfill.
             specialize (IHm l4 H i lh (a :: es1) H0 i1 lh1).
             unfold to_val0 in IHm at 1.
             unfold iris.to_val0 in IHm.
             rewrite Hmerge in IHm.
             destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill').
             eexists ; split => //.
             unfold lfilled, lfill ; fold lfill => //=.
             unfold lfilled in Hfill'. destruct (lfill _ _ (_ ++ _)) => //.
             apply b2p in Hfill' ; by subst.
        * destruct e => //=.
          rewrite merge_suspend in Hetov => //.
          rewrite merge_switch in Hetov => //.
          destruct (exnelts_of_exception_clauses _ _) => //.
          rewrite merge_throw in Hetov => //.
          rewrite merge_notval in Hetov => //.
        * rewrite merge_notval in Hetov => //.
      + destruct (merge_values $ map _ _) eqn:Hmerge => //.
        * destruct v => // ;
                     (try by rewrite merge_notval in Hetov);
                     (try by rewrite merge_return flatten_simplify in Hetov) ;
                     try by rewrite merge_call_host flatten_simplify in Hetov.
          rewrite merge_br flatten_simplify in Hetov.
          inversion Hetov.
          destruct H0.
          apply Eqdep.EqdepTheory.inj_pair2 in H1 ; subst.
          assert (length_rec l1 < m).
          { unfold length_rec in Hsize ; simpl in Hsize. unfold length_rec. lia. }
          
          unfold lfilled, lfill in Hfilled ; 
            destruct lh ; fold lfill in Hfilled => //.
          1-2: destruct i => //.
          all: destruct (const_list l2) eqn:Hl1 => //.
          2-4: destruct (lfill _ _ _) eqn:Hfill => //.
          all: move/eqP in Hfilled.
          all: destruct l2 ; inversion Hfilled ; subst ; 
               last by unfold const_list in Hl1; inversion Hl1.
          -- eexists. split.
             ++ unfold to_val, iris.to_val0 => /=.
                rewrite Hmerge merge_br flatten_simplify => //.
             ++ unfold lfilled, lfill => //=.
                apply/eqP. repeat f_equal.
                assert (iris.to_val0 l1 = Some (brV lh1)) ;
                  first by unfold iris.to_val0 ; rewrite Hmerge.          
                apply iris.of_to_val0 in H0 as <-.
                unfold iris.of_val. 
                done.
          -- assert (lfilled i lh ((a :: es1) ++ es2) l6); 
               first by unfold lfilled ; rewrite Hfill.
             specialize (IHm l6 H i lh (a :: es1) H0 i1 lh1).
             unfold to_val0 in IHm at 1.
             unfold iris.to_val0 in IHm.
             rewrite Hmerge in IHm.
             destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill').
             eexists ; split => //.
             unfold lfilled, lfill ; fold lfill => //=.
             unfold lfilled in Hfill'. destruct (lfill _ _ (_ ++ _)) => //.
             apply b2p in Hfill' ; by subst.
        * destruct e => //=.
          destruct (suselts_of_continuation_clauses _ _) => //. 
          rewrite merge_suspend in Hetov => //.
          rewrite merge_notval in Hetov => //.
          destruct (swelts_of_continuation_clauses _ _) => //. 
          rewrite merge_switch in Hetov => //.
          rewrite merge_notval in Hetov => //. 
          rewrite merge_throw in Hetov => //.
        * rewrite merge_notval in Hetov => //.
      + destruct (merge_values $ map _ _) eqn:Hmerge => //.
        * destruct v => // ;
                     (try by rewrite merge_notval in Hetov);
                     (try by rewrite merge_return flatten_simplify in Hetov) ;
                       try by rewrite merge_call_host flatten_simplify in Hetov.
          destruct i1; last destruct (vh_decrease _) eqn:Hdecr.
          all: try by rewrite merge_notval in Hetov.
          rewrite merge_br flatten_simplify in Hetov.
          inversion Hetov.
          destruct H0.
          apply Eqdep.EqdepTheory.inj_pair2 in H1 ; subst.
          assert (length_rec l0 < m).
          { unfold length_rec in Hsize ; simpl in Hsize. unfold length_rec. lia. }
          
          unfold lfilled, lfill in Hfilled ; 
            destruct lh ; fold lfill in Hfilled => //.
          1-2: destruct i => //.
          all: destruct (const_list l1) eqn:Hl1 => //.
          2-4: destruct (lfill _ _ _) eqn:Hfill => //.
          all: move/eqP in Hfilled.
          all: destruct l1 ; inversion Hfilled ; subst ; 
               last by unfold const_list in Hl1; inversion Hl1.
          -- eexists. split.
             ++ unfold to_val, iris.to_val0 => /=.
                rewrite Hmerge Hdecr merge_br flatten_simplify => //.
             ++ unfold lfilled, lfill => //=.
                apply/eqP. repeat f_equal.
                assert (iris.to_val0 l0 = Some (brV lh1)) ;
                  first by unfold iris.to_val0 ; rewrite Hmerge.          
                apply iris.of_to_val0 in H0 as <-.
                unfold iris.of_val0. by rewrite (vfill_decrease _ Hdecr). 
          -- assert (lfilled i lh ((a :: es1) ++ es2) l4); 
               first by unfold lfilled ; rewrite Hfill.
             specialize (IHm l4 H i lh (a :: es1) H0 (S i1) lh1).
             unfold to_val0 in IHm at 1.
             unfold iris.to_val0 in IHm.
             rewrite Hmerge in IHm.
             destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill').
             eexists ; split => //.
             unfold lfilled, lfill ; fold lfill => //=.
             unfold lfilled in Hfill'. destruct (lfill _ _ (_ ++ _)) => //.
             apply b2p in Hfill' ; by subst.
        * destruct e => //=.
          rewrite merge_suspend in Hetov => //.
          rewrite merge_switch in Hetov => //.
          rewrite merge_throw in Hetov => //.
        * rewrite merge_notval in Hetov => //.
      + destruct (merge_values $ map _ _) => //.
        * destruct v => //.
          all: try by rewrite merge_notval in Hetov.
          rewrite merge_call_host flatten_simplify in Hetov => //.
        * destruct e => //.
          rewrite merge_suspend in Hetov => //.
          rewrite merge_switch in Hetov => //.
          rewrite merge_throw in Hetov => //.
        * rewrite merge_notval in Hetov => //.
      + rewrite merge_call_host flatten_simplify in Hetov.
        by destruct LI. 
    - remember (length_rec LI) as n.
      assert (length_rec LI < S n) ; first lia.
      remember (S n) as m.
      clear Heqn Heqm n.
      generalize dependent s. generalize dependent es1. generalize dependent lh.
      generalize dependent i. 
      generalize dependent LI.
      induction m ; intros LI Hsize ; intros ; first lia.
      destruct es1 ; first eauto.
      unfold to_val, iris.to_val0 in Hetov ; simpl in Hetov.
      destruct LI ; first by inversion Hetov.
      destruct a0 ; try destruct b ; simpl in Hetov  => //.
      all: try by rewrite merge_notval in Hetov.
      + rewrite merge_br flatten_simplify in Hetov => //.
      + rewrite merge_return flatten_simplify in Hetov.
        inversion Hetov ; subst.
        eapply filled_is_val_ret_base_app_cases in Hfilled as HH;[|eauto..].
        destruct HH as [-> [vs [es [-> HH]]]].
        destruct HH as [[es11 [es12 [Heq Hconst]]]
                       |[[es11 [es12 [Heq (Hconst & Hconst')]]]
                        |[es11 [es12 [Heq (Hconst&Hconst'&Hconst'')]]]]].
        { apply const_es_exists in Hconst as Hv.
          destruct Hv as [v Hv].
          exists (retV (SH_base v es12)). rewrite -to_val_ret_eq Heq -Hv.
          split;auto. rewrite Hv in Heq. erewrite of_to_val0. 2: apply to_val_ret_eq.
          rewrite -Heq. auto. }
        { apply const_list_to_val in Hconst' as Hv.
          destruct Hv as (v & Hv & _).
          exists (immV v). split;auto. erewrite of_to_val0;eauto. }
        { apply const_list_to_val in Hconst as Hv.
          destruct Hv as (v & Hv & _).
          exists (immV v). split;auto. erewrite of_to_val0;eauto. }
        unfold iris.to_val0 => /=.
        rewrite merge_return flatten_simplify => //=.
      + rewrite merge_prepend in Hetov.
        destruct (merge_values $ map _ _) eqn:Hmerge => //.
        2: destruct e => //. 
        destruct v0 => //.
        simpl in Hetov.
        rewrite - app_comm_cons in Hfilled.
        fold (AI_const (VAL_num v)) in Hfilled.
        apply lfilled_vLI in Hfilled as [(lh' & Hlh & Hfilled) | (-> & -> & aft & -> & <-)].
        * rewrite app_comm_cons in Hfilled.
          assert (length_rec LI < m) ;
            first by specialize (length_cons_rec (AI_basic $ BI_const v) LI) ; lia.
          specialize (IHm _ H _ _ _ Hfilled s0).
          unfold to_val0 in IHm at 1.
          unfold iris.to_val0 in IHm.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill).
          exists vs' ; split => //.
          subst ; by apply lfilled_prepend.
        * assert (lfilled 0 (LH_base [] aft) (es1 ++ es2) ((es1 ++ es2) ++ aft)).
          unfold lfilled, lfill => //=.
          assert (length_rec ((es1 ++ es2) ++ aft) < m).
          { specialize (length_cons_rec (AI_basic $ BI_const v)
                                        ((es1 ++ es2) ++ aft)) as H1.
            rewrite app_comm_cons in Hsize.
            repeat rewrite - cat_app in Hsize.
            rewrite app_comm_cons in H1.
            repeat rewrite - cat_app in H1.
            lia. }
          specialize (IHm _ H0 _ _ _ H s0).
          unfold to_val0 in IHm at 1.
          unfold iris.to_val0 in IHm.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill).
          remember (  match vs' with
                      | immV l' => (immV (VAL_num v :: l'))
                      | trapV => trapV
                      | @brV i vh => (brV (vh_push_const vh [VAL_num v]))
                      | retV lh => (retV (sh_push_const lh [VAL_num v]))
                      | callHostV tf h vcs lh => (callHostV tf h vcs (llh_push_const lh [VAL_num v]))
                      end ) as v'.
          exists v' ; split; subst => //=. 
          -- unfold to_val, iris.to_val0 => /=.
             rewrite merge_prepend.
             unfold to_val, iris.to_val0 in Htv.
             destruct (merge_values (map _ es1)) eqn:Hmerge1 => //=.
             inversion Htv.
             destruct vs' => //.
             assert (to_val0 es1 = Some trapV) ;
              first by unfold to_val, iris.to_val0 ; rewrite Hmerge1 H2.
             apply to_val_trap_is_singleton in H1 as ->.
             simpl in Hmerge.
             rewrite merge_trap flatten_simplify in Hmerge.
             by destruct (es2 ++ aft).
          -- unfold lfilled, lfill => //=.
             unfold lfilled, lfill in Hfill ; simpl in Hfill.
             apply b2p in Hfill ; rewrite cat_app in Hfill. rewrite Hfill.
             destruct vs' => //.
             apply to_val_trap_is_singleton in Htv as ->.
             simpl in Hmerge.
             rewrite merge_trap flatten_simplify in Hmerge ; by destruct (es2 ++ aft).
             unfold iris.of_val. destruct lh => //.
             unfold iris.of_val. destruct s1 => //.
             unfold iris.of_val. destruct l0 => //.
 + rewrite merge_prepend in Hetov.
        destruct (merge_values $ map _ _) eqn:Hmerge => //.
        2: destruct e => //. 
        destruct v => //.
        simpl in Hetov.
        rewrite - app_comm_cons in Hfilled.
        fold (AI_const (VAL_ref $ VAL_ref_null r)) in Hfilled.
        apply lfilled_vLI in Hfilled as [(lh' & Hlh & Hfilled) | (-> & -> & aft & -> & <-)].
        * rewrite app_comm_cons in Hfilled.
          assert (length_rec LI < m) ;
            first by specialize (length_cons_rec (AI_basic $ BI_ref_null r) LI) ; lia.
          specialize (IHm _ H _ _ _ Hfilled s0).
          unfold to_val0 in IHm at 1.
          unfold iris.to_val0 in IHm.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill).
          exists vs' ; split => //.
          subst ; by apply lfilled_prepend.
        * assert (lfilled 0 (LH_base [] aft) (es1 ++ es2) ((es1 ++ es2) ++ aft)).
          unfold lfilled, lfill => //=.
          assert (length_rec ((es1 ++ es2) ++ aft) < m).
          { specialize (length_cons_rec (AI_basic $ BI_ref_null r)
                                        ((es1 ++ es2) ++ aft)) as H1.
            rewrite app_comm_cons in Hsize.
            repeat rewrite - cat_app in Hsize.
            rewrite app_comm_cons in H1.
            repeat rewrite - cat_app in H1.
            lia. }
          specialize (IHm _ H0 _ _ _ H s0).
          unfold to_val0 in IHm at 1.
          unfold iris.to_val0 in IHm.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill).
          remember (  match vs' with
                      | immV l' => (immV (VAL_ref (VAL_ref_null r) :: l'))
                      | trapV => trapV
                      | @brV i vh => (brV (vh_push_const vh [VAL_ref $ VAL_ref_null r]))
                      | retV lh => (retV (sh_push_const lh [VAL_ref $ VAL_ref_null r]))
                      | callHostV tf h vcs lh => (callHostV tf h vcs (llh_push_const lh [VAL_ref $ VAL_ref_null r]))
                      end ) as v'.
          exists v' ; split; subst => //=. 
          -- unfold to_val, iris.to_val0 => /=.
             rewrite merge_prepend.
             unfold to_val, iris.to_val0 in Htv.
             destruct (merge_values (map _ es1)) eqn:Hmerge1 => //=.
             inversion Htv.
             destruct vs' => //.
             assert (to_val0 es1 = Some trapV) ;
              first by unfold to_val, iris.to_val0 ; rewrite Hmerge1 H2.
             apply to_val_trap_is_singleton in H1 as ->.
             simpl in Hmerge.
             rewrite merge_trap flatten_simplify in Hmerge.
             by destruct (es2 ++ aft).
          -- unfold lfilled, lfill => //=.
             unfold lfilled, lfill in Hfill ; simpl in Hfill.
             apply b2p in Hfill ; rewrite cat_app in Hfill. rewrite Hfill.
             destruct vs' => //.
             apply to_val_trap_is_singleton in Htv as ->.
             simpl in Hmerge.
             rewrite merge_trap flatten_simplify in Hmerge ; by destruct (es2 ++ aft).
             unfold iris.of_val. destruct lh => //.
             unfold iris.of_val. destruct s1 => //.
             unfold iris.of_val. destruct l0 => //.
      + rewrite merge_trap flatten_simplify in Hetov.
        by destruct LI.
      + rewrite merge_prepend in Hetov.
        destruct (merge_values $ map _ _) eqn:Hmerge => //.
        2: destruct e => //. 
        destruct v => //.
        simpl in Hetov.
        rewrite - app_comm_cons in Hfilled.
        fold (AI_const (VAL_ref $ VAL_ref_func f)) in Hfilled.
        apply lfilled_vLI in Hfilled as [(lh' & Hlh & Hfilled) | (-> & -> & aft & -> & <-)].
        * rewrite app_comm_cons in Hfilled.
          assert (length_rec LI < m) ;
            first by specialize (length_cons_rec (AI_ref f) LI) ; lia.
          specialize (IHm _ H _ _ _ Hfilled s0).
          unfold to_val0 in IHm at 1.
          unfold iris.to_val0 in IHm.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill).
          exists vs' ; split => //.
          subst ; by apply lfilled_prepend.
        * assert (lfilled 0 (LH_base [] aft) (es1 ++ es2) ((es1 ++ es2) ++ aft)).
          unfold lfilled, lfill => //=.
          assert (length_rec ((es1 ++ es2) ++ aft) < m).
          { specialize (length_cons_rec (AI_ref f)
                                        ((es1 ++ es2) ++ aft)) as H1.
            rewrite app_comm_cons in Hsize.
            repeat rewrite - cat_app in Hsize.
            rewrite app_comm_cons in H1.
            repeat rewrite - cat_app in H1.
            lia. }
          specialize (IHm _ H0 _ _ _ H s0).
          unfold to_val0 in IHm at 1.
          unfold iris.to_val0 in IHm.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill).
          remember (  match vs' with
                      | immV l' => (immV (VAL_ref (VAL_ref_func f) :: l'))
                      | trapV => trapV
                      | @brV i vh => (brV (vh_push_const vh [VAL_ref $ VAL_ref_func f]))
                      | retV lh => (retV (sh_push_const lh [VAL_ref $ VAL_ref_func f]))
                      | callHostV tf h vcs lh => (callHostV tf h vcs (llh_push_const lh [VAL_ref $ VAL_ref_func f]))
                      end ) as v'.
          exists v' ; split; subst => //=. 
          -- unfold to_val, iris.to_val0 => /=.
             rewrite merge_prepend.
             unfold to_val, iris.to_val0 in Htv.
             destruct (merge_values (map _ es1)) eqn:Hmerge1 => //=.
             inversion Htv.
             destruct vs' => //.
             assert (to_val0 es1 = Some trapV) ;
              first by unfold to_val, iris.to_val0 ; rewrite Hmerge1 H2.
             apply to_val_trap_is_singleton in H1 as ->.
             simpl in Hmerge.
             rewrite merge_trap flatten_simplify in Hmerge.
             by destruct (es2 ++ aft).
          -- unfold lfilled, lfill => //=.
             unfold lfilled, lfill in Hfill ; simpl in Hfill.
             apply b2p in Hfill ; rewrite cat_app in Hfill. rewrite Hfill.
             destruct vs' => //.
             apply to_val_trap_is_singleton in Htv as ->.
             simpl in Hmerge.
             rewrite merge_trap flatten_simplify in Hmerge ; by destruct (es2 ++ aft).
             unfold iris.of_val. destruct lh => //.
             unfold iris.of_val. destruct s1 => //.
             unfold iris.of_val. destruct l0 => //.
      + rewrite merge_prepend in Hetov.
        destruct (merge_values $ map _ _) eqn:Hmerge => //.
        2: destruct e0 => //. 
        destruct v => //.
        simpl in Hetov.
        rewrite - app_comm_cons in Hfilled.
        fold (AI_const (VAL_ref $ VAL_ref_exn e t)) in Hfilled.
        apply lfilled_vLI in Hfilled as [(lh' & Hlh & Hfilled) | (-> & -> & aft & -> & <-)].
        * rewrite app_comm_cons in Hfilled.
          assert (length_rec LI < m) ;
            first by specialize (length_cons_rec (AI_ref_exn e t) LI) ; lia.
          specialize (IHm _ H _ _ _ Hfilled s0).
          unfold to_val0 in IHm at 1.
          unfold iris.to_val0 in IHm.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill).
          exists vs' ; split => //.
          subst ; by apply lfilled_prepend.
        * assert (lfilled 0 (LH_base [] aft) (es1 ++ es2) ((es1 ++ es2) ++ aft)).
          unfold lfilled, lfill => //=.
          assert (length_rec ((es1 ++ es2) ++ aft) < m).
          { specialize (length_cons_rec (AI_ref_exn e t)
                                        ((es1 ++ es2) ++ aft)) as H1.
            rewrite app_comm_cons in Hsize.
            repeat rewrite - cat_app in Hsize.
            rewrite app_comm_cons in H1.
            repeat rewrite - cat_app in H1.
            lia. }
          specialize (IHm _ H0 _ _ _ H s0).
          unfold to_val0 in IHm at 1.
          unfold iris.to_val0 in IHm.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill).
          remember (  match vs' with
                      | immV l' => (immV (VAL_ref (VAL_ref_exn e t) :: l'))
                      | trapV => trapV
                      | @brV i vh => (brV (vh_push_const vh [VAL_ref $ VAL_ref_exn e t]))
                      | retV lh => (retV (sh_push_const lh [VAL_ref $ VAL_ref_exn e t]))
                      | callHostV tf h vcs lh => (callHostV tf h vcs (llh_push_const lh [VAL_ref $ VAL_ref_exn e t]))
                      end ) as v'.
          exists v' ; split; subst => //=. 
          -- unfold to_val, iris.to_val0 => /=.
             rewrite merge_prepend.
             unfold to_val, iris.to_val0 in Htv.
             destruct (merge_values (map _ es1)) eqn:Hmerge1 => //=.
             inversion Htv.
             destruct vs' => //.
             assert (to_val0 es1 = Some trapV) ;
              first by unfold to_val, iris.to_val0 ; rewrite Hmerge1 H2.
             apply to_val_trap_is_singleton in H1 as ->.
             simpl in Hmerge.
             rewrite merge_trap flatten_simplify in Hmerge.
             by destruct (es2 ++ aft).
          -- unfold lfilled, lfill => //=.
             unfold lfilled, lfill in Hfill ; simpl in Hfill.
             apply b2p in Hfill ; rewrite cat_app in Hfill. rewrite Hfill.
             destruct vs' => //.
             apply to_val_trap_is_singleton in Htv as ->.
             simpl in Hmerge.
             rewrite merge_trap flatten_simplify in Hmerge ; by destruct (es2 ++ aft).
             unfold iris.of_val. destruct lh => //.
             unfold iris.of_val. destruct s1 => //.
             unfold iris.of_val. destruct l0 => //.
      + rewrite merge_prepend in Hetov.
        destruct (merge_values $ map _ _) eqn:Hmerge => //.
        2: destruct e => //. 
        destruct v => //.
        simpl in Hetov.
        rewrite - app_comm_cons in Hfilled.
        fold (AI_const (VAL_ref $ VAL_ref_cont f)) in Hfilled.
        apply lfilled_vLI in Hfilled as [(lh' & Hlh & Hfilled) | (-> & -> & aft & -> & <-)].
        * rewrite app_comm_cons in Hfilled.
          assert (length_rec LI < m) ;
            first by specialize (length_cons_rec (AI_ref_cont f) LI) ; lia.
          specialize (IHm _ H _ _ _ Hfilled s0).
          unfold to_val0 in IHm at 1.
          unfold iris.to_val0 in IHm.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill).
          exists vs' ; split => //.
          subst ; by apply lfilled_prepend.
        * assert (lfilled 0 (LH_base [] aft) (es1 ++ es2) ((es1 ++ es2) ++ aft)).
          unfold lfilled, lfill => //=.
          assert (length_rec ((es1 ++ es2) ++ aft) < m).
          { specialize (length_cons_rec (AI_ref_cont f)
                                        ((es1 ++ es2) ++ aft)) as H1.
            rewrite app_comm_cons in Hsize.
            repeat rewrite - cat_app in Hsize.
            rewrite app_comm_cons in H1.
            repeat rewrite - cat_app in H1.
            lia. }
          specialize (IHm _ H0 _ _ _ H s0).
          unfold to_val0 in IHm at 1.
          unfold iris.to_val0 in IHm.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill).
          remember (  match vs' with
                      | immV l' => (immV (VAL_ref (VAL_ref_cont f) :: l'))
                      | trapV => trapV
                      | @brV i vh => (brV (vh_push_const vh [VAL_ref $ VAL_ref_cont f]))
                      | retV lh => (retV (sh_push_const lh [VAL_ref $ VAL_ref_cont f]))
                      | callHostV tf h vcs lh => (callHostV tf h vcs (llh_push_const lh [VAL_ref $ VAL_ref_cont f]))
                      end ) as v'.
          exists v' ; split; subst => //=. 
          -- unfold to_val, iris.to_val0 => /=.
             rewrite merge_prepend.
             unfold to_val, iris.to_val0 in Htv.
             destruct (merge_values (map _ es1)) eqn:Hmerge1 => //=.
             inversion Htv.
             destruct vs' => //.
             assert (to_val0 es1 = Some trapV) ;
              first by unfold to_val, iris.to_val0 ; rewrite Hmerge1 H2.
             apply to_val_trap_is_singleton in H1 as ->.
             simpl in Hmerge.
             rewrite merge_trap flatten_simplify in Hmerge.
             by destruct (es2 ++ aft).
          -- unfold lfilled, lfill => //=.
             unfold lfilled, lfill in Hfill ; simpl in Hfill.
             apply b2p in Hfill ; rewrite cat_app in Hfill. rewrite Hfill.
             destruct vs' => //.
             apply to_val_trap_is_singleton in Htv as ->.
             simpl in Hmerge.
             rewrite merge_trap flatten_simplify in Hmerge ; by destruct (es2 ++ aft).
             unfold iris.of_val. destruct lh => //.
             unfold iris.of_val. destruct s1 => //.
             unfold iris.of_val. destruct l0 => //.
      + rewrite merge_throw in Hetov => //.
      + rewrite merge_suspend in Hetov => //.
      + rewrite merge_switch in Hetov => //. 
    + destruct (merge_values $ map _ _) eqn:Hmerge => //.
      * destruct v => //.
        all: try by rewrite merge_notval in Hetov.
        -- rewrite merge_br flatten_simplify in Hetov => //.
        -- rewrite merge_return flatten_simplify in Hetov.
           inversion Hetov ; subst.
           assert (length_rec l0 < m).
           { unfold length_rec in Hsize ; simpl in Hsize. unfold length_rec. lia. }
           unfold lfilled, lfill in Hfilled ; 
             destruct lh ; fold lfill in Hfilled => //.
           1-2: destruct i => //.
           all: destruct (const_list l1) eqn:Hl1 => //.
           2-4: destruct (lfill _ _ _) eqn:Hfill => //.
           all: move/eqP in Hfilled.
           all: destruct l1 ; inversion Hfilled ; subst ; 
             last by unfold const_list in Hl1; inversion Hl1.
           ++ eexists. split.
              ** unfold to_val, iris.to_val0 => /=.
                 rewrite Hmerge merge_return flatten_simplify => //.
              ** unfold lfilled, lfill => //=.
                 replace l0 with (sfill s0 [AI_basic BI_return]) ; first done.
                 assert (iris.to_val0 l0 = Some (retV s0)) ;
                   first by unfold iris.to_val0 ; rewrite Hmerge.          
                 apply iris.of_to_val0 in H0 as <-.
                 unfold iris.of_val. done.
           ++ assert (lfilled i lh ((a :: es1) ++ es2) l4); 
                first by unfold lfilled ; rewrite Hfill.
              specialize (IHm l4 H i lh (a :: es1) H0 s0).
              unfold to_val0 in IHm at 1.
              unfold iris.to_val0 in IHm.
              rewrite Hmerge in IHm.
              destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill').
              eexists ; split => //.
              unfold lfilled, lfill ; fold lfill => //=.
              unfold lfilled in Hfill'. destruct (lfill _ _ (_ ++ _)) => //.
              apply b2p in Hfill' ; by subst.
        -- rewrite merge_call_host flatten_simplify in Hetov => //.
      * destruct e => //.
        rewrite merge_suspend in Hetov => //.
        rewrite merge_switch in Hetov => //.
        destruct (exnelts_of_exception_clauses _ _) => //. 
        rewrite merge_throw in Hetov => //.
        rewrite merge_notval in Hetov => //. 
      * rewrite merge_notval in Hetov => //.
    + destruct (merge_values $ map _ _) eqn:Hmerge => //.
      * destruct v => //.
        all: try by rewrite merge_notval in Hetov.
        -- rewrite merge_br flatten_simplify in Hetov => //.
        -- rewrite merge_return flatten_simplify in Hetov.
           inversion Hetov ; subst.
           assert (length_rec l1 < m).
           { unfold length_rec in Hsize ; simpl in Hsize. unfold length_rec. lia. }
           unfold lfilled, lfill in Hfilled ; 
             destruct lh ; fold lfill in Hfilled => //.
           1-2: destruct i => //.
           all: destruct (const_list l2) eqn:Hl1 => //.
           2-4: destruct (lfill _ _ _) eqn:Hfill => //.
           all: move/eqP in Hfilled.
           all: destruct l2 ; inversion Hfilled ; subst ; 
             last by unfold const_list in Hl1; inversion Hl1.
           ++ eexists. split.
              ** unfold to_val, iris.to_val0 => /=.
                 rewrite Hmerge merge_return flatten_simplify => //.
              ** unfold lfilled, lfill => //=.
                 replace l1 with (sfill s0 [AI_basic BI_return]) ; first done.
                 assert (iris.to_val0 l1 = Some (retV s0)) ;
                   first by unfold iris.to_val0 ; rewrite Hmerge.          
                 apply iris.of_to_val0 in H0 as <-.
                 unfold iris.of_val. done.
           ++ assert (lfilled i lh ((a :: es1) ++ es2) l6); 
                first by unfold lfilled ; rewrite Hfill.
              specialize (IHm l6 H i lh (a :: es1) H0 s0).
              unfold to_val0 in IHm at 1.
              unfold iris.to_val0 in IHm.
              rewrite Hmerge in IHm.
              destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill').
              eexists ; split => //.
              unfold lfilled, lfill ; fold lfill => //=.
              unfold lfilled in Hfill'. destruct (lfill _ _ (_ ++ _)) => //.
              apply b2p in Hfill' ; by subst.
        -- rewrite merge_call_host flatten_simplify in Hetov => //.
      * destruct e => //.
        destruct (suselts_of_continuation_clauses _ _) => //. 
        rewrite merge_suspend in Hetov => //.
        rewrite merge_notval in Hetov => //.
        destruct (swelts_of_continuation_clauses _ _) => //. 
        rewrite merge_switch in Hetov => //.
        rewrite merge_notval in Hetov => //. 
        rewrite merge_throw in Hetov => //.
      * rewrite merge_notval in Hetov => //.
    + destruct (merge_values $ map _ _) eqn:Hmerge => //.
      * destruct v => //.
        all: try by rewrite merge_notval in Hetov.
        -- destruct i0; last destruct (vh_decrease _) eqn:Hdecr.
           all: try by rewrite merge_notval in Hetov.
           rewrite merge_br flatten_simplify in Hetov => //.
        -- rewrite merge_return flatten_simplify in Hetov.
           inversion Hetov ; subst.
           assert (length_rec l0 < m).
           { unfold length_rec in Hsize ; simpl in Hsize. unfold length_rec. lia. }
           unfold lfilled, lfill in Hfilled ; 
             destruct lh ; fold lfill in Hfilled => //.
           1-2: destruct i => //.
           all: destruct (const_list l1) eqn:Hl1 => //.
           2-4: destruct (lfill _ _ _) eqn:Hfill => //.
           all: move/eqP in Hfilled.
           all: destruct l1 ; inversion Hfilled ; subst ; 
             last by unfold const_list in Hl1; inversion Hl1.
           ++ eexists. split.
              ** unfold to_val, iris.to_val0 => /=.
                 rewrite Hmerge merge_return flatten_simplify => //.
              ** unfold lfilled, lfill => //=.
                 replace l0 with (sfill s0 [AI_basic BI_return]) ; first done.
                 assert (iris.to_val0 l0 = Some (retV s0)) ;
                   first by unfold iris.to_val0 ; rewrite Hmerge.          
                 apply iris.of_to_val0 in H0 as <-.
                 unfold iris.of_val. done.
           ++ assert (lfilled i lh ((a :: es1) ++ es2) l4); 
                first by unfold lfilled ; rewrite Hfill.
              specialize (IHm l4 H i lh (a :: es1) H0 s0).
              unfold to_val0 in IHm at 1.
              unfold iris.to_val0 in IHm.
              rewrite Hmerge in IHm.
              destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill').
              eexists ; split => //.
              unfold lfilled, lfill ; fold lfill => //=.
              unfold lfilled in Hfill'. destruct (lfill _ _ (_ ++ _)) => //.
              apply b2p in Hfill' ; by subst.
        -- rewrite merge_call_host flatten_simplify in Hetov => //.
      * destruct e => //.
        rewrite merge_suspend in Hetov => //.
        rewrite merge_switch in Hetov => //.
        rewrite merge_throw in Hetov => //.
      * rewrite merge_notval in Hetov => //. 
    + destruct (merge_values $ map _ _) => //.
      destruct v => //.
      all: try by rewrite merge_notval in Hetov.
      rewrite merge_call_host flatten_simplify in Hetov => //.
      destruct e => //.
      rewrite merge_suspend in Hetov => //.
      rewrite merge_switch in Hetov => //.
      rewrite merge_throw in Hetov => //. 
    + rewrite merge_call_host flatten_simplify in Hetov. done. 
    - remember (length_rec LI) as n.
      assert (length_rec LI < S n) ; first lia.
      remember (S n) as m.
      clear Heqn Heqm n.
      generalize dependent l0.
      generalize dependent es1. generalize dependent lh.
      generalize dependent i. 
      generalize dependent LI.
      induction m ; intros LI Hsize ; intros ; first lia.
      destruct es1 ; first eauto.
      unfold to_val, iris.to_val0 in Hetov ; simpl in Hetov.
      destruct LI ; first by inversion Hetov.
      destruct a0 ; try destruct b ; simpl in Hetov  => //.
      all: try by rewrite merge_notval in Hetov.
      + rewrite merge_br flatten_simplify in Hetov => //.
      + rewrite merge_return flatten_simplify in Hetov => //.
      + rewrite merge_prepend in Hetov.
        destruct (merge_values $ map _ _) eqn:Hmerge => //.
        2: destruct e => //. 
        destruct v0 => //.
        simpl in Hetov.
        inversion Hetov ; subst.
        rewrite - app_comm_cons in Hfilled.
        fold (AI_const (VAL_num v)) in Hfilled.
        apply lfilled_vLI in Hfilled as [(lh' & Hlh & Hfilled) | (-> & -> & aft & -> & <-)].
        * rewrite app_comm_cons in Hfilled.
          assert (length_rec LI < m) ;
            first by specialize (length_cons_rec (AI_basic $ BI_const v) LI) ; lia.
          specialize (IHm _ H _ _ _ Hfilled l2).
          unfold to_val0 in IHm at 1.
          unfold iris.to_val0 in IHm.
          rewrite Hmerge in IHm.
          
          destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill).
          exists vs' ; split => //.
          subst ; by apply lfilled_prepend.
        * assert (lfilled 0 (LH_base [] aft) (es1 ++ es2) ((es1 ++ es2) ++ aft)).
          unfold lfilled, lfill => //=.
          assert (length_rec ((es1 ++ es2) ++ aft) < m).
          { specialize (length_cons_rec (AI_basic $ BI_const v)
                                        ((es1 ++ es2) ++ aft)) as H1.
            rewrite app_comm_cons in Hsize.
            repeat rewrite - cat_app in Hsize.
            rewrite app_comm_cons in H1.
            repeat rewrite - cat_app in H1.
            lia. }
          specialize (IHm _ H0 _ _ _ H l2).
          unfold to_val0 in IHm at 1.
          unfold iris.to_val0 in IHm.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill).
            remember (  match vs' with
                      | immV l' => (immV (VAL_num v :: l'))
                      | trapV => trapV
                      | @brV i vh => (brV (vh_push_const vh [VAL_num v]))
                      | retV lh => (retV (sh_push_const lh [VAL_num v]))
                      | callHostV tf h vcs lh => (callHostV tf h vcs (llh_push_const lh [VAL_num v]))
                      end ) as v'.
          exists v' ; split; subst => //=.
          -- unfold to_val, iris.to_val0 => /=.
            rewrite merge_prepend.
            unfold to_val, iris.to_val0 in Htv.
            destruct (merge_values (map _ es1)) eqn:Hmerge1 => //=.
            inversion Htv.
            destruct vs' => //.
            assert (to_val0 es1 = Some trapV) ;
              first by unfold to_val, iris.to_val0 ; rewrite Hmerge1 H2.
            apply to_val_trap_is_singleton in H1 as ->.
            simpl in Hmerge.
            rewrite merge_trap flatten_simplify in Hmerge.
            by destruct (es2 ++ aft).
          -- unfold lfilled, lfill => //=.
            unfold lfilled, lfill in Hfill ; simpl in Hfill.
            apply b2p in Hfill ; rewrite cat_app in Hfill. rewrite Hfill.
            destruct vs' => //.
            apply to_val_trap_is_singleton in Htv as ->.
            simpl in Hmerge.
            rewrite merge_trap flatten_simplify in Hmerge ; by destruct (es2 ++ aft).
            unfold iris.of_val. destruct lh => //.
            unfold iris.of_val. destruct s => //.
            unfold iris.of_val. destruct l1 => //.
          + rewrite merge_prepend in Hetov.
        destruct (merge_values $ map _ _) eqn:Hmerge => //.
        2: destruct e => //. 
        destruct v => //.
        simpl in Hetov.
        inversion Hetov ; subst.
        rewrite - app_comm_cons in Hfilled.
        fold (AI_const (VAL_ref (VAL_ref_null r))) in Hfilled.
        apply lfilled_vLI in Hfilled as [(lh' & Hlh & Hfilled) | (-> & -> & aft & -> & <-)].
        * rewrite app_comm_cons in Hfilled.
          assert (length_rec LI < m) ;
            first by specialize (length_cons_rec (AI_basic $ BI_ref_null r) LI) ; lia.
          specialize (IHm _ H _ _ _ Hfilled l2).
          unfold to_val0 in IHm at 1.
          unfold iris.to_val0 in IHm.
          rewrite Hmerge in IHm.
          
          destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill).
          exists vs' ; split => //.
          subst ; by apply lfilled_prepend.
        * assert (lfilled 0 (LH_base [] aft) (es1 ++ es2) ((es1 ++ es2) ++ aft)).
          unfold lfilled, lfill => //=.
          assert (length_rec ((es1 ++ es2) ++ aft) < m).
          { specialize (length_cons_rec (AI_basic $ BI_ref_null r)
                                        ((es1 ++ es2) ++ aft)) as H1.
            rewrite app_comm_cons in Hsize.
            repeat rewrite - cat_app in Hsize.
            rewrite app_comm_cons in H1.
            repeat rewrite - cat_app in H1.
            lia. }
          specialize (IHm _ H0 _ _ _ H l2).
          unfold to_val0 in IHm at 1.
          unfold iris.to_val0 in IHm.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill).
            remember (  match vs' with
                      | immV l' => (immV (VAL_ref (VAL_ref_null r) :: l'))
                      | trapV => trapV
                      | @brV i vh => (brV (vh_push_const vh [VAL_ref (VAL_ref_null r)]))
                      | retV lh => (retV (sh_push_const lh [VAL_ref (VAL_ref_null r)]))
                      | callHostV tf h vcs lh => (callHostV tf h vcs (llh_push_const lh [VAL_ref (VAL_ref_null r)]))
                      end ) as v'.
          exists v' ; split; subst => //=.
          -- unfold to_val, iris.to_val0 => /=.
            rewrite merge_prepend.
            unfold to_val, iris.to_val0 in Htv.
            destruct (merge_values (map _ es1)) eqn:Hmerge1 => //=.
            inversion Htv.
            destruct vs' => //.
            assert (to_val0 es1 = Some trapV) ;
              first by unfold to_val, iris.to_val0 ; rewrite Hmerge1 H2.
            apply to_val_trap_is_singleton in H1 as ->.
            simpl in Hmerge.
            rewrite merge_trap flatten_simplify in Hmerge.
            by destruct (es2 ++ aft).
          -- unfold lfilled, lfill => //=.
            unfold lfilled, lfill in Hfill ; simpl in Hfill.
            apply b2p in Hfill ; rewrite cat_app in Hfill. rewrite Hfill.
            destruct vs' => //.
            apply to_val_trap_is_singleton in Htv as ->.
            simpl in Hmerge.
            rewrite merge_trap flatten_simplify in Hmerge ; by destruct (es2 ++ aft).
            unfold iris.of_val. destruct lh => //.
            unfold iris.of_val. destruct s => //.
            unfold iris.of_val. destruct l1 => //.
    + rewrite merge_trap flatten_simplify in Hetov.
        by destruct LI.
          + rewrite merge_prepend in Hetov.
        destruct (merge_values $ map _ _) eqn:Hmerge => //.
        2: destruct e => //. 
        destruct v => //.
        simpl in Hetov.
        inversion Hetov ; subst.
        rewrite - app_comm_cons in Hfilled.
        fold (AI_const (VAL_ref (VAL_ref_func f0))) in Hfilled.
        apply lfilled_vLI in Hfilled as [(lh' & Hlh & Hfilled) | (-> & -> & aft & -> & <-)].
        * rewrite app_comm_cons in Hfilled.
          assert (length_rec LI < m) ;
            first by specialize (length_cons_rec (AI_ref f0) LI) ; lia.
          specialize (IHm _ H _ _ _ Hfilled l2).
          unfold to_val0 in IHm at 1.
          unfold iris.to_val0 in IHm.
          rewrite Hmerge in IHm.
          
          destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill).
          exists vs' ; split => //.
          subst ; by apply lfilled_prepend.
        * assert (lfilled 0 (LH_base [] aft) (es1 ++ es2) ((es1 ++ es2) ++ aft)).
          unfold lfilled, lfill => //=.
          assert (length_rec ((es1 ++ es2) ++ aft) < m).
          { specialize (length_cons_rec (AI_ref f0)
                                        ((es1 ++ es2) ++ aft)) as H1.
            rewrite app_comm_cons in Hsize.
            repeat rewrite - cat_app in Hsize.
            rewrite app_comm_cons in H1.
            repeat rewrite - cat_app in H1.
            lia. }
          specialize (IHm _ H0 _ _ _ H l2).
          unfold to_val0 in IHm at 1.
          unfold iris.to_val0 in IHm.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill).
            remember (  match vs' with
                      | immV l' => (immV (VAL_ref (VAL_ref_func f0) :: l'))
                      | trapV => trapV
                      | @brV i vh => (brV (vh_push_const vh [VAL_ref (VAL_ref_func f0)]))
                      | retV lh => (retV (sh_push_const lh [VAL_ref (VAL_ref_func f0)]))
                      | callHostV tf h vcs lh => (callHostV tf h vcs (llh_push_const lh [VAL_ref (VAL_ref_func f0)]))
                      end ) as v'.
          exists v' ; split; subst => //=.
          -- unfold to_val, iris.to_val0 => /=.
            rewrite merge_prepend.
            unfold to_val, iris.to_val0 in Htv.
            destruct (merge_values (map _ es1)) eqn:Hmerge1 => //=.
            inversion Htv.
            destruct vs' => //.
            assert (to_val0 es1 = Some trapV) ;
              first by unfold to_val, iris.to_val0 ; rewrite Hmerge1 H2.
            apply to_val_trap_is_singleton in H1 as ->.
            simpl in Hmerge.
            rewrite merge_trap flatten_simplify in Hmerge.
            by destruct (es2 ++ aft).
          -- unfold lfilled, lfill => //=.
            unfold lfilled, lfill in Hfill ; simpl in Hfill.
            apply b2p in Hfill ; rewrite cat_app in Hfill. rewrite Hfill.
            destruct vs' => //.
            apply to_val_trap_is_singleton in Htv as ->.
            simpl in Hmerge.
            rewrite merge_trap flatten_simplify in Hmerge ; by destruct (es2 ++ aft).
            unfold iris.of_val. destruct lh => //.
            unfold iris.of_val. destruct s => //.
            unfold iris.of_val. destruct l1 => //.
              + rewrite merge_prepend in Hetov.
        destruct (merge_values $ map _ _) eqn:Hmerge => //.
        2: destruct e0 => //. 
        destruct v => //.
        simpl in Hetov.
        inversion Hetov ; subst.
        rewrite - app_comm_cons in Hfilled.
        fold (AI_const (VAL_ref (VAL_ref_exn e t))) in Hfilled.
        apply lfilled_vLI in Hfilled as [(lh' & Hlh & Hfilled) | (-> & -> & aft & -> & <-)].
        * rewrite app_comm_cons in Hfilled.
          assert (length_rec LI < m) ;
            first by specialize (length_cons_rec (AI_ref_exn e t) LI) ; lia.
          specialize (IHm _ H _ _ _ Hfilled l2).
          unfold to_val0 in IHm at 1.
          unfold iris.to_val0 in IHm.
          rewrite Hmerge in IHm.
          
          destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill).
          exists vs' ; split => //.
          subst ; by apply lfilled_prepend.
        * assert (lfilled 0 (LH_base [] aft) (es1 ++ es2) ((es1 ++ es2) ++ aft)).
          unfold lfilled, lfill => //=.
          assert (length_rec ((es1 ++ es2) ++ aft) < m).
          { specialize (length_cons_rec (AI_ref_exn e t)
                                        ((es1 ++ es2) ++ aft)) as H1.
            rewrite app_comm_cons in Hsize.
            repeat rewrite - cat_app in Hsize.
            rewrite app_comm_cons in H1.
            repeat rewrite - cat_app in H1.
            lia. }
          specialize (IHm _ H0 _ _ _ H l2).
          unfold to_val0 in IHm at 1.
          unfold iris.to_val0 in IHm.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill).
            remember (  match vs' with
                      | immV l' => (immV (VAL_ref (VAL_ref_exn e t) :: l'))
                      | trapV => trapV
                      | @brV i vh => (brV (vh_push_const vh [VAL_ref (VAL_ref_exn e t)]))
                      | retV lh => (retV (sh_push_const lh [VAL_ref (VAL_ref_exn e t)]))
                      | callHostV tf h vcs lh => (callHostV tf h vcs (llh_push_const lh [VAL_ref (VAL_ref_exn e t)]))
                      end ) as v'.
          exists v' ; split; subst => //=.
          -- unfold to_val, iris.to_val0 => /=.
            rewrite merge_prepend.
            unfold to_val, iris.to_val0 in Htv.
            destruct (merge_values (map _ es1)) eqn:Hmerge1 => //=.
            inversion Htv.
            destruct vs' => //.
            assert (to_val0 es1 = Some trapV) ;
              first by unfold to_val, iris.to_val0 ; rewrite Hmerge1 H2.
            apply to_val_trap_is_singleton in H1 as ->.
            simpl in Hmerge.
            rewrite merge_trap flatten_simplify in Hmerge.
            by destruct (es2 ++ aft).
          -- unfold lfilled, lfill => //=.
            unfold lfilled, lfill in Hfill ; simpl in Hfill.
            apply b2p in Hfill ; rewrite cat_app in Hfill. rewrite Hfill.
            destruct vs' => //.
            apply to_val_trap_is_singleton in Htv as ->.
            simpl in Hmerge.
            rewrite merge_trap flatten_simplify in Hmerge ; by destruct (es2 ++ aft).
            unfold iris.of_val. destruct lh => //.
            unfold iris.of_val. destruct s => //.
            unfold iris.of_val. destruct l1 => //.
              + rewrite merge_prepend in Hetov.
        destruct (merge_values $ map _ _) eqn:Hmerge => //.
        2: destruct e => //. 
        destruct v => //.
        simpl in Hetov.
        inversion Hetov ; subst.
        rewrite - app_comm_cons in Hfilled.
        fold (AI_const (VAL_ref (VAL_ref_cont f0))) in Hfilled.
        apply lfilled_vLI in Hfilled as [(lh' & Hlh & Hfilled) | (-> & -> & aft & -> & <-)].
        * rewrite app_comm_cons in Hfilled.
          assert (length_rec LI < m) ;
            first by specialize (length_cons_rec (AI_ref_cont f0) LI) ; lia.
          specialize (IHm _ H _ _ _ Hfilled l2).
          unfold to_val0 in IHm at 1.
          unfold iris.to_val0 in IHm.
          rewrite Hmerge in IHm.
          
          destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill).
          exists vs' ; split => //.
          subst ; by apply lfilled_prepend.
        * assert (lfilled 0 (LH_base [] aft) (es1 ++ es2) ((es1 ++ es2) ++ aft)).
          unfold lfilled, lfill => //=.
          assert (length_rec ((es1 ++ es2) ++ aft) < m).
          { specialize (length_cons_rec (AI_ref_cont f0)
                                        ((es1 ++ es2) ++ aft)) as H1.
            rewrite app_comm_cons in Hsize.
            repeat rewrite - cat_app in Hsize.
            rewrite app_comm_cons in H1.
            repeat rewrite - cat_app in H1.
            lia. }
          specialize (IHm _ H0 _ _ _ H l2).
          unfold to_val0 in IHm at 1.
          unfold iris.to_val0 in IHm.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as (vs' & Htv & Hfill).
            remember (  match vs' with
                      | immV l' => (immV (VAL_ref (VAL_ref_cont f0) :: l'))
                      | trapV => trapV
                      | @brV i vh => (brV (vh_push_const vh [VAL_ref (VAL_ref_cont f0)]))
                      | retV lh => (retV (sh_push_const lh [VAL_ref (VAL_ref_cont f0)]))
                      | callHostV tf h vcs lh => (callHostV tf h vcs (llh_push_const lh [VAL_ref (VAL_ref_cont f0)]))
                      end ) as v'.
          exists v' ; split; subst => //=.
          -- unfold to_val, iris.to_val0 => /=.
            rewrite merge_prepend.
            unfold to_val, iris.to_val0 in Htv.
            destruct (merge_values (map _ es1)) eqn:Hmerge1 => //=.
            inversion Htv.
            destruct vs' => //.
            assert (to_val0 es1 = Some trapV) ;
              first by unfold to_val, iris.to_val0 ; rewrite Hmerge1 H2.
            apply to_val_trap_is_singleton in H1 as ->.
            simpl in Hmerge.
            rewrite merge_trap flatten_simplify in Hmerge.
            by destruct (es2 ++ aft).
          -- unfold lfilled, lfill => //=.
            unfold lfilled, lfill in Hfill ; simpl in Hfill.
            apply b2p in Hfill ; rewrite cat_app in Hfill. rewrite Hfill.
            destruct vs' => //.
            apply to_val_trap_is_singleton in Htv as ->.
            simpl in Hmerge.
            rewrite merge_trap flatten_simplify in Hmerge ; by destruct (es2 ++ aft).
            unfold iris.of_val. destruct lh => //.
            unfold iris.of_val. destruct s => //.
            unfold iris.of_val. destruct l1 => //.
              + rewrite merge_throw in Hetov => //. 
              + rewrite merge_suspend in Hetov => //.
              + rewrite merge_switch in Hetov => //. 
      + destruct (merge_values $ map _ _) eqn:Hmerge => //.
        * destruct v => //.
          all: try by rewrite merge_notval in Hetov.
          -- rewrite merge_br flatten_simplify in Hetov => //.
          -- rewrite merge_return flatten_simplify in Hetov => //.
          -- rewrite merge_call_host flatten_simplify in Hetov.
             inversion Hetov ; subst.
             assert (length_rec l2 < m).
             { unfold length_rec in Hsize ; simpl in Hsize. unfold length_rec. lia. }
             unfold lfilled, lfill in Hfilled ; 
               destruct lh ; fold lfill in Hfilled => //.
             1-2: destruct i => //.
             all: destruct (const_list l0) eqn:Hl1 => //.
             2-4: destruct (lfill _ _ _) eqn:Hfill => //.
             all: move/eqP in Hfilled.
             all: destruct l0 ; inversion Hfilled ; subst ; 
               last by unfold const_list in Hl1; inversion Hl1.
             ++ eexists. split.
                ** unfold to_val, iris.to_val0 => /=.
                   rewrite Hmerge merge_call_host flatten_simplify => //.
                ** unfold lfilled, lfill => //=.
                   replace l2 with (llfill l4 [AI_call_host f h l]) ; first done.
                   assert (iris.to_val0 l2 = Some (callHostV f h l l4)) ;
                     first by unfold iris.to_val0 ; rewrite Hmerge.          
                   apply iris.of_to_val0 in H0 as <-.
                   unfold iris.of_val. done.
             ++ assert (lfilled i lh ((a :: es1) ++ es2) l6); 
                  first by unfold lfilled ; rewrite Hfill.
                specialize (IHm l6 H i lh (a :: es1) H0 ).
                unfold to_val0 in IHm at 1.
                unfold iris.to_val0 in IHm.
                rewrite Hmerge in IHm.
                destruct (IHm _ Logic.eq_refl) as (vs' & Htv & Hfill').
                eexists ; split => //.
                unfold lfilled, lfill ; fold lfill => //=.
                unfold lfilled in Hfill'. destruct (lfill _ _ (_ ++ _)) => //.
                apply b2p in Hfill' ; by subst.
        * destruct e => //.
          rewrite merge_suspend in Hetov => //.
          rewrite merge_switch in Hetov => //.
          destruct (exnelts_of_exception_clauses _ _) => //.
          rewrite merge_throw in Hetov => //.
          rewrite merge_notval in Hetov => //.
        * rewrite merge_notval in Hetov => //.
      + destruct (merge_values $ map _ _) eqn:Hmerge => //.
        * destruct v => //.
          all: try by rewrite merge_notval in Hetov.
          -- rewrite merge_br flatten_simplify in Hetov => //.
          -- rewrite merge_return flatten_simplify in Hetov => //.
          -- rewrite merge_call_host flatten_simplify in Hetov.
             inversion Hetov ; subst.
             assert (length_rec l3 < m).
             { unfold length_rec in Hsize ; simpl in Hsize. unfold length_rec. lia. }
             unfold lfilled, lfill in Hfilled ; 
               destruct lh ; fold lfill in Hfilled => //.
             1-2: destruct i => //.
             all: destruct (const_list l0) eqn:Hl1 => //.
             2-4: destruct (lfill _ _ _) eqn:Hfill => //.
             all: move/eqP in Hfilled.
             all: destruct l0 ; inversion Hfilled ; subst ; 
               last by unfold const_list in Hl1; inversion Hl1.
             ++ eexists. split.
                ** unfold to_val, iris.to_val0 => /=.
                   rewrite Hmerge merge_call_host flatten_simplify => //.
                ** unfold lfilled, lfill => //=.
                   replace l3 with (llfill l5 [AI_call_host f h l]) ; first done.
                   assert (iris.to_val0 l3 = Some (callHostV f h l l5)) ;
                     first by unfold iris.to_val0 ; rewrite Hmerge.          
                   apply iris.of_to_val0 in H0 as <-.
                   unfold iris.of_val. done.
             ++ assert (lfilled i lh ((a :: es1) ++ es2) l8); 
                  first by unfold lfilled ; rewrite Hfill.
                specialize (IHm l8 H i lh (a :: es1) H0 ).
                unfold to_val0 in IHm at 1.
                unfold iris.to_val0 in IHm.
                rewrite Hmerge in IHm.
                destruct (IHm _ Logic.eq_refl) as (vs' & Htv & Hfill').
                eexists ; split => //.
                unfold lfilled, lfill ; fold lfill => //=.
                unfold lfilled in Hfill'. destruct (lfill _ _ (_ ++ _)) => //.
                apply b2p in Hfill' ; by subst.
        * destruct e => //.
          destruct (suselts_of_continuation_clauses _ _) => //. 
          rewrite merge_suspend in Hetov => //.
          rewrite merge_notval in Hetov => //.
          destruct (swelts_of_continuation_clauses _ _) => //. 
          rewrite merge_switch in Hetov => //.
          rewrite merge_notval in Hetov => //.
          rewrite merge_throw in Hetov => //.
        * rewrite merge_notval in Hetov => //.
      + destruct (merge_values $ map _ _) eqn:Hmerge => //.
        * destruct v => //.
          all: try by rewrite merge_notval in Hetov.
          -- destruct i0; last destruct (vh_decrease _).
             all: try by rewrite merge_notval in Hetov.
             rewrite merge_br flatten_simplify in Hetov => //.
          -- rewrite merge_return flatten_simplify in Hetov => //.
          -- rewrite merge_call_host flatten_simplify in Hetov.
             inversion Hetov ; subst.
             assert (length_rec l2 < m).
             { unfold length_rec in Hsize ; simpl in Hsize. unfold length_rec. lia. }
             unfold lfilled, lfill in Hfilled ; 
               destruct lh ; fold lfill in Hfilled => //.
             1-2: destruct i => //.
             all: destruct (const_list l0) eqn:Hl1 => //.
             2-4: destruct (lfill _ _ _) eqn:Hfill => //.
             all: move/eqP in Hfilled.
             all: destruct l0 ; inversion Hfilled ; subst ; 
               last by unfold const_list in Hl1; inversion Hl1.
             ++ eexists. split.
                ** unfold to_val, iris.to_val0 => /=.
                   rewrite Hmerge merge_call_host flatten_simplify => //.
                ** unfold lfilled, lfill => //=.
                   replace l2 with (llfill l4 [AI_call_host f h l]) ; first done.
                   assert (iris.to_val0 l2 = Some (callHostV f h l l4)) ;
                     first by unfold iris.to_val0 ; rewrite Hmerge.          
                   apply iris.of_to_val0 in H0 as <-.
                   unfold iris.of_val. done.
             ++ assert (lfilled i lh ((a :: es1) ++ es2) l6); 
                  first by unfold lfilled ; rewrite Hfill.
                specialize (IHm l6 H i lh (a :: es1) H0 ).
                unfold to_val0 in IHm at 1.
                unfold iris.to_val0 in IHm.
                rewrite Hmerge in IHm.
                destruct (IHm _ Logic.eq_refl) as (vs' & Htv & Hfill').
                eexists ; split => //.
                unfold lfilled, lfill ; fold lfill => //=.
                unfold lfilled in Hfill'. destruct (lfill _ _ (_ ++ _)) => //.
                apply b2p in Hfill' ; by subst.
        * destruct e => //.
          rewrite merge_suspend in Hetov => //.
          rewrite merge_switch in Hetov => //.
          rewrite merge_throw in Hetov => //.
        * rewrite merge_notval in Hetov => //.
      + destruct (merge_values $ map _ _) eqn:Hmerge => //.
        * destruct v => //.
          all: try by rewrite merge_notval in Hetov.
          rewrite merge_call_host flatten_simplify in Hetov.
          inversion Hetov ; subst.
          assert (length_rec l1 < m).
          { unfold length_rec in Hsize ; simpl in Hsize. unfold length_rec. lia. }
             unfold lfilled, lfill in Hfilled ; 
               destruct lh ; fold lfill in Hfilled => //.
             1-2: destruct i => //.
             all: destruct (const_list l0) eqn:Hl1 => //.
             2-4: destruct (lfill _ _ _) eqn:Hfill => //.
             all: move/eqP in Hfilled.
             all: destruct l0 ; inversion Hfilled ; subst ; 
               last by unfold const_list in Hl1; inversion Hl1.
             eexists. split.
          -- unfold to_val, iris.to_val0 => /=.
                   rewrite Hmerge merge_call_host flatten_simplify => //.
          -- unfold lfilled, lfill => //=.
                   apply/eqP; repeat f_equal.
                   assert (iris.to_val0 l1 = Some (callHostV f h l l3)) ;
                     first by unfold iris.to_val0 ; rewrite Hmerge.          
                   apply iris.of_to_val0 in H0 as <-.
                   unfold iris.of_val. done.
        * destruct e => //.
          rewrite merge_suspend in Hetov => //.
          rewrite merge_switch in Hetov => //.
          rewrite merge_throw in Hetov => //.
        * rewrite merge_notval in Hetov => //.
      + rewrite merge_call_host flatten_simplify in Hetov. 
        inversion Hetov ; subst.
        eapply filled_is_val_call_host_base_app_cases in Hfilled as HH;[|eauto..].
        destruct HH as [-> [vs [es [-> HH]]]].
        destruct HH as [[es11 [es12 [Heq Hconst]]]
                       |[[es11 [es12 [Heq (Hconst & Hconst')]]]
                        |[es11 [es12 [Heq (Hconst&Hconst'&Hconst'')]]]]].
        { apply const_es_exists in Hconst as Hv.
          destruct Hv as [v Hv].
          exists (callHostV f h l ((LL_base v es12))).
          rewrite -to_val_call_host_eq Heq -Hv.
          split;auto. rewrite Hv in Heq. erewrite of_to_val0. 2: apply to_val_call_host_eq.
          rewrite -Heq. auto. }
        { apply const_list_to_val in Hconst' as Hv.
          destruct Hv as (v & Hv & _).
          exists (immV v). split;auto. erewrite of_to_val0;eauto. }
        { apply const_list_to_val in Hconst as Hv.
          destruct Hv as (v & Hv & _).
          exists (immV v). split;auto. erewrite of_to_val0;eauto. }
        unfold iris.to_val0 => /=.
        rewrite merge_call_host flatten_simplify => //=. 
  Qed.



  Lemma lfilled_to_eff_app_sus i lh es1 es2 LI vs k sh:
    lfilled i lh (es1 ++ es2)%list LI ->
    to_eff0 LI = Some (susE vs k sh) ->
    is_pure lh ->
    const_list es1 /\ const_list es2 \/ 
    (∃ esv shin shout,
        es1 = v_to_e_list esv /\
          to_eff0 es2 = Some (susE vs k shin) /\
          susholed_of_lholed lh = Some shout /\
          sus_trans shout (sus_trans (SuBase esv []) shin) = sh
    ) \/
       ∃ shin shout,
         to_eff0 es1 = Some (susE vs k shin) ∧
           susholed_of_lholed lh = Some shout /\
           sus_trans shout (sus_trans (SuBase [] es2) shin) = sh.
  Proof.
    intros Hfilled Heff Hpure.
    eapply lfilled_to_eff_sus in Hpure.
    2: exact Heff.
    2: exact Hfilled.
    destruct Hpure as [Hconst | (shin & shout & Hin & Hout & Htrans)].
    - apply const_list_split in Hconst as [??].
      by left.
    - unfold to_eff0 in Hin.
      rewrite map_app merge_app in Hin.
      unfold to_eff0.
      destruct (merge_values _) eqn:Hmerge => //.
      + destruct v => //.
        * right. left.
          destruct (merge_values (map _ es2)) eqn:Hes2 => //.
          destruct v => //.
          destruct l => //.
          destruct e => //.
          simpl in Hin.
          inversion Hin; subst.
          eexists l, _, shout.
          split. symmetry. fold (of_val0 (immV l)). apply of_to_val0.
          unfold iris.to_val0. rewrite Hmerge. done.
          split; first done.
          split; first done.
          simpl. rewrite sus_append_nil //.
        * simpl in Hin.
          rewrite merge_to_val in Hin.
          destruct es2 => //.
      + destruct e => //.
        simpl in Hin. inversion Hin; subst.
        right. right.
        do 2 eexists.
        split; first done.
        split; first done.
        rewrite merge_to_val.
        simpl.
        rewrite sus_push_const_nil. done.
  Qed.

    Lemma lfilled_to_eff_app_sw i lh es1 es2 LI vs k tf k' sh:
    lfilled i lh (es1 ++ es2)%list LI ->
    to_eff0 LI = Some (swE vs k tf k' sh) ->
    is_pure lh ->
    const_list es1 /\ const_list es2 \/ 
    (∃ esv shin shout,
        es1 = v_to_e_list esv /\
          to_eff0 es2 = Some (swE vs k tf k' shin) /\
          swholed_of_lholed lh = Some shout /\
          sw_trans shout (sw_trans (SwBase esv []) shin) = sh
    ) \/
       ∃ shin shout,
         to_eff0 es1 = Some (swE vs k tf k' shin) ∧
           swholed_of_lholed lh = Some shout /\
           sw_trans shout (sw_trans (SwBase [] es2) shin) = sh.
  Proof.
    intros Hfilled Heff Hpure.
    eapply lfilled_to_eff_sw in Hpure.
    2: exact Heff.
    2: exact Hfilled.
    destruct Hpure as [Hconst | (shin & shout & Hin & Hout & Htrans)].
    - apply const_list_split in Hconst as [??].
      by left.
    - unfold to_eff0 in Hin.
      rewrite map_app merge_app in Hin.
      unfold to_eff0.
      destruct (merge_values _) eqn:Hmerge => //.
      + destruct v => //.
        * right. left.
          destruct (merge_values (map _ es2)) eqn:Hes2 => //.
          destruct v => //.
          destruct l => //.
          destruct e => //.
          simpl in Hin.
          inversion Hin; subst.
          eexists l, _, shout.
          split. symmetry. fold (of_val0 (immV l)). apply of_to_val0.
          unfold iris.to_val0. rewrite Hmerge. done.
          split; first done.
          split; first done.
          simpl. rewrite sw_append_nil //.
        * simpl in Hin.
          rewrite merge_to_val in Hin.
          destruct es2 => //.
      + destruct e => //.
        simpl in Hin. inversion Hin; subst.
        right. right.
        do 2 eexists.
        split; first done.
        split; first done.
        rewrite merge_to_val.
        simpl.
        rewrite sw_push_const_nil. done.
  Qed.

    Lemma lfilled_to_eff_app_thr i lh es1 es2 LI vs k k' sh:
    lfilled i lh (es1 ++ es2)%list LI ->
    to_eff0 LI = Some (thrE vs k k' sh) ->
    is_pure lh ->
    const_list es1 /\ const_list es2 \/ 
    (∃ esv shin shout,
        es1 = v_to_e_list esv /\
          to_eff0 es2 = Some (thrE vs k k' shin) /\
          exnholed_of_lholed lh = Some shout /\
          exn_trans shout (exn_trans (ExBase esv []) shin) = sh
    ) \/
       ∃ shin shout,
         to_eff0 es1 = Some (thrE vs k k' shin) ∧
           exnholed_of_lholed lh = Some shout /\
           exn_trans shout (exn_trans (ExBase [] es2) shin) = sh.
  Proof.
    intros Hfilled Heff Hpure.
    eapply lfilled_to_eff_thr in Hpure.
    2: exact Heff.
    2: exact Hfilled.
    destruct Hpure as [Hconst | (shin & shout & Hin & Hout & Htrans)].
    - apply const_list_split in Hconst as [??].
      by left.
    - unfold to_eff0 in Hin.
      rewrite map_app merge_app in Hin.
      unfold to_eff0.
      destruct (merge_values _) eqn:Hmerge => //.
      + destruct v => //.
        * right. left.
          destruct (merge_values (map _ es2)) eqn:Hes2 => //.
          destruct v => //.
          destruct l => //.
          destruct e => //.
          simpl in Hin.
          inversion Hin; subst.
          eexists l, _, shout.
          split. symmetry. fold (of_val0 (immV l)). apply of_to_val0.
          unfold iris.to_val0. rewrite Hmerge. done.
          split; first done.
          split; first done.
          simpl. rewrite exn_append_nil //.
        * simpl in Hin.
          rewrite merge_to_val in Hin.
          destruct es2 => //.
      + destruct e => //.
        simpl in Hin. inversion Hin; subst.
        right. right.
        do 2 eexists.
        split; first done.
        split; first done.
        rewrite merge_to_val.
        simpl.
        rewrite exn_push_const_nil. done.
  Qed.

  Lemma to_eff_cat_None_inv es1 es2 :
    to_eff0 (es1 ++ es2) = None -> to_eff0 es1 = None.
  Proof.
    unfold to_eff0.
    rewrite map_app merge_app.
    destruct (merge_values _) eqn:Hmerge => //.
    destruct e => //.
  Qed.

  Lemma to_eff_cat_None2_inv es1 es2 :
    to_eff0 (es1 ++ es2) = None -> const_list es1 -> to_eff0 es2 = None.
  Proof.
    unfold to_eff0.
    rewrite map_app merge_app.
    intros H Hes.
    apply const_list_to_val in Hes as (vs & Htv & Hvs).
    unfold iris.to_val0 in Htv.
    destruct (merge_values _) => //.
    inversion Htv; subst.
    destruct (merge_values _) => //.
    destruct e => //.
  Qed. 

  
 Lemma lfilled_to_eff_app i lh es1 es2 LI vs :
    lfilled i lh (es1 ++ es2)%list LI ->
    to_eff0 LI = Some vs ->
    (const_list es1 \/ ∃ vs', to_eff0 es1 = Some vs' ∧ lfilled i lh ((iris.of_eff0 vs') ++ es2) LI).
  Proof.
    intros Hfilled Hetov.
    destruct vs.
    - remember (length_rec LI) as n.
      assert (length_rec LI < S n) ; first lia.
      remember (S n) as m.
      clear Heqn Heqm n.
      generalize dependent sh.
      generalize dependent i0. generalize dependent es1. generalize dependent lh.
      generalize dependent i. 
      generalize dependent LI.
      induction m ; intros LI Hsize ; intros ; first lia.
      destruct es1 ; first eauto.
      unfold to_eff0 in Hetov ; simpl in Hetov.
      destruct LI ; first by inversion Hetov.
      destruct a0 ; try destruct b ; simpl in Hetov  => //.
      all: try by rewrite merge_notval in Hetov.
      + rewrite merge_br in Hetov => //.
      + rewrite merge_return in Hetov => //.
      + rewrite merge_prepend in Hetov.
        destruct (merge_values $ map _ _) eqn:Hmerge => //.
        2: destruct e => //.  
        destruct v0 => //.
        simpl in Hetov.
        inversion Hetov; subst.
        rewrite - app_comm_cons in Hfilled.
        fold (AI_const (VAL_num v)) in Hfilled.
        apply lfilled_vLI in Hfilled as [(lh' & Hlh & Hfilled) | (-> & -> & aft & -> & <-)].
        * rewrite app_comm_cons in Hfilled.
          assert (length_rec LI < m) ;
            first by specialize (length_cons_rec (AI_basic $ BI_const v) LI) ; lia.
          specialize (IHm _ H _ _ _ Hfilled i0 sh0).
          unfold to_eff0 in IHm at 1.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as [Hconst | (vs' & Htv & Hfill)].
          -- by left.
          -- right. exists vs' ; split => //.
             subst ; by apply lfilled_prepend.
        * assert (lfilled 0 (LH_base [] aft) (es1 ++ es2) ((es1 ++ es2) ++ aft)).
          unfold lfilled, lfill => //=.
          assert (length_rec ((es1 ++ es2) ++ aft) < m).
          { specialize (length_cons_rec (AI_basic $ BI_const v)
                                        ((es1 ++ es2) ++ aft)) as H1.
            rewrite app_comm_cons in Hsize.
            repeat rewrite - cat_app in Hsize.
            rewrite app_comm_cons in H1.
            repeat rewrite - cat_app in H1.
            lia. }
          specialize (IHm _ H0 _ _ _ H i0 sh0).
          unfold to_eff0 in IHm at 1.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as [Hconst | (vs' & Htv & Hfill)]; first by left.
          remember (  match vs' with
                      | susE vs i sh => susE vs i (sus_push_const sh [VAL_num v])
                      | swE vs k tf i sh => swE vs k tf i (sw_push_const sh [VAL_num v])
                      | thrE vs k i sh => thrE vs k i (exn_push_const sh [VAL_num v])
                      end ) as v'.
          right. exists  v'; split => //=.
          -- unfold to_eff0 => /=.
             rewrite merge_prepend.
             unfold to_eff0 in Htv.
             destruct (merge_values (map _ es1)) eqn:Hmerge1 => //=.
             inversion Htv; subst e.
             destruct vs'; subst => //.
          -- unfold lfilled, lfill => //=.
             unfold lfilled, lfill in Hfill ; simpl in Hfill.
             apply b2p in Hfill ; rewrite cat_app in Hfill. rewrite Hfill.
             subst v'. destruct vs' => //=.
             rewrite susfill_sus_push_const /= //.
             rewrite swfill_sw_push_const //.
             rewrite exnfill_exn_push_const //.
      + rewrite merge_prepend in Hetov.
        destruct (merge_values $ map _ _) eqn:Hmerge => //.
        2: destruct e => //.  
        destruct v => //.
        simpl in Hetov.
        inversion Hetov; subst.
        rewrite - app_comm_cons in Hfilled.
        fold (AI_const (VAL_ref (VAL_ref_null r))) in Hfilled.
        apply lfilled_vLI in Hfilled as [(lh' & Hlh & Hfilled) | (-> & -> & aft & -> & <-)].
        * rewrite app_comm_cons in Hfilled.
          assert (length_rec LI < m) ;
            first by specialize (length_cons_rec (AI_basic $ BI_ref_null r) LI) ; lia.
          specialize (IHm _ H _ _ _ Hfilled i0 sh0).
          unfold to_eff0 in IHm at 1.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as [Hconst | (vs' & Htv & Hfill)]; first by left.
          right; exists vs' ; split => //.
          subst ; by apply lfilled_prepend.
        * assert (lfilled 0 (LH_base [] aft) (es1 ++ es2) ((es1 ++ es2) ++ aft)).
          unfold lfilled, lfill => //=.
          assert (length_rec ((es1 ++ es2) ++ aft) < m).
          { specialize (length_cons_rec (AI_basic $ BI_ref_null r)
                                        ((es1 ++ es2) ++ aft)) as H1.
            rewrite app_comm_cons in Hsize.
            repeat rewrite - cat_app in Hsize.
            rewrite app_comm_cons in H1.
            repeat rewrite - cat_app in H1.
            lia. }
          specialize (IHm _ H0 _ _ _ H i0 sh0).
          unfold to_eff0 in IHm at 1.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as [Hconst | (vs' & Htv & Hfill)]; first by left.
          remember (  match vs' with
                      | susE vs i sh => susE vs i (sus_push_const sh [VAL_ref $ VAL_ref_null r])
                      | swE vs k tf i sh => swE vs k tf i (sw_push_const sh [VAL_ref $ VAL_ref_null r])
                      | thrE vs k i sh => thrE vs k i (exn_push_const sh [VAL_ref $ VAL_ref_null r])
                          end ) as v'.
          right; exists  v'; split => //=.
          -- unfold to_eff0 => /=.
             rewrite merge_prepend.
             unfold to_eff0 in Htv.
             destruct (merge_values (map _ es1)) eqn:Hmerge1 => //=.
             inversion Htv; subst e.
             destruct vs'; subst => //.
          -- unfold lfilled, lfill => //=.
             unfold lfilled, lfill in Hfill ; simpl in Hfill.
             apply b2p in Hfill ; rewrite cat_app in Hfill. rewrite Hfill.
             subst v'. destruct vs' => //=.
             rewrite susfill_sus_push_const //.
             rewrite swfill_sw_push_const //.
             rewrite exnfill_exn_push_const //. 
           
      + rewrite merge_trap flatten_simplify in Hetov.
        by destruct LI.
      + rewrite merge_prepend in Hetov.
        destruct (merge_values $ map _ _) eqn:Hmerge => //.
        2: destruct e => //.  
        destruct v => //.
        simpl in Hetov.
        inversion Hetov; subst.
        rewrite - app_comm_cons in Hfilled.
        fold (AI_const (VAL_ref (VAL_ref_func f))) in Hfilled.
        apply lfilled_vLI in Hfilled as [(lh' & Hlh & Hfilled) | (-> & -> & aft & -> & <-)].
        * rewrite app_comm_cons in Hfilled.
          assert (length_rec LI < m) ;
            first by specialize (length_cons_rec (AI_ref f) LI) ; lia.
          specialize (IHm _ H _ _ _ Hfilled i0 sh0).
          unfold to_eff0 in IHm at 1.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as [? | (vs' & Htv & Hfill)]; first by left.
          right; exists vs' ; split => //.
          subst ; by apply lfilled_prepend.
        * assert (lfilled 0 (LH_base [] aft) (es1 ++ es2) ((es1 ++ es2) ++ aft)).
          unfold lfilled, lfill => //=.
          assert (length_rec ((es1 ++ es2) ++ aft) < m).
          { specialize (length_cons_rec (AI_ref f)
                                        ((es1 ++ es2) ++ aft)) as H1.
            rewrite app_comm_cons in Hsize.
            repeat rewrite - cat_app in Hsize.
            rewrite app_comm_cons in H1.
            repeat rewrite - cat_app in H1.
            lia. }
          specialize (IHm _ H0 _ _ _ H i0 sh0).
          unfold to_eff0 in IHm at 1.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as [? | (vs' & Htv & Hfill)]; first by left.
          remember (  match vs' with
                          | susE vs i sh => susE vs i (sus_push_const sh [VAL_ref $ VAL_ref_func f])
                      | swE vs k tf i sh => swE vs k tf i (sw_push_const sh [VAL_ref $ VAL_ref_func f])
                      | thrE vs k i sh => thrE vs k i (exn_push_const sh [VAL_ref $ VAL_ref_func f])
                                     end ) as v'.
          right; exists  v'; split => //=.
          -- unfold to_eff0 => /=.
             rewrite merge_prepend.
             unfold to_eff0 in Htv.
             destruct (merge_values (map _ es1)) eqn:Hmerge1 => //=.
             inversion Htv; subst e.
             destruct vs'; subst => //.
          -- unfold lfilled, lfill => //=.
             unfold lfilled, lfill in Hfill ; simpl in Hfill.
             apply b2p in Hfill ; rewrite cat_app in Hfill. rewrite Hfill.
             subst v'. destruct vs' => //=.
             rewrite susfill_sus_push_const //.
             rewrite swfill_sw_push_const //.
             rewrite exnfill_exn_push_const //.
      + rewrite merge_prepend in Hetov.
        destruct (merge_values $ map _ _) eqn:Hmerge => //.
        2: destruct e0 => //.  
        destruct v => //.
        simpl in Hetov.
        inversion Hetov; subst.
        rewrite - app_comm_cons in Hfilled.
        fold (AI_const (VAL_ref (VAL_ref_exn e t))) in Hfilled.
        apply lfilled_vLI in Hfilled as [(lh' & Hlh & Hfilled) | (-> & -> & aft & -> & <-)].
        * rewrite app_comm_cons in Hfilled.
          assert (length_rec LI < m) ;
            first by specialize (length_cons_rec (AI_ref_exn e t) LI) ; lia.
          specialize (IHm _ H _ _ _ Hfilled i0 sh0).
          unfold to_eff0 in IHm at 1.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as [? | (vs' & Htv & Hfill)]; first by left.
          right; exists vs' ; split => //.
          subst ; by apply lfilled_prepend.
        * assert (lfilled 0 (LH_base [] aft) (es1 ++ es2) ((es1 ++ es2) ++ aft)).
          unfold lfilled, lfill => //=.
          assert (length_rec ((es1 ++ es2) ++ aft) < m).
          { specialize (length_cons_rec (AI_ref_exn e t)
                                        ((es1 ++ es2) ++ aft)) as H1.
            rewrite app_comm_cons in Hsize.
            repeat rewrite - cat_app in Hsize.
            rewrite app_comm_cons in H1.
            repeat rewrite - cat_app in H1.
            lia. }
          specialize (IHm _ H0 _ _ _ H i0 sh0).
          unfold to_eff0 in IHm at 1.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as [?|(vs' & Htv & Hfill)]; first by left.
          remember (  match vs' with
                              | susE vs i sh => susE vs i (sus_push_const sh [VAL_ref $ VAL_ref_exn e t])
                      | swE vs k tf i sh => swE vs k tf i (sw_push_const sh [VAL_ref $ VAL_ref_exn e t])
                      | thrE vs k i sh => thrE vs k i (exn_push_const sh [VAL_ref $ VAL_ref_exn e t])
                      end ) as v'.
          right; exists  v'; split => //=.
          -- unfold to_eff0 => /=.
             rewrite merge_prepend.
             unfold to_eff0 in Htv.
             destruct (merge_values (map _ es1)) eqn:Hmerge1 => //=.
             inversion Htv; subst e0.
             destruct vs'; subst => //.
          -- unfold lfilled, lfill => //=.
             unfold lfilled, lfill in Hfill ; simpl in Hfill.
             apply b2p in Hfill ; rewrite cat_app in Hfill. rewrite Hfill.
             subst v'. destruct vs' => //=.
             rewrite susfill_sus_push_const //.
             rewrite swfill_sw_push_const //.
             rewrite exnfill_exn_push_const //.
      + rewrite merge_prepend in Hetov.
        destruct (merge_values $ map _ _) eqn:Hmerge => //.
        2: destruct e => //.  
        destruct v => //.
        simpl in Hetov.
        inversion Hetov; subst.
        rewrite - app_comm_cons in Hfilled.
        fold (AI_const (VAL_ref (VAL_ref_cont f))) in Hfilled.
        apply lfilled_vLI in Hfilled as [(lh' & Hlh & Hfilled) | (-> & -> & aft & -> & <-)].
        * rewrite app_comm_cons in Hfilled.
          assert (length_rec LI < m) ;
            first by specialize (length_cons_rec (AI_ref_cont f) LI) ; lia.
          specialize (IHm _ H _ _ _ Hfilled i0 sh0).
          unfold to_eff0 in IHm at 1.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as [?|(vs' & Htv & Hfill)]; first by left.
          right; exists vs' ; split => //.
          subst ; by apply lfilled_prepend.
        * assert (lfilled 0 (LH_base [] aft) (es1 ++ es2) ((es1 ++ es2) ++ aft)).
          unfold lfilled, lfill => //=.
          assert (length_rec ((es1 ++ es2) ++ aft) < m).
          { specialize (length_cons_rec (AI_ref_cont f)
                                        ((es1 ++ es2) ++ aft)) as H1.
            rewrite app_comm_cons in Hsize.
            repeat rewrite - cat_app in Hsize.
            rewrite app_comm_cons in H1.
            repeat rewrite - cat_app in H1.
            lia. }
          specialize (IHm _ H0 _ _ _ H i0 sh0).
          unfold to_eff0 in IHm at 1.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as [?|(vs' & Htv & Hfill)]; first by left.
          remember (  match vs' with
                      | susE vs i sh => susE vs i (sus_push_const sh [VAL_ref $ VAL_ref_cont f])
                      | swE vs k tf i sh => swE vs k tf i (sw_push_const sh [VAL_ref $ VAL_ref_cont f])
                      | thrE vs k i sh => thrE vs k i (exn_push_const sh [VAL_ref $ VAL_ref_cont f])
                      end ) as v'.
          right; exists  v'; split => //=.
          -- unfold to_eff0 => /=.
             rewrite merge_prepend.
             unfold to_eff0 in Htv.
             destruct (merge_values (map _ es1)) eqn:Hmerge1 => //=.
             inversion Htv; subst e.
             destruct vs'; subst => //.
          -- unfold lfilled, lfill => //=.
             unfold lfilled, lfill in Hfill ; simpl in Hfill.
             apply b2p in Hfill ; rewrite cat_app in Hfill. rewrite Hfill.
             subst v'. destruct vs' => //=.
             rewrite susfill_sus_push_const //.
             rewrite swfill_sw_push_const //.
             rewrite exnfill_exn_push_const //.
      + rewrite merge_throw in Hetov => //.
      + rewrite merge_suspend in Hetov => //.
        inversion Hetov; subst.
        eapply filled_is_eff_sus_base_app_cases in Hfilled as HH;[|eauto..].
        2:{ unfold to_eff0. simpl. rewrite merge_suspend. done. } 
        destruct HH as [-> [vs' [es [-> HH]]]].
        destruct HH as [[es11 [es12 [Heq Hconst]]]
                       |[[es11 [es12 [Heq (Hconst & Hconst')]]]
                        |[es11 [es12 [Heq (Hconst&Hconst'&Hconst'')]]]]].
        all: try by left.
        apply const_es_exists in Hconst as Hv.
        destruct Hv as [v Hv].
        right; exists (susE vs i0 (SuBase v es12)).
        rewrite -to_eff_sus_eq Heq -Hv.
        split;auto. rewrite Hv in Heq. erewrite of_to_eff0.
        2: apply to_eff_sus_eq.
        rewrite -Heq. auto. 
      + rewrite merge_switch in Hetov => //. 
      + destruct (merge_values $ map _ _) eqn:Hmerge => //.
        * destruct v => // ;
                       (try by rewrite merge_br in Hetov);
                     (try by rewrite merge_notval in Hetov);
                     (try by rewrite merge_return in Hetov) ;
                     try by rewrite merge_call_host in Hetov.
        * destruct e => //.
          -- rewrite merge_suspend flatten_simplify in Hetov.
             inversion Hetov.
             subst.
             assert (length_rec l0 < m).
             { unfold length_rec in Hsize ; simpl in Hsize. unfold length_rec. lia. }
             unfold lfilled, lfill in Hfilled ; 
               destruct lh ; fold lfill in Hfilled => //.
             1-2: destruct i => //.
             all: destruct (const_list l1) eqn:Hl1 => //.
             2-4: destruct (lfill _ _ _) eqn:Hfill => //.
             all: move/eqP in Hfilled.
             all: destruct l1 ; inversion Hfilled ; subst ; 
               last by unfold const_list in Hl1; inversion Hl1.
             ++ right. eexists. split.
                ** unfold to_eff0 => /=.
                   rewrite Hmerge merge_suspend flatten_simplify => //.
                ** unfold lfilled, lfill => //=.
                   apply/eqP. repeat f_equal.
                   assert (iris.to_eff0 l0 = Some (susE vs i0 sh0)) ;
                     first by unfold iris.to_eff0 ; rewrite Hmerge.          
                   apply iris.of_to_eff0 in H0 as <-.
                   unfold iris.of_eff0. 
                   done.
             ++ assert (lfilled i lh ((a :: es1) ++ es2) l4); 
                  first by unfold lfilled ; rewrite Hfill.
                specialize (IHm l4 H i lh (a :: es1) H0 i0 sh0).
                unfold to_eff0 in IHm at 1.
                rewrite Hmerge in IHm.
                destruct (IHm Logic.eq_refl) as [? | (vs' & Htv & Hfill')]; first by left.
                right; eexists ; split => //.
                unfold lfilled, lfill ; fold lfill => //=.
                unfold lfilled in Hfill'.
                destruct (lfill _ _ (_ ++ _)) => //.
                apply b2p in Hfill' ; by subst.
          -- rewrite merge_switch in Hetov => //.
          -- destruct (exnelts_of_exception_clauses _ _) => //.
             rewrite merge_throw in Hetov => //.
             rewrite merge_notval in Hetov => //.
        * rewrite merge_notval in Hetov => //.
      + destruct (merge_values $ map _ _) eqn:Hmerge => //.
        * destruct v => // ;
                       (try by rewrite merge_br in Hetov);
                     (try by rewrite merge_notval in Hetov);
                     (try by rewrite merge_return in Hetov) ;
                     try by rewrite merge_call_host in Hetov.
        * destruct e => //.
          -- destruct (suselts_of_continuation_clauses _ _) eqn:Helts=> //.
             2: by rewrite merge_notval in Hetov.
             rewrite merge_suspend flatten_simplify in Hetov.
             inversion Hetov.
             subst.
             assert (length_rec l1 < m).
             { unfold length_rec in Hsize ; simpl in Hsize. unfold length_rec. lia. }
             unfold lfilled, lfill in Hfilled ; 
               destruct lh ; fold lfill in Hfilled => //.
             1-2: destruct i => //.
             all: destruct (const_list l3) eqn:Hl1 => //.
             2-4: destruct (lfill _ _ _) eqn:Hfill => //.
             all: move/eqP in Hfilled.
             all: destruct l3 ; inversion Hfilled ; subst ; 
               last by unfold const_list in Hl1; inversion Hl1.
             ++ right; eexists. split.
                ** unfold to_eff0 => /=.
                   rewrite Hmerge Helts merge_suspend flatten_simplify => //.
                ** unfold lfilled, lfill => //=.
                   apply/eqP. repeat f_equal.
                   by erewrite suselts_of_continuation_clauses_inj.
                   assert (iris.to_eff0 l1 = Some (susE vs i0 sh0)) ;
                     first by unfold iris.to_eff0 ; rewrite Hmerge.          
                   apply iris.of_to_eff0 in H0 as <-.
                   unfold iris.of_eff0. 
                   done.
             ++ assert (lfilled i lh ((a :: es1) ++ es2) l7); 
                  first by unfold lfilled ; rewrite Hfill.
                specialize (IHm l7 H i lh (a :: es1) H0 i0 sh0).
                unfold to_eff0 in IHm at 1.
                rewrite Hmerge in IHm.
                destruct (IHm Logic.eq_refl) as [? | (vs' & Htv & Hfill')]; first by left.
                right; eexists ; split => //.
                unfold lfilled, lfill ; fold lfill => //=.
                unfold lfilled in Hfill'. destruct (lfill _ _ (_ ++ _)) => //.
                apply b2p in Hfill' ; by subst.
          -- destruct (swelts_of_continuation_clauses _ _) => //. 
             rewrite merge_switch in Hetov => //.
             rewrite merge_notval in Hetov => //. 
          -- rewrite merge_throw in Hetov => //.
        * rewrite merge_notval in Hetov => //.
      + destruct (merge_values $ map _ _) eqn:Hmerge => //.
        * destruct v => // ;
                       (try by rewrite merge_br in Hetov);
                     (try by rewrite merge_notval in Hetov);
                     (try by rewrite merge_return in Hetov) ;
                       try by rewrite merge_call_host in Hetov.
          destruct i1; last destruct (vh_decrease _) eqn:Hdecr.
          all: try by rewrite merge_notval in Hetov.
          rewrite merge_br in Hetov => //.
        * destruct e => //.
          -- rewrite merge_suspend flatten_simplify in Hetov.
             inversion Hetov. subst.
             assert (length_rec l0 < m).
             { unfold length_rec in Hsize ; simpl in Hsize. unfold length_rec. lia. }
             
          unfold lfilled, lfill in Hfilled ; 
            destruct lh ; fold lfill in Hfilled => //.
          1-2: destruct i => //.
          all: destruct (const_list l1) eqn:Hl1 => //.
          2-4: destruct (lfill _ _ _) eqn:Hfill => //.
          all: move/eqP in Hfilled.
          all: destruct l1 ; inversion Hfilled ; subst ; 
               last by unfold const_list in Hl1; inversion Hl1.
          ++ right. eexists. split.
             ** unfold to_eff0 => /=.
                rewrite Hmerge merge_suspend flatten_simplify => //.
             ** unfold lfilled, lfill => //=.
                apply/eqP. repeat f_equal.
                assert (iris.to_eff0 l0 = Some (susE vs i0 sh0)) ;
                  first by unfold iris.to_eff0 ; rewrite Hmerge.          
                apply iris.of_to_eff0 in H0 as <-.
                unfold iris.of_eff0. done. 
          ++ assert (lfilled i lh ((a :: es1) ++ es2) l4); 
               first by unfold lfilled ; rewrite Hfill.
             specialize (IHm l4 H i lh (a :: es1) H0 i0 sh0).
             unfold to_eff0 in IHm at 1.
             rewrite Hmerge in IHm.
             destruct (IHm Logic.eq_refl) as [? | (vs' & Htv & Hfill')]; first by left.
             right; eexists ; split => //.
             unfold lfilled, lfill ; fold lfill => //=.
             unfold lfilled in Hfill'. destruct (lfill _ _ (_ ++ _)) => //.
             apply b2p in Hfill' ; by subst.
          -- rewrite merge_switch in Hetov => //.
          -- rewrite merge_throw in Hetov => //.
        * rewrite merge_notval in Hetov => //.
      + destruct (merge_values $ map _ _) eqn:Hmerge => //.
        * destruct v => //.
          all: try by rewrite merge_notval in Hetov.
          rewrite merge_call_host in Hetov => //.
        * destruct e => //.
          -- rewrite merge_suspend flatten_simplify in Hetov => //.
             inversion Hetov. subst.
             assert (length_rec l < m).
             { unfold length_rec in Hsize ; simpl in Hsize. unfold length_rec. lia. }
             
          unfold lfilled, lfill in Hfilled ; 
            destruct lh ; fold lfill in Hfilled => //.
          1-2: destruct i => //.
          all: destruct (const_list l0) eqn:Hl1 => //.
          2-4: destruct (lfill _ _ _) eqn:Hfill => //.
          all: move/eqP in Hfilled.
          all: destruct l0 ; inversion Hfilled ; subst ; 
               last by unfold const_list in Hl1; inversion Hl1.
          right. eexists. split.
             ++ unfold to_eff0 => /=.
                rewrite Hmerge merge_suspend flatten_simplify => //.
             ++ unfold lfilled, lfill => //=.
                apply/eqP. repeat f_equal.
                assert (iris.to_eff0 l = Some (susE vs i0 sh0)) ;
                  first by unfold iris.to_eff0 ; rewrite Hmerge.          
                apply iris.of_to_eff0 in H0 as <-.
                unfold iris.of_eff0. done. 
         -- rewrite merge_switch in Hetov => //.
          -- rewrite merge_throw in Hetov => //.
        * rewrite merge_notval in Hetov => //.
      + rewrite merge_call_host // in Hetov.
    - remember (length_rec LI) as n.
      assert (length_rec LI < S n) ; first lia.
      remember (S n) as m.
      clear Heqn Heqm n.
      generalize dependent sh.
      generalize dependent i0. generalize dependent es1. generalize dependent lh.
      generalize dependent i. 
      generalize dependent LI.
      induction m ; intros LI Hsize ; intros ; first lia.
      destruct es1 ; first eauto.
      unfold to_eff0 in Hetov ; simpl in Hetov.
      destruct LI ; first by inversion Hetov.
      destruct a0 ; try destruct b ; simpl in Hetov  => //.
      all: try by rewrite merge_notval in Hetov.
      + rewrite merge_br in Hetov => //.
      + rewrite merge_return in Hetov => //.
      + rewrite merge_prepend in Hetov.
        destruct (merge_values $ map _ _) eqn:Hmerge => //.
        2: destruct e => //.  
        destruct v0 => //.
        simpl in Hetov.
        inversion Hetov; subst.
        rewrite - app_comm_cons in Hfilled.
        fold (AI_const (VAL_num v)) in Hfilled.
        apply lfilled_vLI in Hfilled as [(lh' & Hlh & Hfilled) | (-> & -> & aft & -> & <-)].
        * rewrite app_comm_cons in Hfilled.
          assert (length_rec LI < m) ;
            first by specialize (length_cons_rec (AI_basic $ BI_const v) LI) ; lia.
          specialize (IHm _ H _ _ _ Hfilled i0 sh0).
          unfold to_eff0 in IHm at 1.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as [Hconst | (vs' & Htv & Hfill)].
          -- by left.
          -- right. exists vs' ; split => //.
             subst ; by apply lfilled_prepend.
        * assert (lfilled 0 (LH_base [] aft) (es1 ++ es2) ((es1 ++ es2) ++ aft)).
          unfold lfilled, lfill => //=.
          assert (length_rec ((es1 ++ es2) ++ aft) < m).
          { specialize (length_cons_rec (AI_basic $ BI_const v)
                                        ((es1 ++ es2) ++ aft)) as H1.
            rewrite app_comm_cons in Hsize.
            repeat rewrite - cat_app in Hsize.
            rewrite app_comm_cons in H1.
            repeat rewrite - cat_app in H1.
            lia. }
          specialize (IHm _ H0 _ _ _ H i0 sh0).
          unfold to_eff0 in IHm at 1.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as [Hconst | (vs' & Htv & Hfill)]; first by left.
          remember (  match vs' with
                      | susE vs i sh => susE vs i (sus_push_const sh [VAL_num v])
                      | swE vs k tf i sh => swE vs k tf i (sw_push_const sh [VAL_num v])
                      | thrE vs k i sh => thrE vs k i (exn_push_const sh [VAL_num v])
                      end ) as v'.
          right. exists  v'; split => //=.
          -- unfold to_eff0 => /=.
             rewrite merge_prepend.
             unfold to_eff0 in Htv.
             destruct (merge_values (map _ es1)) eqn:Hmerge1 => //=.
             inversion Htv; subst e.
             destruct vs'; subst => //.
          -- unfold lfilled, lfill => //=.
             unfold lfilled, lfill in Hfill ; simpl in Hfill.
             apply b2p in Hfill ; rewrite cat_app in Hfill. rewrite Hfill.
             subst v'. destruct vs' => //=.
             rewrite susfill_sus_push_const /= //.
             rewrite swfill_sw_push_const //.
             rewrite exnfill_exn_push_const //.
      + rewrite merge_prepend in Hetov.
        destruct (merge_values $ map _ _) eqn:Hmerge => //.
        2: destruct e => //.  
        destruct v => //.
        simpl in Hetov.
        inversion Hetov; subst.
        rewrite - app_comm_cons in Hfilled.
        fold (AI_const (VAL_ref (VAL_ref_null r))) in Hfilled.
        apply lfilled_vLI in Hfilled as [(lh' & Hlh & Hfilled) | (-> & -> & aft & -> & <-)].
        * rewrite app_comm_cons in Hfilled.
          assert (length_rec LI < m) ;
            first by specialize (length_cons_rec (AI_basic $ BI_ref_null r) LI) ; lia.
          specialize (IHm _ H _ _ _ Hfilled i0 sh0).
          unfold to_eff0 in IHm at 1.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as [Hconst | (vs' & Htv & Hfill)]; first by left.
          right; exists vs' ; split => //.
          subst ; by apply lfilled_prepend.
        * assert (lfilled 0 (LH_base [] aft) (es1 ++ es2) ((es1 ++ es2) ++ aft)).
          unfold lfilled, lfill => //=.
          assert (length_rec ((es1 ++ es2) ++ aft) < m).
          { specialize (length_cons_rec (AI_basic $ BI_ref_null r)
                                        ((es1 ++ es2) ++ aft)) as H1.
            rewrite app_comm_cons in Hsize.
            repeat rewrite - cat_app in Hsize.
            rewrite app_comm_cons in H1.
            repeat rewrite - cat_app in H1.
            lia. }
          specialize (IHm _ H0 _ _ _ H i0 sh0).
          unfold to_eff0 in IHm at 1.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as [Hconst | (vs' & Htv & Hfill)]; first by left.
          remember (  match vs' with
                      | susE vs i sh => susE vs i (sus_push_const sh [VAL_ref $ VAL_ref_null r])
                      | swE vs k tf i sh => swE vs k tf i (sw_push_const sh [VAL_ref $ VAL_ref_null r])
                      | thrE vs k i sh => thrE vs k i (exn_push_const sh [VAL_ref $ VAL_ref_null r])
                          end ) as v'.
          right; exists  v'; split => //=.
          -- unfold to_eff0 => /=.
             rewrite merge_prepend.
             unfold to_eff0 in Htv.
             destruct (merge_values (map _ es1)) eqn:Hmerge1 => //=.
             inversion Htv; subst e.
             destruct vs'; subst => //.
          -- unfold lfilled, lfill => //=.
             unfold lfilled, lfill in Hfill ; simpl in Hfill.
             apply b2p in Hfill ; rewrite cat_app in Hfill. rewrite Hfill.
             subst v'. destruct vs' => //=.
             rewrite susfill_sus_push_const //.
             rewrite swfill_sw_push_const //.
             rewrite exnfill_exn_push_const //. 
           
      + rewrite merge_trap flatten_simplify in Hetov.
        by destruct LI.
      + rewrite merge_prepend in Hetov.
        destruct (merge_values $ map _ _) eqn:Hmerge => //.
        2: destruct e => //.  
        destruct v => //.
        simpl in Hetov.
        inversion Hetov; subst.
        rewrite - app_comm_cons in Hfilled.
        fold (AI_const (VAL_ref (VAL_ref_func f))) in Hfilled.
        apply lfilled_vLI in Hfilled as [(lh' & Hlh & Hfilled) | (-> & -> & aft & -> & <-)].
        * rewrite app_comm_cons in Hfilled.
          assert (length_rec LI < m) ;
            first by specialize (length_cons_rec (AI_ref f) LI) ; lia.
          specialize (IHm _ H _ _ _ Hfilled i0 sh0).
          unfold to_eff0 in IHm at 1.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as [? | (vs' & Htv & Hfill)]; first by left.
          right; exists vs' ; split => //.
          subst ; by apply lfilled_prepend.
        * assert (lfilled 0 (LH_base [] aft) (es1 ++ es2) ((es1 ++ es2) ++ aft)).
          unfold lfilled, lfill => //=.
          assert (length_rec ((es1 ++ es2) ++ aft) < m).
          { specialize (length_cons_rec (AI_ref f)
                                        ((es1 ++ es2) ++ aft)) as H1.
            rewrite app_comm_cons in Hsize.
            repeat rewrite - cat_app in Hsize.
            rewrite app_comm_cons in H1.
            repeat rewrite - cat_app in H1.
            lia. }
          specialize (IHm _ H0 _ _ _ H i0 sh0).
          unfold to_eff0 in IHm at 1.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as [? | (vs' & Htv & Hfill)]; first by left.
          remember (  match vs' with
                          | susE vs i sh => susE vs i (sus_push_const sh [VAL_ref $ VAL_ref_func f])
                      | swE vs k tf i sh => swE vs k tf i (sw_push_const sh [VAL_ref $ VAL_ref_func f])
                      | thrE vs k i sh => thrE vs k i (exn_push_const sh [VAL_ref $ VAL_ref_func f])
                                     end ) as v'.
          right; exists  v'; split => //=.
          -- unfold to_eff0 => /=.
             rewrite merge_prepend.
             unfold to_eff0 in Htv.
             destruct (merge_values (map _ es1)) eqn:Hmerge1 => //=.
             inversion Htv; subst e.
             destruct vs'; subst => //.
          -- unfold lfilled, lfill => //=.
             unfold lfilled, lfill in Hfill ; simpl in Hfill.
             apply b2p in Hfill ; rewrite cat_app in Hfill. rewrite Hfill.
             subst v'. destruct vs' => //=.
             rewrite susfill_sus_push_const //.
             rewrite swfill_sw_push_const //.
             rewrite exnfill_exn_push_const //.
      + rewrite merge_prepend in Hetov.
        destruct (merge_values $ map _ _) eqn:Hmerge => //.
        2: destruct e0 => //.  
        destruct v => //.
        simpl in Hetov.
        inversion Hetov; subst.
        rewrite - app_comm_cons in Hfilled.
        fold (AI_const (VAL_ref (VAL_ref_exn e t))) in Hfilled.
        apply lfilled_vLI in Hfilled as [(lh' & Hlh & Hfilled) | (-> & -> & aft & -> & <-)].
        * rewrite app_comm_cons in Hfilled.
          assert (length_rec LI < m) ;
            first by specialize (length_cons_rec (AI_ref_exn e t) LI) ; lia.
          specialize (IHm _ H _ _ _ Hfilled i0 sh0).
          unfold to_eff0 in IHm at 1.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as [? | (vs' & Htv & Hfill)]; first by left.
          right; exists vs' ; split => //.
          subst ; by apply lfilled_prepend.
        * assert (lfilled 0 (LH_base [] aft) (es1 ++ es2) ((es1 ++ es2) ++ aft)).
          unfold lfilled, lfill => //=.
          assert (length_rec ((es1 ++ es2) ++ aft) < m).
          { specialize (length_cons_rec (AI_ref_exn e t)
                                        ((es1 ++ es2) ++ aft)) as H1.
            rewrite app_comm_cons in Hsize.
            repeat rewrite - cat_app in Hsize.
            rewrite app_comm_cons in H1.
            repeat rewrite - cat_app in H1.
            lia. }
          specialize (IHm _ H0 _ _ _ H i0 sh0).
          unfold to_eff0 in IHm at 1.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as [?|(vs' & Htv & Hfill)]; first by left.
          remember (  match vs' with
                              | susE vs i sh => susE vs i (sus_push_const sh [VAL_ref $ VAL_ref_exn e t])
                      | swE vs k tf i sh => swE vs k tf i (sw_push_const sh [VAL_ref $ VAL_ref_exn e t])
                      | thrE vs k i sh => thrE vs k i (exn_push_const sh [VAL_ref $ VAL_ref_exn e t])
                      end ) as v'.
          right; exists  v'; split => //=.
          -- unfold to_eff0 => /=.
             rewrite merge_prepend.
             unfold to_eff0 in Htv.
             destruct (merge_values (map _ es1)) eqn:Hmerge1 => //=.
             inversion Htv; subst e0.
             destruct vs'; subst => //.
          -- unfold lfilled, lfill => //=.
             unfold lfilled, lfill in Hfill ; simpl in Hfill.
             apply b2p in Hfill ; rewrite cat_app in Hfill. rewrite Hfill.
             subst v'. destruct vs' => //=.
             rewrite susfill_sus_push_const //.
             rewrite swfill_sw_push_const //.
             rewrite exnfill_exn_push_const //.
      + rewrite merge_prepend in Hetov.
        destruct (merge_values $ map _ _) eqn:Hmerge => //.
        2: destruct e => //.  
        destruct v => //.
        simpl in Hetov.
        inversion Hetov; subst.
        rewrite - app_comm_cons in Hfilled.
        fold (AI_const (VAL_ref (VAL_ref_cont f))) in Hfilled.
        apply lfilled_vLI in Hfilled as [(lh' & Hlh & Hfilled) | (-> & -> & aft & -> & <-)].
        * rewrite app_comm_cons in Hfilled.
          assert (length_rec LI < m) ;
            first by specialize (length_cons_rec (AI_ref_cont f) LI) ; lia.
          specialize (IHm _ H _ _ _ Hfilled i0 sh0).
          unfold to_eff0 in IHm at 1.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as [?|(vs' & Htv & Hfill)]; first by left.
          right; exists vs' ; split => //.
          subst ; by apply lfilled_prepend.
        * assert (lfilled 0 (LH_base [] aft) (es1 ++ es2) ((es1 ++ es2) ++ aft)).
          unfold lfilled, lfill => //=.
          assert (length_rec ((es1 ++ es2) ++ aft) < m).
          { specialize (length_cons_rec (AI_ref_cont f)
                                        ((es1 ++ es2) ++ aft)) as H1.
            rewrite app_comm_cons in Hsize.
            repeat rewrite - cat_app in Hsize.
            rewrite app_comm_cons in H1.
            repeat rewrite - cat_app in H1.
            lia. }
          specialize (IHm _ H0 _ _ _ H i0 sh0).
          unfold to_eff0 in IHm at 1.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as [?|(vs' & Htv & Hfill)]; first by left.
          remember (  match vs' with
                      | susE vs i sh => susE vs i (sus_push_const sh [VAL_ref $ VAL_ref_cont f])
                      | swE vs k tf i sh => swE vs k tf i (sw_push_const sh [VAL_ref $ VAL_ref_cont f])
                      | thrE vs k i sh => thrE vs k i (exn_push_const sh [VAL_ref $ VAL_ref_cont f])
                      end ) as v'.
          right; exists  v'; split => //=.
          -- unfold to_eff0 => /=.
             rewrite merge_prepend.
             unfold to_eff0 in Htv.
             destruct (merge_values (map _ es1)) eqn:Hmerge1 => //=.
             inversion Htv; subst e.
             destruct vs'; subst => //.
          -- unfold lfilled, lfill => //=.
             unfold lfilled, lfill in Hfill ; simpl in Hfill.
             apply b2p in Hfill ; rewrite cat_app in Hfill. rewrite Hfill.
             subst v'. destruct vs' => //=.
             rewrite susfill_sus_push_const //.
             rewrite swfill_sw_push_const //.
             rewrite exnfill_exn_push_const //.
      + rewrite merge_throw in Hetov => //.
      + rewrite merge_suspend in Hetov => //.
      + rewrite merge_switch flatten_simplify in Hetov.
        inversion Hetov; subst.
        eapply filled_is_eff_sw_base_app_cases in Hfilled as HH;[|eauto..].
        2:{ unfold to_eff0. simpl. rewrite merge_switch. done. } 
        destruct HH as [-> [vs' [es [-> HH]]]].
        destruct HH as [[es11 [es12 [Heq Hconst]]]
                       |[[es11 [es12 [Heq (Hconst & Hconst')]]]
                        |[es11 [es12 [Heq (Hconst&Hconst'&Hconst'')]]]]].
        all: try by left.
        apply const_es_exists in Hconst as Hv.
        destruct Hv as [v Hv].
        right; exists (swE vs k tf i0 (SwBase v es12)).
        rewrite -to_eff_sw_eq Heq -Hv.
        split;auto. rewrite Hv in Heq. erewrite of_to_eff0.
        2: apply to_eff_sw_eq.
        rewrite -Heq. auto. 
      + destruct (merge_values $ map _ _) eqn:Hmerge => //.
        * destruct v => // ;
                       (try by rewrite merge_br in Hetov);
                     (try by rewrite merge_notval in Hetov);
                     (try by rewrite merge_return in Hetov) ;
                     try by rewrite merge_call_host in Hetov.
        * destruct e => //.
          -- rewrite merge_suspend // in Hetov.
          -- rewrite merge_switch flatten_simplify in Hetov.
             inversion Hetov.
             subst.
             assert (length_rec l0 < m).
             { unfold length_rec in Hsize ; simpl in Hsize. unfold length_rec. lia. }
             unfold lfilled, lfill in Hfilled ; 
               destruct lh ; fold lfill in Hfilled => //.
             1-2: destruct i => //.
             all: destruct (const_list l1) eqn:Hl1 => //.
             2-4: destruct (lfill _ _ _) eqn:Hfill => //.
             all: move/eqP in Hfilled.
             all: destruct l1 ; inversion Hfilled ; subst ; 
               last by unfold const_list in Hl1; inversion Hl1.
             ++ right. eexists. split.
                ** unfold to_eff0 => /=.
                   rewrite Hmerge merge_switch flatten_simplify => //.
                ** unfold lfilled, lfill => //=.
                   apply/eqP. repeat f_equal.
                   assert (iris.to_eff0 l0 = Some (swE vs k tf i0 sh0)) ;
                     first by unfold iris.to_eff0 ; rewrite Hmerge.          
                   apply iris.of_to_eff0 in H0 as <-.
                   unfold iris.of_eff0. 
                   done.
             ++ assert (lfilled i lh ((a :: es1) ++ es2) l4); 
                  first by unfold lfilled ; rewrite Hfill.
                specialize (IHm l4 H i lh (a :: es1) H0 i0 sh0).
                unfold to_eff0 in IHm at 1.
                rewrite Hmerge in IHm.
                destruct (IHm Logic.eq_refl) as [? | (vs' & Htv & Hfill')]; first by left.
                right; eexists ; split => //.
                unfold lfilled, lfill ; fold lfill => //=.
                unfold lfilled in Hfill'.
                destruct (lfill _ _ (_ ++ _)) => //.
                apply b2p in Hfill' ; by subst.
          -- destruct (exnelts_of_exception_clauses _ _) => //.
             rewrite merge_throw in Hetov => //.
             rewrite merge_notval in Hetov => //.
        * rewrite merge_notval in Hetov => //.
      + destruct (merge_values $ map _ _) eqn:Hmerge => //.
        * destruct v => // ;
                       (try by rewrite merge_br in Hetov);
                     (try by rewrite merge_notval in Hetov);
                     (try by rewrite merge_return in Hetov) ;
                     try by rewrite merge_call_host in Hetov.
        * destruct e => //.
          -- destruct (suselts_of_continuation_clauses _ _) eqn:Helts=> //.
             2: by rewrite merge_notval in Hetov.
             rewrite merge_suspend // in Hetov.
          -- destruct (swelts_of_continuation_clauses _ _) eqn:Helts => //.
             2: by rewrite merge_notval in Hetov.
             rewrite merge_switch flatten_simplify in Hetov.
             inversion Hetov.
             subst.
             assert (length_rec l1 < m).
             { unfold length_rec in Hsize ; simpl in Hsize. unfold length_rec. lia. }
             unfold lfilled, lfill in Hfilled ; 
               destruct lh ; fold lfill in Hfilled => //.
             1-2: destruct i => //.
             all: destruct (const_list l3) eqn:Hl1 => //.
             2-4: destruct (lfill _ _ _) eqn:Hfill => //.
             all: move/eqP in Hfilled.
             all: destruct l3 ; inversion Hfilled ; subst ; 
               last by unfold const_list in Hl1; inversion Hl1.
             ++ right; eexists. split.
                ** unfold to_eff0 => /=.
                   rewrite Hmerge Helts merge_switch flatten_simplify => //.
                ** unfold lfilled, lfill => //=.
                   apply/eqP. repeat f_equal.
                   by erewrite swelts_of_continuation_clauses_inj.
                   assert (iris.to_eff0 l1 = Some (swE vs k tf i0 sh0)) ;
                     first by unfold iris.to_eff0 ; rewrite Hmerge.          
                   apply iris.of_to_eff0 in H0 as <-.
                   unfold iris.of_eff0. 
                   done.
             ++ assert (lfilled i lh ((a :: es1) ++ es2) l7); 
                  first by unfold lfilled ; rewrite Hfill.
                specialize (IHm l7 H i lh (a :: es1) H0 i0 sh0).
                unfold to_eff0 in IHm at 1.
                rewrite Hmerge in IHm.
                destruct (IHm Logic.eq_refl) as [? | (vs' & Htv & Hfill')]; first by left.
                right; eexists ; split => //.
                unfold lfilled, lfill ; fold lfill => //=.
                unfold lfilled in Hfill'. destruct (lfill _ _ (_ ++ _)) => //.
                apply b2p in Hfill' ; by subst.
          -- rewrite merge_throw in Hetov => //.
        * rewrite merge_notval in Hetov => //.
      + destruct (merge_values $ map _ _) eqn:Hmerge => //.
        * destruct v => // ;
                       (try by rewrite merge_br in Hetov);
                     (try by rewrite merge_notval in Hetov);
                     (try by rewrite merge_return in Hetov) ;
                       try by rewrite merge_call_host in Hetov.
          destruct i1; last destruct (vh_decrease _) eqn:Hdecr.
          all: try by rewrite merge_notval in Hetov.
          rewrite merge_br in Hetov => //.
        * destruct e => //.
          -- rewrite merge_suspend // in Hetov.
          -- rewrite merge_switch flatten_simplify in Hetov.
             inversion Hetov. subst.
             assert (length_rec l0 < m).
             { unfold length_rec in Hsize ; simpl in Hsize. unfold length_rec. lia. }
             
          unfold lfilled, lfill in Hfilled ; 
            destruct lh ; fold lfill in Hfilled => //.
          1-2: destruct i => //.
          all: destruct (const_list l1) eqn:Hl1 => //.
          2-4: destruct (lfill _ _ _) eqn:Hfill => //.
          all: move/eqP in Hfilled.
          all: destruct l1 ; inversion Hfilled ; subst ; 
               last by unfold const_list in Hl1; inversion Hl1.
          ++ right. eexists. split.
             ** unfold to_eff0 => /=.
                rewrite Hmerge merge_switch flatten_simplify => //.
             ** unfold lfilled, lfill => //=.
                apply/eqP. repeat f_equal.
                assert (iris.to_eff0 l0 = Some (swE vs k tf i0 sh0)) ;
                  first by unfold iris.to_eff0 ; rewrite Hmerge.          
                apply iris.of_to_eff0 in H0 as <-.
                unfold iris.of_eff0. done. 
          ++ assert (lfilled i lh ((a :: es1) ++ es2) l4); 
               first by unfold lfilled ; rewrite Hfill.
             specialize (IHm l4 H i lh (a :: es1) H0 i0 sh0).
             unfold to_eff0 in IHm at 1.
             rewrite Hmerge in IHm.
             destruct (IHm Logic.eq_refl) as [? | (vs' & Htv & Hfill')]; first by left.
             right; eexists ; split => //.
             unfold lfilled, lfill ; fold lfill => //=.
             unfold lfilled in Hfill'. destruct (lfill _ _ (_ ++ _)) => //.
             apply b2p in Hfill' ; by subst.
          -- rewrite merge_throw in Hetov => //.
        * rewrite merge_notval in Hetov => //.
      + destruct (merge_values $ map _ _) eqn:Hmerge => //.
        * destruct v => //.
          all: try by rewrite merge_notval in Hetov.
          rewrite merge_call_host in Hetov => //.
        * destruct e => //.
          -- rewrite merge_suspend // in Hetov.
          -- rewrite merge_switch flatten_simplify in Hetov => //.
             inversion Hetov. subst.
             assert (length_rec l < m).
             { unfold length_rec in Hsize ; simpl in Hsize. unfold length_rec. lia. }
             
          unfold lfilled, lfill in Hfilled ; 
            destruct lh ; fold lfill in Hfilled => //.
          1-2: destruct i => //.
          all: destruct (const_list l0) eqn:Hl1 => //.
          2-4: destruct (lfill _ _ _) eqn:Hfill => //.
          all: move/eqP in Hfilled.
          all: destruct l0 ; inversion Hfilled ; subst ; 
               last by unfold const_list in Hl1; inversion Hl1.
          right. eexists. split.
             ++ unfold to_eff0 => /=.
                rewrite Hmerge merge_switch flatten_simplify => //.
             ++ unfold lfilled, lfill => //=.
                apply/eqP. repeat f_equal.
                assert (iris.to_eff0 l = Some (swE vs k tf i0 sh0)) ;
                  first by unfold iris.to_eff0 ; rewrite Hmerge.          
                apply iris.of_to_eff0 in H0 as <-.
                unfold iris.of_eff0. done. 
          -- rewrite merge_throw in Hetov => //.
        * rewrite merge_notval in Hetov => //.
      + rewrite merge_call_host // in Hetov.
    - remember (length_rec LI) as n.
      assert (length_rec LI < S n) ; first lia.
      remember (S n) as m.
      clear Heqn Heqm n.
      generalize dependent sh.
      generalize dependent i0. generalize dependent es1. generalize dependent lh.
      generalize dependent i. 
      generalize dependent LI.
      induction m ; intros LI Hsize ; intros ; first lia.
      destruct es1 ; first eauto.
      unfold to_eff0 in Hetov ; simpl in Hetov.
      destruct LI ; first by inversion Hetov.
      destruct a1 ; try destruct b ; simpl in Hetov  => //.
      all: try by rewrite merge_notval in Hetov.
      + rewrite merge_br in Hetov => //.
      + rewrite merge_return in Hetov => //.
      + rewrite merge_prepend in Hetov.
        destruct (merge_values $ map _ _) eqn:Hmerge => //.
        2: destruct e => //.  
        destruct v0 => //.
        simpl in Hetov.
        inversion Hetov; subst.
        rewrite - app_comm_cons in Hfilled.
        fold (AI_const (VAL_num v)) in Hfilled.
        apply lfilled_vLI in Hfilled as [(lh' & Hlh & Hfilled) | (-> & -> & aft & -> & <-)].
        * rewrite app_comm_cons in Hfilled.
          assert (length_rec LI < m) ;
            first by specialize (length_cons_rec (AI_basic $ BI_const v) LI) ; lia.
          specialize (IHm _ H _ _ _ Hfilled i0 sh0).
          unfold to_eff0 in IHm at 1.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as [Hconst | (vs' & Htv & Hfill)].
          -- by left.
          -- right. exists vs' ; split => //.
             subst ; by apply lfilled_prepend.
        * assert (lfilled 0 (LH_base [] aft) (es1 ++ es2) ((es1 ++ es2) ++ aft)).
          unfold lfilled, lfill => //=.
          assert (length_rec ((es1 ++ es2) ++ aft) < m).
          { specialize (length_cons_rec (AI_basic $ BI_const v)
                                        ((es1 ++ es2) ++ aft)) as H1.
            rewrite app_comm_cons in Hsize.
            repeat rewrite - cat_app in Hsize.
            rewrite app_comm_cons in H1.
            repeat rewrite - cat_app in H1.
            lia. }
          specialize (IHm _ H0 _ _ _ H i0 sh0).
          unfold to_eff0 in IHm at 1.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as [Hconst | (vs' & Htv & Hfill)]; first by left.
          remember (  match vs' with
                      | susE vs i sh => susE vs i (sus_push_const sh [VAL_num v])
                      | swE vs k tf i sh => swE vs k tf i (sw_push_const sh [VAL_num v])
                      | thrE vs k i sh => thrE vs k i (exn_push_const sh [VAL_num v])
                      end ) as v'.
          right. exists  v'; split => //=.
          -- unfold to_eff0 => /=.
             rewrite merge_prepend.
             unfold to_eff0 in Htv.
             destruct (merge_values (map _ es1)) eqn:Hmerge1 => //=.
             inversion Htv; subst e.
             destruct vs'; subst => //.
          -- unfold lfilled, lfill => //=.
             unfold lfilled, lfill in Hfill ; simpl in Hfill.
             apply b2p in Hfill ; rewrite cat_app in Hfill. rewrite Hfill.
             subst v'. destruct vs' => //=.
             rewrite susfill_sus_push_const /= //.
             rewrite swfill_sw_push_const //.
             rewrite exnfill_exn_push_const //.
      + rewrite merge_prepend in Hetov.
        destruct (merge_values $ map _ _) eqn:Hmerge => //.
        2: destruct e => //.  
        destruct v => //.
        simpl in Hetov.
        inversion Hetov; subst.
        rewrite - app_comm_cons in Hfilled.
        fold (AI_const (VAL_ref (VAL_ref_null r))) in Hfilled.
        apply lfilled_vLI in Hfilled as [(lh' & Hlh & Hfilled) | (-> & -> & aft & -> & <-)].
        * rewrite app_comm_cons in Hfilled.
          assert (length_rec LI < m) ;
            first by specialize (length_cons_rec (AI_basic $ BI_ref_null r) LI) ; lia.
          specialize (IHm _ H _ _ _ Hfilled i0 sh0).
          unfold to_eff0 in IHm at 1.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as [Hconst | (vs' & Htv & Hfill)]; first by left.
          right; exists vs' ; split => //.
          subst ; by apply lfilled_prepend.
        * assert (lfilled 0 (LH_base [] aft) (es1 ++ es2) ((es1 ++ es2) ++ aft)).
          unfold lfilled, lfill => //=.
          assert (length_rec ((es1 ++ es2) ++ aft) < m).
          { specialize (length_cons_rec (AI_basic $ BI_ref_null r)
                                        ((es1 ++ es2) ++ aft)) as H1.
            rewrite app_comm_cons in Hsize.
            repeat rewrite - cat_app in Hsize.
            rewrite app_comm_cons in H1.
            repeat rewrite - cat_app in H1.
            lia. }
          specialize (IHm _ H0 _ _ _ H i0 sh0).
          unfold to_eff0 in IHm at 1.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as [Hconst | (vs' & Htv & Hfill)]; first by left.
          remember (  match vs' with
                      | susE vs i sh => susE vs i (sus_push_const sh [VAL_ref $ VAL_ref_null r])
                      | swE vs k tf i sh => swE vs k tf i (sw_push_const sh [VAL_ref $ VAL_ref_null r])
                      | thrE vs k i sh => thrE vs k i (exn_push_const sh [VAL_ref $ VAL_ref_null r])
                          end ) as v'.
          right; exists  v'; split => //=.
          -- unfold to_eff0 => /=.
             rewrite merge_prepend.
             unfold to_eff0 in Htv.
             destruct (merge_values (map _ es1)) eqn:Hmerge1 => //=.
             inversion Htv; subst e.
             destruct vs'; subst => //.
          -- unfold lfilled, lfill => //=.
             unfold lfilled, lfill in Hfill ; simpl in Hfill.
             apply b2p in Hfill ; rewrite cat_app in Hfill. rewrite Hfill.
             subst v'. destruct vs' => //=.
             rewrite susfill_sus_push_const //.
             rewrite swfill_sw_push_const //.
             rewrite exnfill_exn_push_const //. 
           
      + rewrite merge_trap flatten_simplify in Hetov.
        by destruct LI.
      + rewrite merge_prepend in Hetov.
        destruct (merge_values $ map _ _) eqn:Hmerge => //.
        2: destruct e => //.  
        destruct v => //.
        simpl in Hetov.
        inversion Hetov; subst.
        rewrite - app_comm_cons in Hfilled.
        fold (AI_const (VAL_ref (VAL_ref_func f))) in Hfilled.
        apply lfilled_vLI in Hfilled as [(lh' & Hlh & Hfilled) | (-> & -> & aft & -> & <-)].
        * rewrite app_comm_cons in Hfilled.
          assert (length_rec LI < m) ;
            first by specialize (length_cons_rec (AI_ref f) LI) ; lia.
          specialize (IHm _ H _ _ _ Hfilled i0 sh0).
          unfold to_eff0 in IHm at 1.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as [? | (vs' & Htv & Hfill)]; first by left.
          right; exists vs' ; split => //.
          subst ; by apply lfilled_prepend.
        * assert (lfilled 0 (LH_base [] aft) (es1 ++ es2) ((es1 ++ es2) ++ aft)).
          unfold lfilled, lfill => //=.
          assert (length_rec ((es1 ++ es2) ++ aft) < m).
          { specialize (length_cons_rec (AI_ref f)
                                        ((es1 ++ es2) ++ aft)) as H1.
            rewrite app_comm_cons in Hsize.
            repeat rewrite - cat_app in Hsize.
            rewrite app_comm_cons in H1.
            repeat rewrite - cat_app in H1.
            lia. }
          specialize (IHm _ H0 _ _ _ H i0 sh0).
          unfold to_eff0 in IHm at 1.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as [? | (vs' & Htv & Hfill)]; first by left.
          remember (  match vs' with
                          | susE vs i sh => susE vs i (sus_push_const sh [VAL_ref $ VAL_ref_func f])
                      | swE vs k tf i sh => swE vs k tf i (sw_push_const sh [VAL_ref $ VAL_ref_func f])
                      | thrE vs k i sh => thrE vs k i (exn_push_const sh [VAL_ref $ VAL_ref_func f])
                                     end ) as v'.
          right; exists  v'; split => //=.
          -- unfold to_eff0 => /=.
             rewrite merge_prepend.
             unfold to_eff0 in Htv.
             destruct (merge_values (map _ es1)) eqn:Hmerge1 => //=.
             inversion Htv; subst e.
             destruct vs'; subst => //.
          -- unfold lfilled, lfill => //=.
             unfold lfilled, lfill in Hfill ; simpl in Hfill.
             apply b2p in Hfill ; rewrite cat_app in Hfill. rewrite Hfill.
             subst v'. destruct vs' => //=.
             rewrite susfill_sus_push_const //.
             rewrite swfill_sw_push_const //.
             rewrite exnfill_exn_push_const //.
      + rewrite merge_prepend in Hetov.
        destruct (merge_values $ map _ _) eqn:Hmerge => //.
        2: destruct e0 => //.  
        destruct v => //.
        simpl in Hetov.
        inversion Hetov; subst.
        rewrite - app_comm_cons in Hfilled.
        fold (AI_const (VAL_ref (VAL_ref_exn e t))) in Hfilled.
        apply lfilled_vLI in Hfilled as [(lh' & Hlh & Hfilled) | (-> & -> & aft & -> & <-)].
        * rewrite app_comm_cons in Hfilled.
          assert (length_rec LI < m) ;
            first by specialize (length_cons_rec (AI_ref_exn e t) LI) ; lia.
          specialize (IHm _ H _ _ _ Hfilled i0 sh0).
          unfold to_eff0 in IHm at 1.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as [? | (vs' & Htv & Hfill)]; first by left.
          right; exists vs' ; split => //.
          subst ; by apply lfilled_prepend.
        * assert (lfilled 0 (LH_base [] aft) (es1 ++ es2) ((es1 ++ es2) ++ aft)).
          unfold lfilled, lfill => //=.
          assert (length_rec ((es1 ++ es2) ++ aft) < m).
          { specialize (length_cons_rec (AI_ref_exn e t)
                                        ((es1 ++ es2) ++ aft)) as H1.
            rewrite app_comm_cons in Hsize.
            repeat rewrite - cat_app in Hsize.
            rewrite app_comm_cons in H1.
            repeat rewrite - cat_app in H1.
            lia. }
          specialize (IHm _ H0 _ _ _ H i0 sh0).
          unfold to_eff0 in IHm at 1.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as [?|(vs' & Htv & Hfill)]; first by left.
          remember (  match vs' with
                              | susE vs i sh => susE vs i (sus_push_const sh [VAL_ref $ VAL_ref_exn e t])
                      | swE vs k tf i sh => swE vs k tf i (sw_push_const sh [VAL_ref $ VAL_ref_exn e t])
                      | thrE vs k i sh => thrE vs k i (exn_push_const sh [VAL_ref $ VAL_ref_exn e t])
                      end ) as v'.
          right; exists  v'; split => //=.
          -- unfold to_eff0 => /=.
             rewrite merge_prepend.
             unfold to_eff0 in Htv.
             destruct (merge_values (map _ es1)) eqn:Hmerge1 => //=.
             inversion Htv; subst e0.
             destruct vs'; subst => //.
          -- unfold lfilled, lfill => //=.
             unfold lfilled, lfill in Hfill ; simpl in Hfill.
             apply b2p in Hfill ; rewrite cat_app in Hfill. rewrite Hfill.
             subst v'. destruct vs' => //=.
             rewrite susfill_sus_push_const //.
             rewrite swfill_sw_push_const //.
             rewrite exnfill_exn_push_const //.
      + rewrite merge_prepend in Hetov.
        destruct (merge_values $ map _ _) eqn:Hmerge => //.
        2: destruct e => //.  
        destruct v => //.
        simpl in Hetov.
        inversion Hetov; subst.
        rewrite - app_comm_cons in Hfilled.
        fold (AI_const (VAL_ref (VAL_ref_cont f))) in Hfilled.
        apply lfilled_vLI in Hfilled as [(lh' & Hlh & Hfilled) | (-> & -> & aft & -> & <-)].
        * rewrite app_comm_cons in Hfilled.
          assert (length_rec LI < m) ;
            first by specialize (length_cons_rec (AI_ref_cont f) LI) ; lia.
          specialize (IHm _ H _ _ _ Hfilled i0 sh0).
          unfold to_eff0 in IHm at 1.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as [?|(vs' & Htv & Hfill)]; first by left.
          right; exists vs' ; split => //.
          subst ; by apply lfilled_prepend.
        * assert (lfilled 0 (LH_base [] aft) (es1 ++ es2) ((es1 ++ es2) ++ aft)).
          unfold lfilled, lfill => //=.
          assert (length_rec ((es1 ++ es2) ++ aft) < m).
          { specialize (length_cons_rec (AI_ref_cont f)
                                        ((es1 ++ es2) ++ aft)) as H1.
            rewrite app_comm_cons in Hsize.
            repeat rewrite - cat_app in Hsize.
            rewrite app_comm_cons in H1.
            repeat rewrite - cat_app in H1.
            lia. }
          specialize (IHm _ H0 _ _ _ H i0 sh0).
          unfold to_eff0 in IHm at 1.
          rewrite Hmerge in IHm.
          destruct (IHm Logic.eq_refl) as [?|(vs' & Htv & Hfill)]; first by left.
          remember (  match vs' with
                      | susE vs i sh => susE vs i (sus_push_const sh [VAL_ref $ VAL_ref_cont f])
                      | swE vs k tf i sh => swE vs k tf i (sw_push_const sh [VAL_ref $ VAL_ref_cont f])
                      | thrE vs k i sh => thrE vs k i (exn_push_const sh [VAL_ref $ VAL_ref_cont f])
                      end ) as v'.
          right; exists  v'; split => //=.
          -- unfold to_eff0 => /=.
             rewrite merge_prepend.
             unfold to_eff0 in Htv.
             destruct (merge_values (map _ es1)) eqn:Hmerge1 => //=.
             inversion Htv; subst e.
             destruct vs'; subst => //.
          -- unfold lfilled, lfill => //=.
             unfold lfilled, lfill in Hfill ; simpl in Hfill.
             apply b2p in Hfill ; rewrite cat_app in Hfill. rewrite Hfill.
             subst v'. destruct vs' => //=.
             rewrite susfill_sus_push_const //.
             rewrite swfill_sw_push_const //.
             rewrite exnfill_exn_push_const //.
      + rewrite merge_throw in Hetov => //.
        inversion Hetov; subst.
        eapply filled_is_eff_thr_base_app_cases in Hfilled as HH;[|eauto..].
        2:{ unfold to_eff0. simpl. rewrite merge_throw. done. } 
        destruct HH as [-> [vs' [es [-> HH]]]].
        destruct HH as [[es11 [es12 [Heq Hconst]]]
                       |[[es11 [es12 [Heq (Hconst & Hconst')]]]
                        |[es11 [es12 [Heq (Hconst&Hconst'&Hconst'')]]]]].
        all: try by left.
        apply const_es_exists in Hconst as Hv.
        destruct Hv as [v Hv].
        right; exists (thrE vs a i0 (ExBase v es12)).
        rewrite -to_eff_thr_eq Heq -Hv.
        split;auto. rewrite Hv in Heq. erewrite of_to_eff0.
        2: apply to_eff_thr_eq.
        rewrite -Heq. auto.
      + rewrite merge_suspend in Hetov => //.
          
      + rewrite merge_switch in Hetov => //. 
      + destruct (merge_values $ map _ _) eqn:Hmerge => //.
        * destruct v => // ;
                       (try by rewrite merge_br in Hetov);
                     (try by rewrite merge_notval in Hetov);
                     (try by rewrite merge_return in Hetov) ;
                     try by rewrite merge_call_host in Hetov.
        * destruct e => //.
          -- rewrite merge_suspend // in Hetov.
          -- rewrite merge_switch // in Hetov.
          -- destruct (exnelts_of_exception_clauses _ _) eqn:Helts => //.
             2: by rewrite merge_notval in Hetov.
             rewrite merge_throw flatten_simplify in Hetov.
             inversion Hetov.
             subst.
             assert (length_rec l0 < m).
             { unfold length_rec in Hsize ; simpl in Hsize. unfold length_rec. lia. }
             unfold lfilled, lfill in Hfilled ; 
               destruct lh ; fold lfill in Hfilled => //.
             1-2: destruct i => //.
             all: destruct (const_list l2) eqn:Hl1 => //.
             2-4: destruct (lfill _ _ _) eqn:Hfill => //.
             all: move/eqP in Hfilled.
             all: destruct l2 ; inversion Hfilled ; subst ; 
               last by unfold const_list in Hl1; inversion Hl1.
             ++ right. eexists. split.
                ** unfold to_eff0 => /=.
                   rewrite Hmerge Helts merge_throw flatten_simplify => //.
                ** unfold lfilled, lfill => //=.
                   apply/eqP. repeat f_equal.
                   by erewrite exnelts_of_exception_clauses_inj.
                   assert (iris.to_eff0 l0 = Some (thrE vs a i0 sh0)) ;
                     first by unfold iris.to_eff0 ; rewrite Hmerge.          
                   apply iris.of_to_eff0 in H0 as <-.
                   unfold iris.of_eff0. 
                   done.
             ++ assert (lfilled i lh ((a0 :: es1) ++ es2) l5); 
                  first by unfold lfilled ; rewrite Hfill.
                specialize (IHm l5 H i lh (a0 :: es1) H0 i0 sh0).
                unfold to_eff0 in IHm at 1.
                rewrite Hmerge in IHm.
                destruct (IHm Logic.eq_refl) as [? | (vs' & Htv & Hfill')]; first by left.
                right; eexists ; split => //.
                unfold lfilled, lfill ; fold lfill => //=.
                unfold lfilled in Hfill'.
                destruct (lfill _ _ (_ ++ _)) => //.
                apply b2p in Hfill' ; by subst.
        * rewrite merge_notval in Hetov => //.
      + destruct (merge_values $ map _ _) eqn:Hmerge => //.
        * destruct v => // ;
                       (try by rewrite merge_br in Hetov);
                     (try by rewrite merge_notval in Hetov);
                     (try by rewrite merge_return in Hetov) ;
                     try by rewrite merge_call_host in Hetov.
        * destruct e => //.
          -- destruct (suselts_of_continuation_clauses _ _) eqn:Helts=> //.
             2: by rewrite merge_notval in Hetov.
             rewrite merge_suspend // in Hetov.
          -- destruct (swelts_of_continuation_clauses _ _) eqn:Helts => //.
             2: by rewrite merge_notval in Hetov.
             rewrite merge_switch // in Hetov.
          -- rewrite merge_throw flatten_simplify in Hetov.
             inversion Hetov.
             subst.
             assert (length_rec l1 < m).
             { unfold length_rec in Hsize ; simpl in Hsize. unfold length_rec. lia. }
             unfold lfilled, lfill in Hfilled ; 
               destruct lh ; fold lfill in Hfilled => //.
             1-2: destruct i => //.
             all: destruct (const_list l2) eqn:Hl1 => //.
             2-4: destruct (lfill _ _ _) eqn:Hfill => //.
             all: move/eqP in Hfilled.
             all: destruct l2 ; inversion Hfilled ; subst ; 
               last by unfold const_list in Hl1; inversion Hl1.
             ++ right; eexists. split.
                ** unfold to_eff0 => /=.
                   rewrite Hmerge merge_throw flatten_simplify => //.
                ** unfold lfilled, lfill => //=.
                   apply/eqP. repeat f_equal.
                   assert (iris.to_eff0 l1 = Some (thrE vs a i0 sh0)) ;
                     first by unfold iris.to_eff0 ; rewrite Hmerge.          
                   apply iris.of_to_eff0 in H0 as <-.
                   unfold iris.of_eff0. 
                   done.
             ++ assert (lfilled i lh ((a0 :: es1) ++ es2) l6); 
                  first by unfold lfilled ; rewrite Hfill.
                specialize (IHm l6 H i lh (a0 :: es1) H0 i0 sh0).
                unfold to_eff0 in IHm at 1.
                rewrite Hmerge in IHm.
                destruct (IHm Logic.eq_refl) as [? | (vs' & Htv & Hfill')]; first by left.
                right; eexists ; split => //.
                unfold lfilled, lfill ; fold lfill => //=.
                unfold lfilled in Hfill'. destruct (lfill _ _ (_ ++ _)) => //.
                apply b2p in Hfill' ; by subst.
        * rewrite merge_notval in Hetov => //.
      + destruct (merge_values $ map _ _) eqn:Hmerge => //.
        * destruct v => // ;
                       (try by rewrite merge_br in Hetov);
                     (try by rewrite merge_notval in Hetov);
                     (try by rewrite merge_return in Hetov) ;
                       try by rewrite merge_call_host in Hetov.
          destruct i1; last destruct (vh_decrease _) eqn:Hdecr.
          all: try by rewrite merge_notval in Hetov.
          rewrite merge_br in Hetov => //.
        * destruct e => //.
          -- rewrite merge_suspend // in Hetov.
          -- rewrite merge_switch // in Hetov.
          -- rewrite merge_throw flatten_simplify in Hetov.
             inversion Hetov. subst.
             assert (length_rec l0 < m).
             { unfold length_rec in Hsize ; simpl in Hsize. unfold length_rec. lia. }
             
          unfold lfilled, lfill in Hfilled ; 
            destruct lh ; fold lfill in Hfilled => //.
          1-2: destruct i => //.
          all: destruct (const_list l1) eqn:Hl1 => //.
          2-4: destruct (lfill _ _ _) eqn:Hfill => //.
          all: move/eqP in Hfilled.
          all: destruct l1 ; inversion Hfilled ; subst ; 
               last by unfold const_list in Hl1; inversion Hl1.
          ++ right. eexists. split.
             ** unfold to_eff0 => /=.
                rewrite Hmerge merge_throw flatten_simplify => //.
             ** unfold lfilled, lfill => //=.
                apply/eqP. repeat f_equal.
                assert (iris.to_eff0 l0 = Some (thrE vs a i0 sh0)) ;
                  first by unfold iris.to_eff0 ; rewrite Hmerge.          
                apply iris.of_to_eff0 in H0 as <-.
                unfold iris.of_eff0. done. 
          ++ assert (lfilled i lh ((a0 :: es1) ++ es2) l4); 
               first by unfold lfilled ; rewrite Hfill.
             specialize (IHm l4 H i lh (a0 :: es1) H0 i0 sh0).
             unfold to_eff0 in IHm at 1.
             rewrite Hmerge in IHm.
             destruct (IHm Logic.eq_refl) as [? | (vs' & Htv & Hfill')]; first by left.
             right; eexists ; split => //.
             unfold lfilled, lfill ; fold lfill => //=.
             unfold lfilled in Hfill'. destruct (lfill _ _ (_ ++ _)) => //.
             apply b2p in Hfill' ; by subst.
        * rewrite merge_notval in Hetov => //.
      + destruct (merge_values $ map _ _) eqn:Hmerge => //.
        * destruct v => //.
          all: try by rewrite merge_notval in Hetov.
          rewrite merge_call_host in Hetov => //.
        * destruct e => //.
          -- rewrite merge_suspend // in Hetov.
          -- rewrite merge_switch // in Hetov.
          -- rewrite merge_throw flatten_simplify in Hetov => //.
             inversion Hetov. subst.
             assert (length_rec l < m).
             { unfold length_rec in Hsize ; simpl in Hsize. unfold length_rec. lia. }
             
          unfold lfilled, lfill in Hfilled ; 
            destruct lh ; fold lfill in Hfilled => //.
          1-2: destruct i => //.
          all: destruct (const_list l0) eqn:Hl1 => //.
          2-4: destruct (lfill _ _ _) eqn:Hfill => //.
          all: move/eqP in Hfilled.
          all: destruct l0 ; inversion Hfilled ; subst ; 
               last by unfold const_list in Hl1; inversion Hl1.
          right. eexists. split.
             ++ unfold to_eff0 => /=.
                rewrite Hmerge merge_throw flatten_simplify => //.
             ++ unfold lfilled, lfill => //=.
                apply/eqP. repeat f_equal.
                assert (iris.to_eff0 l = Some (thrE vs a i0 sh0)) ;
                  first by unfold iris.to_eff0 ; rewrite Hmerge.          
                apply iris.of_to_eff0 in H0 as <-.
                unfold iris.of_eff0. done. 
        * rewrite merge_notval in Hetov => //.
      + rewrite merge_call_host // in Hetov.
  Qed.

  
  Lemma to_val_brV_None vs n i lh es LI :
    const_list vs ->
    length vs = n ->
    lfilled i lh (vs ++ [AI_basic (BI_br i)]) LI ->
    iris.to_val0 [AI_label n es LI] = None.
  Proof.
    intros Hconst Hlen Hlfill.
    eapply val_head_stuck_reduce.
    apply r_simple. eapply rs_br;eauto.
    Unshelve.
    apply (Build_store_record [] [] [] [] [] [] []).
    apply (Build_frame [] (Build_instance [] [] [] [] [] [])).
  Qed.

  Lemma to_val_immV_label_None es v m ctx :
    iris.to_val0 es = Some (immV v) ->
    iris.to_val0 [AI_label m ctx es] = None.
  Proof.
    intros Hes.
    eapply val_head_stuck_reduce.
    eapply r_simple, rs_label_const. eapply to_val_const_list;eauto.
    Unshelve. apply (Build_store_record [] [] [] [] [] [] []).
    apply (Build_frame [] (Build_instance [] [] [] [] [] [])).
  Qed.  
  
  Lemma to_val_trapV_label_None es m ctx :
    iris.to_val0 es = Some trapV ->
    iris.to_val0 [AI_label m ctx es] = None.
  Proof.
    intros Hes.
    apply to_val_trap_is_singleton in Hes as ->.
    eapply val_head_stuck_reduce.
    eapply r_simple, rs_label_trap.
    Unshelve. apply (Build_store_record [] [] [] [] [] [] []).
    apply (Build_frame [] (Build_instance [] [] [] [] [] [])).
  Qed.

  Lemma to_val_immV_prompt_None es v m ctx :
    iris.to_val0 es = Some (immV v) ->
    iris.to_val0 [AI_prompt m ctx es] = None.
  Proof.
    intros Hes.
    eapply val_head_stuck_reduce.
    eapply r_simple, rs_prompt_const. eapply to_val_const_list;eauto.
    Unshelve. apply (Build_store_record [] [] [] [] [] [] []).
    apply (Build_frame [] (Build_instance [] [] [] [] [] [])).
  Qed.  
  
  Lemma to_val_trapV_prompt_None es m ctx :
    iris.to_val0 es = Some trapV ->
    iris.to_val0 [AI_prompt m ctx es] = None.
  Proof.
    intros Hes.
    apply to_val_trap_is_singleton in Hes as ->.
    eapply val_head_stuck_reduce.
    eapply r_simple, rs_prompt_trap.
    Unshelve. apply (Build_store_record [] [] [] [] [] [] []).
    apply (Build_frame [] (Build_instance [] [] [] [] [] [])).
  Qed.

  Lemma to_val_immV_handler_None es v ctx :
    iris.to_val0 es = Some (immV v) ->
    iris.to_val0 [AI_handler ctx es] = None.
  Proof.
    intros Hes.
    eapply val_head_stuck_reduce.
    eapply r_simple, rs_handler_const. eapply to_val_const_list;eauto.
    Unshelve. apply (Build_store_record [] [] [] [] [] [] []).
    apply (Build_frame [] (Build_instance [] [] [] [] [] [])).
  Qed.  
  
  Lemma to_val_trapV_handler_None es ctx :
    iris.to_val0 es = Some trapV ->
    iris.to_val0 [AI_handler ctx es] = None.
  Proof.
    intros Hes.
    apply to_val_trap_is_singleton in Hes as ->.
    eapply val_head_stuck_reduce.
    eapply r_simple, rs_handler_trap.
    Unshelve. apply (Build_store_record [] [] [] [] [] [] []).
    apply (Build_frame [] (Build_instance [] [] [] [] [] [])).
  Qed.

  Lemma to_val_cons_immV v l :
    iris.to_val0 (AI_const v :: iris.of_val0 (immV l)) = Some (immV (v :: l)).
  Proof.
    rewrite separate1.
    erewrite to_val_cat_inv;eauto.
    3: apply to_of_val0.
    2: destruct v => //.
    2: destruct v => //. 
    auto.
  Qed.
  Lemma to_val_cons_brV i (lh : valid_holed i) v es :
    iris.to_val0 es = Some (brV lh) ->
    iris.to_val0 (AI_const v :: es) = Some (brV (vh_push_const lh [v])).
  Proof.
    intros Hes.
    unfold to_val,iris.to_val0. simpl.
    unfold to_val,iris.to_val0 in Hes.
    rewrite merge_prepend to_val_instr_AI_const.
    destruct (merge_values (map to_val_instr es)) eqn:Hsome => //.
    simplify_eq.
    simpl. done.
  Qed.
  Lemma to_val_cons_retV s v es :
    iris.to_val0 es = Some (retV s) ->
    iris.to_val0 (AI_const v :: es) = Some (retV (sh_push_const s [v])).
  Proof.
    intros Hes.
    unfold to_val,iris.to_val0. 
    unfold to_val,iris.to_val0 in Hes.
    rewrite merge_prepend to_val_instr_AI_const.
    fold (map to_val_instr es).
    destruct (merge_values (map to_val_instr es)) eqn:Hsome => //.
    simplify_eq. done.
  Qed.
  Lemma to_val_cons_callHostV tf h cvs s v es :
    iris.to_val0 es = Some (callHostV tf h cvs s) ->
    iris.to_val0 (AI_const v :: es) = Some (callHostV tf h cvs (llh_push_const s [v])).
  Proof.
    intros Hes.
    unfold to_val,iris.to_val0. 
    unfold to_val,iris.to_val0 in Hes.
    rewrite /= merge_prepend to_val_instr_AI_const.
    destruct (merge_values (map to_val_instr es)) eqn:Hsome => //.
    simplify_eq. done.
  Qed.

  Lemma to_eff_cons_susE vs i lh v es :
    iris.to_eff0 es = Some (susE vs i lh) ->
    iris.to_eff0 (AI_const v :: es) = Some (susE vs i (sus_push_const lh [v])).
  Proof.
    intros Hes.
    unfold to_eff0. simpl.
    unfold to_eff0 in Hes.
    rewrite merge_prepend to_val_instr_AI_const.
    destruct (merge_values (map to_val_instr es)) eqn:Hsome => //.
    simplify_eq.
    simpl. done.
  Qed.

    Lemma to_eff_cons_swE vs k tf i lh v es :
    iris.to_eff0 es = Some (swE vs k tf i lh) ->
    iris.to_eff0 (AI_const v :: es) = Some (swE vs k tf i (sw_push_const lh [v])).
  Proof.
    intros Hes.
    unfold to_eff0. simpl.
    unfold to_eff0 in Hes.
    rewrite merge_prepend to_val_instr_AI_const.
    destruct (merge_values (map to_val_instr es)) eqn:Hsome => //.
    simplify_eq.
    simpl. done.
  Qed.
    Lemma to_eff_cons_thrE vs k i lh v es :
    iris.to_eff0 es = Some (thrE vs k i lh) ->
    iris.to_eff0 (AI_const v :: es) = Some (thrE vs k i (exn_push_const lh [v])).
  Proof.
    intros Hes.
    unfold to_eff0. simpl.
    unfold to_eff0 in Hes.
    rewrite merge_prepend to_val_instr_AI_const.
    destruct (merge_values (map to_val_instr es)) eqn:Hsome => //.
    simplify_eq.
    simpl. done.
  Qed.
  
  Lemma to_val_cons_None es v :
    iris.to_val0 es = None ->
    iris.to_val0 (AI_const v :: es) = None.
  Proof.
    intros Hes.
    rewrite separate1.
    apply to_val_cat_None2;auto.
    simpl. rewrite const_const => //.
  Qed.
   Lemma to_val_cons_None_inv es v :
     is_const v ->
     iris.to_val0 (v :: es) = None ->
     iris.to_val0 es = None \/ es = [::AI_trap].
   Proof.
     unfold iris.to_val0 => /=.
     destruct v => //=.
     destruct b => //=.
     all: rewrite merge_prepend.
     all: destruct (merge_values _) eqn:Hmerge => //=.
     all: try destruct v0 => //=.
     all: try destruct e => //=.
     all: try destruct v => //=.
     all: remember (to_val0 es) as tv.
     all: remember Heqtv as Heqtv'; clear HeqHeqtv'.
     all: unfold to_val, iris.to_val0 in Heqtv.
     all: rewrite Hmerge in Heqtv.
     all: rewrite Heqtv' in Heqtv.
     all: try apply to_val_trap_is_singleton in Heqtv as ->.
     all: try by right.
     all: try by left.
   Qed.

   Lemma to_eff_cons_None es v :
    iris.to_eff0 es = None ->
    iris.to_eff0 (AI_const v :: es) = None.
  Proof.
    intros Hes.
    rewrite separate1.
    apply to_eff_cat_None2;auto.
    simpl. rewrite const_const => //.
  Qed.
   Lemma to_eff_cons_None_inv es v :
     is_const v ->
     iris.to_eff0 (v :: es) = None ->
     iris.to_eff0 es = None.
   Proof.
     unfold iris.to_eff0 => /=.
     destruct v => //=.
     destruct b => //=.
     all: rewrite merge_prepend.
     all: destruct (merge_values _) eqn:Hmerge => //=.
     all: try destruct e => //.
     all: try destruct e0 => //=.
  Qed.
  
  Lemma to_val_AI_trap_Some_nil es vs :
    iris.to_val0 ([AI_trap] ++ es) = Some vs -> es = [].
  Proof.
    unfold iris.to_val0.
    simpl. rewrite merge_trap flatten_simplify.
    destruct es => //. 
  Qed.

  Lemma to_val_None_label n es' LI :
    iris.to_val0 LI = None ->
    iris.to_val0 [AI_label n es' LI] = None.
  Proof.
    intros HLI.
    unfold iris.to_val0. cbn. 
    unfold iris.to_val0 in HLI.
    destruct (merge_values (map to_val_instr LI)) eqn:Hmerge => //.
    destruct e => //. 
  Qed.

   Lemma to_eff_None_label n es' LI :
    iris.to_eff0 LI = None ->
    iris.to_eff0 [AI_label n es' LI] = None.
  Proof.
    intros HLI.
    unfold iris.to_eff0. cbn. 
    unfold iris.to_eff0 in HLI.
    destruct (merge_values (map to_val_instr LI)) eqn:Hmerge => //.
    destruct v => //.
    destruct i => //.
    destruct (vh_decrease _) => //. 
  Qed.

  Lemma to_val_None_prompt n es' LI :
    iris.to_val0 LI = None ->
    iris.to_val0 [AI_prompt n es' LI] = None.
  Proof.
    intros HLI.
    unfold iris.to_val0. simpl.
    unfold iris.to_val0 in HLI.
    destruct (merge_values (map to_val_instr LI)) eqn:Hmerge => //.
    destruct e => //.
    destruct (suselts_of_continuation_clauses _) => //.
    destruct (swelts_of_continuation_clauses _) => //. 
  Qed.

   Lemma to_eff_None_prompt n es' LI :
    iris.to_eff0 LI = None ->
    iris.to_eff0 [AI_prompt n es' LI] = None.
  Proof.
    intros HLI.
    unfold iris.to_eff0. simpl.
    unfold iris.to_eff0 in HLI.
    destruct (merge_values (map to_val_instr LI)) eqn:Hmerge => //.
    destruct v => //.
  Qed.

    Lemma to_val_None_handler es' LI :
    iris.to_val0 LI = None ->
    iris.to_val0 [AI_handler es' LI] = None.
  Proof.
    intros HLI.
    unfold iris.to_val0. cbn. 
    unfold iris.to_val0 in HLI.
    destruct (merge_values (map to_val_instr LI)) eqn:Hmerge => //.
    destruct e => //.
    destruct (exnelts_of_exception_clauses) => //. 
  Qed.

  Lemma to_eff_None_handler es' LI :
    iris.to_eff0 LI = None ->
    iris.to_eff0 [AI_handler es' LI] = None.
  Proof.
    intros HLI.
    unfold iris.to_eff0. cbn. 
    unfold iris.to_eff0 in HLI.
    destruct (merge_values (map to_val_instr LI)) eqn:Hmerge => //.
    destruct v => //.
  Qed.

  Lemma to_val_None_lfilled LI k lh es :
    iris.to_val0 es = None → lfilled k lh es LI -> iris.to_val0 LI = None.
  Proof.
    revert LI k es;
      induction lh;intros LI k es Hnone Hfill%lfilled_Ind_Equivalent.
    all: inversion Hfill;simplify_eq.
    - apply to_val_cat_None2;auto.
      apply to_val_cat_None1;auto. 
    - apply lfilled_Ind_Equivalent in H8.
      apply IHlh in H8;auto.
      apply to_val_cat_None2;auto.
      apply to_val_cat_None1;auto.
      apply to_val_None_label. auto.
    - apply lfilled_Ind_Equivalent in H7.
      apply IHlh in H7;auto.
      apply to_val_cat_None2;auto.
      apply to_val_cat_None1;auto.
      apply to_val_None_handler. auto.
    - apply lfilled_Ind_Equivalent in H8.
      apply IHlh in H8;auto.
      apply to_val_cat_None2;auto.
      apply to_val_cat_None1;auto.
      apply to_val_None_prompt. auto.

  Qed.

    Lemma to_eff_None_lfilled LI k lh es :
      (const_list es -> False) -> iris.to_eff0 es = None → lfilled k lh es LI -> iris.to_eff0 LI = None.
  Proof.
    revert LI k es;
      induction lh;intros LI k es Hes Hnone Hfill%lfilled_Ind_Equivalent.
    all: inversion Hfill;simplify_eq.
    - apply to_eff_cat_None2;auto.
      apply to_eff_cat_None1;auto. 
    - apply lfilled_Ind_Equivalent in H8.
      apply IHlh in H8;auto.
      apply to_eff_cat_None2;auto.
      apply to_eff_cat_None1;auto.
      apply to_eff_None_label. auto.
    - apply lfilled_Ind_Equivalent in H7.
      apply IHlh in H7;auto.
      apply to_eff_cat_None2;auto.
      apply to_eff_cat_None1;auto.
      apply to_eff_None_handler. auto.
    - apply lfilled_Ind_Equivalent in H8.
      apply IHlh in H8;auto.
      apply to_eff_cat_None2;auto.
      apply to_eff_cat_None1;auto.
      apply to_eff_None_prompt. auto.

  Qed.


  Lemma to_eff_None_lfilled_inv LI k lh es :
    is_pure lh -> iris.to_eff0 LI = None → lfilled k lh es LI -> iris.to_eff0 es = None.
  Proof.
    intros Hpure.
    revert LI k es;
      induction Hpure.
    all: intros LI k es' Hnone Hfill%lfilled_Ind_Equivalent.
    all: inversion Hfill;simplify_eq.
    - apply to_eff_cat_None2_inv in Hnone => //.
      apply to_eff_cat_None_inv in Hnone => //. 
    - apply lfilled_Ind_Equivalent in H8.
      apply IHHpure in H8;auto.
      apply to_eff_cat_None2_inv in Hnone => //.
      apply to_eff_cat_None_inv in Hnone => //.
      unfold to_eff0.
      unfold to_eff0 in Hnone.
      simpl in Hnone.
      destruct (merge_values (map _ LI0)) => //.
      destruct e => //. 
  Qed. 

  Lemma to_val_app_retV v :
  ∀ (s : simple_valid_holed) (es : iris.expr0),
    iris.to_val0 es = Some (retV s)
    → iris.to_val0 (v_to_e_list v ++ es)%SEQ =
        Some (retV (sh_push_const s v)).
  Proof.
    induction v;intros s es Hes.
    simpl. rewrite sh_push_const_nil;auto.
    simpl.
    apply IHv in Hes.
    rewrite (separate1 a).
    erewrite sh_push_const_app.
    apply to_val_cons_retV with (v:=a) in Hes.
    rewrite Hes. auto.
  Qed.

  Lemma to_val_local_inv n f LI v :
    iris.to_val0 [AI_frame n f LI] = Some v ->
    ∃ tf h w vh, v = callHostV tf h w (LL_frame [] n f vh []).
  Proof.
    intros Hv.
    unfold iris.to_val0 in Hv. cbn in Hv.
    destruct (merge_values (map to_val_instr LI));try done.
    destruct v0;try done.
    inversion Hv;eauto.
    destruct e => //. 
  Qed.

   Lemma to_eff_local_inv n f LI v :
     iris.to_eff0 [AI_frame n f LI] = Some v ->
     (∃ vs i sh, v = susE vs i (SuFrame [] n f sh [])) \/
       (∃ vs i k tf sh, v = swE vs i k tf (SwFrame [] n f sh [])) \/
       ∃ vs i k sh, v = thrE vs i k (ExFrame [] n f sh []).
   Proof.
    intros Hv.
    unfold iris.to_eff0 in Hv. cbn in Hv.
    destruct (merge_values (map to_val_instr LI));try done.
    destruct v0;try done.
    destruct e => //. 
    all: inversion Hv;eauto.
    right; left; eauto. by repeat eexists.
    right; right; eauto.
  Qed.

  Lemma to_val_local_add_frame LI' tf h w vh n f :
    iris.to_val0 LI' = Some (callHostV tf h w vh) ->
    iris.to_val0 [AI_frame n f LI'] = Some (callHostV tf h w (LL_frame [] n f vh [])).
  Proof.
    intros Hv.
    unfold iris.to_val0 in Hv. cbn in Hv.
    unfold iris.to_val0. cbn.
    destruct (merge_values (map to_val_instr LI'));try done.
    simplify_eq.  auto.
  Qed.

  Lemma sfill_call_host_compose wh vh tf h w es1 :
    iris.to_val0 es1 = None ->
    sfill wh [AI_call_host tf h w] = sfill vh es1 ->
    ∃ vh', es1 = sfill vh' [AI_call_host tf h w].
  Proof.
    intros Hnone Hs.
    assert (es1 ≠ []);[intros Hcontr;subst;done|].
    assert (const_list es1 = false).
    { destruct (const_list es1) eqn:Hcontr; auto. apply const_list_to_val in Hcontr as (? & ? & ?). congruence. }
    assert (es1 = [AI_trap] → False).
    { intros Hcontr. subst. done. }
    
    revert wh Hs.
    induction vh;intros wh Hs.
    - destruct wh.
      all: cbn in *.
      all: rewrite separate1 in Hs.
      all: symmetry in Hs.
      all: apply const_list_snoc_eq3 in Hs;auto;[|apply v_to_e_is_const_list..].
      all: destruct Hs as [vs2 [es2 [Heq1 [Heq2 [Heq3 Hconst]]]]].
      all: apply const_es_exists in Hconst as [? ?].
      all: simplify_eq.
      exists (SH_base x es2).
      2: eexists (SH_rec x n l2 wh es2).
      3: eexists (SH_prompt _ _ _ _ _).
      4: eexists (SH_handler _ _ _ _).
      all: cbn.
      all: auto.
    - destruct wh.
      all: cbn in *.
      all: rewrite separate1 in Hs.
      all: rewrite (separate1 _ l1) in Hs.
      all: apply const_list_snoc_eq3 in Hs;auto;[|apply v_to_e_is_const_list..].
      all: destruct Hs as [vs2 [es2 [Heq1 [Heq2 [Heq3 Hconst]]]]].
      all: apply const_es_exists in Hconst as [? ?].
      all: simplify_eq.
      all: destruct x as [ | v00 ?]; last by destruct v00 => //; destruct v => //.
      all: inversion Heq2; subst.
      apply IHvh in H5 as [vh' Hvh'].
      subst es1. eauto.
    - destruct wh.
      all: cbn in *.
      all: rewrite separate1 in Hs.
      all: rewrite (separate1 _ l2) in Hs.
      all: apply const_list_snoc_eq3 in Hs;auto;[|apply v_to_e_is_const_list..].
      all: destruct Hs as [vs2 [es2 [Heq1 [Heq2 [Heq3 Hconst]]]]].
      all: apply const_es_exists in Hconst as [? ?].
      all: simplify_eq.
      all: destruct x as [ | v00 ?]; last by destruct v00 => //; destruct v => //.
      all: inversion Heq2; subst.
      apply IHvh in H5 as [vh' Hvh'].
      subst es1. eauto.
    - destruct wh.
      all: cbn in *.
      all: rewrite separate1 in Hs.
      all: rewrite (separate1 _ l1) in Hs.
      all: apply const_list_snoc_eq3 in Hs;auto;[|apply v_to_e_is_const_list..].
      all: destruct Hs as [vs2 [es2 [Heq1 [Heq2 [Heq3 Hconst]]]]].
      all: apply const_es_exists in Hconst as [? ?].
      all: simplify_eq.
      all: destruct x as [ | v00 ?]; last by destruct v00 => //; destruct v => //.
      all: inversion Heq2; subst.
      apply IHvh in H4 as [vh' Hvh'].
      subst es1. eauto.
  Qed.

  Lemma llfill_call_host_compose wh vh tf h w es1 :
    iris.to_val0 es1 = None ->
    llfill wh [AI_call_host tf h w] = llfill vh es1 ->
    ∃ vh', es1 = llfill vh' [AI_call_host tf h w].
  Proof.
    intros Hnone Hs.
    assert (es1 ≠ []);[intros Hcontr;subst;done|].
    assert (const_list es1 = false).
    { destruct (const_list es1) eqn:Hcontr; auto. apply const_list_to_val in Hcontr as (? & ? & ?). congruence. }
    assert (es1 = [AI_trap] → False).
    { intros Hcontr. subst. done. }
    
    revert wh Hs. induction vh;intros wh Hs.
    - destruct wh.
      all: cbn in *.
      all: rewrite separate1 in Hs.
      all: symmetry in Hs.
      all: apply const_list_snoc_eq3 in Hs;auto;[|apply v_to_e_is_const_list..].
      all: destruct Hs as [vs2 [es2 [Heq1 [Heq2 [Heq3 Hconst]]]]].
      all: apply const_es_exists in Hconst as [? ?].
      all: simplify_eq.
      exists (LL_base x es2).
      2: eexists (LL_label _ _ _ _ _).
      3: eexists (LL_frame _ _ _ _ _).
      4: eexists (LL_prompt _ _ _ _ _).
      5: eexists (LL_handler _ _ _ _).
      all: cbn.
      all: auto.
    - destruct wh.
      all: cbn in *.
      all: rewrite separate1 in Hs.
      all: rewrite (separate1 _ l1) in Hs.
      all: apply const_list_snoc_eq3 in Hs;auto;[|apply v_to_e_is_const_list..].
      all: destruct Hs as [vs2 [es2 [Heq1 [Heq2 [Heq3 Hconst]]]]].
      all: apply const_es_exists in Hconst as [? ?].
      all: simplify_eq.
      all: destruct x as [|v00 ?]; last by destruct v00 => //; destruct v.
      all: inversion Heq2; subst.
      apply IHvh in H5 as [vh' Hvh'].
      subst es1. eauto.
    - destruct wh.
      all: cbn in *.
      all: rewrite separate1 in Hs.
      all: rewrite (separate1 _ l0) in Hs.
      all: apply const_list_snoc_eq3 in Hs;auto;[|apply v_to_e_is_const_list..].
      all: destruct Hs as [vs2 [es2 [Heq1 [Heq2 [Heq3 Hconst]]]]].
      all: apply const_es_exists in Hconst as [? ?].
      all: simplify_eq.
      all: destruct x as [|v00 ?]; last by destruct v00 => //; destruct v.
      all: inversion Heq2; subst.
      apply IHvh in H5 as [vh' Hvh'].
      subst es1. eauto.
    - destruct wh.
      all: cbn in *.
      all: rewrite separate1 in Hs.
      all: rewrite (separate1 _ l2) in Hs.
      all: apply const_list_snoc_eq3 in Hs;auto;[|apply v_to_e_is_const_list..].
      all: destruct Hs as [vs2 [es2 [Heq1 [Heq2 [Heq3 Hconst]]]]].
      all: apply const_es_exists in Hconst as [? ?].
      all: simplify_eq.
      all: destruct x as [|v00 ?]; last by destruct v00 => //; destruct v.
      all: inversion Heq2; subst.
      apply IHvh in H5 as [vh' Hvh'].
      subst es1. eauto.
    - destruct wh.
      all: cbn in *.
      all: rewrite separate1 in Hs.
      all: rewrite (separate1 _ l1) in Hs.
      all: apply const_list_snoc_eq3 in Hs;auto;[|apply v_to_e_is_const_list..].
      all: destruct Hs as [vs2 [es2 [Heq1 [Heq2 [Heq3 Hconst]]]]].
      all: apply const_es_exists in Hconst as [? ?].
      all: simplify_eq.
      all: destruct x as [|v00 ?]; last by destruct v00 => //; destruct v.
      all: inversion Heq2; subst.
      apply IHvh in H4 as [vh' Hvh'].
      subst es1. eauto.
  Qed.

  Lemma to_val_local_none n f es1 vh :
    iris.to_val0 [AI_frame n f (llfill vh es1)] = None ->
    iris.to_val0 [AI_frame n f es1] = None.
  Proof.
    intros Hv.
    destruct (iris.to_val0 [AI_frame n f es1]) eqn:Hsome;auto.
    exfalso.
    apply to_val_local_inv in Hsome as Heq.
    destruct Heq as [tf [h [w [wh Heq]]]]. subst v.
    assert ([AI_frame n f es1] = llfill (LL_frame [] n f (LL_base [] []) []) es1) as Heq.
    { simpl. rewrite app_nil_r. auto. }
    rewrite Heq in Hsome.
    apply of_to_val0 in Hsome.
    simpl in Hsome. inversion Hsome.
    rewrite app_nil_r in H0. subst es1.
    simplify_eq. pose proof (llfill_nested vh wh [AI_call_host tf h w]) as [vh' Hvh'].
    rewrite Hvh' in Hv.
    assert (iris.of_val0 (callHostV tf h w (LL_frame [] n f vh' [])) =
              [AI_frame n f (llfill vh' [AI_call_host tf h w])]).
    { cbn. auto. }
    assert (iris.to_val0 [AI_frame n f (llfill vh' [AI_call_host tf h w])] =
              Some (callHostV tf h w (LL_frame [] n f vh' []))).
    { rewrite -H0. apply to_of_val0. }
    congruence.
  Qed.

  Lemma to_val_local_none_inv n f es1 vh :
    iris.to_val0 es1 = None ->
    iris.to_val0 [AI_frame n f es1] = None ->
    iris.to_val0 [AI_frame n f (llfill vh es1)] = None.
  Proof.
    intros Hnone Hv.
    destruct (iris.to_val0 [AI_frame n f (llfill vh es1)]) eqn:Hsome;auto.
    exfalso.
    apply to_val_local_inv in Hsome as Heq.
    destruct Heq as [tf [h [w [wh Heq]]]]. subst v.
    assert ([AI_frame n f (llfill vh es1)] = llfill (LL_frame [] n f vh []) es1) as Heq.
    { simpl. auto. }
    rewrite Heq in Hsome.
    apply of_to_val0 in Hsome.
    simpl in Hsome. inversion Hsome.
    apply llfill_call_host_compose in H0 as [vh' Hvh'];auto.
    assert ([AI_frame n f es1] =
              iris.of_val0 (callHostV tf h w (LL_frame [] n f vh' []))).
    { cbn. rewrite Hvh'. auto. }
    
    assert (iris.to_val0 [AI_frame n f es1] = Some (callHostV tf h w (LL_frame [] n f vh' [])));[|congruence].
    rewrite H. apply to_of_val0.
  Qed.

  (* The following lemma will generalise to any local fill *)
  Lemma to_val_local_no_local_none n f e :
    iris.to_val0 [AI_frame n f e] = None ->
    match iris.to_val0 e with
    | Some (callHostV _ _ _ _) => False
    | _ => True
    end.
  Proof.
    intros Hv.
    destruct (iris.to_val0 e) eqn:He;auto.
    destruct v;auto.
    unfold iris.to_val0 in Hv.
    unfold iris.to_val0 in He.
    cbn in *.
    destruct (merge_values (map to_val_instr e)) eqn:Hmerge;try done.
    destruct v;try done.
  Qed.

  Fixpoint ll_of_sh sh :=
    match sh with
    | SH_base bef aft => LL_base bef aft
    | SH_rec bef n es sh aft => LL_label bef n es (ll_of_sh sh) aft
    | SH_prompt bef tf hs sh aft => LL_prompt bef tf hs (ll_of_sh sh) aft
    | SH_handler bef hs sh aft => LL_handler bef hs (ll_of_sh sh) aft
    end.

  Lemma sfill_to_llfill sh e :
    sfill sh e = llfill (ll_of_sh sh) e.
  Proof.
    induction sh;auto.
    all: simpl.
    all: rewrite IHsh.
    all: auto.
  Qed.

  Lemma to_val_local_ret_none n f e vh :
    iris.to_val0 e = Some (retV vh) ->
    iris.to_val0 [AI_frame n f e] = None.
  Proof.
    unfold iris.to_val0. cbn.
    destruct (merge_values (map to_val_instr e)); try done.
    destruct v; done.
  Qed.

  Lemma to_val_local_none_none n f e :
    iris.to_val0 e = None ->
    iris.to_val0 [AI_frame n f e] = None.
  Proof.
    unfold iris.to_val0. cbn.
    destruct (merge_values (map to_val_instr e)); try done.
    destruct e0 => //. 
  Qed.

  Lemma to_eff_local_none_none n f e :
    iris.to_eff0 e = None ->
    iris.to_eff0 [AI_frame n f e] = None.
  Proof.
    unfold iris.to_eff0. cbn.
    destruct (merge_values (map to_val_instr e)); try done.
    destruct v => //. 
  Qed.
  
End wasm_lang_properties.
