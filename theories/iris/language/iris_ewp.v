(* weakest_precondition.v *)

(* This theory introduces a notion of weakest precondition for reasoning about
   [eff_lang] programs. The key idea is to extend a weakest-precondition
   assertion with a pair of protocols to describe the effects that a program
   (fragment) might perform; the first protocol specifies one-shot effects,
   whereas the second one specifies multi-shot effects. *)

From iris.proofmode Require Import base tactics classes.
From iris.program_logic Require Import weakestpre.
From Wasm.iris.language.iris Require Export iris.
From Wasm.iris.language Require Export protocols iris_resources.


Set Bullet Behavior "Strict Subproofs".

(* ========================================================================== *)
(** * Weakest Precondition. *)

(* -------------------------------------------------------------------------- *)
(** Definition. *)

Definition meta_protocol `{!wasmG Σ} : Type :=
  ( (tagidx -d> iProt Σ) *
    (tagidx -d> (iProt Σ * (hholed -d> iPropO Σ))) *
      (tagidx -d> list value -d> iPropO Σ) )%type.

Definition get_suspend `{!wasmG Σ} i (Ψ : meta_protocol) : iProt Σ :=
  let '(Ψ,_,_) := Ψ in Ψ i.
Definition get_switch `{!wasmG Σ} i (Ψ : meta_protocol) :=
  let '(_,Ψ,_) := Ψ in Ψ i.
Definition get_switch1 `{!wasmG Σ} i (Ψ : meta_protocol) :=
  let '(Ψ,_) := get_switch i Ψ in Ψ.
Definition get_switch2 `{!wasmG Σ} i (Ψ : meta_protocol) :=
  let '(_,Ψ) := get_switch i Ψ in Ψ.
Definition get_throw `{!wasmG Σ} i (Ψ : meta_protocol) :=
  let '(_,_,Ψ) := Ψ in Ψ i.

Definition bot_suspend `{!wasmG Σ} : tagidx -d> iProt Σ := 
  λ (_: tagidx), iProt_bottom.
Definition bot_switch `{!wasmG Σ} : tagidx -d> (iProt Σ * (hholed -d> iPropO Σ))%type :=
  λ (_: tagidx), (iProt_bottom, λ (_: hholed), False%I).
Definition bot_throw `{!wasmG Σ} : tagidx -d> list value -d> iPropO Σ :=
  λ (_: tagidx) (_ : list value), False%I.
Definition meta_bottom `{!wasmG Σ}: meta_protocol :=
  ( bot_suspend, bot_switch, bot_throw ).





(*  Inductive effect_identifier : Type :=
| SuspendE : tagidx -> effect_identifier
| SwitchE : tagidx -> effect_identifier
| ThrowE : tagidx -> effect_identifier 
. *)


  

Definition ewp_pre `{!wasmG Σ} :
  (coPset -d> expr -d>
     meta_protocol -d>
     (val -d> iPropO Σ) -d> iPropO Σ) →
  (coPset -d> expr -d> 
     meta_protocol -d>
     (val -d> iPropO Σ) -d> iPropO Σ)
  := λ ewp E e₁ Ψ Φ,
  match to_val e₁ with
  | Some v =>
      |={E}=> Φ v
  | None =>
      match to_eff e₁ with
      | Some (thrE vs i a sh, f) =>
          (* weird that i is unused; not weird for sh that part makes sense actually *) 
          get_throw a Ψ vs
      | Some (susE vs i sh, f) =>
          iProt_car (upcl $ get_suspend i Ψ) vs
            (λ w, ▷ ewp E (susfill i sh (v_to_e_list w), f) Ψ Φ)
      | Some (swE vs k tf (Mk_tagidx i) sh, f) => (* attempt *)
          ∃ cont t1s t2s tf' ts,
          N.of_nat i ↦□[tag] Tf [] ts ∗
          N.of_nat k ↦[wcont] Live tf cont ∗
          ⌜ tf' = Tf (t1s ++ [T_ref (T_contref (Tf t2s ts))]) ts ⌝ ∗
          ⌜ tf = Tf (t1s ++ [T_ref (T_contref tf')]) t2s ⌝ ∗
          get_switch2 (Mk_tagidx i) Ψ (hholed_of_valid_hholed cont) ∗
          iProt_car (upcl $ get_switch1 (Mk_tagidx i) Ψ) vs
                ( λ w, ▷ ewp E (swfill (Mk_tagidx i) sh (v_to_e_list w), f) Ψ Φ)
      | None =>
          ∀ s1,
            state_interp s1 ={E,∅}=∗ 
              ⌜ reducible e₁ s1 ⌝ ∗ 
              ∀ e₂ s2, ⌜ prim_step e₁ s1 [] e₂ s2 [] ⌝ 
                ={∅}▷=∗ |={∅,E}=>
                state_interp s2 ∗ ewp E e₂ Ψ Φ
      end
  end%I.

Local Instance ewp_pre_contractive `{!wasmG Σ} : Contractive ewp_pre.
Proof.
  rewrite /ewp_pre=> n ewp ewp' Hwp E e Ψ Φ.
(*  f_equiv.
  f_equiv.
  { f_equiv. f_equiv. f_equiv.
    intros => ?. f_equiv. f_contractive. apply Hwp. *)
      
  do 5 f_equiv; try by intros => ?; try f_contractive; apply Hwp.
  2:{ do 12 (f_contractive || f_equiv).
      apply Hwp. }
  f_equiv. f_equiv. f_equiv. f_equiv. f_equiv. f_equiv. f_equiv.
  f_equiv. f_equiv. f_equiv. f_equiv. f_equiv. f_equiv. f_equiv.
  f_equiv. f_equiv. 
  intros => ?. f_contractive. apply Hwp. 
Qed.
Definition ewp_def `{!wasmG Σ} :
  coPset -d> expr -d> 
    meta_protocol -d> 
    (val -d> iPropO Σ) -d> iPropO Σ :=
  fixpoint ewp_pre.
Definition ewp_aux `{!wasmG Σ} : seal ewp_def. Proof. by eexists. Qed.
Definition ewp_eq `{!wasmG Σ} := ewp_aux.(seal_eq).
Definition ewp' `{!wasmG Σ} := ewp_aux.(unseal).



(* -------------------------------------------------------------------------- *)
(** Non-expansiveness. *)

Lemma ewp_unfold `{!wasmG Σ} E e Ψ Φ :
  ewp_def E e Ψ Φ ⊣⊢ ewp_pre ewp_def E e Ψ Φ.
Proof. by rewrite /ewp_def; apply (fixpoint_unfold ewp_pre). Qed.


Global Instance ewp_ne `{!wasmG Σ} E e n :
  Proper ((dist n) ==> (dist n) ==> (dist n) ) (ewp_def E e).
Proof.
  revert e.
  induction (lt_wf n) as [n _ IH]=> e Ψ1 Ψ1' HΨ1 Φ Φ' HΦ.
  rewrite !ewp_unfold /ewp_pre /upcl. simpl.
  f_equiv. { f_equiv. f_equiv. }
  f_equiv.
  - f_equiv. f_equiv.
    + do 3 f_equiv. 
      * apply IProt_ne.
        f_equiv.
        inversion HΨ1.
        destruct Ψ1, Ψ1'.
        simpl in H.
        destruct H.
        destruct p, p0.
        simpl.
        simpl in H.
        f_equiv.
      * f_equiv. intros ?. do 2 (f_contractive || f_equiv).
        apply IH.
        done.
        all: eapply dist_le; eauto with lia.
        all: by apply SIdx.lt_le_incl. 
    + destruct (get_switch i Ψ1) eqn:H1.
      destruct (get_switch i Ψ1') eqn:H1'.
      f_equiv. f_equiv. f_equiv. f_equiv. f_equiv. f_equiv.
      f_equiv. f_equiv. f_equiv. f_equiv. f_equiv. f_equiv.
      f_equiv. f_equiv. f_equiv. f_equiv. 
      * inversion HΨ1. destruct Ψ1. destruct Ψ1'.
        inversion H. destruct p, p0.
        simpl in H3. simpl in H1. simpl in H1'.
        unfold get_switch2.
        simpl.
        rewrite H1 H1'.
        assert (o0 ≡{n}≡ o2); last by f_equiv.
        assert ((o, o0) ≡{n}≡ (o1, o2)) as Hres; last by inversion Hres.
        rewrite -H1 -H1'. f_equiv. 
      * f_equiv. intros ?. do 2 (f_contractive || f_equiv).
        -- destruct Ψ1, Ψ1'. destruct p, p0.
           inversion HΨ1. inversion H.
           apply IProt_ne.
           f_equiv.
           simpl in H1, H1', H3.
           rewrite /get_switch1 /= H1 H1'. 
           assert ((o, o0) ≡{n}≡ (o1, o2)) as Hres; last by inversion Hres.
           rewrite -H1 -H1'. f_equiv. 
        -- f_equiv. f_equiv. f_contractive.
           apply IH; try done; eapply dist_le; eauto; try by apply SIdx.lt_le_incl.
    + destruct Ψ1, Ψ1'. inversion HΨ1. destruct p, p0. simpl.
      simpl in H0. f_equiv. 
  - do 5 f_equiv. do 10 (f_contractive || f_equiv).
    apply IH; try done; eapply dist_le; eauto; try by apply SIdx.lt_le_incl.
Qed.

Global Instance ewp_proper `{!wasmG Σ} E e:
  Proper ((≡) ==> (≡) ==> (≡)) (ewp_def E e).
Proof.
  intros Ψ1 Ψ1' ? Φ Φ' ?.
  by apply equiv_dist=>n; apply ewp_ne; apply equiv_dist.
Qed.


(* -------------------------------------------------------------------------- *)
(** Notation. *)

Notation "'EWP' e 'UNDER' f @ E {{ Φ } }" :=
  (ewp_def E (e, f)%E meta_bottom (λ '(v, h), Φ v h))
  (at level 20, e, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' 'UNDER'  f  @  E  {{  Φ  } } ']' ']'") : bi_scope.
Notation "'EWP' e 'UNDER' f @ E <| Ψ |> {{ Φ } }" :=
  (ewp_def E (e, f)%E Ψ (λ '(v, h), Φ v h))
  (at level 20, e, Ψ, Φ at level 200,
    format "'[' 'EWP'  e  '/' '[          ' 'UNDER'  f  @  E  <|  Ψ  |>  {{  Φ  } } ']' ']'") : bi_scope. 


(* Postcondition includes binder. *)

Notation "'EWP' e 'UNDER' f @ E {{ v ; h , Φ } }" :=
  (ewp_def E (e, f)%E meta_bottom (λ '(v,h), Φ))
  (at level 20, e, v, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' 'UNDER'  f  @  E  {{  v  ; h  , Φ  } } ']' ']'") : bi_scope.
 Notation "'EWP' e 'UNDER' f @ E <| Ψ |> {{ v ; h , Φ } }" :=
  (ewp_def E (e, f)%E Ψ (λ '(v, h), Φ))
  (at level 20, e, v, Ψ, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' 'UNDER'  f  @  E  <| Ψ |>  {{  v ; h , Φ   } } ']' ']'") : bi_scope. 

(* Mask is implicitly specified by ⊤. *)

Notation "'EWP' e 'UNDER' f {{ v ; h , Φ } }" :=
  (ewp_def ⊤ (e, f)%E meta_bottom (λ '(v, h), Φ))
  (at level 20, e, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' 'UNDER'  f  {{ v ; h , Φ   } } ']' ']'") : bi_scope.
 Notation "'EWP' e 'UNDER' f <| Ψ |> {{ v ; h , Φ } }" :=
  (ewp_def ⊤ (e, f)%E Ψ (λ '(v, h), Φ))
  (at level 20, e, Ψ, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          '  'UNDER'  f  <|  Ψ  |>  {{  v ; h , Φ  } } ']' ']'") : bi_scope. 

(* No binder and no mask. *)

Notation "'EWP' e 'UNDER' f {{ Φ } }" :=
  (ewp_def ⊤ (e, f)%E meta_bottom (λ '(v, h), Φ v h))
  (at level 20, e at level 200,
   format "'[' 'EWP'  e  '/' '[          '  'UNDER'  f  {{  Φ  } } ']' ']'") : bi_scope.
 Notation "'EWP' e 'UNDER' f <| Ψ |> {{ Φ } }" :=
  (ewp_def ⊤ (e, f)%E Ψ (λ '(v, h), Φ v h))
  (at level 20, e, Ψ at level 200,
   format "'[' 'EWP'  e  '/' '[          '  'UNDER'  f  <|  Ψ  |>  {{  Φ } } ']' ']'") : bi_scope. 

(* Tests *)
(* Check (λ Σ es P Q, EWP es <| λ _, iProt_bottom |> {{ λ v, True }})%I.
 Check (λ Σ es P Q, EWP es <| λ i w, λne Φ, ⌜ i = SuspendE (Mk_tagidx 1) ⌝ ∗ ((>> v >> ! v {{ P }} ; << w << ? w {{ Q }})%iprot w Φ) |> {{ λ v, True }})%I. *)


Section wp.
  Context `{!wasmG Σ}.

  Lemma ewp_value_fupd' (E : coPset) (f: frame) (Ψ : meta_protocol) Φ (v: val0) :
    EWP of_val0 v UNDER f @ E <| Ψ |> {{ Φ }} ⊣⊢ |={E}=> Φ v f .
  Proof. rewrite ewp_unfold /ewp_pre. rewrite /to_val /= to_of_val0. auto. Qed.

  Lemma ewp_effect_sus' E f Ψ Φ vs i sh : EWP of_eff0 (susE vs i sh) UNDER f @ E <| Ψ |> {{ Φ }} ⊣⊢ iProt_car (upcl $ get_suspend i Ψ) vs (λ w, ▷ EWP susfill i sh (v_to_e_list w) UNDER f @ E <| Ψ |> {{ Φ }}).
  Proof.
    rewrite ewp_unfold /ewp_pre. rewrite /to_eff /to_val to_of_eff0.
    destruct (to_val0 _) eqn:Habs => //.
    exfalso; eapply to_val_to_eff => //.
    rewrite to_of_eff0 //.
  Qed.

  Lemma ewp_effect_sw' E f Ψ Φ vs k tf i sh : EWP of_eff0 (swE vs k tf (Mk_tagidx i) sh) UNDER f @ E <| Ψ |> {{ Φ }} ⊣⊢ 
  ∃ cont t1s t2s tf' ts,
  N.of_nat i ↦□[tag] Tf [] ts ∗                                                
  N.of_nat k ↦[wcont] Live tf cont ∗
    ⌜ tf' = Tf (t1s ++ [T_ref (T_contref (Tf t2s ts))]) ts ⌝ ∗
    ⌜ tf = Tf (t1s ++ [T_ref (T_contref tf')]) t2s ⌝ ∗
              get_switch2 (Mk_tagidx i) Ψ (hholed_of_valid_hholed cont) ∗ 
              iProt_car (upcl $ get_switch1 (Mk_tagidx i) Ψ) vs
              ( λ w, ▷ EWP swfill (Mk_tagidx i) sh (v_to_e_list w) UNDER f @ E <| Ψ |> {{ Φ }}).
  Proof.
    rewrite ewp_unfold /ewp_pre. rewrite /to_val /to_eff to_of_eff0.
    destruct (to_val0 _) eqn:Habs => //.
    exfalso; eapply to_val_to_eff => //.
    rewrite to_of_eff0 //.
  Qed.


   Lemma ewp_effect_thr' E f Ψ  Φ vs i a sh : EWP of_eff0 (thrE vs i a sh) UNDER f @ E <| Ψ |> {{ Φ }} ⊣⊢  get_throw a Ψ vs.
  Proof.
    rewrite ewp_unfold /ewp_pre. rewrite /to_eff to_of_eff0 /to_val.
    destruct (to_val0 _) eqn:Habs => //.
    exfalso; eapply to_val_to_eff => //.
    rewrite to_of_eff0 //.
  Qed.


  Definition meta_leq (Ψ1 Ψ2: meta_protocol) : iProp Σ :=
    ((∀ i, get_suspend i Ψ1 ⊑ get_suspend i Ψ2)%iprot ∗
       (∀ i, get_switch1 i Ψ1 ⊑ get_switch1 i Ψ2)%iprot ∗
       □ (∀ i c, get_switch2 i Ψ1 c -∗ get_switch2 i Ψ2 c) ∗
       □ (∀ i v, get_throw i Ψ1 v -∗ get_throw i Ψ2 v))%I.

  Lemma meta_leq_refl Ψ : ⊢ meta_leq Ψ Ψ.
  Proof.
    destruct Ψ as [[??]?].
    iSplit; first by iIntros (?); iApply iProt_le_refl.
    iSplit; first by iIntros (?); iApply iProt_le_refl.
    iSplit; first by iIntros "!>" (??) "?".
    by iIntros "!>" (??) "?".
  Qed. 
  

  Lemma ewp_strong_mono E1 E2 e f Φ1 Φ2 Ψ1 Ψ2  :
    E1 ⊆ E2 →
    EWP e UNDER f @ E1 <| Ψ1 |> {{ Φ1 }} -∗
            meta_leq Ψ1 Ψ2 -∗
            (∀ v f, Φ1 v f ={E2}=∗ Φ2 v f) -∗
            EWP e UNDER f @ E2 <| Ψ2 |> {{ Φ2 }}.
  Proof.
    iIntros (HE) "H #HΨ HΦ".
    iLöb as "IH" forall (e f E1 E2 HE Φ1 Φ2).
    rewrite !ewp_unfold /ewp_pre /=.
    destruct (to_val0 e) as [v|] eqn:?.
    { iMod (fupd_mask_mono E1 E2 with "H") as "H".
      done.
      iFrame.
      iApply ("HΦ" with "[> -]").
      done. }
    destruct (to_eff0 e) as [eff|] eqn:?.
    { destruct eff.
      all: destruct i.
      - iDestruct "H" as (Φ) "[HΦ1 H]".
        iDestruct "HΨ" as "[HΨ Hrest]".
        iExists Φ.
        iSplitL "HΦ1".
        iApply ("HΨ" with "HΦ1").
        iIntros (w) "Hw".
        iDestruct ("H" with "Hw") as "H".
        iNext.
        iApply ("IH" with "[] H [$]"); eauto.
      - iDestruct "HΨ" as "(Hrest1 & HΨ1 & HΨ2 & Hrest2)".
        iDestruct "H" as (cont t1s t2s tf' ts) "(#Htag & Hk & -> & -> & Hcont0 & %Φ & HΦ1 & H)".
        iFrame.
        iExists _,_,_,_.
        do 3 (iSplit; first done).
        iSplitL "Hcont0"; first by iApply "HΨ2".
        iExists Φ.
        iSplitL "HΦ1"; first by iApply "HΨ1".
        iIntros (w) "Hw".
        iDestruct ("H" with "Hw") as "H".
        iNext.
        iApply ("IH" with "[] H [$]"); eauto. 
      - iDestruct "HΨ" as "(Hrest1 & Hrest2 & Hrest3 & HΨ)".
        by iApply "HΨ". 
    } 
    iIntros (σ1) "Hσ".
    iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
    iDestruct ("H" $! σ1) as "H".
    iMod ("H" with "[$]") as "[% H]".
    iModIntro. iSplit; [done|].
    iIntros (e2 ? Hstep).
    iMod ("H" with "[//]") as "H". iIntros "!> !>".  iMod "H". iModIntro.
    iMod "H" as "[Hσ H]".
    iMod "Hclose".
    iModIntro.
    iFrame.
    destruct e2.
    iApply ("IH" with "[] H"); eauto.
  Qed. 

  Lemma fupd_ewp E e f Ψ  Φ :
    TCEq (to_eff0 e) None ->
    (|={E}=> EWP e UNDER f @ E <| Ψ |>  {{ Φ }}) ⊢ EWP e UNDER f @ E <| Ψ |> {{ Φ }}.
  Proof.
    rewrite ewp_unfold /ewp_pre. iIntros (He) "H".
    simpl.
    destruct (to_val0 e) as [v|] eqn:?.
    { by iMod "H". }
    destruct (to_eff0 e) as [eff|] eqn:?.
    { inversion He. } 
    iIntros (σ1) "Hσ1". iMod "H". by iApply "H".
  Qed. 
  
  Lemma ewp_fupd E e f Ψ Φ : EWP e UNDER f @ E <| Ψ |> {{ v ; h , |={E}=> Φ v h }} ⊢ EWP e UNDER f @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros "H". iApply (ewp_strong_mono E with "H"); auto.
    iApply meta_leq_refl. 
  Qed. 


  (* Is this true anymore? *)
  (*
  Lemma ewp_atomic E1 E2 e Ψ Φ a `{!Atomic (stuckness_to_atomicity NotStuck) e} :
    (|={E1,E2}=> EWP e UNDER f @ E2 <| Ψ |> {{ v, |={E2,E1}=> Φ v ∗ Pred a }}) ⊢ EWP e UNDER f @ E1 <| Ψ |> {{ v, Φ v ∗ Pred a }}.
  Proof.
    iIntros "H". rewrite !ewp_unfold /ewp_pre.
    destruct (to_val e) as [v|] eqn:He.
    { by iDestruct "H" as ">>>$". }
    destruct (to_eff e) as [eff|] eqn:Hf.
    { destruct eff.
      - 
    iIntros (σ1) "Hσ". iMod "H". iMod ("H" $! σ1 with "Hσ") as "[$ H]".
    iModIntro. iIntros (e2 σ2 efs Hstep).
    iApply (step_fupdN_wand with "[H]"); first by iApply "H".
    iIntros ">[Hσ H]". iDestruct "H" as (a') "(H' & H & Hefs)". destruct s.
    - rewrite !wp_unfold /wp_pre. destruct (to_val e2) as [v2|] eqn:He2.
      + iDestruct ("H" with "H'") as ">>[? ?]". iFrame.
        iModIntro. (* iExists _. iFrame. *) iIntros "?".
        iApply wp_unfold. rewrite /wp_pre /= He2. by iFrame.
      + iDestruct ("H" with "H'") as "H".
        iMod ("H" $! _ _ [] with "[$]") as "[H _]". iDestruct "H" as %(? & ? & ? & ? & ?).
        by edestruct (atomic _ _ _ _ _ Hstep).
    - destruct (atomic _ _ _ _ _ Hstep) as [v <-%of_to_val].
      rewrite wp_value_fupd'. iMod ("H" with "[$]") as ">[H H']".
      iModIntro. iFrame "Hσ Hefs". iExists _. iFrame. iIntros "?". iApply wp_value_fupd'. by iFrame.
  Qed. *)

  (** In this stronger version of [wp_step_fupdN], the masks in the
      step-taking fancy update are a bit weird and somewhat difficult to
      use in practice. Hence, we prove it for the sake of completeness,
      but [wp_step_fupdN] is just a little bit weaker, suffices in
      practice and is easier to use.

   See the statement of [wp_step_fupdN] below to understand the use of
   ordinary conjunction here. *)
  Lemma ewp_step_fupdN_strong n f E1 E2 e P Ψ Φ :
    TCEq (to_val0 e) None → TCEq (to_eff0 e) None -> E2 ⊆ E1 →
    (∀ σ, state_interp σ
                   ={E1,∅}=∗ ⌜n ≤ 1⌝) ∧
      ((|={E1,E2}=> |={∅}▷=>^n |={E2,E1}=> P) ∗
         EWP e UNDER f @ E2 <| Ψ |> {{ v ; h , P ={E1}=∗ Φ v h }}) -∗
            EWP e UNDER f @ E1 <| Ψ |>  {{ Φ }}.
  Proof.
    destruct n as [|n].
    { iIntros (? ? ?) "/= [_ [HP Hwp]]".
      iApply (ewp_strong_mono with "Hwp") => //.
      iApply meta_leq_refl. 
      iIntros (v ?) "H". iApply ("H" with "[>HP]"). by do 2 iMod "HP". }
    rewrite !ewp_unfold /ewp_pre /=. iIntros (-> -> ?) "H".
    iIntros (σ1) "Hσ".
    destruct (decide (n ≤ 0)) as [Hn|Hn]; first last.
    { iDestruct "H" as "[Hn _]".
      iDestruct ("Hn" $! σ1) as "Hn".
      iMod ("Hn" with "Hσ") as %?. lia. }
    iDestruct "H" as "[_ [>HP Hwp]]".
    iDestruct ("Hwp" $! σ1) as "Hwp".
    iMod ("Hwp" with "[$]") as "[$ H]".
    iMod "HP".
    iIntros "!>" (e2 s2 Hstep). iMod ("H" $! e2 s2 with "[% //]") as "H".
    iIntros "!>!>". iMod "H". iMod "HP". iModIntro.
    destruct n; last lia.
    simpl.
    iMod "H" as "[H Hwp]".
    iMod "HP".
    iModIntro.
    iFrame.
    destruct e2.
    iApply (ewp_strong_mono with "Hwp"); [done | iApply meta_leq_refl | ].
    iIntros (v ?) "HΦ". iApply ("HΦ" with "HP").
  Qed. 


  (** * Derived rules *)
  Lemma ewp_mono E e f Φ1 Φ2 Ψ1 Ψ2 : (∀ v f, Φ1 v f ⊢ Φ2 v f) → (⊢ meta_leq Ψ1 Ψ2) -> EWP e UNDER f @ E <| Ψ1 |> {{ Φ1 }} ⊢ EWP e UNDER f @ E <| Ψ2 |> {{ Φ2 }}.
  Proof.
    iIntros (HΦ HΨ) "H"; iApply (ewp_strong_mono with "H"); auto.
    iIntros (v ?) "?". iFrame. by iApply HΦ.
  Qed. 

   Lemma ewp_mono_post E e f Φ1 Φ2 Ψ : (∀ v f, Φ1 v f ⊢ Φ2 v f) → EWP e UNDER f @ E <| Ψ |> {{ Φ1 }} ⊢ EWP e UNDER f @ E <| Ψ |> {{ Φ2 }}.
   Proof.
     iIntros (HΦ) "H"; iApply (ewp_strong_mono with "H"); auto.
     iApply meta_leq_refl. 
    iIntros (v ?) "?". iFrame. by iApply HΦ.
  Qed. 

   Lemma ewp_mono_prot E e f Φ Ψ1 Ψ2 : (⊢ meta_leq Ψ1 Ψ2) -> EWP e UNDER f @ E <| Ψ1 |> {{ Φ }} ⊢ EWP e UNDER f @ E <| Ψ2 |> {{ Φ }}.
  Proof.
    iIntros (HΨ) "H"; iApply (ewp_strong_mono with "H"); auto.
  Qed.  
  
  Lemma ewp_mask_mono E1 E2 e f Ψ  Φ : E1 ⊆ E2 → EWP e UNDER f @ E1 <| Ψ |> {{ Φ }} ⊢ EWP e UNDER f @ E2 <| Ψ |> {{ Φ }}.
  Proof. iIntros (?) "H"; iApply (ewp_strong_mono with "H"); auto.
         iApply meta_leq_refl. 
  Qed.

(*
  Global Instance ewp_mono' E e :
    Proper (pointwise_relation _ (⊢) ==> (⊢)) (ewp_def E e).
  Proof. by intros Φ Φ' ?; apply wp_mono. Qed.
  Global Instance wp_flip_mono' s E e :
    Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (wp (PROP:=iProp Σ) s E e).
  Proof. by intros Φ Φ' ?; apply wp_mono. Qed. *)

  Lemma ewp_value_fupd E f Ψ  Φ e v : to_val0 e = Some v → EWP e UNDER f @ E <| Ψ |> {{ Φ }} ⊣⊢ |={E}=> Φ v f .
  Proof. intros H. apply of_to_val0 in H as <-. by apply ewp_value_fupd'. Qed.
  Lemma ewp_value' E f Ψ Φ v : Φ v f ⊢ EWP (of_val0 v) UNDER f @ E <| Ψ |> {{ Φ }}.
  Proof. rewrite ewp_value_fupd'. auto. Qed.
  Lemma ewp_value E f Ψ Φ e v : to_val0 e = Some v → Φ v f ⊢ EWP e UNDER f @ E <| Ψ |> {{ Φ }}.
  Proof. intros H. apply of_to_val0 in H as <-. apply ewp_value'. Qed.

  Lemma ewp_effect_sus E f Ψ Φ vs i sh es:
    to_eff0 es = Some (susE vs i sh) ->
    EWP es UNDER f @ E <| Ψ |> {{ Φ }} ⊣⊢ iProt_car (upcl $ get_suspend i Ψ) vs (λ w, ▷ EWP (susfill i sh (v_to_e_list w)) UNDER f @ E <| Ψ |> {{ Φ }}).
  Proof.
    intros. apply of_to_eff0 in H. subst. by apply ewp_effect_sus'.
  Qed.

  
  Lemma ewp_effect_sw E f Ψ Φ vs k tf i sh es:
    to_eff0 es = Some (swE vs k tf (Mk_tagidx i) sh) ->
    EWP es UNDER f @ E <| Ψ |> {{ Φ }} ⊣⊢  
      ∃ cont t1s t2s tf' ts,
        N.of_nat i ↦□[tag] Tf [] ts ∗
  N.of_nat k ↦[wcont] Live tf cont ∗
    ⌜ tf' = Tf (t1s ++ [T_ref (T_contref (Tf t2s ts))]) ts ⌝ ∗
    ⌜ tf = Tf (t1s ++ [T_ref (T_contref tf')]) t2s ⌝ ∗
              get_switch2 (Mk_tagidx i) Ψ (hholed_of_valid_hholed cont) ∗ 
              iProt_car (upcl $ get_switch1 (Mk_tagidx i) Ψ) vs
              ( λ w, ▷ EWP swfill (Mk_tagidx i) sh (v_to_e_list w) UNDER f @ E <| Ψ |> {{ Φ }} ).
  Proof.
    intros. apply of_to_eff0 in H. subst. by apply ewp_effect_sw'.
  Qed.

  Lemma ewp_effect_thr E f Ψ Φ vs i a sh es:
    to_eff0 es = Some (thrE vs i a sh) ->
    EWP es UNDER f @ E <| Ψ |> {{ Φ }} ⊣⊢  get_throw a Ψ vs.
  Proof.
    intros. apply of_to_eff0 in H. subst. by apply ewp_effect_thr'.
  Qed. 

  Lemma ewp_frame_l E e f Ψ Φ R : R ∗ EWP e UNDER f @ E <| Ψ |> {{ Φ }} ⊢ EWP e UNDER f @ E <| Ψ |> {{ v ; h , R ∗ Φ v h }}.
  Proof. iIntros "[? H]". iApply (ewp_strong_mono with "H"); auto with iFrame.
         iApply meta_leq_refl. 
  Qed.
  Lemma ewp_frame_r E e f Ψ  Φ R : EWP e UNDER f @ E <| Ψ |> {{ Φ }} ∗ R ⊢ EWP e UNDER f @ E <| Ψ |> {{ v ; h , Φ v h ∗ R }}.
  Proof. iIntros "[H ?]". iApply (ewp_strong_mono with "H"); auto with iFrame.
         iApply meta_leq_refl. 
  Qed.

  (** This lemma states that if we can prove that [n] laters are used in
      the current physical step, then one can perform an n-steps fancy
      update during that physical step. The resources needed to prove the
      bound on [n] are not used up: they can be reused in the proof of
      the WP or in the proof of the n-steps fancy update. In order to
      describe this unusual resource flow, we use ordinary conjunction as
      a premise. *)
  Lemma ewp_step_fupdN n E1 E2 e f P Ψ Φ :
    TCEq (to_val0 e) None → TCEq (to_eff0 e) None -> E2 ⊆ E1 →
    (∀ σ, state_interp σ
          ={E1,∅}=∗ ⌜n ≤ 1 ⌝) ∧
      ((|={E1∖E2,∅}=> |={∅}▷=>^n |={∅,E1∖E2}=> P) ∗
      EWP e UNDER f @ E2 <| Ψ |> {{ v ; h , P ={E1}=∗ Φ v h }}) -∗
                                                    EWP e UNDER f @ E1 <| Ψ |> {{ Φ }}.
  Proof.
    iIntros (???) "H". iApply (ewp_step_fupdN_strong with "[H]"); [done|].
    iApply (bi.and_mono_r with "H"). apply bi.sep_mono_l. iIntros "HP".
    iMod fupd_mask_subseteq_emptyset_difference as "H"; [|iMod "HP"]; [set_solver|].
    iMod "H" as "_". replace (E1 ∖ (E1 ∖ E2)) with E2; last first.
    { set_unfold=>x. destruct (decide (x ∈ E2)); naive_solver. }
    iModIntro. iApply (step_fupdN_wand with "HP"). iIntros "H".
    iApply fupd_mask_frame; [|iMod "H"; iModIntro]; [set_solver|].
    by rewrite difference_empty_L (comm_L (∪)) -union_difference_L.
  Qed.
  Lemma ewp_step_fupd E1 E2 e f P Ψ Φ :
    TCEq (to_val0 e) None → TCEq (to_eff0 e) None -> E2 ⊆ E1 →
    (|={E1}[E2]▷=> P) -∗ EWP e UNDER f @ E2 <| Ψ |> {{ v ; h , P ={E1}=∗ Φ v h }} -∗ EWP e UNDER f @ E1 <| Ψ |> {{ Φ }}.
  Proof.
    iIntros (???) "HR H".
    iApply (ewp_step_fupdN_strong 1 f E1 E2 with "[-]") => //. iSplit.
    - iIntros (?) "_". iMod (fupd_mask_subseteq ∅) as "_"; [set_solver+|].
      auto with lia.
    - iFrame "H". iMod "HR" as "$". auto.
  Qed.

  Lemma ewp_frame_step_l E1 E2 e f Ψ  Φ R :
    TCEq (to_val0 e) None → TCEq (to_eff0 e) None -> E2 ⊆ E1 →
    (|={E1}[E2]▷=> R) ∗ EWP e UNDER f @ E2 <| Ψ |> {{ Φ }} ⊢ EWP e UNDER f @ E1 <| Ψ |> {{ v ; h , R ∗ Φ v h }}.
  Proof.
    iIntros (???) "[Hu Hwp]". iApply (ewp_step_fupd with "Hu"); try done.
    iApply (ewp_mono_post with "Hwp"). by iIntros (??) "$$".
  Qed.
  Lemma ewp_frame_step_r E1 E2 e f Ψ  Φ R :
    TCEq (to_val0 e) None → TCEq (to_eff0 e) None -> E2 ⊆ E1 →
    EWP e UNDER f @ E2 <| Ψ |> {{ Φ }} ∗ (|={E1}[E2]▷=> R) ⊢ EWP e UNDER f @ E1 <| Ψ |> {{ v ; h , Φ v h ∗ R }}.
  Proof.
    iIntros (???) "[Hwp Hu]". iApply (ewp_step_fupd with "Hu"); try done.
    iApply (ewp_mono_post with "Hwp"). by iIntros (??) "$$".
  Qed.
  Lemma ewp_frame_step_l' E e f Ψ  Φ R :
    TCEq (to_val0 e) None → TCEq (to_eff0 e) None ->  ▷ R ∗ EWP e UNDER f @ E <| Ψ |> {{ Φ }} ⊢ EWP e UNDER f @ E <| Ψ |> {{ v ; h , R ∗ Φ v h }}.
  Proof. iIntros (??) "[??]". iApply (ewp_frame_step_l E E); try iFrame; eauto. Qed.
  Lemma ewp_frame_step_r' E e f Ψ  Φ R :
    TCEq (to_val0 e) None → TCEq (to_eff0 e) None -> EWP e UNDER f @ E <| Ψ |> {{ Φ }} ∗ ▷ R ⊢ EWP e UNDER f @ E <| Ψ |> {{ v ; h , Φ v h ∗ R }}.
  Proof. iIntros (??) "[??]". iApply (ewp_frame_step_r E E); try iFrame; eauto. Qed.

  Lemma ewp_wand E e f P Φ Ψ :
    EWP e UNDER f @ E <| P |> {{ Φ }} -∗ (∀ v f, Φ v f -∗ Ψ v f) -∗ EWP e UNDER f @ E <| P |>  {{ Ψ }}.
  Proof.
    iIntros "Hwp H". iApply (ewp_strong_mono with "Hwp"); auto.
    iApply meta_leq_refl. 
    iIntros (??) "?". by iApply "H".
  Qed.
  Lemma ewp_wand_l E e f P Φ Ψ :
    (∀ v f, Φ v f -∗ Ψ v f) ∗ EWP e UNDER f @ E <| P |>  {{ Φ }} ⊢ EWP e UNDER f @ E <| P |> {{ Ψ }}.
  Proof. iIntros "[H Hwp]". iApply (ewp_wand with "Hwp"). done. Qed.
  Lemma ewp_wand_r E e f P Φ Ψ :
    EWP e UNDER f @ E <| P |> {{ Φ }} ∗ (∀ v f, Φ v f -∗ Ψ v f) ⊢ EWP e UNDER f @ E <| P |> {{ Ψ }}.
  Proof. iIntros "[Hwp H]". by iApply (ewp_wand with "Hwp H"). Qed.
  Lemma ewp_frame_wand E e f Ψ Φ R :
    R -∗ EWP e UNDER f @ E <| Ψ |> {{ v ; h , R -∗ Φ v h }} -∗ EWP e UNDER f @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros "HR HWP". iApply (ewp_wand with "HWP").
    iIntros (v ?) "HΦ". iFrame. by iApply "HΦ".
  Qed.

  (* Some lifting lemmas restated and reproved *)
  Local Hint Resolve reducible_no_obs_reducible : core.

     Lemma ewp_lift_step_fupdN E Ψ Φ e1 f1 :
    to_val0 e1 = None → to_eff0 e1 = None ->
    (∀ σ1, state_interp σ1 ={E,∅}=∗
    ⌜reducible ((e1, f1): expr) σ1 ⌝ ∗
    ∀ e2 f2 s2, ⌜prim_step (e1, f1) σ1 [] (e2, f2) s2 [] ⌝
      ={∅}▷=∗ |={∅,E}=>
      state_interp s2 ∗ EWP e2 UNDER f2 @ E <| Ψ |> {{ Φ }})
      ⊢ EWP e1 UNDER f1 @ E <| Ψ |> {{ Φ }}.
   Proof.
     rewrite ewp_unfold /ewp_pre /= => -> ->.
     iIntros "H".
     iIntros (σ) "Hs".
     iMod ("H" with "Hs") as "[%H H]".
     iModIntro.
     iSplit; first done.
     iIntros ([??] ? ?).
     iApply "H".
     done.
   Qed. 
(*     iIntros "H" (σ1) "Hσ".
     iMod ("H" with "Hσ") as "(Hred & H)".
     iFrame.
     done.
     iIntros "!>" (e2 σ2 Hred).
     iSpecialize ("H" $! e2 σ2 Hred).
     iApply (step_fupdN_mono with "H").
     iIntros "H".
     iMod "H" as "[Hσ H]".
     iModIntro. iFrame.
     iDestruct "H" as (a) "[Ha H]".
     iApply ("H" with "Ha").
   Qed. *)

   Lemma ewp_lift_step_fupd E f Ψ Φ e1 :
  to_val0 e1 = None → to_eff0 e1 = None ->
  (∀ σ1, state_interp σ1 ={E,∅}=∗
    ⌜reducible ((e1, f): expr) σ1 ⌝ ∗
    ∀ e2 f2 s2, ⌜prim_step (e1, f) σ1 [] (e2, f2) s2 [] ⌝ ={∅}=∗ ▷ |={∅,E}=>
      state_interp s2 ∗ EWP e2 UNDER f2 @ E <| Ψ |> {{ Φ }})
    ⊢ EWP e1 UNDER f @ E <| Ψ |> {{ Φ }}.
  Proof.
    intros ? ?. rewrite -ewp_lift_step_fupdN => //. simpl.
    do 14 f_equiv.
    iIntros "H !>". iMod "H". iModIntro. iFrame.
  Qed.


  (** Derived lifting lemmas. *)
  Lemma ewp_lift_step E f Ψ  Φ e1 :
    to_val0 e1 = None → to_eff0 e1 = None ->
    (∀ σ1, state_interp σ1 ={E,∅}=∗
    ⌜reducible ((e1, f): expr) σ1 ⌝ ∗
    ▷ ∀ e2 f2 s2, ⌜prim_step (e1, f) σ1 [] (e2, f2) s2 []⌝ ={∅,E}=∗
      state_interp s2 ∗ EWP e2 UNDER f2 @ E <| Ψ |> {{ Φ }})
      ⊢ EWP e1 UNDER f @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros (??) "H". iApply ewp_lift_step_fupd => //. iIntros (?) "Hσ".
    iMod ("H" with "Hσ") as "[$ H]". iIntros "!> * % !> !>". by iApply "H".
  Qed.

  Lemma ewp_lift_pure_step_no_fork E E' Ψ Φ e1 a :
    (∀ f1 σ1, reducible ((e1, f1): expr) σ1) →
    (∀ κ σ1 e2 σ2 f1 f2, prim_step (e1, f1) σ1 κ (e2, f2) σ2 [] → κ = [] ∧ σ2 = σ1 /\ f2 = f1) →
    (|={E}[E']▷=> ∀ κ e2 σ f, ⌜prim_step (e1, f) σ κ (e2, f) σ []⌝ → (EWP e2 UNDER a @ E <| Ψ |> {{ Φ }}))
      ⊢ EWP e1 UNDER a @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros (Hsafe Hstep) "H". iApply ewp_lift_step.
    { specialize (Hsafe (Build_frame [] (Build_instance [] [] [] [] [] [])) (Build_store_record [] [] [] [] [] [] [])).
      apply reducible_not_val in Hsafe.
      simpl in Hsafe.
      destruct (to_val0 e1) => //. } 
    { destruct (to_eff0 e1) eqn:? => //.
      destruct e.
      1, 3: specialize (Hsafe (Build_frame [] (Build_instance [] [] [] [] [] [])) (Build_store_record [] [] [] [] [] [] [])).
      1-2: destruct Hsafe as (? & [??] & ? & ? & ? & _).
       1-2: apply eff_head_stuck_reduce in H as [Habs | (? & ? & ? & ? & ? & ? & ? & Habs & _)]; by rewrite Habs in Heqo.
      specialize (Hsafe empty_frame (Build_store_record [] [] [] [] [] [] (repeat (Cont_hh (Tf [] []) (HH_base [] [])) (S k)))). 
      destruct Hsafe as (? & ? & ? & ? & ?).
      unfold language.prim_step in H. 
      destruct x0.
      destruct H as [H _].
      apply eff_head_stuck_reduce in H as [Habs | (? & ? & ? & ? & ? & ? & ? & Habs & Habs' & _)]; rewrite Habs in Heqo => //.
      inversion Heqo; subst.
      rewrite nth_error_repeat in Habs'; last lia.
      done. }

    iIntros (σ1) "Hσ". iMod "H".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iSplit.
    { iPureIntro. done. }
    iNext. iIntros (e2 ? ? ?).
    destruct (Hstep [] σ1 e2 s2 a f2) as (_ & Hσ); auto.
    inversion Hσ; subst.
    iMod (state_interp_mono with "Hσ") as "$".
    iMod "Hclose" as "_". iMod "H". iModIntro.
    destruct a.
    iDestruct ("H" with "[//]") as "$". 
  Qed.


  (* Atomic steps don't need any mask-changing business here, one can
     use the generic lemmas here. *)
    Lemma ewp_lift_atomic_step_fupd {E1 E2 Ψ Φ} e1 a:
    to_val0 e1 = None → to_eff0 e1 = None ->
    (∀ σ1, state_interp σ1 ={E1}=∗
    ⌜ reducible ((e1, a): expr) σ1 ⌝ ∗
    ∀ e2 s2 f2, ⌜prim_step (e1, a) σ1 [] (e2, f2) s2 []⌝ ={E1}[E2]▷=∗
      state_interp s2  ∗
      match to_val0 e2 with
      | None => False
      | Some v => Φ v f2 
      end )
      ⊢ EWP e1 UNDER a @ E1 <| Ψ |> {{ v ; f , Φ v f }}.
  Proof.
    iIntros (??) "H".
    iApply (ewp_lift_step_fupd E1 _ _ _ e1)=> //; iIntros (σ1) "Hσ1".
    iMod ("H" $! σ1 with "Hσ1") as "[$ H]".
    iApply fupd_mask_intro; first set_solver.
    iIntros "Hclose" (e2 ?? ?). iMod "Hclose" as "_".
    iMod ("H" $! e2 s2 with "[#]") as "H"; [done|].
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose !>".
    iMod "Hclose" as "_". iMod "H" as "($ & HQ)".
    destruct (to_val0 e2) eqn:?; last by iExFalso.
    iApply fupd_mask_intro;[auto|].
    iIntros "Hcls". 
    iApply ewp_value ;[|iFrame]. done. 
  Qed.

  Lemma ewp_lift_atomic_step {E Ψ Φ} e1 a:
    to_val0 e1 = None → to_eff0 e1 = None ->
    (∀ σ1, state_interp σ1 ={E}=∗
    ⌜reducible ((e1, a): expr) σ1 ⌝ ∗
    ▷ ∀ e2 s2 f2, ⌜prim_step (e1, a) σ1 [] (e2, f2) s2 []⌝ ={E}=∗
      state_interp s2 ∗
      match to_val0 e2 with
      | None => False
      | Some v => Φ v f2 end )
      ⊢ EWP e1 UNDER a @ E <| Ψ |> {{ v ; f, Φ v f }}.
  Proof.
    iIntros (??) "H". iApply ewp_lift_atomic_step_fupd. done. done.
    iIntros (?) "?". iMod ("H" with "[$]") as "[$ H]".
    iIntros "!> *". iIntros (Hstep) "!> !>".
    by iApply "H".
  Qed.


  Lemma ewp_lift_pure_det_step_no_fork {E E' Ψ Φ} e1 e2 a :
    (∀ σ1 f1, reducible ((e1, f1): expr) σ1 ) →
    (∀ σ1 κ e2' σ2 f1 f2, prim_step (e1, f1) σ1 κ (e2', f2) σ2 []  →
                    κ = [] ∧ σ2 = σ1 ∧ f2 = f1 /\ e2' = e2 ) →
    (|={E}[E']▷=> EWP e2 UNDER a @ E <| Ψ |> {{ Φ }}) ⊢ EWP e1 UNDER a @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros (? Hpuredet) "H". iApply (ewp_lift_pure_step_no_fork E E'); try done.
    { naive_solver. }
    iApply (step_fupd_wand with "H"); iIntros "H".
    iIntros (κ e' σ f (_&?&?&->)%Hpuredet); auto.
  Qed.

 (* Lemma ewp_pure_step_fupd E E' e1 e2 φ n Ψ  Φ a :
    PureExec φ n ((e1, a): expr) (e2, a) →
    φ →
    (|={E}[E']▷=>^n EWP e2 UNDER a @ E <| Ψ |> {{ Φ }}) ⊢ EWP e1 UNDER a @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros (Hexec Hφ) "Hwp". specialize (Hexec Hφ).
    iInduction Hexec as [e|n e1' e2' e3 [Hsafe ?]] "IH"; simpl; first done.
    destruct e1'. iApply ewp_lift_pure_det_step_no_fork.
    - intros σ. specialize (Hsafe σ). eauto using reducible_not_val.
    - intros.  apply pure_step_det in H as (-> & -> & -> & _).
      done.
    - by iApply (step_fupd_wand with "Hwp").
  Qed.

  Lemma ewp_pure_step_later E e1 e2 φ n Ψ Φ a :
    PureExec φ n e1 e2 →
    φ →
    ▷^n (EWP e2 UNDER a @ E <| Ψ |> {{ Φ }}) ⊢ EWP e1 UNDER a @ E <| Ψ |> {{ Φ }}.
  Proof.
    intros Hexec ?. rewrite -ewp_pure_step_fupd //. clear Hexec.
    induction n as [|n IH]; by rewrite //= -step_fupd_intro // IH.
  Qed. *)

  (* proofmode classes *)
  Global Instance frame_ewp p E e R P f Φ Ψ :
    (∀ v f, Frame p R (Φ v f) (Ψ v f)) →
    Frame p R (EWP e UNDER f @ E <| P |>  {{ Φ }}) (EWP e UNDER f @ E <| P |> {{ Ψ }}) | 2.
  Proof. rewrite /Frame=> HR. rewrite ewp_frame_l. apply ewp_mono_post, HR. Qed.

(*  Global Instance is_except_0_ewp E e Ψ Φ : IsExcept0 (EWP e UNDER f @ E <| Ψ |> {{ Φ }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_ewp -except_0_fupd -fupd_intro. Qed. *)

(*  Global Instance elim_modal_bupd_ewp p E e P Ψ Φ :
    ElimModal True p false (|==> P) P (EWP e UNDER f @ E <| Ψ |> {{ Φ }}) (EWP e UNDER f @ E <| Ψ |> {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r wand_elim_r fupd_ewp.
  Qed. *)

(*  Global Instance elim_modal_fupd_ewp p E e P Ψ Φ :
    ElimModal True p false (|={E}=> P) P (EWP e UNDER f @ E <| Ψ |> {{ Φ }}) (EWP e UNDER f @ E <| Ψ |> {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r fupd_ewp.
  Qed. *)

(*  Global Instance elim_modal_fupd_ewp_atomic p E1 E2 e P Ψ Φ a :
    ElimModal (Atomic (stuckness_to_atomicity NotStuck) e) p false
            (|={E1,E2}=> P) P
            (EWP e UNDER f @ E1 <| Ψ |> {{ v, Φ v ∗ Pred a }})%I (EWP e UNDER f @ E2 <| Ψ |> {{ v, |={E2,E1}=> Φ v ∗ Pred a }})%I | 100.
  Proof.
    intros ?. rewrite bi.intuitionistically_if_elim
                      fupd_frame_r bi.wand_elim_r ewp_atomic. auto.
  Qed. *)

(*  Global Instance add_modal_fupd_ewp E e P Φ :
    AddModal (|={E}=> P) P (WP e @ s; E {{ Φ }}).
  Proof. by rewrite /AddModal fupd_frame_r wand_elim_r fupd_wp. Qed. *)

(*  Global Instance elim_acc_ewp_atomic {X} E1 E2 α β γ e Ψ Φ a :
    ElimAcc (X:=X) (Atomic (stuckness_to_atomicity NotStuck) e)
            (fupd E1 E2) (fupd E2 E1)
            α β γ (EWP e UNDER f @ E1 <| Ψ |> {{ v, Φ v ∗ Pred a }})%I
            (λ x, EWP e UNDER f @ E2 <| Ψ |> {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) ∗ Pred a }})%I | 100.
  Proof.
    iIntros (?) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (wp_wand with "(Hinner Hα)").
    iIntros (v) ">[H [H' $]]". iApply "H'". by iApply "Hclose".
  Qed. 

  Global Instance elim_acc_wp_nonatomic {X} E α β γ e s Φ :
    ElimAcc (X:=X) True (fupd E E) (fupd E E)
            α β γ (WP e @ s; E {{ Φ }})
            (λ x, WP e @ s; E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply wp_fupd.
    iApply (wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed. *)


End wp.



