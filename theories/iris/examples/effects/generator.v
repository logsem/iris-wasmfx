
From mathcomp Require Import ssreflect eqtype seq ssrbool bigop.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map.
From iris.base_logic.lib Require Export fancy_updates.
From iris.program_logic Require Import adequacy.
From iris.bi Require Export weakestpre.
From iris.algebra Require Import list excl_auth.
From Wasm Require Import type_checker_reflects_typing.
From Wasm.iris.rules Require Export iris_rules iris_example_helper.
From Wasm.iris.host Require Export iris_host.


Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition naturals_type := Tf [] [].
Definition cont_type := T_contref naturals_type.
Definition sum_until_body_type := Tf [] [T_num T_i32].
Definition sum_until_type := Tf [T_num T_i32] [T_num T_i32].
Definition tag_type := Tf [T_num T_i32] [].

Definition gen_tag := Mk_tagident 0.

Definition naturals_locs :=
  [ T_num T_i32 ].

Definition sum_until_locs := [T_num T_i32; T_num T_i32; T_ref cont_type].


Definition naturals :=
  [
    BI_loop (Tf [] []) [
      BI_get_local 0;
      BI_suspend gen_tag; (* suspend with generated number *)
      BI_get_local 0; (* generate next number *)
      BI_const (xx 1);
      BI_binop T_i32 (Binop_i BOI_add);
      BI_set_local 0;
      BI_br 0 (* loop *)
    ]
  ].

Definition t_ctxt_naturals :=
  {|
    tc_types_t := [naturals_type; sum_until_type];
    tc_func_t := [naturals_type; sum_until_type];
    tc_global := [];
    tc_table := [];
    tc_memory := [];
    tc_local := naturals_locs;
    tc_label := [[]];
    tc_return := Some [];
    tc_refs := [];
    tc_tags_t := [tag_type]
  |}.

Lemma naturals_typing : be_typing t_ctxt_naturals naturals naturals_type.
Proof.
  apply /b_e_type_checker_reflects_typing.
  done.
Qed.


Definition sum_until := [
    (* param $upto = 0 *)
    (* local $v = 1 *)
    (* local $sum = 2 *)
    (* local $k = 3 *)
    BI_ref_func 0;
    BI_contnew (Type_lookup 0);
    BI_set_local 3; (* $k *)
    BI_loop (* $l *) (Tf [] []) [
      BI_block (* $on_gen *) (Tf [] [T_num T_i32; T_ref (cont_type)]) [
        BI_get_local 3; (* $k *)
        BI_resume (Type_lookup 0) [ HC_catch gen_tag 0 (* $on_gen *) ];
        BI_unreachable
      ];
      BI_set_local 3; (* $k *)
      BI_set_local 1; (* $v *)

      BI_get_local 2; (* $sum *)
      BI_get_local 1; (* $v *)
      BI_binop T_i32 (Binop_i BOI_add);
      BI_set_local 2; (* $sum *)

      BI_get_local 1; (* $v *)
      BI_get_local 0; (* $upto *)
      BI_relop T_i32 (Relop_i (ROI_lt SX_U));
      BI_br_if 0 (* $l *)
    ];
    BI_get_local 2 (* $sum *)
  ].

Definition t_ctxt_sum_until :=
  {|
    tc_types_t := [naturals_type; sum_until_type];
    tc_func_t := [naturals_type; sum_until_type];
    tc_global := [];
    tc_table := [];
    tc_memory := [];
    tc_local := T_num T_i32 :: sum_until_locs;
    tc_label := [[T_num T_i32]];
    tc_return := Some [T_num T_i32];
    tc_refs := [];
    tc_tags_t := [tag_type]
  |}.

Lemma sum_until_typing : be_typing t_ctxt_sum_until sum_until sum_until_body_type.
Proof.
  rewrite /sum_until separate3.
  eapply bet_composition'.
  {
    rewrite separate1.
    eapply bet_composition'.
    constructor; done.
    rewrite separate1.
    eapply bet_composition'.
    constructor; done.
    constructor; done.
  }
  rewrite separate1.
  eapply bet_composition'.
  {
    constructor; simpl.
    rewrite (separate1 (BI_block _ _)).
    eapply bet_composition'.
    {
      rewrite (separate1 (BI_block _ _)).
      eapply bet_composition'.
      2: apply /b_e_type_checker_reflects_typing; simpl; done.
      constructor.
      rewrite (separate1 (BI_get_local _)).
      eapply bet_composition'.
      constructor; done.
      apply /b_e_type_checker_reflects_typing; simpl.
      done.
    }
    by apply /b_e_type_checker_reflects_typing.
  }
  by apply /b_e_type_checker_reflects_typing.
Qed.


(* Helper lemmas about bounded inegers *)

Definition yx i := Wasm_int.int_of_Z i32m i.
Definition xy i := Wasm_int.nat_of_uint i32m i.

Lemma Z_Int32_add_congruent a b : yx (a + b) = Wasm_int.Int32.iadd (yx a) (yx b).
Proof.
  unfold yx, Wasm_int.Int32.iadd, Wasm_int.Int32.add.
  simpl.
  apply Wasm_int.Int32.eqm_samerepr.
  unfold Wasm_int.Int32.eqm.
  apply Zbits.eqmod_add.
  1,2: rewrite Wasm_int.Int32.Z_mod_modulus_eq.
  1,2: apply Zbits.eqmod_mod.
  1,2: unfold Wasm_int.Int32.modulus,
  Wasm_int.Int32.wordsize,
  Integers.Wordsize_32.wordsize.
  1,2: lias.
Qed.

Lemma nat_Int32_add_congruent (a b : nat) : yx (a + b)%nat = Wasm_int.Int32.iadd (yx a) (yx b).
Proof.
  rewrite Nat2Z.inj_add.
  apply Z_Int32_add_congruent.
Qed.

Lemma Z_Int32_incr n : yx (S n) = Wasm_int.Int32.iadd (yx n) (Wasm_int.Int32.repr 1).
Proof.
  replace (Z.of_nat $ S n) with (Z.add n 1); last lia.
  apply Z_Int32_add_congruent.
Qed.

Lemma xy_incr_no_overflow x :
  Wasm_int.Int32.ltu x (Wasm_int.Int32.iadd x (Wasm_int.Int32.one)) ->
  xy (Wasm_int.Int32.iadd x (Wasm_int.Int32.one)) = S $ xy x.
Proof.
  intros Hx_lt_x1.
  unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add.
  unfold xy.
  simpl.
  rewrite Wasm_int.Int32.Z_mod_modulus_eq.
  pose proof (Wasm_int.Int32.unsigned_range x) as [H0x Hxmod].
  rewrite Z.mod_small.
  - by rewrite Z2Nat.inj_succ.
  - split; first lia.
    unfold Wasm_int.Int32.ltu, Coqlib.zlt in Hx_lt_x1.
    destruct Z_lt_dec as [H|] in Hx_lt_x1; last done.
    unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add in H.
    simpl in H.
    rewrite Wasm_int.Int32.Z_mod_modulus_eq in H.
    destruct (Z_lt_ge_dec (Wasm_int.Int32.unsigned x + 1) Wasm_int.Int32.modulus) as [Hsmall | Hlarge].
    + exact Hsmall.
    + exfalso.
      assert (Wasm_int.Int32.unsigned x + 1 = Wasm_int.Int32.modulus)%Z as Heq by lia.
      rewrite Heq in H.
      rewrite Z_mod_same_full in H.
      lia.
Qed.

Lemma yx_xy_yx n :
  yx n = yx $ xy $ yx n.
Proof.
  unfold yx, xy.
  rewrite Wasm_int.Int32.int_of_Z_nat_of_uint.
  done.
Qed.

Lemma int32_incr_no_overflow x :
  (∃ y, Wasm_int.Int32.ltu x y) ->
  Wasm_int.Int32.ltu x
  (Wasm_int.Int32.iadd x Wasm_int.Int32.one).
Proof.
  intros [y Hx_lt_y].
  unfold Wasm_int.Int32.ltu, Coqlib.zlt.
  destruct Z_lt_dec as [|H]; first done.
  exfalso.
  apply H; clear H.
  unfold Wasm_int.Int32.iadd, Wasm_int.Int32.add.
  simpl.
  rewrite Wasm_int.Int32.Z_mod_modulus_eq.
  unfold Wasm_int.Int32.ltu, Coqlib.zlt in Hx_lt_y.
  destruct Z_lt_dec as [H|]; last done.
  rewrite Z.mod_small; first lia.
  pose proof Wasm_int.Int32.unsigned_range x as [Hx0 Hxmod].
  pose proof Wasm_int.Int32.unsigned_range y as [_ Hymod].
  lia.
Qed.

Lemma zlt_succ_or_eq (x y : Z) :
  (x < y)%Z -> (x + 1 < y \/ x + 1 = y)%Z.
Proof. lia. Qed.

Lemma int32_lt_incr x y :
  Wasm_int.Int32.ltu x y ->
  Wasm_int.Int32.ltu (Wasm_int.Int32.iadd x Wasm_int.Int32.one) y ∨
  Wasm_int.Int32.eq (Wasm_int.Int32.iadd x Wasm_int.Int32.one) y.
Proof.
  intros Hx_lt_u.
  unfold Wasm_int.Int32.eq, Wasm_int.Int32.ltu in *.
  simpl.
  rewrite Wasm_int.Int32.Z_mod_modulus_eq.
  unfold Coqlib.zlt in Hx_lt_u.
  destruct (Z_lt_dec (Wasm_int.Int32.unsigned x) (Wasm_int.Int32.unsigned y)) as [H|] in Hx_lt_u; last done.
  rewrite Z.mod_small.
  - pose proof (zlt_succ_or_eq H) as [Hlt | Heq].
    + left. unfold Coqlib.zlt. by destruct (Z_lt_dec (Wasm_int.Int32.unsigned x + 1) (Wasm_int.Int32.unsigned y)).
    + right. rewrite Heq. apply Coqlib.zeq_true.
  - pose proof Wasm_int.Int32.unsigned_range x as [Hx0 Hxmod].
    pose proof Wasm_int.Int32.unsigned_range y as [_ Hymod].
    lia.
Qed.

Lemma int32_ltu_zero x :
  Wasm_int.Int32.ltu (yx 0) x = false ->
  x = yx 0.
Proof.
  intros Hltu.
  unfold Wasm_int.Int32.ltu, Coqlib.zlt in Hltu.
  destruct (Z_lt_dec _) as [|Hnltu]; first done.
  apply Znot_lt_ge in Hnltu as Hgeq.
  pose proof Wasm_int.Int32.unsigned_range x as [Hx0 _].
  simpl in Hgeq.
  assert (Wasm_int.Int32.unsigned x = 0); first lias.
  unfold yx; simpl.
  symmetry.
  apply Wasm_int.Int32.eqm_repr_eq.
  rewrite H.
  apply Wasm_int.Int32.eqm_refl.
Qed.


Section generator_spec.

  Context `{!wasmG Σ}.

  Fixpoint Permitted (xs: list i32) :=
    match xs with
    | [] => True
    | x :: xs' => Permitted xs' ∧ x = yx $ length xs'
    end.

  Definition SEQ (I : list i32 -> iProp Σ) : iProt Σ :=
    ( >> (x : i32) (xs : list i32) >>
      ! ([VAL_num $ VAL_int32 x]) {{ ⌜Permitted (x :: xs)⌝ ∗ I xs}} ;
      ? ([]) {{ I (x :: xs) }})%iprot.

  Definition Ψgen (addr_tag : nat) I :=
    (λ x, 
    match x with
    | (Mk_tagidx addr) => if Nat.eqb addr addr_tag then SEQ I else iProt_bottom
    end, bot_switch, bot_throw).

  Definition generator_inst addr_naturals addr_sum_until addr_tag :=
    {|
      inst_types := [ naturals_type; sum_until_type ];
      inst_funcs := [ addr_naturals; addr_sum_until ];
      inst_tab := [];
      inst_memory := [];
      inst_globs := [];
      inst_tags := [ addr_tag ]
    |}.

  Definition closure_naturals addr_naturals addr_sum_until addr_tag :=
    FC_func_native (generator_inst addr_naturals addr_sum_until addr_tag)
      naturals_type
      naturals_locs
      naturals.

  Opaque upcl.

  Lemma naturals_loop_invariant addr_naturals addr_sum_until addr_tag n Φ (I : list i32 -> iProp Σ) xs :
    N.of_nat addr_tag ↦□[tag] tag_type -∗
    ⌜yx $ length xs = n⌝ -∗
    ⌜Permitted xs⌝ -∗
    I xs -∗
    EWP [AI_basic
          (BI_loop (Tf [] [])
              [BI_get_local 0; BI_suspend gen_tag; BI_get_local 0;
              BI_const (xx 1); BI_binop T_i32 (Binop_i BOI_add);
              BI_set_local 0; BI_br 0])]
      UNDER {|
        f_locs := [VAL_num (VAL_int32 n)];
        f_inst := generator_inst addr_naturals addr_sum_until addr_tag
      |} <| Ψgen addr_tag I |> {{ Φ }}.
  Proof.
    iIntros "#Htag H_xs_agree_n HPermitted_xs HI_xs".
    iLöb as "IH" forall (xs n).

    iPoseProof "H_xs_agree_n" as "%H_xs_agree_n".
    iPoseProof "HPermitted_xs" as "%HPermitted_xs".

    rewrite <- (app_nil_l [AI_basic _]).
    iApply ewp_loop; try done.
    iModIntro.
    simpl.

    iApply (ewp_label_bind with "[-]").
    2: {
      iPureIntro.
      unfold lfilled, lfill => //=.
      instantiate (5 := []).
      simpl.
      rewrite app_nil_r.
      done.
    }

    (* get_local will result in 'n' on stack *)
    rewrite (separate1 (AI_basic (BI_get_local 0))).
    iApply ewp_seq; try done.
    repeat iSplitR.
    2: {
      iApply ewp_get_local; try done.
      auto_instantiate.
    }
    by iIntros (?) "[% _]".
    simpl.
    iIntros (??) "[-> ->]".
    simpl.

    (* Reason about suspend *)
    rewrite (separate2 (AI_basic _)).
    iApply ewp_seq; first done.

    (* We use 'I xs' to reason about the suspend. *)
    (* We will need it for the protocol. *)
    iSplitR; last iSplitL "HI_xs".
    2: {
      rewrite (separate1 (AI_basic (BI_const _))).
      iApply ewp_suspend; try done.
      3: iFrame "#".
      instantiate (1 := [VAL_num (VAL_int32 n)]).
      1,2: done.
      simpl.
      rewrite Nat.eqb_refl.
      unfold SEQ.
      rewrite (upcl_tele' [tele _ _] [tele] ).
      simpl.
      iExists n, xs.
      iFrame.
      iSplit; first done.
      iSplit; first done.
      iIntros "!> HI_xs_n".
      instantiate (1 := λ v f, (⌜v = immV []⌝ ∗ ⌜f = Build_frame _ _⌝ ∗ I (n :: xs))%I).
      repeat iSplit; done.
    }
    by iIntros (?) "[%Hcontra _]".

    iIntros (??) "(-> & -> & HI_xs_n)".
    simpl.

    rewrite (separate1 (AI_basic (BI_get_local 0))).
    iApply ewp_seq; first done.
    repeat iSplitR.
    2: {
      iApply ewp_get_local; first done.
      auto_instantiate.
    }
    by iIntros (? [Hcontra _]).

    iIntros (?? [-> ->]).
    simpl.

    rewrite (separate3 (AI_basic _)).
    iApply ewp_seq; first done.
    repeat iSplitR.
    2: {
      iApply ewp_binop; first done.
      auto_instantiate.
    }
    by iIntros (? [Hcontra _]).

    iIntros (?? [-> ->]).
    simpl.

    rewrite (separate2 (AI_basic _)).
    iApply ewp_seq; first done.
    repeat iSplitR.
    2: {
      fold (AI_const $ VAL_num (VAL_int32 (Wasm_int.Int32.iadd n (Wasm_int.Int32.repr 1)))).
      iApply ewp_set_local; first (simpl; lia).
      simpl.
      auto_instantiate.
    }
    by iIntros (? [Hcontra _]).

    iIntros (?? [-> ->]).
    simpl.
 
    iApply ewp_value; first done.
    simpl.
    iIntros (LI HLI).
    move /lfilledP in HLI.
    inversion HLI; subst.
    inversion H8; subst.
    simpl.

    iApply ewp_br.
    3: {
      instantiate (1 := 0).
      instantiate (1 := []).
      instantiate (1 := LH_base [] _).
      unfold lfilled, lfill => //=.
    }
    1,2: done.
    simpl.
    iModIntro.
    iApply "IH"; last done.
    - iPureIntro.
      simpl.
      apply Z_Int32_incr.
    - done.
  Qed.


  Definition naturals_spec addr_naturals cl_naturals Ψ (I : list i32 -> iProp Σ) : iProp Σ :=
    (□ (∀ f, I [] -∗
    N.of_nat addr_naturals ↦[wf] cl_naturals -∗
    EWP [AI_invoke addr_naturals] UNDER f <| Ψ |> {{ v ; f, False }})).

  Lemma naturals_spec_proof addr_naturals addr_sum_until cl_naturals (I : list i32 -> iProp Σ) :
   ∀ addr_tag,
   cl_naturals = closure_naturals addr_naturals addr_sum_until addr_tag ->
   N.of_nat addr_tag ↦□[tag] tag_type
   ⊢ naturals_spec addr_naturals cl_naturals (Ψgen addr_tag I) I.
  Proof.
    iIntros (addr_tag ->) "#Htag".
    iIntros (f) "!>".
    iIntros "HI_empty Hwf_naturals".

    rewrite <- (app_nil_l [AI_invoke _]).
    iApply (ewp_invoke_native with "Hwf_naturals"); try done.
    iIntros "!> _".
    simpl.

    iApply ewp_frame_bind; try done.
    instantiate (1 := λ v f, False%I).
    simpl.
    iSplitR; first by iIntros.
    iSplitL; last by iIntros.

    rewrite <- (app_nil_l [AI_basic _]).
    iApply ewp_block; try done.
    simpl.

    iApply (ewp_label_bind with "[-]").
    2 :{
      iPureIntro.
      unfold lfilled, lfill => //=.
      instantiate (5 := []).
      simpl.
      rewrite app_nil_r.
      done.
    }
    iApply naturals_loop_invariant.
    4: done.
    all: auto.
  Qed.

End generator_spec.

Section sum_until_spec.

  Context `{!wasmG Σ}.
  Context `{!inG Σ (excl_authR (listO (leibnizO i32)))}.

  Definition auth_list γ xs := own γ (●E xs).
  Definition frag_list γ xs := own γ (◯E xs).

  Lemma alloc_initial :
   ⊢ |==> ∃ γ , (auth_list γ [] ∗ frag_list γ []).
  Proof.
    iMod (own_alloc (●E [] ⋅ ◯E [])) as (γ) "[Hγ_auth Hγ_frac]"; first by apply excl_auth_valid.
    by iFrame.
  Qed.

  Lemma own_auth_frag_agree γ xs ys :
    auth_list γ ys -∗
    frag_list γ xs -∗
    ⌜ys = xs⌝.
  Proof.
    iIntros "Hauth Hfrag".
    iCombine "Hauth Hfrag" gives "%HValid".
    iPureIntro.
    by apply excl_auth_agree_L.
  Qed.

  Lemma auth_frag_update γ x xs ys :
    auth_list γ ys -∗
    frag_list γ xs -∗
    |==> auth_list γ (x :: ys) ∗ frag_list γ (x :: ys).
  Proof.
    iIntros "Hauth Hfrag".
    unfold auth_list, frag_list.
    rewrite <- own_op.
    iCombine "Hauth Hfrag" as "Hboth".
    iApply (own_update with "Hboth").
    apply excl_auth_update.
  Qed.


  Definition sum_until_inst addr_naturals addr_sum_until addr_tag :=
    {|
      inst_types := [ naturals_type; sum_until_type ];
      inst_funcs := [ addr_naturals; addr_sum_until ];
      inst_tab := [];
      inst_memory := [];
      inst_globs := [];
      inst_tags := [ addr_tag ]
    |}.

  Definition closure_sum_until addr_naturals addr_sum_until addr_tag :=
    FC_func_native (sum_until_inst addr_naturals addr_sum_until addr_tag)
      sum_until_type
      sum_until_locs
      sum_until.

  Definition Sum_until_i32 (n : i32) := yx $ \sum_(0 <= i < S $ xy n) i.

  Lemma sum_until_loop_invariant γ addr_naturals addr_sum_until addr_tag xs k h LI (upto v sum: i32) :
    ⌜Wasm_int.Int32.ltu v upto⌝ -∗
    ⌜sum = Sum_until_i32 v⌝ -∗
    ⌜hfilled No_var (hholed_of_valid_hholed h) [] LI⌝ -∗
    N.of_nat addr_tag ↦□[tag] tag_type -∗
    N.of_nat k↦[wcont]Live (Tf [] []) h -∗
    auth_list γ (v :: xs) -∗
    EWP LI UNDER empty_frame <| Ψgen addr_tag (frag_list γ) |> {{ _;_, False }} -∗
      EWP [AI_basic
            (BI_loop (Tf [] [])
                [BI_block (Tf [] [T_num T_i32; T_ref cont_type])
                  [BI_get_local 3; BI_resume (Type_lookup 0) [HC_catch gen_tag 0];
                    BI_unreachable]; BI_set_local 3; BI_set_local 1;
                BI_get_local 2; BI_get_local 1; BI_binop T_i32 (Binop_i BOI_add);
                BI_set_local 2; BI_get_local 1; BI_get_local 0;
                BI_relop T_i32 (Relop_i (ROI_lt SX_U));
                BI_br_if 0])]
      UNDER {|
              f_locs :=
                [VAL_num (VAL_int32 upto); VAL_num (VAL_int32 v);
                  VAL_num (VAL_int32 sum);
                  VAL_ref (VAL_ref_cont k)];
              f_inst := sum_until_inst addr_naturals addr_sum_until addr_tag
            |}
      {{ w ; f, ∃ v' sum' k',
        ⌜w = immV []⌝ ∗
        ⌜f =  {|
                f_locs :=
                  [VAL_num (VAL_int32 upto); VAL_num (VAL_int32 v');
                    VAL_num (VAL_int32 sum');
                    VAL_ref (VAL_ref_cont k')];
                f_inst := sum_until_inst addr_naturals addr_sum_until addr_tag
              |}⌝ ∗
        ⌜sum' = Sum_until_i32 upto⌝
      }}.
  Proof.
    iIntros "Hv_lt_upto Hsum HLI #Htag Hcont Hauth Hcont_spec".
    iLöb as "IH" forall (LI h xs k v sum).
    iPoseProof "Hsum" as "%Hsum".
    iPoseProof "HLI" as "%HLI".
    iPoseProof "Hv_lt_upto" as "%Hv_lt_upto".

    (* enter loop *)
    rewrite <- (app_nil_l [AI_basic _]).
    iApply ewp_loop; try done.
    simpl.
    iApply (ewp_label_bind with "[-]").
    2: {
      iPureIntro.
      unfold lfilled, lfill => //=.
      instantiate (5 := []).
      simpl.
      rewrite app_nil_r.
      done.
    }

    (* reason about resumption block *)
    rewrite (separate1 (AI_basic (BI_block _ _))).
    iApply ewp_seq; first done.
    iSplitR; last iSplitR "Hauth".
    2: {
      rewrite <- (app_nil_l [AI_basic (BI_block _ _)]).
      iApply ewp_block; try done.
      simpl.
      iApply (ewp_label_bind with "[-]").
      2: {
        iPureIntro.
        unfold lfilled, lfill => //=.
        instantiate (5 := []).
        simpl.
        rewrite app_nil_r.
        done.
      }
      (* put continuation on stack *)
      rewrite (separate1 (AI_basic (BI_get_local _))).
      iApply ewp_seq; first done.
      repeat iSplitR.
      2: {
        iApply ewp_get_local; first done.
        auto_instantiate.
      }
      by iIntros (? [Hcontra _]).
      iIntros (?? [-> ->]); simpl.
      rewrite (separate2 (AI_ref_cont _)).
      iApply ewp_seq; first done.

      iSplitR; last iSplitL.
      2: {
        (* reason about resumption *)
        rewrite <- (app_nil_l [AI_ref_cont _; _]).
        iApply ewp_resume.
        done. done. done.
        simpl. instantiate (1 := [_]) => //.
        unfold agree_on_uncaptured => /=.
        instantiate (1 := Ψgen addr_tag (frag_list γ)). 
        repeat split => //. 
        intros i.
        destruct (i == Mk_tagidx addr_tag) eqn:Hi => //.
        move/eqP in Hi.
        intros _.
        unfold Ψgen.
        destruct i as [addr].
        destruct (addr =? addr_tag) eqn:Hn => //.
        exfalso; apply Hi.
        by apply Nat.eqb_eq in Hn as ->.
        unfold get_suspend. rewrite Hn. done.
        done.
        iFrame "Hcont".
        iSplitR; last iSplitR; last iSplitL "Hcont_spec".
        3: {
          iExact "Hcont_spec".
        }
        by iIntros.
        2: iSplitR; first by iIntros (? HFalse).
        2: {
          Opaque upcl.
          iSimpl.
          iSplit; last done.
          iFrame "Htag".
          iIntros "!>" (vs k' h') "Hcont HΨgen".
          rewrite Nat.eqb_refl.
          rewrite (upcl_tele' [tele _ _] [tele]).
          simpl.
          iDestruct "HΨgen" as "(%x & %xs' & -> & [%HPermitted_x_xs' Hfrag] & Hcont_spec)".
          iSimpl.
          instantiate (1 := λ v,
            ( ∃ k h x xs, ⌜ v = brV _ ⌝ ∗
              N.of_nat k ↦[wcont] Live _ h ∗
              ⌜Permitted xs ∧ x = yx (length xs)⌝ ∗
              frag_list γ xs ∗
              ( frag_list γ (x :: xs) -∗
                ∃ LI , ⌜hfilled No_var (hholed_of_valid_hholed h) [] LI⌝ ∗
              ▷ EWP LI
                UNDER empty_frame <| Ψgen addr_tag (frag_list γ) |> {{ _;_,False }}
              )
            )%I
          ).
          iApply ewp_value.
          done.
          iFrame.
          iFrame "%".
          done. (* iSplitR; first done.
          iIntros "Hfrag".
          iDestruct ("Hcont_spec" with "Hfrag") as (LI') "[%HLI' Hcont_spec]".
          iExists LI'.
          iSplit; last done.
          iPureIntro.
          by (destruct (hfilled No_var (hholed_of_valid_hholed h') [] LI')). *)
        }
        by iIntros "(% & % & % & % & %Hcontra & _)".
      }
      by iIntros (?) "[(% & % & % & % & %Hcontra & _) _]".

      simpl.
      iIntros (??) "[(%k' & %h' & %x & %xs' & -> & Hcont & %HPermitted_x_xs' & Hfrag & Hcont_spec) ->]".
      simpl.
      iApply ewp_value; first done.
      simpl.
      iIntros (LI' HLI').
      move /lfilledP in HLI'.
      inversion HLI'; subst.
      inversion H8; subst; simpl.

      iApply ewp_br.
      3: {
        instantiate (1 := 0).
        instantiate (1 := [AI_basic (BI_const (VAL_int32 x)); AI_ref_cont k']).
        instantiate (1 := LH_base [] _).
        unfold lfilled, lfill => //=.
      }
      1,2 : done.
      simpl.
      iApply ewp_value; first done.
      simpl.
      instantiate (1 := λ w f,
        (∃ k' x xs' h', 
          ⌜w = immV _⌝ ∗
          ⌜f = Build_frame _ _⌝ ∗
          ⌜Permitted (x :: xs')⌝ ∗
          N.of_nat k'↦[wcont]Live (Tf [] []) h' ∗
          frag_list γ xs' ∗
          ( frag_list γ (x :: xs') -∗
                ∃ LI', ⌜hfilled No_var (hholed_of_valid_hholed h') [] LI'⌝ ∗
              ▷ EWP LI'
                UNDER empty_frame <| Ψgen addr_tag (frag_list γ) |> {{ _;_,False }}
          )
        )%I
      ).
      simpl.
      iFrame.
      iFrame "%".
      done.
    }
    by iIntros (?) "(% & % & % & % & %Hcontra & _)".
    iIntros (??) "(%k' & %x & %xs' & %h' & -> & -> & %HPermitted_x_xs' & Hcont & Hfrag & Hcont_spec)".
    simpl.
    iPoseProof (own_auth_frag_agree with "Hauth Hfrag") as "<-".
    iApply fupd_ewp.
    iMod (auth_frag_update _ x _ _ with "Hauth Hfrag") as "[Hauth Hfrag]".
    iModIntro.

    (* Store continuation in $k *)
    rewrite (separate3 (AI_basic (BI_const _))).
    iApply ewp_seq; first done.
    iSplitR; last iSplitR.

    2: {
      rewrite (separate1 (AI_basic (BI_const _))).
      iApply ewp_val_app; first done.
      iSplitR.
      2: {
        fold (AI_const (VAL_ref (VAL_ref_cont k'))).

        instantiate (1 := λ v f, (⌜ v = immV [_] ⌝ ∗ ⌜ f = Build_frame _ _ ⌝)%I).
        iApply ewp_set_local; first lias.
        done.
      }
      by iIntros "!>" (?) "[%Hcontra _]".
    }
    by iIntros (?) "[%Hcontra _]".
    simpl.
    iIntros (?? [-> ->]).
    simpl.

    (* Store generated value, 'x' in $v *)
    rewrite (separate2 (AI_basic (BI_const _))).
    iApply ewp_seq; first done.
    iSplitR; last iSplitR.
    2: {
      fold (AI_const $ VAL_num $ VAL_int32 x).
      iApply ewp_set_local; first lias.
      auto_instantiate.
    }
    by iIntros (? [Hcontra _]).
    iIntros (?? [-> ->]); simpl.

    (* add %v to %sum *)
    rewrite (separate4 (AI_basic (BI_get_local _))).
    iApply ewp_seq; first done.
    iSplitR; last iSplitR.
    2: {
      rewrite (separate1 (AI_basic (BI_get_local _))).
      iApply ewp_seq; first done.
      iSplitR; last iSplitR.
      2: {
        iApply ewp_get_local.
        done.
        auto_instantiate.
      }
      by iIntros (? [Hcontra _]).
      iIntros (?? [-> ->]); simpl.
      rewrite (separate2 (AI_basic (BI_const _))).
      iApply ewp_seq; first done.
      iSplitR; last iSplitR.
      2: {
        rewrite (separate1 (AI_basic (BI_const _))).
        iApply ewp_val_app; first done.
        iSplitR.
        2: {
          instantiate (1 := λ v f, (⌜v = immV _ ⌝ ∗ ⌜ f = Build_frame _ _ ⌝)%I).
          by iApply ewp_get_local.
        }
        by iIntros (? [Hcontra ?]).
      }
      by iIntros (? [Hcontra ?]).
      iIntros (?? [-> ->]); simpl.
      rewrite (separate3 (AI_basic (BI_const _))).
      iApply ewp_seq; first done.
      iSplitR; last iSplitR.
      2: {
        iApply ewp_binop; first done.
        auto_instantiate.
      }
      by iIntros (? [Hcontra _]).
      iIntros (?? [-> ->]); simpl.
      assert (AI_basic
      (BI_const (VAL_int32 (Wasm_int.Int32.iadd (Sum_until_i32 v) x))) =
      AI_const $ VAL_num $ VAL_int32 (Wasm_int.Int32.iadd (Sum_until_i32 v) x)
      ) as H; first done.
      rewrite H.
      iApply ewp_set_local; first lias.
      auto_instantiate.
    }
    by iIntros (? [Hcontra ?]).
    iIntros (?? [-> ->]); simpl.

    (* get $v and $upto on the stack *)
    rewrite (separate2 (AI_basic (BI_get_local _))).
    iApply ewp_seq; first done.
    iSplitR; last iSplitR.
    2: {
      rewrite (separate1 (AI_basic (BI_get_local _))).
      iApply ewp_seq; first done.
      iSplitR; last iSplitR.
      2: {
        iApply ewp_get_local.
        done.
        auto_instantiate.
      }
      by iIntros (? [Hcontra _]).
      iIntros (?? [-> ->]); simpl.
      
      rewrite (separate1 (AI_basic (BI_const _))).
      iApply ewp_val_app; first done.
      iSplitR.
      2: {
        instantiate (1 := λ v f, (⌜v = immV _ ⌝ ∗ ⌜ f = Build_frame _ _ ⌝)%I).
        by iApply ewp_get_local.
      }
      by iIntros "!>" (? [Hcontra _]).
    }
    by iIntros (? [Hcontra _]).
    iIntros (?? [-> ->]); simpl.

    (* compare $v to $upto *)
    rewrite (separate3 (AI_basic (BI_const _))).
    iApply ewp_seq; first done.
    iSplitR; last iSplitR.
    2: {
      iApply ewp_relop; first done.
      auto_instantiate.
    }
    by iIntros (? [Hcontra _]).
    iIntros (?? [-> ->]); simpl.

    destruct (Wasm_int.Int32.ltu x upto) eqn:Hltu; simpl.
    - (* Case: x < upto *)
      iApply ewp_br_if_true; first done.
      iApply ewp_value; first done.
      simpl.
      iIntros (LI' HLI').
      move /lfilledP in HLI'.
      inversion HLI'; subst.
      inversion H8; subst.
      simpl.
      iApply ewp_br.
      3: {
        instantiate (1 := 0).
        instantiate (1 := []).
        instantiate (1 := LH_base [] []).
        unfold lfilled, lfill => //=.
      }
      done.
      done.
      simpl.
      iDestruct ("Hcont_spec" with "Hfrag") as (LI') "[%Hfilled_h'_LI' HewpLI']".
      iIntros "!> !>".
      clear HLI' H7 H8 H1.
      iApply ("IH" with "[] [] [] [Hcont] [Hauth] [HewpLI']").
      + done.
      + iPureIntro.
        destruct HPermitted_x_xs' as [[_ Hv] Hx].
        simpl in Hx.
        rewrite Z_Int32_incr in Hx.
        subst x.
        subst v.
        unfold Sum_until_i32 at 2.
        rewrite xy_incr_no_overflow.
        2: {
          apply int32_incr_no_overflow.
          by eexists.
        }
        rewrite big_nat_recr //=.
        rewrite nat_Int32_add_congruent.
        f_equal.
        rewrite Z_Int32_incr.
        f_equal.
        by apply yx_xy_yx.
      + done.
      + done.
      + done.
      + done.
    - (* Case: upto <= x *)
      iApply ewp_br_if_false; first done.
      simpl.
      iIntros (LI' HLI').
      move /lfilledP in HLI'.
      inversion HLI'; subst.
      inversion H8; subst.
      iApply ewp_label_value; first done.
      iIntros "!> !>".
      iClear (HLI' H7 H8 H1) "IH".
      iPureIntro.
      destruct HPermitted_x_xs' as [[HPermitted_xs Hv] Hx].
      simpl in Hx.
      rewrite Z_Int32_incr in Hx.
      replace (@length (Equality.sort i32) xs) with (@length Wasm_int.Int32.T xs) in Hv; last done.
      rewrite <- Hv in Hx.
      assert (x = upto) as <-. {
        apply Wasm_int.Int32.same_if_eq.
        clear Hv h' HLI HPermitted_xs k'.
        replace (Wasm_int.Int32.iadd v (Wasm_int.Int32.repr 1)) with (Wasm_int.Int32.iadd v Wasm_int.Int32.one) in Hx; last done.
        apply int32_lt_incr in Hv_lt_upto as [Hv1_lt_upto | Hv1_eq_upto]; rewrite <- Hx in *.
        - by rewrite Hv1_lt_upto in Hltu.
        - done.
      }
      repeat eexists.
      unfold Sum_until_i32 at 2.
      subst x.
      rewrite xy_incr_no_overflow; last done.
      rewrite big_nat_recr //=.
      rewrite nat_Int32_add_congruent.
      f_equal.
      rewrite Z_Int32_incr.
      f_equal.
      rewrite Hv.
      by apply yx_xy_yx.
  Qed.


  Definition sum_until_spec addr_naturals addr_sum_until cl_naturals cl_sum_until : iProp Σ :=
    (□ (∀ f upto, N.of_nat addr_sum_until ↦[wf] cl_sum_until -∗
    N.of_nat addr_naturals ↦[wf] cl_naturals -∗
    EWP [AI_const $ VAL_num $ VAL_int32 upto; AI_invoke addr_sum_until] UNDER f
      {{ v ; f', ⌜f = f'⌝ ∗ ⌜v = immV [VAL_num $ VAL_int32 $ Sum_until_i32 upto]⌝ }})).

  Lemma sum_until_spec_proof addr_naturals addr_sum_until cl_naturals cl_sum_until :
   ∀ addr_tag,
   cl_naturals = closure_naturals addr_naturals addr_sum_until addr_tag ->
   cl_sum_until = closure_sum_until addr_naturals addr_sum_until addr_tag ->
   N.of_nat addr_tag ↦□[tag] tag_type
   ⊢ sum_until_spec addr_naturals addr_sum_until cl_naturals cl_sum_until.
  Proof.
    iIntros (addr_tag -> ->) "#Htag".
    iIntros (f upto) "!> Hwf_sum_until Hwf_naturals".

    rewrite separate1.
    iApply (ewp_invoke_native with "Hwf_sum_until"); try done.
    iIntros "!> Hwf_sum_until"; simpl.

    iApply ewp_frame_bind; try done.
    iSplitR; last iSplitR "Hwf_sum_until".
    2: {
      rewrite <- (app_nil_l [AI_basic _]).
      iApply ewp_block; try done.
      simpl.

      iApply (ewp_label_bind with "[-]").
      2: {
        iPureIntro.
        unfold lfilled, lfill => //=.
        instantiate (5 := []).
        simpl.
        rewrite app_nil_r.
        done.
      }

      (* reason about body of sum_until *)

      (* create func ref to naturals *)
      rewrite (separate1 (AI_basic _)).
      iApply ewp_seq; first done.
      repeat iSplitR.
      2: {
        iApply ewp_ref_func; first done.
        auto_instantiate.
      }
      by iIntros (? [Hcontra _]).
      iIntros (?? [-> ->]); simpl.

      (* create continuation *)
      rewrite separate2.
      iApply ewp_seq; first done.
      repeat iSplitR.
      2: by iApply ewp_contnew.
      by iIntros (?) "(% & %Hcontra & _)".
      iIntros (??) "(% & -> & -> & Hcont)"; simpl.

      (* store continuation in $k *)
      rewrite separate2.
      iApply ewp_seq; first done.
      repeat iSplitR.
      2: {
        fold (AI_const $ VAL_ref $ VAL_ref_cont kaddr).
        iApply ewp_set_local; first lias.
        auto_instantiate.
      }
      by iIntros (? [Hcontra _]).
      iIntros (?? [-> ->]); simpl.

      (* create ghost resources to track generated value *)
      iApply fupd_ewp.
      iMod (alloc_initial) as "(%γ & Hauth & Hfrag)".
      iModIntro.

      (* enter loop *)
      rewrite separate1.
      iApply ewp_seq; first done.
      iSplitR; last iSplitL.
      2: {
        rewrite <- (app_nil_l [AI_basic _]).
        iApply ewp_loop; try done.
        simpl.
        iApply (ewp_label_bind with "[-]").
        2: {
          iPureIntro.
          unfold lfilled, lfill => //=.
          instantiate (5 := []).
          simpl.
          rewrite app_nil_r.
          done.
        }

        (* reason about resumption block *)
        rewrite separate1.
        iApply ewp_seq; first done.
        iSplitR; last iSplitR "Hauth".
        2: {
          rewrite <- (app_nil_l [AI_basic _]).
          iApply ewp_block; try done.
          simpl.
          iApply (ewp_label_bind with "[-]").
          2: {
            iPureIntro.
            unfold lfilled, lfill => //=.
            instantiate (5 := []).
            simpl.
            rewrite app_nil_r.
            done.
          }
          (* put continuation on stack *)
          rewrite separate1.
          iApply ewp_seq; first done.
          repeat iSplitR.
          2: {
            iApply ewp_get_local; first done.
            auto_instantiate.
          }
          by iIntros (? [Hcontra _]).
          iIntros (?? [-> ->]); simpl.
          rewrite separate2.
          iApply ewp_seq; first done.

          iSplitR; last iSplitL.
          2: {
            (* reason about resumption *)
            rewrite <- (app_nil_l [AI_ref_cont _; _]).
            iApply ewp_resume.
            done. done. done. 
            simpl. instantiate (1 := [_]) => //.
            unfold agree_on_uncaptured => /=.
            instantiate (1 := Ψgen addr_tag (frag_list γ)).
            repeat split => //.
            intros i.
            destruct (i == Mk_tagidx addr_tag) eqn:Hi => //.
            move/eqP in Hi.
            intros _.
            unfold Ψgen.
            destruct i as [addr].
            destruct (addr =? addr_tag) eqn:Hn => //.
            exfalso; apply Hi.
            by apply Nat.eqb_eq in Hn as ->.
            rewrite /get_suspend Hn //.
            2: iFrame "Hcont".
            unfold hfilled, hfill => //=.
            iSplitR; last iSplitR; last iSplitL "Hwf_naturals Hfrag".
            3: {
              iApply (ewp_call_reference with "Hwf_naturals"); try done.
              iIntros "!> !> Hwf_naturals".
              by iApply (naturals_spec_proof with "[] [Hfrag] [Hwf_naturals]").
            }
            by iIntros.
            2: iSplitR; first by iIntros (? HFalse).
            2: {
              Opaque upcl.
              iSimpl.
              iSplit; last done.
              iFrame "Htag".
              iIntros "!>" (vs k h) "Hcont HΨgen".
              rewrite Nat.eqb_refl.
              rewrite (upcl_tele' [tele _ _] [tele]).
              simpl.
              iDestruct "HΨgen" as "(%x & %xs & -> & [HPermitted_xs_x Hfrag] & Hcont_spec)".
              iSimpl.
              instantiate (1 := λ v,
                ( ∃ k h x xs, ⌜ v = brV _ ⌝ ∗
                  N.of_nat k ↦[wcont] Live _ h ∗
                  ⌜Permitted xs ∧ x = yx (length xs)⌝ ∗
                  frag_list γ xs ∗
                  ( frag_list γ (x :: xs) -∗
                    ∃ LI , ⌜hfilled No_var (hholed_of_valid_hholed h) [] LI⌝ ∗
                 ▷ EWP LI
                    UNDER empty_frame <| Ψgen addr_tag (frag_list γ) |> {{ _;_,False }}
                  )
                )%I
              ).
              iApply ewp_value.
              done.
              iFrame.
              done.
(*              iSplitR; first done.
              iIntros "Hfrag".
              iDestruct ("Hcont_spec" with "Hfrag") as (LI) "[%HLI Hewp]".
              iExists LI.
              iSplit; last done.
              iPureIntro.
              by (destruct (hfilled No_var (hholed_of_valid_hholed h) [] LI)). *)
            }
            by iIntros "(% & % & % & % & %Hcontra & _)".
          }
          by iIntros (?) "[(% & % & % & % & %Hcontra & _) _]".

          iIntros (??) "[(%k & %h & %x & %xs & -> & Hcont & HPermitted_xs_x & Hfrag & Hcont_spec) ->]".
          simpl.

          iApply ewp_value; first done.
          simpl.
          iIntros (LI HLI).
          move /lfilledP in HLI.
          inversion HLI; subst.
          inversion H8; subst; simpl.

          iApply ewp_br.
          3: {
            instantiate (1 := 0).
            instantiate (1 := [AI_basic (BI_const (VAL_int32 x)); AI_ref_cont k]).
            instantiate (1 := LH_base [] _).
            unfold lfilled, lfill => //=.
          }
          1,2 : done.
          simpl.
          iApply ewp_value; first done.
          simpl.
          instantiate (1 := λ v f,
            (∃ k x xs h, 
              ⌜v = immV _⌝ ∗
              ⌜f = Build_frame _ _⌝ ∗
              ⌜Permitted (x :: xs)⌝ ∗
              N.of_nat k↦[wcont]Live (Tf [] []) h ∗
              frag_list γ xs ∗
              ( frag_list γ (x :: xs) -∗
                    ∃ LI , ⌜hfilled No_var (hholed_of_valid_hholed h) [] LI⌝ ∗
                 ▷ EWP LI
                    UNDER empty_frame <| Ψgen addr_tag (frag_list γ) |> {{ _;_,False }}
              )
            )%I
          ).
          simpl.
          iFrame.
          done.
        }
        by iIntros (?) "(% & % & % & % & %Hcontra & _)".
        iIntros (??) "(%k & %x & %xs & %h & -> & -> & %HPermitted_x_xs & Hcont & Hfrag & Hcont_spec)".
        simpl.
        iPoseProof (own_auth_frag_agree with "Hauth Hfrag") as "<-".
        iApply fupd_ewp.
        iMod (auth_frag_update _ x [] _ with "Hauth Hfrag") as "[Hauth Hfrag]".
        iModIntro.

        (* Store continuation in $k *)
        rewrite separate3.
        iApply ewp_seq; first done.
        iSplitR; last iSplitR.

        2: {
          rewrite (separate1 (AI_basic _)).
          iApply ewp_val_app; first done.
          iSplitR.
          2: {
            fold (AI_const (VAL_ref (VAL_ref_cont k))).

            instantiate (1 := λ v f, (⌜ v = immV [_] ⌝ ∗ ⌜ f = Build_frame _ _ ⌝)%I).
            iApply ewp_set_local; first lias.
            done.
          }
          by iIntros "!>" (?) "[%Hcontra _]".
        }
        by iIntros (?) "[%Hcontra _]".

        iIntros (?? [-> ->]).
        simpl.

        (* Store generated value, 'x' in $v *)
        rewrite separate2.
        iApply ewp_seq; first done.
        iSplitR; last iSplitR.
        2: {
          fold (AI_const $ VAL_num $ VAL_int32 x).
          iApply ewp_set_local; first lias.
          auto_instantiate.
        }
        by iIntros (? [Hcontra _]).
        iIntros (?? [-> ->]); simpl.

        (* add %v to %sum *)
        rewrite separate4.
        iApply ewp_seq; first done.
        iSplitR; last iSplitR.
        2: {
          rewrite separate1.
          iApply ewp_seq; first done.
          iSplitR; last iSplitR.
          2: {
            iApply ewp_get_local.
            done.
            auto_instantiate.
          }
          by iIntros (? [Hcontra _]).
          iIntros (?? [-> ->]); simpl.
          rewrite separate2.
          iApply ewp_seq; first done.
          iSplitR; last iSplitR.
          2: {
            rewrite separate1.
            iApply ewp_val_app; first done.
            iSplitR.
            2: {
              instantiate (1 := λ v f, (⌜v = immV _ ⌝ ∗ ⌜ f = Build_frame _ _ ⌝)%I).
              by iApply ewp_get_local.
            }
            by iIntros (? [Hcontra ?]).
          }
          by iIntros (? [Hcontra ?]).
          iIntros (?? [-> ->]); simpl.
          rewrite separate3.
          iApply ewp_seq; first done.
          iSplitR; last iSplitR.
          2: {
            iApply ewp_binop; first done.
            auto_instantiate.
          }
          by iIntros (? [Hcontra _]).
          iIntros (?? [-> ->]); simpl.
          fold (AI_const $ VAL_num $ VAL_int32 (Wasm_int.Int32.iadd Wasm_int.Int32.zero x)).
          iApply ewp_set_local; first lias.
          auto_instantiate.
        }
        by iIntros (? [Hcontra ?]).
        iIntros (?? [-> ->]); simpl.

        (* get $v and $upto on the stack *)
        rewrite (separate2 (AI_basic _)).
        iApply ewp_seq; first done.
        iSplitR; last iSplitR.
        2: {
          rewrite (separate1 (AI_basic _)).
          iApply ewp_seq; first done.
          iSplitR; last iSplitR.
          2: {
            iApply ewp_get_local.
            done.
            auto_instantiate.
          }
          by iIntros (? [Hcontra _]).
          iIntros (?? [-> ->]); simpl.
          
          rewrite (separate1 $ AI_basic _).
          iApply ewp_val_app; first done.
          iSplitR.
          2: {
            instantiate (1 := λ v f, (⌜v = immV _ ⌝ ∗ ⌜ f = Build_frame _ _ ⌝)%I).
            by iApply ewp_get_local.
          }
          by iIntros "!>" (? [Hcontra _]).
        }
        by iIntros (? [Hcontra _]).
        iIntros (?? [-> ->]); simpl.

        (* compare $v to $upto *)
        rewrite separate3.
        iApply ewp_seq; first done.
        iSplitR; last iSplitR.
        2: {
          iApply ewp_relop; first done.
          auto_instantiate.
        }
        by iIntros (? [Hcontra _]).
        iIntros (?? [-> ->]); simpl.
        destruct HPermitted_x_xs as [HPermitted_xs Hx_0].
        simpl in Hx_0.
        rewrite Hx_0.
        destruct (Wasm_int.Int32.ltu (yx 0%nat) upto) eqn:Hltu; simpl.
        - (* Case: 0 < upto *)
          iApply ewp_br_if_true; first done.
          iApply ewp_value; first done.
          simpl.
          iIntros (LI HLI).
          move /lfilledP in HLI.
          inversion HLI; subst.
          inversion H8; subst.
          simpl.
          iApply ewp_br.
          3: {
            instantiate (1 := 0).
            instantiate (1 := []).
            instantiate (1 := LH_base [] []).
            unfold lfilled, lfill => //=.
          }
          done.
          done.
          simpl.
          iDestruct ("Hcont_spec" with "Hfrag") as (LI) "[%Hfilled_h_LI HewpLI]".
          iIntros "!> !>".
          iApply (sum_until_loop_invariant with "[] [] [] [] [Hcont] [Hauth] [-]"); try done.
          iPureIntro. 
          unfold Sum_until_i32.
          rewrite big_nat_recl //=.
          by rewrite big_geq.
        - (* Case: upto = 0 *)
          iApply ewp_br_if_false; first done.
          simpl.
          iIntros (LI HLI).
          move /lfilledP in HLI.
          inversion HLI; subst.
          inversion H8; subst.
          iApply ewp_label_value; first done.
          iIntros "!> !>".
          iExists (yx 0), (yx 0), k.
          iSplitR; first done.
          iSplitR; first done.
          iPureIntro.
          clear HLI H7 H8 H1.
          apply int32_ltu_zero in Hltu.
          subst upto.
          unfold yx; simpl.
          unfold Sum_until_i32.
          rewrite big_nat_recl //=.
          by rewrite big_geq.
      }
      by iIntros (?) "(% & % & % & %Hcontra & _)".

      iIntros (??) "(% & % & % & -> & -> & ->)"; simpl.
      iApply ewp_get_local; first done.
      simpl.
      iIntros (LI HLI).
      move /lfilledP in HLI.
      inversion HLI; subst.
      inversion H8; subst.
      simpl.
      iApply ewp_label_value; first done.
      simpl.
      instantiate (1 := λ v f , (⌜v = immV _⌝)%I).
      done.
    }
    by iIntros (? Hcontra).
    iIntros (?? ->).
    simpl.
    by iApply ewp_frame_value.
  Qed.

  Lemma sum_until_100 addr_naturals addr_sum_until addr_tag f :
    N.of_nat addr_sum_until ↦[wf] closure_sum_until addr_naturals addr_sum_until addr_tag -∗
    N.of_nat addr_naturals ↦[wf] closure_naturals addr_naturals addr_sum_until addr_tag -∗
    N.of_nat addr_tag ↦□[tag] tag_type -∗
    EWP [AI_const $ VAL_num $ VAL_int32 $ yx 100; AI_invoke addr_sum_until] UNDER f
      {{ v ; f', ⌜f = f' ∧ v = immV [VAL_num $ VAL_int32 $ yx 5050]⌝ }}.
  Proof.
    iIntros "Haddr_sum_until Haddr_naturals #Htag".
    iApply (ewp_wand with "[-] []").
    - iApply (sum_until_spec_proof with "[] [Haddr_sum_until] [Haddr_naturals]"); done.
    - iIntros (?? [-> ->]).
      iPureIntro.
      split; first done.
      unfold Sum_until_i32.
      repeat f_equal.
      replace (xy (yx 100)) with (100); last done.
      repeat rewrite big_nat_recl //=.
      rewrite big_geq; done.
  Qed.

  Lemma sum_until_0 addr_naturals addr_sum_until addr_tag f :
    N.of_nat addr_sum_until ↦[wf] closure_sum_until addr_naturals addr_sum_until addr_tag -∗
    N.of_nat addr_naturals ↦[wf] closure_naturals addr_naturals addr_sum_until addr_tag -∗
    N.of_nat addr_tag ↦□[tag] tag_type -∗
    EWP [AI_const $ VAL_num $ VAL_int32 $ yx 0; AI_invoke addr_sum_until] UNDER f
      {{ v ; f', ⌜f = f' ∧ v = immV [VAL_num $ VAL_int32 $ yx 0]⌝ }}.
  Proof.
    iIntros "Haddr_sum_until Haddr_naturals #Htag".
    iApply (ewp_wand with "[-] []").
    - iApply (sum_until_spec_proof with "[] [Haddr_sum_until] [Haddr_naturals]"); done.
    - iIntros (?? [-> ->]).
      iPureIntro.
      split; first done.
      unfold Sum_until_i32.
      repeat f_equal.
      replace (xy (yx 0)) with (0); last done.
      repeat rewrite big_nat_recl //=.
      rewrite big_geq; done.
  Qed.

  Lemma sum_until_3_neg addr_naturals addr_sum_until addr_tag f :
    N.of_nat addr_sum_until ↦[wf] closure_sum_until addr_naturals addr_sum_until addr_tag -∗
    N.of_nat addr_naturals ↦[wf] closure_naturals addr_naturals addr_sum_until addr_tag -∗
    N.of_nat addr_tag ↦□[tag] tag_type -∗
    EWP [AI_const $ VAL_num $ VAL_int32 $ yx (-4294967293); AI_invoke addr_sum_until] UNDER f
      {{ v ; f', ⌜f = f' ∧ v = immV [VAL_num $ VAL_int32 $ yx 6]⌝ }}.
  Proof.
    iIntros "Haddr_sum_until Haddr_naturals #Htag".
    iApply (ewp_wand with "[-] []").
    - iApply (sum_until_spec_proof with "[] [Haddr_sum_until] [Haddr_naturals]"); done.
    - iIntros (?? [-> ->]).
      iPureIntro.
      split; first done.
      unfold Sum_until_i32.
      repeat f_equal.
      replace (xy (yx (-4294967293))) with (3); last done.
      repeat rewrite big_nat_recl //=.
      rewrite big_geq; done.
  Qed.

End sum_until_spec.




