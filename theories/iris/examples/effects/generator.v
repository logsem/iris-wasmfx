
From mathcomp Require Import ssreflect eqtype seq ssrbool bigop.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
From iris.program_logic Require Import adequacy.
From iris.bi Require Export weakestpre.
From iris.algebra Require Import list excl_auth.
From Wasm Require Import type_checker_reflects_typing.
From Wasm.iris.rules Require Export iris_rules iris_example_helper.
From Wasm.iris.host Require Export iris_host.
From Wasm.iris.examples.effects Require Import coroutines_module coroutines_implementation_code.


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
    tc_types_t := [];
tc_func_t := [];
    tc_global := [];
    tc_table := [];
    tc_memory := [];
    tc_local := naturals_locs;
    tc_label := [[]];
    tc_return := None;
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
    tc_types_t := [naturals_type];
    tc_func_t := [naturals_type];
    tc_global := [];
    tc_table := [];
    tc_memory := [];
    tc_local := T_num T_i32 :: sum_until_locs;
    tc_label := [[]];
    tc_return := None;
    tc_refs := [];
    tc_tags_t := [Tf [T_num T_i32] []]
  |}.

Lemma sum_until_typing : be_typing t_ctxt_sum_until sum_until sum_until_body_type.
Proof.
  rewrite /sum_until separate3.
  eapply bet_composition'.
  {
    apply /b_e_type_checker_reflects_typing.
    simpl.
    done.
  }
  rewrite separate1.
  eapply bet_composition'.
  {
    constructor; simpl.
    rewrite (separate1 (BI_block _ _)).
    eapply bet_composition'.
    {
      apply /b_e_type_checker_reflects_typing.
      simpl.
      done.
    }
    rewrite (separate2 (BI_set_local _)).
    eapply bet_composition'.
    {
      apply /b_e_type_checker_reflects_typing.
      simpl.
      done.
    }
    by apply /b_e_type_checker_reflects_typing.
  }
  by apply /b_e_type_checker_reflects_typing.
Qed.


Section generator_spec.

  Context `{!wasmG Σ}.
  Context `{!inG Σ (excl_authR (listO (leibnizO i32)))}.

  Definition yx i := Wasm_int.int_of_Z i32m i.

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

  Lemma Z_Int32_incr n : yx (S n) = Wasm_int.Int32.iadd (yx n) (Wasm_int.Int32.repr 1).
  Proof.
    replace (Z.of_nat $ S n) with (Z.add n 1); last lia.
    apply Z_Int32_add_congruent.
  Qed.

  Fixpoint Permitted (xs: list i32) :=
    match xs with
    | [] => True
    | x :: xs' => Permitted xs' ∧ x = yx $ length xs'
    end.

  Definition SEQ (I : list i32 -> iProp Σ) : iProt Σ :=
    ( >> (x : i32) (xs : list i32) >>
      ! ([VAL_num $ VAL_int32 x]) {{ ⌜Permitted (x :: xs)⌝ ∗ I xs}} ;
      ? ([]) {{ I (x :: xs) }})%iprot.

  Definition Ψgen (addr_tag : nat) I x :=
    match x with
    | SuspendE (Mk_tagidx addr_tag) => SEQ I
    | _ => iProt_bottom
    end.

  Definition naturals_inst addr_naturals addr_tag :=
    {|
      inst_types := [ naturals_type ];
      inst_funcs := [ addr_naturals ];
      inst_tab := [];
      inst_memory := [];
      inst_globs := [];
      inst_tags := [ addr_tag ]
    |}.

  Definition closure_naturals addr_naturals addr_tag :=
    FC_func_native (naturals_inst addr_naturals addr_tag)
      naturals_type
      naturals_locs
      naturals.

  Opaque upcl.

  Lemma naturals_loop_invariant addr_naturals addr_tag n Φ (I : list i32 -> iProp Σ) xs :
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
        f_inst := naturals_inst addr_naturals addr_tag
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
      unfold SEQ.
      rewrite (upcl_tele' [tele _ _] [tele] ).
      simpl.
      iExists n, xs.
      iFrame.
      iSplit; first done.
      iSplit; first done.
      iIntros "!> HI_xs_n".
      instantiate (1 := λ v f, (⌜v = immV [] ∧ f = {|
        f_locs := [VAL_num (VAL_int32 n)];
        f_inst := naturals_inst addr_naturals addr_tag
      |}⌝ ∗ I (n :: xs))%I).
      simpl.
      by iSplit.
    }
    by iIntros (?) "[[%Hcontra _] _]".
    simpl.
    iIntros (??) "[[-> ->] HI_xs_n]".
    simpl.

    rewrite (separate1 (AI_basic (BI_get_local 0))).
    iApply ewp_seq; first done.
    repeat iSplitR.
    2: {
      iApply ewp_get_local; first done.
      by instantiate (1 := λ v f, ⌜v = immV _ ∧ f = {|
        f_locs := [VAL_num (VAL_int32 n)];
        f_inst := naturals_inst addr_naturals addr_tag
      |}⌝%I).
    }
    by iIntros (? [Hcontra _]).
    simpl.
    iIntros (?? [-> ->]).
    simpl.

    rewrite (separate3 (AI_basic _)).
    iApply ewp_seq; first done.
    repeat iSplitR.
    2: {
      iApply ewp_binop; first done.
      simpl.
      instantiate (1 := λ v f, ⌜v = immV _ ∧ f = {|
        f_locs := [VAL_num (VAL_int32 n)];
        f_inst := naturals_inst addr_naturals addr_tag
      |}⌝%I).
      by iSplit.
    }
    by iIntros (? [Hcontra _]).
    simpl.
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
    simpl.
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

  Lemma naturals_spec addr_naturals addr_tag f (I : list i32 -> iProp Σ) :
    I [] -∗
    N.of_nat addr_naturals ↦[wf] closure_naturals addr_naturals addr_tag -∗
    N.of_nat addr_tag ↦□[tag] tag_type -∗
    EWP [AI_invoke addr_naturals] UNDER f <| Ψgen addr_tag I  |> {{ v ; f, False }}.
  Proof.
    iIntros "HI_empty Hwf_naturals #Htag".

    rewrite <- (app_nil_l [AI_invoke _]).
    iApply (ewp_invoke_native with "Hwf_naturals").
    done.
    done.
    done.
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

  (*Definition Sum_until_i32 (n : i32) := xx $ \sum_(0 <= i < n) i.*)

  Lemma sum_until_spec addr_naturals addr_sum_until addr_tag f (n : i32) :
    N.of_nat addr_sum_until ↦[wf] closure_sum_until addr_naturals addr_sum_until addr_tag -∗
    N.of_nat addr_naturals ↦[wf] closure_naturals addr_naturals addr_tag -∗
    N.of_nat addr_tag ↦□[tag] tag_type -∗
    EWP [AI_const $ VAL_num $ VAL_int32 n; AI_invoke addr_sum_until] UNDER f
      {{ v ; f', ⌜f = f' ∧ v = v⌝ }}. (* TODO: post condition *)
  Proof.
    iIntros "Hwf_sum_until Hwf_naturals #Htag".

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
        (*instantiate (1 := λ v f,*)
        (*  ( ∃ k h x xs, ⌜ v = brV _ ⌝ ∗*)
        (*  N.of_nat k ↦[wcont] Live _ h ∗*)
        (*  frag_list γ xs ∗*)
        (*  ⌜Permitted xs ∧ x = yx (length xs)⌝*)
        (*  )%I*)
        (*).*)
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
            iApply ewp_resume; try done.
            simpl. instantiate (1 := [_]) => //.
            unfold agree_on_uncaptured => /=.
            instantiate (1 := Ψgen addr_tag (frag_list γ)).
            repeat split => //.
            intros i.
            destruct (i == Mk_tagidx addr_tag) eqn:Hi => //.
            move/eqP in Hi.
            intros _.
            admit.
            2: iFrame "Hcont".
            unfold hfilled, hfill => //=.
            iSplitR; last iSplitR; last iSplitL "Hwf_naturals Hfrag".
            3: {
              iApply (ewp_call_reference with "Hwf_naturals"); try done.
              iIntros "!> !> Hwf_naturals".
              by iApply (naturals_spec with "[Hfrag] [Hwf_naturals]").
            }
            by iIntros.
            2: iSplitR; first by iIntros (? HFalse).
            2: {
              Opaque upcl.
              iSimpl.
              iSplit; last done.
              iFrame "Htag".
              iIntros "!>" (vs k h) "Hcont HΨgen".
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
              iSplitR; first done.
              admit.
            }
            by iIntros "(% & % & % & % & %Hcontra & _)".
          }
          by iIntros (?) "[(% & % & % & % & %Hcontra & _) _]".

          simpl.
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
              ⌜f =  {|
      f_locs :=
        [VAL_num (VAL_int32 n); VAL_num (VAL_int32 Wasm_int.Int32.zero);
         VAL_num (VAL_int32 Wasm_int.Int32.zero);
         VAL_ref (VAL_ref_cont kaddr)];
      f_inst := sum_until_inst addr_naturals addr_sum_until addr_tag
    |}⌝ ∗
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
        admit.
      }

      admit.
      admit.

    }
    admit.
    admit.
  Admitted.


End sum_until_spec.
