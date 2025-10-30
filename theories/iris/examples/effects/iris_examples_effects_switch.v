From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
From Wasm.iris.rules Require Export iris_rules iris_example_helper.
From Wasm Require Import type_checker_reflects_typing.

Set Bullet Behavior "Strict Subproofs".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Example Programs *)
Section Example2.
  Context `{!wasmG Σ}.

  Definition f'_type := Tf [] [T_num T_i32].
  Definition f'_cont_type := T_contref f'_type.

  Definition g_type := Tf [T_ref f'_cont_type] [T_num T_i32].
  Definition g_cont_type := T_contref g_type.

  Definition f_type := Tf [T_ref g_cont_type] [T_num T_i32].
  Definition f_cont_type := T_contref f_type.

  Definition main_type := Tf [] [T_num T_i32].

  Definition swap_tag : tag_identifier := Mk_tagident 0.
  Definition swap_tag_type := Tf [] [T_num T_i32].

  Definition main_body :=
    [ BI_ref_func 1;
      BI_contnew (Type_lookup 1);

      BI_ref_func 0;
      BI_contnew (Type_lookup 0);

      BI_resume (Type_lookup 0) [HC_switch swap_tag];

      BI_return
    ].

  Definition f_body :=
    [ BI_get_local 0;
      BI_switch (Type_lookup 1) (Mk_tagident 0);
      BI_unreachable
    ].

  Definition g_body :=
    [ BI_const (xx 42) ].

  Definition typing_context : t_context :=
  {|
    tc_types_t := [f_type; g_type; f'_type; main_type];
    tc_func_t := [f_type; g_type; main_type];
    tc_global := [];
    tc_table := [];
    tc_memory := [];
    tc_local := [T_ref g_cont_type];
    tc_label := [];
    tc_return := Some [];
    tc_refs := [];
    tc_tags_t := [swap_tag_type]
  |}.

  Lemma g_body_type : be_typing typing_context g_body (Tf [] [T_num T_i32]).
  Proof.
    apply /b_e_type_checker_reflects_typing; done.
  Qed.

  Lemma f_body_type : be_typing typing_context f_body (Tf [] [T_num T_i32]).
  Proof.
    unfold f_body.
    rewrite separate1.
    eapply bet_composition'.
    by constructor.
    rewrite separate1.
    eapply bet_composition'.
    eapply bet_switch; try done.
    unfold g_type, f'_cont_type, f'_type.
    instantiate (1 := []).
    instantiate (1 := []).
    done.
    done.
    apply /b_e_type_checker_reflects_typing.
    done.
  Qed.


  Definition typing_context_main : t_context :=
  {|
    tc_types_t := [f_type; g_type; f'_type; main_type];
    tc_func_t := [f_type; g_type; main_type];
    tc_global := [];
    tc_table := [];
    tc_memory := [];
    tc_local := [];
    tc_label := [];
    tc_return := Some [];
    tc_refs := [];
    tc_tags_t := [Tf [] [T_num T_i32]]
  |}.


  Lemma main_body_type : be_typing typing_context_main main_body main_type.
  Proof.
    rewrite /main_body separate1.
    eapply bet_composition'.
    {
      apply /b_e_type_checker_reflects_typing.
      simpl.
      done.
    }
    rewrite separate1.
    eapply bet_composition'.
    {
      constructor.
      done.
    }

    rewrite separate1.
    eapply bet_composition'.
    {
      apply /b_e_type_checker_reflects_typing.
      simpl.
      done.
    }
    rewrite separate1.
    eapply bet_composition'.
    {
      rewrite (separate1 (T_ref _)).
      eapply bet_weakening.
      constructor.
      done.
    }
    simpl.
    rewrite separate1.
    eapply bet_composition'.
    {
      rewrite (separate1 (T_ref _)).
      apply bet_resume.
      done.
      repeat constructor.
    }
    apply /b_e_type_checker_reflects_typing.
    done.
  Qed.


  Definition inst addrg addrf addrmain tag :=
    {|
      inst_types  := [f'_type; g_type; f_type; main_type];
      inst_funcs  := [addrg; addrf; addrmain];
      inst_tab    := [];
      inst_memory := [];
      inst_globs  := [];
      inst_tags   := [tag];
    |}.

  Lemma g_spec : ∀(addrg addrf addrmain tag: nat) f k,
    (N.of_nat addrg) ↦[wf] FC_func_native (inst addrf addrg addrmain tag) g_type [] g_body -∗
    EWP [AI_ref_cont k; AI_invoke addrg] UNDER f {{ v; f', ⌜v = (immV [VAL_num $ xx 42]) ∧ f = f'⌝ }}.
  Proof.
    iIntros (??????) "Hwf_addrg".

    (* Reason about invocation of g function *)
    rewrite separate1.
    iApply (ewp_invoke_native with "Hwf_addrg"); try done.

    (* Reason about g_body in a frame *)
    iIntros "!> Hwf_addrg"; simpl.
    iApply ewp_frame_bind => //.
    repeat iSplitR.

    2: {
      rewrite <- (app_nil_l _).
      iApply ewp_block; try done.
      iModIntro; simpl.
      iApply ewp_label_value.
      done.
      auto_instantiate.
    }

    { by iIntros (? [Hcontra _]). }

    iIntros (?? [-> ->]).
    simpl.
    by iApply ewp_frame_value.
  Qed.

  Definition Ψ (addr_tag : nat) : meta_protocol :=
    (bot_suspend,
    λ t, match t with
          | (Mk_tagidx addr) =>
              if Nat.eqb addr addr_tag then
                (iProt_bottom, λ hh, False%I)
              else
                (iProt_bottom, λ hh, False%I)
          end,
    bot_throw).


  Lemma f_spec : ∀(addrg addrf addrmain tag: nat) f k vh,
    (N.of_nat k↦[wcont]Live (Tf [T_ref f'_cont_type] [T_num T_i32]) vh) -∗
    (N.of_nat addrf) ↦[wf] FC_func_native (inst addrg addrf addrmain tag) f_type [] f_body -∗
    (N.of_nat tag) ↦□[tag] swap_tag_type -∗
    EWP [AI_ref_cont k; AI_invoke addrf] UNDER f <| Ψ tag |> {{ v; f', False }}.
  Proof.
    iIntros (???????) "Hwcont_g Hwf_addrf #Htag".

    (* Reason about invocation of f function *)
    rewrite (separate1 (AI_ref_cont _)).
    iApply (ewp_invoke_native with "Hwf_addrf"); try done.

    (* Reason about f_body in a frame *)
    iIntros "!> Hwf_addrf"; simpl.
    iApply ewp_frame_bind => //.
    iSplitR; last iSplitL "Hwcont_g".

    2: {
      unfold f_body.
      rewrite <- (app_nil_l [AI_basic _]).
      iApply ewp_block; try done.
      iModIntro; simpl.
      iApply (ewp_label_bind with "[-]").
      2: {
        iPureIntro.
        instantiate (5 := []).
        unfold lfilled; simpl.
        by rewrite app_nil_r.
      }
      rewrite (separate1 (AI_basic _)).
      iApply ewp_seq; first done.
      repeat iSplitR.
      2: { iApply ewp_get_local. done. auto_instantiate. }
      by iIntros (? [Hcontra _]).
      iIntros (?? [-> ->]).
      simpl.
      (* Reason about switch *)
      rewrite separate2.
      iApply ewp_seq; first done.
      simpl.
      iSplitR; last iSplitL "Hwcont_g".
      2: {
        rewrite <- (app_nil_l [AI_ref_cont _; _]).
        iApply ewp_switch.
        done.
        done.
        done.
        instantiate (1 := []).
        done.
        done.
        iFrame "#".
        iFrame "Hwcont_g".
        admit.
      }
      admit.
      admit.
    }
    admit.
    admit.

  Admitted.

  Lemma main_spec : ∀(addrg addrf addrmain tag: nat) f,
    (N.of_nat addrg) ↦[wf] FC_func_native (inst addrg addrf addrmain tag) g_type [] g_body -∗
    (N.of_nat addrf) ↦[wf] FC_func_native (inst addrg addrf addrmain tag) f_type [] f_body -∗
    (N.of_nat addrmain) ↦[wf] FC_func_native (inst addrg addrf addrmain tag) main_type [] main_body -∗
    (N.of_nat tag) ↦□[tag] Tf [] [] -∗
    EWP [AI_invoke addrmain] UNDER f {{ v; f', ⌜v = (immV [VAL_num $ xx 42]) ∧ f = f'⌝}}.
  Proof.
  Admitted.

End Example2.
