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
Section Example1.
  Context `{!wasmG Σ}.

  Print empty_context.


  Definition aux_type := Tf [] [].
  Definition main_type := Tf [] [T_num T_i32].
  
  Definition aux_body :=
    [ BI_suspend (Mk_tagident 0) ].

  
  Definition t_ctxt :=
    {| tc_types_t := [aux_type; main_type];
      tc_func_t := [aux_type; main_type];
      tc_global := [];
      tc_table := [];
      tc_memory := [];
      tc_local := [];
      tc_label := [];
      tc_return := None;
      tc_refs := [];
      tc_tags_t := [aux_type] |}.



  Lemma aux_typing : be_typing t_ctxt aux_body aux_type.
  Proof.
    apply/b_e_type_checker_reflects_typing.
    done.
  Qed. 
    
  
  Definition aux_prot : iProt Σ :=
    ( ! (immV []) {{ True%I }} ; ? (immV []) {{ False }})%iprot.
        
  

  Definition Ψaux x :=
    match x with
    | SuspendE (Mk_tagidx 0) => aux_prot
    | _ => iProt_bottom
    end.



  Definition old_main_body :=
    [ BI_block (Tf [] [T_ref (T_contref aux_type)]) [
          BI_ref_func 0;
          BI_contnew (Type_lookup 0);
          BI_resume (Type_lookup 0) [ HC_catch (Mk_tagident 0) 0 ]
          (* would need to add a continuation here to make it typecheck *)
        ] ;
      BI_drop ;
      BI_const (xx 1)
    ].

  Definition main_body :=
    [ BI_block (Tf [] []) [
          BI_block (Tf [] [T_ref (T_contref aux_type)]) [
              BI_ref_func 0;
              BI_contnew (Type_lookup 0);
              BI_resume (Type_lookup 0) [ HC_catch (Mk_tagident 0) 0 ];
              BI_br 1
            ] ;
          BI_drop
        ];
      BI_const (xx 1)
    ].

  Lemma main_typing : be_typing t_ctxt main_body main_type.
  Proof.
    rewrite /main_body separate1.
    eapply bet_composition'.
    - constructor.
      rewrite (separate1 (BI_block _ _)).
      eapply bet_composition'.
      + constructor.
        apply/b_e_type_checker_reflects_typing.
        done.
      + constructor.
    - constructor.
  Qed. 

  Definition inst :=
    {| inst_types := [ aux_type; main_type ];
      inst_funcs := [ 0; 1 ] ;
      inst_tab := [];
      inst_memory := [];
      inst_globs := [];
      inst_tags := [0] |}.

  Lemma spec_aux a f:
    N.of_nat a ↦[wf] FC_func_native inst aux_type [] aux_body ∗
      0%N ↦□[tag] Tf [] []
      ⊢ EWP [AI_invoke a] UNDER f <| Ψaux |> {{ v ; f' , False }}.
  Proof.
    iIntros "(Ha & Htag)".
    
    (* Make the invocation *)
    rewrite -(app_nil_l [_]).
    iApply (ewp_invoke_native with "Ha").
    done.
    done.
    done.
    iIntros "!> Ha".
    
    (* Bind into the frame *)
    iApply ewp_frame_bind => //.
    iSplitR.
    instantiate (1 := λ _ _, False%I).
    iIntros "%" => //. 
    iSplitL "Htag".
        
    (* Bind into the block *)
    rewrite -(app_nil_l [_]).
    iApply ewp_block.
    done. done. done. done.
    iIntros "!>".
    iApply (ewp_label_bind with "[Htag]").
    2:{ iPureIntro. unfold lfilled, lfill => //=.
        instantiate (5 := []).
        simpl.
        rewrite app_nil_r.
        done. }

    (* Desugar the suspend *)
    rewrite -(app_nil_l [_]).
    rewrite -(N2Nat.id 0).
    iApply (ewp_suspend_desugar with "[$Htag]").
    done. done. instantiate (1 := []). done. done.
(*    iIntros "Htag". *)

    (* Perform suspend operation *)
    iApply ewp_suspend.
    rewrite (upcl_tele' [tele ] [tele]).
    iSimpl.
    iSplitL. done.
    iSplitL. done.
    iIntros "!> H".
    done.
        
    iIntros (w ?) "%" => //.

  Qed. 
  
    

  
  Lemma spec_main f a:
    N.of_nat a ↦[wf] FC_func_native inst main_type [] main_body
      ∗  0%N ↦□[tag] Tf [] [] ∗ 0%N ↦[wf] FC_func_native inst aux_type [] aux_body
      ⊢ EWP [AI_invoke a] UNDER f {{ w ; f' , ⌜ w = immV [VAL_num $ xx 1] ⌝ ∗  ⌜ f' = f ⌝ }}.
  Proof.
    iIntros "(Ha & #Htag & Haux)".
    
    (* Make the invocation *)
    rewrite -(app_nil_l [_]).
    iApply (ewp_invoke_native with "Ha").
    done.
    done.
    done.
    iIntros "!> Ha".
    
    (* Bind into the calling frame *)
    iApply ewp_frame_bind => //.
    iSplitR; last first.
    iFrame.
    iSplitL.

    - (* 1. prove a ewp for the inside of the calling frame *)
      
      (* Bind into the calling block *)
      rewrite -(app_nil_l [AI_basic _]).
      iApply ewp_block.
      done. done. done. done.
      iIntros "!>".
      iApply (ewp_label_bind with "[-]").
      2:{ iPureIntro. unfold lfilled, lfill => //=.
          instantiate (5 := []).
          simpl.
          rewrite app_nil_r.
          done. }

      (* Two instructions on the stack: a block and a value 1. Focus on the first *)

      rewrite (separate1 (AI_basic _)).
      iApply ewp_seq; first done.
      iSplitR; last first.
      iSplitL.

      + (* 1. prove a ewp for the left-hand operation (i.e. the block) *)

        (* Bind into the outer block *)
        rewrite -(app_nil_l [AI_basic _]).
        iApply ewp_block.
        done. done. done. done.
        iIntros "!>".
        iApply (ewp_label_bind with "[-]").
        2:{ iPureIntro. unfold lfilled, lfill => //=.
            instantiate (5 := []).
            simpl.
            rewrite app_nil_r.
            done. }

        (* Two instructions on the stack: a block and a drop. Focus on the first *)

        
        rewrite (separate1 (AI_basic _)).
        iApply ewp_seq; first done.
        iSplitR; last first.
        iSplitL.

        * (* 1. prove a ewp for the left-hand operation (i.e. the block) *)

          (* Bind into the inner block *)
          rewrite -(app_nil_l [AI_basic _ ]).
          iApply ewp_block.
          done. done. done. done.
          iIntros "!>".
          iApply (ewp_label_bind with "[-]").
          2:{ iPureIntro. unfold lfilled, lfill => //=.
              instantiate (5 := []).
              simpl.
              rewrite app_nil_r.
              done. }

          
          (* Desugar the function reference *)
          rewrite (separate1 $ AI_basic _).
          iApply ewp_seq; first done.
          iSplitR; last first.
          iSplitR.
          iApply ewp_ref_func.
          done.
          auto_instantiate.
          2: by iIntros (?) "[% _]".
          iIntros (w f') "[-> ->]".
          iSimpl.


          (* Create the new continuation *)
          rewrite separate2.
          iApply ewp_seq; first done.
          iSplitR; last first.
          iSplitR.
          iApply ewp_contnew.
          done.
          2: by iIntros (?) "(%kaddr & % & _)".
          iIntros (w f') "(%kaddr & -> & -> & Hcont)".
          iSimpl.

          (* Two operations on the stack: resuming and breaking. Focus on the first *)

          rewrite (separate2 (AI_ref_cont _)).
          iApply ewp_seq; first done.
          iSplitR; last first.
          iSplitL.

          -- (* 1. Prove a ewp for the resume *) 


            rewrite -(app_nil_l [AI_ref_cont _;_]).
            iApply (ewp_resume with "[$Hcont Haux]").
            done. done. done. simpl. instantiate (1 := [_]). done.
            instantiate (1 := Ψaux).
            unfold agree_on_uncaptured.
            repeat split.
            intros i Hi.
            unfold Ψaux.
            destruct i => //=.
            destruct n => //=.
            unfold hfilled, hfill => //=.
            erewrite eq_refl. done.
            iSplitR; last first.
            iSplitR; last first. 
            (*            iSplitR; first by instantiate (1 := λ f, ⌜ f = Build_frame _ _ ⌝%I). *)
            iSplitL; last iSplitR.

            (* Resume instruction premise 1: ewp for the body *)      
            ++ rewrite - (N2Nat.id 0).
               iApply (ewp_call_reference with "Haux").
               done. done.
               iIntros "!> !> Haux".
               (* apply the spec for aux *)
               iApply spec_aux.
               iFrame. done.

            (* Resume instruction presime 2: what happens if the computation terminates *)
            ++ iIntros (w) "%" => //.

            (* Resume instruction premise 3: clause triples, i.e. what happens if an effect is triggered *)
            ++ Opaque upcl. iSimpl. iSplit; last done.
               iFrame "Htag".
               iIntros "!>" (vs k h) "Hcont HΨ".
               (* we know that the triggered effect obeys the protocol *)
               rewrite (upcl_tele' [tele] [tele]).
               simpl.
               iDestruct "HΨ" as "(% & _)".
               inversion H; subst; clear H.
               iApply ewp_value.
               unfold IntoVal.
               apply of_to_val.
               simpl. cbn. done.
               instantiate (1 := λ v, (∃ k h, ⌜ v = brV _ ⌝ ∗ N.of_nat k ↦[wcont] Cont_hh _ h)%I).
               iExists k, h.
               iFrame. done.
            ++ iIntros "(% & % & % & _)" => //.
            ++ iIntros (?) "%" => //.

          -- (* 2. now focus on the Br after the resume *)
            iIntros (w f') "[(%k & %h & -> & Hcont) ->]".
            iSimpl.
            iApply ewp_value.
            unfold IntoVal.
            apply of_to_val. cbn. done.
            iIntros (LI HLI).
            move/lfilledP in HLI; inversion HLI; subst.
            inversion H8; subst.
            iSimpl.
            iApply ewp_br.
            3:{ instantiate (1 := 0).
                 instantiate (1 := [_]).
                 instantiate (2 := LH_base [] _).
                 unfold lfilled, lfill => //=. }
            done. done.
            iIntros "!>".
            iApply ewp_value.
            apply of_to_val => //.
            instantiate (1 := λ v f, (∃ k h, ⌜ v = immV _ ⌝ ∗ _)%I).
(*            iSplitL; last by instantiate (1 := λ f, ⌜ f = Build_frame _ _ ⌝%I). *)
            iExists k, h.
            iSplit; first done.
            iExact "Hcont".
          -- by iIntros (?) "[(%k & %h & % & _) _]".


        * (* 2. now focus on the drop after the block *)
          iIntros (w f') "(%k & %h & -> & Hcont)".
          iSimpl.
          iApply (ewp_wand with "[]").
          fold (AI_const (VAL_ref (VAL_ref_cont k))).
          iApply ewp_drop.
          by instantiate (1 := λ v f, ⌜ v = immV _ ⌝%I).
          iIntros (??) "->".
          iIntros (LI HLI).
          move/lfilledP in HLI.
          inversion HLI; subst.
          inversion H8; subst.
          iSimpl.
          iApply (ewp_wand with "[]").
          iApply ewp_label_value.
          done.
          by instantiate (1 := λ v f, ⌜ v = immV _ ⌝%I).
(*          by instantiate (1 := λ f, ⌜ f = Build_frame _ _ ⌝%I). *)
          iIntros (w ?) "->".
          instantiate (1 := λ v f, (∃ k h, ⌜ v = immV _ ⌝ ∗ _)%I).
          iExists k, h.
          iSplit; first done.
          iExact "Hcont".

        * by iIntros (?) "(%k & %h & % & _)".

      + iIntros (w f') "(%k & %h & -> & Hcont)".
        iSimpl.
        iApply ewp_value.
        apply of_to_val => //.
        (* iSplitL; last by instantiate (1 := λ f, ⌜ f = Build_frame _ _ ⌝%I). *)
        (* iIntros (f') "->". *)
        iIntros (LI HLI).
        move/lfilledP in HLI; inversion HLI; subst.
        inversion H8; subst.
        iSimpl.
        iApply ewp_wand.
        iApply ewp_label_value.
        done.
        by instantiate (1 := λ v f, ⌜ v = immV _ ⌝%I).
        iIntros (w ?) "->".
        instantiate (1 := λ v f, (∃ k h, ⌜ v = immV _ ⌝ ∗ _)%I).
        iExists k, h.
        iSplit; first done.
        iExact "Hcont".

      + by iIntros (?) "(% & % & % & _)".


    - iIntros (w f') "(%k & %h & -> & Hcont)".
      iApply ewp_frame_value.
      rewrite to_of_val => //.
      done. done. 

    - iIntros (?) "(% & % & % & _)" => //.
  Qed. 

End Example1.
        
          

          

          
          
          
