
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
From Wasm.iris.examples.effects Require Import generator.
From Wasm.iris.examples.effects Require Import generator_module.


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

Definition sum_until_client_100 :=
  [BI_const $ xx 100; BI_call 0].

Definition sum_until_client_0:=
  [BI_const $ xx 0; BI_call 0].

Definition sum_until_client_neg :=
  [BI_const $ xx (-4294967293); BI_call 0].

Section GeneratorClient.
  Context `{!wasmG Σ, !hvisG Σ, !hmsG Σ, !hasG Σ, !ghostG Σ}.
  

  Definition sum_until_client tag_exp_addr generator_exp_addr sum_until_exp_addr mod_addr n :=
    [ ID_instantiate [ tag_exp_addr; generator_exp_addr; sum_until_exp_addr ] mod_addr [];
H_invoke sum_until_exp_addr [VAL_int32 n]
    ].

  Notation "{{{{ P }}}} es {{{{ v , Q }}}}" :=
    (□ ∀ Φ, P -∗ (∀ v, Q -∗ Φ v) -∗ WP (es : host_expr) @ NotStuck ; ⊤ {{ v, Φ v }})%I (at level 50).


  Lemma instantiate_client tag_exp_addr naturals_exp_addr sum_until_exp_addr mod_addr n :
    ⊢ {{{{
        mod_addr ↪[mods] generator_module ∗
        (∃ exp0, tag_exp_addr ↪[vis] exp0) ∗
        (∃ exp1, naturals_exp_addr ↪[vis] exp1) ∗
        (∃ exp2, sum_until_exp_addr ↪[vis] exp2)
      }}}}
        ((sum_until_client tag_exp_addr naturals_exp_addr sum_until_exp_addr mod_addr n, [], empty_frame) : host_expr)
      {{{{ w, ⌜w = (immHV [VAL_num (VAL_int32 $ Sum_until_i32 n)], empty_frame)⌝ }}}}.
  Proof.
    iIntros "!>" (Φ) "(Hmod & Hexp0 & Hexp1 & Hexp2 ) HΦ".

    (* instantiate generator module *)
    iApply (wp_seq_host_nostart with "[] Hmod [Hexp0 Hexp1 Hexp2]").
    done. done.
    2:{
      iIntros "Hmod".
      iApply (instantiate_generator with "[$Hmod $Hexp0 $Hexp1 $Hexp2]").
      iIntros (x) "(-> & Hmod & H)".
      iFrame.
      instantiate (1 := λ v, (⌜ v = (immHV [], empty_frame) ⌝ ∗ _)%I).
      iSplit; first done.
      iExact "H".
    }
    by iIntros (?) "[% _]".
    iIntros (w f) "(%Heq & %addr_naturals & %addr_sum_until & %addr_tag & %name_tag & %name_naturals & %name_sum_until & %cl_naturals & %cl_sum_until & Hexp0 & Hexp1 & Hexp2 & %Htypenaturals & %Htypesum_until & Hwfnaturals & Hwfsum_until & Htag & Hnaturals_spec & Hsum_until_spec) Hmod".
    iDestruct (pointsto_ne with "Hwfnaturals Hwfsum_until") as %Hne.
    inversion Heq; subst. clear Heq.

    replace [] with (v_to_e_list []); last done.
    iApply (wp_invoke_host with "[$] [$Hwfsum_until]").
    done.
    done.
    iIntros "!> Hexpsum_until Hwfsum_until".

    iApply wp_lift_wasm.

    (* Prove the specification of sum_until *)
    simpl.
    iApply (ewp_wand with "[-HΦ]").
    iApply ("Hsum_until_spec" with "Htag Hwfsum_until Hwfnaturals").
    iIntros (?? [<- ->]); simpl.
    iApply wp_value; first done.
    by iApply "HΦ".
  Qed.

End GeneratorClient.





Section generator_client_adequacy.

  Context (Σ: gFunctors).
  Context {inv_preg: invGpreS Σ}.
  Context {na_invg: na_invG Σ}.
  Context {func_preg: gen_heapGpreS N function_closure Σ}.
  Context {tab_preg: gen_heapGpreS (N*N) funcelem Σ}.
  Context {tabsize_preg: gen_heapGpreS N nat Σ}.
  Context {tablimits_preg: gen_heapGpreS N (option N) Σ}.
  Context {mem_preg: gen_heapGpreS (N*N) byte Σ}.
  Context {memsize_preg: gen_heapGpreS N N Σ}.
  Context {memlimit_preg: gen_heapGpreS N (option N) Σ}.
  Context {glob_preg: gen_heapGpreS N global Σ}.
  Context {vis_preg: gen_heapGpreS N module_export Σ}.
  Context {ms_preg: gen_heapGpreS N module Σ}.
  Context {has_preg: gen_heapGpreS N host_action Σ}.
  Context {tag_preg: gen_heapGpreS N function_type Σ}.
  Context {cont_preg: gen_heapGpreS N continuation_resource Σ}.
  Context {exn_preg: gen_heapGpreS N exception Σ}.
  Context {ghost_preg: ghostG Σ}.

  Definition near_empty_store : store_record := Build_store_record [] [] [] [] [ ] [] [].

  (* The following addresses could be generalised, as long as there are
     no duplicates *)
  Definition tag_exp_addr := 0%N.
  Definition naturals_exp_addr := 1%N.
  Definition sum_until_exp_addr := 4%N.

  Definition mod_addr := 0%N.

  
  Definition exports: vi_store :=
     (<[ tag_exp_addr := {| modexp_name := [Byte.x00]; modexp_desc := MED_global (Mk_globalidx (N.to_nat 0)) |} ]> (
    (<[ naturals_exp_addr := {| modexp_name := [Byte.x00]; modexp_desc := MED_global (Mk_globalidx (N.to_nat 0)) |} ]> (
      <[ sum_until_exp_addr := {| modexp_name := [Byte.x00]; modexp_desc := MED_global (Mk_globalidx (N.to_nat 0)) |} ]> ∅)))).
  
  Lemma generator_client_adequacy n he' S' V' M' HA':
    rtc erased_step (([ (sum_until_client tag_exp_addr naturals_exp_addr sum_until_exp_addr mod_addr n, [], empty_frame) ],
                       (near_empty_store, exports, [generator_module], [] )) : cfg wasm_host_lang)
      ([he'] , (S', V', M', HA')) ->
    (forall v, iris_host.to_val he' = Some v ->
          v = (immHV [VAL_num (VAL_int32 $ Sum_until_i32 n)], empty_frame)).
  Proof.
    intros Hstep.
    pose proof (wp_adequacy Σ wasm_host_lang NotStuck
                  (sum_until_client tag_exp_addr naturals_exp_addr sum_until_exp_addr mod_addr n, [], empty_frame)
                  (near_empty_store, exports, [generator_module], [] )
                  (λ v,   v = (immHV [VAL_num (VAL_int32 $ Sum_until_i32 n)], empty_frame) 
      )).
    simpl in H.
    
    eassert _.
    { apply H.
      iIntros (Hinv κs).
      iMod (gen_heap_init (∅:gmap N function_closure)) as (func_heapg) "[Hfunc_ctx _]".
      iMod (gen_heap_init (∅:gmap (N*N) funcelem)) as (tab_heapg) "[Htab_ctx _]".
      iMod (gen_heap_init (∅:gmap N nat)) as (tabsize_heapg) "[Htabsize_ctx _]".
      iMod (@gen_heap_init _ _ _ _ _ tablimits_preg (∅:gmap N (option N))) as (tablimit_heapg) "[Htablimit_ctx _]".
      iMod (gen_heap_init (∅:gmap (N*N) byte)) as (mem_heapg) "[Hmem_ctx _]".
      iMod (gen_heap_init (∅:gmap N N)) as (memsize_heapg) "[Hmemsize_ctx _]".
      iMod (@gen_heap_init _ _ _ _ _ memlimit_preg (∅:gmap N (option N))) as (memlimit_heapg) "[Hmemlimit_ctx _]".
      iMod (gen_heap_init (∅:gmap N global)) as (global_heapg) "[Hglobal_ctx _]".
      iMod (gen_heap_init (∅: gmap N function_type)) as (tag_heapg) "[Htag_ctx _]".
      iMod (gen_heap_init (∅: gmap N continuation_resource)) as (cont_heapg) "[Hcont_ctx _]".
      iMod (gen_heap_init (∅: gmap N exception)) as (exn_heapg) "[Hexn_ctx _]".
      
      apply (@gen_heapGpreS_heap) in vis_preg as vis_heapg.
      iMod (ghost_map_alloc (∅:gmap N module_export)) as (γvis) "[Hvis_ctx _]".
      apply (@gen_heapGpreS_heap) in ms_preg as ms_heapg.
      iMod (ghost_map_alloc (∅:gmap N module)) as (γms) "[Hms_ctx _]".
      apply (@gen_heapGpreS_heap) in has_preg as has_heapg.
      iMod (ghost_map_alloc (∅:gmap N host_action)) as (γhas) "[Hhas_ctx _]".

      iMod (@na_alloc Σ na_invg) as (logrel_nais) "Hna".
      pose wasmg := WasmG Σ Hinv func_heapg cont_heapg exn_heapg tag_heapg tab_heapg tabsize_heapg
                          tablimit_heapg mem_heapg memsize_heapg memlimit_heapg
                          global_heapg.
      pose visgg := HVisG Σ vis_heapg γvis.
      pose msgg := HMsG Σ ms_heapg γms.
      pose hasgg := HAsG Σ has_heapg γhas.
      pose logrel_na_invs := Build_logrel_na_invs _ na_invg logrel_nais.

      iMod (ghost_map_insert sum_until_exp_addr {| modexp_name := [Byte.x00]; modexp_desc := MED_global (Mk_globalidx (N.to_nat 0)) |}
             with "Hvis_ctx") as "[Hvis_ctx Hv1]";[auto|].
      iMod (ghost_map_insert naturals_exp_addr {| modexp_name := [Byte.x00]; modexp_desc := MED_global (Mk_globalidx (N.to_nat 0)) |}
             with "Hvis_ctx") as "[Hvis_ctx Hv2]";[auto|].
      iMod (ghost_map_insert tag_exp_addr {| modexp_name := [Byte.x00]; modexp_desc := MED_global (Mk_globalidx (N.to_nat 0)) |}
             with "Hvis_ctx") as "[Hvis_ctx Hv3]";[auto|].
      iMod (ghost_map_insert mod_addr generator_module with "Hms_ctx") as "[Hms_ctx Hm0]";[auto|].
      
      iDestruct (instantiate_client $! (λ v, ⌜ v = (immHV [VAL_num (VAL_int32 $ Sum_until_i32 n)], empty_frame) ⌝%I) 
                  with "[$Hm0 Hv1 Hv2 Hv3]") as "HH".
      iFrame. 

      iDestruct ("HH" with "[]") as "HH";[auto|].
      iModIntro.
      iExists _,_.
      iFrame "HH".
      iFrame.
    }
    intros v Hval.
    destruct X. eapply adequate_result with (t2 := []).
    apply iris_host.of_to_val in Hval as <-. eauto.
  Qed.

End generator_client_adequacy.

Theorem generalor_example:
  forall n he' S' V' M' HA',
    rtc erased_step (([ (sum_until_client tag_exp_addr naturals_exp_addr sum_until_exp_addr mod_addr n, [], empty_frame) ],
                       (near_empty_store, exports, [generator_module], [] )) : cfg wasm_host_lang)
      ([he'] , (S', V', M', HA')) ->
    (forall v, iris_host.to_val he' = Some v ->
          v = (immHV [VAL_num (VAL_int32 $ Sum_until_i32 n)], empty_frame)).
Proof.
   set (Σ := #[invΣ;
              na_invΣ;
              gen_heapΣ N function_closure;
              gen_heapΣ (N*N) funcelem;
              gen_heapΣ N nat;
              gen_heapΣ N (option N);
              gen_heapΣ (N*N) byte;
              gen_heapΣ N N;
              gen_heapΣ N (option N);
              gen_heapΣ N global;
              gen_heapΣ N module_export;
              gen_heapΣ N module;
               gen_heapΣ N host_action;
               gen_heapΣ N function_type;
               gen_heapΣ N continuation_resource;
               gen_heapΣ N exception;
               ghostΣ
      ]).
  eapply (@generator_client_adequacy Σ); typeclasses eauto.
Qed.

