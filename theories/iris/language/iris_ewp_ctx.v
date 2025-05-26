From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language weakestpre.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From Wasm.iris.helpers Require Import iris_properties.
From Wasm Require Import stdpp_aux (* datatypes common operations properties memory_list *).
From Wasm.iris.language.iris Require Export iris_locations iris.
From Wasm.iris.language Require Export iris_ewp.

(* A Definition of a context dependent WP for WASM expressions *)



Definition ewp_wasm_ctx `{!wasmG Σ}
          (* s : stuckness *) (E : coPset) (e : language.expr wasm_lang)
          Ψ (Φ : val -> iProp Σ) (i : nat) (lh : lholed) : iProp Σ := 
  ∀ LI, ⌜lfilled i lh e LI⌝ -∗ EWP LI @ E <| Ψ |> {{ Φ }}.


Definition ewp_wasm_frame `{!wasmG Σ}
  (* s : stuckness*) (E : coPset) (es : language.expr wasm_lang)
          Ψ (Φ : val -> iProp Σ) (n: nat) (f: frame) : iProp Σ :=
  
  EWP [AI_local n f es] @ E <| Ψ |> {{ Φ }}.

Definition ewp_wasm_ctx_frame `{!wasmG Σ}
          (*s : stuckness *) (E : coPset) (es : language.expr wasm_lang)
  Ψ (Φ : val -> iProp Σ) (n: nat) (f: frame) (i : nat) (lh : lholed) : iProp Σ :=
  
  ∀ LI, ⌜lfilled i lh es LI⌝ -∗ EWP [AI_local n f LI] @ E <| Ψ |> {{ Φ }}.


(* Notations *)

(* Context wps for blocks *)
Notation "'EWP' e @ E 'CTX' i ; lh <| Ψ |> {{ Φ } }" := (ewp_wasm_ctx E e%E Ψ Φ i lh)
  (at level 20, e, Ψ, Φ, lh at level 200, only parsing) : bi_scope.
Notation "'EWP' e @ E 'CTX' i ; lh {{ Φ } }" := (ewp_wasm_ctx E e%E (λ _, iProt_bottom) Φ i lh)
  (at level 20, e, Φ, lh at level 200, only parsing) : bi_scope.
Notation "'EWP' e 'CTX' i ; lh <| Ψ |> {{ Φ } }" := (ewp_wasm_ctx ⊤ e%E Ψ Φ i lh)
  (at level 20, e, Ψ, Φ, lh at level 200, only parsing) : bi_scope.
Notation "'EWP' e 'CTX' i ; lh {{ Φ } }" := (ewp_wasm_ctx ⊤ e%E (λ _, iProt_bottom) Φ i lh)
                                              (at level 20, e, Φ, lh at level 200, only parsing) : bi_scope.

(* Empty context *)
Notation "'EWP' e @ E 'CTX_EMPTY' <| Ψ |> {{ Φ } }" := (ewp_wasm_ctx E e%E Ψ Φ 0 (LH_base [] []))
                                                         (at level 20, e, Ψ, Φ at level 200, only parsing) : bi_scope.
Notation "'EWP' e @ E 'CTX_EMPTY' {{ Φ } }" := (ewp_wasm_ctx E e%E (λ _, iProt_bottom) Φ 0 (LH_base [] []))
                                                 (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'EWP' e 'CTX_EMPTY' <| Ψ |> {{ Φ } }" := (ewp_wasm_ctx ⊤ e%E Ψ Φ 0 (LH_base [] []))
                                                     (at level 20, e, Ψ, Φ at level 200, only parsing) : bi_scope.
Notation "'EWP' e 'CTX_EMPTY' {{ Φ } }" := (ewp_wasm_ctx ⊤ e%E (λ _, iProt_bottom) Φ 0 (LH_base [] []))
                                                 (at level 20, e, Φ at level 200, only parsing) : bi_scope.

(* With explicit v *)

Notation "'EWP' e @ E 'CTX' i ; lh <| Ψ |> {{ v , Φ } }" := (ewp_wasm_ctx E e%E Ψ (λ v, Φ) i lh)
  (at level 20, e, Ψ, Φ, lh at level 200, only parsing) : bi_scope.
Notation "'EWP' e @ E 'CTX' i ; lh {{ v , Φ } }" := (ewp_wasm_ctx E e%E (λ _, iProt_bottom) (λ v, Φ) i lh)
  (at level 20, e, Φ, lh at level 200, only parsing) : bi_scope.
Notation "'EWP' e 'CTX' i ; lh <| Ψ |> {{ v , Φ } }" := (ewp_wasm_ctx ⊤ e%E Ψ (λ v, Φ) i lh)
  (at level 20, e, Ψ, Φ, lh at level 200, only parsing) : bi_scope.
Notation "'EWP' e 'CTX' i ; lh {{ v , Φ } }" := (ewp_wasm_ctx ⊤ e%E (λ _, iProt_bottom) (λ v, Φ) i lh)
                                              (at level 20, e, Φ, lh at level 200, only parsing) : bi_scope.
Notation "'EWP' e @ E 'CTX_EMPTY' <| Ψ |> {{ v , Φ } }" := (ewp_wasm_ctx E e%E Ψ (λ v, Φ) 0 (LH_base [] []))
                                                         (at level 20, e, Ψ, Φ at level 200, only parsing) : bi_scope.
Notation "'EWP' e @ E 'CTX_EMPTY' {{ v , Φ } }" := (ewp_wasm_ctx E e%E (λ _, iProt_bottom) (λ v, Φ) 0 (LH_base [] []))
                                                 (at level 20, e, Φ at level 200, only parsing) : bi_scope.
Notation "'EWP' e 'CTX_EMPTY' <| Ψ |> {{ v , Φ } }" := (ewp_wasm_ctx ⊤ e%E Ψ (λ v, Φ) 0 (LH_base [] []))
                                                     (at level 20, e, Ψ, Φ at level 200, only parsing) : bi_scope.
Notation "'EWP' e 'CTX_EMPTY' {{ v , Φ } }" := (ewp_wasm_ctx ⊤ e%E (λ _, iProt_bottom) (λ v, Φ) 0 (LH_base [] []))
                                                 (at level 20, e, Φ at level 200, only parsing) : bi_scope.


(* Frame wps for Local *)

Notation "'EWP' e @ E 'FRAME' n ; f <| Ψ |> {{ Φ } }" := (ewp_wasm_frame E e%E Ψ Φ n f)
  (at level 20, e, Ψ, Φ, n, f at level 200, only parsing) : bi_scope.

Notation "'EWP' e @ E 'FRAME' n ; f <| Ψ |> {{ v , Q } }" := (ewp_wasm_frame E e%E Ψ (λ v, Q) n f)
  (at level 20, e, Ψ, Q, n, f at level 200,
    format "'[hv' 'EWP'  e  '/' @  '[' '/' E  ']' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' <| '[' Ψ ']' |>  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

Notation "'EWP' e @ E 'FRAME' n ; f 'CTX' i ; lh <| Ψ |> {{ v , Q } }" := (ewp_wasm_ctx_frame E e%E Ψ (λ v, Q) n f i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'EWP'  e  '/' @  '[' '/' E  ']' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' <| '[' Ψ ']' |> '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'EWP' e @ E 'FRAME' n ; f 'CTX_EMPTY' <| Ψ |> {{ v , Q } }" := (ewp_wasm_ctx_frame E e%E Ψ (λ v, Q) n f 0 (LH_base [] []))
  (at level 20, e, Q at level 200,
    format "'[hv' 'EWP'  e  '/' @  '[' '/' E  ']' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX_EMPTY'  '/' <| '[' Ψ ']' |> '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

(* no Ψ *)
Notation "'EWP' e @ E 'FRAME' n ; f {{ Φ } }" := (ewp_wasm_frame E e%E (λ _, iProt_bottom) Φ n f)
  (at level 20, e, Φ, n, f at level 200, only parsing) : bi_scope.

Notation "'EWP' e @ E 'FRAME' n ; f {{ v , Q } }" := (ewp_wasm_frame E e%E (λ _, iProt_bottom) (λ v, Q) n f)
  (at level 20, e, Q, n, f at level 200,
    format "'[hv' 'EWP'  e  '/' @  '[' '/' E  ']' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

Notation "'EWP' e @ E 'FRAME' n ; f 'CTX' i ; lh {{ v , Q } }" := (ewp_wasm_ctx_frame E e%E (λ _, iProt_bottom) (λ v, Q) n f i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'EWP'  e  '/' @  '[' '/' E  ']' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'EWP' e @ E 'FRAME' n ; f 'CTX_EMPTY' {{ v , Q } }" := (ewp_wasm_ctx_frame E e%E (λ _, iProt_bottom) (λ v, Q) n f 0 (LH_base [] []))
  (at level 20, e, Q at level 200,
    format "'[hv' 'EWP'  e  '/' @  '[' '/' E  ']' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX_EMPTY'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

(* no @E *)
Notation "'EWP' e 'FRAME' n ; f <| Ψ |> {{ Φ } }" := (ewp_wasm_frame ⊤ e%E Ψ Φ n f)
  (at level 20, e, Ψ, Φ, n, f at level 200, only parsing) : bi_scope.

Notation "'EWP' e 'FRAME' n ; f <| Ψ |> {{ v , Q } }" := (ewp_wasm_frame ⊤ e%E Ψ (λ v, Q) n f)
  (at level 20, e, Ψ, Q, n, f at level 200,
    format "'[hv' 'EWP'  e  '/' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' <| '[' Ψ ']' |>  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

Notation "'EWP' e 'FRAME' n ; f 'CTX' i ; lh <| Ψ |> {{ v , Q } }" := (ewp_wasm_ctx_frame ⊤ e%E Ψ (λ v, Q) n f i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'EWP'  e  '/' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' <| '[' Ψ ']' |> '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'EWP' e 'FRAME' n ; f 'CTX_EMPTY' <| Ψ |> {{ v , Q } }" := (ewp_wasm_ctx_frame ⊤ e%E Ψ (λ v, Q) n f 0 (LH_base [] []))
  (at level 20, e, Q at level 200,
    format "'[hv' 'EWP'  e  '/' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX_EMPTY'  '/' <| '[' Ψ ']' |> '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

(* no Ψ, no @E *)
Notation "'EWP' e 'FRAME' n ; f {{ Φ } }" := (ewp_wasm_frame ⊤ e%E (λ _, iProt_bottom) Φ n f)
  (at level 20, e, Φ, n, f at level 200, only parsing) : bi_scope.

Notation "'EWP' e 'FRAME' n ; f {{ v , Q } }" := (ewp_wasm_frame ⊤ e%E (λ _, iProt_bottom) (λ v, Q) n f)
  (at level 20, e, Q, n, f at level 200,
    format "'[hv' 'EWP'  e  '/' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

Notation "'EWP' e 'FRAME' n ; f 'CTX' i ; lh {{ v , Q } }" := (ewp_wasm_ctx_frame ⊤ e%E (λ _, iProt_bottom) (λ v, Q) n f i lh)
  (at level 20, e, Q, lh at level 200,
   format "'[hv' 'EWP'  e  '/' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.
Notation "'EWP' e 'FRAME' n ; f 'CTX_EMPTY' {{ v , Q } }" := (ewp_wasm_ctx_frame ⊤ e%E (λ _, iProt_bottom) (λ v, Q) n f 0 (LH_base [] []))
  (at level 20, e, Q at level 200,
   format "'[hv' 'EWP'  e  '/' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX_EMPTY'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.



(* Tactics *)
Ltac only_one_reduction H :=
  let Hstart := fresh "Hstart" in
  let a := fresh "a" in
  let Hstart1 := fresh "Hstart" in
  let Hstart2 := fresh "Hstart" in
  let Hσ := fresh "Hσ" in 
  eapply reduce_det in H
      as [H | [ [? Hstart] | (* [ [a [cl [tf [h [i0 [Hstart [Hnth Hcl]]]]]]] | *) (? & ? & ? & Hstart & Hstart1 & Hstart2 & Hσ)(* ] *)]] ;
  last (by repeat econstructor) ;
  first (try inversion H ; subst ; clear H => /=; match goal with [f: frame |- _] => iExists f; iFrame; by iIntros | _ => idtac end) ;
  try by repeat (unfold first_instr in Hstart ; simpl in Hstart) ; inversion Hstart.
