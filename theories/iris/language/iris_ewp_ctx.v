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
  f f' Ψ (Φ : val -> iProp Σ) (i : nat) (lh : lholed) : iProp Σ := 
  ∀ LI, ⌜lfilled i lh e LI⌝ -∗ EWP LI UNDER f @ E <| Ψ |> {{ Φ ; f' }}.


Definition ewp_wasm_frame `{!wasmG Σ}
  (* s : stuckness*) (E : coPset) (es : language.expr wasm_lang)
  f h Ψ (Φ : val -> iProp Σ) (n: nat) (f': frame) : iProp Σ :=
  
  EWP [AI_local n f' es] UNDER f @ E <| Ψ |> {{ Φ ; h }}.

Definition ewp_wasm_ctx_frame `{!wasmG Σ}
          (*s : stuckness *) (E : coPset) (es : language.expr wasm_lang)
  f' h Ψ (Φ : val -> iProp Σ) (n: nat) (f: frame) (i : nat) (lh : lholed) : iProp Σ :=
  
  ∀ LI, ⌜lfilled i lh es LI⌝ -∗ EWP [AI_local n f LI] UNDER f' @ E <| Ψ |> {{ Φ ; h }}.


(* Notations *)

(* Context wps for blocks *)
 Notation "'EWP' e 'UNDER' f @ E 'CTX' i ; lh <| Ψ |> {{ Φ ; h } }" := (ewp_wasm_ctx E e%E f h Ψ Φ i lh)
  (at level 20, e, h, f, Ψ, Φ, lh at level 200, only parsing) : bi_scope. 
Notation "'EWP' e 'UNDER' f @ E 'CTX' i ; lh {{ Φ ; h } }" := (ewp_wasm_ctx E e%E f h ( λ _, iProt_bottom ) Φ i lh)
  (at level 20, e, h, f, Φ, lh at level 200, only parsing) : bi_scope.
 Notation "'EWP' e 'UNDER' f 'CTX' i ; lh <| Ψ |> {{ Φ ; h } }" := (ewp_wasm_ctx ⊤ e%E f h Ψ Φ i lh)
  (at level 20, e, h, f, Ψ, Φ, lh at level 200, only parsing) : bi_scope. 
Notation "'EWP' e 'UNDER' f 'CTX' i ; lh {{ Φ ; h } }" := (ewp_wasm_ctx ⊤ e%E f h ( λ _, iProt_bottom ) Φ i lh)
                                              (at level 20, e, h, f, Φ, lh at level 200, only parsing) : bi_scope.

(* Empty context *)
 Notation "'EWP' e 'UNDER' f @ E 'CTX_EMPTY' <| Ψ |> {{ Φ ; h } }" := (ewp_wasm_ctx E e%E f h Ψ Φ 0 (LH_base [] []))
                                                         (at level 20, e, h, f, Ψ, Φ at level 200, only parsing) : bi_scope. 
Notation "'EWP' e 'UNDER' f @ E 'CTX_EMPTY' {{ Φ ; h } }" := (ewp_wasm_ctx E e%E f h (λ _, iProt_bottom) Φ 0 (LH_base [] []))
                                                 (at level 20, e, h, f, Φ at level 200, only parsing) : bi_scope.
 Notation "'EWP' e 'UNDER' f 'CTX_EMPTY' <| Ψ |> {{ Φ ; h } }" := (ewp_wasm_ctx ⊤ e%E f h Ψ Φ 0 (LH_base [] []))
                                                     (at level 20, e, h, f, Ψ, Φ at level 200, only parsing) : bi_scope. 
Notation "'EWP' e 'UNDER' f 'CTX_EMPTY' {{ Φ ; h } }" := (ewp_wasm_ctx ⊤ e%E f h (λ _, iProt_bottom) Φ 0 (LH_base [] []))
                                                 (at level 20, e, h, f, Φ at level 200, only parsing) : bi_scope.

(* With explicit v *)

 Notation "'EWP' e 'UNDER' f @ E 'CTX' i ; lh <| Ψ |> {{ v , Φ ; h } }" := (ewp_wasm_ctx E e%E f h Ψ (λ v, Φ) i lh)
  (at level 20, e, h, f, Ψ, Φ, lh at level 200, only parsing) : bi_scope. 
Notation "'EWP' e 'UNDER' f @ E 'CTX' i ; lh {{ v , Φ ; h } }" := (ewp_wasm_ctx E e%E f h (λ _, iProt_bottom) (λ v, Φ) i lh)
  (at level 20, e, h, f, Φ, lh at level 200, only parsing) : bi_scope.
 Notation "'EWP' e 'UNDER' f 'CTX' i ; lh <| Ψ |> {{ v , Φ ; h } }" := (ewp_wasm_ctx ⊤ e%E f h Ψ (λ v, Φ) i lh)
  (at level 20, e, h, f, Ψ, Φ, lh at level 200, only parsing) : bi_scope. 
Notation "'EWP' e 'UNDER' f 'CTX' i ; lh {{ v , Φ ; h } }" := (ewp_wasm_ctx ⊤ e%E f h (λ _, iProt_bottom) (λ v, Φ) i lh)
                                              (at level 20, e, h, f, Φ, lh at level 200, only parsing) : bi_scope.
 Notation "'EWP' e 'UNDER' f @ E 'CTX_EMPTY' <| Ψ |> {{ v , Φ ; h } }" := (ewp_wasm_ctx E e%E f h Ψ (λ v, Φ) 0 (LH_base [] []))
                                                         (at level 20, e, h, f, Ψ, Φ at level 200, only parsing) : bi_scope. 
Notation "'EWP' e 'UNDER' f @ E 'CTX_EMPTY' {{ v , Φ ; h } }" := (ewp_wasm_ctx E e%E f h (λ _, iProt_bottom) (λ v, Φ) 0 (LH_base [] []))
                                                 (at level 20, e, h, f, Φ at level 200, only parsing) : bi_scope.
 Notation "'EWP' e 'UNDER' f 'CTX_EMPTY' <| Ψ |> {{ v , Φ ; h } }" := (ewp_wasm_ctx ⊤ e%E f h Ψ (λ v, Φ) 0 (LH_base [] []))
                                                     (at level 20, e, h, f, Ψ, Φ at level 200, only parsing) : bi_scope. 
Notation "'EWP' e 'UNDER' f 'CTX_EMPTY' {{ v , Φ ; h } }" := (ewp_wasm_ctx ⊤ e%E f h (λ _, iProt_bottom) (λ v, Φ) 0 (LH_base [] []))
                                                 (at level 20, e, h, f, Φ at level 200, only parsing) : bi_scope.


(* Frame wps for Local *)

 Notation "'EWP' e 'UNDER' g @ E 'FRAME' n ; f <| Ψ |> {{ Φ ; h } }" := (ewp_wasm_frame E e%E g h Ψ Φ n f)
  (at level 20, e, h, g, Ψ, Φ, n, f at level 200, only parsing) : bi_scope. 

 Notation "'EWP' e 'UNDER' g @ E 'FRAME' n ; f <| Ψ |> {{ v , Q ; h } }" := (ewp_wasm_frame E e%E g h Ψ (λ v, Q) n f)
  (at level 20, e, h, g, Ψ, Q, n, f at level 200,
    format "'[hv' 'EWP'  e  '/' 'UNDER'  g  @  '[' '/' E  ']' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' <| '[' Ψ ']' |>  '/' {{  '[' v ,  '/' Q  ']'  ;  h  } } ']'") : bi_scope. 

 Notation "'EWP' e 'UNDER' g @ E 'FRAME' n ; f 'CTX' i ; lh <| Ψ |> {{ v , Q ; h } }" := (ewp_wasm_ctx_frame E e%E g h Ψ (λ v, Q) n f i lh)
  (at level 20, e, h, g, Q, lh at level 200,
   format "'[hv' 'EWP'  e  '/' 'UNDER'  g  @  '[' '/' E  ']' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' <| '[' Ψ ']' |> '/' {{  '[' v ,  '/' Q  ']'   ;  h  } } ']'") : bi_scope. 
 Notation "'EWP' e 'UNDER' g @ E 'FRAME' n ; f 'CTX_EMPTY' <| Ψ |> {{ v , Q ; h } }" := (ewp_wasm_ctx_frame E e%E g h Ψ (λ v, Q) n f 0 (LH_base [] []))
  (at level 20, e, h, g, Q at level 200,
    format "'[hv' 'EWP'  e  '/' 'UNDER'  g  @  '[' '/' E  ']' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX_EMPTY'  '/' <| '[' Ψ ']' |> '/' {{  '[' v ,  '/' Q  ']'  ;  h  } } ']'") : bi_scope. 

(* no Ψ *)
Notation "'EWP' e 'UNDER' g @ E 'FRAME' n ; f {{ Φ ; h } }" := (ewp_wasm_frame E e%E g h (λ _, iProt_bottom) Φ n f)
  (at level 20, e, h, g, Φ, n, f at level 200, only parsing) : bi_scope.

Notation "'EWP' e 'UNDER' g @ E 'FRAME' n ; f {{ v , Q ; h } }" := (ewp_wasm_frame E e%E g h (λ _, iProt_bottom) (λ v, Q) n f)
  (at level 20, e, h, g, Q, n, f at level 200,
    format "'[hv' 'EWP'  e  '/' 'UNDER'  g  @  '[' '/' E  ']' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' {{  '[' v ,  '/' Q  ']'  ;  h  } } ']'") : bi_scope.

Notation "'EWP' e 'UNDER' g @ E 'FRAME' n ; f 'CTX' i ; lh {{ v , Q ; h } }" := (ewp_wasm_ctx_frame E e%E g h (λ _, iProt_bottom) (λ v, Q) n f i lh)
  (at level 20, e, h, g, Q, lh at level 200,
   format "'[hv' 'EWP'  e  '/' 'UNDER'  g  @  '[' '/' E  ']' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' {{  '[' v ,  '/' Q  ']'  ;  h  } } ']'") : bi_scope.
Notation "'EWP' e 'UNDER' g @ E 'FRAME' n ; f 'CTX_EMPTY' {{ v , Q ; h } }" := (ewp_wasm_ctx_frame E e%E g h (λ _, iProt_bottom) (λ v, Q) n f 0 (LH_base [] []))
  (at level 20, e, h, g, Q at level 200,
    format "'[hv' 'EWP'  e  '/' 'UNDER'  g  @  '[' '/' E  ']' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX_EMPTY'  '/' {{  '[' v ,  '/' Q  ']'  ;  h  } } ']'") : bi_scope.

(* no @E *)
 Notation "'EWP' e 'UNDER' g 'FRAME' n ; f <| Ψ |> {{ Φ ; h } }" := (ewp_wasm_frame ⊤ e%E g h Ψ Φ n f)
  (at level 20, e, h, g, Ψ, Φ, n, f at level 200, only parsing) : bi_scope.

Notation "'EWP' e 'UNDER' g 'FRAME' n ; f <| Ψ |> {{ v , Q ; h } }" := (ewp_wasm_frame ⊤ e%E g h Ψ (λ v, Q) n f)
  (at level 20, e, h, g, Ψ, Q, n, f at level 200,
    format "'[hv' 'EWP'  e  '/' 'UNDER'  g  'FRAME'  '/' '[' n ;  '/' f ']'  '/' <| '[' Ψ ']' |>  '/' {{  '[' v ,  '/' Q  ']'  ;  h  } } ']'") : bi_scope.

Notation "'EWP' e 'UNDER' g 'FRAME' n ; f 'CTX' i ; lh <| Ψ |> {{ v , Q ; h } }" := (ewp_wasm_ctx_frame ⊤ e%E g h Ψ (λ v, Q) n f i lh)
  (at level 20, e, h, g, Q, lh at level 200,
   format "'[hv' 'EWP'  e  '/' 'UNDER'  g  'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' <| '[' Ψ ']' |> '/' {{  '[' v ,  '/' Q  ']'  ;  h  } } ']'") : bi_scope.
Notation "'EWP' e 'UNDER' g 'FRAME' n ; f 'CTX_EMPTY' <| Ψ |> {{ v , Q ; h } }" := (ewp_wasm_ctx_frame ⊤ e%E g h Ψ (λ v, Q) n f 0 (LH_base [] []))
  (at level 20, e, h, g, Q at level 200,
    format "'[hv' 'EWP'  e  '/' 'UNDER'  g  'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX_EMPTY'  '/' <| '[' Ψ ']' |> '/' {{  '[' v ,  '/' Q  ']'  ;  h  } } ']'") : bi_scope. 

(* no Ψ, no @E *)
Notation "'EWP' e 'UNDER' g 'FRAME' n ; f {{ Φ ; h } }" := (ewp_wasm_frame ⊤ e%E g h (λ _, iProt_bottom) Φ n f)
  (at level 20, e, h, f, Φ, n, g at level 200, only parsing) : bi_scope.

Notation "'EWP' e 'UNDER' g 'FRAME' n ; f {{ v , Q ; h } }" := (ewp_wasm_frame ⊤ e%E g h (λ _, iProt_bottom) (λ v, Q) n f)
  (at level 20, e, h, g, Q, n, f at level 200,
    format "'[hv' 'EWP'  e  '/' 'UNDER'  g  'FRAME'  '/' '[' n ;  '/' f ']'  '/' {{  '[' v ,  '/' Q  ']'  ;  h  } } ']'") : bi_scope.

Notation "'EWP' e 'UNDER' g 'FRAME' n ; f 'CTX' i ; lh {{ v , Q ; h } }" := (ewp_wasm_ctx_frame ⊤ e%E g h (λ _, iProt_bottom) (λ v, Q) n f i lh)
  (at level 20, e, h, g, Q, lh at level 200,
   format "'[hv' 'EWP'  e  '/' 'UNDER'  g  'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' {{  '[' v ,  '/' Q  ']'  ;  h  } } ']'") : bi_scope.
Notation "'EWP' e 'UNDER' g 'FRAME' n ; f 'CTX_EMPTY' {{ v , Q ; h } }" := (ewp_wasm_ctx_frame ⊤ e%E g h (λ _, iProt_bottom) (λ v, Q) n f 0 (LH_base [] []))
  (at level 20, e, h, g, Q at level 200,
   format "'[hv' 'EWP'  e  '/' 'UNDER'  g  'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX_EMPTY'  '/' {{  '[' v ,  '/' Q  ']'  ;  h  } } ']'") : bi_scope.



(* Tactics *)
Ltac only_one_reduction H :=
  let Hstart := fresh "Hstart" in
  let a := fresh "a" in
  let Hstart1 := fresh "Hstart" in
  let Hstart2 := fresh "Hstart" in
  let Hσ := fresh "Hσ" in 
  eapply reduce_det in H
      as [Hσ [[? ?] | [ (? & Hstart) | (? & ? & ? & Hstart & Hstart1 & Hstart2 & ?)]]] ;
  last (by repeat econstructor) ;
  first (try inversion Hσ; subst => /=; iFrame => //);
  try by repeat (unfold first_instr in Hstart ; simpl in Hstart) ; inversion Hstart.
