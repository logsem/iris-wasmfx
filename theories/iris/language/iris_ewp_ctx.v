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
          (* s : stuckness *) (E : coPset) (e : expr0)
  f Ψ (Φ : val0 -> frame -> iProp Σ) (i : nat) (lh : lholed) : iProp Σ := 
  ∀ LI, ⌜lfilled i lh e LI⌝ -∗ EWP LI UNDER f @ E <| Ψ |> {{ Φ }}.


Definition ewp_wasm_frame `{!wasmG Σ}
  (* s : stuckness*) (E : coPset) (es : expr0)
  f Ψ (Φ : val0 -> frame -> iProp Σ) (n: nat) (f': frame) : iProp Σ :=
  
  EWP [AI_local n f' es] UNDER f @ E <| Ψ |> {{ Φ }}.

Definition ewp_wasm_ctx_frame `{!wasmG Σ}
          (*s : stuckness *) (E : coPset) (es : expr0)
  f' Ψ (Φ : val0 -> frame -> iProp Σ) (n: nat) (f: frame) (i : nat) (lh : lholed) : iProp Σ :=
  
  ∀ LI, ⌜lfilled i lh es LI⌝ -∗ EWP [AI_local n f LI] UNDER f' @ E <| Ψ |> {{ Φ }}.


(* Notations *)

(* Context wps for blocks *)
 Notation "'EWP' e 'UNDER' f @ E 'CTX' i ; lh <| Ψ |> {{ Φ } }" := (ewp_wasm_ctx E e%E f Ψ Φ i lh)
  (at level 20, e, f, Ψ, Φ, lh at level 200, only parsing) : bi_scope. 
Notation "'EWP' e 'UNDER' f @ E 'CTX' i ; lh {{ Φ } }" := (ewp_wasm_ctx E e%E f ( λ _, iProt_bottom ) Φ i lh)
  (at level 20, e, f, Φ, lh at level 200, only parsing) : bi_scope.
 Notation "'EWP' e 'UNDER' f 'CTX' i ; lh <| Ψ |> {{ Φ } }" := (ewp_wasm_ctx ⊤ e%E f Ψ Φ i lh)
  (at level 20, e, f, Ψ, Φ, lh at level 200, only parsing) : bi_scope. 
Notation "'EWP' e 'UNDER' f 'CTX' i ; lh {{ Φ } }" := (ewp_wasm_ctx ⊤ e%E f ( λ _, iProt_bottom ) Φ i lh)
                                              (at level 20, e, f, Φ, lh at level 200, only parsing) : bi_scope.

(* Empty context *)
 Notation "'EWP' e 'UNDER' f @ E 'CTX_EMPTY' <| Ψ |> {{ Φ } }" := (ewp_wasm_ctx E e%E f Ψ Φ 0 (LH_base [] []))
                                                         (at level 20, e, f, Ψ, Φ at level 200, only parsing) : bi_scope. 
Notation "'EWP' e 'UNDER' f @ E 'CTX_EMPTY' {{ Φ } }" := (ewp_wasm_ctx E e%E f (λ _, iProt_bottom) Φ 0 (LH_base [] []))
                                                 (at level 20, e, f, Φ at level 200, only parsing) : bi_scope.
 Notation "'EWP' e 'UNDER' f 'CTX_EMPTY' <| Ψ |> {{ Φ } }" := (ewp_wasm_ctx ⊤ e%E f Ψ Φ 0 (LH_base [] []))
                                                     (at level 20, e, f, Ψ, Φ at level 200, only parsing) : bi_scope. 
Notation "'EWP' e 'UNDER' f 'CTX_EMPTY' {{ Φ } }" := (ewp_wasm_ctx ⊤ e%E f (λ _, iProt_bottom) Φ 0 (LH_base [] []))
                                                 (at level 20, e, f, Φ at level 200, only parsing) : bi_scope.

(* With explicit v *)

 Notation "'EWP' e 'UNDER' f @ E 'CTX' i ; lh <| Ψ |> {{ v ; h , Φ } }" := (ewp_wasm_ctx E e%E f Ψ (λ v h, Φ) i lh)
  (at level 20, e, f, Ψ, Φ, lh at level 200, only parsing) : bi_scope. 
Notation "'EWP' e 'UNDER' f @ E 'CTX' i ; lh {{ v ; h , Φ } }" := (ewp_wasm_ctx E e%E f (λ _, iProt_bottom) (λ v h, Φ) i lh)
  (at level 20, e, f, Φ, lh at level 200, only parsing) : bi_scope.
 Notation "'EWP' e 'UNDER' f 'CTX' i ; lh <| Ψ |> {{ v ; h , Φ } }" := (ewp_wasm_ctx ⊤ e%E f Ψ (λ v h, Φ) i lh)
  (at level 20, e, f, Ψ, Φ, lh at level 200, only parsing) : bi_scope. 
Notation "'EWP' e 'UNDER' f 'CTX' i ; lh {{ v ; h , Φ } }" := (ewp_wasm_ctx ⊤ e%E f (λ _, iProt_bottom) (λ v h, Φ) i lh)
                                              (at level 20, e, f, Φ, lh at level 200, only parsing) : bi_scope.
 Notation "'EWP' e 'UNDER' f @ E 'CTX_EMPTY' <| Ψ |> {{ v ; h , Φ } }" := (ewp_wasm_ctx E e%E f Ψ (λ v h, Φ) 0 (LH_base [] []))
                                                         (at level 20, e, f, Ψ, Φ at level 200, only parsing) : bi_scope. 
Notation "'EWP' e 'UNDER' f @ E 'CTX_EMPTY' {{ v ; h , Φ } }" := (ewp_wasm_ctx E e%E f (λ _, iProt_bottom) (λ v, Φ) 0 (LH_base [] []))
                                                 (at level 20, e, f, Φ at level 200, only parsing) : bi_scope.
 Notation "'EWP' e 'UNDER' f 'CTX_EMPTY' <| Ψ |> {{ v ; h , Φ } }" := (ewp_wasm_ctx ⊤ e%E f Ψ (λ v h, Φ) 0 (LH_base [] []))
                                                     (at level 20, e, f, Ψ, Φ at level 200, only parsing) : bi_scope. 
Notation "'EWP' e 'UNDER' f 'CTX_EMPTY' {{ v ; h , Φ } }" := (ewp_wasm_ctx ⊤ e%E f (λ _, iProt_bottom) (λ v h, Φ) 0 (LH_base [] []))
                                                 (at level 20, e, f, Φ at level 200, only parsing) : bi_scope.


(* Frame wps for Local *)

 Notation "'EWP' e 'UNDER' g @ E 'FRAME' n ; f <| Ψ |> {{ Φ } }" := (ewp_wasm_frame E e%E g Ψ Φ n f)
  (at level 20, e, g, Ψ, Φ, n, f at level 200, only parsing) : bi_scope. 

 Notation "'EWP' e 'UNDER' g @ E 'FRAME' n ; f <| Ψ |> {{ v ; h , Q } }" := (ewp_wasm_frame E e%E g Ψ (λ v h, Q) n f)
  (at level 20, e, g, Ψ, Q, n, f at level 200,
    format "'[hv' 'EWP'  e  '/' 'UNDER'  g  @  '[' '/' E  ']' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' <| '[' Ψ ']' |>  '/' {{  '[' v ; h ,  '/' Q  ']'  } } ']'") : bi_scope. 

 Notation "'EWP' e 'UNDER' g @ E 'FRAME' n ; f 'CTX' i ; lh <| Ψ |> {{ v ; h , Q } }" := (ewp_wasm_ctx_frame E e%E g Ψ (λ v h, Q) n f i lh)
  (at level 20, e, g, Q, lh at level 200,
   format "'[hv' 'EWP'  e  '/' 'UNDER'  g  @  '[' '/' E  ']' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' <| '[' Ψ ']' |> '/' {{  '[' v ; h ,  '/' Q  ']'   } } ']'") : bi_scope. 
 Notation "'EWP' e 'UNDER' g @ E 'FRAME' n ; f 'CTX_EMPTY' <| Ψ |> {{ v ; h , Q  } }" := (ewp_wasm_ctx_frame E e%E g Ψ (λ v h, Q) n f 0 (LH_base [] []))
  (at level 20, e, g, Q at level 200,
    format "'[hv' 'EWP'  e  '/' 'UNDER'  g  @  '[' '/' E  ']' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX_EMPTY'  '/' <| '[' Ψ ']' |> '/' {{  '[' v ; h ,  '/' Q  ']' } } ']'") : bi_scope. 

(* no Ψ *)
Notation "'EWP' e 'UNDER' g @ E 'FRAME' n ; f {{ Φ } }" := (ewp_wasm_frame E e%E g (λ _, iProt_bottom) Φ n f)
  (at level 20, e, g, Φ, n, f at level 200, only parsing) : bi_scope.

Notation "'EWP' e 'UNDER' g @ E 'FRAME' n ; f {{ v ; h , Q } }" := (ewp_wasm_frame E e%E g (λ _, iProt_bottom) (λ v h, Q) n f)
  (at level 20, e, g, Q, n, f at level 200,
    format "'[hv' 'EWP'  e  '/' 'UNDER'  g  @  '[' '/' E  ']' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' {{  '[' v ; h ,  '/' Q  ']'  } } ']'") : bi_scope.

Notation "'EWP' e 'UNDER' g @ E 'FRAME' n ; f 'CTX' i ; lh {{ v ; h , Q } }" := (ewp_wasm_ctx_frame E e%E g (λ _, iProt_bottom) (λ v h, Q) n f i lh)
  (at level 20, e, g, Q, lh at level 200,
   format "'[hv' 'EWP'  e  '/' 'UNDER'  g  @  '[' '/' E  ']' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' {{  '[' v ; h ,  '/' Q  ']'   } } ']'") : bi_scope.
Notation "'EWP' e 'UNDER' g @ E 'FRAME' n ; f 'CTX_EMPTY' {{ v ; h , Q } }" := (ewp_wasm_ctx_frame E e%E g (λ _, iProt_bottom) (λ v h, Q) n f 0 (LH_base [] []))
  (at level 20, e, g, Q at level 200,
    format "'[hv' 'EWP'  e  '/' 'UNDER'  g  @  '[' '/' E  ']' 'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX_EMPTY'  '/' {{  '[' v ; h ,  '/' Q  ']'  } } ']'") : bi_scope.

(* no @E *)
 Notation "'EWP' e 'UNDER' g 'FRAME' n ; f <| Ψ |> {{ Φ } }" := (ewp_wasm_frame ⊤ e%E g Ψ Φ n f)
  (at level 20, e, g, Ψ, Φ, n, f at level 200, only parsing) : bi_scope.

Notation "'EWP' e 'UNDER' g 'FRAME' n ; f <| Ψ |> {{ v ; h , Q } }" := (ewp_wasm_frame ⊤ e%E g Ψ (λ v h, Q) n f)
  (at level 20, e, g, Ψ, Q, n, f at level 200,
    format "'[hv' 'EWP'  e  '/' 'UNDER'  g  'FRAME'  '/' '[' n ;  '/' f ']'  '/' <| '[' Ψ ']' |>  '/' {{  '[' v ; h ,  '/' Q  ']'  } } ']'") : bi_scope.

Notation "'EWP' e 'UNDER' g 'FRAME' n ; f 'CTX' i ; lh <| Ψ |> {{ v ; h , Q } }" := (ewp_wasm_ctx_frame ⊤ e%E g Ψ (λ v h, Q) n f i lh)
  (at level 20, e, g, Q, lh at level 200,
   format "'[hv' 'EWP'  e  '/' 'UNDER'  g  'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' <| '[' Ψ ']' |> '/' {{  '[' v ; h ,  '/' Q  ']'  } } ']'") : bi_scope.
Notation "'EWP' e 'UNDER' g 'FRAME' n ; f 'CTX_EMPTY' <| Ψ |> {{ v ; h , Q } }" := (ewp_wasm_ctx_frame ⊤ e%E g Ψ (λ v h, Q) n f 0 (LH_base [] []))
  (at level 20, e, g, Q at level 200,
    format "'[hv' 'EWP'  e  '/' 'UNDER'  g  'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX_EMPTY'  '/' <| '[' Ψ ']' |> '/' {{  '[' v ; h ,  '/' Q  ']'  } } ']'") : bi_scope. 

(* no Ψ, no @E *)
Notation "'EWP' e 'UNDER' g 'FRAME' n ; f {{ Φ } }" := (ewp_wasm_frame ⊤ e%E g (λ _, iProt_bottom) Φ n f)
  (at level 20, e, f, Φ, n, g at level 200, only parsing) : bi_scope.

Notation "'EWP' e 'UNDER' g 'FRAME' n ; f {{ v ; h , Q } }" := (ewp_wasm_frame ⊤ e%E g (λ _, iProt_bottom) (λ v h, Q) n f)
  (at level 20, e, g, Q, n, f at level 200,
    format "'[hv' 'EWP'  e  '/' 'UNDER'  g  'FRAME'  '/' '[' n ;  '/' f ']'  '/' {{  '[' v ; h ,  '/' Q  ']'  } } ']'") : bi_scope.

Notation "'EWP' e 'UNDER' g 'FRAME' n ; f 'CTX' i ; lh {{ v ; h , Q } }" := (ewp_wasm_ctx_frame ⊤ e%E g (λ _, iProt_bottom) (λ v h, Q) n f i lh)
  (at level 20, e, g, Q, lh at level 200,
   format "'[hv' 'EWP'  e  '/' 'UNDER'  g  'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX'  '/' '[' i ;  '/' lh ']'  '/' {{  '[' v ; h ,  '/' Q  ']'   } } ']'") : bi_scope.
Notation "'EWP' e 'UNDER' g 'FRAME' n ; f 'CTX_EMPTY' {{ v ; h , Q } }" := (ewp_wasm_ctx_frame ⊤ e%E g (λ _, iProt_bottom) (λ v h, Q) n f 0 (LH_base [] []))
  (at level 20, e, g, Q at level 200,
   format "'[hv' 'EWP'  e  '/' 'UNDER'  g  'FRAME'  '/' '[' n ;  '/' f ']'  '/' 'CTX_EMPTY'  '/' {{  '[' v ; h ,  '/' Q  ']'  } } ']'") : bi_scope.



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
