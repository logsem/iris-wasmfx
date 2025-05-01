From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language weakestpre.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map na_invariants.
From iris.base_logic.lib Require Export fancy_updates.
From Wasm.iris.helpers Require Import iris_properties.
From Wasm Require Import stdpp_aux (* datatypes common operations properties memory_list *).
From Wasm.iris.language.iris Require Export iris_locations iris.
From Wasm.iris.language Require Export iris_ewp. 


Import uPred.

Set Default Proof Using "Type".

Close Scope byte_scope.

Definition expr := iris.expr.
Definition val := iris.val.
Definition to_val := iris.to_val.

(* Defining a Wasm-specific WP with frame existence *)
Section wp_def.
  

Canonical Structure wasm_lang := Language wasm_mixin.
 
Local Definition reducible := @reducible wasm_lang.

(* Implicit Type σ : state. *)

Class wasmG Σ :=
  WasmG {
      func_invG :: invGS Σ;
      func_gen_hsG :: gen_heapGS N function_closure Σ;

      cont_gen_hsG :: gen_heapGS N continuation Σ;

      tag_gen_hsG :: gen_heapGS N function_type Σ;
      
      tab_gen_hsG :: gen_heapGS (N*N) funcelem Σ;
      
      tabsize_hsG :: gen_heapGS N nat Σ;
      
      tablimit_hsG :: gen_heapGS N (option N) Σ;

      mem_gen_hsG :: gen_heapGS (N*N) byte Σ;

      memsize_gen_hsG :: gen_heapGS N N Σ;

      memlimit_hsG :: gen_heapGS N (option N) Σ;

      glob_gen_hsG :: gen_heapGS N global Σ;

      locs_gen_hsG :: ghost_mapG Σ unit frame;

      frameGName : gname
    }.

(* functor needed for NA invariants -- those used by the logical
relation have a separate name from general ones *)
Class logrel_na_invs Σ :=
  {
    logrel_na_invG :: na_invG Σ;
    logrel_nais : na_inv_pool_name
  }.

Definition proph_id := positive. (* ??? *)


#[export] Instance eqdecision_frame: EqDecision frame.
Proof. decidable_equality. Qed.

Definition gen_heap_wasm_store `{!wasmG Σ} (s: store_record) : iProp Σ :=
  ((gen_heap_interp (gmap_of_list s.(s_funcs))) ∗
   (gen_heap_interp (gmap_of_table s.(s_tables))) ∗
   (gen_heap_interp (gmap_of_memory s.(s_mems))) ∗
   (gen_heap_interp (gmap_of_list s.(s_globals))) ∗
   (gen_heap_interp (gmap_of_list (fmap operations.length_mem s.(s_mems)))) ∗
   (gen_heap_interp (gmap_of_list (fmap tab_size s.(s_tables)))) ∗
   (@gen_heap_interp _ _ _ _ _ memlimit_hsG (gmap_of_list (fmap mem_max_opt s.(s_mems)))) ∗
   (@gen_heap_interp _ _ _ _ _ tablimit_hsG (gmap_of_list (fmap table_max_opt s.(s_tables)))))%I.



Definition state_interp `{!wasmG Σ} σ :=
  let: (s, locs, inst) := σ in
  ((@gen_heap_interp _ _ _ _ _ func_gen_hsG (gmap_of_list s.(s_funcs))) ∗
     (@gen_heap_interp _ _ _ _ _ cont_gen_hsG (gmap_of_list s.(s_conts))) ∗
     (@gen_heap_interp _ _ _ _ _ tag_gen_hsG (gmap_of_list s.(s_tags))) ∗
      (@gen_heap_interp _ _ _ _ _ tab_gen_hsG (gmap_of_table s.(s_tables))) ∗
      (gen_heap_interp (gmap_of_memory s.(s_mems))) ∗
      (gen_heap_interp (gmap_of_list s.(s_globals))) ∗
      (ghost_map_auth frameGName 1 (<[ tt := Build_frame locs inst ]> ∅)) ∗ 
      (gen_heap_interp (gmap_of_list (fmap operations.length_mem s.(s_mems)))) ∗
      (gen_heap_interp (gmap_of_list (fmap tab_size s.(s_tables)))) ∗
      (@gen_heap_interp _ _ _ _ _ memlimit_hsG (gmap_of_list (fmap mem_max_opt s.(s_mems)))) ∗
      (@gen_heap_interp _ _ _ _ _ tablimit_hsG (gmap_of_list (fmap table_max_opt s.(s_tables))))
      
     )%I.

(* Lemma state_interp_mono `{!wasmG Σ} s0 : state_interp s0 ={∅}=∗ state_interp s0.
Proof.
  iIntros "H". done.
Qed. *)

Lemma state_interp_mono `{!wasmG Σ} s0 : state_interp s0 ⊢ |={∅}=> state_interp s0.
Proof.
  iIntros "H". done.
Qed.
  

Global Instance heapG_irisG `{!wasmG Σ} : irisGS wasm_lang Σ := {
  iris_invGS := func_invG; 
  state_interp σ _ κs _ := state_interp σ; 
    num_laters_per_step _ := 0;
    fork_post _ := True%I ;
    state_interp_mono s0 _ _ _ := state_interp_mono s0 
  }.

End wp_def.

(* Resource ownerships *) 
Notation "n ↦[wf]{ q } v" := (pointsto (L:=N) (V:=function_closure) n q v%V)
                           (at level 20, q at level 5, format "n ↦[wf]{ q } v") : bi_scope.
Notation "n ↦[wf] v" := (pointsto (L:=N) (V:=function_closure) n (DfracOwn 1) v%V)
                          (at level 20, format "n ↦[wf] v") : bi_scope.
Notation "n ↦[wcont]{ q } v" := (pointsto (L:=N) (V:=continuation) n q v%V)
                           (at level 20, q at level 5, format "n ↦[wcont]{ q } v") : bi_scope.
Notation "n ↦[wcont] v" := (pointsto (L:=N) (V:=continuation) n (DfracOwn 1) v%V)
                             (at level 20, format "n ↦[wcont] v") : bi_scope.

Notation "n ↪[tag] v" := (exists q, pointsto (L:=N) (V:=function_type) n q v%V)
                           (at level 20, format "n ↪[tag] v") : bi_scope.

Notation "n ↦[wt]{ q } [ i ] v" := (pointsto (L:=N*N) (V:=funcelem) (n, i) q v%V)
                           (at level 20, q at level 5, format "n ↦[wt]{ q } [ i ] v") : bi_scope.
Notation "n ↦[wt][ i ] v" := (pointsto (L:=N*N) (V:=funcelem) (n, i) (DfracOwn 1) v%V)
                           (at level 20, format "n ↦[wt][ i ] v") : bi_scope.
Notation "n ↪[wtsize] m" := (pointsto (L:=N) (V:=nat) n (DfracDiscarded) m%V)
                              (at level 20, format "n ↪[wtsize] m") : bi_scope.
Notation "n ↪[wtlimit] m" := (pointsto (L:=N) (V:=option N) (hG:=tablimit_hsG) n (DfracDiscarded) m%V)
                              (at level 20, format "n ↪[wtlimit] m") : bi_scope.
Notation "n ↦[wm]{ q } [ i ] v" := (pointsto (L:=N*N) (V:=byte) (n, i) q v%V)
                           (at level 20, q at level 5, format "n ↦[wm]{ q } [ i ] v") : bi_scope.
Notation "n ↦[wm][ i ] v" := (pointsto (L:=N*N) (V:=byte) (n, i) (DfracOwn 1) v% V)
                           (at level 20, format "n ↦[wm][ i ] v") : bi_scope.
Notation "n ↦[wmlength] v" := (pointsto (L:=N) (V:=N) n (DfracOwn 1) v% V)
                           (at level 20, format "n ↦[wmlength] v") : bi_scope.
Notation "n ↪[wmlimit] v" := (pointsto (L:=N) (V:=option N) (hG:=memlimit_hsG) n (DfracDiscarded) v% V)
                           (at level 20, format "n ↪[wmlimit] v") : bi_scope.
Notation "n ↦[wg]{ q } v" := (pointsto (L:=N) (V:=global) n q v%V)
                           (at level 20, q at level 5, format "n ↦[wg]{ q } v").
Notation "n ↦[wg] v" := (pointsto (L:=N) (V:=global) n (DfracOwn 1) v%V)
                      (at level 20, format "n ↦[wg] v") .
Notation " ↪[frame]{ q } v" := (ghost_map_elem frameGName tt q v%V)
                           (at level 20, q at level 5, format " ↪[frame]{ q } v") .
Notation " ↪[frame] v" := (ghost_map_elem frameGName tt (DfracOwn 1) v%V)
                           (at level 20, format " ↪[frame] v").

(* Predicates for memory blocks and whole tables *)  
Definition mem_block `{!wasmG Σ} (n: N) (m: memory) :=
  (([∗ list] i ↦ b ∈ (m.(mem_data).(ml_data)), n ↦[wm][ (N.of_nat i) ] b ) ∗
     n ↦[wmlength] length_mem m ∗ n ↪[wmlimit] (mem_max_opt m))%I.

Definition mem_block_at_pos `{!wasmG Σ} (n: N) (l:bytes) k :=
  ([∗ list] i ↦ b ∈ l, n ↦[wm][ (N.of_nat (N.to_nat k+i)) ] b)%I.

Notation "n ↦[wmblock] m" := (mem_block n m)
                           (at level 20, format "n ↦[wmblock] m"): bi_scope.
Notation "n ↦[wms][ i ] l" := (mem_block_at_pos n l i)                    
                                (at level 20, format "n ↦[wms][ i ] l"): bi_scope.


Definition tab_block `{!wasmG Σ} (n: N) (tab: tableinst) :=
  (([∗ list] i ↦ tabelem ∈ (tab.(table_data)), n ↦[wt][ (N.of_nat i) ] tabelem ) ∗
     (n ↪[wtsize] (tab_size tab)) ∗ (n ↪[wtlimit] (table_max_opt tab)))%I.

Notation "n ↦[wtblock] t" := (tab_block n t)
                           (at level 20, format "n ↦[wtblock] t"): bi_scope.

Definition mem_equiv (m1 m2: memory): Prop :=
  m1.(mem_max_opt) = m2.(mem_max_opt) /\
  m1.(mem_data).(ml_data) = m2.(mem_data).(ml_data).

Lemma mem_equiv_wmblock_rewrite `{!wasmG Σ} (m1 m2: memory) n:
  mem_equiv m1 m2 ->
  (n ↦[wmblock] m1)%I ≡ (n ↦[wmblock] m2)%I.
Proof.
  unfold mem_equiv, mem_block.
  destruct m1, m2.
  destruct mem_data, mem_data0 => //=.
  by move => [-> ->] => //.
Qed.


Section Wasm_wp.
  Context `{!wasmG Σ}.


(*
Global Instance ewp_wasm : weakestpre.irisGS_gen HasLc iris.wasm_lang Σ.
  Proof using Σ wasmG0.
    eapply ewp'. Unshelve. exact frame. exact (λ f,  ↪[frame] f)%I. Defined. *) 

End Wasm_wp.

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
      as [H | [ [i0 Hstart] | (* [ [a [cl [tf [h [i0 [Hstart [Hnth Hcl]]]]]]] | *) (i1 & i2 & i3 & Hstart & Hstart1 & Hstart2 & Hσ)(* ] *)]] ;
  last (by repeat econstructor) ;
  first (try inversion H ; subst ; clear H => /=; match goal with [f: frame |- _] => iExists f; iFrame; by iIntros | _ => idtac end) ;
  try by repeat (unfold first_instr in Hstart ; simpl in Hstart) ; inversion Hstart.
