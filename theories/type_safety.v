(** Proof of type safety by progress and preservation **)
From Stdlib Require Import Program.Equality NArith.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.

From Wasm Require Export operations typing datatypes_properties typing opsem properties type_preservation type_progress.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Lemma reduce_trans_ind σ σ' (P: (store_record * frame * list administrative_instruction) -> Prop) :
  P σ ->
  reduce_trans σ σ' ->
  (forall σ σ', P σ -> reduce_tuple σ σ' -> P σ') ->
  P σ'.
Proof.
  intros Hσ Hred HI.
  induction Hred.
  - eapply HI. exact Hσ. exact H.
  - exact Hσ.
  - apply IHHred2.
    apply IHHred1.
    exact Hσ.
Qed.


Theorem type_safety:
  forall s f es ts s' f' es',
    config_typing s f es ts ->
    reduce_trans (s, f, es) (s', f', es') ->
    (* either es' is in terminal form (constant, trap, or unhandled effect) *)
    terminal_form es' \/
      (* or es' is stuck on a call to a host function (the host language must handle the call for the execution to be able to resume *)
      (exists tf h vcs n, first_instr es' = Some (AI_call_host tf h vcs,n)) \/
      (* or es' reduces *)
      exists s'' f'' es'', reduce s' f' es' s'' f'' es''.
Proof.
  intros s f es ts s' f' es' Htype Hred.
  apply (@reduce_trans_ind _ _
           (( fun '(s', f', es') => config_typing s' f' es' ts))) in Hred.
  - simpl in Hred.
    eapply t_progress. exact Hred.
  - exact Htype.
  - clear. intros [[??]?] [[??]?] Htype Hred.
    eapply t_preservation.
    exact Hred. exact Htype.
Qed. 
