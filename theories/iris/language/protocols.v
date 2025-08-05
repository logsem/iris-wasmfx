(* protocols.v *)

(* This file introduces the notion of _protocols_. A protocol describes
   the effects that a program may perform. It does so by describing a relation
   between a value and a predicate. Intuitively, such a value corresponds to
   the _payload_ of an effect (i.e. the value [v] in [do v]) and such a
   predicate corresponds to the condition upon which the paused computation
   can be resumed. *)

From iris.proofmode Require Import tactics.
From iris.base_logic Require Export lib.iprop.
From Wasm.iris.language.iris Require Import iris.
 
Set Default Proof Using "Type".
Set Bullet Behavior "Strict Subproofs".
Close Scope byte_scope.

Definition protocol_value := list value.
Canonical Structure protocol_valueO := leibnizO protocol_value.

(* ========================================================================== *)
(** * Protocols. *)

(* -------------------------------------------------------------------------- *)
(** Definition of the Domain of Protocols. *)

Section iProt.
Set Primitive Projections.
Record iProt Σ := IProt { iProt_car : protocol_value -d> (protocol_value -d> iPropO Σ) -n> iPropO Σ }.
End iProt.
Arguments IProt {_} _.
Arguments iProt_car {_} _.

Declare Scope iprot_scope.
Delimit Scope iprot_scope with iprot.
Bind Scope iprot_scope with iProt.
Local Open Scope iprot.


(* -------------------------------------------------------------------------- *)
(** Inhabited. *)

Instance iProt_inhabited {Σ} : Inhabited (iProt Σ) := populate (IProt inhabitant).


(* -------------------------------------------------------------------------- *)
(** OFE Structure. *)

Section iprot_ofe.
  Context {Σ : gFunctors}.
  Instance iProt_equiv : Equiv (iProt Σ) := λ e1 e2,
    iProt_car e1 ≡ iProt_car e2.
  Instance iProt_dist : Dist (iProt Σ) := λ n e1 e2,
    iProt_car e1 ≡{n}≡ iProt_car e2.
  Lemma iProt_ofe_mixin : OfeMixin (iProt Σ).
  Proof. by apply (iso_ofe_mixin iProt_car). Qed.
  Canonical Structure iProtO := Ofe (iProt Σ) iProt_ofe_mixin.
  Global Instance iProt_cofe : Cofe iProtO.
  Proof. by apply (iso_cofe IProt iProt_car). Qed.
End iprot_ofe.


(* -------------------------------------------------------------------------- *)
(** Non-expansiveness of Projections. *)

Global Instance IProt_ne {Σ} : NonExpansive (IProt (Σ:=Σ)).
Proof. by intros ???. Qed.
Global Instance IProt_proper {Σ} : Proper ((≡) ==> (≡)) (IProt (Σ:=Σ)).
Proof. by intros ???. Qed.
Global Instance iProt_car_ne {Σ} : NonExpansive (iProt_car (Σ:=Σ)).
Proof. by intros ???. Qed.
Global Instance iProt_car_proper {Σ} : Proper ((≡) ==> (≡)) (iProt_car (Σ:=Σ)).
Proof. by intros ???. Qed.


(* -------------------------------------------------------------------------- *)
(** Protocol-Equivalence Principles. *)

Lemma iProt_equivI' {Σ} `{!BiInternalEq SPROP} (e1 e2 : iProt Σ) :
  e1 ≡ e2 ⊣⊢@{SPROP} iProt_car e1 ≡ iProt_car e2.
Proof.
  apply (anti_symm _).
  - by apply f_equivI, iProt_car_ne.
  - destruct e1; destruct e2. simpl.
    by apply f_equivI, IProt_ne.
Qed.

Lemma iProt_equivI {Σ} `{!BiInternalEq SPROP} (e1 e2 : iProt Σ) :
  e1 ≡ e2 ⊣⊢@{SPROP} ∀ v q, iProt_car e1 v q ≡ iProt_car e2 v q.
Proof.
  trans (iProt_car e1 ≡ iProt_car e2 : SPROP)%I.
  - by apply iProt_equivI'.
  - rewrite discrete_fun_equivI. f_equiv=>v.
    by apply ofe_morO_equivI.
Qed.


(* ========================================================================== *)
(** * Notions of Protocol Monotonicity. *)

Section protocol_monotonicity.
  (* Context `{!irisGS prot_lang Σ}. *)

  (* Monotonic Protocol. *)
  Class MonoProt {Σ} (Ψ : iProt Σ) := {
    monotonic_prot v Φ Φ' :
      (∀ w, Φ w -∗ Φ' w) -∗ Ψ.(iProt_car) v Φ -∗ Ψ.(iProt_car) v Φ'
  }.

  (* Persistently Monotonic Protocol. *)
  Class PersMonoProt {Σ} (Ψ : iProt Σ) := {
    pers_monotonic_prot v Φ Φ' :
      □ (∀ w, Φ w -∗ Φ' w) -∗ Ψ.(iProt_car) v Φ -∗ Ψ.(iProt_car) v Φ'
  }.

End protocol_monotonicity.


(* ========================================================================== *)
(** * Upward Closure. *)

(* -------------------------------------------------------------------------- *)
(** Definition of the Upward Closure. *)

(* The _upward closure_ of a protocol [Ψ] is the smallest monotonic protocol
   that is greater than [Ψ] according to the _protocol ordering_ (defined in
   the remainder of this theory).

   The _persistently upward closure_ of a protocol [Ψ] is the smallest
   persistently monotonic protocol that is greater than [Ψ].

   Terminology:
   - [upcl OS Ψ]: Upward closure.
   - [upcl MS Ψ]: Persistent upward closure. *)

Program Definition upcl {Σ} (Ψ : iProt Σ) : iProt Σ :=
  IProt (λ v, λne Φ', ∃ Φ, iProt_car Ψ v Φ ∗ (∀ w, Φ w -∗ Φ' w))%I.
Next Obligation.
  intros ???. by simpl; repeat f_equiv.
Defined.
Arguments upcl _ _%_iprot.


(* -------------------------------------------------------------------------- *)
(** Properties of the Upward Closure. *)

(* Non-expansiveness. *)
Instance upcl_ne {Σ} n : Proper ((dist n) ==> (dist n)) (upcl (Σ:=Σ)).
Proof. by intros ?? Hne ??; simpl; repeat (apply Hne || f_equiv). Qed.
Instance upcl_proper {Σ} : Proper ((≡) ==> (≡)) (upcl (Σ:=Σ)).
Proof.
  intros ????. apply equiv_dist=>n.
  apply upcl_ne; by apply equiv_dist.
Qed.

(* The upward closure is monotonic. *)
Instance upcl_mono_prot {Σ} (Ψ : iProt Σ) : MonoProt (upcl Ψ).
Proof.
  constructor.
  iIntros (v Φ' Φ'') "HΦ'' [%Φ [HΨ HΦ']]".
  iExists Φ. iFrame. simpl. iIntros (w) "HΦ".
  by iApply "HΦ''"; iApply "HΦ'".
Qed.


(* The upward closure has no action over monotonic protocols. *)
Lemma upcl_id {Σ} (Ψ : iProt Σ) `{!MonoProt Ψ} : upcl Ψ ≡ Ψ.
Proof.
  iIntros (v Φ'). iSplit.
  - iIntros "[%Φ [HΨ HΦ']]". by iApply (monotonic_prot with "HΦ'").
  - iIntros "HΨ". iExists Φ'. iFrame. simpl. by iIntros (w) "Hw".
Qed.


(* ========================================================================== *)
(** * Construction of Protocols. *)

(* -------------------------------------------------------------------------- *)
(** Protocol Operators. *)

(* Bottom protocol. *)
Instance iProt_bottom {Σ} : Bottom (iProt Σ) := IProt (λ _, λne _, False%I).

(* Pre/post protocol.
   - Precondition is given by the pair of [v] and [P].
   - Postcondition is given by the predicate [Φ]. *)
Program Definition iProtPre_base_def {Σ}
  (v : protocol_value) (P : iProp Σ) (Φ : protocol_value -d> iPropO Σ) : iProt Σ :=
  IProt (λ v', λne Φ', ⌜ v = v' ⌝ ∗ P ∗ (∀ w, Φ w -∗ Φ' w))%I.
Next Obligation. by intros ???; simpl; repeat f_equiv. Qed.
Definition iProtPre_base_aux : seal (@iProtPre_base_def). by eexists. Qed.
Definition iProtPre_base := iProtPre_base_aux.(unseal).
Definition iProtPre_base_eq : @iProtPre_base = @iProtPre_base_def :=
  iProtPre_base_aux.(seal_eq).
Arguments iProtPre_base {_} _ _%_I _%_iprot.
Instance: Params (@iProtPre_base) 4 := {}.

(* Close a protocol with an existential quantifier. *)
Program Definition iProtPre_exist_def {Σ A} (e : A → iProt Σ) : iProt Σ :=
  IProt (λ v', λne q', ∃ a, iProt_car (e a) v' q')%I.
Next Obligation. solve_proper. Qed.
Definition iProtPre_exist_aux : seal (@iProtPre_exist_def). by eexists. Qed.
Definition iProtPre_exist := iProtPre_exist_aux.(unseal).
Definition iProtPre_exist_eq : @iProtPre_exist = @iProtPre_exist_def :=
  iProtPre_exist_aux.(seal_eq).
Arguments iProtPre_exist {_ _} _%_iprot.
Instance: Params (@iProtPre_exist) 3 := {}.

(* Iterate the existential closure. *)
Definition iProtPre_texist {Σ} {TT : tele} (e : TT → iProt Σ) : iProt Σ :=
  tele_fold (@iProtPre_exist Σ) (λ x, x) (tele_bind e).
Arguments iProtPre_texist {_ _} _%_iprot /.

(* Construct a predicate from a pair of a value [w] and an assertion [Q]. *)
Definition iProtPost_base_def {Σ} (w : protocol_value) (Q : iProp Σ) : protocol_value -d> iPropO Σ
  := (λ w', ⌜ w = w' ⌝ ∗ Q)%I.
Definition iProtPost_base_aux : seal (@iProtPost_base_def). by eexists. Qed.
Definition iProtPost_base := iProtPost_base_aux.(unseal).
Definition iProtPost_base_eq : @iProtPost_base = @iProtPost_base_def :=
  iProtPost_base_aux.(seal_eq).
Arguments iProtPost_base {_} _ _%_I.
Instance: Params (@iProtPost_base) 2 := {}.

(* Close a predicate with an existential quantifier. *)
Program Definition iProtPost_exist_def {Σ A}
  (e : A → (protocol_value -d> iPropO Σ)) : protocol_value -d> iPropO Σ :=
  (λ w', ∃ a, e a w')%I.
Definition iProtPost_exist_aux : seal (@iProtPost_exist_def). by eexists. Qed.
Definition iProtPost_exist := iProtPost_exist_aux.(unseal).
Definition iProtPost_exist_eq : @iProtPost_exist = @iProtPost_exist_def :=
  iProtPost_exist_aux.(seal_eq).
Arguments iProtPost_exist {_ _} _%_iprot.
Instance: Params (@iProtPost_exist) 2 := {}.

Definition iProtPost_texist {Σ} {TT : tele}
  (e : TT → (protocol_value -d> iPropO Σ)) : protocol_value -d> iPropO Σ :=
  tele_fold (@iProtPost_exist Σ) (λ x, x) (tele_bind e).
Arguments iProtPost_texist {_ _} _%_iprot /.

(* Protocol marked by a function [f]. *)
Program Definition iProt_marker_def {Σ} (f : protocol_value → protocol_value) (e : iProt Σ) : iProt Σ :=
  IProt (λ v', λne q', ∃ w', ⌜ v' = f w' ⌝ ∗ iProt_car e w' q')%I.
Next Obligation. solve_proper. Qed.
Definition iProt_marker_aux : seal (@iProt_marker_def). by eexists. Qed.
Definition iProt_marker := iProt_marker_aux.(unseal).
Definition iProt_marker_eq : @iProt_marker = @iProt_marker_def :=
  iProt_marker_aux.(seal_eq).
Arguments iProt_marker {_} _ _%_iprot.
Instance: Params (@iProt_marker) 3 := {}.

(* Extend a given protocol with the constraint
   that the sent values satisfy [P]. *)
Program Definition iProt_filter_def {Σ} (P : protocol_value → Prop) (e : iProt Σ) : iProt Σ :=
  IProt (λ v', λne q', ⌜ P v' ⌝ ∗ iProt_car e v' q')%I.
Next Obligation. solve_proper. Qed.
Definition iProt_filter_aux : seal (@iProt_filter_def). by eexists. Qed.
Definition iProt_filter := iProt_filter_aux.(unseal).
Definition iProt_filter_eq : @iProt_filter = @iProt_filter_def :=
  iProt_filter_aux.(seal_eq).
Arguments iProt_filter {_} _ _%_iprot.
Instance: Params (@iProt_marker) 3 := {}.

(* Protocol sum. *)
Program Definition iProt_sum_def {Σ} (e1 e2 : iProt Σ) : iProt Σ :=
  IProt (λ w', λne q', (iProt_car e1 w' q') ∨ (iProt_car e2 w' q'))%I.
Next Obligation. solve_proper. Qed.
Definition iProt_sum_aux : seal (@iProt_sum_def). by eexists. Qed.
Definition iProt_sum := iProt_sum_aux.(unseal).
Definition iProt_sum_eq : @iProt_sum = @iProt_sum_def :=
  iProt_sum_aux.(seal_eq).
Arguments iProt_sum {_} _%_iprot _%_iprot.
Instance: Params (@iProt_sum) 3 := {}.


(* -------------------------------------------------------------------------- *)
(** Notation. *)

(* Notation for send/recv protocols. *)

Notation "'!' v {{ P } } ; Q' " := (iProtPre_base v P Q')
  (at level 200, v at level 20, right associativity,
   format "'!' v {{  P  } } ; Q' ") : iprot_scope.

Notation "'?' w {{ Q } }" := (iProtPost_base w Q)
  (at level 200, w at level 20, right associativity,
   format "'?' w  {{  Q  } }") : iprot_scope.

Notation ">> x .. y >> e" := 
  (iProtPre_exist (λ x, .. (iProtPre_exist (λ y, e)) .. )%iprot)
  (at level 200, x binder, y binder, right associativity,
   format ">>  x  ..  y >>  e") : iprot_scope.

Notation "<< x .. y << e" := 
  (iProtPost_exist (λ x, .. (iProtPost_exist (λ y, e)) .. )%iprot)
  (at level 200, x binder, y binder, right associativity,
   format "<<  x  ..  y <<  e") : iprot_scope.

Notation "'>>..' x .. y >> e" := 
  (iProtPre_texist (λ x, .. (iProtPre_texist (λ y, e)) .. )%iprot)
  (at level 200, x binder, y binder, right associativity,
   format ">>..  x  ..  y >>  e") : iprot_scope.

Notation "'<<..' x .. y << e" := 
  (iProtPost_texist (λ x, .. (iProtPost_texist (λ y, e)) .. )%iprot)
  (at level 200, x binder, y binder, right associativity,
   format "<<..  x  ..  y <<  e") : iprot_scope.

(* Notation for protocol sum and marked protocol. *)

Notation "Ψ1 '<+>' Ψ2"  := (iProt_sum Ψ1 Ψ2)
  (at level 20, right associativity,
   format "Ψ1 <+> Ψ2") : iprot_scope.

Notation "f '#>' Ψ"  := (iProt_marker f Ψ)
  (at level 15, right associativity,
   format "f #> Ψ") : iprot_scope.

Notation "P '?>' Ψ"  := (iProt_filter P Ψ)
  (at level 15, right associativity,
   format "P ?> Ψ") : iprot_scope.

(* Test. *)
(* Check (λ Σ P Q, (>> v >> ! v {{ P }} ; << w << ? w {{ Q }} @ MS)). *)


(* -------------------------------------------------------------------------- *)
(** Unfolding Principles. *)

Lemma iProtPre_texist_eq {Σ} {TT : tele} v p (e : TT → iProt Σ) :
  iProt_car (>>.. x >> (e x))%iprot v p ⊣⊢ (∃.. x, iProt_car (e x) v p).
Proof.
  rewrite /iProtPre_texist iProtPre_exist_eq.
  induction TT as [|T TT IH]; simpl; [done|]. f_equiv=> x. by apply IH.
Qed.

Lemma iProtPost_texist_eq {Σ} {TT : tele} w (e : TT → _ -d> iPropO Σ) :
  (<<.. y << (e y))%iprot w ⊣⊢ (∃.. y, (e y) w).
Proof.
  rewrite /iProtPost_texist iProtPost_exist_eq.
  induction TT as [|T TT IH]; simpl; [done|].
  rewrite /iProtPost_exist_def. f_equiv=>x. by apply IH.
Qed.

(* This lemma allows the unfolding of the definition of a
   send/recv protocol at once; that is, the arbitrary
   number of binders are correspondingly interpreted as
   existential/universal quantifiers. *)
Lemma iProt_tele_eq {Σ} {TT1 TT2 : tele}
  (v : TT1 →       protocol_value) (P : TT1 →       iProp Σ)
  (w : TT1 → TT2 → protocol_value) (Q : TT1 → TT2 → iProp Σ) v' Φ' :
    iProt_car (>>.. x >> ! (v x  ) {{ P x   }};
              <<.. y << ? (w x y) {{ Q x y }}) v' Φ'
   ⊣⊢
    (∃.. x, ⌜ v x = v' ⌝ ∗ P x ∗
                      (∀.. y, Q x y -∗ Φ' (w x y)))%I.
Proof.
  rewrite iProtPre_texist_eq iProtPre_base_eq. do 2 f_equiv.
  iSplit; iIntros "(-> & HP & HΦ')"; iSplit; try done; iFrame.
  { iIntros (y) "HQ". iApply "HΦ'". rewrite iProtPost_texist_eq.
    iExists y. rewrite iProtPost_base_eq. by iFrame. }
  { iIntros (y) "HQ". rewrite iProtPost_texist_eq iProtPost_base_eq.
    iDestruct "HQ" as (w') "(<- & HQ)". by iApply "HΦ'". }
Qed.


(* -------------------------------------------------------------------------- *)
(** Properties of Protocol Operators. *)


Section protocol_operators_properties.
  Context {Σ : gFunctors}.
  Implicit Types Ψ : iProt Σ.


  (* Non-expansiveness. *)
  
  Global Instance iProtPre_base_ne n :
    Proper
      ((dist n) ==> (dist n) ==> (dist n) ==> (dist n)) (iProtPre_base (Σ:=Σ)).
  Proof.
    intros ?????????. rewrite iProtPre_base_eq /iProtPre_base_def.
    intros ??. simpl; by repeat (apply H || f_equiv).
  Qed. 
  Global Instance iProtPre_base_proper :
    Proper ((≡) ==> (≡) ==> (≡) ==> (≡)) (iProtPre_base (Σ:=Σ)).
  Proof.
    intros ?????????.
    apply equiv_dist=>n; apply iProtPre_base_ne; by apply equiv_dist.
  Qed. 

  Global Instance iProtPost_base_ne n :
    Proper ((dist n) ==> (dist n) ==> (dist n) ==> (dist n))
           (iProtPost_base (Σ:=Σ)).
  Proof.
    intros ?????????.
    rewrite iProtPost_base_eq /iProtPost_base_def. solve_proper.
  Qed.
  Global Instance iProtPost_base_proper :
    Proper ((≡) ==> (≡) ==> (≡) ==> (≡)) (iProtPost_base (Σ:=Σ)).
  Proof.
    intros ?????????.
    apply equiv_dist=>n; apply iProtPost_base_ne; by apply equiv_dist.
  Qed.

  Global Instance iProt_sum_ne n :
    Proper ((dist n) ==> (dist n) ==> (dist n)) (iProt_sum (Σ:=Σ)).
  Proof.
    intros ??????. rewrite iProt_sum_eq /iProt_sum_def.
    f_equiv=>w' q' //=. f_equiv; by apply iProt_car_ne.
  Qed.
  Global Instance iProt_sum_proper :
    Proper ((≡) ==> (≡) ==> (≡)) (iProt_sum (Σ:=Σ)).
  Proof.
    intros ??????.
    apply equiv_dist=>n; apply iProt_sum_ne; by apply equiv_dist.
  Qed.

  Global Instance iProt_marker_ne f n :
    Proper ((dist n) ==> (dist n)) (iProt_marker (Σ:=Σ) f).
  Proof.
    intros ???. rewrite iProt_marker_eq /iProt_marker_def.
    f_equiv=>w' q' //=. f_equiv=> v'. f_equiv; by apply iProt_car_ne.
  Qed.
  Global Instance iProt_marker_proper f :
    Proper ((≡) ==> (≡)) (iProt_marker (Σ:=Σ) f).
  Proof.
    intros ???. apply equiv_dist=>n; apply iProt_marker_ne; by apply equiv_dist.
  Qed.

  Global Instance iProt_filter_ne P n :
    Proper ((dist n) ==> (dist n)) (iProt_filter (Σ:=Σ) P).
  Proof.
    intros ???. rewrite iProt_filter_eq /iProt_filter_def.
    f_equiv=>v' q' //=. f_equiv; by apply iProt_car_ne.
  Qed.
  Global Instance iProt_filter_proper P :
    Proper ((≡) ==> (≡)) (iProt_filter (Σ:=Σ) P).
  Proof.
    intros ???. apply equiv_dist=>n; apply iProt_filter_ne; by apply equiv_dist.
  Qed.

  Global Instance iProtPre_exist_ne A n :
    Proper (pointwise_relation _ (dist n) ==> (dist n)) (@iProtPre_exist Σ A).
  Proof. rewrite iProtPre_exist_eq=> m1 m2 Hm v p /=. f_equiv=> x. apply Hm. Qed.
  Global Instance iProtPre_exist_proper A :
    Proper (pointwise_relation _ (≡) ==> (≡)) (@iProtPre_exist Σ A).
  Proof. rewrite iProtPre_exist_eq=> m1 m2 Hm v p /=. f_equiv=> x. apply Hm. Qed.

  Global Instance iProtPost_exist_ne A n :
    Proper (pointwise_relation _ (dist n) ==> (dist n)) (@iProtPost_exist Σ A).
  Proof.
    rewrite iProtPost_exist_eq /iProtPost_exist_def => m1 m2 Hm w /=.
    f_equiv=>x. apply Hm.
  Qed.
  Global Instance iProtPost_exist_proper A :
    Proper (pointwise_relation _ (≡) ==> (≡)) (@iProtPost_exist Σ A).
  Proof.
    rewrite iProtPost_exist_eq /iProtPost_exist_def => m1 m2 Hm w /=.
    f_equiv=> x. apply Hm.
  Qed.


  (* Algebraic properties. *)

  Global Instance iProt_sum_comm : Comm (≡) (iProt_sum (Σ:=Σ)).
  Proof.
    intros e1 e2 v q. rewrite iProt_sum_eq /iProt_sum_def //=.
    iSplit; iIntros "H"; iDestruct "H" as "[H|H]".
    { by iRight. } { by iLeft. } { by iRight. } { by iLeft. }
  Qed.
  Global Instance iProt_sum_assoc : Assoc (≡) (iProt_sum (Σ:=Σ)).
  Proof.
    intros e1 e2 e3 v q. rewrite iProt_sum_eq /iProt_sum_def //=.
    iSplit; iIntros "H";
    [ iDestruct "H" as "[H|[H|H]]"
    | iDestruct "H" as "[[H|H]|H]" ].
    { by iLeft; iLeft. } { by iLeft; iRight. } { by iRight. }
    { by iLeft. } { by iRight; iLeft. } { by iRight; iRight. }
  Qed.
  Global Instance iProt_sum_left_id : LeftId (≡) (⊥) (iProt_sum (Σ:=Σ)).
  Proof.
    intros e v q. rewrite iProt_sum_eq /iProt_sum_def //=.
    iSplit; iIntros "H"; [iDestruct "H" as "[H|H]"|]; by iFrame.
  Qed.
  Global Instance iProt_sum_right_id : RightId (≡) (⊥) (iProt_sum (Σ:=Σ)).
  Proof. intros e. rewrite iProt_sum_comm. by apply iProt_sum_left_id. Qed.

  Lemma iProt_filter_bottom P : (P ?> ⊥ ≡ (⊥ : iProt Σ))%iprot.
  Proof.
    intros v q. rewrite iProt_filter_eq /iProt_filter_def //=.
    by iSplit; [iIntros "[_ H]"|].
  Qed.
  Lemma iProt_filter_true (Ψ : iProt Σ) : ((λ _, True) ?> Ψ ≡ Ψ)%iprot.
  Proof.
    intros v q. rewrite iProt_filter_eq /iProt_filter_def //=.
    iSplit; [iIntros "[_ H]"|iIntros "H"]; by auto.
  Qed.
  Lemma iProt_filter_false (Ψ : iProt Σ) : ((λ _, False) ?> Ψ ≡ (⊥ : iProt Σ))%iprot.
  Proof.
    intros v q. rewrite iProt_filter_eq /iProt_filter_def //=.
    iSplit; [iIntros "[H _]"|iIntros "H"]; by auto.
  Qed.
  Lemma iProt_filter_filter P Q (Ψ : iProt Σ) :
    (P ?> (Q ?> Ψ) ≡ (λ (v : protocol_value), P v ∧ Q v) ?> Ψ)%iprot.
  Proof.
    intros v q. rewrite iProt_filter_eq /iProt_filter_def //=.
    iSplit; [iIntros "(% & % & H)"|iIntros "[[% %] H]"]; by auto.
  Qed.
  Lemma iProt_filter_filter_l (P Q : protocol_value → Prop) (Ψ : iProt Σ) :
    (∀ v, P v → Q v) → (P ?> (Q ?> Ψ) ≡ P ?> Ψ)%iprot.
  Proof.
    intros H v q. rewrite iProt_filter_eq /iProt_filter_def //=.
    iSplit; [iIntros "(% & % & H)"|iIntros "[% H]"]; by auto.
  Qed.
  Lemma iProt_filter_filter_r (P Q : protocol_value → Prop) Ψ :
    (∀ v, Q v → P v) → (P ?> (Q ?> Ψ) ≡ Q ?> Ψ)%iprot.
  Proof.
    intros H v q. rewrite iProt_filter_eq /iProt_filter_def //=.
    iSplit; [iIntros "(% & % & H)"|iIntros "[% H]"]; by auto.
  Qed.

  Lemma iProt_filter_sum_distr P Ψ1 Ψ2 :
    ((P ?> (Ψ1 <+> Ψ2)) ≡ (P ?> Ψ1) <+> (P ?> Ψ2))%iprot.
  Proof.
    intros v q. rewrite iProt_sum_eq iProt_filter_eq /iProt_sum_def /iProt_filter_def.
    simpl. iSplit; [iIntros "[% [H|H]]"|iIntros "[[% H]|[% H]]"]; by auto.
  Qed.

  Lemma iProt_sum_filter_eq (P : protocol_value → Prop) `{!∀ v, Decision (P v)} Ψ :
    (Ψ ≡ (P ?> Ψ) <+> ((λ v, ¬ P v) ?> Ψ))%iprot.
  Proof.
    intros v q. rewrite iProt_sum_eq iProt_filter_eq /iProt_sum_def /iProt_filter_def.
    simpl. iSplit; [iIntros "H"|iIntros "[[% H]|[% H]]"]; iFrame.
    iPureIntro. case (decide (P v)); by auto.
  Qed.

  Lemma iProt_marker_bottom f : (f #> ⊥ ≡ (⊥ : iProt Σ))%iprot.
  Proof.
    intros v q. rewrite iProt_marker_eq /iProt_marker_def //=.
    iSplit; iIntros "H"; [iDestruct "H" as (w) "[_ H]"|]; done.
  Qed.

  Lemma iProt_marker_sum_distr f (Ψ1 Ψ2 : iProt Σ) :
    ((f #> (Ψ1 <+> Ψ2)) ≡ (f #> Ψ1) <+> (f #> Ψ2))%iprot.
  Proof.
    intros v q. rewrite iProt_sum_eq iProt_marker_eq /iProt_sum_def /iProt_marker_def.
    simpl. iSplit; iIntros "H".
    - iDestruct "H" as (w') "[-> [H|H]]"; by eauto.
    - iDestruct "H" as "[H|H]"; iDestruct "H" as (w') "[-> H]"; by eauto.
  Qed.

  Lemma iProt_marker_compose f g (Ψ : iProt Σ) :
    ((f #> (g #> Ψ)) ≡ ((f ∘ g) #> Ψ))%iprot.
  Proof.
    intros v q. rewrite iProt_marker_eq /iProt_marker_def.
    simpl. iSplit; iIntros "H".
    - iDestruct "H" as (u') "[-> H]"; iDestruct "H" as (w') "[-> H]"; by eauto.
    - iDestruct "H" as (w') "[-> H]"; by eauto.
  Qed.

  Lemma iProt_marker_tele {TT1 TT2 : tele} f
  (v : TT1 →       protocol_value) (P : TT1 →       iProp Σ)
  (w : TT1 → TT2 → protocol_value) (Q : TT1 → TT2 → iProp Σ) :
    (f #> (>>.. x >> !    (v x  )  {{ P x }};
           <<.. y << ?    (w x y)  {{ Q x y }}))
   ≡
          (>>.. x >> ! (f (v x  )) {{ P x }};
           <<.. y << ? (  (w x y)) {{ Q x y }}).
  Proof.
    intros u' q'. iSplit; rewrite iProt_marker_eq /iProt_marker_def //=.
    { iIntros "H". iDestruct "H" as (u) "[-> H]".
      rewrite !iProtPre_texist_eq iProtPre_base_eq //=.
      iDestruct "H" as (x) "(<- & HP & Hk)". iExists x. by iFrame. }
    { iIntros "H". rewrite !iProtPre_texist_eq iProtPre_base_eq //=.
      iDestruct "H" as (u) "(<- & HP & Heq)". iExists (v u).
      iSplit; [done|]. rewrite iProtPre_texist_eq. iExists u. by iFrame. }
  Qed.
  Lemma iProt_marker_tele' (TT1 TT2 : tele) f
  (v : TT1 -t>         protocol_value) (P : TT1 -t>         iProp Σ)
  (w : TT1 -t> TT2 -t> protocol_value) (Q : TT1 -t> TT2 -t> iProp Σ) :
    (f #> (>>.. x >> !           (tele_app v x)
                     {{          (tele_app P x)   }};
           <<.. y << ? (tele_app (tele_app w x) y)
                     {{ tele_app (tele_app Q x) y }}))
   ≡
          (>>.. x >> !        (f (tele_app v x))
                     {{          (tele_app P x)   }};
           <<.. y << ? (tele_app (tele_app w x) y)
                     {{ tele_app (tele_app Q x) y }}).
  Proof. by rewrite (iProt_marker_tele _ (tele_app v) (tele_app P)
                  (λ x y, tele_app (tele_app w x) y)
                  (λ x y, tele_app (tele_app Q  x) y)).
  Qed.


  Global Instance send_recv_mono_prot {TT1 TT2 : tele}
    (v' : TT1 →       protocol_value) (P : TT1 →       iProp Σ)
    (w' : TT1 → TT2 → protocol_value) (Q : TT1 → TT2 → iProp Σ) :
      MonoProt (>>.. x >> ! (v' x)   {{ P x   }};
                <<.. y << ? (w' x y) {{ Q x y }}).
  Proof.
    constructor.
    iIntros (v Φ Φ') "HΦ". rewrite !iProt_tele_eq.
    iIntros "[%x [%Heq [HP HΦ']]]". iExists x.
    iFrame. iSplit; [done|]. simpl. iIntros (y) "HQ".
    iApply "HΦ". by iApply "HΦ'".
  Qed.



  (* Properties related to the upward closure. *)

  Lemma upcl_bottom v Φ : iProt_car (upcl (⊥ : iProt Σ)) v Φ ≡ False%I.
  Proof. by iSplit; [iIntros "[%Q [H _]]"|iIntros "H"]. Qed.

  Lemma upcl_m_tele {TT1 TT2 : tele}
    (v' : TT1 →       protocol_value) (P : TT1 →       iProp Σ)
    (w' : TT1 → TT2 → protocol_value) (Q : TT1 → TT2 → iProp Σ) v Φ :
    iProt_car (upcl
      (>>.. x >> ! (v' x)   {{ P x   }};
       <<.. y << ? (w' x y) {{ Q x y }})) v Φ ≡
    (∃.. x, ⌜ v = v' x ⌝ ∗ P x ∗
                    (∀.. y, Q x y -∗ Φ (w' x y)))%I.
  Proof.
    rewrite /upcl. iSplit.
    - iIntros "H". iDestruct "H" as (Q') "[HP HQ']".
      rewrite iProtPre_texist_eq iProtPre_base_eq /iProtPre_base_def.
      iDestruct "HP" as (x) "(<- & HP & HΦ)". iExists x. iFrame.
      iSplit; [done|].
(*      iApply (bi.intuitionistically_if_mono with "[HΦ HQ']");[| 
      by iApply bi.intuitionistically_if_sep_2; iFrame]. *)
      iIntros (y) "HQ".
      iApply "HQ'". iApply "HΦ".
      rewrite iProtPost_texist_eq iProtPost_base_eq /iProtPost_base_def.
      iExists y. by iFrame.
    - iIntros "H". iDestruct "H" as (x) "(-> & HP & HQ)".
      iExists (<<.. y << ? (w' x y) {{ Q x y }})%iprot.
      rewrite iProtPre_texist_eq. iSplitL "HP".
      + iExists x. rewrite iProtPre_base_eq /iProtPre_base_def //=. iFrame.
        by simpl; auto.
      + (* iApply (bi.intuitionistically_if_mono with "HQ"). *)
        iIntros (w) "HQ'".
        rewrite iProtPost_texist_eq iProtPost_base_eq.
        iDestruct "HQ'" as (y) "[<- HQ']". by iApply "HQ".
  Qed.
  Lemma upcl_tele {TT1 TT2 : tele}
    (v' : TT1 →       protocol_value) (P : TT1 →       iProp Σ)
    (w' : TT1 → TT2 → protocol_value) (Q : TT1 → TT2 → iProp Σ) v Φ :
    iProt_car (upcl
      (>>.. x >> ! (v' x)   {{ P x   }};
       <<.. y << ? (w' x y) {{ Q x y }})) v Φ ≡
    (∃.. x, ⌜ v = v' x ⌝ ∗ P x ∗
      (∀.. y, Q x y -∗ Φ (w' x y)))%I.
  Proof. by apply (upcl_m_tele _ _ _ _). Qed.

  Lemma upcl_m_tele' (TT1 TT2 : tele)
    (v' : TT1 -t>         protocol_value) (P : TT1 -t>         iProp Σ)
    (w' : TT1 -t> TT2 -t> protocol_value) (Q : TT1 -t> TT2 -t> iProp Σ) v Φ :
    iProt_car (upcl 
      (>>.. x >> !           (tele_app v' x)
                 {{          (tele_app P  x)   }};
       <<.. y << ? (tele_app (tele_app w' x) y)
                 {{ tele_app (tele_app Q  x) y }} )) v Φ ≡
    (∃.. x, ⌜ v = tele_app v' x ⌝ ∗ tele_app P x ∗
                    (∀.. y, tele_app (tele_app Q  x) y -∗
                 Φ (tele_app (tele_app w' x) y)))%I.
  Proof. by rewrite (upcl_m_tele (tele_app v') (tele_app P)
                    (λ x y, tele_app (tele_app w' x) y)
                    (λ x y, tele_app (tele_app Q  x) y)).
  Qed.
  Lemma upcl_tele' (TT1 TT2 : tele)
    (v' : TT1 -t>         protocol_value) (P : TT1 -t>         iProp Σ)
    (w' : TT1 -t> TT2 -t> protocol_value) (Q : TT1 -t> TT2 -t> iProp Σ) v Φ :
    iProt_car (upcl
      (>>.. x >> !           (tele_app v' x)
                 {{          (tele_app P  x)   }};
       <<.. y << ? (tele_app (tele_app w' x) y)
                 {{ tele_app (tele_app Q  x) y }})) v Φ ≡
    (∃.. x, ⌜ v = tele_app v' x ⌝ ∗ tele_app P x ∗
      (∀.. y, tele_app (tele_app Q  x) y -∗
           Φ (tele_app (tele_app w' x) y)))%I.
  Proof. by apply upcl_m_tele'. Qed.

  Lemma upcl_marker_tele {TT1 TT2 : tele} f
    (v' : TT1 →       protocol_value) (P : TT1 →       iProp Σ)
    (w' : TT1 → TT2 → protocol_value) (Q : TT1 → TT2 → iProp Σ) :
    upcl 
      (f #> (>>.. x >> !    (v' x  )  {{ P x   }};
             <<.. y << ?    (w' x y)  {{ Q x y }})) ≡
    upcl
            (>>.. x >> ! (f (v' x  )) {{ P x   }};
             <<.. y << ? (  (w' x y)) {{ Q x y }}).
  Proof. by rewrite iProt_marker_tele. Qed.

  Lemma upcl_marker_intro f v Ψ Φ :
    iProt_car (upcl Ψ) v Φ ⊢ iProt_car (upcl (f #> Ψ)) (f v) Φ.
  Proof.
    rewrite /upcl iProt_marker_eq.
    iIntros "H". iDestruct "H" as (Q) "[He HQ]".
    iExists Q. by iFrame.
  Qed.

  Lemma upcl_marker_elim f {Hf: Inj (=) (=) f} v Ψ Φ :
    iProt_car (upcl (f #> Ψ)) (f v) Φ ⊢ iProt_car (upcl Ψ) v Φ.
  Proof.
    iIntros "H". rewrite iProt_marker_eq /upcl //=.
    iDestruct "H" as (Q) "[HP HQ]".
    iDestruct "HP" as (w') "[% HP]". rewrite (Hf _ _ H).
    iExists Q. by iFrame.
  Qed.

  Lemma upcl_marker_elim' f v Ψ Φ :
    iProt_car (upcl (f #> Ψ)) v Φ ⊢ ∃ w, ⌜ v = f w ⌝ ∗ iProt_car (upcl Ψ) w Φ.
  Proof.
    iIntros "H". rewrite iProt_marker_eq /upcl //=.
    iDestruct "H" as (Q) "[HP HQ]". iDestruct "HP" as (w) "[-> HP]".
    iExists w. iSplit; [done|]. iExists Q. by iFrame.
  Qed.

  Lemma upcl_filter v P Ψ Φ :
    iProt_car (upcl (P ?> Ψ)) v Φ ⊣⊢ ⌜ P v ⌝ ∗ iProt_car (upcl Ψ) v Φ.
  Proof.
    rewrite iProt_filter_eq /upcl //=. iSplit.
    - iIntros "H". iDestruct "H" as (Q) "[[% HP] HQ]".
      iSplit; [done|]. by eauto with iFrame.
    - iIntros "[% H]". iDestruct "H" as (Q) "[HP HQ]".
      by eauto with iFrame.
  Qed.

  Lemma upcl_sum_assoc v Ψ1 Ψ2 Ψ3 Φ :
    iProt_car (upcl (Ψ1 <+> (Ψ2 <+> Ψ3))) v Φ ≡
      iProt_car (upcl ((Ψ1 <+> Ψ2) <+> Ψ3)) v Φ.
  Proof. by apply iProt_car_proper; rewrite iProt_sum_assoc. Qed.

  Lemma upcl_sum_comm v Ψ1 Ψ2 Φ :
    iProt_car (upcl (Ψ2 <+> Ψ1)) v Φ ≡ iProt_car (upcl (Ψ1 <+> Ψ2)) v Φ.
  Proof. by apply iProt_car_proper; rewrite iProt_sum_comm. Qed.

  Lemma upcl_sum_intro_l v Ψ1 Ψ2 Φ :
    iProt_car (upcl Ψ1) v Φ ⊢ iProt_car (upcl (Ψ1 <+> Ψ2)) v Φ.
  Proof.
    rewrite /upcl iProt_sum_eq.
    iIntros "H". iDestruct "H" as (Q) "[He HQ]". iExists Q. by iFrame.
  Qed.

  Lemma upcl_sum_intro_r v Ψ1 Ψ2 Φ :
    iProt_car (upcl Ψ2) v Φ ⊢ iProt_car (upcl (Ψ1 <+> Ψ2)) v Φ.
  Proof.
    iIntros "H". rewrite upcl_sum_comm.
    by iApply upcl_sum_intro_l.
  Qed.

  Lemma upcl_sum_elim v Ψ1 Ψ2 Φ :
    iProt_car (upcl (Ψ1 <+> Ψ2)) v Φ ⊢
      (iProt_car (upcl Ψ1) v Φ) ∨ (iProt_car (upcl Ψ2) v Φ).
  Proof.
    iIntros "H". iDestruct "H" as (Q) "[HP HQ]".
    rewrite iProt_sum_eq. iDestruct "HP" as "[HP|HP]".
    { iLeft;  iExists Q; by iFrame. }
    { iRight; iExists Q; by iFrame. }
  Qed.

  Lemma upcl_sum v Ψ1 Ψ2 Φ :
    iProt_car (upcl (Ψ1 <+> Ψ2)) v Φ ≡
      ((iProt_car (upcl Ψ1) v Φ) ∨ (iProt_car (upcl Ψ2) v Φ))%I.
  Proof.
    iSplit; [iApply upcl_sum_elim|].
    by iIntros "[?|?]"; [iApply upcl_sum_intro_l|iApply upcl_sum_intro_r].
  Qed.

End protocol_operators_properties.


(* ========================================================================== *)
(** * Protocol Ordering. *)

(* -------------------------------------------------------------------------- *)
(** Definition of Protocol Ordering. *)

Program Definition iProt_le {Σ} : iProtO -n> iProtO -n> iPropO Σ :=
  (λne Ψ1 Ψ2, □ (∀ v Φ, Ψ1.(iProt_car) v Φ -∗ Ψ2.(iProt_car) v Φ))%I.
Next Obligation.
  intros ???. repeat (apply iProt_car_ne || f_equiv); done.
Defined.
Next Obligation.
  intros ????. simpl. repeat (apply iProt_car_ne || f_equiv); done.
Defined.

Infix "⊑" := (iProt_le) (at level 70, only parsing) : iprot_scope.


(* -------------------------------------------------------------------------- *)
(** Properties of Protocol Ordering. *)

Section protocol_ordering_properties.
  Context {Σ : gFunctors}.
  Implicit Types Ψ : iProt Σ.

  (* Non-expansiveness. *)
  Global Instance iProt_le_ne n :
    Proper ((dist n) ==> (dist n)) (iProt_le (Σ:=Σ)).
  Proof.
    rewrite /iProt_le. intros ????.
    repeat (apply iProt_car_ne || f_equiv); done.
  Qed.
  Global Instance iProt_le_proper :  Proper ((≡) ==> (≡)) (iProt_le (Σ:=Σ)).
  Proof.
    intros ????. apply equiv_dist=>n; apply iProt_le_ne; by apply equiv_dist.
  Qed.
 
  (* (⊑) is a preorder. *)
  Lemma iProt_le_refl Ψ : ⊢ (Ψ ⊑ Ψ)%iprot.
  Proof. iModIntro. by iIntros (v Φ) "H". Qed.
  Lemma iProt_le_trans Ψ1 Ψ2 Ψ3 : (Ψ1 ⊑ Ψ2 -∗ Ψ2 ⊑ Ψ3 -∗ Ψ1 ⊑ Ψ3)%iprot.
  Proof.
    iIntros "#H12 #H23". iModIntro. iIntros (v Φ) "H1".
    iApply "H23". by iApply "H12".
  Qed.

  (* Bottom protocol is the bottom element of (⊑). *)
  Lemma iProt_le_bottom Ψ : ⊢ (⊥ ⊑ Ψ)%iprot.
  Proof. iModIntro. by iIntros (v Φ) "H". Qed.

  Lemma iProt_le_sum_l Ψ1 Ψ2 : ⊢ (Ψ1 ⊑ Ψ1 <+> Ψ2)%iprot.
  Proof. iModIntro. iIntros (v Φ) "H". by rewrite iProt_sum_eq //=; iLeft. Qed.
  Lemma iProt_le_sum_r Ψ1 Ψ2 : ⊢ (Ψ2 ⊑ Ψ1 <+> Ψ2)%iprot.
  Proof. rewrite (iProt_sum_comm Ψ1 Ψ2). by iApply iProt_le_sum_l. Qed.

  Lemma iProt_le_sum Ψ1 Ψ2 Ψ1' Ψ2' :
    (Ψ1 ⊑ Ψ1' -∗ Ψ2 ⊑ Ψ2' -∗ Ψ1 <+> Ψ2 ⊑ Ψ1' <+> Ψ2')%iprot.
  Proof.
    iIntros "#HΨ1 #HΨ2". iModIntro. iIntros (v Φ).
    rewrite !iProt_sum_eq //=.
    by iIntros "[Hprot|Hprot]"; [iLeft; iApply "HΨ1"| iRight; iApply "HΨ2"].
  Qed.

  Lemma iProt_le_marker f Ψ1 Ψ2 : (Ψ1 ⊑ Ψ2 -∗ (f #> Ψ1) ⊑ (f #> Ψ2))%iprot.
  Proof.
    iIntros "#HΨ". iModIntro. iIntros (v Φ).
    rewrite iProt_marker_eq //=. iIntros "[%w [-> Hprot]]".
    iExists w. iSplit; [done|]. by iApply "HΨ".
  Qed.

  Lemma iProt_le_upcl Ψ1 Ψ2 : (Ψ1 ⊑ Ψ2 -∗ (upcl Ψ1) ⊑ (upcl Ψ2))%iprot.
  Proof.
    iIntros "#Hle" (v Φ) "!# [%Φ' [HΨ1 HΦ']]".
    iExists Φ'. iSplitL "HΨ1"; [by iApply "Hle"|].
    done.
  Qed.

End protocol_ordering_properties.
