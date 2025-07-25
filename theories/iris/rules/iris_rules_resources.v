From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
Require Import Coq.Program.Equality.
From Wasm.iris.language Require Export iris_ewp_ctx.
From Wasm.iris.helpers Require Export iris_properties.

Import uPred.

Set Bullet Behavior "Strict Subproofs".

Set Default Proof Using "Type". 
Close Scope byte_scope.

Section iris_rules_resources.

Let reducible := @reducible wasm_lang.

Context `{!wasmG Σ}.

Lemma mem_block_lookup_data wms n mem:
  ⊢ (gen_heap_interp (gmap_of_memory wms)) -∗
  (gen_heap_interp (gmap_of_list (fmap length_mem wms))) -∗
  n ↦[wmblock] mem -∗
  ⌜ ∃ m, wms !! (N.to_nat n) = Some m /\ m.(mem_data).(ml_data) = mem.(mem_data).(ml_data)⌝.
Proof.
  iIntros "Hwm Hwmlength Hm".
  iDestruct "Hm" as "(Hmelem & Hmlength & _)".
  iDestruct (gen_heap_valid with "Hwmlength Hmlength") as "%Hmlength".
  rewrite gmap_of_list_lookup list_lookup_fmap in Hmlength.
  destruct (wms !! N.to_nat n) eqn:Hmem => //.
  iAssert (⌜∀ i, mem.(mem_data).(ml_data) !! i = m.(mem_data).(ml_data) !! i⌝%I) as "%Hmldata".
  {
    iIntros (i).
    destruct (mem.(mem_data).(ml_data) !! i) eqn:Hmemdata => /=.
    - iDestruct (big_sepL_lookup with "Hmelem") as "Hmelem" => //.
      iDestruct (gen_heap_valid with "Hwm Hmelem") as "%Hmelem".
      rewrite gmap_of_list_2d_lookup list_lookup_fmap Hmem in Hmelem.
      simpl in Hmelem.
      by rewrite Nat2N.id in Hmelem.
    - rewrite -> lookup_ge_None in Hmemdata.
      iPureIntro. symmetry.
      rewrite -> lookup_ge_None.
      repeat unfold length_mem, memory_list.length_mem in Hmlength.
      simpl in Hmlength.
      inversion Hmlength; subst; clear Hmlength.
      apply Nat2N.inj in H0.
      by lias.
  }
  iPureIntro.
  exists m.
  split => //.
  by apply list_eq.
Qed.

Lemma mem_block_lookup wms n mem:
  ⊢ (gen_heap_interp (gmap_of_memory wms)) -∗
  (gen_heap_interp (gmap_of_list (fmap length_mem wms))) -∗
  (@gen_heap_interp _ _ _ _ _ memlimit_hsG (gmap_of_list (fmap mem_max_opt wms))) -∗
  n ↦[wmblock] mem -∗
  ⌜ ∃ m, wms !! (N.to_nat n) = Some m /\ m.(mem_data).(ml_data) = mem.(mem_data).(ml_data) /\ m.(mem_max_opt) = mem.(mem_max_opt)⌝.
Proof.
  iIntros "Hwm Hwmlength Hwmlimit Hm".
  unfold mem_block.
  iDestruct "Hm" as "(Hmelem & Hmlength & Hmlimit)".
  iDestruct (gen_heap_valid with "Hwmlimit Hmlimit") as "%Hmlimit".
  rewrite gmap_of_list_lookup list_lookup_fmap in Hmlimit.
  iDestruct (mem_block_lookup_data with "Hwm Hwmlength [$]") as "%H".
  destruct (wms !! N.to_nat n) eqn:Hmem => //.
  destruct H as [m0 [Hmeq Hmdata]].
  inversion Hmeq; subst; clear Hmeq.
  iPureIntro.
  exists m0.
  repeat split => //.
  simpl in Hmlimit.
  by inversion Hmlimit.
Qed.

Lemma tab_block_lookup_data wts n tab:
  ⊢ (gen_heap_interp (gmap_of_table wts)) -∗
  (gen_heap_interp (gmap_of_list (fmap tab_size wts))) -∗
  n ↦[wtblock] tab -∗
  ⌜ ∃ t, wts !! (N.to_nat n) = Some t /\ t.(table_data) = tab.(table_data)⌝.
Proof.
  iIntros "Hwt Hwtsize Ht".
  unfold tab_block.
  iDestruct "Ht" as "(Htelem & Htsize & Htlimit)".
  iDestruct (gen_heap_valid with "Hwtsize Htsize") as "%Htsize".
  rewrite gmap_of_list_lookup list_lookup_fmap in Htsize.
  destruct (wts !! N.to_nat n) eqn:Htab => //.
  
  iAssert (⌜∀ i, tab.(table_data) !! i = t.(table_data) !! i⌝%I) as "%Htdata".
  {
    iIntros (i).
    destruct (tab.(table_data) !! i) eqn:Htdata => /=.
    - iDestruct (big_sepL_lookup with "Htelem") as "Htelem" => //.
      iDestruct (gen_heap_valid with "Hwt Htelem") as "%Htelem".
      rewrite gmap_of_list_2d_lookup list_lookup_fmap Htab in Htelem.
      simpl in Htelem.
      by rewrite Nat2N.id in Htelem.
    - rewrite -> lookup_ge_None in Htdata.
      iPureIntro. symmetry.
      rewrite -> lookup_ge_None.
      unfold tab_size in Htsize.
      simpl in *.
      inversion Htsize; by lias.
  }
  iPureIntro.
  exists t.
  split => //.
  by apply list_eq.
Qed.

Lemma tab_block_lookup wts n tab:
  ⊢ (gen_heap_interp (gmap_of_table wts)) -∗
  (gen_heap_interp (gmap_of_list (fmap tab_size wts))) -∗
  (@gen_heap_interp _ _ _ _ _ tablimit_hsG (gmap_of_list (fmap table_max_opt wts))) -∗
  n ↦[wtblock] tab -∗
  ⌜ wts !! (N.to_nat n) = Some tab⌝.
Proof.
  iIntros "Hwt Hwtsize Hwtlimit Ht".
  unfold tab_block.
  iDestruct "Ht" as "(Htelem & Htsize & Htlimit)".
  iDestruct (gen_heap_valid with "Hwtlimit Htlimit") as "%Htlimit".
  rewrite gmap_of_list_lookup list_lookup_fmap in Htlimit.
  iDestruct (tab_block_lookup_data with "Hwt Hwtsize [$]") as "%H".
  destruct (wts !! N.to_nat n) eqn:Htab => //.
  destruct H as [t0 [Hteq Htdata]].
  inversion Hteq; subst; clear Hteq.
  iPureIntro.
  simpl in Htlimit.
  inversion Htlimit; subst; clear Htlimit.
  destruct t0, tab.
  simpl in *.
  by subst.
Qed.


(* Instance related *)

Lemma ewp_get_local (E : coPset) (v: value) (i: nat) Ψ (Φ: iris.val -> frame -> iProp Σ) f:
  (f_locs f) !! i = Some v -> 
  ▷Φ (immV [v]) f -∗
   EWP ([AI_basic (BI_get_local i)]) UNDER f @ E <| Ψ |> {{ w ; h , Φ w h }}.
Proof.
  iIntros (Hlook) "HΦ".
  iApply ewp_lift_atomic_step => //=.
  iIntros (σ) "Hσ !>".
  rewrite - nth_error_lookup in Hlook.
  iSplit.
  - iPureIntro.
    exists [], [AI_const v], (σ, f_locs f, f_inst f), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_get_local => //.
  - iIntros "!>" (es ??? HStep) "!>".
    destruct HStep as [H _].
    only_one_reduction H.
    destruct f; iFrame.
    unfold to_val => //=. rewrite to_val_instr_AI_const //=.
Qed.

Lemma ewp_set_local (E : coPset) (v : value) (i: nat) Ψ (Φ: iris.val -> frame -> iProp Σ) f:
  i < length (f_locs f) ->
  ▷ Φ (immV []) (Build_frame (set_nth v (f_locs f) i v) (f_inst f)) -∗
    EWP ([AI_const v; AI_basic (BI_set_local i)]) UNDER f @ E <| Ψ |> {{ w ; h , Φ w h }}.
Proof.
  iIntros (Hlen) "HΦ".
  iApply ewp_lift_atomic_step => //=.
  rewrite /to_val /= merge_prepend to_val_instr_AI_const //.
  rewrite /to_eff /= merge_prepend to_val_instr_AI_const //.
  
  iIntros (σ) "Hσ !>".
  iSplit.
  - iPureIntro.
    exists [], [], (σ, set_nth v (f_locs f) i v, (f_inst f)), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply r_set_local => //=.
    rewrite -(rwP ssrnat.leP). lia.
  - iIntros "!>" (es ??? HStep).
    iModIntro.
    destruct HStep as [H _].
    eapply reduce_det in H as [-> [H | [ [? Hstart] |  (?&?&?&Hstart & Hstart1 & Hstart2
                                                               & Hσ)]]] ;
      last (eapply r_set_local with (f' := {| f_locs := set_nth v (f_locs f) i v; f_inst := f_inst f |}); eauto) ;
    try by unfold first_instr in Hstart ; simpl in Hstart ; inversion Hstart.
    destruct H as [<- <-].
    iFrame "# ∗ %". 
    rewrite separate1 -cat_app first_instr_const // in Hstart.
    rewrite /= const_const //.
    rewrite -(rwP ssrnat.leP) /=. lia.
Qed.

Lemma ewp_tee_local (E : coPset) (v : value) (i : nat) Ψ (Φ : iris.val -> frame -> iProp Σ) f :
  ⊢ 
    ▷ (EWP [AI_const v ; AI_const v ;
                       AI_basic (BI_set_local i)]
                     UNDER f @ E <| Ψ |> {{ Φ }}) -∗
             EWP [AI_const v ; AI_basic (BI_tee_local i)] UNDER f @ E <| Ψ |> {{ Φ }}.
Proof.
  iIntros "Hwp".
  iApply ewp_lift_step => //=.
  rewrite /to_val /= merge_prepend to_val_instr_AI_const //.
  rewrite /to_eff /= merge_prepend to_val_instr_AI_const //.
  iIntros (σ) "Hσ".
  iApply fupd_mask_intro ; first by solve_ndisj.
  iIntros "Hfupd".
  iSplit.
  - iPureIntro.
    unfold reducible, language.prim_step => //=.
    eexists _,_,(_,_,_),_.
    repeat split => //=.
    apply r_simple, rs_tee_local.
    rewrite const_const //.
  - iIntros "!>" (es ??? HStep).
    iMod "Hfupd".
    iModIntro.
    destruct HStep as [H _].
    edestruct reduce_det.
    exact H.
    constructor. constructor. rewrite const_const //.
    inversion H0; subst; clear H0.
    destruct H1 as [[-> ->]| H0].
    destruct f; iFrame.
    destruct H0 as [[??]|(?&?&?&?&_)].
    rewrite separate1 -cat_app first_instr_const // in H0.
    rewrite /= const_const //.
    rewrite separate1 -cat_app first_instr_const // in H0.
    rewrite /= const_const //.
Qed.

Lemma ewp_get_global (E : coPset) (v: value_num) (f: frame) (n: nat) Ψ (Φ: iris.val -> frame -> iProp Σ) (g: global) (k: nat) q:
  (f_inst f).(inst_globs) !! n = Some k ->
  g.(g_val) = v ->
  ▷ Φ(immV [VAL_num v]) f -∗
    N.of_nat k ↦[wg]{ q } g -∗
  EWP ([AI_basic (BI_get_global n)]) UNDER f @ E <| Ψ |> {{ w ; h, Φ w h ∗ N.of_nat k ↦[wg]{ q } g }}.
Proof.
  iIntros (Hinstg Hgval) "HΦ Hglob".
  iApply (ewp_wand _ _ _ _ _ (λ w h, (Φ w h ∗ N.of_nat k↦[wg]{ q } g))%I with "[-]") ;[|by iIntros (??) "?";iFrame].
  iApply ewp_lift_atomic_step => //=.
  iIntros (σ) "Hσ !>".
  iDestruct "Hσ" as "(? & ? & ? & ? & ? & Hg & Hi & ? & ?)".
  iDestruct (gen_heap_valid with "Hg Hglob") as "%Hglob".
  simplify_map_eq.
  rewrite gmap_of_list_lookup Nat2N.id in Hglob.
  rewrite - nth_error_lookup in Hglob.
  rewrite - nth_error_lookup in Hinstg.
  assert ( sglob_val σ
                     (f_inst {| f_locs := f_locs f; f_inst := f_inst f |}) n =
           Some (g_val g) ) as Hsglob.
  { unfold sglob_val, option_map, sglob, option_bind, operations.option_bind, sglob_ind => /=.
    by rewrite Hinstg Hglob.
  }
  iSplit.
  - iPureIntro.
    unfold reducible, language.prim_step => /=.
    eexists [], [AI_basic (BI_const (g_val g))], (_, _, _), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    by apply r_get_global.
  - iIntros "!>" (es ??? HStep) "!>".
    destruct HStep as [H _].
    only_one_reduction H. destruct f; iFrame.
(*    rewrite to_val_AI_const.
    iFrame. *)
Qed.

Lemma ewp_set_global (E : coPset) (v: value_num) (f: frame) (n: nat) Ψ (Φ: iris.val -> frame -> iProp Σ) (g: global) (k: nat):
  (f_inst f).(inst_globs) !! n = Some k ->
  ▷ Φ (immV []) f -∗
  N.of_nat k ↦[wg] g -∗
  EWP [AI_basic (BI_const v); AI_basic (BI_set_global n)] UNDER f @ E <| Ψ |> {{ w ; h , Φ w h ∗ N.of_nat k ↦[wg] Build_global (g_mut g) v }}.
Proof.
  iIntros (Hinstg) "HΦ Hglob".
  iApply (ewp_wand _ _ _ _ _ (λ w h, (Φ w h ∗ N.of_nat k ↦[wg] Build_global (g_mut g) v) )%I with "[-]");[|by iIntros (??) "?";iFrame].
  iApply ewp_lift_atomic_step => //=.
  iIntros (σ) "Hσ !>".

  iDestruct "Hσ" as "(? & ? & ? & ? & ? & Hg & Hi & ?)".
  iDestruct (gen_heap_valid with "Hg Hglob") as "%Hglob".
  
  simplify_map_eq.
  rewrite gmap_of_list_lookup Nat2N.id in Hglob.
  rewrite - nth_error_lookup in Hglob.
  rewrite - nth_error_lookup in Hinstg.
  assert (supdate_glob σ
                       (f_inst {| f_locs := f_locs f; f_inst := f_inst f |}) n v = 
            Some
    {|
      s_funcs := s_funcs σ;
      s_tables := s_tables σ;
      s_mems := s_mems σ;
      s_conts := s_conts σ;
      s_exns := s_exns σ;
      s_tags := s_tags σ;
      s_globals :=
        update_list_at (s_globals σ) k {| g_mut := g_mut g; g_val := v |}
    |}) as Hsglob.
  { unfold supdate_glob, supdate_glob_s, option_map, sglob, option_bind, operations.option_bind, sglob_ind => /=.
    by rewrite Hinstg Hglob.
  } 
  iSplit.
  - iPureIntro.
    unfold reducible, language.prim_step => /=.
    eexists [], _, (_, _, _), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_set_global;eauto.
    
  - iIntros "!>" (es ??? HStep).
    destruct HStep as [H _].
    only_one_reduction H.
    iMod (gen_heap_update with "Hg Hglob") as "[Hg Hglob]".
    destruct f; iFrame. rewrite nth_error_lookup in Hglob.
    apply lookup_lt_Some in Hglob as Hlt.
    rewrite -update_list_at_is_set_nth;[|apply/ssrnat.leP; rewrite -length_is_size;lia].
    rewrite -fmap_insert_set_nth//.
    rewrite -gmap_of_list_insert;[|by rewrite Nat2N.id].
    rewrite Nat2N.id. by iFrame.
(*    rewrite separate1 -cat_app first_instr_const // in Hstart.
    rewrite /= const_const //. *)
Qed.

(* Auxiliary lemmas for load/store *)

Lemma mem_update_length dat dat' k b:
  mem_update k b dat = Some dat' -> length (ml_data dat) = length (ml_data dat').
Proof.
  intros Hupd.
  unfold mem_update in Hupd.
  destruct ( _ <? _)%N eqn:Hl ; inversion Hupd; clear Hupd.
  subst => /=.
  rewrite split_preserves_length => //.
  remember (length _) as x.
  move/N.ltb_spec0 in Hl; by lias.
Qed.

Lemma length_store (m m': memory) (n: N) (off: static_offset) (bs: bytes) :
  store m n off bs (length bs) = Some m' -> 
  length m.(mem_data).(ml_data) = length m'.(mem_data).(ml_data).
Proof.
  intros.
  unfold store, write_bytes, fold_lefti in H.
  destruct (_ <=? _)%N eqn:Hlen ; try by inversion H.
  cut (forall j dat dat',
          j <= length bs ->
          let i := length bs - j in
          (let '(_,acc_end) :=
            fold_left
              (λ '(k, acc) x,
                (k + 1,
                  match acc with
                  | Some dat => mem_update (n + off + N.of_nat k)%N x dat
                  | None => None
                  end)) (bytes_takefill #00%byte j (drop i bs))
              (i, Some dat) in acc_end) = Some dat' ->
                               length (ml_data dat) = length (ml_data (mem_data m)) ->
                               length (ml_data dat') = length (ml_data (mem_data m))).
  - intros Hi.
    assert (length bs <= length bs) ; first lia.
    destruct (let '(_, acc_end) := fold_left _ _ _ in acc_end) eqn:Hfl ; try by inversion H.
    apply (Hi _ (mem_data m) m0) in H0 => //=.
    + destruct m' ; inversion H ; by subst.
    + rewrite PeanoNat.Nat.sub_diag.
      unfold drop.
      exact Hfl.
  - induction j ; intros ; subst i.
    + rewrite Nat.sub_0_r in H1.
      rewrite drop_all in H1.
      simpl in H1. inversion H1. by rewrite - H4.
    + assert (j <= length bs) ; first lia.
      destruct (drop (length bs - S j) bs) eqn:Hdrop.
      * assert (length (drop (length bs - S j) bs) = 0) ; first by rewrite Hdrop.
        rewrite length_drop in H4. lia.
      * assert (exists dat0, mem_update (n + off + N.of_nat (length bs - S j))%N
                                   b dat = Some dat0) as [dat0 Hdat0].
         { unfold mem_update. apply N.leb_le in Hlen.
           assert (n + off + N.of_nat (length bs - S j) <
                     N.of_nat (length (ml_data dat)))%N.
           rewrite H2.
           unfold length_mem, memory_list.length_mem in Hlen.
           lia.
           apply N.ltb_lt in H4.
           rewrite H4.
           by eexists _. } 
        apply (IHj dat0 dat') in H3.
        ++ done.
        ++ simpl in H1.
           rewrite Hdat0 in H1.
           replace (length bs - j) with (length bs - S j + 1) ; last lia.
           rewrite - drop_drop.
           rewrite Hdrop.
           unfold drop => //=.
        ++ erewrite <- mem_update_length => //=.
Qed.


Lemma store_mem_max_opt (m m' : memory) n off bs l :
  store m n off bs l = Some m' ->
  mem_max_opt m = mem_max_opt m'.
Proof.
  intros.
  unfold store in H.
  destruct ( _ <=? _)%N ; try by inversion H.
  unfold write_bytes in H.
  destruct (fold_lefti _ _ _) ; try by inversion H.
Qed.


Lemma those_app {A} (l1 : list (option A)) l2 tl1 tl2 :
  those l1 = Some tl1 -> those l2 = Some tl2 -> those (l1 ++ l2) = Some (tl1 ++ tl2).
Proof.
  by apply those_app.
Qed.

Lemma those_app_inv {A} (l1 : list (option A)) l2 tl :
  those (l1 ++ l2) = Some tl ->
  exists tl1 tl2, those l1 = Some tl1 /\ those l2 = Some tl2 /\ tl1 ++ tl2 = tl.
Proof.
  by apply those_app_inv.
Qed.


Lemma wms_append n k b bs :
  ⊢ (n ↦[wms][k] (b :: bs) ∗-∗ ( n↦[wm][k] b ∗ n↦[wms][N.add k 1%N] bs))%I.
Proof.
  iSplit.
  - iIntros "Hwms". unfold mem_block_at_pos, big_opL. rewrite Nat.add_0_r.
    rewrite N2Nat.id.
    fold (big_opL (M := iPropI Σ)).
    iDestruct "Hwms" as "[Hwm Hwms]".
    iSplitL "Hwm" => //=.
    iApply (big_sepL_impl with "Hwms").
    iIntros (k0 x) "!> %Hx Hwm".
    replace (N.to_nat k + S k0) with (N.to_nat (k+1) + k0) => //=.
    lia.
  - iIntros "[Hwm Hwms]". unfold mem_block_at_pos, big_opL.
    rewrite Nat.add_0_r N2Nat.id.
    fold (big_opL (M := iPropI Σ)).
    iSplitL "Hwm" => //=.
    iApply (big_sepL_impl with "Hwms").
    iIntros (k0 x) "!> %Hx Hwm".
    replace (N.to_nat (k+1) + k0) with (N.to_nat k + S k0) => //=.
    lia.
Qed.

Lemma map_iota_lift {A} (f : nat -> A) g n len :
  (forall x, f (x + 1) = g x) -> map f (iota (n+1) len) = map g (iota n len).
Proof.
  intros Hfg.
  generalize dependent n.
  induction len ; intros => //=.
  rewrite Hfg. replace (S (n+1)) with (S n + 1) ; last lia.
  rewrite IHlen. done.
Qed. 

Lemma load_append m k off b bs :
  load m k off (length (b :: bs)) = Some (b :: bs) ->
  load m k (off + 1)%N (length bs) = Some bs.
Proof.
  unfold load ; intros Hm.
  replace (off + N.of_nat (length (b :: bs)))%N with
    (off + 1 + N.of_nat (length bs))%N in Hm ; last by simpl ; lia.
  destruct (k + (off + 1 + N.of_nat (length bs)) <=? length_mem m)%N ; try by inversion Hm.
  unfold read_bytes. unfold read_bytes in Hm. simpl in Hm.
  destruct (mem_lookup (k + off + N.of_nat 0)%N (mem_data m)) ; inversion Hm.
  rewrite list_extra.cons_app in H0.
  destruct (those_app_inv [Some b0] _ _ H0) as (tl1 & tl2 & Htl1 & Htl2 & Htl).
  unfold those in Htl1. simpl in Htl1. inversion Htl1 ; subst ; clear Htl1.
  inversion Htl ; subst ; clear Htl.
  erewrite <- map_iota_lift => //=.
  intros. replace (k + off + N.of_nat (x+1))%N with
    (k + (off + 1) + N.of_nat x)%N => //=.
  lia.
Qed.

Lemma list_trivial_replace {A} l (x : A) k :
  l !! k = Some x ->
  cat (seq.take k l) (cat [x] (seq.drop (k+1) l)) = l.
Proof.
  generalize dependent k.
  induction l ; intros ; destruct k ; inversion H.
  - simpl. by rewrite drop0. 
  - apply IHl in H1. simpl. rewrite H1. done.
Qed.

Lemma trivial_update m k b :
  read_bytes m k 1 = Some [b] ->
  mem_update k b (mem_data m) = Some (mem_data m).
Proof.
  intro Hread.
  unfold mem_update.
  unfold read_bytes in Hread.
  unfold those in Hread.
  simpl in Hread.
  rewrite N.add_0_r in Hread.
  destruct (mem_lookup k (mem_data m)) eqn:Hlookup ; inversion Hread ; subst ; clear Hread.
  unfold mem_lookup in Hlookup.
  rewrite nth_error_lookup in Hlookup.
  assert (k < N.of_nat (length (ml_data (mem_data m))))%N.
  { apply lookup_lt_Some in Hlookup. lia. } 
  apply N.ltb_lt in H.
  rewrite H.
  rewrite list_trivial_replace => //=.
  by destruct (mem_data m).
Qed.


Definition incr_fst {A} (a : nat * A) := (fst a + 1,snd a).

Lemma incr_fst_equals {A} x n (o : A) :
  incr_fst x = (n,o) -> x = (n-1,o).
Proof.
  intros ; destruct x. unfold incr_fst in H. simpl in H.
  inversion H; subst; f_equal; by lias.
Qed.

Lemma fold_left_lift {A B} (f : (nat * A) -> B -> (nat * A)) g l i acc :
  (forall i acc x, f (i+1,acc) x = incr_fst (g (i,acc) x)) ->
  fold_left f l (i+1,acc) = incr_fst (fold_left g l (i,acc)).
Proof. 
  intros Hfg.
  generalize dependent i.
  generalize dependent acc.
  induction l ; intros => //=.
  rewrite Hfg.
  destruct (g (i, acc) a).
  unfold incr_fst => //=.
Qed.


Lemma store_append1 m k off b bs m':
  store m k off (b :: bs) (length (b :: bs)) = Some m' ->
  exists m'', store m'' k (off + 1)%N bs (length bs) = Some m' /\
           store m k off [b] 1 = Some m''.
Proof.
  intro Hstore.
  unfold store.
  unfold store in Hstore.
  destruct (k + off + N.of_nat (length (b :: bs)) <=? length_mem m)%N eqn:Hlen ;
    try by inversion Hstore.
  apply N.leb_le in Hlen.
  simpl in Hlen.
  assert (k + off + N.of_nat 1 <= length_mem m)%N ; first lia.
  apply N.leb_le in H.
  rewrite H.
  unfold write_bytes, fold_lefti => //=.
  rewrite N.add_0_r.
  unfold mem_update.
  unfold length_mem, memory_list.length_mem in H.
  apply N.leb_le in H.
  assert (k + off < N.of_nat (length (ml_data (mem_data m))))%N ; first lia.
  apply N.ltb_lt in H0.
  rewrite H0.
  eexists _ ; split => //=.
  remember {| mem_data := _ ; mem_max_opt := _ |} as m''.
  assert (store m k off [b] 1 = Some m'').
  { subst. unfold store. apply N.leb_le in H. rewrite H.
    unfold write_bytes, fold_lefti => //=.
    unfold mem_update. rewrite N.add_0_r.
    rewrite H0. done. }
  assert (length_mem m'' = length_mem m).
  { unfold length_mem, memory_list.length_mem. erewrite <- length_store => //=.
    by instantiate (1 := [b]) => //=. }
  assert (mem_max_opt m'' = mem_max_opt m) as Hmax; first by 
    eapply Logic.eq_sym, store_mem_max_opt.  
  rewrite H2.
  assert (k + (off + 1) + N.of_nat (length bs) <= length_mem m)%N ; first lia.
  apply N.leb_le in H3. rewrite H3.
  unfold write_bytes, fold_lefti in Hstore.
  simpl in Hstore.
  rewrite N.add_0_r in Hstore.
  replace (mem_update (k + off)%N b (mem_data m)) with (Some (mem_data m'')) in Hstore.
  rewrite <- (plus_O_n 1) in Hstore.
  destruct (fold_left _ _ (0 + 1, _)) eqn:Hfl ; try by inversion Hstore.
  rewrite (fold_left_lift _ (λ '(k0, acc) x,
                              (k0 + 1,
                                match acc with
                                | Some dat =>
                                    if (k + (off + 1) + N.of_nat k0 <?
                                          N.of_nat (length (ml_data dat)))%N
                                    then
                                      Some {| ml_data :=
                                             seq.take (N.to_nat (k + (off + 1) +
                                                                   N.of_nat k0))
                                                      (ml_data dat) ++
                                                      x :: seq.drop (N.to_nat (k + (off + 1) + N.of_nat k0) + 1)
                                                      (ml_data dat)
                                           |}
                                    else None
                                | None => None
                                end)))
    in Hfl.
  apply incr_fst_equals in Hfl.
  rewrite Hfl.
  rewrite Hmax.
  done.
  intros. unfold incr_fst => //=.
  unfold mem_update.
  replace (k + off + N.of_nat (i+1))%N with (k + (off + 1) + N.of_nat i)%N ; last lia.
  done.
  unfold store in H1.
  apply N.leb_le in H.
  rewrite H in H1.
  unfold write_bytes, fold_lefti in H1.
  simpl in H1.
  rewrite N.add_0_r in H1.
  destruct (mem_update (k + off)%N b (mem_data m)) eqn:Hupd ; try by inversion H1.
Qed.


Lemma enough_space_to_store m k off bs :
  (k + off + N.of_nat (length bs) <= length_mem m)%N ->
  exists mf, store m k off bs (length bs) = Some mf.
Proof.
  intros Hmlen.
  unfold store.
  apply N.leb_le in Hmlen.
  rewrite Hmlen.
  unfold write_bytes, fold_lefti. 
  cut (forall i dat,
          i <= length bs ->
          length (ml_data dat) = N.to_nat (length_mem m) ->
          let j := length bs - i in
          exists datf, (let '(_, acc_end) :=
                      fold_left (λ '(k0,acc) x,
                                  (k0 + 1,
                                    match acc with
                                    | Some dat => mem_update (k + off + N.of_nat k0)%N x dat
                                    | None => None
                                    end)) (bytes_takefill #00%byte (length (drop j bs))
                                                          (drop j bs))
                                (j, Some dat) in acc_end) = Some datf).
  - intros H.
    assert (length bs <= length bs) ; first lia.
    apply (H _ (mem_data m)) in H0 as [datf' Hdatf'].
    + rewrite PeanoNat.Nat.sub_diag in Hdatf'.
      unfold drop in Hdatf'.
      rewrite Hdatf'.
      by eexists _.
    + unfold length_mem, memory_list.length_mem.
      by rewrite Nat2N.id.
  - induction i ; intros ; subst j.
    + rewrite Nat.sub_0_r.
      rewrite drop_all => //=.
      by eexists _.
    + assert (i <= length bs) ; first lia.
      destruct (drop (length bs - S i) bs) eqn:Hdrop.
      * assert (length (drop (length bs - S i) bs) = 0) ; first by rewrite Hdrop.
        rewrite length_drop in H2. lia.
      * assert (exists datupd,
                   mem_update (k + off + N.of_nat (length bs - S i))%N b dat =
                     Some datupd ) as [datupd Hdatupd].
        { unfold mem_update.
           apply N.leb_le in Hmlen.
           assert ( k + off + N.of_nat (length bs - S i) <
                      N.of_nat (length (ml_data dat)))%N ;
             first lia.
           apply N.ltb_lt in H2 ; rewrite H2.
           by eexists _. }
        eapply (IHi datupd) in H1 as [datf Hdatf].
        ++ rewrite - Hdrop. rewrite length_drop.
           rewrite <- (take_drop 1 (drop (length bs - S i) bs)).
           rewrite drop_drop.
           rewrite Hdrop.
           unfold take.
           replace (length bs - S i + 1) with (length bs - i) ; last lia.
           replace (length bs - (length bs - S i)) with (S i) ; last lia.
           simpl.
           replace (length bs - S i + 1) with (length bs - i) ; last lia.
           rewrite length_drop in Hdatf.
           replace (length bs - (length bs - i)) with i in Hdatf ; last lia.
           rewrite Hdatupd.
           rewrite Hdatf.
           by eexists _.
        ++ rewrite <- H0.
           by erewrite <- mem_update_length.
Qed.

Lemma mem_update_insert k b dat dat':
  mem_update k b dat = Some dat' ->
  dat' = Build_memory_list (<[(N.to_nat k) := b]> (ml_data dat)) /\
  (N.to_nat k) < length (ml_data dat).
Proof.
  unfold mem_update.
  destruct (k <? N.of_nat (length (ml_data dat)))%N eqn:Hk => //.
  move => Hupd.
  inversion Hupd; subst; clear Hupd.
  apply N.ltb_lt in Hk.
  split; last by lia.
  f_equal.
  rewrite - (list_insert_destruct (N.to_nat k) (ml_data dat) b) => //.
  lia.
Qed.
  
Lemma update_swap k b dat k' b' dat' dat'' :
  k <> k' ->
  mem_update k b dat = Some dat' ->
  mem_update k' b' dat' = Some dat'' ->
  exists dat0, mem_update k' b' dat = Some dat0 /\
            mem_update k b dat0 = Some dat''.
Proof.
  intros Hkk' Hupd Hupd'.
  apply mem_update_insert in Hupd as [Hupd Hk].
  apply mem_update_insert in Hupd' as [Hupd' Hk'].
  assert (length (ml_data dat) = length (ml_data dat')) as Hupdlen.
  { subst => /=.
    by rewrite length_insert.
  }
  exists (Build_memory_list (<[(N.to_nat k') := b']> (ml_data dat))).
  unfold mem_update.
  assert (k' <? N.of_nat (length (ml_data dat')))%N as Hk'0.
  { apply N.ltb_lt. lia. }
  assert (k <? N.of_nat (length (ml_data dat)))%N as Hk0.
  { apply N.ltb_lt. lia. }
  rewrite Hupdlen Hk'0 length_insert Hk0 => /=.
  subst.
  split; (do 2 f_equal); rewrite - list_insert_destruct; try by lias.
  rewrite list_insert_destruct; last by lias.
  simpl.
  rewrite list_insert_commute; last by lias.
  rewrite - (list_insert_destruct (N.to_nat k)) => //.
  by rewrite length_insert.
Qed.
  

Lemma swap_stores m m' m'' k off b bs :
  store m k off [b] 1 = Some m' ->
  store m' k (off + 1)%N bs (length bs) = Some m'' ->
  exists m0, store m k (off + 1)%N bs (length bs) = Some m0 /\
          store m0 k off [b] 1 = Some m''.
Proof.
  intros.
  assert (length_mem m = length_mem m') as Hmlen ;
    first (unfold length_mem, memory_list.length_mem ; erewrite length_store => //= ;
          by instantiate (1:=[b]) => //=).
  unfold store in H0.
  destruct (k + (off + 1) + N.of_nat (length (bs)) <=? length_mem m')%N eqn:Hlen ;
    try by inversion H0.
  apply N.leb_le in Hlen.
  rewrite <- Hmlen in Hlen.
  destruct (enough_space_to_store m k (off + 1)%N (bs)) as [m0 Hm0] => //=.
  exists m0 ; split => //=.
  unfold store, write_bytes, fold_lefti => //=.
  assert (length_mem m = length_mem m0) as Hmlen0 ;
    first by unfold length_mem, memory_list.length_mem ; erewrite length_store.
  rewrite Hmlen0 in Hlen.
  assert (k + off + 1 <= length_mem m0)%N ; first lia.
  apply N.leb_le in H1 ; rewrite H1.
  rewrite N.add_0_r.
  unfold mem_update.
  apply N.leb_le in H1.
  assert (k + off < N.of_nat (length (ml_data (mem_data m0))))%N ;
    first by unfold length_mem, memory_list.length_mem in H1 ; lia.
  apply N.ltb_lt in H2.
  rewrite H2.
  rewrite - H0.
  unfold write_bytes, fold_lefti.
  unfold store, write_bytes, fold_lefti in H.
  rewrite - Hmlen0 in H1.
  apply N.leb_le in H1 ; rewrite H1 in H.
  simpl in H.
  rewrite N.add_0_r in H.
  unfold mem_update in H.
  replace (length (ml_data (mem_data m0))) with (length (ml_data (mem_data m)))
    in H2 ; last by eapply length_store.
  rewrite H2 in H.
  inversion H.
  unfold store in Hm0.
  rewrite - Hmlen0 in Hlen.
  apply N.leb_le in Hlen ; rewrite Hlen in Hm0.
  unfold write_bytes, fold_lefti in Hm0.
  destruct (fold_left _ _ _) eqn:Hfl.
  destruct o ; inversion Hm0.
  simpl.
  assert (m1 = mem_data m0) ; first by rewrite - H5.
  (*    simpl in Hfl. *)
  cut (forall i dat datf n,
          i <= length bs ->
          length (ml_data dat) = N.to_nat (length_mem m) ->
          let j := length bs - i in
          fold_left (λ '(k0, acc) x,
                      (k0 + 1,
                        match acc with
                        | Some dat => mem_update (k + (off + 1) + N.of_nat k0)%N x dat
                        | None => None
                        end)) (bytes_takefill #00%byte (length (drop j bs))
                                              (drop j bs))
                    (j, Some dat) = (n, Some datf) ->
          exists m, fold_left (λ '(k0, acc) x,
                           (k0 + 1,
                             match acc with
                             | Some dat => mem_update (k + (off + 1) + N.of_nat k0)%N
                                                     x dat
                             | None => None
                             end)) (bytes_takefill #00%byte (length (drop j bs))
                                                   (drop j bs))
                         (j, mem_update (k + off)%N b dat) =
                 (m, mem_update (k + off)%N b datf)).
  - intros Hi.
    assert (length bs <= length bs) as Hlbs; first lia.
    apply (Hi _ (mem_data m) m1 n) in Hlbs as [nn Hia].
    + rewrite PeanoNat.Nat.sub_diag in Hia.
      unfold drop in Hia.
      unfold mem_update in Hia.
      rewrite H2 in Hia.
      rewrite Hia.
      rewrite H3.
      unfold length_mem, memory_list.length_mem in Hmlen0 ; rewrite Hmlen0 in H2 ;
        rewrite H2.
      done.
    + unfold length_mem, memory_list.length_mem.
      by rewrite Nat2N.id.
    + rewrite PeanoNat.Nat.sub_diag.
      unfold drop.
      done.
  - induction i ; intros ; subst j.
    + rewrite Nat.sub_0_r.
      rewrite drop_all.
      simpl.
      rewrite Nat.sub_0_r in H8.
      rewrite drop_all in H8.
      simpl in H8.
      inversion H8.
      by eexists _.
    + assert (i <= length bs) ; first lia.
      destruct (drop (length bs - S i) bs) eqn:Hdrop.
      * assert (length (drop (length bs - S i) bs) = 0) ; first by rewrite Hdrop.
        rewrite length_drop in H10. lia.
      * assert (exists dat', mem_update (k + off)%N b dat = Some dat') as [dat' Hdat'].
        { unfold mem_update. rewrite H7 Nat2N.id H2. by eexists _. }
        assert (exists dat'',
                   mem_update (k + (off + 1) + N.of_nat (length bs - S i))%N b0 dat'
                   = Some dat'') as [dat'' Hdat''].
        { unfold mem_update.
          erewrite <- mem_update_length => //=.
          rewrite H7 Nat2N.id.
          apply N.leb_le in Hlen.
          assert (k + (off + 1) + N.of_nat (length bs - S i) < N.of_nat (length (ml_data (mem_data m))))%N.
          { unfold length_mem, memory_list.length_mem in Hlen.
            assert (N.of_nat (length bs - S i) < N.of_nat (length bs))%N ; lia. }
          apply N.ltb_lt in H10.
          rewrite H10.
          by eexists _. }
        rewrite - Hdrop.
        assert (k + off <> k + (off + 1) + N.of_nat (length bs - S i))%N ; first lia.
        destruct (update_swap _ _ _ _ _ _ _ H10 Hdat' Hdat'')
          as (dat0 & Hdat0 & Hdat0'') => //=.
        eapply (IHi dat0) in H9 as [nn Hflf].
        ++ rewrite length_drop.
           rewrite <- (take_drop 1 (drop (length bs - S i) bs)).
           rewrite drop_drop.
           rewrite Hdrop.
           unfold take.
           replace (length bs - S i + 1) with (length bs - i) ; last lia.
           replace (length bs - (length bs - S i)) with (S i) ; last lia.
           simpl.
           replace (length bs - S i + 1) with (length bs - i) ; last lia.
           rewrite length_drop in Hflf.
           replace (length bs - (length bs - i)) with i in Hflf ; last lia.
           rewrite Hdat' Hdat''.
           rewrite - Hdat0''.
           rewrite Hflf.
           by eexists _.
        ++ erewrite <- mem_update_length => //=.
        ++ rewrite - Hdrop in H8.
           rewrite length_drop in H8.
           replace (length bs - (length bs - S i)) with (S i) in H8 ; last lia.
           rewrite length_drop.
           replace (length bs - (length bs - i)) with i ; last lia.
           rewrite Hdrop in H8.
           simpl in H8.
           rewrite Hdat0 in H8.
           replace (length bs - i) with (length bs - S i + 1) ; last lia.
           rewrite - drop_drop.
           rewrite Hdrop.
           unfold drop => //=.
Qed.

Lemma store_trivial m k off bs :
  load m k off (length bs) = Some bs ->
  store m k off bs (length bs) = Some m. 
Proof.
  intros.
  unfold store.
  unfold load in H.
  rewrite N.add_assoc in H.
  destruct (k + off + N.of_nat (length bs) <=? length_mem m)%N ; try by inversion H.
  unfold write_bytes.
  unfold read_bytes in H.
  unfold fold_lefti.
  cut (forall k1,
          k1 <= length bs ->
          let k0 := length bs - k1 in
          those (map (λ off0, mem_lookup (k + off + N.of_nat off0)%N (mem_data m))
                       (iota k0 (length (drop k0 bs)))) = Some (drop k0 bs) ->
            match (let
                      '(_, acc_end) :=
                      fold_left
                        (λ '(k0, acc) x,
                          (k0 + 1,
                            match acc with
                            | Some dat => mem_update (k + off + N.of_nat k0)%N x dat
                            | None => None
                            end)) (bytes_takefill #00%byte (length (drop k0 bs))
                                                  (drop k0 bs))
                        (k0, Some (mem_data m)) in acc_end)
            with
            | Some dat => Some {| mem_data := dat ; mem_max_opt := mem_max_opt m |}
            | None => None
            end = Some m).
  intros Hk.
  assert (length bs <= length bs) ; first lia.
  apply Hk in H0.
  rewrite PeanoNat.Nat.sub_diag in H0.
  unfold drop in H0. done.
  rewrite PeanoNat.Nat.sub_diag.
  unfold drop. done.
  induction k1. intros.
  subst k0.
  rewrite Nat.sub_0_r.
  rewrite drop_all => //=.
  by destruct m.
  intros. subst k0.
  assert (k1 <= length bs) ; first lia.
  apply IHk1 in H2. 
  rewrite <- (take_drop 1 (drop (length bs - S k1) bs)).
  rewrite drop_drop.
  destruct (drop (length bs - S k1) bs) eqn:Hdrop.
  assert (length (drop (length bs - S k1) bs) = 0) ; first by rewrite Hdrop.
  rewrite length_drop in H3. lia.
  unfold take.
  replace (length bs - S k1 + 1) with (length bs - k1) ; last lia.
  simpl.
  replace (length bs - S k1 + 1) with (length bs - k1) ; last lia.
  replace (mem_update (k + off + N.of_nat (length bs - S k1))%N b (mem_data m))
    with (Some (mem_data m)).
  done.
  rewrite trivial_update => //=.
  simpl in H1.
  rewrite list_extra.cons_app in H1. 
  apply those_app_inv in H1 as (tl1 & tl2 & Htl1 & Htl2 & Htl).
  unfold those in Htl1.
  simpl in Htl1. unfold read_bytes, those => //=.
  rewrite N.add_0_r.
  destruct (mem_lookup _ _) ; inversion Htl1.
  rewrite - H3 in Htl.
  by inversion Htl.
  rewrite length_drop in H1.
  replace (length bs - (length bs - S k1)) with (S k1) in H1 ; last lia.
  simpl in H1.
  rewrite list_extra.cons_app in H1. 
  apply those_app_inv in H1 as (tl1 & tl2 & Htl1 & Htl2 & Htl).
  replace (S (length bs - S k1)) with (length bs - k1) in Htl2 ; last lia.
  rewrite length_drop.
  replace (length bs - (length bs - k1)) with k1 ; last lia.  
  rewrite Htl2.
  unfold those in Htl1.
  simpl in Htl1.
  destruct (mem_lookup _ _) ; inversion Htl1 ; subst.
  inversion Htl.
  rewrite - (take_drop 1 (drop _ _)) in H3. 
  destruct (drop (length bs - S k1) bs) eqn:Hdrop.
  assert (length (drop (length bs - S k1) bs) = 0) ; first by rewrite Hdrop.
  rewrite length_drop in H1. lia.
  unfold take in H3.
  rewrite <- Hdrop in H3.
  rewrite drop_drop in H3.
  inversion H3.
  replace (length bs - S k1 +1) with (length bs - k1) ; last lia.
  done.
Qed.  


Lemma store_append m k off b bs m':
  store m k off (b :: bs) (length (b :: bs)) = Some m' ->
  exists m'', store m k (off + 1)%N bs (length bs) = Some m'' /\
           store m'' k off [b] 1 = Some m'.
Proof.
  intros Hm.
  apply store_append1 in Hm as (m0 & Hm0 & Hm0').
  eapply swap_stores => //=.
Qed.

Lemma mem_grow_max m n m':
  mem_grow m n = Some m' ->
  mem_max_opt m = mem_max_opt m'.
Proof.
  move => Hgrow.
  unfold mem_grow in Hgrow.
  destruct (mem_size m + n <=? page_limit)%N eqn:HLP => //=.
  destruct (mem_max_opt m) eqn:Hmlimit => //=.
  - destruct (mem_size m + n <=? n0)%N => //=.
    by inversion Hgrow.
  - by inversion Hgrow.
Qed.
  
Lemma gen_heap_update_big_wm bs bs' k off n (mems mems' : list memory) (m m' : memory) :
  length bs = length bs' -> 
  load m k off (length bs) = Some bs ->
  store m k off bs' (length bs') = Some m' ->
  update_list_at mems n m' = mems' ->
  mems !! n = Some m ->
  gen_heap_interp (gmap_of_memory mems) -∗
                  N.of_nat n ↦[wms][N.add k off] bs ==∗
                  gen_heap_interp (gmap_of_memory mems') ∗
                  N.of_nat n ↦[wms][N.add k off] bs'.
Proof.
  move : mems' m' off bs'.
  induction bs ; iIntros (mems' m' off bs' Hlen Hm Hm' Hmems Hmemsn) "Hσ Hwms".
  { simpl in Hlen. apply Logic.eq_sym, nil_length_inv in Hlen ; subst.
    iSplitR "Hwms" => //=.
    rewrite update_trivial => //=.
    simpl in Hm'. unfold store in Hm'.
    simpl in Hm. unfold load in Hm.
    rewrite <- N.add_assoc in Hm'.
    destruct (k + (off + N.of_nat 0) <=? length_mem m)%N ; try by inversion Hm.
    unfold write_bytes in Hm'. simpl in Hm'.
    destruct m ; simpl in Hm'.
    by rewrite Hm' in Hmemsn. }
  destruct bs' ; inversion Hlen.
  iDestruct (wms_append with "Hwms") as "[Hwm Hwms]".
  rewrite <- N.add_assoc.
  destruct (store_append _ _ _ _ _ _ Hm') as (m'' & Hm'' & Hb).
  iMod (IHbs with "Hσ Hwms") as "[Hσ Hwms]" => //; first by eapply load_append.
  iMod (gen_heap_update with "Hσ Hwm") as "[Hσ Hwm]". 
  iIntros "!>".
  iSplitR "Hwms Hwm" ; last by iApply wms_append ; rewrite N.add_assoc ; iFrame.

  unfold store in Hb.
  destruct (k + off + N.of_nat 1 <=? length_mem m'')%N eqn: Hlen0; try by inversion Hb.
  unfold write_bytes, fold_lefti in Hb ; simpl in Hb.
  rewrite N.add_0_r in Hb.
  destruct (mem_update (k + off)%N b (mem_data m'')) eqn:Hupd ; inversion Hb; clear Hb.

  rewrite update_list_at_insert ; last by apply lookup_lt_Some in Hmemsn.
  rewrite update_list_at_insert in Hmems ; last by apply lookup_lt_Some in Hmemsn.

  rewrite <- Hmems.
  rewrite <- H1.
  erewrite gmap_of_memory_insert => //.
  - rewrite Nat2N.id.
    by rewrite list_insert_insert.
  - rewrite Nat2N.id.
    rewrite list_lookup_insert => //; last by apply lookup_lt_Some in Hmemsn.
  - simpl in Hlen0.
    move/N.leb_spec0 in Hlen0.
    unfold length_mem, memory_list.length_mem in Hlen0.
    lia.
Qed.

Lemma length_bits v t:
  types_num_agree t v -> length (bits v) = length_tnum t.
Proof.
  intros. unfold bits.
  destruct v ; destruct t ; by inversion H.
Qed.


Lemma memory_in_bounds m i b :
  (ml_data (mem_data m)) !! i = Some b -> i < N.to_nat (length_mem m) .
Proof.
  intros. 
  apply lookup_lt_Some in H. unfold length_mem, memory_list.length_mem.
  lia.
Qed.


Lemma take_drop {A} n (l : list A) : l = seq.take n l ++ seq.drop n l.
Proof.
  rewrite <- cat_app.
  by rewrite cat_take_drop.
Qed.


Lemma those_map_Some (f : nat -> option byte) (l : list byte) :
  (forall x : nat, x < length l -> f x = l !! x) ->
  those (map f (iota 0 (length l))) = Some l.
Proof.
  remember (length l) as n. generalize dependent l.
  induction n ; intros.
  { apply Logic.eq_sym, nil_length_inv in Heqn ; subst ; by unfold those. }
  destruct l ; first by inversion Heqn. 
  cut (exists ys y, b :: l = ys ++ [y]) ;
  [ intro Htail ; destruct Htail as (ys & y & Htail) |
    exists (removelast (b :: l)) ;
    exists (List.last (b :: l) b) ;
    apply app_removelast_last ;
    apply not_eq_sym ; apply nil_cons ].
  rewrite Htail. rewrite Htail in Heqn. rewrite Htail in H.
  rewrite length_app in Heqn. simpl in Heqn.
  rewrite Nat.add_1_r in Heqn. inversion Heqn.
  assert (forall x, x < n -> f x = ys !! x).
  { intros. rewrite H ; last lia.
    rewrite lookup_app_l => //=. by rewrite <- H1. }
  destruct n. rewrite <- H1. apply Logic.eq_sym, nil_length_inv in H1. rewrite H1.
  unfold those => //=. rewrite H. rewrite H1 => //=. lia.
  rewrite (take_drop (length ys) (iota 0 (S (length ys)))).
  rewrite take_iota. 
  unfold ssrnat.minn. 
  replace (S (length ys - 1)) with (length ys) ; last by rewrite <- H1 ; lia.
  rewrite ssrnat.leqnn.
  rewrite drop_iota => //=.
  unfold ssrnat.addn. replace (0+length ys) with (length ys) ; last lia.
  unfold ssrnat.subn. replace (S (length ys) - length ys) with 1 ; last lia.
  simpl.
  rewrite map_app. apply those_app. rewrite <- H1. apply (IHn ys H1 H0).
  unfold those => //=. rewrite H. 
  rewrite list_lookup_middle => //=. rewrite <- H1 ; lia.
Qed.


Lemma wms_is_load n k off bv m ws :
  length bv > 0 -> s_mems ws !! n = Some m ->
  (N.of_nat n ↦[wms][ k + off ] bv -∗
            gen_heap_interp (gmap_of_memory (s_mems ws))
            -∗ ⌜ load m k off (length bv) = Some bv ⌝).
Proof.
  iIntros (Ht Hm) "Hwms Hm".
  iAssert ( (∀ i, ⌜ i < length bv ⌝ -∗
                               ⌜ (ml_data (mem_data m)) !! (N.to_nat (k + off + N.of_nat i))
                  = bv !! i ⌝)%I ) as "%Hmeq".
  { iIntros (i) "%Hi".
    iDestruct (big_sepL_lookup with "Hwms") as "H" => //.
    destruct (nth_lookup_or_length bv i (bytes.encode 1)) => //=.
    lia.
    iDestruct (gen_heap_valid with "Hm H") as "%H".
    rewrite gmap_of_list_2d_lookup list_lookup_fmap Nat2N.id Hm in H.
    unfold memory_to_list in H. simpl in H. rewrite Nat2N.id in H.
    iPureIntro. replace (N.to_nat (k + off + N.of_nat i)) with
      (N.to_nat (k + off) + i). rewrite H.
    apply Logic.eq_sym.
    destruct (nth_lookup_or_length bv i (bytes.encode 1)) => //=.
    lia. lia. }
  
  iPureIntro.
  unfold load.
  replace (k + (off + N.of_nat (length bv)) <=? length_mem m)%N with true.
  unfold read_bytes, mem_lookup.
  apply those_map_Some => //=.
  intros.
  rewrite nth_error_lookup. by apply Hmeq.
  apply Logic.eq_sym, N.leb_le.
  assert (ml_data (mem_data m) !! N.to_nat (k + off + N.of_nat (length bv - 1)) =
            bv !! (length bv - 1)). apply Hmeq ; first lia.
  destruct (nth_lookup_or_length bv (length bv - 1) (bytes.encode 1)) => //=. 
  rewrite e in H.
  apply memory_in_bounds in H. unfold lt in H.
  replace (S (N.to_nat (k + off + N.of_nat (length bv - 1)))) with
    (N.to_nat (k + (off + N.of_nat (length bv)))) in H. lia.
  rewrite <- N2Nat.inj_succ. 
  rewrite <- N.add_succ_r. 
  rewrite <- Nat2N.inj_succ. lia. lia.
Qed.

Lemma wms_is_load_packed n k off bv m len ws sx :
  length bv > 0 ->
  s_mems ws !! n = Some m ->
  (N.of_nat n ↦[wms][ k + off ] bv -∗
            gen_heap_interp (gmap_of_memory (s_mems ws))
            -∗ ⌜ load_packed (sx) m k off (length bv) len = Some bv ⌝).
Proof.
  iIntros (Hlt Hm) "Hwms Hm".
  unfold load_packed,sign_extend.
  iDestruct (wms_is_load with "Hwms Hm") as %Hload;[auto|eauto|].
  rewrite Hload. simpl. auto.
Qed.

Lemma wms_implies_bounds n k off bv ws m :
  length bv > 0 ->
  s_mems ws !! n = Some m ->
  N.of_nat n ↦[wms][ k + off ] bv -∗
  gen_heap_interp (gmap_of_memory (s_mems ws)) -∗      
  ⌜ (k + off + N.of_nat (length bv) ≤ length_mem m)%N ⌝.
Proof.
  iIntros ( Hgt Hm) "Hn Hm".
  iDestruct (wms_is_load with "Hn Hm") as %Hload;eauto.
  unfold load in Hload.
  edestruct (_ <=? _)%N eqn:Hbound;[|by inversion Hload].
  iPureIntro.
  apply N.leb_le in Hbound. lia.
Qed.

Lemma length_iota len i :
  length (iota i len) = (len).
Proof.
  rewrite length_is_size.
  by apply size_iota.
Qed.

Lemma load_prefix m k off bs len :
  len < length bs ->
  load m k off (length bs) = Some bs ->
  (∃ tl1 tl2, bs = tl1 ++ tl2 ∧ load m k off (len) = Some tl1).
Proof.
  intros Hlen Hload.
  unfold load, read_bytes, fold_lefti.
  unfold load, read_bytes in Hload.
  rewrite N.add_assoc in Hload.
  (* rewrite - Hlen. *)
  destruct (_ <=? _)%N eqn:Hklen ; try by inversion Hload.
  destruct (k + (off + N.of_nat (len)) <=? length_mem m)%N eqn:Hklen'.
  2: { apply N.leb_le in Hklen. apply N.leb_nle in Hklen'. lia. }
  
  rewrite (take_drop (len) (iota 0 (length bs))) in Hload.
  rewrite map_app in Hload.
  apply those_app_inv in Hload as Hload'.
  destruct Hload' as [tl1 [tl2 [Hload1 [Hload2 Heq]]]].
  rewrite take_iota in Hload1.
  assert (ssrnat.minn (len) (length bs) = len) as HH.
  { apply/ssrnat.minn_idPl/ssrnat.leP. lia. }
  rewrite HH in Hload1.
  eexists _,_. split;eauto.
Qed.

Lemma if_load_then_store bs bs' m k off :
  length bs = length bs' ->
  load m k off (length bs) = Some bs ->
  exists m', store m k off bs' (length bs') = Some m'.
Proof.
  intros Hlen Hload.
  unfold store, write_bytes, fold_lefti.
  unfold load, read_bytes in Hload.
  rewrite N.add_assoc in Hload.
  rewrite - Hlen.
  destruct (_ <=? _)%N eqn:Hklen ; try by inversion Hload.
  cut (forall i dat,
          length (ml_data dat) = length (ml_data (mem_data m)) ->
          i <= length bs ->
          let j := length bs - i in
          those (map (λ off0, mem_lookup (k + off + N.of_nat off0)%N (mem_data m))
                     (iota j i)) = Some (drop j bs) ->
          exists dat', (let '(_, acc_end) :=
                     fold_left
                       (λ '(k0, acc) x,
                         (k0 + 1,
                           match acc with
                           | Some dat => mem_update (k + off + N.of_nat k0)%N x dat
                           | None => None
                           end)) (bytes_takefill #00%byte i (drop j bs'))
                       (j, Some dat) in acc_end) = Some dat').
  - intros Hi.
    assert (length bs <= length bs) ; first lia.
    eapply Hi in H as [dat' Hdat'].
    + rewrite PeanoNat.Nat.sub_diag in Hdat'.
      unfold drop in Hdat'.
      rewrite Hdat'.
      by eexists _.
    + done.
    + rewrite PeanoNat.Nat.sub_diag.
      unfold drop.
      exact Hload.
  - induction i ; intros ; subst j.
    + rewrite Nat.sub_0_r.
      rewrite Hlen.
      rewrite drop_all.
      simpl.
      by eexists _.
    + assert (i <= length bs) ; first lia.
      destruct (drop (length bs - S i) bs') eqn:Hdrop.
      * assert (length (drop (length bs - S i) bs') = 0) ; first by rewrite Hdrop.
        rewrite length_drop in H3. lia.
      * destruct (drop (length bs - S i) bs) eqn:Hdrop0.
        **  assert (length (drop (length bs - S i) bs) = 0) ; first by rewrite Hdrop0.
            rewrite length_drop in H3. lia.
        ** assert (exists dat0, mem_update (k + off + N.of_nat (length bs - S i))%N b dat =
                             Some dat0) as [dat0 Hdat0].
           { unfold mem_update.
             assert (k + off + N.of_nat (length bs - S i) <
                       N.of_nat (length (ml_data dat)))%N.
             rewrite H.
             unfold length_mem, memory_list.length_mem in Hklen.
             apply N.leb_le in Hklen.
             lia.
             apply N.ltb_lt in H3.
             rewrite H3.
             by eexists _. } 
           eapply (IHi dat0) in H2 as [dat' Hdat'].
        ++ simpl.
           replace (length bs - i) with (length bs - S i + 1) in Hdat' ; last lia.
           rewrite - drop_drop in Hdat'.
           rewrite Hdrop in Hdat'.
           unfold drop in Hdat'.
           rewrite Hdat0.
           rewrite Hdat'.
           by eexists _.
        ++ rewrite - H.
           erewrite <- mem_update_length ; last exact Hdat0.
           done.
        ++ simpl in H1.
           rewrite - those_those0 in H1.
           unfold those0 in H1.
           fold (those0 (A:=byte)) in H1.
           rewrite those_those0 in H1.
           destruct (mem_lookup _ _) ; try by inversion H1.
           unfold option_map in H1.
           destruct (those (map (λ off0, mem_lookup (k + off + N.of_nat off0)%N
                                (mem_data m))
                                (iota (S (length bs - S i)) i)) )
                    eqn:Hth ; try by inversion H1.
           replace (S (length bs - S i)) with (length bs - i) in Hth ; last lia.
           rewrite Hth.
           inversion H1.
           replace (length bs - i) with (length bs - S i + 1) ; last lia.
           rewrite - drop_drop.
           rewrite Hdrop0 => //=.
Qed.

Lemma length_load m k off len tl1 :
  load m k off len = Some tl1 ->
  length tl1 = len.
Proof.
  unfold load.
  intros Hload.
  destruct (_ <=? _)%N eqn:Hklen ; try by inversion Hload.
  unfold read_bytes in Hload. clear Hklen.
  apply length_those in Hload. 
  rewrite length_iota in Hload. auto.
Qed.
  
Lemma if_load_then_store_weak bs bs' m k off :
  length bs' <= length bs ->
  load m k off (length bs) = Some bs ->
  exists m', store m k off bs' (length bs') = Some m'.
Proof.
  intros Hlen Hload.
  inversion Hlen.
  { eapply if_load_then_store. symmetry. apply H0. auto. }
  { assert (length bs' < length bs);[lia|].
    eapply load_prefix in Hload as [tl1 [tl2 [Heq Htl1]]];[|eauto].
    apply length_load in Htl1 as Hlen'.
    eapply if_load_then_store;[apply Hlen'|]. rewrite Hlen';auto.
  }
Qed.

Lemma length_bytes_takefill b len bytes :
  length (bytes_takefill b len bytes) = len.
  revert bytes;induction len;intros bytes;simpl;auto.
  { destruct bytes; simpl; f_equiv;auto. }
Qed.

Lemma drop_S_inv {A : Type} n (bs : list A) b l : drop n bs = (b :: l) -> drop (S n) bs = l.
Proof.
  revert n b l;induction bs;intros n b l Hdrop.
  { simpl in *. destruct n;done. }
  { simpl in *. destruct n;simplify_eq.
    { rewrite /drop in Hdrop. simplify_eq. auto. }
    { simpl in Hdrop. eapply IHbs. eauto. }
  }
Qed.                                       

Lemma enough_space_to_store' m k off bs len :
  len < length bs ->
  (k + off + N.of_nat len <= length_mem m)%N ->
  exists mf, store m k off bs len = Some mf.
Proof.
  intros Hlen Hmlen.
  unfold store.
  apply N.leb_le in Hmlen.
  rewrite Hmlen.
  unfold write_bytes, fold_lefti. 
  cut (forall i dat,
          i <= len ->
          length (ml_data dat) = N.to_nat (length_mem m) ->
          let j := len - i in
          exists datf, (let '(_, acc_end) :=
                      fold_left (λ '(k0,acc) x,
                                  (k0 + 1,
                                    match acc with
                                    | Some dat => mem_update (k + off + N.of_nat k0)%N x dat
                                    | None => None
                                    end)) (bytes_takefill #00%byte (len - j)
                                                          (drop j bs))
                                (j, Some dat) in acc_end) = Some datf).
  - intros H.
    assert (len <= len) ; first lia.
    apply (H _ (mem_data m)) in H0 as [datf' Hdatf'].
    + rewrite PeanoNat.Nat.sub_diag in Hdatf'.
      unfold drop in Hdatf'.
      rewrite PeanoNat.Nat.sub_0_r in Hdatf'.
      rewrite Hdatf'.
      by eexists _.
    + unfold length_mem, memory_list.length_mem.
      by rewrite Nat2N.id.
  - induction i ; intros ; subst j.
    + rewrite Nat.sub_0_r.
      rewrite PeanoNat.Nat.sub_diag /=;eauto.
    + assert (i <= len) ; first lia.
      destruct (drop (len - S i) bs) eqn:Hdrop.
      * assert (length (drop (len - S i) bs) = 0) ; first by rewrite Hdrop.
        rewrite length_drop in H2. lia.
      * assert (exists datupd,
                   mem_update (k + off + N.of_nat (len - S i))%N b dat =
                     Some datupd ) as [datupd Hdatupd].
        { unfold mem_update.
           apply N.leb_le in Hmlen.
           assert ( k + off + N.of_nat (len - S i) <
                      N.of_nat (length (ml_data dat)))%N ;
             first lia.
           apply N.ltb_lt in H2 ; rewrite H2.
          by eexists _. }
        eapply (IHi datupd) in H1 as [datf Hdatf].
        ++ rewrite - Hdrop. rewrite Hdrop.
           assert (len - (len - S i) = S i) as ->;[lia|].
           simpl. rewrite Hdatupd.
           assert (len - (len - i) = i) as Heq;[lia|]. rewrite Heq in Hdatf.
           replace (len- S i + 1) with (len - i) ; last lia.
           destruct (len - S i) eqn:Hi.
           { rewrite /drop in Hdrop. destruct bs;try done. simplify_eq.
             assert (len - i = 1) as Hii;[lia|].
             rewrite Hii in Hdatf.
             simpl in Hdatf. rewrite /drop in Hdatf. rewrite Hii.
             rewrite Hdatf. eauto. }
           { destruct bs;try done. simpl in Hdrop.
             assert (len - i = S (S n)) as Hii; [lia|].
             rewrite Hii in Hdatf. simpl in Hdatf.
             erewrite drop_S_inv in Hdatf;[|eauto].
             rewrite Hii Hdatf. eauto. }
        ++ rewrite <- H0.
           by erewrite <- mem_update_length.
Qed.

  
Lemma store_weak m k off bs m' len' :
  len' < (length bs) ->
  store m k off bs (length bs) = Some m' ->
  ∃ m'', store m k off bs len' = Some m''.
Proof.
  intros Hlt Hstore.
  unfold store in Hstore.
  edestruct (_ <=? _)%N eqn:Hle;[|by inversion Hstore].
  apply N.leb_le in Hle.
  assert ((k + off + N.of_nat len' ≤ length_mem m)%N) as Hle';[lia|].
  eapply enough_space_to_store';auto.
Qed.

Lemma if_load_then_store_packed bs bs' m k off len sx :
  length bs' <= length bs ->
  load_packed sx m k off (length bs) len = Some bs ->
  exists m', store_packed m k off bs' (length bs') = Some m'.
Proof.
  intros Hlen Hload.
  unfold store_packed, write_bytes, fold_lefti.
  unfold load_packed, sign_extend in Hload.
  eapply if_load_then_store_weak;eauto.
  destruct (load m k off (length bs));simpl in Hload;auto.
Qed.  

Lemma wms_is_not_load n k off len m ws llen :
  (k + off + llen > len)%N ->
  s_mems ws !! n = Some m ->
  ((N.of_nat n) ↦[wmlength] len -∗
  gen_heap_interp (gmap_of_list (length_mem <$> s_mems ws)) -∗
  ⌜ load m k off (N.to_nat llen) = None ⌝).
Proof.
  iIntros (Ht Hm) "Hwms Hm".
  iDestruct (gen_heap_valid with "Hm Hwms") as %Hmlen.
  rewrite gmap_of_list_lookup in Hmlen.
  rewrite Nat2N.id in Hmlen.
  rewrite list_lookup_fmap Hm /= in Hmlen. inversion Hmlen;subst.
  unfold load.
  destruct ((k + (off + N.of_nat (N.to_nat llen)) <=? length_mem m)%N) eqn:Hcontr;auto.
  rewrite N2Nat.id in Hcontr. apply N.leb_le in Hcontr. lia.
Qed.

Lemma wms_is_not_load_packed n k off len m ws llen len' sx :
  (k + off + llen > len)%N ->
  s_mems ws !! n = Some m ->
  ((N.of_nat n) ↦[wmlength] len -∗
  gen_heap_interp (gmap_of_list (length_mem <$> s_mems ws)) -∗
  ⌜ load_packed sx m k off (N.to_nat llen) len' = None ⌝).
Proof.
  iIntros (Ht Hm) "Hwms Hm".
  iDestruct (gen_heap_valid with "Hm Hwms") as %Hmlen.
  rewrite gmap_of_list_lookup in Hmlen.
  rewrite Nat2N.id in Hmlen.
  rewrite list_lookup_fmap Hm /= in Hmlen. inversion Hmlen;subst.
  unfold load_packed,load.
  destruct ((k + (off + N.of_nat (N.to_nat llen)) <=? length_mem m)%N) eqn:Hcontr;auto.
  rewrite N2Nat.id in Hcontr. apply N.leb_le in Hcontr. lia.
Qed.

Lemma wms_is_not_store n k off len m ws llen bv :
  (k + off + llen > len)%N ->
  s_mems ws !! n = Some m ->
  ((N.of_nat n) ↦[wmlength] len -∗
  gen_heap_interp (gmap_of_list (length_mem <$> s_mems ws)) -∗
  ⌜ store m k off bv (N.to_nat llen) = None ⌝).
Proof.
  iIntros (Ht Hm) "Hwms Hm".
  iDestruct (gen_heap_valid with "Hm Hwms") as %Hmlen.
  rewrite gmap_of_list_lookup in Hmlen.
  rewrite Nat2N.id in Hmlen.
  rewrite list_lookup_fmap Hm /= in Hmlen. inversion Hmlen;subst.
  unfold store.
  destruct ((k + off + N.of_nat (N.to_nat llen) <=? length_mem m)%N) eqn:Hcontr;auto.
  rewrite N2Nat.id in Hcontr. apply N.leb_le in Hcontr. lia.
Qed.

Lemma wms_is_not_store_packed n k off len m ws llen bv :
  (k + off + llen > len)%N ->
  s_mems ws !! n = Some m ->
  ((N.of_nat n) ↦[wmlength] len -∗
  gen_heap_interp (gmap_of_list (length_mem <$> s_mems ws)) -∗
  ⌜ store_packed m k off bv (N.to_nat llen) = None ⌝).
Proof.
  iIntros (Ht Hm) "Hwms Hm".
  iDestruct (gen_heap_valid with "Hm Hwms") as %Hmlen.
  rewrite gmap_of_list_lookup in Hmlen.
  rewrite Nat2N.id in Hmlen.
  rewrite list_lookup_fmap Hm /= in Hmlen. inversion Hmlen;subst.
  unfold store_packed,store.
  destruct ((k + off + N.of_nat (N.to_nat llen) <=? length_mem m)%N) eqn:Hcontr;auto.
  rewrite N2Nat.id in Hcontr. apply N.leb_le in Hcontr. lia.
Qed.

Lemma bytes_takefill_idem len bs :
  (bytes_takefill #00%byte len (bytes_takefill #00%byte len bs))
  = (bytes_takefill #00%byte len bs).
Proof.
  revert bs.
  induction len;intros bs;simpl;auto.
  destruct bs;f_equiv;auto.
Qed.
      
Lemma store_bytes_takefill_eq m k off len bs :
  store m k off (bytes_takefill #00%byte len bs) len = store m k off bs len.
Proof.
  unfold store.
  destruct (_ <=? _)%N;eauto.
  rewrite bytes_takefill_idem. auto.
Qed.

Lemma store_mem_len_eq m k off bv mf n mem :
  mem !! n = Some m ->
  store m k off bv (length bv) = Some mf ->
  length_mem <$> update_list_at mem n mf = length_mem <$> mem.
Proof.
  unfold update_list_at.
  intros Hm Hstore.
  apply length_store in Hstore.
  apply take_drop_middle in Hm.
  assert (length_mem <$> mem = length_mem <$> take n mem ++ (m :: drop (S n) mem)%SEQ) as ->.
  { f_equiv. auto. }
  rewrite (separate1 m).
  rewrite !fmap_app.
  erewrite fmap_app.
  f_equiv;[by rewrite firstn_is_take_n|].
  f_equiv.
  { simpl. f_equiv. unfold length_mem, memory_list.length_mem.
    rewrite Hstore. auto. }
  { rewrite ssrnat.addn1. auto. }
Qed.


Lemma deserialise_bits v t :
  types_num_agree t v -> wasm_deserialise (bits v) t = v.
Proof.
  intros Htv.
  unfold wasm_deserialise.
  destruct t ;
    unfold bits ;
    destruct v ; (try by inversion Htv).
  rewrite Memdata.decode_encode_int.
  rewrite Z.mod_small.
  by rewrite Wasm_int.Int32.repr_unsigned.
  destruct s ; simpl ; replace (two_power_pos (_ * _))
    with Wasm_int.Int32.modulus ; [lia | done].
  rewrite Memdata.decode_encode_int.
  rewrite Z.mod_small.
  by rewrite Wasm_int.Int64.repr_unsigned.
  destruct s ; simpl ; replace (two_power_pos (_ * _))
    with Wasm_int.Int64.modulus ; [lia | done].
  rewrite Memdata.decode_encode_int_4.
  by rewrite Wasm_float.FloatSize32.of_to_bits.
  rewrite Memdata.decode_encode_int_8.
  by rewrite Wasm_float.FloatSize64.of_to_bits.
Qed.

Lemma bits_deserialise bs t :
  length bs = length_tnum t ->
  bits (wasm_deserialise bs t) = bs.
Proof.
  intros Hlen.
  unfold wasm_deserialise.
  destruct t ; simpl in Hlen ;
    repeat (destruct bs ; try by inversion Hlen) ;
    unfold bits.
  - unfold serialise_i32.
    rewrite Wasm_int.Int32.unsigned_repr ;
      unfold Memdata.decode_int, Memdata.int_of_bytes,  Memdata.rev_if_be.
    unfold Memdata.encode_int, Memdata.bytes_of_int, Memdata.rev_if_be.
    destruct Archi.big_endian ;
      unfold Memdata.int_of_bytes ;    
      simpl ; 
      rewrite Z.mul_0_l ; 
      rewrite Z.add_0_r ; 
      do 3 ( rewrite Z_div_plus ; last lia ;
             rewrite (Z.div_small (Integers.Byte.unsigned _) 256) ;
             last (by replace 256%Z with Integers.Byte.modulus ; last done ;
                     by apply Integers.Byte.unsigned_range) ; 
             rewrite Z.add_0_l) ; 
      rewrite Integers.Byte.repr_unsigned ;
      do 3 ( erewrite (Integers.Byte.eqm_repr_eq (Integers.Byte.unsigned _ + _) _) ;
             last (unfold Integers.Byte.eqm ;
                   replace Integers.Byte.modulus with 256%Z ; last done ;
                   unfold Zbits.eqmod ;
                   eexists _ ; by rewrite Z.add_comm)) ; 
      done.
    destruct Archi.big_endian ;
      simpl ;
      replace Wasm_int.Int32.max_unsigned with 4294967295%Z ; try done ;
      specialize (Integers.Byte.unsigned_range b) ; intros H ;
      replace Integers.Byte.modulus with 256%Z in H ; try done ;
      specialize (Integers.Byte.unsigned_range b0) ; intros H0 ;
      replace Integers.Byte.modulus with 256%Z in H0 ; try done ;
      specialize (Integers.Byte.unsigned_range b1) ; intros H1 ;
      replace Integers.Byte.modulus with 256%Z in H1 ; try done ;
      specialize (Integers.Byte.unsigned_range b2) ; intros H2 ;
      replace Integers.Byte.modulus with 256%Z in H2 ; try done ;
      lia.
  - unfold serialise_i64.
    rewrite Wasm_int.Int64.unsigned_repr ;
      unfold Memdata.decode_int, Memdata.int_of_bytes, Memdata.rev_if_be.
    unfold Memdata.encode_int, Memdata.bytes_of_int, Memdata.rev_if_be.
    destruct Archi.big_endian ;
      unfold Memdata.int_of_bytes ; 
      simpl ; 
      rewrite Z.mul_0_l ; 
      rewrite Z.add_0_r ; 
      do 7 ( rewrite Z_div_plus ; last lia ;
             rewrite (Z.div_small (Integers.Byte.unsigned _) 256) ;
             last (by replace 256%Z with Integers.Byte.modulus ; last done ;
                     by apply Integers.Byte.unsigned_range) ; 
             rewrite Z.add_0_l) ; 
      rewrite Integers.Byte.repr_unsigned ;
      do 7 ( erewrite (Integers.Byte.eqm_repr_eq (Integers.Byte.unsigned _ + _) _) ;
             last (unfold Integers.Byte.eqm ;
                   replace Integers.Byte.modulus with 256%Z ; last done ;
                   unfold Zbits.eqmod ;
                   eexists _ ; by rewrite Z.add_comm)) ;
      done.
    destruct Archi.big_endian ;
      simpl ;
      specialize (Integers.Byte.unsigned_range b) ; intros H ;
      replace Integers.Byte.modulus with 256%Z in H ; try done ;
      specialize (Integers.Byte.unsigned_range b0) ; intros H0 ;
      replace Integers.Byte.modulus with 256%Z in H0 ; try done ;
      specialize (Integers.Byte.unsigned_range b1) ; intros H1 ;
      replace Integers.Byte.modulus with 256%Z in H1 ; try done ;
      specialize (Integers.Byte.unsigned_range b2) ; intros H2 ;
      replace Integers.Byte.modulus with 256%Z in H2 ; try done ;
      specialize (Integers.Byte.unsigned_range b3) ; intros H3 ;
      replace Integers.Byte.modulus with 256%Z in H3 ; try done ;
      specialize (Integers.Byte.unsigned_range b4) ; intros H4 ;
      replace Integers.Byte.modulus with 256%Z in H4 ; try done ;
      specialize (Integers.Byte.unsigned_range b5) ; intros H5 ;
      replace Integers.Byte.modulus with 256%Z in H5 ; try done ;
      specialize (Integers.Byte.unsigned_range b6) ; intros H6 ;
      replace Integers.Byte.modulus with 256%Z in H6 ; try done ;
      replace Wasm_int.Int64.max_unsigned with 18446744073709551615%Z ; try done ;
      lia.
  - unfold serialise_f32.
    rewrite Wasm_float.FloatSize32.to_of_bits Integers.Int.unsigned_repr ;
      unfold Memdata.decode_int, Memdata.int_of_bytes , Memdata.rev_if_be.
    unfold Memdata.encode_int, Memdata.bytes_of_int, Memdata.rev_if_be.
    destruct Archi.big_endian ;
      unfold Memdata.int_of_bytes ;    
      simpl ; 
      rewrite Z.mul_0_l ; 
      rewrite Z.add_0_r ;
      do 3 ( rewrite Z_div_plus ; last lia ;
             rewrite (Z.div_small (Integers.Byte.unsigned _) 256) ;
             last (by replace 256%Z with Integers.Byte.modulus ; last done ;
                     by apply Integers.Byte.unsigned_range) ; 
             rewrite Z.add_0_l) ;
      rewrite Integers.Byte.repr_unsigned ;
      do 3 ( erewrite (Integers.Byte.eqm_repr_eq (Integers.Byte.unsigned _ + _) _) ;
             last (unfold Integers.Byte.eqm ;
                   replace Integers.Byte.modulus with 256%Z ; last done ;
                   unfold Zbits.eqmod ;
                   eexists _ ; by rewrite Z.add_comm)) ;
      done.
    destruct Archi.big_endian ;
      simpl ;
      replace Integers.Int.max_unsigned with 4294967295%Z ; try done ;
      specialize (Integers.Byte.unsigned_range b) ; intros H ;
      replace Integers.Byte.modulus with 256%Z in H ; try done ;
      specialize (Integers.Byte.unsigned_range b0) ; intros H0 ;
      replace Integers.Byte.modulus with 256%Z in H0 ; try done ;
      specialize (Integers.Byte.unsigned_range b1) ; intros H1 ;
      replace Integers.Byte.modulus with 256%Z in H1 ; try done ;
      specialize (Integers.Byte.unsigned_range b2) ; intros H2 ;
      replace Integers.Byte.modulus with 256%Z in H2 ; try done ;
      lia.
  - unfold serialise_f64.
    rewrite Wasm_float.FloatSize64.to_of_bits Integers.Int64.unsigned_repr ;
      unfold Memdata.decode_int, Memdata.int_of_bytes, Memdata.rev_if_be.
    unfold Memdata.encode_int, Memdata.bytes_of_int, Memdata.rev_if_be.
    destruct Archi.big_endian ;
      unfold Memdata.int_of_bytes ; 
      simpl ; 
      rewrite Z.mul_0_l ; 
      rewrite Z.add_0_r ; 
      do 7 ( rewrite Z_div_plus ; last lia ;
             rewrite (Z.div_small (Integers.Byte.unsigned _) 256) ;
             last (by replace 256%Z with Integers.Byte.modulus ; last done ;
                     by apply Integers.Byte.unsigned_range) ; 
             rewrite Z.add_0_l) ; 
      rewrite Integers.Byte.repr_unsigned ;
      do 7 ( erewrite (Integers.Byte.eqm_repr_eq (Integers.Byte.unsigned _ + _) _) ;
             last (unfold Integers.Byte.eqm ;
                   replace Integers.Byte.modulus with 256%Z ; last done ;
                   unfold Zbits.eqmod ;
                   eexists _ ; by rewrite Z.add_comm)) ;
      done.
    destruct Archi.big_endian ;
      simpl ;
      specialize (Integers.Byte.unsigned_range b) ; intros H ;
      replace Integers.Byte.modulus with 256%Z in H ; try done ;
      specialize (Integers.Byte.unsigned_range b0) ; intros H0 ;
      replace Integers.Byte.modulus with 256%Z in H0 ; try done ;
      specialize (Integers.Byte.unsigned_range b1) ; intros H1 ;
      replace Integers.Byte.modulus with 256%Z in H1 ; try done ;
      specialize (Integers.Byte.unsigned_range b2) ; intros H2 ;
      replace Integers.Byte.modulus with 256%Z in H2 ; try done ;
      specialize (Integers.Byte.unsigned_range b3) ; intros H3 ;
      replace Integers.Byte.modulus with 256%Z in H3 ; try done ;
      specialize (Integers.Byte.unsigned_range b4) ; intros H4 ;
      replace Integers.Byte.modulus with 256%Z in H4 ; try done ;
      specialize (Integers.Byte.unsigned_range b5) ; intros H5 ;
      replace Integers.Byte.modulus with 256%Z in H5 ; try done ;
      specialize (Integers.Byte.unsigned_range b6) ; intros H6 ;
      replace Integers.Byte.modulus with 256%Z in H6 ; try done ;
      replace Integers.Int64.max_unsigned with 18446744073709551615%Z ; try done ;
      lia.
Qed.    


Lemma deserialise_type bs t :
  types_num_agree t (wasm_deserialise bs t).
Proof.
  unfold wasm_deserialise.
  by destruct t.
Qed.


Lemma wms_implies_smems_is_Some ws n k b bs :
  gen_heap_interp (gmap_of_memory (s_mems ws)) -∗
                  ([∗ list] i ↦ b  ∈ (b :: bs), pointsto (L:=N*N) (V:=byte)
                                                     (N.of_nat n, N.of_nat (N.to_nat k+i))
                                                     (DfracOwn 1) b) -∗
                  (([∗ list] i ↦ b  ∈ (b :: bs), pointsto (L:=N*N) (V:=byte)
                                                     (N.of_nat n, N.of_nat (N.to_nat k+i))
                                                     (DfracOwn 1) b) ∗
                                                                     gen_heap_interp (gmap_of_memory (s_mems ws)) ∗
                            ⌜ exists m, s_mems ws !! n = Some m ⌝).
Proof.
  iIntros "Hm Hwms".
  unfold big_opL.
  iDestruct "Hwms" as "[Hwm Hwms]".
  rewrite Nat.add_0_r. rewrite N2Nat.id.
  iDestruct (gen_heap_valid with "Hm Hwm") as "%Hm".
  iSplitR "Hm".
  - by iSplitL "Hwm".
  - iSplitL => //=. iPureIntro.
    destruct (s_mems ws !! n) as [m|] eqn:Hn ; first by eexists.
    rewrite no_memory_no_memories in Hm => //=.
Qed.

Lemma ewp_load_deserialize Ψ (Φ:iris.val -> frame -> iProp Σ) (E:coPset) t (bv:bytes)
      (off: static_offset) (a: alignment_exponent)
      (k: i32) (n:nat) (f0: frame):
  length bv = length_tnum t ->
  f0.(f_inst).(inst_memory) !! 0 = Some n ->
  (▷ Φ (immV [VAL_num $ wasm_deserialise bv t]) f0 ∗
     N.of_nat n ↦[wms][ N.add (Wasm_int.N_of_uint i32m k) off ] bv ⊢
     (EWP [AI_basic (BI_const (VAL_int32 k)) ;
          AI_basic (BI_load t None a off)] UNDER f0 @ E <| Ψ |> {{ w ; h , (Φ w h ∗ (N.of_nat n) ↦[wms][ N.add (Wasm_int.N_of_uint i32m k) off ]bv) }})).
Proof.
  iIntros (Htv Hinstn) "(HΦ & Hwms)".
  iApply ewp_lift_atomic_step => //=.
  iIntros (σ) "Hσ !>".
  iDestruct "Hσ" as "(? & ? & ? & ? & Hm & ? & Hframe & Hγ)".
  
  destruct bv eqn:Hb. destruct t;done.
  iDestruct (wms_implies_smems_is_Some with "Hm Hwms") as "(Hwms & Hm & %Hm)".
  destruct Hm as [m Hm].
  rewrite <- Hb.
  iDestruct (wms_is_load with "Hwms Hm") as "%Hload" => //=.
  { rewrite Hb. simpl;lia. }
  rewrite -Hb in Htv.
  rewrite Htv in Hload.
  rewrite - nth_error_lookup in Hm.
  rewrite - nth_error_lookup in Hinstn.
  simpl in Hinstn.
  destruct (inst_memory _) eqn:Hinstmem => //.
  inversion Hinstn; subst; clear Hinstn.
  iSplit.
  - iPureIntro.
    unfold language.reducible, language.prim_step => /=.
    eexists [], [AI_basic (BI_const _)], (_,_,_), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply r_load_success => //.
    unfold smem_ind.
    by rewrite Hinstmem.
  - iIntros "!>" (es ??? HStep) "!>".

    destruct HStep as [H _].
    eapply reduce_det in H as [-> [ H | [ [? Hfirst] |  (?&?&?&Hfirst & Hfirst2 &
                                                                  Hfirst3 & Hσ)]]] ;
      last (destruct f0; eapply r_load_success => //= ; unfold smem_ind ; by rewrite Hinstmem) ;
      try by     unfold first_instr in Hfirst ; simpl in Hfirst ; inversion Hfirst.
    destruct H as [<- <-]. destruct f0; iFrame. 
Qed.

Lemma ewp_load Ψ (Φ:iris.val -> frame -> iProp Σ) (E:coPset) t v
      (off: static_offset) (a: alignment_exponent)
      (k: i32) (n:nat) (f: frame):
  types_num_agree t v ->
  f.(f_inst).(inst_memory) !! 0 = Some n ->
  (▷ Φ (immV [VAL_num v]) f ∗
     N.of_nat n ↦[wms][ N.add (Wasm_int.N_of_uint i32m k) off ]
     (bits v) ⊢
     (EWP [AI_basic (BI_const (VAL_int32 k)) ;
          AI_basic (BI_load t None a off)] UNDER f @ E <| Ψ |> {{ w ; h , (Φ w h ∗ (N.of_nat n) ↦[wms][ N.add (Wasm_int.N_of_uint i32m k) off ](bits v)) }})).
Proof.
  iIntros (Htv Hinstn) "(HΦ & Hwms)".
  iApply ewp_load_deserialize;auto.
  { erewrite length_bits;eauto. }
  rewrite deserialise_bits;auto. iFrame.
Qed.

Lemma ewp_load_packed_deserialize Ψ (Φ:iris.val -> frame -> iProp Σ) (E:coPset) t (bv:bytes)
      (off: static_offset) (a: alignment_exponent)
      (k: i32) (n:nat) (f0: frame) tp sx:
  length bv = length_tp tp ->
  f0.(f_inst).(inst_memory) !! 0 = Some n ->
  (▷ Φ (immV [VAL_num $ wasm_deserialise bv t]) f0 ∗
     N.of_nat n ↦[wms][ N.add (Wasm_int.N_of_uint i32m k) off ] bv ⊢
     (EWP [AI_basic (BI_const (VAL_int32 k)) ;
          AI_basic (BI_load t (Some (tp, sx)) a off)] UNDER f0 @ E <| Ψ |> {{ w ; h , (Φ w h ∗ (N.of_nat n) ↦[wms][ N.add (Wasm_int.N_of_uint i32m k) off ]bv) }})).
Proof.
  iIntros (Htv Hinstn) "(HΦ & Hwms)".
  iApply ewp_lift_atomic_step => //=.
  iIntros (σ) "Hσ !>".

  iDestruct "Hσ" as "(? &? & ? & ? & Hm & ? & Hframe & Hγ)".
  
  destruct bv eqn:Hb.
  destruct tp;done.
  iDestruct (wms_implies_smems_is_Some with "Hm Hwms") as "(Hwms & Hm & %Hm)".
  destruct Hm as [m Hm].
  rewrite <- Hb.
  iDestruct (wms_is_load_packed _ _ _ _ _ (length_tnum t) _ sx  with "Hwms Hm") as "%Hload" => //=.
  { rewrite Hb. simpl. lia. }
  rewrite - nth_error_lookup in Hm.
  rewrite - nth_error_lookup in Hinstn.
  simpl in Hinstn.
  rewrite -Hb in Htv.
  rewrite Htv in Hload.
  destruct (inst_memory _) eqn:Hinstmem => //.
  inversion Hinstn; subst; clear Hinstn.
  iSplit.
  - iPureIntro.
    unfold language.reducible, language.prim_step => /=.
    eexists [], [AI_basic (BI_const _)], (_,_,_), [].
    unfold iris.prim_step => /=.
    repeat split => //.
    eapply r_load_packed_success => //.
    unfold smem_ind.
    by rewrite Hinstmem.
  - iIntros "!>" (es ??? HStep) "!>".

    destruct HStep as [H _].
    eapply reduce_det in H as [-> [ H | [ [? Hfirst] | (?&?&?&Hfirst & Hfirst2 &
                                                                  Hfirst3 & Hσ)(* ] *)]] ];
      last (destruct f0; eapply r_load_packed_success => //= ; unfold smem_ind ; by rewrite Hinstmem) ; 
      try by     unfold first_instr in Hfirst ; simpl in Hfirst ; inversion Hfirst.
    destruct H as [<- <-]. destruct f0; iFrame. 
Qed.

Lemma ewp_load_failure Ψ (Φ:iris.val -> frame -> iProp Σ) (E:coPset)
      (off: static_offset) (a: alignment_exponent)
      (k: i32) (n:nat) (f0: frame) t len:
  f0.(f_inst).(inst_memory) !! 0 = Some n ->
  ((Wasm_int.N_of_uint i32m k) + off + (N.of_nat (length_tnum t)) > len)%N ->
  (▷ Φ trapV f0 ∗ (N.of_nat n) ↦[wmlength] len  ⊢
     (EWP [AI_basic (BI_const (VAL_int32 k)) ;
          AI_basic (BI_load t None a off)] UNDER f0 @ E <| Ψ |> {{ w ; h, (Φ w h ∗ (N.of_nat n) ↦[wmlength] len) }})).
Proof.
  iIntros (Htv Hinstn) "(HΦ & Hwms)".
  iApply ewp_lift_atomic_step => //=.
  iIntros (σ) "Hσ !>".

  iDestruct "Hσ" as "(? & ? & ? & Hm & ? & Hframe & Hγ & ?)".
  iAssert (⌜is_Some (s_mems σ !! n)⌝)%I as %[m Hm].
  { iDestruct (gen_heap_valid with "Hγ Hwms") as %HH.
    rewrite gmap_of_list_lookup in HH.
    rewrite Nat2N.id in HH.
    rewrite list_lookup_fmap /= in HH.
    destruct (s_mems σ !! n );eauto. }  
  simplify_map_eq.
  iDestruct (wms_is_not_load with "Hwms Hγ") as %Hnload;[eauto..|].
  rewrite Nat2N.id in Hnload.
  destruct (inst_memory _) eqn:Hinstmem => //.
  inversion Hinstn; subst; clear Hinstn.
  iSplit.
  - iPureIntro.
    unfold language.reducible, language.prim_step => /=.
    eexists [], [AI_trap], (_, _,_), [].
    repeat split => //.
    eapply r_load_failure => //=.
    unfold smem_ind.
    by rewrite Hinstmem.
    by rewrite nth_error_lookup.
  - iIntros "!>" (es ??? HStep).

    rewrite -nth_error_lookup in Hm.
    iModIntro.
    destruct HStep as [HStep _].
    eapply reduce_det in HStep as [-> [H | [[? Hfirst] | (?&?&?& Hfirst & Hfirst2 &
                                                                       Hfirst3 & Hσ)]]] ;
      last (destruct f0; eapply r_load_failure => //= ; unfold smem_ind ; by rewrite Hinstmem) ;
      try by     unfold first_instr in Hfirst ; simpl in Hfirst ; inversion Hfirst.
    destruct H as [<- <-].
    iFrame. 
Qed.

Lemma ewp_load_packed_failure Ψ (Φ:iris.val -> frame -> iProp Σ) (E:coPset)
      (off: static_offset) (a: alignment_exponent)
      (k: i32) (n:nat) (f0: frame) t len tp sx :
  f0.(f_inst).(inst_memory) !! 0 = Some n ->
  ((Wasm_int.N_of_uint i32m k) + off + (N.of_nat (length_tp tp)) > len)%N ->
  (▷ Φ trapV f0 ∗ (N.of_nat n) ↦[wmlength] len  ⊢
     (EWP [AI_basic (BI_const (VAL_int32 k)) ;
          AI_basic (BI_load t (Some (tp,sx)) a off)] UNDER f0 @ E <| Ψ |> {{ w ; h, (Φ w h ∗ (N.of_nat n) ↦[wmlength] len) }})).
Proof.
  iIntros (Htv Hinstn) "(HΦ & Hwms)".
  iApply ewp_lift_atomic_step => //=.
  iIntros (σ) "Hσ !>".

  iDestruct "Hσ" as "(? & ? & ? &  Hm & ? & Hframe & Hγ & ?)".
  iAssert (⌜is_Some (s_mems σ !! n)⌝)%I as %[m Hm].
  { iDestruct (gen_heap_valid with "Hγ Hwms") as %HH.
    rewrite gmap_of_list_lookup in HH.
    rewrite Nat2N.id in HH.
    rewrite list_lookup_fmap /= in HH.
    destruct (s_mems σ !! n );eauto. }  
  simplify_map_eq.
  iDestruct (wms_is_not_load_packed _ _ _ _ _ _ _ (length_tnum t) sx  with "Hwms Hγ") as %Hnload;[eauto..|].
  rewrite Nat2N.id in Hnload.
  destruct (inst_memory _) eqn:Hinstmem => //.
  inversion Hinstn; subst; clear Hinstn.
  iSplit.
  - iPureIntro.
    unfold language.reducible, language.prim_step => /=.
    eexists [], [AI_trap], (_, _,_), [].
    repeat split => //.
    eapply r_load_packed_failure => //=.
    unfold smem_ind.
    by rewrite Hinstmem.
    by rewrite nth_error_lookup.
  - iIntros "!>" (es ??? HStep).

    rewrite -nth_error_lookup in Hm.
    iModIntro.
    destruct HStep as [HStep _].
    eapply reduce_det in HStep as [-> [H | [[? Hfirst] | (?&?&?& Hfirst & Hfirst2 &
                                                                       Hfirst3 & Hσ)]]] ;
      last (destruct f0; eapply r_load_packed_failure => //= ; unfold smem_ind ; by rewrite Hinstmem) ;
      try by     unfold first_instr in Hfirst ; simpl in Hfirst ; inversion Hfirst.
    destruct H as [<- <-].
    iFrame. 
Qed.


Lemma ewp_store Ψ (ϕ: iris.val -> frame -> iProp Σ) (E: coPset) t v
      (bs : bytes) (off: static_offset) (a: alignment_exponent) (k: i32) (n: nat) (f: frame):
  types_num_agree t v ->
  length bs = length_tnum t ->
  f.(f_inst).(inst_memory) !! 0 = Some n ->
  (▷ ϕ (immV []) f ∗
     N.of_nat n ↦[wms][ N.add (Wasm_int.N_of_uint i32m k) off ] bs) ⊢
  (EWP ([AI_basic (BI_const (VAL_int32 k)); AI_basic (BI_const v); AI_basic (BI_store t None a off)]) UNDER f @ E <| Ψ |> {{ w ; h, (ϕ w h ∗ (N.of_nat n) ↦[wms][ Wasm_int.N_of_uint i32m k + off ] (bits v)) }}).
Proof.
  iIntros (Hvt Hbs Hinstn) "(HΦ & Hwms)".
  iApply ewp_lift_atomic_step => //=.
  iIntros (σ) "Hσ !>".

  iDestruct "Hσ" as "(? & ? & ? & ? & Hm & ? & Hmemlength & ? & Hmemlimit & ?)".
  
  erewrite <- (bits_deserialise bs) => //=.
  remember (wasm_deserialise bs t) as vinit.
  assert (types_num_agree t vinit) as Hvinit.
  { rewrite Heqvinit. by apply deserialise_type. }
  destruct (bits vinit) eqn:Hb. destruct vinit ; inversion Hb.
  iDestruct (wms_implies_smems_is_Some with "Hm Hwms") as "(Hwms & Hm & %Hm)".
  destruct Hm as [m Hm].
  rewrite <- Hb.
  iDestruct (wms_is_load with "Hwms Hm") as "%Hload" => //=.
  { rewrite Hb. simpl;lia. }
  apply length_bits in Hvinit as Htt.
  apply length_bits in Hvt as Httv.
  rewrite - nth_error_lookup in Hm.
  rewrite - nth_error_lookup in Hinstn.
  simpl in Hinstn.
  destruct (inst_memory _) eqn: Hinstmem => //.
  inversion Hinstn; subst m0; clear Hinstn.
  iSplit.
  - iPureIntro.
    unfold language.reducible, language.prim_step => /=.
    
    edestruct (if_load_then_store (bits vinit) (bits v)) as [mem Hsomemem];eauto.
    { simplify_eq. erewrite length_bits => //=. }
    erewrite length_bits in Hsomemem => //=.
    eexists [], [], (_, _,_), [].
    repeat split => //.
    eapply r_store_success => //=.
    unfold smem_ind.
    by rewrite Hinstmem.    
  - iIntros "!>" (es ??? HStep).

    edestruct (if_load_then_store (bits vinit) (bits v)) as [mem Hsomemem] ; eauto;
      repeat erewrite length_bits => //=.
    erewrite length_bits in Hsomemem => //=.
    iMod (gen_heap_update_big_wm (bits vinit) (bits v) with "Hm Hwms") as "[Hm Hwms]".
    do 2 erewrite length_bits => //=. eauto.
    erewrite length_bits => //=.
    done.
    rewrite nth_error_lookup in Hm => //=.
    iModIntro.
    destruct HStep as [HStep _].
    eapply reduce_det in HStep as [-> [H | [[? Hfirst] | (?&?&?& Hfirst & Hfirst2 &
                                                                       Hfirst3 & Hσ) ]]] ;
      last (destruct f; eapply r_store_success => //= ; unfold smem_ind ; by rewrite Hinstmem) ;
      try by     unfold first_instr in Hfirst ; simpl in Hfirst ; inversion Hfirst.
    destruct H as [<- <-].
    iFrame.
    rewrite update_list_at_insert; last by rewrite nth_error_lookup in Hm; apply lookup_lt_Some in Hm.
    repeat rewrite list_fmap_insert.
    assert (length_mem mem = length_mem m) as Hmsize.
    { rewrite <- (length_bits v) in Hsomemem => //=.
      apply length_store in Hsomemem.
      by unfold length_mem, memory_list.length_mem; rewrite Hsomemem. }  
    rewrite Hmsize.
    apply store_mem_max_opt in Hsomemem as Hmemlimit.
    rewrite - Hmemlimit.
    do 2 (rewrite list_insert_id; last by rewrite list_lookup_fmap; rewrite - nth_error_lookup; rewrite Hm).
    iFrame. 
Qed.

Lemma ewp_store_packed Ψ (ϕ: iris.val -> frame -> iProp Σ) (E: coPset) t v
      (bs : bytes) (off: static_offset) (a: alignment_exponent) (k: i32) (n: nat) (f0: frame) tp:
  types_num_agree t v ->
  length bs = length_tp tp ->
  length_tp tp <  length_tnum t ->
  f0.(f_inst).(inst_memory) !! 0 = Some n ->
  (▷ ϕ (immV []) f0 ∗
  N.of_nat n ↦[wms][ N.add (Wasm_int.N_of_uint i32m k) off ] bs) ⊢
   (EWP ([AI_basic (BI_const (VAL_int32 k)); AI_basic (BI_const v); AI_basic (BI_store t (Some tp) a off)]) UNDER f0 @ E <| Ψ |>
                  {{ w ; h, (ϕ w h ∗ (N.of_nat n) ↦[wms][ Wasm_int.N_of_uint i32m k + off ] bytes_takefill #00%byte (length_tp tp) 
             (bits v))  }}).
Proof.
  iIntros (Hvt Hbs Hlt Hinstn) "(HΦ & Hwms)".
  iApply ewp_lift_atomic_step => //=.
  iIntros (σ) "Hσ !>".

  iDestruct "Hσ" as "(? & ? & ? & ? & Hm & ? & Hmemlength & ? & Hmemlimit & ?)".
  destruct bs.
  { simpl in Hbs. destruct tp;simpl in Hbs;lia. }
  iDestruct (wms_implies_smems_is_Some with "Hm Hwms") as "(Hwms & Hm & %Hm)".
  destruct Hm as [m Hm].
  iDestruct (wms_is_load with "Hwms Hm") as %Hload;eauto.
  { simpl. lia. }
  iDestruct (wms_implies_bounds with "Hwms Hm") as %Hbound;eauto.
  { simpl;lia. }
  rewrite Hbs in Hbound.
  apply enough_space_to_store' with (bs:=bits v) in Hbound as Hstore;cycle 1.
  { erewrite length_bits;eauto. } 
  destruct Hstore as [mf Hstore].
  rewrite - nth_error_lookup in Hm.
  rewrite - nth_error_lookup in Hinstn.
  simpl in Hinstn.
  destruct (inst_memory _) eqn: Hinstmem => //.
  inversion Hinstn; subst m0; clear Hinstn.
  iSplit.
  - iPureIntro.
    unfold language.reducible, language.prim_step => /=.
    eexists [], [], (_, _,_), [].
    repeat split => //.
    eapply r_store_packed_success => //=.
    unfold smem_ind.
    by rewrite Hinstmem.
  - iIntros "!>" (es ??? HStep).

    iMod (gen_heap_update_big_wm (b :: bs) (bytes_takefill #00%byte (length_tp tp) (bits v)) with "Hm Hwms")
      as "[Hm Hwms]";eauto.
    { by rewrite Hbs length_bytes_takefill. }
    { rewrite length_bytes_takefill.
      rewrite store_bytes_takefill_eq. eauto. }
    { by rewrite nth_error_lookup in Hm. }
    iModIntro.
    destruct HStep as [HStep _].
    eapply reduce_det in HStep as [-> [H | [[? Hfirst] |  (?&?&?& Hfirst & Hfirst2 &
                                                          Hfirst3 & Hσ) ]]] ;
      last (destruct f0; eapply r_store_packed_success => //= ; unfold smem_ind ; by rewrite Hinstmem) ;
      try by     unfold first_instr in Hfirst ; simpl in Hfirst ; inversion Hfirst.
    destruct H as [<- <-].
    iFrame. 
    iSimpl. erewrite (store_mem_len_eq _ _ _ (bytes_takefill #00%byte (length_tp tp) (bits v)));[iFrame|..].
    + apply store_mem_max_opt in Hstore as Hmemlimit.   
    rewrite update_list_at_insert; last by rewrite nth_error_lookup in Hm; apply lookup_lt_Some in Hm.
    rewrite list_fmap_insert list_insert_id => //.
    by rewrite list_lookup_fmap - nth_error_lookup Hm -Hmemlimit.
  + by rewrite nth_error_lookup in Hm.
  + rewrite length_bytes_takefill. rewrite store_bytes_takefill_eq. by eauto.
Qed. 

Lemma ewp_store_failure Ψ (ϕ: iris.val -> frame -> iProp Σ) (E: coPset) t v
       (off: static_offset) (a: alignment_exponent) (k: i32) (n: nat) (f0: frame) len:
  types_num_agree t v ->
  f0.(f_inst).(inst_memory) !! 0 = Some n ->
  ((Wasm_int.N_of_uint i32m k) + off + (N.of_nat (length_tnum t)) > len)%N ->
  (▷ ϕ (trapV) f0 ∗
   (N.of_nat n) ↦[wmlength] len) ⊢
  (EWP ([AI_basic (BI_const (VAL_int32 k)); AI_basic (BI_const v); AI_basic (BI_store t None a off)]) UNDER f0 @ E <| Ψ |> {{ w ; h, (ϕ w h ∗ (N.of_nat n) ↦[wmlength] len) }}).
Proof.
  iIntros (Htypes Htv Hinstn) "(HΦ & Hwms)".
  iApply ewp_lift_atomic_step => //=.
  iIntros (σ) "Hσ !>".

  iDestruct "Hσ" as "(? & ? & ? & ? & Hm & ? & Hγ & ?)".

  iAssert (⌜is_Some (s_mems σ !! n)⌝)%I as %[m Hm].
  { iDestruct (gen_heap_valid with "Hγ Hwms") as %HH.
    rewrite gmap_of_list_lookup in HH.
    rewrite Nat2N.id in HH.
    rewrite list_lookup_fmap /= in HH.
    destruct (s_mems σ !! n );eauto. }  
  simplify_map_eq.
  iDestruct (wms_is_not_store with "Hwms Hγ") as %Hnload;[eauto..|].
  rewrite Nat2N.id in Hnload.
  destruct (inst_memory _) eqn:Hinstmem => //.
  inversion Hinstn; subst; clear Hinstn.
  iSplit.
  - iPureIntro.
    unfold language.reducible, language.prim_step => /=.
    eexists [], [AI_trap], (_, _,_), [].
    repeat split => //.
    eapply r_store_failure => //=.
    unfold smem_ind.
    by rewrite Hinstmem.
    by rewrite nth_error_lookup.
  - iIntros "!>" (es ??? HStep).

    rewrite -nth_error_lookup in Hm.
    iModIntro.
    destruct HStep as [HStep _].
    eapply reduce_det in HStep as [-> [H | [[? Hfirst] | (?&?&?& Hfirst & Hfirst2 &
                                                                       Hfirst3 & Hσ)]]] ;
      last (destruct f0; eapply r_store_failure => //= ; unfold smem_ind ; by rewrite Hinstmem) ;
      try by     unfold first_instr in Hfirst ; simpl in Hfirst ; inversion Hfirst.
    destruct H as [<- <-].
    iFrame. 
Qed.

Lemma ewp_store_packed_failure Ψ (ϕ: iris.val -> frame -> iProp Σ) (E: coPset) t v
      (off: static_offset) (a: alignment_exponent) (k: i32) (n: nat) (f0: frame) len tp:
  types_num_agree t v ->
  f0.(f_inst).(inst_memory) !! 0 = Some n ->
  ((Wasm_int.N_of_uint i32m k) + off + (N.of_nat (length_tp tp)) > len)%N ->
  (▷ ϕ (trapV) f0 ∗
   (N.of_nat n) ↦[wmlength] len) ⊢
  (EWP ([AI_basic (BI_const (VAL_int32 k)); AI_basic (BI_const v); AI_basic (BI_store t (Some tp) a off)]) UNDER f0 @ E <| Ψ |> {{ w ; h, (ϕ w h ∗ (N.of_nat n) ↦[wmlength] len)}}).
Proof.
  iIntros (Htypes Htv Hinstn) "(HΦ & Hwms)".
  iApply ewp_lift_atomic_step => //=.
  iIntros (σ) "Hσ !>".

  iDestruct "Hσ" as "(? & ? & ? & ? & Hm & ? & Hγ & ?)".
  iAssert (⌜is_Some (s_mems σ !! n)⌝)%I as %[m Hm].
  { iDestruct (gen_heap_valid with "Hγ Hwms") as %HH.
    rewrite gmap_of_list_lookup in HH.
    rewrite Nat2N.id in HH.
    rewrite list_lookup_fmap /= in HH.
    destruct (s_mems σ !! n );eauto. }  
  simplify_map_eq.
  iDestruct (wms_is_not_store with "Hwms Hγ") as %Hnload;[eauto..|].
  rewrite Nat2N.id in Hnload.
  destruct (inst_memory _) eqn:Hinstmem => //.
  inversion Hinstn; subst; clear Hinstn.
  iSplit.
  - iPureIntro.
    unfold language.reducible, language.prim_step => /=.
    eexists [], [AI_trap], (_, _,_), [].
    repeat split => //.
    eapply r_store_packed_failure => //=.
    unfold smem_ind.
    by rewrite Hinstmem.
    by rewrite nth_error_lookup.
  - iIntros "!>" (es ??? HStep).

    rewrite -nth_error_lookup in Hm.
    iModIntro.
    destruct HStep as [HStep _].
    eapply reduce_det in HStep as [-> [H | [[? Hfirst] | (?&?&?& Hfirst & Hfirst2 &
                                                                       Hfirst3 & Hσ)]]] ;
      last (destruct f0; eapply r_store_packed_failure => //= ; unfold smem_ind ; by rewrite Hinstmem) ;
      try by     unfold first_instr in Hfirst ; simpl in Hfirst ; inversion Hfirst.
    destruct H as [<- <-].
    iFrame. 
Qed.
  

Lemma ewp_current_memory (E: coPset) (k: nat) (n: N) (f:frame) Ψ (Φ: iris.val -> frame -> iProp Σ):
  f.(f_inst).(inst_memory) !! 0 = Some k ->
  (▷ Φ (immV [VAL_num (VAL_int32 (Wasm_int.int_of_Z i32m (ssrnat.nat_of_bin (N.div n page_size))))]) f ∗
   (N.of_nat k) ↦[wmlength] n) ⊢
   EWP ([AI_basic (BI_current_memory)]) UNDER f @ E <| Ψ |> {{ w; h, (Φ w h∗ (N.of_nat k) ↦[wmlength] n) }}.
Proof.
  iIntros (Hf) "(HΦ & Hmemlength)".
  iApply ewp_lift_atomic_step => //=.
  iIntros (σ) "Hσ !>".

  iDestruct "Hσ" as "(? & ? & ? & ? & Hm & ? & Hγ & ?)".
  iDestruct (gen_heap_valid with "Hγ Hmemlength") as "%Hmemlength".
  rewrite - nth_error_lookup in Hf.
  rewrite gmap_of_list_lookup list_lookup_fmap Nat2N.id in Hmemlength => /=.
  destruct (s_mems σ !! k) eqn:Hmemlookup => //.
  rewrite - nth_error_lookup in Hmemlookup.
  simpl in Hmemlength.
  inversion Hmemlength; clear Hmemlength.
  iSplit.
  - iPureIntro.
    eexists [], [AI_basic (BI_const (VAL_int32 (Wasm_int.int_of_Z i32m (ssrnat.nat_of_bin (N.div n page_size)))))], (_,_,_), [].

    unfold iris.prim_step => /=.
    repeat split => //.
    eapply r_current_memory => //.
    unfold mem_size.
    by f_equal.
  - iIntros "!>" (es ??? HStep) "!>".

    destruct HStep as [H _].
    only_one_reduction H.
    iFrame. destruct f => //.
Qed.

Lemma gen_heap_alloc_grow (m m' : memory) (mems mems' : list memory) (k : nat) (n : N) : 
  mems !! k = Some m ->
  mem_grow m n = Some m' ->
  update_list_at mems k m' = mems' ->
  gen_heap_interp (gmap_of_memory mems) ==∗
                  gen_heap_interp (gmap_of_memory mems')
                  ∗ N.of_nat k↦[wms][ length_mem m ]
                  repeat (#00%byte) (N.to_nat (n * page_size)).
Proof.
  iIntros (Hmems Hgrow Hupd) "Hmems".
  assert (k < length mems) as Hk ; first by eapply lookup_lt_Some.
  assert (length (seq.take k mems) = k) as Hlentake.
  { rewrite length_is_size size_takel => //=.
    unfold ssrnat.leq, ssrnat.subn.
    rewrite - length_is_size.
    replace (k - length mems) with 0 => //= ; lia. }
  unfold mem_grow, memory_list.mem_grow in Hgrow.
  destruct (mem_size m + n <=? page_limit)%N => //=.
  destruct (mem_max_opt m) eqn:Hmaxlim.
  destruct (mem_size m +n <=? n0)%N ; inversion Hgrow.
  - remember (N.to_nat (n * page_size)) as size.
    clear Heqsize n Hgrow.
    remember (Some n0) as sn.
    clear Heqsn.
    subst mems' m' sn.
    iInduction size as [|size] "IH".
    + simpl.
      rewrite cats0.
      rewrite update_trivial.
      unfold mem_block_at_pos => //=.
      by iSplitL.
      rewrite Hmems.
      destruct m. by destruct mem_data => //=.
    + iMod ("IH" with "Hmems") as "[Hmems Hm]".
      iMod (gen_heap_alloc with "Hmems") as "( Hmems & Hown & Htk )".
      * unfold gmap_of_memory.
        instantiate (1 := (N.of_nat k, (length_mem m + N.of_nat(size))%N)).
        rewrite gmap_of_list_2d_lookup => //=.
        rewrite Nat2N.id.
        rewrite list_lookup_fmap => //=.
        unfold update_list_at => //=.
        rewrite list_lookup_middle => //=.
        unfold memory_to_list => //=.
        rewrite lookup_app_r.
        rewrite lookup_ge_None => //=.
        rewrite length_repeat.
        unfold length_mem, memory_list.length_mem.
        lia.
        unfold length_mem, memory_list.length_mem.
        lia.
      * iModIntro. 
        iSplitL "Hmems".
        -- instantiate (1 := #00%byte).
           replace (<[ _ := _ ]> (gmap_of_memory _)) with
             (gmap_of_memory
                (update_list_at
                   mems k
                   {| mem_data :=
                     {| ml_data := ml_data (mem_data m) ++
                                          repeat #00%byte (S size)
                     |} ;
                     mem_max_opt := mem_max_opt m
                   |})).
           done.
           apply map_eq.
           intros.
           destruct i.
           unfold gmap_of_memory.
           rewrite gmap_of_list_2d_lookup. 
           rewrite list_lookup_fmap.
           unfold memory_to_list.
           destruct (decide (N.to_nat n = k)) ; subst.
           ++ unfold update_list_at at 1 => //=.
              rewrite list_lookup_middle => //=.
              destruct (decide (n1 = (length_mem m + N.of_nat size)%N)) ; subst.
              ** rewrite N2Nat.id.
                 rewrite lookup_insert.
                 rewrite lookup_app_r.
                 unfold length_mem, memory_list.length_mem.
                 replace (N.to_nat (N.of_nat (length (ml_data (mem_data m))) +
                                      N.of_nat size) -
                         length (ml_data (mem_data m))) with size ; last lia.
                 rewrite repeat_cons.
                 rewrite lookup_app_r ; last by rewrite length_repeat.
                 rewrite length_repeat.
                 rewrite PeanoNat.Nat.sub_diag => //=.
                 unfold length_mem, memory_list.length_mem ; lia.
              ** rewrite lookup_insert_ne ; last by intro H ; inversion H ; apply n2.
                 rewrite gmap_of_list_2d_lookup.
                 rewrite list_lookup_fmap.
                 unfold update_list_at => //=.
                 rewrite (list_lookup_middle _ _ _ (N.to_nat n)) => //=.
                 rewrite repeat_cons.
                 rewrite catA.
                 destruct (decide (n1 < (length_mem m + N.of_nat size))%N).
                 rewrite lookup_app_l => //=.
                 rewrite length_app length_repeat.
                 unfold length_mem, memory_list.length_mem in l.
                 lia.
                 rewrite lookup_ge_None_2. 
                 rewrite lookup_ge_None_2 => //=.
                 rewrite length_app length_repeat.
                 unfold length_mem, memory_list.length_mem in n3.
                 lia.
                 repeat rewrite length_app => //=.
                 rewrite length_repeat.
                 unfold length_mem, memory_list.length_mem in n3.
                 unfold length_mem, memory_list.length_mem in n2.
                 lia.
           ++ rewrite lookup_insert_ne ; last by intros H ; inversion H ; lia.
              rewrite gmap_of_list_2d_lookup.
              rewrite list_lookup_fmap.
              rewrite update_ne => //=. 
              rewrite update_ne => //=.
        -- replace (S size) with (size + 1) ; last lia.
           rewrite repeat_app.
           unfold mem_block_at_pos.
           iApply big_opL_app.
           iFrame "Hm".
           iSplitL => //=.
           rewrite length_repeat.
           rewrite Nat2N.inj_add.
           rewrite N2Nat.id.
           rewrite Nat.add_0_r.
           done.
  - remember (N.to_nat (n * page_size)) as size.
    inversion Hgrow.
    clear Heqsize n Hgrow.
    remember None as sn.
    clear Heqsn.
    subst mems' m' sn.
    iInduction size as [|size] "IH".
    + simpl.
      rewrite cats0.
      rewrite update_trivial.
      unfold mem_block_at_pos => //=.
      by iSplitL.
      rewrite Hmems.
      destruct m. by destruct mem_data => //=.
    + iMod ("IH" with "Hmems") as "[Hmems Hm]".
      iMod (gen_heap_alloc with "Hmems") as "( Hmems & Hown & Htk )".
      * unfold gmap_of_memory.
        instantiate (1 := (N.of_nat k, (length_mem m + N.of_nat(size))%N)).
        rewrite gmap_of_list_2d_lookup => //=.
        rewrite Nat2N.id.
        rewrite list_lookup_fmap => //=.
        unfold update_list_at => //=.
        rewrite list_lookup_middle => //=.
        unfold memory_to_list => //=.
        rewrite lookup_app_r.
        rewrite lookup_ge_None => //=.
        rewrite length_repeat.
        unfold length_mem, memory_list.length_mem.
        lia.
        unfold length_mem, memory_list.length_mem.
        lia.
      * iModIntro. 
        iSplitL "Hmems".
        -- instantiate (1 := #00%byte).
           replace (<[ _ := _ ]> (gmap_of_memory _)) with
             (gmap_of_memory
                (update_list_at
                   mems k
                   {| mem_data :=
                     {| ml_data := ml_data (mem_data m) ++
                                          repeat #00%byte (S size)
                     |} ;
                     mem_max_opt := mem_max_opt m
                   |})).
           done.
           apply map_eq.
           intros.
           destruct i.
           unfold gmap_of_memory.
           rewrite gmap_of_list_2d_lookup. 
           rewrite list_lookup_fmap.
           unfold memory_to_list.
           destruct (decide (N.to_nat n = k)) ; subst.
           ++ unfold update_list_at at 1 => //=.
              rewrite list_lookup_middle => //=.
              destruct (decide (n0 = (length_mem m + N.of_nat size)%N)) ; subst.
              ** rewrite N2Nat.id.
                 rewrite lookup_insert.
                 rewrite lookup_app_r.
                 unfold length_mem, memory_list.length_mem.
                 replace (N.to_nat (N.of_nat (length (ml_data (mem_data m))) +
                                      N.of_nat size) -
                         length (ml_data (mem_data m))) with size ; last lia.
                 rewrite repeat_cons.
                 rewrite lookup_app_r ; last by rewrite length_repeat.
                 rewrite length_repeat.
                 rewrite PeanoNat.Nat.sub_diag => //=.
                 unfold length_mem, memory_list.length_mem ; lia.
              ** rewrite lookup_insert_ne ; last by intro H ; inversion H ; apply n1.
                 rewrite gmap_of_list_2d_lookup.
                 rewrite list_lookup_fmap.
                 unfold update_list_at => //=.
                 rewrite (list_lookup_middle _ _ _ (N.to_nat n)) => //=.
                 rewrite repeat_cons.
                 rewrite catA.
                 destruct (decide (n0 < (length_mem m + N.of_nat size))%N).
                 rewrite lookup_app_l => //=.
                 rewrite length_app length_repeat.
                 unfold length_mem, memory_list.length_mem in l.
                 lia.
                 rewrite lookup_ge_None_2. 
                 rewrite lookup_ge_None_2 => //=.
                 rewrite length_app length_repeat.
                 unfold length_mem, memory_list.length_mem in n2.
                 lia.
                 repeat rewrite length_app => //=.
                 rewrite length_repeat.
                 unfold length_mem, memory_list.length_mem in n2.
                 unfold length_mem, memory_list.length_mem in n1.
                 lia.
           ++ rewrite lookup_insert_ne ; last by intros H ; inversion H ; lia.
              rewrite gmap_of_list_2d_lookup.
              rewrite list_lookup_fmap.
              rewrite update_ne => //=. 
              rewrite update_ne => //=.
        -- replace (S size) with (size + 1) ; last lia.
           rewrite repeat_app.
           unfold mem_block_at_pos.
           iApply big_opL_app.
           iFrame "Hm".
           iSplitL => //=.
           rewrite length_repeat.
           rewrite Nat2N.inj_add.
           rewrite N2Nat.id.
           rewrite Nat.add_0_r.
           done.
Qed.

Definition mem_in_bound (c: N):= (c <= page_limit)%N.

Lemma ewp_grow_memory (E: coPset) (k: nat) (f : frame)
      (n: N) Ψ (Φ Φ' : iris.val -> frame -> iProp Σ) (c: i32):
  f.(f_inst).(inst_memory) !! 0 = Some k ->
  ( 
     (N.of_nat k) ↦[wmlength] n ∗
     ▷ Φ (immV [VAL_num $ VAL_int32 (Wasm_int.int_of_Z i32m (ssrnat.nat_of_bin (n `div` page_size)%N))]) f ∗
     ▷ Φ' (immV [VAL_num $ VAL_int32 int32_minus_one]) f)
    ⊢ EWP [AI_basic (BI_const (VAL_int32 c)) ; AI_basic (BI_grow_memory)]
    UNDER f @ E <| Ψ |> {{ w ; h, ((Φ w h ∗
                    ((N.of_nat k) ↦[wms][ n ]
                    repeat #00%byte (N.to_nat (Wasm_int.N_of_uint i32m c * page_size))) ∗
                    (N.of_nat k) ↦[wmlength]
                    (n + Wasm_int.N_of_uint i32m c * page_size)%N) ∗
                    ⌜ mem_in_bound ((n `div` page_size + Wasm_int.N_of_uint i32m c)) ⌝
                 ∨ (Φ' w h ∗ (N.of_nat k) ↦[wmlength] n)) }}.
Proof.
  iIntros (Hfm) "(Hmlength & HΦ & HΨ)".
  iApply ewp_lift_atomic_step => //=.
  iIntros (σ) "Hσ !>".

  iDestruct "Hσ" as "(? & ? & ? & ? & Hm & ? & Hmemlength & ? & Hmemlimit & ?)".

  iDestruct (gen_heap_valid with "Hmemlength Hmlength") as "%Hmemlength".
  rewrite - nth_error_lookup in Hfm.
  rewrite gmap_of_list_lookup list_lookup_fmap Nat2N.id in Hmemlength => /=.
  destruct (s_mems σ !! k) eqn:Hmemlookup => //.
  simpl in Hmemlength.
  inversion Hmemlength as [Hmemlength']; clear Hmemlength.
  iSplit.
  - iPureIntro.
    unfold reducible, language.prim_step => /=.
    eexists _,_,(_,_,_),_.
    repeat split => //=.
    eapply r_grow_memory_failure => //=.
    by rewrite nth_error_lookup.
  - iIntros "!>" (es ??? HStep). 

    destruct HStep as [H _].
    remember [AI_basic (BI_const (VAL_int32 c)) ; AI_basic BI_grow_memory] as es0.
    remember {| f_locs := f_locs f ; f_inst := f_inst f |} as f0.
    remember {| f_locs := locs2 ; f_inst := inst2 |} as f'.
    replace [AI_basic (BI_const (VAL_int32 c)) ; AI_basic BI_grow_memory] with
      ([AI_basic (BI_const (VAL_int32 c))] ++ [AI_basic BI_grow_memory]) in Heqes0 => //=.
    induction H ; try by inversion Heqes0 ;
      try by apply app_inj_tail in Heqes0 as [_ Habs] ; inversion Habs.
    all: try by destruct vs; last (by repeat destruct vs => //); inversion Heqes0.
    all: try by destruct ves; last (by repeat destruct ves => //); inversion Heqes0.
    { destruct H ; try by inversion Heqes0 ;
        try by apply app_inj_tail in Heqes0 as [_ Habs] ; inversion Habs.
      rewrite Heqes0 in H0.
      move/lfilledP in H0.
      inversion H0; subst.
      all: try by do 3 destruct vs => //.
      all: try by do 3 destruct bef => //. 
    } 
    { (* grow_memory succeeded *)
      inversion Heqes0 ; subst c0; clear Heqes0.
      unfold smem_ind in H.
      destruct f; rewrite Heqf0 in Heqf'; inversion Heqf'; subst; simpl in *.
      destruct (inst_memory inst2) ; try by inversion Hfm.
      simpl in Hfm.
      inversion Hfm ; subst m1 ; clear Hfm.
      inversion H ; subst i ; clear H.
      rewrite nth_error_lookup in H0.
      rewrite Hmemlookup in H0.
      inversion H0 ; subst m0 ; clear H0.
      unfold mem_size.

      unfold upd_s_mem => //=.
      iMod (gen_heap_update with "Hmemlength Hmlength") as "[Hmemlength Hmlength]".
      iMod (gen_heap_alloc_grow with "Hm") as "[Hm Hown]" => //=.
      iIntros "!>".
      iFrame.
      iSplitL "Hmemlength Hmemlimit".
      - rewrite - gmap_of_list_insert.
        + rewrite Nat2N.id.
          instantiate (1:= length_mem mem').
          rewrite - list_fmap_insert.
          rewrite update_list_at_insert; last by apply lookup_lt_Some in Hmemlookup.
          iFrame.
          rewrite list_fmap_insert list_insert_id => //.
          rewrite list_lookup_fmap Hmemlookup.
          apply mem_grow_max in H2.
          simpl.
          by f_equal.
        + rewrite Nat2N.id.
          rewrite length_fmap.
          by apply lookup_lt_Some in Hmemlookup.
      - iLeft.
        iSplit.
        + apply mem_grow_length in H2.
          rewrite H2. 
          replace (Wasm_int.N_of_uint i32m c) with (Z.to_N (Wasm_int.Int32.unsigned c)) ;
            last done.
          iFrame.
        + iPureIntro.
          unfold mem_in_bound.
          unfold mem_grow in H2.
          destruct (_ <=? page_limit)%N eqn:HLP => //=.
          unfold mem_size in HLP.
          move/N.leb_spec0 in HLP.
          by apply HLP.
    }
    { (* grow_memory failed *)
      iSplitR "HΨ Hmlength"  => //.
      iFrame => //.
      simpl.
      iRight.
      rewrite Heqf0; destruct f;
      by iFrame.  }
    rewrite Heqes0 in H0.
    move/lfilledP in H0; inversion H0; subst.
    2: by repeat destruct vs => //.
    2-3: by repeat destruct bef => //. 
    destruct vs.
    { destruct es ; first by exfalso ; eapply empty_no_reduce.
      inversion H0.
      apply app_eq_unit in H9 as [[ -> -> ] | [-> ->]].
      by subst ; exfalso ; eapply values_no_reduce.
      subst.
      unfold lfilled, lfill in H1.
      simpl in H1.
      rewrite app_nil_r in H1.
      move/eqP in H1 ; subst.
      apply IHreduce => //=. }
    exfalso.
    inversion H0.
    apply app_eq_unit in H9 as [[ _ Hes ] | [ _ Hes]].
    apply app_eq_unit in Hes as [[ -> _ ] | [Hes _ ]].
    by eapply empty_no_reduce.
    rewrite <- app_nil_l in Hes.
    clear - Hes H.
    induction H.
    destruct H.
    all: try by inversion Hes.
    all: try by do 2 destruct vs => //.
    move/lfilledP in H0; inversion H0; subst.
    do 2 destruct vs => //.
    all: try by do 2 destruct bef => //.
    all: try by do 2 destruct ves => //.
    move/lfilledP in H0; inversion H0; subst.
    all: try by do 2 destruct vs => //.
    all: try by do 2 destruct bef => //.
    destruct vs; last by destruct vs, es => //; empty_list_no_reduce.
    destruct es; first empty_list_no_reduce.
    inversion H6; subst.
    destruct es, es'0 => //.
    destruct es, es'0 => //.
    destruct vs => //.
    inversion H2; subst.
    simpl in H6. done.
Qed.
      
End iris_rules_resources.

