Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition CrossSwap (st st' : list Z * list Z) (op : Z * Z) : Prop :=
  let ' (s, t) := st in let ' (s', t') := st' in let ' (i, j) := op in
  0 <= i < Zlength s /\ 0 <= j < Zlength t /\
  s' = replace_Znth i (Znth j t 0) s /\ t' = replace_Znth j (Znth i s 0) t.
Definition SwapsWork (s t : list Z) (ops : list (Z * Z)) : Prop :=
  1 <= Zlength ops <= 2 * Zlength s /\ exists st : list (list Z * list Z),
    Zlength st = Zlength ops + 1 /\ Znth 0 st ([], []) = (s, t) /\
    (forall q, 0 <= q < Zlength ops -> CrossSwap (Znth q st ([], [])) (Znth (q + 1) st ([], [])) (Znth q ops (0, 0))) /\
    fst (Znth (Zlength ops) st ([], [])) = snd (Znth (Zlength ops) st ([], [])).
Definition Pre (s t : list Z) : Prop :=
  (* Stated explicitly in the P046 solver Require, so dropped here:
       2 <= Zlength s <= 50 /\
       Zlength t = Zlength s /\
       Forall (fun c => 97 <= c <= 122) s /\
       Forall (fun c => 97 <= c <= 122) t  *)
  s <> t.

Definition Spec (s t : list Z) (out : option (list (Z * Z))) : Prop :=
  (out = None /\ ~exists ops, SwapsWork s t ops) \/ (exists ops, out = Some ops /\ SwapsWork s t ops).

Definition CountedPrefix
    (s t : list Z) (i : Z) (counts : list Z) : Prop :=
  Zlength counts = 26 /\
  forall c, 0 <= c < 26 ->
    Znth c counts 0 =
      Z.of_nat
        (count_occ Z.eq_dec
          (sublist 0 i s ++ sublist 0 i t) (97 + c)).

Definition CountsEvenBefore (counts : list Z) (bound : Z) : Prop :=
  forall c, 0 <= c < bound -> Z.modulo (Znth c counts 0) 2 = 0.

Definition CombinedEven (s t : list Z) : Prop :=
  forall c, 0 <= c < 26 ->
    Z.modulo
      (Z.of_nat (count_occ Z.eq_dec (s ++ t) (97 + c))) 2 = 0.

Definition CombinedOddAt (s t : list Z) (c : Z) : Prop :=
  0 <= c < 26 /\
  Z.modulo
    (Z.of_nat (count_occ Z.eq_dec (s ++ t) (97 + c))) 2 = 1.

Definition SwapTrace
    (s0 t0 s t : list Z) (ops : list (Z * Z)) : Prop :=
  exists states : list (list Z * list Z),
    Zlength states = Zlength ops + 1 /\
    Znth 0 states ([], []) = (s0, t0) /\
    (forall q, 0 <= q < Zlength ops ->
      CrossSwap
        (Znth q states ([], []))
        (Znth (q + 1) states ([], []))
        (Znth q ops (0, 0))) /\
    Znth (Zlength ops) states ([], []) = (s, t).

Definition PrefixEqual (s t : list Z) (i : Z) : Prop :=
  forall k, 0 <= k < i -> Znth k s 0 = Znth k t 0.

Definition NoValueInRange
    (l : list Z) (value lo hi : Z) : Prop :=
  forall k, lo <= k < hi -> Znth k l 0 <> value.

Definition OperationLists
    (ops : list (Z * Z)) (is js : list Z) : Prop :=
  Zlength is = Zlength ops /\
  Zlength js = Zlength ops /\
  (forall q, 0 <= q < Zlength ops ->
    Znth q is 0 = fst (Znth q ops (0, 0)) + 1 /\
    Znth q js 0 = snd (Znth q ops (0, 0)) + 1).

Definition RepairState
    (source target s t : list Z) (i : Z)
    (ops : list (Z * Z)) : Prop :=
  Zlength s = Zlength source /\
  Zlength t = Zlength target /\
  PrefixEqual s t i /\
  Permutation (source ++ target) (s ++ t) /\
  CombinedEven s t /\
  SwapTrace source target s t ops /\
  0 <= Zlength ops <= 2 * i.

Require Import Coq.micromega.Lia.
Lemma zlength_replace_znth__count_invariants :
  forall {A : Type} (l : list A) (n : Z) (v : A),
    Zlength (replace_Znth n v l) = Zlength l.
Proof.
  intros A l n v.
  assert (Hlen : forall (m : nat) (xs : list A),
    length (replace_nth m xs v) = length xs).
  {
    intros m xs.
    revert m.
    induction xs as [|x xs IH]; intros [|m]; simpl; auto.
  }
  rewrite !Zlength_correct.
  unfold replace_Znth.
  rewrite Hlen.
  reflexivity.
Qed.
Lemma counted_prefix_counter_bound__count_invariants :
  forall (s t counts : list Z) (i c : Z),
    0 <= i ->
    i <= Zlength s ->
    i <= Zlength t ->
    0 <= c < 26 ->
    CountedPrefix s t i counts ->
    0 <= Znth c counts 0 <= 2 * i.
Proof.
  intros s t counts i c Hi His Hit Hc Hprefix.
  destruct Hprefix as [_ Hprefix].
  specialize (Hprefix c Hc).
  rewrite Hprefix.
  pose proof
    (count_occ_bound Z.eq_dec (97 + c)
      (sublist 0 i s ++ sublist 0 i t)) as Hbound.
  assert (HboundZ :
    Z.of_nat
      (count_occ Z.eq_dec (sublist 0 i s ++ sublist 0 i t) (97 + c)) <=
    Z.of_nat (length (sublist 0 i s ++ sublist 0 i t))) by lia.
  rewrite <- Zlength_correct in HboundZ.
  rewrite Zlength_app in HboundZ.
  rewrite (Zlength_sublist0 i s) in HboundZ by lia.
  rewrite (Zlength_sublist0 i t) in HboundZ by lia.
  lia.
Qed.
Lemma counted_prefix_step__count_invariants :
  forall (s t counts : list Z) (i : Z),
    0 <= i < Zlength s ->
    0 <= i < Zlength t ->
    97 <= Znth i s 0 <= 122 ->
    97 <= Znth i t 0 <= 122 ->
    CountedPrefix s t i counts ->
    CountedPrefix s t (i + 1)
      (replace_Znth (Znth i t 0 - 97)
        (Znth (Znth i t 0 - 97)
          (replace_Znth (Znth i s 0 - 97)
            (Znth (Znth i s 0 - 97) counts 0 + 1) counts) 0 + 1)
        (replace_Znth (Znth i s 0 - 97)
          (Znth (Znth i s 0 - 97) counts 0 + 1) counts)).
Proof.
  intros s t counts i His Hit Hsi Hti Hprefix.
  destruct Hprefix as [Hlen Hprefix].
  unfold CountedPrefix.
  split.
  - rewrite !zlength_replace_znth__count_invariants.
    exact Hlen.
  - intros c Hc.
    assert (Hsi_idx : 0 <= Znth i s 0 - 97 < Zlength counts) by lia.
    assert (Hti_idx : 0 <= Znth i t 0 - 97 < Zlength counts) by lia.
    assert (Hc_idx : 0 <= c < Zlength counts) by lia.
    specialize (Hprefix c Hc).
    assert (Hs_sub :
      sublist 0 (i + 1) s = sublist 0 i s ++ [Znth i s 0]).
    {
      rewrite (sublist_split 0 (i + 1) i s) by lia.
      rewrite (sublist_single 0 i s) by lia.
      reflexivity.
    }
    assert (Ht_sub :
      sublist 0 (i + 1) t = sublist 0 i t ++ [Znth i t 0]).
    {
      rewrite (sublist_split 0 (i + 1) i t) by lia.
      rewrite (sublist_single 0 i t) by lia.
      reflexivity.
    }
    rewrite Hs_sub, Ht_sub.
    rewrite !count_occ_app.
    destruct (Z.eq_dec (Znth i s 0) (97 + c)) as [Hsc | Hsc];
      destruct (Z.eq_dec (Znth i t 0) (97 + c)) as [Htc | Htc].
    + rewrite (@count_occ_cons_eq Z Z.eq_dec [] (Znth i s 0) (97 + c)) by exact Hsc.
      rewrite (@count_occ_cons_eq Z Z.eq_dec [] (Znth i t 0) (97 + c)) by exact Htc.
      cbn [count_occ].
      replace (Znth i t 0 - 97) with c in * by lia.
      replace (Znth i s 0 - 97) with c in * by lia.
      rewrite Znth_replace_Znth_Same by
        (rewrite zlength_replace_znth__count_invariants; exact Hc_idx).
      rewrite Znth_replace_Znth_Same by exact Hc_idx.
      rewrite count_occ_app in Hprefix.
      rewrite Hprefix.
      rewrite !Nat2Z.inj_add.
      lia.
    + rewrite (@count_occ_cons_eq Z Z.eq_dec [] (Znth i s 0) (97 + c)) by exact Hsc.
      rewrite (@count_occ_cons_neq Z Z.eq_dec [] (Znth i t 0) (97 + c)) by exact Htc.
      cbn [count_occ].
      replace (Znth i s 0 - 97) with c in * by lia.
      rewrite Znth_replace_Znth_Diff by
        (try rewrite zlength_replace_znth__count_invariants; lia).
      rewrite Znth_replace_Znth_Same by exact Hc_idx.
      rewrite count_occ_app in Hprefix.
      rewrite Hprefix.
      rewrite !Nat2Z.inj_add.
      lia.
    + rewrite (@count_occ_cons_neq Z Z.eq_dec [] (Znth i s 0) (97 + c)) by exact Hsc.
      rewrite (@count_occ_cons_eq Z Z.eq_dec [] (Znth i t 0) (97 + c)) by exact Htc.
      cbn [count_occ].
      replace (Znth i t 0 - 97) with c in * by lia.
      rewrite Znth_replace_Znth_Same by
        (rewrite zlength_replace_znth__count_invariants; lia).
      rewrite Znth_replace_Znth_Diff by (try exact Hsi_idx; try exact Hc_idx; lia).
      rewrite count_occ_app in Hprefix.
      rewrite Hprefix.
      rewrite !Nat2Z.inj_add.
      lia.
    + rewrite (@count_occ_cons_neq Z Z.eq_dec [] (Znth i s 0) (97 + c)) by exact Hsc.
      rewrite (@count_occ_cons_neq Z Z.eq_dec [] (Znth i t 0) (97 + c)) by exact Htc.
      cbn [count_occ].
      rewrite Znth_replace_Znth_Diff by
        (try rewrite zlength_replace_znth__count_invariants; lia).
      rewrite Znth_replace_Znth_Diff by (try exact Hsi_idx; try exact Hc_idx; lia).
      rewrite count_occ_app in Hprefix.
      rewrite Hprefix.
      rewrite !Nat2Z.inj_add.
      lia.
Qed.
Lemma counted_prefix_full_count__parity_scan :
  forall source target n counts c,
    n = Zlength source ->
    Zlength target = n ->
    CountedPrefix source target n counts ->
    0 <= c < 26 ->
    Znth c counts 0 =
      Z.of_nat (count_occ Z.eq_dec (source ++ target) (97 + c)).
Proof.
  intros source target n counts c Hsource Htarget Hcounted Hc.
  destruct Hcounted as [_ Hcounted].
  specialize (Hcounted c Hc).
  rewrite (sublist_self source n Hsource) in Hcounted.
  rewrite (sublist_self target n (eq_sym Htarget)) in Hcounted.
  exact Hcounted.
Qed.
Lemma counts_even_before_succ__parity_scan :
  forall counts c,
    0 <= c ->
    0 <= Znth c counts 0 ->
    CountsEvenBefore counts c ->
    Z.rem (Znth c counts 0) 2 = 0 ->
    CountsEvenBefore counts (c + 1).
Proof.
  intros counts c Hc Hcurrent_nonneg Heven Hcurrent.
  rewrite Z.rem_mod_nonneg in Hcurrent by lia.
  unfold CountsEvenBefore in *.
  intros k Hk.
  destruct (Z.lt_trichotomy k c) as [Hlt | [Heq | Hgt]].
  - apply Heven; lia.
  - subst k; exact Hcurrent.
  - lia.
Qed.
Lemma combined_parity_from_full_counts__parity_scan :
  forall source target n counts,
    n = Zlength source ->
    Zlength target = n ->
    CountedPrefix source target n counts ->
    (CountsEvenBefore counts 26 -> CombinedEven source target) /\
    (forall c,
      0 <= c < 26 ->
      Z.rem (Znth c counts 0) 2 <> 0 ->
      CombinedOddAt source target c).
Proof.
  intros source target n counts Hsource Htarget Hcounted.
  split.
  - intros Heven c Hc.
    unfold CountsEvenBefore in Heven.
    specialize (Heven c Hc).
    rewrite (counted_prefix_full_count__parity_scan
      source target n counts c Hsource Htarget Hcounted Hc) in Heven.
    exact Heven.
  - intros c Hc Hodd.
    pose proof (counted_prefix_full_count__parity_scan
      source target n counts c Hsource Htarget Hcounted Hc) as Hfull.
    assert (0 <= Znth c counts 0) as Hnonneg by (rewrite Hfull; lia).
    rewrite Z.rem_mod_nonneg in Hodd by lia.
    split; [exact Hc |].
    rewrite <- Hfull.
    pose proof (Z.mod_pos_bound (Znth c counts 0) 2 ltac:(lia)) as Hmod.
    lia.
Qed.
Lemma repair_state_initial__repair_control :
  forall source target,
    CombinedEven source target ->
    RepairState source target source target 0 [].
Proof.
  intros source target Heven.
  unfold RepairState.
  split; [reflexivity |].
  split; [reflexivity |].
  split.
  - unfold PrefixEqual. intros k Hk. lia.
  - split.
    + apply Permutation_refl.
    + split; [exact Heven |].
      split.
      * unfold SwapTrace.
        exists [(source, target)].
        split; [reflexivity |].
        split; [reflexivity |].
        split.
        -- intros q Hq. rewrite Zlength_nil in Hq. lia.
        -- reflexivity.
      * rewrite Zlength_nil. lia.
Qed.
Lemma no_value_range_empty__repair_control :
  forall l value lo,
    NoValueInRange l value lo lo.
Proof.
  intros l value lo k Hk.
  lia.
Qed.
Lemma no_value_range_extend__repair_control :
  forall l value lo hi,
    NoValueInRange l value lo hi ->
    Znth hi l 0 <> value ->
    NoValueInRange l value lo (hi + 1).
Proof.
  intros l value lo hi Hrange Hhi k Hk.
  destruct (Z_lt_ge_dec k hi) as [Hlt | Hge].
  - apply Hrange. lia.
  - assert (k = hi) by lia. subst k. exact Hhi.
Qed.
Lemma operation_lists_empty__repair_control :
  OperationLists [] [] [].
Proof.
  unfold OperationLists.
  split; [reflexivity |].
  split; [reflexivity |].
  intros q Hq.
  rewrite Zlength_nil in Hq.
  lia.
Qed.
Lemma repair_state_advance_equal__repair_transitions :
  forall source target s t i ops,
    RepairState source target s t i ops ->
    0 <= i < Zlength s ->
    Znth i s 0 = Znth i t 0 ->
    RepairState source target s t (i + 1) ops.
Proof.
  intros source target s t i ops Hstate Hi Heq.
  unfold RepairState in *.
  destruct Hstate as
      [Hs [Ht [Hprefix [Hperm [Heven [Htrace [Hop0 Hop1]]]]]]].
  repeat split; try assumption.
  - unfold PrefixEqual in *.
    intros k Hk.
    destruct (Z_lt_ge_dec k i).
    + apply Hprefix. lia.
    + assert (k = i) by lia. subst k. exact Heq.
  - lia.
Qed.
Lemma replace_znth_preserves_char_bounds__repair_transitions :
  forall xs i v k,
    Zlength xs = k ->
    0 <= i < k ->
    97 <= v <= 122 ->
    (forall q, 0 <= q < k -> 97 <= Znth q xs 0 <= 122) ->
    forall q, 0 <= q < k ->
      97 <= Znth q (replace_Znth i v xs) 0 <= 122.
Proof.
  intros xs i v k Hlen Hi Hv Hxs q Hq.
  destruct (Z.eq_dec q i) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by lia. exact Hv.
  - rewrite Znth_replace_Znth_Diff by lia. apply Hxs. exact Hq.
Qed.
Lemma replace_Znth_decomp__repair_transitions :
  forall {A : Type} i (l : list A) (v : A),
    0 <= i < Zlength l ->
    replace_Znth i v l =
      firstn (Z.to_nat i) l ++ v :: skipn (S (Z.to_nat i)) l.
Proof.
  intros A i l v Hi.
  unfold replace_Znth.
  revert i Hi.
  induction l as [|x l IH]; intros i Hi.
  - rewrite Zlength_nil in Hi. lia.
  - simpl.
    destruct (Z.to_nat i) eqn:Ei.
    + reflexivity.
    + simpl.
      f_equal.
      replace n with (Z.to_nat (i - 1)) by lia.
      apply IH.
      rewrite Zlength_cons in Hi.
      lia.
Qed.
Lemma Zlength_replace_Znth__repair_transitions :
  forall {A : Type} (l : list A) i (v : A),
    Zlength (replace_Znth i v l) = Zlength l.
Proof.
  intros A l i v.
  revert i.
  induction l; simpl in *; intros; auto.
  unfold replace_Znth in *.
  destruct (Z.to_nat i).
  - simpl. do 2 rewrite Zlength_cons. lia.
  - simpl. do 2 rewrite Zlength_cons.
    specialize (IHl (Z.of_nat n)).
    replace (Z.to_nat (Z.of_nat n)) with n in IHl by lia.
    rewrite IHl. lia.
Qed.
Lemma cross_swap_combined_permutation__repair_transitions :
  forall s t a b,
    0 <= a < Zlength s ->
    0 <= b < Zlength t ->
    Permutation (s ++ t)
      (replace_Znth a (Znth b t 0) s ++
       replace_Znth b (Znth a s 0) t).
Proof.
  intros s t a b Ha Hb.
  pose proof
    (replace_Znth_decomp__repair_transitions a s (Znth a s 0) Ha) as Hs.
  pose proof
    (replace_Znth_decomp__repair_transitions b t (Znth b t 0) Hb) as Ht.
  rewrite replace_Znth_Znth in Hs, Ht.
  rewrite (replace_Znth_decomp__repair_transitions a s (Znth b t 0)) by
      exact Ha.
  rewrite (replace_Znth_decomp__repair_transitions b t (Znth a s 0)) by
      exact Hb.
  rewrite Hs at 1.
  rewrite Ht at 1.
  repeat rewrite <- app_assoc.
  apply Permutation_app_head.
  apply (proj2 (Permutation_count_occ Z.eq_dec _ _)).
  intro z.
  repeat rewrite count_occ_app.
  simpl.
  destruct (Z.eq_dec (Znth a s 0) z);
  destruct (Z.eq_dec (Znth b t 0) z); lia.
Qed.
Lemma combined_even_permutation__repair_transitions :
  forall s t s' t',
    CombinedEven s t ->
    Permutation (s ++ t) (s' ++ t') ->
    CombinedEven s' t'.
Proof.
  intros s t s' t' Heven Hperm.
  unfold CombinedEven in *.
  intros c Hc.
  pose proof
    (proj1 (Permutation_count_occ Z.eq_dec (s ++ t) (s' ++ t'))
       Hperm (97 + c)) as Hcount.
  rewrite <- Hcount.
  apply Heven. exact Hc.
Qed.
Lemma swap_trace_append__repair_transitions :
  forall source target s t ops s' t' op,
    SwapTrace source target s t ops ->
    CrossSwap (s, t) (s', t') op ->
    SwapTrace source target s' t' (ops ++ [op]).
Proof.
  intros source target s t ops s' t' op Htrace Hstep.
  unfold SwapTrace in *.
  destruct Htrace as [states [Hlen [Hfirst [Hsteps Hlast]]]].
  exists (states ++ [(s', t')]).
  repeat split.
  - rewrite !Zlength_app, !Zlength_cons, !Zlength_nil. lia.
  - rewrite app_Znth1.
    + exact Hfirst.
    + rewrite Hlen. pose proof (Zlength_nonneg ops). lia.
  - intros q Hq.
    rewrite Zlength_app, Zlength_cons, Zlength_nil in Hq.
    destruct (Z_lt_ge_dec q (Zlength ops)).
    + rewrite !app_Znth1 by lia.
      apply Hsteps. lia.
    + assert (q = Zlength ops) by lia. subst q.
      rewrite app_Znth1 by
          (rewrite Hlen; pose proof (Zlength_nonneg ops); lia).
      rewrite app_Znth2 by (rewrite Hlen; lia).
      rewrite app_Znth2 by lia.
      replace (Zlength ops - Zlength ops) with 0 by lia.
      replace (Zlength ops + 1 - Zlength states) with 0 by lia.
      simpl.
      rewrite Hlast.
      exact Hstep.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil.
    rewrite app_Znth2 by (rewrite Hlen; lia).
    rewrite Hlen.
    rewrite Z.sub_diag.
    simpl. reflexivity.
Qed.
Lemma operation_lists_append__repair_transitions :
  forall ops is js a b,
    OperationLists ops is js ->
    OperationLists (ops ++ [(a, b)]) (is ++ [a + 1]) (js ++ [b + 1]).
Proof.
  intros ops is js a b Hlists.
  unfold OperationLists in *.
  destruct Hlists as [His [Hjs Hentries]].
  split.
  - rewrite !Zlength_app, !Zlength_cons, !Zlength_nil. lia.
  - split.
    + rewrite !Zlength_app, !Zlength_cons, !Zlength_nil. lia.
    + intros q Hq.
    rewrite Zlength_app, Zlength_cons, Zlength_nil in Hq.
    destruct (Z_lt_ge_dec q (Zlength ops)).
    * rewrite !app_Znth1 by lia. apply Hentries. lia.
    * assert (q = Zlength ops) by lia. subst q.
      rewrite !app_Znth2 by lia.
      rewrite His, Hjs.
      repeat rewrite Z.sub_diag.
      simpl. auto.
Qed.
Lemma repair_state_cross_swap__repair_transitions :
  forall source target s t i ops s' t' a b,
    RepairState source target s t i ops ->
    CrossSwap (s, t) (s', t') (a, b) ->
    PrefixEqual s' t' (i + 1) ->
    Zlength ops + 1 <= 2 * (i + 1) ->
    RepairState source target s' t' (i + 1) (ops ++ [(a, b)]).
Proof.
  intros source target s t i ops s' t' a b
    Hstate Hcross Hprefix Hbound.
  unfold CrossSwap in Hcross.
  simpl in Hcross.
  destruct Hcross as [Ha [Hb [Hs' Ht']]].
  subst s' t'.
  unfold RepairState in *.
  destruct Hstate as
      [Hs [Ht [Holdprefix [Hperm [Heven [Htrace [Hop0 Hop1]]]]]]].
  pose proof
    (cross_swap_combined_permutation__repair_transitions s t a b Ha Hb)
    as Hswapperm.
  repeat split.
  - rewrite Zlength_replace_Znth__repair_transitions. exact Hs.
  - rewrite Zlength_replace_Znth__repair_transitions. exact Ht.
  - exact Hprefix.
  - eapply Permutation_trans; eauto.
  - eapply combined_even_permutation__repair_transitions; eauto.
  - eapply
      (swap_trace_append__repair_transitions
        source target s t ops _ _ (a, b)); try exact Htrace.
    unfold CrossSwap. simpl.
    split; [exact Ha |]. split; [exact Hb |]. split; reflexivity.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil.
    pose proof (Zlength_nonneg ops). lia.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.
Lemma repair_state_one_cross_swap__repair_transitions :
  forall source target s t i ops j,
    RepairState source target s t i ops ->
    Zlength s = Zlength t ->
    0 <= i < Zlength s ->
    i < j < Zlength s ->
    Znth j s 0 = Znth i s 0 ->
    RepairState source target
      (replace_Znth j (Znth i t 0) s)
      (replace_Znth i (Znth j s 0) t)
      (i + 1) (ops ++ [(j, i)]).
Proof.
  intros source target s t i ops j Hstate Hlen Hi Hj Hmatch.
  apply (repair_state_cross_swap__repair_transitions
    source target s t i ops
    (replace_Znth j (Znth i t 0) s)
    (replace_Znth i (Znth j s 0) t) j i); try assumption.
  - unfold CrossSwap. simpl. repeat split; try reflexivity; lia.
  - unfold PrefixEqual.
    intros k Hk.
    destruct (Z_lt_ge_dec k i).
    + rewrite !Znth_replace_Znth_Diff by lia.
      unfold RepairState in Hstate.
      destruct Hstate as [_ [_ [Hprefix _]]].
      apply Hprefix. lia.
    + assert (k = i) by lia. subst k.
      rewrite Znth_replace_Znth_Diff by lia.
      rewrite Znth_replace_Znth_Same by lia.
      symmetry. exact Hmatch.
  - unfold RepairState in Hstate.
    destruct Hstate as [_ [_ [_ [_ [_ [_ Hops]]]]]].
    lia.
Qed.
Lemma repair_state_two_cross_swaps__repair_transitions :
  forall source target s t i ops j,
    RepairState source target s t i ops ->
    Zlength s = Zlength t ->
    0 <= i < Zlength s ->
    i < j < Zlength s ->
    Znth j t 0 = Znth i s 0 ->
    RepairState source target
      (replace_Znth j
        (Znth i (replace_Znth j (Znth j s 0) t) 0)
        (replace_Znth j (Znth j t 0) s))
      (replace_Znth i
        (Znth j (replace_Znth j (Znth j t 0) s) 0)
        (replace_Znth j (Znth j s 0) t))
      (i + 1) ((ops ++ [(j, j)]) ++ [(j, i)]).
Proof.
  intros source target s t i ops j Hstate Hlen Hi Hj Hmatch.
  set (s1 := replace_Znth j (Znth j t 0) s).
  set (t1 := replace_Znth j (Znth j s 0) t).
  set (s2 := replace_Znth j (Znth i t1 0) s1).
  set (t2 := replace_Znth i (Znth j s1 0) t1).
  assert (Hj_t : 0 <= j < Zlength t) by lia.
  assert (Hcross1 : CrossSwap (s, t) (s1, t1) (j, j)).
  { unfold CrossSwap, s1, t1. simpl.
    split; [lia |]. split; [lia |]. split; reflexivity. }
  assert (Hlen_s1 : Zlength s1 = Zlength s).
  { unfold s1. apply Zlength_replace_Znth__repair_transitions. }
  assert (Hlen_t1 : Zlength t1 = Zlength t).
  { unfold t1. apply Zlength_replace_Znth__repair_transitions. }
  assert (Hcross2 : CrossSwap (s1, t1) (s2, t2) (j, i)).
  { unfold CrossSwap, s2, t2. simpl.
    split; [lia |]. split; [lia |]. split; reflexivity. }
  assert (Hperm1 : Permutation (s ++ t) (s1 ++ t1)).
  { unfold s1, t1.
    apply cross_swap_combined_permutation__repair_transitions; lia. }
  assert (Hperm2 : Permutation (s1 ++ t1) (s2 ++ t2)).
  { unfold s2, t2.
    apply cross_swap_combined_permutation__repair_transitions; lia. }
  assert (Hprefix2 : PrefixEqual s2 t2 (i + 1)).
  { unfold PrefixEqual.
    intros k Hk.
    destruct (Z_lt_ge_dec k i).
    - unfold s2.
      rewrite Znth_replace_Znth_Diff by
          (repeat rewrite Zlength_replace_Znth__repair_transitions; lia).
      unfold s1.
      rewrite Znth_replace_Znth_Diff by lia.
      unfold t2.
      rewrite Znth_replace_Znth_Diff by
          (repeat rewrite Zlength_replace_Znth__repair_transitions; lia).
      unfold t1.
      rewrite Znth_replace_Znth_Diff by lia.
      unfold RepairState in Hstate.
      destruct Hstate as [_ [_ [Hprefix _]]].
      apply Hprefix. lia.
    - assert (k = i) by lia. subst k.
      unfold s2.
      rewrite Znth_replace_Znth_Diff by
          (repeat rewrite Zlength_replace_Znth__repair_transitions; lia).
      unfold s1.
      rewrite Znth_replace_Znth_Diff by lia.
      unfold t2.
      rewrite Znth_replace_Znth_Same by
          (repeat rewrite Zlength_replace_Znth__repair_transitions; lia).
      unfold s1.
      rewrite Znth_replace_Znth_Same by lia.
      symmetry. exact Hmatch. }
  unfold s1, t1, s2, t2 in *.
  unfold RepairState in *.
  destruct Hstate as
      [Hs [Ht [Hprefix [Hperm [Heven [Htrace [Hop0 Hop1]]]]]]].
  repeat split.
  - rewrite Zlength_replace_Znth__repair_transitions.
    eapply eq_trans; [exact Hlen_s1 | exact Hs].
  - rewrite Zlength_replace_Znth__repair_transitions.
    eapply eq_trans; [exact Hlen_t1 | exact Ht].
  - exact Hprefix2.
  - eapply Permutation_trans; [exact Hperm |].
    eapply Permutation_trans; eauto.
  - eapply combined_even_permutation__repair_transitions.
    + eapply combined_even_permutation__repair_transitions; eauto.
    + exact Hperm2.
  - apply swap_trace_append__repair_transitions with
      (s := replace_Znth j (Znth j t 0) s)
      (t := replace_Znth j (Znth j s 0) t)
      (op := (j, i)).
    + apply swap_trace_append__repair_transitions with
        (s := s) (t := t) (op := (j, j)); assumption.
    + exact Hcross2.
  - rewrite !Zlength_app, !Zlength_cons, !Zlength_nil.
    pose proof (Zlength_nonneg ops). lia.
  - rewrite !Zlength_app, !Zlength_cons, !Zlength_nil. lia.
Qed.
Lemma replace_Znth_decompose__final_results :
  forall (l : list Z) i v d,
    0 <= i < Zlength l ->
    exists pre suf,
      l = pre ++ Znth i l d :: suf /\
      replace_Znth i v l = pre ++ v :: suf.
Proof.
  induction l as [|a l IH]; intros i v d Hi.
  - rewrite Zlength_nil in Hi. lia.
  - rewrite Zlength_cons in Hi.
    destruct (Z.eq_dec i 0) as [->|Hnz].
    + exists [], l. simpl. split; reflexivity.
    + assert (0 < i) by lia.
      specialize (IH (i - 1) v d ltac:(lia)).
      destruct IH as (pre & suf & Hl & Hreplace).
      exists (a :: pre), suf.
      rewrite Znth_cons by lia.
      rewrite replace_Znth_cons by lia.
      simpl. split.
      * now f_equal.
      * now f_equal.
Qed.
Lemma cross_swap_preserves_count__final_results :
  forall st st' op x,
    CrossSwap st st' op ->
    count_occ Z.eq_dec (fst st ++ snd st) x =
    count_occ Z.eq_dec (fst st' ++ snd st') x.
Proof.
  intros [s t] [s' t'] [i j] x Hswap.
  unfold CrossSwap in Hswap; simpl in Hswap.
  destruct Hswap as (Hi & Hj & -> & ->).
  set (a := Znth i s 0) in *.
  set (b := Znth j t 0) in *.
  destruct (replace_Znth_decompose__final_results s i b 0 Hi)
    as (sp & ss & Hs & Hs').
  destruct (replace_Znth_decompose__final_results t j a 0 Hj)
    as (tp & ts & Ht & Ht').
  change (s = sp ++ a :: ss) in Hs.
  change (t = tp ++ b :: ts) in Ht.
  assert (Hperm :
    Permutation (s ++ t)
      (replace_Znth i b s ++ replace_Znth j a t)).
  {
    rewrite Hs', Ht', Hs, Ht.
    repeat rewrite <- app_assoc.
    apply (Permutation_app_head sp).
    rewrite !app_assoc.
    change
      (Permutation
        (a :: (ss ++ tp) ++ b :: ts)
        (b :: (ss ++ tp) ++ a :: ts)).
    eapply Permutation_trans.
    - apply perm_skip. apply Permutation_sym. apply Permutation_middle.
    - eapply Permutation_trans.
      + apply perm_swap.
      + apply perm_skip. apply Permutation_middle.
  }
  exact ((proj1 (Permutation_count_occ Z.eq_dec _ _)) Hperm x).
Qed.
Lemma trace_prefix_preserves_count__final_results :
  forall states ops q x,
    (forall k, 0 <= k < Zlength ops ->
      CrossSwap
        (Znth k states ([], []))
        (Znth (k + 1) states ([], []))
        (Znth k ops (0, 0))) ->
    0 <= q <= Zlength ops ->
    count_occ Z.eq_dec
      (fst (Znth 0 states ([], [])) ++ snd (Znth 0 states ([], []))) x =
    count_occ Z.eq_dec
      (fst (Znth q states ([], [])) ++ snd (Znth q states ([], []))) x.
Proof.
  intros states ops q x Hstep Hq.
  remember (Z.to_nat q) as n eqn:Hn.
  revert q Hn Hq.
  induction n as [|n IH]; intros q Hn Hq.
  - assert (q = 0) by (apply Z2Nat.inj; simpl; lia).
    subst q. reflexivity.
  - assert (Hqeq : q = Z.of_nat (S n)) by
      (apply Z2Nat.inj; simpl; lia).
    specialize (IH (Z.of_nat n) ltac:(rewrite Nat2Z.id; reflexivity) ltac:(lia)).
    rewrite Hqeq.
    eapply eq_trans; [exact IH|].
    replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia.
    apply (cross_swap_preserves_count__final_results
      (Znth (Z.of_nat n) states ([], []))
      (Znth (Z.of_nat n + 1) states ([], []))
      (Znth (Z.of_nat n) ops (0, 0)) x).
    apply Hstep. lia.
Qed.
Lemma swap_trace_preserves_count__final_results :
  forall s0 t0 s t ops x,
    SwapTrace s0 t0 s t ops ->
    count_occ Z.eq_dec (s0 ++ t0) x =
    count_occ Z.eq_dec (s ++ t) x.
Proof.
  intros s0 t0 s t ops x Htrace.
  unfold SwapTrace in Htrace.
  destruct Htrace as (states & Hlen & Hstart & Hstep & Hend).
  pose proof
    (trace_prefix_preserves_count__final_results
      states ops (Zlength ops) x Hstep
      ltac:(pose proof (Zlength_nonneg ops); lia)) as Hcount.
  rewrite Hstart, Hend in Hcount. simpl in Hcount.
  exact Hcount.
Qed.
Lemma combined_odd_forbids_swaps_work__final_results :
  forall s t c ops,
    CombinedOddAt s t c ->
    ~ SwapsWork s t ops.
Proof.
  intros s t c ops Hodd Hwork.
  unfold CombinedOddAt in Hodd.
  destruct Hodd as (Hc & Hodd).
  unfold SwapsWork in Hwork.
  destruct Hwork as (Hbounds & states & Hlen & Hstart & Hstep & Hfinal).
  set (last := Znth (Zlength ops) states ([], [])).
  change (fst last = snd last) in Hfinal.
  assert (Htrace : SwapTrace s t (fst last) (snd last) ops).
  {
    unfold SwapTrace. exists states.
    repeat split; try assumption.
    unfold last. destruct (Znth (Zlength ops) states ([], [])).
    reflexivity.
  }
  pose proof
    (swap_trace_preserves_count__final_results
      s t (fst last) (snd last) ops (97 + c) Htrace) as Hcount.
  rewrite Hfinal in Hcount.
  rewrite count_occ_app in Hcount.
  rewrite count_occ_app in Hodd.
  rewrite Hcount in Hodd.
  rewrite count_occ_app in Hodd.
  rewrite Nat2Z.inj_add in Hodd.
  replace
    (Z.of_nat (count_occ Z.eq_dec (snd last) (97 + c)) +
     Z.of_nat (count_occ Z.eq_dec (snd last) (97 + c)))
    with
    (2 * Z.of_nat (count_occ Z.eq_dec (snd last) (97 + c)))
    in Hodd by lia.
  rewrite Z.mul_comm in Hodd.
  rewrite Z.mod_mul in Hodd by lia.
  lia.
Qed.
Lemma prefix_equal_full__final_results :
  forall s t i,
    Zlength s = Zlength t ->
    Zlength s <= i ->
    PrefixEqual s t i ->
    s = t.
Proof.
  intros s t i Hlen Hi Hprefix.
  apply (nth_ext s t 0 0).
  - rewrite !Zlength_correct in Hlen. lia.
  - intros n Hn.
    specialize (Hprefix (Z.of_nat n) ltac:(rewrite Zlength_correct in Hi; lia)).
    unfold Znth in Hprefix.
    now rewrite Nat2Z.id in Hprefix.
Qed.
Lemma repair_state_success_swaps_work__final_results :
  forall source target s t i ops,
    source <> target ->
    Zlength source = Zlength target ->
    i = Zlength source ->
    RepairState source target s t i ops ->
    SwapsWork source target ops.
Proof.
  intros source target s t i ops Hneq Hsource_target Hi Hrepair.
  unfold RepairState in Hrepair.
  destruct Hrepair as
    (Hslen & Htlen & Hprefix & Hperm & Heven & Htrace & Hops).
  assert (Hst : s = t).
  {
    apply (prefix_equal_full__final_results s t i).
    - lia.
    - lia.
    - exact Hprefix.
  }
  unfold SwapTrace in Htrace.
  destruct Htrace as (states & Hstates_len & Hstart & Hstep & Hend).
  assert (Hops_nonzero : Zlength ops <> 0).
  {
    intro Hzero.
    apply Hneq.
    assert (Hpairs : (source, target) = (s, t)).
    {
      rewrite <- Hstart, <- Hend, Hzero. reflexivity.
    }
    inversion Hpairs. congruence.
  }
  unfold SwapsWork.
  split.
  - lia.
  - exists states. repeat split; try assumption.
    rewrite Hend. simpl. exact Hst.
Qed.
Lemma no_value_full_count_zero__final_results :
  forall l v,
    NoValueInRange l v 0 (Zlength l) ->
    count_occ Z.eq_dec l v = 0%nat.
Proof.
  intros l v Hnone.
  apply (proj1 (count_occ_not_In Z.eq_dec l v)).
  intro Hin.
  destruct (In_nth l v 0 Hin) as (n & Hn & Hnth).
  specialize (Hnone (Z.of_nat n) ltac:(rewrite Zlength_correct; lia)).
  apply Hnone.
  unfold Znth. now rewrite Nat2Z.id.
Qed.
Lemma paired_prefix_unmatched_count_odd__final_results :
  forall s t i v,
    Zlength s = Zlength t ->
    0 <= i < Zlength s ->
    PrefixEqual s t i ->
    Znth i s 0 = v ->
    Znth i t 0 <> v ->
    NoValueInRange s v (i + 1) (Zlength s) ->
    NoValueInRange t v (i + 1) (Zlength t) ->
    exists k : nat,
      count_occ Z.eq_dec (s ++ t) v = (2 * k + 1)%nat.
Proof.
  induction s as [|a s IH]; intros t i v Hlen Hi Hprefix Hsi Hti Hsuf Htuf.
  - rewrite Zlength_nil in Hi. lia.
  - destruct t as [|b t].
    + rewrite Zlength_nil, Zlength_cons in Hlen.
      pose proof (Zlength_nonneg s). lia.
    + rewrite !Zlength_cons in Hlen, Hi.
      destruct (Z.eq_dec i 0) as [->|Hine].
      * rewrite !Znth0_cons in Hsi, Hti.
        subst a.
        assert (Hsnone : NoValueInRange s v 0 (Zlength s)).
        {
          unfold NoValueInRange in *.
          intros k Hk.
          specialize (Hsuf (k + 1) ltac:(rewrite Zlength_cons; lia)).
          rewrite Znth_cons in Hsuf by lia.
          replace (k + 1 - 1) with k in Hsuf by lia. exact Hsuf.
        }
        assert (Htnone : NoValueInRange t v 0 (Zlength t)).
        {
          unfold NoValueInRange in *.
          intros k Hk.
          specialize (Htuf (k + 1) ltac:(rewrite Zlength_cons; lia)).
          rewrite Znth_cons in Htuf by lia.
          replace (k + 1 - 1) with k in Htuf by lia. exact Htuf.
        }
        pose proof (no_value_full_count_zero__final_results s v Hsnone) as Hscount.
        pose proof (no_value_full_count_zero__final_results t v Htnone) as Htcount.
        exists 0%nat.
        rewrite count_occ_app. simpl.
        destruct (Z.eq_dec v v); [|contradiction].
        destruct (Z.eq_dec b v); [contradiction|].
        lia.
      * assert (0 < i) by lia.
        assert (Hlen_tail : Zlength s = Zlength t).
        { rewrite Zlength_cons in Hlen. lia. }
        assert (Hab : a = b).
        {
          specialize (Hprefix 0 ltac:(lia)).
          now rewrite !Znth0_cons in Hprefix.
        }
        subst b.
        assert (Hprefix_tail : PrefixEqual s t (i - 1)).
        {
          unfold PrefixEqual in *.
          intros k Hk.
          specialize (Hprefix (k + 1) ltac:(lia)).
          rewrite !Znth_cons in Hprefix by lia.
          replace (k + 1 - 1) with k in Hprefix by lia. exact Hprefix.
        }
        assert (Hsuf_tail : NoValueInRange s v i (Zlength s)).
        {
          unfold NoValueInRange in *.
          intros k Hk.
          specialize (Hsuf (k + 1) ltac:(rewrite Zlength_cons; lia)).
          rewrite Znth_cons in Hsuf by lia.
          replace (k + 1 - 1) with k in Hsuf by lia. exact Hsuf.
        }
        assert (Htuf_tail : NoValueInRange t v i (Zlength t)).
        {
          unfold NoValueInRange in *.
          intros k Hk.
          specialize (Htuf (k + 1) ltac:(rewrite Zlength_cons; lia)).
          rewrite Znth_cons in Htuf by lia.
          replace (k + 1 - 1) with k in Htuf by lia. exact Htuf.
        }
        rewrite Znth_cons in Hsi, Hti by lia.
        destruct
          (IH t (i - 1) v Hlen_tail ltac:(lia)
            Hprefix_tail Hsi Hti
            ltac:(replace (i - 1 + 1) with i by lia; exact Hsuf_tail)
            ltac:(replace (i - 1 + 1) with i by lia; exact Htuf_tail))
          as (k & Hcount).
        rewrite count_occ_app. simpl.
        rewrite count_occ_app in Hcount.
        destruct (Z.eq_dec a v).
        -- exists (S k). lia.
        -- exists k. lia.
Qed.
Lemma no_match_contradicts_combined_even__final_results :
  forall s t i v,
    Zlength s = Zlength t ->
    0 <= i < Zlength s ->
    97 <= v <= 122 ->
    PrefixEqual s t i ->
    Znth i s 0 = v ->
    Znth i t 0 <> v ->
    NoValueInRange s v (i + 1) (Zlength s) ->
    NoValueInRange t v (i + 1) (Zlength t) ->
    ~ CombinedEven s t.
Proof.
  intros s t i v Hlen Hi Hv Hprefix Hsi Hti Hsuf Htuf Heven.
  destruct
    (paired_prefix_unmatched_count_odd__final_results
      s t i v Hlen Hi Hprefix Hsi Hti Hsuf Htuf)
    as (k & Hcount).
  specialize (Heven (v - 97) ltac:(lia)).
  replace (97 + (v - 97)) with v in Heven by lia.
  rewrite Hcount in Heven.
  rewrite Nat2Z.inj_add, Nat2Z.inj_mul in Heven.
  change ((2 * Z.of_nat k + 1) mod 2 = 0) in Heven.
  assert (Harith : 2 * Z.of_nat k + 1 = 1 + Z.of_nat k * 2).
  { lia. }
  assert (Hmod : (2 * Z.of_nat k + 1) mod 2 = 1).
  {
    rewrite Harith.
    rewrite (Z_mod_plus 1 (Z.of_nat k) 2 ltac:(lia)).
    reflexivity.
  }
  lia.
Qed.
