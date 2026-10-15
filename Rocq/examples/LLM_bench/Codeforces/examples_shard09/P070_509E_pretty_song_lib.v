Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope R_scope.

Definition Vowel (c : Z) : Prop := c = 73%Z \/ c = 69%Z \/ c = 65%Z \/ c = 79%Z \/ c = 85%Z \/ c = 89%Z.
Definition Pre (s : list Z) : Prop :=
  (* Stated explicitly in the P070 solver Require, so dropped here:
       (1 <= Zlength s <= 500000)%Z /\
       Forall (fun c => (65 <= c <= 90)%Z) s  *)
  True.

Definition Spec (s : list Z) (out : R) : Prop :=
  out = sum_range_R 0%Z (Zlength s - 1)%Z (fun i =>
    sum_range_R i (Zlength s - 1)%Z (fun j =>
      IZR (#(fun q : Z => (i <= q < j + 1)%Z /\ Vowel (Znth q s 0%Z))) / IZR ((j - i + 1)%Z))).

(* Representation helpers for the P070 solver contract. *)
Definition PrettyTerm (s : list Z) (len : Z) : Z :=
  sum_range 0 (Zlength s - len) (fun i =>
    #(fun q : Z => (i <= q < i + len)%Z /\ Vowel (Znth q s 0%Z))).

(* The table of those totals, one per length. *)
Definition PrettyTermTable (s terms : list Z) : Prop :=
  Zlength terms = Zlength s /\
  forall len, (1 <= len <= Zlength s)%Z ->
    Znth (len - 1)%Z terms 0%Z = PrettyTerm s len.

Definition PrettyTerms (s terms : list Z) (out : R) : Prop :=
  PrettyTermTable s terms /\
  out = sum_range_R 1 (Zlength s) (fun len =>
          Rdiv (IZR (Znth (len - 1)%Z terms 0%Z)) (IZR len)).

(* Internal annotation predicates.  Array lengths, machine bounds and spatial
   ownership stay explicit in the C invariants. *)
Definition VowelPrefixCounts (s counts : list Z) : Prop :=
  forall k, (0 <= k < Zlength counts)%Z ->
    Znth k counts 0%Z =
      #(fun q : Z => (0 <= q < k)%Z /\ Vowel (Znth q s 0%Z)).

Definition PrefixCountTotals (counts totals : list Z) : Prop :=
  forall k, (0 <= k < Zlength totals)%Z ->
    Znth k totals 0%Z =
      sum_range 0 k (fun q => Znth q counts 0%Z).

Definition PrettyTermPrefix (s terms : list Z) : Prop :=
  forall len, (1 <= len <= Zlength terms)%Z ->
    Znth (len - 1)%Z terms 0%Z = PrettyTerm s len.

(* Begin the append-only proof/dependency area after the frozen declarations. *)
Lemma generated_goal_real_scope_separator : True.
Proof. exact I. Qed.

(* Export the real-number surface needed by the generated return witness. *)
Require Export Coq.Reals.Reals.

Require Import Coq.micromega.Lia.
Lemma set_card_empty__prefix_init_exit :
  forall {A : Type} (P : A -> Prop) (FP : Finite P),
    (forall x, ~ P x) -> @set_card A P FP = 0%Z.
Proof.
  intros A P FP Hempty.
  unfold set_card, SumLib.Sum.sum.
  destruct (@enum A P FP) as [|x xs] eqn:Hen; [reflexivity |].
  exfalso.
  apply (Hempty x).
  apply (proj2 (@enum_ok A P FP x)).
  rewrite Hen. simpl. auto.
Qed.
Lemma vowel_prefix_counts_single_zero__prefix_init_exit :
  forall s, VowelPrefixCounts s ((0%Z) :: nil).
Proof.
  intros s k Hk.
  rewrite Zlength_cons, Zlength_nil in Hk.
  assert (k = 0%Z) by lia. subst k.
  simpl.
  symmetry.
  apply set_card_empty__prefix_init_exit.
  intros q [Hq _]. lia.
Qed.
Lemma set_card_Z_as_sum__prefix_vowel_append :
  forall (low high : Z) (P : Z -> Prop),
    #(fun i : Z => (low <= i < high)%Z /\ P i) =
    SumLib.Sum.sum (fun i : Z => (low <= i < high)%Z)
      (fun i => if prop_dec (P i) then 1%Z else 0%Z).
Proof.
  intros low high P.
  unfold set_card, SumLib.Sum.sum.
  cbn [finite_Z_range' finite_Z_range].
  assert (Hfilter : forall xs : list Z,
    fold_right (fun _ acc : Z => (1 + acc)%Z) 0%Z
      (filter (fun i => if prop_dec (P i) then true else false) xs) =
    fold_right (fun i acc : Z =>
      ((if prop_dec (P i) then 1%Z else 0%Z) + acc)%Z) 0%Z xs).
  {
    induction xs as [|i xs IH]; simpl; [reflexivity |].
    destruct (prop_dec (P i)); simpl.
    - exact (f_equal (fun n : Z => (1 + n)%Z) IH).
    - exact IH.
  }
  apply Hfilter.
Qed.
Lemma set_card_Z_extend_true__prefix_vowel_append :
  forall (i : Z) (P : Z -> Prop),
    (0 <= i)%Z ->
    P i ->
    #(fun q : Z => (0 <= q < i + 1)%Z /\ P q) =
      (#(fun q : Z => (0 <= q < i)%Z /\ P q) + 1)%Z.
Proof.
  intros i P Hi HP.
  rewrite !set_card_Z_as_sum__prefix_vowel_append.
  rewrite SumLib.ZRange.sum_Z_range_extend_right by exact Hi.
  destruct (prop_dec (P i)); [lia | contradiction].
Qed.
Lemma vowel_prefix_counts_extend_vowel__prefix_vowel_append :
  forall (s counts : list Z) (i : Z),
    (Zlength counts = i + 1)%Z ->
    (0 <= i)%Z ->
    VowelPrefixCounts s counts ->
    Vowel (Znth i s 0%Z) ->
    VowelPrefixCounts s (counts ++ [(Znth i counts 0%Z + 1)%Z]).
Proof.
  intros s counts i Hlen Hi Hprefix Hvowel.
  unfold VowelPrefixCounts in *.
  intros k Hk.
  rewrite Zlength_app, Zlength_cons, Zlength_nil in Hk.
  destruct (Z_lt_ge_dec k (i + 1)%Z) as [Hlt | Hge].
  - rewrite app_Znth1 by lia.
    apply Hprefix. lia.
  - assert (Hki : k = (i + 1)%Z) by lia.
    subst k.
    rewrite app_Znth2 by lia.
    replace (i + 1 - Zlength counts)%Z with 0%Z by lia.
    rewrite Znth0_cons.
    rewrite (Hprefix i) by lia.
    rewrite set_card_Z_extend_true__prefix_vowel_append by assumption.
    reflexivity.
Qed.
Lemma prefix_count_bounds_extend__prefix_vowel_append :
  forall (counts : list Z) (i : Z),
    (Zlength counts = i + 1)%Z ->
    (0 <= i)%Z ->
    (forall k, (0 <= k < i + 1)%Z ->
      (0 <= Znth k counts 0%Z <= k)%Z) ->
    forall k, (0 <= k < (i + 1) + 1)%Z ->
      (0 <= Znth k (counts ++ [(Znth i counts 0%Z + 1)%Z]) 0%Z <= k)%Z.
Proof.
  intros counts i Hlen Hi Hbounds k Hk.
  destruct (Z_lt_ge_dec k (i + 1)%Z) as [Hlt | Hge].
  - rewrite app_Znth1 by lia.
    apply Hbounds. lia.
  - assert (Hki : k = (i + 1)%Z) by lia.
    subst k.
    rewrite app_Znth2 by lia.
    replace (i + 1 - Zlength counts)%Z with 0%Z by lia.
    rewrite Znth0_cons.
    pose proof (Hbounds i ltac:(lia)).
    lia.
Qed.
Lemma replace_Znth_app_last__prefix_vowel_append :
  forall (prefix : list Z) (old value : Z),
    replace_Znth (Zlength prefix) value (prefix ++ [old]) =
    prefix ++ [value].
Proof.
  intros prefix old value.
  rewrite replace_Znth_app_r by lia.
  rewrite replace_Znth_nothing by lia.
  replace (Zlength prefix - Zlength prefix)%Z with 0%Z by lia.
  reflexivity.
Qed.
Lemma set_card_Z_as_sum__prefix_nonvowel_append :
  forall (low high : Z) (P : Z -> Prop),
    #(fun q : Z => (low <= q < high)%Z /\ P q) =
    SumLib.Sum.sum (fun q : Z => (low <= q < high)%Z)
      (fun q => if prop_dec (P q) then 1%Z else 0%Z).
Proof.
  intros low high P.
  unfold set_card, SumLib.Sum.sum.
  cbn [finite_Z_range' finite_Z_range].
  assert (Hfilter : forall xs : list Z,
    fold_right (fun _ acc : Z => (1 + acc)%Z) 0%Z
      (filter (fun q => if prop_dec (P q) then true else false) xs) =
    fold_right (fun q acc : Z =>
      ((if prop_dec (P q) then 1%Z else 0%Z) + acc)%Z) 0%Z xs).
  {
    induction xs as [|q xs IH]; simpl; [reflexivity |].
    destruct (prop_dec (P q)); simpl.
    - exact (f_equal (fun n : Z => (1 + n)%Z) IH).
    - exact IH.
  }
  apply Hfilter.
Qed.
Lemma set_card_Z_extend_false__prefix_nonvowel_append :
  forall (i : Z) (P : Z -> Prop),
    (0 <= i)%Z ->
    ~ P i ->
    #(fun q : Z => (0 <= q < i + 1)%Z /\ P q) =
    #(fun q : Z => (0 <= q < i)%Z /\ P q).
Proof.
  intros i P Hi Hnot.
  rewrite !set_card_Z_as_sum__prefix_nonvowel_append.
  rewrite SumLib.ZRange.sum_Z_range_extend_right by exact Hi.
  destruct (prop_dec (P i)) as [HP | _]; [contradiction | lia].
Qed.
Lemma vowel_prefix_counts_extend_nonvowel__prefix_nonvowel_append :
  forall (s counts : list Z) (i : Z),
    (Zlength counts = i + 1)%Z ->
    (0 <= i)%Z ->
    VowelPrefixCounts s counts ->
    ~ Vowel (Znth i s 0%Z) ->
    VowelPrefixCounts s (counts ++ [Znth i counts 0%Z]).
Proof.
  intros s counts i Hlen Hi Hprefix Hnonvowel.
  unfold VowelPrefixCounts in *.
  intros k Hk.
  rewrite Zlength_app, Zlength_cons, Zlength_nil in Hk.
  destruct (Z_lt_dec k (Zlength counts)) as [Hkold | Hknew].
  - rewrite app_Znth1 by lia.
    apply Hprefix. lia.
  - assert (Hkeq : k = (i + 1)%Z) by lia.
    subst k.
    rewrite app_Znth2 by lia.
    replace (i + 1 - Zlength counts)%Z with 0%Z by lia.
    rewrite Znth0_cons.
    rewrite Hprefix by lia.
    symmetry.
    apply set_card_Z_extend_false__prefix_nonvowel_append; assumption.
Qed.
Lemma replace_Znth_app_last__prefix_nonvowel_append :
  forall (prefix : list Z) old value,
    replace_Znth (Zlength prefix) value (prefix ++ [old]) =
    prefix ++ [value].
Proof.
  intros prefix old value.
  rewrite replace_Znth_app_r by lia.
  rewrite replace_Znth_nothing by lia.
  replace (Zlength prefix - Zlength prefix)%Z with 0%Z by lia.
  reflexivity.
Qed.
Lemma prefix_count_bounds_extend_nonvowel__prefix_nonvowel_append :
  forall (counts : list Z) (i : Z),
    (0 <= i)%Z ->
    (Zlength counts = i + 1)%Z ->
    (forall k, (0 <= k < i + 1)%Z ->
      (0 <= Znth k counts 0 <= k)%Z) ->
    forall k, (0 <= k < (i + 1) + 1)%Z ->
      (0 <= Znth k (counts ++ [Znth i counts 0]) 0 <= k)%Z.
Proof.
  intros counts i Hi Hlen Hbounds k Hk.
  destruct (Z_lt_dec k (Zlength counts)) as [Hkold | Hknew].
  - rewrite app_Znth1 by lia.
    apply Hbounds. lia.
  - assert (Hkeq : k = (i + 1)%Z) by lia.
    subst k.
    rewrite app_Znth2 by lia.
    replace (i + 1 - Zlength counts)%Z with 0%Z by lia.
    rewrite Znth0_cons.
    specialize (Hbounds i ltac:(lia)).
    lia.
Qed.
Lemma prefix_count_totals_init__prefix_totals :
  forall counts,
    PrefixCountTotals counts [Znth 0%Z counts 0%Z].
Proof.
  intros counts.
  unfold PrefixCountTotals.
  intros k Hk.
  rewrite Zlength_cons, Zlength_nil in Hk.
  assert (k = 0%Z) by lia.
  subst k.
  simpl.
  unfold sum_range.
  rewrite SumLib.ZRange.sum_Z_range_single.
  reflexivity.
Qed.
Lemma sum_range_succ__prefix_totals :
  forall (i : Z) (f : Z -> Z),
    (0 <= i)%Z ->
    sum_range 0%Z i f =
      (sum_range 0%Z (i - 1)%Z f + f i)%Z.
Proof.
  intros i f Hi.
  unfold sum_range.
  replace (i - 1 + 1)%Z with i by lia.
  rewrite SumLib.ZRange.sum_Z_range_extend_right by lia.
  reflexivity.
Qed.
Lemma replace_Znth_app_last__prefix_totals :
  forall (xs : list Z) old value,
    replace_Znth (Zlength xs) value (xs ++ old :: nil) =
    xs ++ value :: nil.
Proof.
  intros xs old value.
  rewrite replace_Znth_app_r by lia.
  rewrite replace_Znth_nothing by lia.
  replace (Zlength xs - Zlength xs)%Z with 0%Z by lia.
  reflexivity.
Qed.
Lemma triangular_step__prefix_totals :
  forall i : Z,
    (1 <= i)%Z ->
    (Z.quot ((i - 1) * i) 2 + i = Z.quot (i * (i + 1)) 2)%Z.
Proof.
  intros i Hi.
  rewrite !Z.quot_div_nonneg by nia.
  replace (i * (i + 1))%Z with ((i - 1) * i + i * 2)%Z by ring.
  rewrite Z.div_add by lia.
  ring.
Qed.
Lemma prefix_count_totals_extend__prefix_totals :
  forall (counts totals : list Z) (i : Z),
    (1 <= i)%Z ->
    (i < Zlength counts)%Z ->
    Zlength totals = i ->
    (forall k, (0 <= k < Zlength counts)%Z ->
      (0 <= Znth k counts 0%Z <= k)%Z) ->
    (forall k, (0 <= k < i)%Z ->
      (0 <= Znth k totals 0%Z <= Z.quot (k * (k + 1)) 2)%Z) ->
    PrefixCountTotals counts totals ->
    let totals' := totals ++
      (Znth (i - 1)%Z totals 0%Z + Znth i counts 0%Z)%Z :: nil in
    PrefixCountTotals counts totals' /\
    (forall k, (0 <= k < i + 1)%Z ->
      (0 <= Znth k totals' 0%Z <= Z.quot (k * (k + 1)) 2)%Z).
Proof.
  intros counts totals i Hi Hicounts Hlen Hcounts Hbounds Htotals.
  cbn zeta.
  split.
  - unfold PrefixCountTotals in *.
    intros k Hk.
    rewrite Zlength_app, Zlength_cons, Zlength_nil in Hk.
    destruct (Z_lt_ge_dec k (Zlength totals)) as [Hkold | Hklast].
    + rewrite app_Znth1 by lia.
      apply Htotals. lia.
    + assert (k = i) by lia.
      subst k.
      rewrite app_Znth2 by lia.
      replace (i - Zlength totals)%Z with 0%Z by lia.
      rewrite Znth0_cons.
      rewrite Htotals with (k := (i - 1)%Z) by lia.
      symmetry.
      exact (sum_range_succ__prefix_totals i
        (fun q : Z => Znth q counts 0%Z) ltac:(lia)).
  - intros k Hk.
    destruct (Z_lt_ge_dec k (Zlength totals)) as [Hkold | Hklast].
    + rewrite app_Znth1 by lia.
      apply Hbounds. lia.
    + assert (k = i) by lia.
      subst k.
      rewrite app_Znth2 by lia.
      replace (i - Zlength totals)%Z with 0%Z by lia.
      rewrite Znth0_cons.
      specialize (Hbounds (i - 1)%Z ltac:(lia)).
      specialize (Hcounts i ltac:(lia)).
      replace (i - 1 + 1)%Z with i in Hbounds by lia.
      rewrite <- triangular_step__prefix_totals by exact Hi.
      nia.
Qed.
Lemma set_card_Z_as_sum__pretty_terms :
  forall (low high : Z) (P : Z -> Prop),
    #(fun z : Z => (low <= z < high)%Z /\ P z) =
    SumLib.Sum.sum (fun z : Z => (low <= z < high)%Z)
      (fun z => if prop_dec (P z) then 1%Z else 0%Z).
Proof.
  intros low high P.
  unfold set_card, SumLib.Sum.sum.
  cbn [finite_Z_range' finite_Z_range].
  assert (Hfilter : forall zs : list Z,
    fold_right (fun _ acc : Z => (1 + acc)%Z) 0%Z
      (filter (fun z => if prop_dec (P z) then true else false) zs) =
    fold_right (fun z acc : Z =>
      ((if prop_dec (P z) then 1%Z else 0%Z) + acc)%Z) 0%Z zs).
  {
    induction zs as [|z zs IH]; simpl; [reflexivity |].
    destruct (prop_dec (P z)); simpl.
    - exact (f_equal (fun n : Z => (1 + n)%Z) IH).
    - exact IH.
  }
  apply Hfilter.
Qed.
Lemma vowel_window_from_prefix__pretty_terms :
  forall (s counts : list Z) (start len : Z),
    (0 <= start)%Z -> (0 <= len)%Z ->
    (start + len < Zlength counts)%Z ->
    VowelPrefixCounts s counts ->
    #(fun q : Z => (start <= q < start + len)%Z /\ Vowel (Znth q s 0%Z)) =
    (Znth (start + len) counts 0%Z - Znth start counts 0%Z)%Z.
Proof.
  intros s counts start len Hstart Hlen Hend Hprefix.
  unfold VowelPrefixCounts in Hprefix.
  rewrite Hprefix by lia.
  rewrite Hprefix by lia.
  rewrite !set_card_Z_as_sum__pretty_terms.
  rewrite (SumLib.ZRange.sum_Z_range_split 0 start (start + len)) by lia.
  ring.
Qed.
Lemma pretty_term_from_prefix_totals__pretty_terms :
  forall (s counts totals : list Z) (n len : Z),
    Zlength s = n ->
    Zlength counts = (n + 1)%Z ->
    Zlength totals = (n + 1)%Z ->
    (1 <= len <= n)%Z ->
    VowelPrefixCounts s counts ->
    PrefixCountTotals counts totals ->
    (Znth n totals 0%Z - Znth (len - 1) totals 0%Z -
      Znth (n - len) totals 0%Z)%Z = PrettyTerm s len.
Proof.
  intros s counts totals n len Hs Hcounts Htotals Hlen Hprefix Htot.
  unfold PrefixCountTotals in Htot.
  rewrite Htot by lia.
  rewrite Htot by lia.
  rewrite Htot by lia.
  unfold PrettyTerm. rewrite Hs. unfold sum_range.
  rewrite (SumLib.ZRange.sum_Z_range_ext 0 (n - len + 1)
    (fun i => #(fun q : Z => (i <= q < i + len)%Z /\ Vowel (Znth q s 0%Z)))
    (fun i => (Znth (i + len) counts 0%Z - Znth i counts 0%Z)%Z)).
  2:{ intros i Hi. apply vowel_window_from_prefix__pretty_terms;
      [lia | lia | lia | exact Hprefix]. }
  rewrite SumLib.ZRange.sum_Z_range_sub.
  pose proof (SumLib.ZRange.sum_Z_range_shift 0 (n - len + 1) len
    (fun q => Znth q counts 0%Z)) as Hshift.
  replace (0 + len)%Z with len in Hshift by lia.
  replace (n - len + 1 + len)%Z with (n + 1)%Z in Hshift by lia.
  rewrite <- Hshift.
  rewrite (SumLib.ZRange.sum_Z_range_split 0 len (n + 1)) by lia.
  replace (len - 1 + 1)%Z with len by lia.
  ring.
Qed.
Lemma pretty_term_bounds__pretty_terms :
  forall (s : list Z) (n len : Z),
    Zlength s = n ->
    (1 <= len <= n)%Z ->
    (0 <= PrettyTerm s len <= n * n)%Z.
Proof.
  intros s n len Hs Hlen.
  unfold PrettyTerm. rewrite Hs. unfold sum_range.
  assert (Hwindow : forall i,
    (0 <= i < n - len + 1)%Z ->
    (0 <= #(fun q : Z => (i <= q < i + len)%Z /\ Vowel (Znth q s 0%Z)) <= len)%Z).
  {
    intros i Hi.
    rewrite set_card_Z_as_sum__pretty_terms.
    pose proof (SumLib.ZRange.sum_Z_range_bounds i (i + len)
      (fun q => if prop_dec (Vowel (Znth q s 0%Z)) then 1%Z else 0%Z)
      0 1 ltac:(lia)) as Hbounds.
    assert (Hindicator : forall q,
      (i <= q < i + len)%Z ->
      (0 <= (if prop_dec (Vowel (Znth q s 0%Z)) then 1%Z else 0%Z) <= 1)%Z).
    {
      intros q Hq.
      destruct (prop_dec (Vowel (Znth q s 0%Z))); simpl; lia.
    }
    specialize (Hbounds Hindicator).
    nia.
  }
  pose proof (SumLib.ZRange.sum_Z_range_bounds 0 (n - len + 1)
    (fun i => #(fun q : Z => (i <= q < i + len)%Z /\ Vowel (Znth q s 0%Z)))
    0 len ltac:(lia) Hwindow) as Houter.
  nia.
Qed.
Lemma pretty_term_prefix_extend__pretty_terms :
  forall (s terms : list Z) (len value : Z),
    Zlength terms = (len - 1)%Z ->
    PrettyTermPrefix s terms ->
    value = PrettyTerm s len ->
    PrettyTermPrefix s (terms ++ value :: nil).
Proof.
  intros s terms len value Hlength Hprefix Hvalue.
  unfold PrettyTermPrefix in *.
  intros k Hk.
  rewrite Zlength_app, Zlength_cons, Zlength_nil in Hk.
  destruct (Z_lt_ge_dec k len) as [Hlt | Hge].
  - rewrite app_Znth1 by lia.
    apply Hprefix. lia.
  - assert (k = len) by lia. subst k.
    rewrite app_Znth2 by lia.
    replace (len - 1 - Zlength terms)%Z with 0%Z by lia.
    rewrite Znth0_cons.
    exact Hvalue.
Qed.
Lemma NoDup_map_inj__final_result :
  forall {A B : Type} (f : A -> B) xs,
    (forall x y, In x xs -> In y xs -> f x = f y -> x = y) ->
    NoDup xs -> NoDup (map f xs).
Proof.
  intros A B f xs Hinj Hnd.
  induction Hnd as [|x xs Hnotin Hnd IH]; simpl.
  - constructor.
  - constructor.
    + intro Hin.
      apply in_map_iff in Hin as [y [Heq Hy]].
      apply Hnotin.
      assert (x = y).
      { apply (Hinj x y).
        - left. reflexivity.
        - right. exact Hy.
        - symmetry. exact Heq. }
      subst y. exact Hy.
    + apply IH.
      intros u v Hu Hv Heq.
      apply (Hinj u v).
      * right. exact Hu.
      * right. exact Hv.
      * exact Heq.
Qed.
Lemma NoDup_flat_map_indexed__final_result :
  forall {A B C : Type} (xs : list A) (ys : A -> list B)
         (f : A -> B -> C),
    NoDup xs ->
    (forall x, In x xs -> NoDup (ys x)) ->
    (forall x y1 y2, In x xs -> In y1 (ys x) -> In y2 (ys x) ->
       f x y1 = f x y2 -> y1 = y2) ->
    (forall x1 x2 y1 y2,
       In x1 xs -> In x2 xs -> x1 <> x2 ->
       In y1 (ys x1) -> In y2 (ys x2) -> f x1 y1 <> f x2 y2) ->
    NoDup (flat_map (fun x => map (f x) (ys x)) xs).
Proof.
  intros A B C xs ys f Hnd Hys Hinj Hdisj.
  induction Hnd as [|x xs Hnotin Hnd IH]; simpl.
  - constructor.
  - apply NoDup_app.
    + apply NoDup_map_inj__final_result.
      * intros y1 y2 Hy1 Hy2 Heq.
        apply (Hinj x y1 y2).
        -- left. reflexivity.
        -- exact Hy1.
        -- exact Hy2.
        -- exact Heq.
      * apply Hys. left. reflexivity.
    + apply IH.
      * intros x' Hx'. apply Hys. right. exact Hx'.
      * intros x' y1 y2 Hx' Hy1 Hy2 Heq.
        apply (Hinj x' y1 y2).
        -- right. exact Hx'.
        -- exact Hy1.
        -- exact Hy2.
        -- exact Heq.
      * intros x1 x2 y1 y2 Hx1 Hx2 Hneq Hy1 Hy2.
        apply (Hdisj x1 x2 y1 y2).
        -- right. exact Hx1.
        -- right. exact Hx2.
        -- exact Hneq.
        -- exact Hy1.
        -- exact Hy2.
    + intros p Hp1 Hp2.
      apply in_map_iff in Hp1 as [y1 [Heq1 Hy1]].
      apply in_flat_map in Hp2 as [x2 [Hx2 Hp2]].
      apply in_map_iff in Hp2 as [y2 [Heq2 Hy2]].
      subst p.
      apply (Hdisj x x2 y1 y2).
      * left. reflexivity.
      * right. exact Hx2.
      * intro Heq. subst x2. contradiction.
      * exact Hy1.
      * exact Hy2.
      * symmetry. exact Heq2.
Qed.
Lemma interval_pairs_by_start_member__final_result :
  forall n i j,
    In (i, j)
      (flat_map (fun i : Z => map (fun j : Z => (i, j)) (Zrange i n))
        (Zrange 0 n)) <->
    (0 <= i)%Z /\ (i <= j)%Z /\ (j < n)%Z.
Proof.
  intros n i j.
  rewrite in_flat_map. split.
  - intros [i' [Hi' Hp]].
    apply in_map_iff in Hp as [j' [Heq Hj']].
    inversion Heq; subst.
    rewrite <- In_Zrange in Hi', Hj'. lia.
  - intros Hrange.
    exists i. split.
    + rewrite <- In_Zrange. lia.
    + apply in_map_iff. exists j. split; [reflexivity |].
      rewrite <- In_Zrange. lia.
Qed.
Lemma interval_pairs_by_length_member__final_result :
  forall n i j,
    In (i, j)
      (flat_map
        (fun len : Z => map (fun i : Z => (i, i + len - 1)%Z)
          (Zrange 0 (n - len + 1)))
        (Zrange 1 (n + 1))) <->
    (0 <= i)%Z /\ (i <= j)%Z /\ (j < n)%Z.
Proof.
  intros n i j.
  rewrite in_flat_map. split.
  - intros [len [Hlen Hp]].
    apply in_map_iff in Hp as [i' [Heq Hi']].
    inversion Heq; subst.
    rewrite <- In_Zrange in Hlen, Hi'. lia.
  - intros Hrange.
    exists (j - i + 1)%Z. split.
    + rewrite <- In_Zrange. lia.
    + apply in_map_iff. exists i. split.
      * f_equal; lia.
      * rewrite <- In_Zrange. lia.
Qed.
Lemma interval_pairs_by_start_NoDup__final_result :
  forall n,
    NoDup
      (flat_map (fun i : Z => map (fun j : Z => (i, j)) (Zrange i n))
        (Zrange 0 n)).
Proof.
  intros n.
  apply NoDup_flat_map_indexed__final_result.
  - apply NoDup_Zrange.
  - intros. apply NoDup_Zrange.
  - intros i y1 y2 Hi Hy1 Hy2 Heq. congruence.
  - intros i1 i2 y1 y2 Hi1 Hi2 Hneq Hy1 Hy2 Heq.
    injection Heq. contradiction.
Qed.
Lemma interval_pairs_by_length_NoDup__final_result :
  forall n,
    NoDup
      (flat_map
        (fun len : Z => map (fun i : Z => (i, i + len - 1)%Z)
          (Zrange 0 (n - len + 1)))
        (Zrange 1 (n + 1))).
Proof.
  intros n.
  apply NoDup_flat_map_indexed__final_result.
  - apply NoDup_Zrange.
  - intros. apply NoDup_Zrange.
  - intros len y1 y2 Hlen Hy1 Hy2 Heq. congruence.
  - intros len1 len2 i1 i2 Hlen1 Hlen2 Hneq Hi1 Hi2 Heq.
    injection Heq as Hi Hij.
    subst i2. apply Hneq. lia.
Qed.
Lemma interval_pairs_reindex_permutation__final_result :
  forall n,
    Permutation
      (flat_map (fun i : Z => map (fun j : Z => (i, j)) (Zrange i n))
        (Zrange 0 n))
      (flat_map
        (fun len : Z => map (fun i : Z => (i, i + len - 1)%Z)
          (Zrange 0 (n - len + 1)))
        (Zrange 1 (n + 1))).
Proof.
  intros n. apply NoDup_Permutation.
  - apply interval_pairs_by_start_NoDup__final_result.
  - apply interval_pairs_by_length_NoDup__final_result.
  - intros [i j].
    rewrite interval_pairs_by_start_member__final_result.
    rewrite interval_pairs_by_length_member__final_result.
    tauto.
Qed.
Lemma fold_Rplus_map_permutation__final_result :
  forall {A : Type} (f : A -> R) xs ys,
    Permutation xs ys ->
    fold_right Rplus 0%R (map f xs) =
    fold_right Rplus 0%R (map f ys).
Proof.
  intros A f xs ys Hperm. induction Hperm; simpl.
  - reflexivity.
  - rewrite IHHperm. reflexivity.
  - ring.
  - rewrite IHHperm1, IHHperm2. reflexivity.
Qed.
Lemma fold_Rplus_map_app__final_result :
  forall {A : Type} (f : A -> R) xs ys,
    fold_right Rplus 0%R (map f (xs ++ ys)) =
    (fold_right Rplus 0%R (map f xs) +
     fold_right Rplus 0%R (map f ys))%R.
Proof.
  intros A f xs. induction xs as [|x xs IH]; intros ys; simpl.
  - ring.
  - rewrite IH. ring.
Qed.
Lemma fold_Rplus_map_flat_map__final_result :
  forall {A B C : Type} (xs : list A) (ys : A -> list B)
         (encode : A -> B -> C) (h : C -> R),
    fold_right Rplus 0%R
      (map h (flat_map (fun x => map (encode x) (ys x)) xs)) =
    fold_right Rplus 0%R
      (map (fun x => fold_right Rplus 0%R
        (map (fun y => h (encode x y)) (ys x))) xs).
Proof.
  intros A B C xs. induction xs as [|x xs IH]; intros ys encode h; simpl.
  - reflexivity.
  - rewrite fold_Rplus_map_app__final_result.
    rewrite map_map. simpl. rewrite IH. reflexivity.
Qed.
Lemma fold_Rplus_map_flat_map_pair__final_result :
  forall {A B : Type} (xs : list A) (ys : A -> list B) (f : A -> B -> R),
    fold_right Rplus 0%R
      (map (fun p => f (fst p) (snd p))
        (flat_map (fun x => map (fun y => (x, y)) (ys x)) xs)) =
    fold_right Rplus 0%R
      (map (fun x => fold_right Rplus 0%R (map (f x) (ys x))) xs).
Proof.
  intros A B xs. induction xs as [|x xs IH]; intros ys f; simpl.
  - reflexivity.
  - rewrite fold_Rplus_map_app__final_result.
    rewrite map_map. simpl. rewrite IH. reflexivity.
Qed.
Lemma sum_range_R_triangle_reindex__final_result :
  forall n (f : Z -> Z -> R),
    sum_range_R 0 (n - 1) (fun i => sum_range_R i (n - 1) (f i)) =
    sum_range_R 1 n
      (fun len => sum_range_R 0 (n - len)
        (fun i => f i (i + len - 1)%Z)).
Proof.
  intros n f. unfold sum_range_R.
  replace (n - 1 + 1)%Z with n by ring.
  change
    (fold_right Rplus 0%R
      (map (fun i => fold_right Rplus 0%R (map (f i) (Zrange i n)))
        (Zrange 0 n)) =
     fold_right Rplus 0%R
      (map
        (fun len => fold_right Rplus 0%R
          (map (fun i => f i (i + len - 1)%Z) (Zrange 0 (n - len + 1))))
        (Zrange 1 (n + 1)))).
  rewrite <- (fold_Rplus_map_flat_map_pair__final_result
    (Zrange 0 n) (fun i => Zrange i n) f).
  pose proof (fold_Rplus_map_flat_map__final_result
    (Zrange 1 (n + 1)) (fun len => Zrange 0 (n - len + 1))
    (fun len i => (i, i + len - 1)%Z)
    (fun p => f (fst p) (snd p))) as Hlength.
  cbn [fst snd] in Hlength. rewrite <- Hlength. clear Hlength.
  apply fold_Rplus_map_permutation__final_result.
  apply interval_pairs_reindex_permutation__final_result.
Qed.
Lemma IZR_fold_Zplus__final_result :
  forall xs (f : Z -> Z),
    IZR (fold_right (fun x acc => f x + acc)%Z 0%Z xs) =
    fold_right Rplus 0%R (map (fun x => IZR (f x)) xs).
Proof.
  intros xs. induction xs as [|x xs IH]; intros f; simpl.
  - reflexivity.
  - rewrite plus_IZR, IH. reflexivity.
Qed.
Lemma IZR_sum_range_as_sum_range_R__final_result :
  forall lo hi (f : Z -> Z),
    IZR (sum_range lo hi f) =
    sum_range_R lo hi (fun x => IZR (f x)).
Proof.
  intros lo hi f. unfold sum_range, sum_range_R.
  rewrite SumLib.ZRange.sum_range_unfold.
  apply IZR_fold_Zplus__final_result.
Qed.
Lemma sum_range_R_div_ext__final_result :
  forall lo hi (f : Z -> Z) d,
    (IZR (sum_range lo hi f) / IZR d)%R =
    sum_range_R lo hi (fun x => (IZR (f x) / IZR d)%R).
Proof.
  intros lo hi f d.
  rewrite IZR_sum_range_as_sum_range_R__final_result.
  unfold sum_range_R, Rdiv.
  generalize (Zrange lo (hi + 1)).
  intros xs. induction xs as [|x xs IH]; simpl.
  - ring.
  - rewrite <- IH. ring.
Qed.
Lemma sum_range_R_ext__final_result :
  forall lo hi (f g : Z -> R),
    (forall x, (lo <= x <= hi)%Z -> f x = g x) ->
    sum_range_R lo hi f = sum_range_R lo hi g.
Proof.
  intros lo hi f g Hext. unfold sum_range_R.
  assert (Hfold : forall xs,
    (forall x, In x xs -> f x = g x) ->
    fold_right Rplus 0%R (map f xs) =
    fold_right Rplus 0%R (map g xs)).
  { intros xs. induction xs as [|x xs IH]; intros Hall; simpl.
    - reflexivity.
    - rewrite Hall by (left; reflexivity).
      rewrite IH.
      + reflexivity.
      + intros y Hy. apply Hall. right. exact Hy. }
  apply Hfold. intros x Hx. apply Hext.
  rewrite <- In_Zrange in Hx. lia.
Qed.
Lemma spec_pretty_terms_reindex__final_result :
  forall s terms,
    PrettyTermTable s terms ->
    sum_range_R 0 (Zlength s - 1) (fun i =>
      sum_range_R i (Zlength s - 1) (fun j =>
        IZR (#(fun q : Z => (i <= q < j + 1)%Z /\ Vowel (Znth q s 0%Z))) /
        IZR (j - i + 1))) =
    sum_range_R 1 (Zlength s) (fun len =>
      IZR (Znth (len - 1) terms 0%Z) / IZR len).
Proof.
  intros s terms [Hlen Hterms].
  rewrite sum_range_R_triangle_reindex__final_result.
  apply sum_range_R_ext__final_result.
  intros len Hlen_range.
  rewrite Hterms by lia.
  unfold PrettyTerm.
  rewrite sum_range_R_div_ext__final_result.
  apply sum_range_R_ext__final_result.
  intros i Hi.
  replace (i + len - 1 + 1)%Z with (i + len)%Z by lia.
  replace (i + len - 1 - i + 1)%Z with len by ring.
  reflexivity.
Qed.
Lemma spec_pretty_terms_exists__final_result :
  forall s terms,
    PrettyTermTable s terms ->
    exists out, Spec s out /\ PrettyTerms s terms out.
Proof.
  intros s terms Htable.
  exists (sum_range_R 1 (Zlength s) (fun len =>
    IZR (Znth (len - 1) terms 0%Z) / IZR len)).
  split.
  - unfold Spec.
    symmetry.
    apply spec_pretty_terms_reindex__final_result.
    exact Htable.
  - split.
    + exact Htable.
    + reflexivity.
Qed.
