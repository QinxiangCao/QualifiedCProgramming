Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition RotationMatches (a b:list Z) (d score:Z) : Prop :=
  0 <= d < Zlength a /\
  score=#(fun i:Z=>0 <= i < Zlength a /\ Znth i a 0 = Znth((i + d) mod Zlength a) b 0).
Definition Pre (a b:list Z) : Prop :=
  (* Stated explicitly in the P038 solver Require, so dropped here:
       1 <= Zlength a <= 200000 /\ Zlength b = Zlength a /\ *)
  Permutation a (Zrange 1 (Zlength a + 1)) /\
  Permutation b (Zrange 1 (Zlength b + 1)).
Definition Spec (a b:list Z) (out:Z) : Prop :=
  max_value_of_subset Z.le (fun v => exists d, RotationMatches a b d v) (fun x => x) out.

Definition PositionTable
    (values table : list Z) (n : Z) : Prop :=
  Zlength values = n /\
  Zlength table = n + 1 /\
  (forall i, 0 <= i < n ->
    1 <= Znth i values 0 <= n /\
    Znth (Znth i values 0) table 0 = i) /\
  (forall v, 1 <= v <= n -> 0 <= Znth v table 0 < n).

Definition RotationTallyPrefix
    (pa pb : list Z) (n next : Z) (counts : list Z) : Prop :=
  Zlength counts = n /\
  1 <= next <= n + 1 /\
  forall s, 0 <= s < n ->
    Znth s counts 0 =
      #(fun v : Z =>
          1 <= v < next /\
          (Znth v pa 0 - Znth v pb 0) mod n = s) /\
    0 <= Znth s counts 0 <= next - 1.

Definition CountPrefixMaximum
    (counts : list Z) (upto best : Z) : Prop :=
  0 <= upto <= Zlength counts /\
  0 <= best /\
  (forall s, 0 <= s < upto -> Znth s counts 0 <= best) /\
  (upto = 0 -> best = 0) /\
  (0 < upto -> exists s, 0 <= s < upto /\ Znth s counts 0 = best).

Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.Zquot.
Require Import Coq.setoid_ring.Ring.
Lemma In_Znth_Zlength__setup_layout {A : Type} :
  forall (l : list A) (x d : A),
    In x l ->
    exists i, 0 <= i < Zlength l /\ Znth i l d = x.
Proof.
  intros l x d Hin.
  pose proof (@In_nth A l x d Hin) as [i [Hi Hnth]].
  exists (Z.of_nat i).
  split.
  - rewrite Zlength_correct. lia.
  - unfold Znth. rewrite Nat2Z.id. exact Hnth.
Qed.
Lemma position_table_from_permutation_inverse__setup_layout :
  forall values table n,
    Zlength values = n ->
    Zlength table = n + 1 ->
    Permutation values (Zrange 1 (n + 1)) ->
    (forall i, 0 <= i < n -> 1 <= Znth i values 0 <= n) ->
    (forall i, 0 <= i < n -> Znth (Znth i values 0) table 0 = i) ->
    PositionTable values table n.
Proof.
  intros values table n Hvalues Htable Hperm Hbounds Hinverse.
  unfold PositionTable.
  split; [exact Hvalues |].
  split; [exact Htable |].
  split.
  - intros i Hi. split; [apply Hbounds; exact Hi | apply Hinverse; exact Hi].
  - intros v Hv.
    assert (Hinrange : In v (Zrange 1 (n + 1))).
    { apply (proj1 (In_Zrange 1 (n + 1) v)). lia. }
    assert (Hinvalues : In v values).
    { eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hinrange]. }
    destruct (In_Znth_Zlength__setup_layout values v 0 Hinvalues)
      as [i [Hi Hiv]].
    rewrite Hvalues in Hi.
    specialize (Hinverse i Hi).
    rewrite Hiv in Hinverse.
    rewrite Hinverse.
    exact Hi.
Qed.
Lemma set_card_empty__setup_layout :
  forall {A : Type} (P : A -> Prop) (FP : Finite P),
    (forall x, ~ P x) -> @set_card A P FP = 0.
Proof.
  intros A P FP Hempty.
  unfold set_card, SumLib.Sum.sum.
  destruct (@enum A P FP) as [|x xs] eqn:Hen; [reflexivity |].
  exfalso.
  apply (Hempty x).
  apply (proj2 (@enum_ok A P FP x)).
  rewrite Hen. simpl. auto.
Qed.
Lemma replace_nth_length__tally_transitions :
  forall {A : Type} (i : nat) (value : A) (xs : list A),
    length (replace_nth i xs value) = length xs.
Proof.
  intros A i value xs.
  revert xs.
  induction i as [|i IH]; intros xs; destruct xs; simpl; auto.
Qed.
Lemma Zlength_replace_Znth__tally_transitions :
  forall {A : Type} (i : Z) (value : A) (xs : list A),
    Zlength (replace_Znth i value xs) = Zlength xs.
Proof.
  intros A i value xs.
  rewrite !Zlength_correct.
  unfold replace_Znth.
  rewrite replace_nth_length__tally_transitions.
  reflexivity.
Qed.
Lemma set_card_Z_as_sum__tally_transitions :
  forall (low high : Z) (P : Z -> Prop),
    #(fun z : Z => low <= z < high /\ P z) =
    SumLib.Sum.sum (fun z : Z => low <= z < high)
      (fun z => if prop_dec (P z) then 1 else 0).
Proof.
  intros low high P.
  unfold set_card, SumLib.Sum.sum.
  cbn [finite_Z_range' finite_Z_range].
  assert (Hfilter : forall zs : list Z,
    fold_right (fun _ acc : Z => 1 + acc) 0
      (filter (fun z => if prop_dec (P z) then true else false) zs) =
    fold_right (fun z acc : Z =>
      (if prop_dec (P z) then 1 else 0) + acc) 0 zs).
  {
    induction zs as [|z zs IH]; simpl; [reflexivity |].
    destruct (prop_dec (P z)); simpl.
    - exact (f_equal (fun n : Z => 1 + n) IH).
    - exact IH.
  }
  apply Hfilter.
Qed.
Lemma set_card_Z_extend_true__tally_transitions :
  forall (low high : Z) (P : Z -> Prop),
    low <= high -> P high ->
    #(fun z : Z => low <= z < high + 1 /\ P z) =
    #(fun z : Z => low <= z < high /\ P z) + 1.
Proof.
  intros low high P Hrange HP.
  rewrite !set_card_Z_as_sum__tally_transitions.
  rewrite SumLib.ZRange.sum_Z_range_extend_right by exact Hrange.
  destruct (prop_dec (P high)) as [_ | Hnot]; [lia | contradiction].
Qed.
Lemma set_card_Z_extend_false__tally_transitions :
  forall (low high : Z) (P : Z -> Prop),
    low <= high -> ~ P high ->
    #(fun z : Z => low <= z < high + 1 /\ P z) =
    #(fun z : Z => low <= z < high /\ P z).
Proof.
  intros low high P Hrange HP.
  rewrite !set_card_Z_as_sum__tally_transitions.
  rewrite SumLib.ZRange.sum_Z_range_extend_right by exact Hrange.
  destruct (prop_dec (P high)) as [Hp | _]; [contradiction | lia].
Qed.
Lemma nonnegative_rem_eq_mod__tally_transitions :
  forall a n,
    0 < n ->
    0 <= Z.rem a n ->
    Z.rem a n = a mod n.
Proof.
  intros a n Hn Hrem.
  destruct (Z_le_gt_dec 0 a) as [Ha | Ha].
  - apply Z.rem_mod_nonneg; lia.
  - assert (Z.rem a n <= 0) by (apply Z.rem_nonpos; lia).
    assert (Z.rem a n = 0) by lia.
    assert (a mod n = 0).
    {
      apply (proj1 (Zrem_Zmod_zero a n ltac:(lia))).
      assumption.
    }
    lia.
Qed.
Lemma rotation_tally_prefix_step__tally_transitions :
  forall pa pb n v counts shift,
    RotationTallyPrefix pa pb n v counts ->
    1 <= v <= n ->
    0 <= shift < n ->
    shift = Z.rem ((Znth v pa 0 - Znth v pb 0) + n) n ->
    RotationTallyPrefix pa pb n (v + 1)
      (replace_Znth shift (Znth shift counts 0 + 1) counts).
Proof.
  intros pa pb n v counts shift Htally Hv Hshift Heqshift.
  assert (Hrem_nonneg :
    0 <= Z.rem ((Znth v pa 0 - Znth v pb 0) + n) n) by
    (rewrite <- Heqshift; lia).
  pose proof (nonnegative_rem_eq_mod__tally_transitions
    ((Znth v pa 0 - Znth v pb 0) + n) n ltac:(lia) Hrem_nonneg)
    as Hrem_mod.
  assert (Heqshiftmod :
    shift = (Znth v pa 0 - Znth v pb 0) mod n).
  {
    rewrite Heqshift, Hrem_mod.
    replace (Znth v pa 0 - Znth v pb 0 + n)
      with ((Znth v pa 0 - Znth v pb 0) + 1 * n) by ring.
    rewrite Z.mod_add by lia.
    reflexivity.
  }
  unfold RotationTallyPrefix in *.
  destruct Htally as [Hlen [Hnext Hall]].
  split.
  - rewrite Zlength_replace_Znth__tally_transitions. exact Hlen.
  - split; [lia |].
    intros s Hs.
    specialize (Hall s Hs) as [Hcount Hbound].
    split.
    + destruct (Z.eq_dec s shift) as [Heq | Hneq].
      * subst s.
        rewrite Znth_replace_Znth_Same by lia.
        rewrite Hcount.
        symmetry.
        apply set_card_Z_extend_true__tally_transitions; [lia |].
        symmetry. exact Heqshiftmod.
      * rewrite Znth_replace_Znth_Diff by lia.
        rewrite Hcount.
        symmetry.
        apply set_card_Z_extend_false__tally_transitions; [lia |].
        intro Hres.
        apply Hneq.
        rewrite Heqshiftmod.
        symmetry. exact Hres.
    + destruct (Z.eq_dec s shift) as [Heq | Hneq].
      * subst s.
        rewrite Znth_replace_Znth_Same by lia.
        lia.
      * rewrite Znth_replace_Znth_Diff by lia.
        lia.
Qed.
Lemma count_prefix_max_step_gt__tally_transitions :
  forall counts s best,
    0 <= s < Zlength counts ->
    CountPrefixMaximum counts s best ->
    Znth s counts 0 > best ->
    CountPrefixMaximum counts (s + 1) (Znth s counts 0).
Proof.
  intros counts s best Hs Hmax Hgt.
  unfold CountPrefixMaximum in *.
  destruct Hmax as [Hrange [Hbest [Hbound [Hzero Hattain]]]].
  split.
  - lia.
  - split; [lia |].
    split.
    + intros i Hi.
      destruct (Z.eq_dec i s) as [-> | Hneq].
      * lia.
      * apply Z.lt_le_incl.
        apply Z.le_lt_trans with best; [apply Hbound; lia | lia].
    + split.
      * lia.
      * intros _.
        exists s. lia.
Qed.
Lemma count_prefix_max_step_le__tally_transitions :
  forall counts s best,
    0 <= s < Zlength counts ->
    CountPrefixMaximum counts s best ->
    0 <= Znth s counts 0 ->
    Znth s counts 0 <= best ->
    CountPrefixMaximum counts (s + 1) best.
Proof.
  intros counts s best Hs Hmax Hnonneg Hle.
  unfold CountPrefixMaximum in *.
  destruct Hmax as [Hrange [Hbest [Hbound [Hzero Hattain]]]].
  split.
  - lia.
  - split; [exact Hbest |].
    split.
    + intros i Hi.
      destruct (Z.eq_dec i s) as [-> | Hneq].
      * exact Hle.
      * apply Hbound. lia.
    + split.
      * lia.
      * intros _.
        destruct (Z.eq_dec s 0) as [-> | Hsne].
        -- exists 0. split; [lia |].
           specialize (Hzero eq_refl).
           lia.
        -- specialize (Hattain ltac:(lia)) as [i [Hi Heq]].
           exists i. split; [lia | exact Heq].
Qed.
Lemma set_card_bijection__final_result :
  forall {A B : Type} (P : A -> Prop) (Q : B -> Prop)
         (FP : Finite P) (FQ : Finite Q) (f : A -> B) (g : B -> A),
    (forall x, P x -> Q (f x)) ->
    (forall y, Q y -> P (g y)) ->
    (forall x, P x -> g (f x) = x) ->
    (forall y, Q y -> f (g y) = y) ->
    @set_card A P FP = @set_card B Q FQ.
Proof.
  intros A B P Q FP FQ f g Hf Hg Hgf Hfg.
  unfold set_card, SumLib.Sum.sum.
  assert (Hnodup_map : NoDup (map f (@enum A P FP))).
  {
    assert (Hgeneral : forall xs : list A,
      NoDup xs -> (forall x, In x xs -> P x) -> NoDup (map f xs)).
    {
      intros xs Hnodup.
      induction Hnodup as [|x xs Hnotin Hnodup IH]; intros Hall; simpl.
      - constructor.
      - constructor.
        + intro Hin.
          apply in_map_iff in Hin.
          destruct Hin as [y [Hfy Hy]].
          apply Hnotin.
          assert (HPx : P x) by (apply Hall; left; reflexivity).
          assert (HPy : P y) by (apply Hall; right; exact Hy).
          assert (Hxy : x = y).
          {
            rewrite <- (Hgf x HPx), <- (Hgf y HPy).
            congruence.
          }
          rewrite Hxy. exact Hy.
        + apply IH. intros y Hy. apply Hall. right. exact Hy.
    }
    apply Hgeneral.
    - exact (@enum_nodup A P FP).
    - intros x Hx. apply (proj2 (@enum_ok A P FP x)). exact Hx.
  }
  assert (Hperm : Permutation (map f (@enum A P FP)) (@enum B Q FQ)).
  {
    apply NoDup_Permutation.
    - exact Hnodup_map.
    - exact (@enum_nodup B Q FQ).
    - intros y.
      rewrite <- (@enum_ok B Q FQ y).
      split.
      + intros Hin.
        apply in_map_iff in Hin.
        destruct Hin as [x [Hxy Hx]].
        subst y.
        apply Hf.
        apply (proj2 (@enum_ok A P FP x)). exact Hx.
      + intros HyQ.
        apply in_map_iff.
        exists (g y). split.
        * apply Hfg. exact HyQ.
        * apply (proj1 (@enum_ok A P FP (g y))).
          apply Hg. exact HyQ.
  }
  assert (Hfold_count : forall (C : Type) (l : list C),
    fold_right (fun _ (acc : Z) => 1 + acc) 0 l = Z.of_nat (length l)).
  {
    intros C l. induction l as [|x xs IH].
    - reflexivity.
    - change (1 + fold_right (fun _ (acc : Z) => 1 + acc) 0 xs =
        Z.of_nat (S (length xs))).
      rewrite IH, Nat2Z.inj_succ. lia.
  }
  rewrite !Hfold_count.
  rewrite <- (Permutation_length Hperm), length_map.
  reflexivity.
Qed.
Lemma In_Znth_Zlength__final_result :
  forall {A : Type} (l : list A) (x d : A),
    In x l -> exists i, 0 <= i < Zlength l /\ Znth i l d = x.
Proof.
  intros A l x d Hin.
  destruct (@In_nth A l x d Hin) as [i [Hi Hnth]].
  exists (Z.of_nat i). split.
  - rewrite Zlength_correct. lia.
  - unfold Znth. rewrite Nat2Z.id. exact Hnth.
Qed.
Lemma position_table_lookup_value__final_result :
  forall values table n,
    Permutation values (Zrange 1 (n + 1)) ->
    PositionTable values table n ->
    forall v, 1 <= v <= n ->
      Znth (Znth v table 0) values 0 = v.
Proof.
  intros values table n Hperm Htable v Hv.
  destruct Htable as [Hlen [_ [Hforward _]]].
  assert (Hin_range : In v (Zrange 1 (n + 1))).
  { apply (proj1 (In_Zrange 1 (n + 1) v)). lia. }
  assert (Hin_values : In v values).
  { apply (Permutation_in v (Permutation_sym Hperm)). exact Hin_range. }
  destruct (In_Znth_Zlength__final_result values v 0 Hin_values)
    as [i [Hi Hiv]].
  specialize (Hforward i ltac:(lia)) as [_ Htablev].
  rewrite Hiv in Htablev.
  rewrite Htablev.
  exact Hiv.
Qed.
Lemma neg_mod_formula__final_result :
  forall n s, 0 < n -> 0 <= s < n ->
    (- s) mod n = if Z.eq_dec s 0 then 0 else n - s.
Proof.
  intros n s Hn Hs.
  destruct (Z.eq_dec s 0) as [-> | Hne].
  - simpl. apply Z.mod_0_l. lia.
  - destruct (Z.eq_dec s 0); [contradiction |].
    symmetry. apply Z.mod_unique with (q := -1).
    + left. lia.
    + ring.
Qed.
Lemma neg_mod_involution__final_result :
  forall n s, 0 < n -> 0 <= s < n ->
    (- ((- s) mod n)) mod n = s.
Proof.
  intros n s Hn Hs.
  rewrite (neg_mod_formula__final_result n s Hn Hs).
  destruct (Z.eq_dec s 0) as [-> | Hne].
  - simpl. apply Z.mod_0_l. lia.
  - rewrite (neg_mod_formula__final_result n (n - s)) by lia.
    destruct (Z.eq_dec (n - s) 0); [lia |].
    ring.
Qed.
Lemma rotation_mod_equiv__final_result :
  forall n i j s,
    0 < n -> 0 <= i < n -> 0 <= j < n -> 0 <= s < n ->
    ((i - j) mod n = s <->
     j = (i + ((- s) mod n)) mod n).
Proof.
  intros n i j s Hn Hi Hj Hs.
  destruct (Z.eq_dec s 0) as [-> | Hsne].
  - rewrite neg_mod_formula__final_result by lia.
    destruct (Z.eq_dec 0 0); [|contradiction].
    replace ((i + 0) mod n) with i by
      (rewrite Z.add_0_r; symmetry; apply Z.mod_small; lia).
    split; intro H.
    + destruct (Z_le_gt_dec j i) as [Hji | Hij].
      * rewrite Z.mod_small in H by lia. lia.
      * assert (Hmod : (i - j) mod n = n + i - j).
        { symmetry. apply Z.mod_unique with (q := -1); [left; lia | ring]. }
        rewrite Hmod in H. lia.
    + subst j. rewrite Z.sub_diag. apply Z.mod_0_l. lia.
  - rewrite neg_mod_formula__final_result by lia.
    destruct (Z.eq_dec s 0); [contradiction |].
    destruct (Z_le_gt_dec j i) as [Hji | Hij].
    + assert (Hdiff : (i - j) mod n = i - j).
      { apply Z.mod_small. lia. }
      rewrite Hdiff.
      split; intro H.
      * assert (Hrhs : (i + (n - s)) mod n = j).
        { symmetry. apply Z.mod_unique with (q := 1); [left; lia | lia]. }
        symmetry. exact Hrhs.
      * destruct (Z_lt_ge_dec i s) as [His | Hsi].
        -- rewrite Z.mod_small in H by lia. lia.
        -- assert (Hrhs : (i + (n - s)) mod n = i - s).
           { symmetry. apply Z.mod_unique with (q := 1); [left; lia | ring]. }
           rewrite Hrhs in H. lia.
    + assert (Hdiff : (i - j) mod n = n + i - j).
      { symmetry. apply Z.mod_unique with (q := -1); [left; lia | ring]. }
      rewrite Hdiff.
      split; intro H.
      * rewrite Z.mod_small by lia. lia.
      * destruct (Z_lt_ge_dec i s) as [His | Hsi].
        -- rewrite Z.mod_small in H by lia. lia.
        -- assert (Hrhs : (i + (n - s)) mod n = i - s).
           { symmetry. apply Z.mod_unique with (q := 1); [left; lia | ring]. }
           rewrite Hrhs in H. lia.
Qed.
Lemma rotation_bucket_cardinality__final_result :
  forall a b pa pb n s,
    0 < n ->
    Permutation a (Zrange 1 (n + 1)) ->
    Permutation b (Zrange 1 (n + 1)) ->
    PositionTable a pa n ->
    PositionTable b pb n ->
    0 <= s < n ->
    #(fun i : Z =>
        0 <= i < n /\
        Znth i a 0 = Znth ((i + ((- s) mod n)) mod n) b 0) =
    #(fun v : Z =>
        1 <= v < n + 1 /\
        (Znth v pa 0 - Znth v pb 0) mod n = s).
Proof.
  intros a b pa pb n s Hn Hpa_perm Hpb_perm Hpa Hpb Hs.
  eapply set_card_bijection__final_result
    with (f := fun i => Znth i a 0)
         (g := fun v => Znth v pa 0).
  - intros i [Hi Hmatch].
    pose proof Hpa as Hpa_parts.
    pose proof Hpb as Hpb_parts.
    destruct Hpa_parts as [_ [_ [Hpa_forward Hpa_range]]].
    destruct Hpb_parts as [_ [_ [Hpb_forward Hpb_range]]].
    specialize (Hpa_forward i Hi) as [Hva Hpai].
    set (j := (i + ((- s) mod n)) mod n).
    assert (Hj : 0 <= j < n).
    { unfold j. apply Z.mod_pos_bound. lia. }
    specialize (Hpb_forward j Hj) as [_ Hpbj].
    split; [lia |].
    change (Znth i a 0 = Znth j b 0) in Hmatch.
    rewrite <- Hmatch in Hpbj.
    rewrite Hpai, Hpbj.
    apply (proj2 (rotation_mod_equiv__final_result n i j s Hn Hi Hj Hs)).
    unfold j. reflexivity.
  - intros v [Hv Hmod].
    pose proof Hpa as Hpa_parts.
    pose proof Hpb as Hpb_parts.
    destruct Hpa_parts as [_ [_ [Hpa_forward Hpa_range]]].
    destruct Hpb_parts as [_ [_ [Hpb_forward Hpb_range]]].
    specialize (Hpa_range v ltac:(lia)) as Hi.
    specialize (Hpb_range v ltac:(lia)) as Hj.
    split; [exact Hi |].
    pose proof (position_table_lookup_value__final_result
      a pa n Hpa_perm Hpa v ltac:(lia)) as Ha_lookup.
    pose proof (position_table_lookup_value__final_result
      b pb n Hpb_perm Hpb v ltac:(lia)) as Hb_lookup.
    pose proof (proj1 (rotation_mod_equiv__final_result n
      (Znth v pa 0) (Znth v pb 0) s Hn Hi Hj Hs) Hmod) as Hshift.
    rewrite <- Hshift, Ha_lookup, Hb_lookup.
    reflexivity.
  - intros i [Hi _].
    pose proof Hpa as Hpa_parts.
    destruct Hpa_parts as [_ [_ [Hpa_forward _]]].
    exact (proj2 (Hpa_forward i Hi)).
  - intros v [Hv _].
    apply position_table_lookup_value__final_result with (n := n);
      assumption || lia.
Qed.
Lemma rotation_tally_max_implies_spec__final_result :
  forall a b pa pb n counts best,
    1 <= n ->
    Pre a b ->
    PositionTable a pa n ->
    PositionTable b pb n ->
    RotationTallyPrefix pa pb n (n + 1) counts ->
    CountPrefixMaximum counts n best ->
    Spec a b best.
Proof.
  intros a b pa pb n counts best Hn Hpre Hpa Hpb Htally Hmax.
  destruct Hpre as [Ha_perm Hb_perm].
  pose proof Hpa as Hpa_copy.
  pose proof Hpb as Hpb_copy.
  destruct Hpa_copy as [Halen [_ _]].
  destruct Hpb_copy as [Hblen [_ _]].
  rewrite Halen in Ha_perm.
  rewrite Hblen in Hb_perm.
  destruct Htally as [Hcounts_len [_ Htally]].
  destruct Hmax as [_ [Hbest_nonneg [Hupper [_ Hattain]]]].
  unfold Spec, max_value_of_subset, max_object_of_subset.
  exists best. split.
  - split.
    + destruct (Hattain ltac:(lia)) as [s [Hs Hcount_best]].
      exists ((- s) mod n).
      unfold RotationMatches.
      split.
      * rewrite Halen. apply Z.mod_pos_bound. lia.
      * rewrite Halen.
        specialize (Htally s Hs) as [Htally_s _].
        rewrite Hcount_best in Htally_s.
        rewrite (rotation_bucket_cardinality__final_result
          a b pa pb n s ltac:(lia) Ha_perm Hb_perm Hpa Hpb Hs).
        exact Htally_s.
    + intros score [d [Hd Hscore]].
      rewrite Halen in Hd, Hscore.
      set (s := (- d) mod n).
      assert (Hs : 0 <= s < n).
      { unfold s. apply Z.mod_pos_bound. lia. }
      specialize (Htally s Hs) as [Htally_s _].
      specialize (Hupper s Hs).
      assert (Hinv : (- s) mod n = d).
      { unfold s. apply neg_mod_involution__final_result; lia. }
      rewrite Hscore.
      rewrite <- Hinv.
      rewrite (rotation_bucket_cardinality__final_result
        a b pa pb n s ltac:(lia) Ha_perm Hb_perm Hpa Hpb Hs).
      rewrite <- Htally_s.
      exact Hupper.
  - reflexivity.
Qed.
