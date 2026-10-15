Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Local Open Scope Z_scope.

Definition CommonMultipleOfChosen (a : list Z) (indices : Z -> Prop) (x : Z) : Prop :=
  forall i, indices i -> (Znth i a 0 | x).

Definition LeastCommonOfChosen (a : list Z) (indices : Z -> Prop) (x : Z) : Prop :=
  min_value_of_subset (fun left right : Z => (left | right))
    (fun candidate : Z =>
      1 <= candidate /\ CommonMultipleOfChosen a indices candidate)
    (fun candidate => candidate) x.

Definition SpecialChoice (a : list Z) (indices : Z -> Prop) : Prop :=
  (forall i, indices i -> 0 <= i < Zlength a) /\
  exists x, LeastCommonOfChosen a indices x /\ ~ In x a.

Definition Pre (a : list Z) : Prop :=
  1 <= Zlength a <= 2000 /\
  Forall (fun x => 1 <= x <= 1000000000) a.

Definition Spec (a : list Z) (out : Z) : Prop :=
  max_value_of_subset_with_default Z.le
    (fun candidate : (Z -> Prop) * Z =>
      SpecialChoice a (fst candidate) /\
      snd candidate = #(fun i : Z => 0 <= i < Zlength a /\ fst candidate i))
    snd 0 out.

Definition GcdValue (a b : Z) : Z :=
  Z.gcd a b.

Definition LcmCapValue (a b cap out : Z) : Prop :=
  let exact := Z.lcm a b in
  out = if exact <=? cap then exact else cap + 1.

Definition CompareResult (a b out : Z) : Prop :=
  (a > b /\ out = 1) \/
  (a < b /\ out = -1) \/
  (a = b /\ out = 0).

Require Import Coq.Sorting.Permutation.

Definition CopyMaxState
    (input copied : list Z) (processed mx : Z) : Prop :=
  copied = sublist 0 processed input /\
  ((processed = 0 /\ mx = 0) \/
   (0 < processed /\
    max_value_of_subset Z.le
      (fun i : Z => 0 <= i < processed)
      (fun i => Znth i input 0) mx)).

Definition LcmPrefixState
    (values : list Z) (processed cap acc : Z) : Prop :=
  exists exact,
    LeastCommonOfChosen values (fun i : Z => 0 <= i < processed) exact /\
    acc = if exact <=? cap then exact else cap + 1.

Definition PrefixContains
    (values : list Z) (processed d : Z) : Prop :=
  exists i, 0 <= i < processed /\ Znth i values 0 = d.

Definition PrefixDividingIndex
    (values : list Z) (d processed i : Z) : Prop :=
  0 <= i < processed /\ (Znth i values 0 | d).

Definition DivisorScanState
    (values : list Z) (d processed present count acc : Z) : Prop :=
  (present = 0 \/ present = 1) /\
  (present = 1 <-> PrefixContains values processed d) /\
  count = #(PrefixDividingIndex values d processed) /\
  exists exact,
    LeastCommonOfChosen values
      (PrefixDividingIndex values d processed) exact /\
    acc = if exact <=? d then exact else d + 1.

Definition FullDividingIndex
    (values : list Z) (d i : Z) : Prop :=
  0 <= i < Zlength values /\ (Znth i values 0 | d).

Definition DivisorCandidateCount
    (values : list Z) (d count : Z) : Prop :=
  ~ In d values /\
  count = #(FullDividingIndex values d) /\
  LeastCommonOfChosen values (FullDividingIndex values d) d.

Definition EnumeratedDivisor
    (mx q z d : Z) : Prop :=
  (exists r,
      1 <= r < q /\
      r * r <= mx /\
      mx mod r = 0 /\
      (d = r \/ d = mx / r)) \/
  (mx mod q = 0 /\ q * q <= mx /\
   ((1 <= z /\ d = q) \/ (2 <= z /\ d = mx / q))).

Definition EnumeratedScore
    (values : list Z) (mx q z score : Z) : Prop :=
  score = 0 \/
  exists d,
    EnumeratedDivisor mx q z d /\
    DivisorCandidateCount values d score.

Definition DivisorBestState
    (values : list Z) (mx q z ans : Z) : Prop :=
  max_value_of_subset Z.le
    (EnumeratedScore values mx q z)
    (fun score => score) ans.

Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Psatz.
Require Import Coq.ZArith.Zquot.
Lemma gcd_mod_step_nonnegative__gcd_arithmetic :
  forall a b, 0 < b -> Z.gcd b (Z.rem a b) = Z.gcd a b.
Proof.
  intros a b Hb.
  transitivity (Z.gcd (Z.rem a b) b).
  - apply Z.gcd_comm.
  - transitivity (Z.gcd b a).
    + apply Z.gcd_rem. lia.
    + apply Z.gcd_comm.
Qed.
Lemma gcd_positive_bounds__lcm_cap_contract :
  forall a b : Z, 1 <= a -> 1 <= b ->
    1 <= Z.gcd a b /\ Z.gcd a b <= b /\ (Z.gcd a b | a).
Proof.
  intros a b Ha Hb.
  pose proof (Z.gcd_nonneg a b) as Hg_nonneg.
  assert (Hg_nonzero : Z.gcd a b <> 0).
  { intro Hg_zero.
    apply Z.gcd_eq_0_l in Hg_zero.
    lia. }
  assert (Hg_pos : 0 < Z.gcd a b) by lia.
  split; [lia |].
  split.
  - apply Z.divide_pos_le; [lia | apply Z.gcd_divide_r].
  - apply Z.gcd_divide_l.
Qed.
Lemma lcm_as_gcd_quotient_product__lcm_cap_contract :
  forall a b : Z, 1 <= a -> 1 <= b ->
    Z.lcm a b = (a ÷ Z.gcd a b) * b.
Proof.
  intros a b Ha Hb.
  destruct (gcd_positive_bounds__lcm_cap_contract a b Ha Hb)
    as [Hg_pos [Hg_le_b Hg_div_a]].
  assert (Hg_nonzero : Z.gcd a b <> 0) by lia.
  unfold Z.lcm.
  rewrite Z.abs_eq.
  - rewrite <- Z.gcd_div_swap.
    rewrite <- Z.quot_div_exact; [reflexivity | exact Hg_nonzero | exact Hg_div_a].
  - assert (Hb_div_pos : 0 < b / Z.gcd a b).
    { apply Z.div_str_pos. lia. }
    nia.
Qed.
Lemma copy_max_state_step_high__copy_loop :
  forall input copied processed mx,
    0 <= processed < Zlength input ->
    CopyMaxState input copied processed mx ->
    Znth processed input 0 > mx ->
    CopyMaxState input (copied ++ Znth processed input 0 :: nil)
      (processed + 1) (Znth processed input 0).
Proof.
  intros input copied processed mx Hbounds [Hcopied Hstate] Hhigh.
  unfold CopyMaxState.
  split.
  - rewrite Hcopied.
    rewrite (sublist_split 0 (processed + 1) processed input) by lia.
    rewrite (sublist_single 0 processed input) by lia.
    reflexivity.
  - right.
    split; [lia |].
    unfold max_value_of_subset, max_object_of_subset.
    exists processed.
    split.
    + split.
      * change (0 <= processed < processed + 1).
        lia.
      *
      intros b Hb.
      change (0 <= b < processed + 1) in Hb.
      destruct (Z_lt_ge_dec b processed) as [Hlt | Hge].
      -- destruct Hstate as [[Hzero _] | [_ Hmax]].
         ++ lia.
         ++ unfold max_value_of_subset, max_object_of_subset in Hmax.
            destruct Hmax as [w [[_ Hupper] Hw]].
            specialize (Hupper b ltac:(change (0 <= b < processed); lia)).
            lia.
      -- assert (b = processed) by lia.
         subst b.
         lia.
    + reflexivity.
Qed.
Lemma copy_max_state_step_low__copy_loop :
  forall input copied processed mx,
    0 <= processed < Zlength input ->
    1 <= Znth processed input 0 ->
    CopyMaxState input copied processed mx ->
    Znth processed input 0 <= mx ->
    CopyMaxState input (copied ++ Znth processed input 0 :: nil)
      (processed + 1) mx.
Proof.
  intros input copied processed mx Hbounds Hpositive [Hcopied Hstate] Hlow.
  unfold CopyMaxState.
  split.
  - rewrite Hcopied.
    rewrite (sublist_split 0 (processed + 1) processed input) by lia.
    rewrite (sublist_single 0 processed input) by lia.
    reflexivity.
  - right.
    split; [lia |].
    destruct Hstate as [[Hzero Hmx] | [Hprocessed Hmax]].
    + lia.
    + unfold max_value_of_subset, max_object_of_subset in *.
      destruct Hmax as [w [[Hw Hupper] Hwvalue]].
      exists w.
      split.
      * split.
        -- change (0 <= w < processed + 1).
           change (0 <= w < processed) in Hw.
           lia.
        --
        intros b Hb.
        change (0 <= b < processed + 1) in Hb.
        destruct (Z_lt_ge_dec b processed) as [Hlt | Hge].
        ++ apply Hupper.
           change (0 <= b < processed).
           lia.
        ++ assert (b = processed) by lia.
           subst b.
           lia.
      * exact Hwvalue.
Qed.
Lemma least_common_empty_is_one__copy_exit :
  forall values,
    LeastCommonOfChosen values (fun i : Z => 0 <= i < 0) 1.
Proof.
  intros values.
  unfold LeastCommonOfChosen, min_value_of_subset, min_object_of_subset.
  exists 1.
  split.
  - split.
    + split.
      * lia.
      * unfold CommonMultipleOfChosen.
        intros i Hi.
        lia.
    + intros candidate Hcandidate.
      destruct Hcandidate as [_ _].
      apply Z.divide_1_l.
  - reflexivity.
Qed.
Lemma copy_max_state_complete__copy_exit :
  forall input copied processed mx,
    processed = Zlength input ->
    1 <= processed ->
    CopyMaxState input copied processed mx ->
    (forall k, 0 <= k < processed ->
       1 <= Znth k input 0 /\ Znth k input 0 <= 1000000000) ->
    copied = input /\
    Zlength copied = processed /\
    (forall k, 0 <= k < processed ->
       1 <= Znth k copied 0 /\ Znth k copied 0 <= 1000000000) /\
    1 <= mx.
Proof.
  intros input copied processed mx Hlength Hpositive Hstate Hbounds.
  unfold CopyMaxState in Hstate.
  destruct Hstate as [Hcopied [Hzero | Hnonzero]].
  - lia.
  - destruct Hnonzero as [_ Hmax].
    destruct Hmax as [index [[[Hindex0 Hindex1] Hgreatest] Hvalue]].
    assert (Hcopied_input : copied = input).
    {
      rewrite Hcopied.
      apply sublist_self.
      exact Hlength.
    }
    assert (Hmx_positive : 1 <= mx).
    {
      specialize (Hbounds index (conj Hindex0 Hindex1)).
      destruct Hbounds as [Hlower _].
      simpl in Hvalue.
      lia.
    }
    rewrite Hcopied_input.
    split.
    + reflexivity.
    + split.
      * symmetry. exact Hlength.
      * split.
        -- exact Hbounds.
        -- exact Hmx_positive.
Qed.
Lemma least_common_exact_extend__lcm_prefix :
  forall values processed exact,
    0 <= processed ->
    LeastCommonOfChosen values (fun i : Z => 0 <= i < processed) exact ->
    1 <= Znth processed values 0 ->
    LeastCommonOfChosen values (fun i : Z => 0 <= i < processed + 1)
      (Z.lcm exact (Znth processed values 0)).
Proof.
  intros values processed exact Hprocessed Hleast Hvalue.
  unfold LeastCommonOfChosen, min_value_of_subset in *.
  destruct Hleast as [old [[Hold_member Hold_min] Hold_eq]].
  subst old.
  exists (Z.lcm exact (Znth processed values 0)).
  split.
  - split.
    + split.
      * pose proof (Z.lcm_nonneg exact (Znth processed values 0)).
        assert (Z.lcm exact (Znth processed values 0) <> 0).
        { intro Hz.
          apply Z.lcm_eq_0 in Hz.
          destruct Hold_member as [Hexact _].
          lia. }
        lia.
      * unfold CommonMultipleOfChosen in *.
        intros j Hj.
        destruct (Z.lt_ge_cases j processed) as [Hlt | Hge].
        -- eapply Z.divide_trans.
           ++ apply Hold_member. lia.
           ++ apply Z.divide_lcm_l.
        -- assert (j = processed) by lia. subst j.
           apply Z.divide_lcm_r.
    + intros candidate [Hcandidate_pos Hcandidate_common].
      apply Z.lcm_divide_iff.
      split.
      * apply Hold_min. split; [exact Hcandidate_pos |].
        unfold CommonMultipleOfChosen in *.
        intros j Hj. apply Hcandidate_common. lia.
      * apply Hcandidate_common. lia.
  - reflexivity.
Qed.
Lemma least_common_prefix_extend__lcm_prefix :
  forall values processed cap acc next,
    0 <= processed ->
    1 <= cap ->
    1 <= Znth processed values 0 ->
    LcmPrefixState values processed cap acc ->
    LcmCapValue acc (Znth processed values 0) cap next ->
    LcmPrefixState values (processed + 1) cap next.
Proof.
  intros values processed cap acc next Hprocessed Hcap_pos Hvalue Hstate Hcap.
  destruct Hstate as [exact [Hexact Hacc]].
  assert (Hexact_pos : 1 <= exact).
  { pose proof Hexact as Hleast.
    unfold LeastCommonOfChosen, min_value_of_subset in Hleast.
    destruct Hleast as [x [[Hxmember Hxmin] Hxeq]].
    destruct Hxmember as [Hxpos Hxcommon].
    subst x. exact Hxpos. }
  exists (Z.lcm exact (Znth processed values 0)).
  split.
  - apply least_common_exact_extend__lcm_prefix; assumption.
  - unfold LcmCapValue in Hcap.
    destruct (exact <=? cap) eqn:Hec.
    + apply Z.leb_le in Hec.
      subst acc. exact Hcap.
    + apply Z.leb_gt in Hec.
      subst acc.
      assert (Hnew_pos : 0 < Z.lcm exact (Znth processed values 0)).
      { pose proof (Z.lcm_nonneg exact (Znth processed values 0)).
        assert (Z.lcm exact (Znth processed values 0) <> 0).
        { intro Hz. apply Z.lcm_eq_0 in Hz. lia. }
        lia. }
      assert (Hexact_new : exact <= Z.lcm exact (Znth processed values 0)).
      { apply Z.divide_pos_le; [exact Hnew_pos | apply Z.divide_lcm_l]. }
      assert (Hnew_cmp : (Z.lcm exact (Znth processed values 0) <=? cap) = false).
      { apply Z.leb_gt. lia. }
      rewrite Hnew_cmp.
      assert (Hcapped_pos : 0 < Z.lcm (cap + 1) (Znth processed values 0)).
      { pose proof (Z.lcm_nonneg (cap + 1) (Znth processed values 0)).
        assert (Z.lcm (cap + 1) (Znth processed values 0) <> 0).
        { intro Hz. apply Z.lcm_eq_0 in Hz. lia. }
        lia. }
      assert (Hcapped_le : cap + 1 <= Z.lcm (cap + 1) (Znth processed values 0)).
      { apply Z.divide_pos_le; [exact Hcapped_pos | apply Z.divide_lcm_l]. }
      assert (Hcapped_cmp :
        (Z.lcm (cap + 1) (Znth processed values 0) <=? cap) = false).
      { apply Z.leb_gt. lia. }
      rewrite Hcapped_cmp in Hcap.
      exact Hcap.
Qed.
Lemma permutation_preserves_pointwise_bounds__lcm_prefix :
  forall values sorted n lower upper,
    Permutation values sorted ->
    Zlength values = n ->
    Zlength sorted = n ->
    (forall i, 0 <= i < n -> lower <= Znth i values 0 <= upper) ->
    forall i, 0 <= i < n -> lower <= Znth i sorted 0 <= upper.
Proof.
  intros values sorted n lower upper Hperm Hvalues Hsorted Hbounds i Hi.
  assert (Hin_sorted : In (Znth i sorted 0) sorted).
  { unfold Znth. apply nth_In. rewrite Zlength_correct in Hsorted. lia. }
  assert (Hin_values : In (Znth i sorted 0) values).
  { eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hin_sorted]. }
  destruct (In_nth values (Znth i sorted 0) 0 Hin_values)
    as [j [Hj Hnth]].
  specialize (Hbounds (Z.of_nat j)).
  assert (0 <= Z.of_nat j < n).
  { rewrite <- Hvalues, Zlength_correct. lia. }
  specialize (Hbounds H).
  unfold Znth in Hbounds.
  rewrite Nat2Z.id in Hbounds.
  rewrite Hnth in Hbounds.
  exact Hbounds.
Qed.
Lemma set_card_Z_as_sum__lcm_prefix :
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
  { induction zs as [|z zs IH]; simpl; [reflexivity |].
    destruct (prop_dec (P z)); simpl.
    - exact (f_equal (fun n : Z => 1 + n) IH).
    - exact IH. }
  apply Hfilter.
Qed.
Lemma set_card_Z_range_upper_bound__lcm_prefix :
  forall (low high : Z) (P : Z -> Prop),
    low <= high ->
    #(fun z : Z => low <= z < high /\ P z) <= high - low.
Proof.
  intros low high P Hrange.
  rewrite set_card_Z_as_sum__lcm_prefix.
  eapply Z.le_trans.
  - apply SumLib.ZRange.sum_Z_range_upper_bound with (b := 1).
    + exact Hrange.
    + intros z Hz. destruct (prop_dec (P z)); lia.
  - lia.
Qed.
Lemma set_card_Z_range_exact__lcm_prefix :
  forall low high : Z,
    low <= high ->
    #(fun z : Z => low <= z < high) = high - low.
Proof.
  intros low high Hrange.
  unfold set_card.
  change (SumLib.Sum.sum (fun z : Z => low <= z < high) (fun _ => 1) =
    high - low).
  rewrite SumLib.ZRange.sum_Z_range_const by exact Hrange.
  lia.
Qed.
Lemma full_lcm_outside_array_spec__lcm_prefix :
  forall original copied n mx all,
    n = Zlength original ->
    1 <= n ->
    1 <= mx ->
    CopyMaxState original copied n mx ->
    LcmPrefixState copied n mx all ->
    all <> mx ->
    Spec original n.
Proof.
  intros original copied n mx all Hn Hnpos Hmx Hcopy Hprefix Hneq.
  destruct Hcopy as [Hcopied Hmaxcase].
  assert (Hcopied_eq : copied = original).
  { rewrite Hcopied, Hn. apply sublist_self. reflexivity. }
  destruct Hmaxcase as [[Hzero _] | [Hnzero Hmax]]; [lia |].
  destruct Hprefix as [exact [Hexact Hacc]].
  assert (Hexact_pos : 1 <= exact).
  { pose proof Hexact as Hleast.
    unfold LeastCommonOfChosen, min_value_of_subset in Hleast.
    destruct Hleast as [x [[Hxmember Hxmin] Hxeq]].
    destruct Hxmember as [Hxpos Hxcommon]. subst x. exact Hxpos. }
  destruct Hmax as [max_index [[Hmax_index Hmax_bound] Hmax_value]].
  assert (Hmx_divides : (mx | exact)).
  { unfold LeastCommonOfChosen, min_value_of_subset in Hexact.
    destruct Hexact as [x [[[Hxpos Hxcommon] Hxmin] Hxeq]].
    subst x. unfold CommonMultipleOfChosen in Hxcommon.
    rewrite Hcopied_eq in Hxcommon.
    rewrite <- Hmax_value. apply Hxcommon. exact Hmax_index. }
  assert (Hmx_le : mx <= exact).
  { apply Z.divide_pos_le; [lia | exact Hmx_divides]. }
  assert (Hexact_gt : mx < exact).
  { destruct (Z.eq_dec exact mx) as [Heq | Hne].
    - subst exact.
      assert (Hcmp : (mx <=? mx) = true) by (apply Z.leb_le; lia).
      rewrite Hcmp in Hacc. contradiction.
    - lia. }
  assert (Hexact_notin : ~ In exact original).
  { intro Hin.
    destruct (In_nth original exact 0 Hin) as [j [Hj Hnth]].
    specialize (Hmax_bound (Z.of_nat j)).
    assert (0 <= Z.of_nat j < n).
    { rewrite Hn, Zlength_correct. lia. }
    specialize (Hmax_bound H).
    rewrite Hmax_value in Hmax_bound.
    unfold Znth in Hmax_bound.
    rewrite Nat2Z.id, Hnth in Hmax_bound.
    lia. }
  unfold Spec, max_value_of_subset_with_default.
  left. split.
  - unfold max_value_of_subset.
    exists ((fun i : Z => 0 <= i < Zlength original), n).
    split.
    + unfold max_object_of_subset. split.
      * split.
        -- unfold SpecialChoice. split.
           ++ intros i Hi. exact Hi.
           ++ exists exact. split.
              ** rewrite <- Hn. rewrite <- Hcopied_eq. exact Hexact.
              ** exact Hexact_notin.
        -- simpl. rewrite Hn.
           symmetry.
           rewrite set_card_Z_as_sum__lcm_prefix.
           transitivity
             (SumLib.Sum.sum
               (fun z : Z => 0 <= z < Zlength original) (fun _ => 1)).
           ++ apply SumLib.Sum.sum_ext. intros z Hz.
              destruct (prop_dec (0 <= z < Zlength original));
                [reflexivity | contradiction].
           ++ rewrite SumLib.ZRange.sum_Z_range_const by lia. lia.
      * intros [indices count] Hcandidate. simpl.
        destruct Hcandidate as [Hspecial Hcount].
        simpl in Hcount.
        rewrite Hcount.
        rewrite Hn.
        pose proof
          (set_card_Z_range_upper_bound__lcm_prefix
            0 (Zlength original) indices ltac:(lia)).
        lia.
    + reflexivity.
  - lia.
Qed.
Lemma copy_max_full_upper__lcm_prefix :
  forall original copied n mx i,
    0 <= i < n ->
    CopyMaxState original copied n mx ->
    Znth i copied 0 <= mx.
Proof.
  intros original copied n mx i Hi Hcopy.
  destruct Hcopy as [Hcopied Hmaxcase].
  destruct Hmaxcase as [[Hzero Hmx] | [Hnpos Hmax]]; [lia |].
  destruct Hmax as [max_index [[Hmax_index Hmax_bound] Hmax_value]].
  specialize (Hmax_bound i Hi).
  rewrite Hmax_value in Hmax_bound.
  rewrite Hcopied, Znth_sublist0 by lia.
  exact Hmax_bound.
Qed.
Lemma set_card_empty__divisor_init :
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
Lemma divisor_best_initial__divisor_init :
  forall values mx, DivisorBestState values mx 1 0 0.
Proof.
  intros values mx.
  unfold DivisorBestState, max_value_of_subset.
  exists 0.
  split.
  - unfold max_object_of_subset.
    split.
    + unfold EnumeratedScore. left. reflexivity.
    + intros score Hscore.
      unfold EnumeratedScore in Hscore.
      destruct Hscore as [Hscore | [d [Hd _]]].
      * lia.
      * unfold EnumeratedDivisor in Hd.
        destruct Hd as [[r [Hr _]] | [_ [_ [[Hz _] | [Hz _]]]]]; lia.
  - reflexivity.
Qed.
Lemma divisor_scan_initial__divisor_init :
  forall values d, 1 <= d -> DivisorScanState values d 0 0 0 1.
Proof.
  intros values d Hd.
  unfold DivisorScanState, PrefixContains, PrefixDividingIndex.
  split.
  - left. reflexivity.
  - split.
    + split.
      * intro H. discriminate.
      * intros [i [Hi _]]. lia.
    + split.
      * symmetry.
        apply set_card_empty__divisor_init.
        intros i [Hi _]. lia.
      * exists 1.
        split.
        -- unfold LeastCommonOfChosen, min_value_of_subset.
           exists 1.
           split.
           ++ unfold min_object_of_subset.
              split.
              ** split; [lia |].
                 unfold CommonMultipleOfChosen.
                 intros i Hi. lia.
              ** intros candidate _. exists candidate. lia.
           ++ reflexivity.
        -- apply Z.leb_le in Hd.
           rewrite Hd. reflexivity.
Qed.
Lemma two_divisors_bounds__divisor_init :
  forall mx q,
    1 <= q -> q * q <= mx -> Z.rem mx q = 0 ->
    (1 <= q <= mx) /\ (1 <= Z.quot mx q <= mx).
Proof.
  intros mx q Hq Hsq Hrem.
  assert (Hq0 : q <> 0) by lia.
  pose proof (Z.quot_rem mx q Hq0) as Hquot.
  rewrite Hrem in Hquot.
  split; nia.
Qed.
Lemma set_card_Z_as_sum__divisor_scan :
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
Lemma set_card_Z_extend_true__divisor_scan :
  forall (low high : Z) (P : Z -> Prop),
    low <= high -> P high ->
    #(fun z : Z => low <= z < high + 1 /\ P z) =
    #(fun z : Z => low <= z < high /\ P z) + 1.
Proof.
  intros low high P Hrange HP.
  rewrite !set_card_Z_as_sum__divisor_scan.
  rewrite SumLib.ZRange.sum_Z_range_extend_right by exact Hrange.
  destruct (prop_dec (P high)) as [_ | Hnot]; [lia | contradiction].
Qed.
Lemma set_card_Z_extend_false__divisor_scan :
  forall (low high : Z) (P : Z -> Prop),
    low <= high -> ~ P high ->
    #(fun z : Z => low <= z < high + 1 /\ P z) =
    #(fun z : Z => low <= z < high /\ P z).
Proof.
  intros low high P Hrange HP.
  rewrite !set_card_Z_as_sum__divisor_scan.
  rewrite SumLib.ZRange.sum_Z_range_extend_right by exact Hrange.
  destruct (prop_dec (P high)) as [Hp | _]; [contradiction | lia].
Qed.
Lemma least_common_indices_ext__divisor_scan :
  forall (values : list Z) (left right : Z -> Prop) exact,
    (forall i, left i <-> right i) ->
    LeastCommonOfChosen values left exact ->
    LeastCommonOfChosen values right exact.
Proof.
  intros values left right exact Hext Hleast.
  unfold LeastCommonOfChosen, min_value_of_subset,
    min_object_of_subset in *.
  destruct Hleast as [chosen [[[Hpositive Hcommon] Hminimal] Heq]].
  exists chosen. split; [split; [split |] | exact Heq].
  - exact Hpositive.
  - unfold CommonMultipleOfChosen in *.
    intros i Hi. apply Hcommon. apply Hext. exact Hi.
  - intros candidate [Hpositive' Hcommon'].
    apply Hminimal. split; [exact Hpositive' |].
    unfold CommonMultipleOfChosen in *.
    intros i Hi. apply Hcommon'. apply Hext. exact Hi.
Qed.
Lemma least_common_divides_common__divisor_scan :
  forall (values : list Z) (indices : Z -> Prop) exact candidate,
    LeastCommonOfChosen values indices exact ->
    1 <= candidate ->
    CommonMultipleOfChosen values indices candidate ->
    (exact | candidate).
Proof.
  intros values indices exact candidate Hleast Hpositive Hcommon.
  unfold LeastCommonOfChosen, min_value_of_subset,
    min_object_of_subset in Hleast.
  destruct Hleast as [chosen [[_ Hminimal] Heq]].
  cbn in Heq. subst chosen.
  apply Hminimal. split; assumption.
Qed.
Lemma least_common_extend__divisor_scan :
  forall (values : list Z) d processed exact value,
    0 <= processed ->
    1 <= exact ->
    1 <= value ->
    value = Znth processed values 0 ->
    (value | d) ->
    LeastCommonOfChosen values
      (PrefixDividingIndex values d processed) exact ->
    LeastCommonOfChosen values
      (PrefixDividingIndex values d (processed + 1))
      (Z.lcm exact value).
Proof.
  intros values d processed exact value Hprocessed Hexact Hvalue
    Hvalue_eq Hvalue_div Hleast.
  unfold LeastCommonOfChosen, min_value_of_subset,
    min_object_of_subset in *.
  destruct Hleast as [chosen [[[Hchosen_pos Hchosen_common]
    Hchosen_min] Hchosen_eq]].
  cbn in Hchosen_eq. subst chosen.
  exists (Z.lcm exact value). split; [split; [split |] | reflexivity].
  - pose proof (Z.lcm_nonneg exact value) as Hnonneg.
    assert (Z.lcm exact value <> 0).
    {
      intro Hz.
      apply (proj1 (Z.lcm_eq_0 exact value)) in Hz.
      lia.
    }
    lia.
  - unfold CommonMultipleOfChosen in *.
    intros j Hj.
    unfold PrefixDividingIndex in Hj.
    destruct Hj as [[Hj0 Hjhigh] Hjdiv].
    destruct (Z.eq_dec j processed) as [-> | Hneq].
    + rewrite <- Hvalue_eq. apply Z.divide_lcm_r.
    + apply Z.divide_trans with exact.
      * apply Hchosen_common.
        unfold PrefixDividingIndex. split; [lia | exact Hjdiv].
      * apply Z.divide_lcm_l.
  - intros candidate [Hcandidate_pos Hcandidate_common].
    apply (proj2 (Z.lcm_divide_iff exact value candidate)). split.
    + apply Hchosen_min. split; [exact Hcandidate_pos |].
      unfold CommonMultipleOfChosen in *.
      intros j Hj. apply Hcandidate_common.
      unfold PrefixDividingIndex in *.
      destruct Hj as [Hbounds Hdiv]. split; [lia | exact Hdiv].
    + unfold CommonMultipleOfChosen in Hcandidate_common.
      rewrite Hvalue_eq.
      apply Hcandidate_common.
      unfold PrefixDividingIndex. split; [lia |].
      rewrite <- Hvalue_eq. exact Hvalue_div.
Qed.
Lemma divisor_scan_step_dividing__divisor_scan :
  forall (values : list Z) d processed present count acc out new_present,
    0 <= processed ->
    1 <= d ->
    1 <= Znth processed values 0 ->
    (Znth processed values 0 | d) ->
    LcmCapValue acc (Znth processed values 0) d out ->
    DivisorScanState values d processed present count acc ->
    ((Znth processed values 0 = d /\ new_present = 1) \/
     (Znth processed values 0 <> d /\ new_present = present)) ->
    DivisorScanState values d (processed + 1) new_present (count + 1) out.
Proof.
  intros values d processed present count acc out new_present
    Hprocessed Hd Hvalue Hdiv Hcap Hstate Hpresent_case.
  destruct Hstate as [Hpresent_range [Hpresent_iff
    [Hcount [exact [Hleast Hacc]]]]].
  assert (Hd_common : CommonMultipleOfChosen values
    (PrefixDividingIndex values d processed) d).
  {
    unfold CommonMultipleOfChosen, PrefixDividingIndex.
    intros j [_ Hjdiv]. exact Hjdiv.
  }
  assert (Hexact_div_d : (exact | d)).
  {
    eapply least_common_divides_common__divisor_scan;
      [exact Hleast | exact Hd | exact Hd_common].
  }
  assert (Hexact_le_d : exact <= d).
  { apply Z.divide_pos_le; [lia | exact Hexact_div_d]. }
  assert (Hexact_leb : (exact <=? d) = true).
  { apply Z.leb_le. exact Hexact_le_d. }
  rewrite Hexact_leb in Hacc. subst acc.
  unfold LcmCapValue in Hcap.
  split.
  - destruct Hpresent_case as [[_ ->] | [_ ->]]; [lia | exact Hpresent_range].
  - split.
    + destruct Hpresent_case as [[Heq ->] | [Hneq ->]].
      * split.
        -- intros _. unfold PrefixContains.
           exists processed. split; [lia | exact Heq].
        -- intros _. reflexivity.
      * rewrite Hpresent_iff. split.
        -- intros [j [Hbounds Hj]].
           unfold PrefixContains. exists j. split; [lia | exact Hj].
        -- intros [j [[Hj0 Hjhigh] Hj]].
           unfold PrefixContains.
           destruct (Z.eq_dec j processed) as [-> | Hjne].
           ++ contradiction.
           ++ exists j. split; [lia | exact Hj].
    + split.
      * unfold PrefixDividingIndex in *.
        rewrite (set_card_Z_extend_true__divisor_scan 0 processed
          (fun j => (Znth j values 0 | d))) by assumption.
        lia.
      * exists (Z.lcm exact (Znth processed values 0)). split.
        -- eapply least_common_extend__divisor_scan;
             [exact Hprocessed | | exact Hvalue | reflexivity |
              exact Hdiv | exact Hleast].
           unfold LeastCommonOfChosen, min_value_of_subset,
             min_object_of_subset in Hleast.
           destruct Hleast as [chosen [[[Hpositive _] _] Heq]].
           cbn in Heq. lia.
        -- exact Hcap.
Qed.
Lemma divisor_scan_step_nondividing__divisor_scan :
  forall (values : list Z) d processed present count acc,
    0 <= processed ->
    Znth processed values 0 <> d ->
    ~ (Znth processed values 0 | d) ->
    DivisorScanState values d processed present count acc ->
    DivisorScanState values d (processed + 1) present count acc.
Proof.
  intros values d processed present count acc Hprocessed Hneq Hnotdiv Hstate.
  destruct Hstate as [Hpresent_range [Hpresent_iff
    [Hcount [exact [Hleast Hacc]]]]].
  split; [exact Hpresent_range |]. split.
  - rewrite Hpresent_iff. split.
    + intros [j [Hbounds Hj]].
      unfold PrefixContains. exists j. split; [lia | exact Hj].
    + intros [j [[Hj0 Hjhigh] Hj]].
      unfold PrefixContains.
      destruct (Z.eq_dec j processed) as [-> | Hjne].
      * contradiction.
      * exists j. split; [lia | exact Hj].
  - split.
    + unfold PrefixDividingIndex in *.
      rewrite (set_card_Z_extend_false__divisor_scan 0 processed
        (fun j => (Znth j values 0 | d))) by assumption.
      exact Hcount.
    + exists exact. split; [| exact Hacc].
      eapply least_common_indices_ext__divisor_scan;
        [| exact Hleast].
      intros j. unfold PrefixDividingIndex.
      split.
      * intros [[Hj0 Hjhigh] Hjdiv].
        split; [lia | exact Hjdiv].
      * intros [[Hj0 Hjhigh] Hjdiv].
        destruct (Z.eq_dec j processed) as [-> | Hjne].
        -- contradiction.
        -- split; [lia | exact Hjdiv].
Qed.
Lemma positive_divisor_le__divisor_scan :
  forall x d : Z,
    1 <= x -> 1 <= d -> Z.rem d x = 0 ->
    (x | d) /\ x <= d.
Proof.
  intros x d Hx Hd Hmod.
  assert (Hdiv : (x | d)).
  {
    pose proof (Z.rem_divide d x ltac:(lia)) as Hiff.
    apply (proj1 Hiff). exact Hmod.
  }
  split; [exact Hdiv |].
  apply Z.divide_pos_le; [lia | exact Hdiv].
Qed.
Lemma Znth_In_bounds__candidate_update : forall (xs : list Z) i,
  0 <= i < Zlength xs -> In (Znth i xs 0) xs.
Proof.
  intros xs i Hi. unfold Znth. apply nth_In.
  replace (length xs) with (Z.to_nat (Zlength xs)).
  - apply Z2Nat.inj_lt; lia.
  - rewrite Zlength_correct, Nat2Z.id. reflexivity.
Qed.
Lemma enumerated_divisor_step__candidate_update : forall mx q z d x,
  0 <= z < 2 -> mx mod q = 0 -> q * q <= mx ->
  d = Znth z (q :: (mx / q) :: nil) 0 ->
  (EnumeratedDivisor mx q (z + 1) x <->
   EnumeratedDivisor mx q z x \/ x = d).
Proof.
  intros mx q z d x Hz Hmod Hsq Hd.
  assert (z = 0 \/ z = 1) as [-> | ->] by lia.
  - rewrite Znth0_cons in Hd. subst d.
    unfold EnumeratedDivisor. simpl. tauto.
  - rewrite Znth_cons in Hd by lia. rewrite Znth0_cons in Hd. subst d.
    unfold EnumeratedDivisor. simpl. intuition; lia.
Qed.
Lemma enumerated_score_step__candidate_update : forall values mx q z d score,
  0 <= z < 2 -> mx mod q = 0 -> q * q <= mx ->
  d = Znth z (q :: (mx / q) :: nil) 0 ->
  (EnumeratedScore values mx q (z + 1) score <->
   EnumeratedScore values mx q z score \/
   DivisorCandidateCount values d score).
Proof.
  intros values mx q z d score Hz Hmod Hsq Hd.
  unfold EnumeratedScore. split.
  - intros [Hzero | [d' [Henum Hcandidate]]].
    + left. left. exact Hzero.
    + apply (proj1 (enumerated_divisor_step__candidate_update
        mx q z d d' Hz Hmod Hsq Hd)) in Henum.
      destruct Henum as [Hold | Heq].
      * left. right. exists d'. auto.
      * right. subst d'. exact Hcandidate.
  - intros [[Hzero | [d' [Henum Hcandidate]]] | Hcandidate].
    + left. exact Hzero.
    + right. exists d'. split; [|exact Hcandidate].
      apply (proj2 (enumerated_divisor_step__candidate_update
        mx q z d d' Hz Hmod Hsq Hd)). auto.
    + right. exists d. split; [|exact Hcandidate].
      apply (proj2 (enumerated_divisor_step__candidate_update
        mx q z d d Hz Hmod Hsq Hd)). auto.
Qed.
Lemma divisor_candidate_count_unique__candidate_update : forall values d x y,
  DivisorCandidateCount values d x ->
  DivisorCandidateCount values d y -> x = y.
Proof.
  intros values d x y [_ [Hx _]] [_ [Hy _]]. lia.
Qed.
Lemma divisor_best_add_score__candidate_update : forall values mx q z d old score,
  0 <= z < 2 -> mx mod q = 0 -> q * q <= mx ->
  d = Znth z (q :: (mx / q) :: nil) 0 ->
  DivisorBestState values mx q z old ->
  DivisorCandidateCount values d score -> old < score ->
  DivisorBestState values mx q (z + 1) score.
Proof.
  intros values mx q z d old score Hz Hmod Hsq Hd Hbest Hcandidate Hlt.
  unfold DivisorBestState, max_value_of_subset, max_object_of_subset in *.
  destruct Hbest as [best [[Hbest_mem Hbest_max] Hbest_eq]]. subst best.
  exists score. split; [split | reflexivity].
  - apply (proj2 (enumerated_score_step__candidate_update
      values mx q z d score Hz Hmod Hsq Hd)). right. exact Hcandidate.
  - intros other Hother.
    apply (proj1 (enumerated_score_step__candidate_update
      values mx q z d other Hz Hmod Hsq Hd)) in Hother.
    destruct Hother as [Hold | Hnew].
    + specialize (Hbest_max other Hold). lia.
    + assert (other = score) by
        (eapply divisor_candidate_count_unique__candidate_update; eauto).
      lia.
Qed.
Lemma divisor_best_skip_score__candidate_update : forall values mx q z d old,
  0 <= z < 2 -> mx mod q = 0 -> q * q <= mx ->
  d = Znth z (q :: (mx / q) :: nil) 0 ->
  DivisorBestState values mx q z old ->
  (forall score, DivisorCandidateCount values d score -> score <= old) ->
  DivisorBestState values mx q (z + 1) old.
Proof.
  intros values mx q z d old Hz Hmod Hsq Hd Hbest Hbound.
  unfold DivisorBestState, max_value_of_subset, max_object_of_subset in *.
  destruct Hbest as [best [[Hbest_mem Hbest_max] Hbest_eq]]. subst best.
  exists old. split; [split | reflexivity].
  - apply (proj2 (enumerated_score_step__candidate_update
      values mx q z d old Hz Hmod Hsq Hd)). left. exact Hbest_mem.
  - intros other Hother.
    apply (proj1 (enumerated_score_step__candidate_update
      values mx q z d other Hz Hmod Hsq Hd)) in Hother.
    destruct Hother as [Hold | Hnew].
    + exact (Hbest_max other Hold).
    + exact (Hbound other Hnew).
Qed.
Lemma In_Znth_exists__candidate_update : forall (xs : list Z) x,
  In x xs -> exists i, 0 <= i < Zlength xs /\ Znth i xs 0 = x.
Proof.
  intros xs x Hin.
  destruct (In_nth xs x 0 Hin) as [n [Hn Hnth]].
  exists (Z.of_nat n). split.
  - rewrite Zlength_correct. lia.
  - unfold Znth. rewrite Nat2Z.id. exact Hnth.
Qed.
Lemma full_common_iff_values__candidate_update : forall values d candidate,
  CommonMultipleOfChosen values (FullDividingIndex values d) candidate <->
  forall x, In x values -> (x | d) -> (x | candidate).
Proof.
  intros values d candidate. split.
  - intros Hcommon x Hin Hdiv.
    destruct (In_Znth_exists__candidate_update values x Hin)
      as [i [Hi Hx]].
    subst x. apply Hcommon. split; assumption.
  - intros Hvalues i [Hi Hdiv].
    apply Hvalues with (x := Znth i values 0).
    + apply Znth_In_bounds__candidate_update. exact Hi.
    + exact Hdiv.
Qed.
Lemma full_common_permutation__candidate_update : forall xs ys d candidate,
  Permutation xs ys ->
  CommonMultipleOfChosen xs (FullDividingIndex xs d) candidate <->
  CommonMultipleOfChosen ys (FullDividingIndex ys d) candidate.
Proof.
  intros xs ys d candidate Hperm.
  rewrite !full_common_iff_values__candidate_update.
  split; intros H x Hin Hdiv.
  - apply H with (x := x).
    + eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hin].
    + exact Hdiv.
  - apply H with (x := x).
    + eapply Permutation_in; eauto.
    + exact Hdiv.
Qed.
Lemma least_common_full_permutation__candidate_update : forall xs ys d candidate,
  Permutation xs ys ->
  LeastCommonOfChosen xs (FullDividingIndex xs d) candidate <->
  LeastCommonOfChosen ys (FullDividingIndex ys d) candidate.
Proof.
  intros xs ys d candidate Hperm.
  unfold LeastCommonOfChosen, min_value_of_subset, min_object_of_subset.
  split.
  - intros [best [[[Hpos Hcommon] Hleast] Heq]]. exists best. split.
    + split.
      * split; [exact Hpos |].
        apply (proj1 (full_common_permutation__candidate_update
          xs ys d best Hperm)); exact Hcommon.
      * intros other [Hother_pos Hother_common]. apply Hleast. split.
        -- exact Hother_pos.
        -- apply (proj2 (full_common_permutation__candidate_update
            xs ys d other Hperm)); exact Hother_common.
    + exact Heq.
  - intros [best [[[Hpos Hcommon] Hleast] Heq]]. exists best. split.
    + split.
      * split; [exact Hpos |].
        apply (proj2 (full_common_permutation__candidate_update
          xs ys d best Hperm)); exact Hcommon.
      * intros other [Hother_pos Hother_common]. apply Hleast. split.
        -- exact Hother_pos.
        -- apply (proj1 (full_common_permutation__candidate_update
            xs ys d other Hperm)); exact Hother_common.
    + exact Heq.
Qed.
Lemma set_card_Z_as_sum__candidate_update : forall low high (P : Z -> Prop),
  #(fun z : Z => low <= z < high /\ P z) =
  SumLib.Sum.sum (fun z : Z => low <= z < high)
    (fun z => if prop_dec (P z) then 1 else 0).
Proof.
  intros low high P. unfold set_card, SumLib.Sum.sum.
  cbn [finite_Z_range' finite_Z_range].
  assert (Hfilter : forall zs : list Z,
    fold_right (fun _ acc : Z => 1 + acc) 0
      (filter (fun z => if prop_dec (P z) then true else false) zs) =
    fold_right (fun z acc : Z =>
      (if prop_dec (P z) then 1 else 0) + acc) 0 zs).
  { induction zs as [|z zs IH]; simpl; [reflexivity|].
    destruct (prop_dec (P z)); simpl.
    - exact (f_equal (fun n : Z => 1 + n) IH).
    - exact IH. }
  apply Hfilter.
Qed.
Lemma full_dividing_card_cons__candidate_update : forall x xs d,
  #(FullDividingIndex (x :: xs) d) =
  (if prop_dec (x | d) then 1 else 0) + #(FullDividingIndex xs d).
Proof.
  intros x xs d. unfold FullDividingIndex.
  rewrite !set_card_Z_as_sum__candidate_update.
  exact (sum_Z_range_Znth_cons_indexed 0 x xs
    (fun _ v => if prop_dec (v | d) then 1 else 0)).
Qed.
Lemma full_dividing_card_permutation__candidate_update : forall xs ys d,
  Permutation xs ys ->
  #(FullDividingIndex xs d) = #(FullDividingIndex ys d).
Proof.
  intros xs ys d Hperm. induction Hperm.
  - reflexivity.
  - rewrite !full_dividing_card_cons__candidate_update. rewrite IHHperm.
    reflexivity.
  - repeat rewrite full_dividing_card_cons__candidate_update. lia.
  - etransitivity; eassumption.
Qed.
Lemma prefix_contains_full_iff__candidate_update : forall values processed d,
  processed = Zlength values ->
  (PrefixContains values processed d <-> In d values).
Proof.
  intros values processed d Hlen. subst processed. split.
  - intros [i [Hi Hd]]. rewrite <- Hd.
    apply Znth_In_bounds__candidate_update. exact Hi.
  - intros Hin. destruct (In_Znth_exists__candidate_update values d Hin)
      as [i [Hi Hd]]. exists i. auto.
Qed.
Lemma completed_scan_l_ineligible__candidate_update : forall values sorted d processed
    present count acc,
  Permutation values sorted -> processed = Zlength sorted ->
  present = 0 -> acc <> d ->
  DivisorScanState sorted d processed present count acc ->
  forall score, ~ DivisorCandidateCount values d score.
Proof.
  intros values sorted d processed present count acc Hperm Hprocessed
    Hpresent Hneq Hscan score Hcandidate.
  unfold DivisorScanState in Hscan.
  destruct Hscan as [_ [_ [_ [exact [Hexact Hacc_eq]]]]].
  destruct Hcandidate as [_ [_ Hcandidate]].
  rewrite Hprocessed in Hexact.
  pose proof (proj2 (least_common_full_permutation__candidate_update
    values sorted d exact Hperm) Hexact) as Hexact_values.
  unfold LeastCommonOfChosen, min_value_of_subset, min_object_of_subset
    in Hexact_values, Hcandidate.
  destruct Hexact_values as [a [[[Ha_pos Ha_common] Ha_min] Ha_eq]].
  destruct Hcandidate as [b [[[Hb_pos Hb_common] Hb_min] Hb_eq]].
  subst a b.
  pose proof (Ha_min d (conj Hb_pos Hb_common)) as Hexact_d.
  pose proof (Hb_min exact (conj Ha_pos Ha_common)) as Hd_exact.
  destruct (Z.divide_antisym exact d Hexact_d Hd_exact) as [Heq | Heq];
    [|lia].
  subst exact. destruct (d <=? d) eqn:Hle; lia.
Qed.
Lemma completed_scan_present_ineligible__candidate_update :
  forall values sorted d processed present count acc,
  Permutation values sorted -> processed = Zlength sorted ->
  present <> 0 ->
  DivisorScanState sorted d processed present count acc ->
  forall score, ~ DivisorCandidateCount values d score.
Proof.
  intros values sorted d processed present count acc Hperm Hprocessed
    Hnonzero Hscan score Hcandidate.
  unfold DivisorScanState in Hscan.
  destruct Hscan as [Hflag [Hcontains _]].
  assert (present = 1) as Hone by (destruct Hflag; lia).
  pose proof (proj1 Hcontains Hone) as Hprefix.
  pose proof (proj1 (prefix_contains_full_iff__candidate_update
    sorted processed d Hprocessed) Hprefix) as Hin_sorted.
  destruct Hcandidate as [Hnotin _]. apply Hnotin.
  eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hin_sorted].
Qed.
Lemma completed_scan_candidate__candidate_update : forall values sorted d processed
    present count acc,
  Permutation values sorted ->
  processed = Zlength sorted -> present = 0 -> acc = d ->
  DivisorScanState sorted d processed present count acc ->
  DivisorCandidateCount values d count.
Proof.
  intros values sorted d processed present count acc Hperm Hprocessed
    Hpresent Hacc Hscan.
  unfold DivisorScanState in Hscan.
  destruct Hscan as [_ [Hcontains [Hcount [exact [Hexact Hacc_eq]]]]].
  assert (Hnot_sorted : ~ In d sorted).
  { intro Hin.
    pose proof (proj2 (prefix_contains_full_iff__candidate_update
      sorted processed d Hprocessed) Hin) as Hprefix.
    pose proof (proj2 Hcontains Hprefix) as Hone. lia. }
  assert (Hexact_d : exact = d).
  { rewrite Hacc in Hacc_eq. destruct (exact <=? d) eqn:Hle.
    - symmetry. exact Hacc_eq.
    - lia. }
  subst exact.
  unfold DivisorCandidateCount. split.
  - intro Hin. apply Hnot_sorted.
    eapply Permutation_in; eauto.
  - split.
    + rewrite Hcount, Hprocessed.
      symmetry. apply full_dividing_card_permutation__candidate_update.
      exact Hperm.
    + apply (proj2 (least_common_full_permutation__candidate_update
        values sorted d d Hperm)).
      rewrite Hprocessed in Hexact. exact Hexact.
Qed.
Lemma copy_max_full_permutation__candidate_update :
  forall original copied sorted n mx,
  n = Zlength original -> CopyMaxState original copied n mx ->
  Permutation copied sorted -> Permutation original sorted.
Proof.
  intros original copied sorted n mx Hn Hcopy Hperm.
  unfold CopyMaxState in Hcopy. destruct Hcopy as [Hcopied _].
  subst n.
  assert (Hfull : sublist 0 (Zlength original) original = original).
  { unfold sublist. simpl. rewrite Zlength_correct, Nat2Z.id, firstn_all.
    reflexivity. }
  rewrite Hfull in Hcopied. subst copied. exact Hperm.
Qed.
Lemma divisor_best_advance_dividing__outer_transition :
  forall values mx q z ans,
    1 <= q ->
    q * q <= mx ->
    Z.rem mx q = 0 ->
    2 <= z ->
    DivisorBestState values mx q z ans ->
    DivisorBestState values mx (q + 1) 0 ans.
Proof.
  intros values mx q z ans Hq Hsq Hrem Hz Hbest.
  assert (Hqn : q <> 0) by lia.
  assert (Hmod : mx mod q = 0).
  { apply (proj1 (Zrem_Zmod_zero mx q Hqn)). exact Hrem. }
  assert (Henum : forall score,
      EnumeratedScore values mx q z score <->
      EnumeratedScore values mx (q + 1) 0 score).
  {
    intro score.
    unfold EnumeratedScore, EnumeratedDivisor.
    split.
    - intros [Hzero | [d [[Hprev | Hcur] Hcount]]].
      + now left.
      + right. exists d. split; [left|exact Hcount].
        destruct Hprev as [r [[Hr1 Hrq] [Hrsq [Hrmod Hd]]]].
        exists r. repeat split; try lia; assumption.
      + right. exists d. split; [left|exact Hcount].
        destruct Hcur as [_ [_ [[_ Hd] | [_ Hd]]]];
          exists q; repeat split; try lia; assumption.
    - intros [Hzero | [d [[Hprev | Hcur] Hcount]]].
      + now left.
      + right. exists d. split; [|exact Hcount].
        destruct Hprev as [r [[Hr1 Hrq1] [Hrsq [Hrmod Hd]]]].
        assert (Hrle : r <= q) by lia.
        destruct (proj1 (Z.lt_eq_cases r q) Hrle) as [Hrq | Hrq].
        * left. exists r. repeat split; assumption.
        * right. subst r. repeat split; try lia; assumption.
      + destruct Hcur as [_ [_ [[Hbad _] | [Hbad _]]]]; lia.
  }
  unfold DivisorBestState, max_value_of_subset, max_object_of_subset in *.
  destruct Hbest as [score [[Hscore Hmax] Hscore_eq]].
  exists score. split; [split|exact Hscore_eq].
  - apply Henum. exact Hscore.
  - intros other Hother. apply Hmax. apply Henum. exact Hother.
Qed.
Lemma divisor_best_advance_nondividing__outer_transition :
  forall values mx q ans,
    1 <= q ->
    Z.rem mx q <> 0 ->
    DivisorBestState values mx q 0 ans ->
    DivisorBestState values mx (q + 1) 0 ans.
Proof.
  intros values mx q ans Hq Hrem Hbest.
  assert (Hqn : q <> 0) by lia.
  assert (Hmod : mx mod q <> 0).
  {
    intro Hzero. apply Hrem.
    apply (proj2 (Zrem_Zmod_zero mx q Hqn)). exact Hzero.
  }
  assert (Henum : forall score,
      EnumeratedScore values mx q 0 score <->
      EnumeratedScore values mx (q + 1) 0 score).
  {
    intro score.
    unfold EnumeratedScore, EnumeratedDivisor.
    split.
    - intros [Hzero | [d [[Hprev | Hcur] Hcount]]].
      + now left.
      + right. exists d. split; [left|exact Hcount].
        destruct Hprev as [r [[Hr1 Hrq] [Hrsq [Hrmod Hd]]]].
        exists r. repeat split; try lia; assumption.
      + destruct Hcur as [_ [_ [[Hbad _] | [Hbad _]]]]; lia.
    - intros [Hzero | [d [[Hprev | Hcur] Hcount]]].
      + now left.
      + right. exists d. split; [|exact Hcount].
        destruct Hprev as [r [[Hr1 Hrq1] [Hrsq [Hrmod Hd]]]].
        left. exists r. repeat split; try lia.
        assert (Hrle : r <= q) by lia.
        destruct (proj1 (Z.lt_eq_cases r q) Hrle) as [Hrq | Hrq]; [assumption|].
        subst r. contradiction.
      + destruct Hcur as [_ [_ [[Hbad _] | [Hbad _]]]]; lia.
  }
  unfold DivisorBestState, max_value_of_subset, max_object_of_subset in *.
  destruct Hbest as [score [[Hscore Hmax] Hscore_eq]].
  exists score. split; [split|exact Hscore_eq].
  - apply Henum. exact Hscore.
  - intros other Hother. apply Hmax. apply Henum. exact Hother.
Qed.
Lemma divisor_enumeration_complete__final_result :
  forall mx q d,
    1 <= mx ->
    1 <= q ->
    q * q > mx ->
    (q - 1) * (q - 1) <= mx ->
    1 <= d ->
    (d | mx) ->
    EnumeratedDivisor mx q 0 d.
Proof.
  intros mx q d Hmx Hq Habove Hbelow Hd Hdiv.
  destruct Hdiv as [k Hfactor].
  assert (Hk : 1 <= k) by nia.
  destruct (Z_lt_ge_dec d q) as [Hdq | Hdq].
  - left. exists d. repeat split.
    + exact Hd.
    + exact Hdq.
    + nia.
    + rewrite Hfactor. apply Z_mod_mult.
    + left. reflexivity.
  - assert (Hkq : k < q).
    {
      destruct (Z_lt_ge_dec k q) as [Hkq | Hqk]; [exact Hkq |].
      exfalso.
      assert (Hqd : q * q <= q * d) by
        (apply Z.mul_le_mono_nonneg_l; lia).
      assert (Hkd : q * d <= k * d) by
        (apply Z.mul_le_mono_nonneg_r; lia).
      lia.
    }
    left. exists k. repeat split.
    + exact Hk.
    + exact Hkq.
    + rewrite Hfactor.
      apply Z.mul_le_mono_nonneg_l; lia.
    + rewrite Hfactor, Z.mul_comm. apply Z_mod_mult.
    + right. rewrite Hfactor, Z.mul_comm.
      symmetry. apply Z_div_mult. lia.
Qed.
Lemma set_card_Z_as_sum__final_result :
  forall (low high : Z) (P : Z -> Prop),
    #(fun x : Z => low <= x < high /\ P x) =
    SumLib.Sum.sum (fun x : Z => low <= x < high)
      (fun x => if prop_dec (P x) then 1 else 0).
Proof.
  intros low high P.
  unfold set_card, SumLib.Sum.sum.
  cbn [finite_Z_range' finite_Z_range].
  assert (Hfilter : forall xs : list Z,
    fold_right (fun _ acc : Z => 1 + acc) 0
      (filter (fun x => if prop_dec (P x) then true else false) xs) =
    fold_right (fun x acc : Z =>
      (if prop_dec (P x) then 1 else 0) + acc) 0 xs).
  {
    induction xs as [|x xs IH]; simpl; [reflexivity |].
    destruct (prop_dec (P x)); simpl.
    - exact (f_equal (fun z : Z => 1 + z) IH).
    - exact IH.
  }
  apply Hfilter.
Qed.
Lemma set_card_Z_subset_le__final_result :
  forall (low high : Z) (P Q : Z -> Prop),
    (forall x, low <= x < high -> P x -> Q x) ->
    #(fun x : Z => low <= x < high /\ P x) <=
    #(fun x : Z => low <= x < high /\ Q x).
Proof.
  intros low high P Q Hsub.
  rewrite !set_card_Z_as_sum__final_result.
  apply SumLib.ZRange.sum_Z_range_le.
  intros x Hx. destruct (prop_dec (P x)); destruct (prop_dec (Q x));
    try lia; exfalso; eauto.
Qed.
Lemma set_card_extensional__final_result :
  forall {A : Type} (P Q : A -> Prop) (FP : Finite P) (FQ : Finite Q),
    (forall x, P x <-> Q x) ->
    @set_card A P FP = @set_card A Q FQ.
Proof.
  intros A P Q FP FQ Hequiv.
  unfold set_card, SumLib.Sum.sum.
  assert (Hperm : Permutation (@enum A P FP) (@enum A Q FQ)).
  {
    apply NoDup_Permutation.
    - exact (@enum_nodup A P FP).
    - exact (@enum_nodup A Q FQ).
    - intros x.
      rewrite <- (@enum_ok A P FP x), <- (@enum_ok A Q FQ x).
      apply Hequiv.
  }
  induction Hperm.
  - reflexivity.
  - change (1 + fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 l =
            1 + fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 l').
    rewrite IHHperm. reflexivity.
  - reflexivity.
  - etransitivity; eassumption.
Qed.
Lemma special_choice_divisor_correspondence__final_result :
  forall a mx,
    LeastCommonOfChosen a (fun i : Z => 0 <= i < Zlength a) mx ->
    (forall indices,
      SpecialChoice a indices ->
      exists x,
        1 <= x /\ (x | mx) /\
        DivisorCandidateCount a x (#(FullDividingIndex a x)) /\
        #(fun i : Z => 0 <= i < Zlength a /\ indices i) <=
          #(FullDividingIndex a x)) /\
    (forall d count,
      DivisorCandidateCount a d count ->
      SpecialChoice a (FullDividingIndex a d) /\
      #(FullDividingIndex a d) = count).
Proof.
  intros a mx Hfull.
  unfold LeastCommonOfChosen, min_value_of_subset, min_object_of_subset
    in Hfull.
  destruct Hfull as [full_candidate [[[Hmxpos Hmxcommon] Hmxleast] Heqmx]].
  simpl in Heqmx. subst full_candidate.
  split.
  - intros indices Hchoice.
    unfold SpecialChoice in Hchoice.
    destruct Hchoice as [Hbounds [x [Hchosen Hnotin]]].
    unfold LeastCommonOfChosen, min_value_of_subset, min_object_of_subset
      in Hchosen.
    destruct Hchosen as [chosen_candidate
      [[[Hxpos Hxcommon] Hxleast] Heqx]].
    simpl in Heqx. subst chosen_candidate.
    exists x. repeat split.
    + exact Hxpos.
    + apply Hxleast. split; [exact Hmxpos |].
      intros idx Hidx.
      apply Hmxcommon. apply Hbounds. exact Hidx.
    + exact Hnotin.
    + unfold LeastCommonOfChosen, min_value_of_subset,
        min_object_of_subset.
      exists x. split.
      * split.
        -- split; [exact Hxpos |].
           intros idx [_ Hdiv]. exact Hdiv.
        -- intros y [Hypos Hycommon].
           apply Hxleast. split; [exact Hypos |].
           intros idx Hidx.
           apply Hycommon. split.
           ++ apply Hbounds. exact Hidx.
           ++ apply Hxcommon. exact Hidx.
      * reflexivity.
    + apply set_card_Z_subset_le__final_result.
      intros idx Hidx Hchosen_idx.
      apply Hxcommon. exact Hchosen_idx.
  - intros d count Hcandidate.
    unfold DivisorCandidateCount in Hcandidate.
    destruct Hcandidate as [Hnotin [Hcount Hlcm]].
    split.
    + unfold SpecialChoice. split.
      * intros idx [Hidx _]. exact Hidx.
      * exists d. split; assumption.
    + symmetry. exact Hcount.
Qed.
Lemma divisor_best_complete_implies_spec__final_result :
  forall a mx q ans,
    1 <= mx ->
    1 <= q ->
    q * q > mx ->
    (q - 1) * (q - 1) <= mx ->
    0 <= ans ->
    LeastCommonOfChosen a (fun i : Z => 0 <= i < Zlength a) mx ->
    DivisorBestState a mx q 0 ans ->
    Spec a ans.
Proof.
  intros a mx q ans Hmx Hq Habove Hbelow Hans Hfull Hbest.
  pose proof
    (special_choice_divisor_correspondence__final_result a mx Hfull)
    as [Hchoice_to_divisor Hdivisor_to_choice].
  unfold DivisorBestState, max_value_of_subset, max_object_of_subset
    in Hbest.
  destruct Hbest as [best [[Hbest_score Hbest_upper] Hbest_eq]].
  simpl in Hbest_eq. subst best.
  unfold Spec, max_value_of_subset_with_default.
  destruct Hbest_score as [Hzero | [d [Henum Hd_candidate]]].
  - right. split.
    + intros [indices count] Hcandidate_pair.
      simpl.
      destruct Hcandidate_pair as [Hchoice Hcount].
      simpl in Hchoice, Hcount.
      destruct (Hchoice_to_divisor indices Hchoice)
        as [x [Hxpos [Hxdiv [Hx_candidate Hcard_le]]]].
      assert (Hx_enum : EnumeratedDivisor mx q 0 x).
      {
        apply divisor_enumeration_complete__final_result; assumption.
      }
      assert (Hx_score : EnumeratedScore a mx q 0
        (#(FullDividingIndex a x))).
      {
        right. exists x. split; assumption.
      }
      specialize (Hbest_upper _ Hx_score).
      lia.
    + symmetry. exact Hzero.
  - left. split.
    + unfold max_value_of_subset, max_object_of_subset.
      exists (FullDividingIndex a d, ans). split.
      * split.
        -- simpl.
           pose proof (Hdivisor_to_choice d ans Hd_candidate)
             as [Hd_choice Hd_count].
           split; [exact Hd_choice |].
           simpl. rewrite <- Hd_count.
           apply set_card_extensional__final_result.
           intros idx. unfold FullDividingIndex. tauto.
        -- intros [indices count] Hcandidate_pair.
           simpl.
           destruct Hcandidate_pair as [Hchoice Hcount].
           simpl in Hchoice, Hcount.
           destruct (Hchoice_to_divisor indices Hchoice)
             as [x [Hxpos [Hxdiv [Hx_candidate Hcard_le]]]].
           assert (Hx_enum : EnumeratedDivisor mx q 0 x).
           {
             apply divisor_enumeration_complete__final_result; assumption.
           }
           assert (Hx_score : EnumeratedScore a mx q 0
             (#(FullDividingIndex a x))).
           {
             right. exists x. split; assumption.
           }
           specialize (Hbest_upper _ Hx_score).
           lia.
      * reflexivity.
    + exact Hans.
Qed.
