From Coq Require Import ZArith List.
Require Import AUXLib.ListLib.
Import ListNotations.
Local Open Scope Z_scope.

Definition CRTLCMPrefix (moduli : list Z) (count : Z) : Z :=
  fold_left Z.lcm (firstn (Z.to_nat count) moduli) 1.

Definition CRTCongruent (value residue modulus : Z) : Prop :=
  exists quotient, value = residue + modulus * quotient.

Definition CRTAllCongruences
    (residues moduli : list Z) (count value : Z) : Prop :=
  forall index,
    0 <= index < count ->
    CRTCongruent value (Znth index residues 0) (Znth index moduli 0).

Definition ExtendedCRTInputs
    (residues moduli : list Z) (n : Z) : Prop :=
  1 <= n /\
  Zlength residues = n /\
  Zlength moduli = n /\
  forall index,
    0 <= index < n ->
    0 < Znth index moduli 0 <= 2147483647 /\
    0 <= Znth index residues 0 < Znth index moduli 0.

Definition ExtendedCRTSystemCompatible
    (residues moduli : list Z) (n : Z) : Prop :=
  exists solution, CRTAllCongruences residues moduli n solution.

Definition ExtendedCRTIntSafe (moduli : list Z) (n : Z) : Prop :=
  (forall count,
     1 <= count <= n ->
     0 < CRTLCMPrefix moduli count <= 2147483647) /\
  (forall index,
     1 <= index < n ->
     2 * Z.quot
       (Znth index moduli 0)
       (Z.gcd (CRTLCMPrefix moduli index) (Znth index moduli 0))
       <= 2147483647).

Definition ExtendedCRTSystemResult
    (residues moduli : list Z)
    (n result combined_modulus : Z) : Prop :=
  combined_modulus = CRTLCMPrefix moduli n /\
  0 <= result < combined_modulus /\
  CRTAllCongruences residues moduli n result.

Definition CRTPrefixMeaning
    (residues moduli : list Z)
    (count answer combined_modulus : Z) : Prop :=
  combined_modulus = CRTLCMPrefix moduli count /\
  CRTAllCongruences residues moduli count answer.

Definition CRTReducedMergeEquation
    (current_answer current_modulus next_residue next_modulus
     multiplier : Z) : Prop :=
  let gcd := Z.gcd current_modulus next_modulus in
  exists adjustment,
    (current_modulus / gcd) * multiplier +
      (next_modulus / gcd) * adjustment =
    (next_residue - current_answer) / gcd.

From Coq Require Import Lia.
From Coq Require Import Lia Ring.
Lemma extended_crt_index_bounds__machine_bounds :
  forall residues moduli n index,
    ExtendedCRTInputs residues moduli n ->
    0 <= index < n ->
    (0 < Znth index moduli 0 <= 2147483647 /\
     0 <= Znth index residues 0 < Znth index moduli 0).
Proof.
  intros residues moduli n index Hinputs Hindex.
  unfold ExtendedCRTInputs in Hinputs.
  destruct Hinputs as [_ [_ [_ Hbounds]]].
  apply Hbounds.
  exact Hindex.
Qed.
Lemma positive_gcd_quotient_bounds__machine_bounds :
  forall current_modulus modulus gcd,
    0 < modulus <= 2147483647 ->
    gcd = Z.gcd current_modulus modulus ->
    0 < gcd ->
    0 < Z.quot modulus gcd <= 2147483647.
Proof.
  intros current_modulus modulus gcd Hmodulus Hgcd Hgcd_pos.
  assert (Hdivide : (gcd | modulus)).
  { subst gcd. apply Z.gcd_divide_r. }
  rewrite Z.quot_div_exact.
  - split.
    + apply Z.div_str_pos.
      split.
      * exact Hgcd_pos.
      * apply Z.divide_pos_le.
        -- lia.
        -- exact Hdivide.
    + apply Z.div_le_upper_bound; nia.
  - lia.
  - exact Hdivide.
Qed.
Lemma signed_difference_division_bounds__machine_bounds :
  forall residue answer divisor,
    0 <= residue <= 2147483647 ->
    0 <= answer <= 2147483647 ->
    0 < divisor ->
    -2147483648 < Z.quot (residue - answer) divisor <= 2147483647.
Proof.
  intros residue answer divisor Hresidue Hanswer Hdivisor.
  split.
  - assert (-2147483647 <= Z.quot (residue - answer) divisor).
    { apply Z.quot_le_lower_bound; nia. }
    lia.
  - apply Z.quot_le_upper_bound; nia.
Qed.
Lemma bounded_merge_arithmetic__machine_bounds :
  forall answer lcm multiplier reduced_modulus,
    0 <= answer < lcm ->
    0 <= multiplier < reduced_modulus ->
    0 < lcm ->
    lcm * reduced_modulus <= 2147483647 ->
    (multiplier * lcm <= 2147483647 /\
     -2147483648 <= multiplier * lcm /\
     answer + multiplier * lcm <= 2147483647 /\
     -2147483648 <= answer + multiplier * lcm).
Proof.
  intros answer lcm multiplier reduced_modulus
    Hanswer Hmultiplier Hlcm Hproduct.
  nia.
Qed.
Lemma crt_prefix_meaning_one__prefix_boundaries :
  forall residues moduli n,
    ExtendedCRTInputs residues moduli n ->
    1 <= n ->
    CRTPrefixMeaning residues moduli 1
      (Znth 0 residues 0) (Znth 0 moduli 0).
Proof.
  intros residues moduli n Hinputs Hn.
  unfold ExtendedCRTInputs in Hinputs.
  destruct Hinputs as [Hn' [Hresidues [Hmoduli Hall]]].
  destruct residues as [| residue residues].
  - cbn in Hresidues. lia.
  - destruct moduli as [| modulus moduli].
    + cbn in Hmoduli. lia.
    + specialize (Hall 0 ltac:(lia)) as Hzero.
      destruct Hzero as [[Hmodulus_pos Hmodulus_max]
                         [Hresidue_nonneg Hresidue_lt]].
      unfold CRTPrefixMeaning, CRTLCMPrefix,
        CRTAllCongruences, CRTCongruent.
      rewrite Z2Nat.inj_pos, Pos2Nat.inj_1.
      cbn [firstn fold_left].
      repeat rewrite Znth0_cons in *.
      split.
      * symmetry. apply Z.lcm_1_l_nonneg. lia.
      * intros index Hindex.
        assert (index = 0) by lia.
        subst index.
        exists 0.
        repeat rewrite Znth0_cons.
        ring.
Qed.
Lemma crt_prefix_meaning_to_result__prefix_boundaries :
  forall residues moduli n i answer combined_modulus,
    i = n ->
    0 <= answer < combined_modulus ->
    CRTPrefixMeaning residues moduli i answer combined_modulus ->
    ExtendedCRTSystemResult residues moduli n answer combined_modulus.
Proof.
  intros residues moduli n i answer combined_modulus Hi Hanswer Hprefix.
  subst i.
  unfold CRTPrefixMeaning in Hprefix.
  unfold ExtendedCRTSystemResult.
  tauto.
Qed.
Lemma quot_div_of_divide_pos__merge_transition :
  forall numerator denominator : Z,
    0 < denominator ->
    (denominator | numerator) ->
    numerator ÷ denominator = numerator / denominator.
Proof.
  intros numerator denominator Hdenominator Hdivide.
  destruct Hdivide as [quotient Hnumerator].
  rewrite Hnumerator, Z.quot_mul, Z.div_mul by lia.
  reflexivity.
Qed.
Lemma firstn_succ_nth__merge_transition {A : Type} :
  forall (l : list A) (n : nat) (default : A),
    (n < length l)%nat ->
    firstn (S n) l = firstn n l ++ [nth n l default].
Proof.
  induction l as [|a l IH]; intros n default Hn.
  - simpl in Hn. lia.
  - destruct n as [|n].
    + reflexivity.
    + simpl in *. f_equal. apply IH. lia.
Qed.
Lemma fold_left_lcm_all_divide__merge_transition :
  forall (values : list Z) (accumulator difference : Z),
    (accumulator | difference) ->
    (forall value, In value values -> (value | difference)) ->
    (fold_left Z.lcm values accumulator | difference).
Proof.
  induction values as [|value values IH]; intros accumulator difference Hacc Hall.
  - exact Hacc.
  - simpl. apply IH.
    + apply Z.lcm_least.
      * exact Hacc.
      * apply Hall. now left.
    + intros other Hother. apply Hall. now right.
Qed.
Lemma fold_left_lcm_preserves_divide__merge_transition :
  forall (values : list Z) (accumulator divisor : Z),
    (divisor | accumulator) ->
    (divisor | fold_left Z.lcm values accumulator).
Proof.
  induction values as [|value values IH]; intros accumulator divisor Hdiv.
  - exact Hdiv.
  - simpl. apply IH.
    destruct Hdiv as [q Hacc].
    destruct (Z.divide_lcm_l accumulator value) as [r Hlcm].
    exists (q * r). nia.
Qed.
Lemma fold_left_lcm_in_divides__merge_transition :
  forall (values : list Z) (accumulator value : Z),
    In value values ->
    (value | fold_left Z.lcm values accumulator).
Proof.
  intros values accumulator value Hin.
  apply in_split in Hin as [before [after Heq]].
  subst values.
  rewrite fold_left_app. simpl.
  apply fold_left_lcm_preserves_divide__merge_transition.
  apply Z.divide_lcm_r.
Qed.
Lemma crt_lcm_prefix_multiple__merge_transition :
  forall (moduli : list Z) (count index : Z),
    0 <= index < count ->
    count <= Zlength moduli ->
    (Znth index moduli 0 | CRTLCMPrefix moduli count).
Proof.
  intros moduli count index Hindex Hcount.
  assert (Hcount_nonneg : 0 <= count) by lia.
  assert (Hindex_nonneg : 0 <= index) by lia.
  assert (Hcount_nat : (Z.to_nat count <= length moduli)%nat).
  { apply Nat2Z.inj_le. rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct. lia. }
  assert (Hindex_nat : (Z.to_nat index < Z.to_nat count)%nat).
  { apply Z2Nat.inj_lt; lia. }
  unfold CRTLCMPrefix.
  apply fold_left_lcm_in_divides__merge_transition.
  assert (Hnth :
      nth (Z.to_nat index) (firstn (Z.to_nat count) moduli) 0 =
      Znth index moduli 0).
  { rewrite nth_firstn by exact Hindex_nat. reflexivity. }
  rewrite <- Hnth.
  apply nth_In.
  rewrite length_firstn, Nat.min_l by exact Hcount_nat.
  exact Hindex_nat.
Qed.
Lemma crt_prefix_solution_congruent_lcm__merge_transition :
  forall (residues moduli : list Z) (count answer combined solution : Z),
    0 <= count ->
    CRTPrefixMeaning residues moduli count answer combined ->
    CRTAllCongruences residues moduli count solution ->
    (combined | solution - answer).
Proof.
  intros residues moduli count answer combined solution Hcount Hprefix Hsolution.
  destruct Hprefix as [Hcombined Hanswer].
  subst combined.
  unfold CRTLCMPrefix.
  apply fold_left_lcm_all_divide__merge_transition.
  - exists (solution - answer). nia.
  - intros modulus Hin.
    destruct (In_nth _ _ 0 Hin) as [k [Hk Hnth]].
    assert (Hkcount_nat : (k < Z.to_nat count)%nat).
    { eapply Nat.lt_le_trans; [exact Hk |].
      rewrite length_firstn. lia. }
    assert (Hkcount : 0 <= Z.of_nat k < count).
    { split; [lia |].
      rewrite <- (Z2Nat.id count Hcount).
      lia. }
    assert (Hmodulus : Znth (Z.of_nat k) moduli 0 = modulus).
    { unfold Znth. rewrite Nat2Z.id.
      rewrite nth_firstn in Hnth by exact Hkcount_nat.
      exact Hnth. }
    specialize (Hanswer (Z.of_nat k) Hkcount).
    specialize (Hsolution (Z.of_nat k) Hkcount).
    rewrite Hmodulus in Hanswer, Hsolution.
    unfold CRTCongruent in Hanswer, Hsolution.
    destruct Hanswer as [answer_q Hanswer].
    destruct Hsolution as [solution_q Hsolution].
    exists (solution_q - answer_q). nia.
Qed.
Lemma crt_merge_difference_divisible__merge_transition :
  forall (residues moduli : list Z) (n index answer combined : Z),
    ExtendedCRTSystemCompatible residues moduli n ->
    CRTPrefixMeaning residues moduli index answer combined ->
    0 <= index < n ->
    (Z.gcd combined (Znth index moduli 0) |
      Znth index residues 0 - answer).
Proof.
  intros residues moduli n index answer combined Hcompatible Hprefix Hindex.
  destruct Hcompatible as [solution Hsolution].
  assert (Hsolution_prefix :
      CRTAllCongruences residues moduli index solution).
  { intros old_index Hold_index. apply Hsolution. lia. }
  pose proof
    (crt_prefix_solution_congruent_lcm__merge_transition
      residues moduli index answer combined solution
      (proj1 Hindex) Hprefix Hsolution_prefix) as Hprefix_div.
  specialize (Hsolution index Hindex).
  unfold CRTCongruent in Hsolution.
  destruct Hsolution as [next_q Hsolution].
  destruct Hprefix_div as [prefix_q Hprefix_div].
  destruct (Z.gcd_divide_l combined (Znth index moduli 0))
    as [combined_q Hcombined].
  destruct (Z.gcd_divide_r combined (Znth index moduli 0))
    as [modulus_q Hmodulus].
  exists (combined_q * prefix_q - modulus_q * next_q).
  nia.
Qed.
Lemma reduced_merge_equation_from_bezout__merge_transition :
  forall (current_answer current_modulus next_residue next_modulus
          gcd x_coefficient y_coefficient normalized quotient : Z),
    gcd = Z.gcd current_modulus next_modulus ->
    0 < gcd ->
    (gcd | next_residue - current_answer) ->
    current_modulus * x_coefficient + next_modulus * y_coefficient = gcd ->
    x_coefficient * ((next_residue - current_answer) / gcd) =
      normalized + (next_modulus / gcd) * quotient ->
    CRTReducedMergeEquation current_answer current_modulus
      next_residue next_modulus normalized.
Proof.
  intros current_answer current_modulus next_residue next_modulus
    gcd x_coefficient y_coefficient normalized quotient
    Hgcd Hgcd_pos Hdifference Hbezout Hnormalized.
  destruct (Z.gcd_divide_l current_modulus next_modulus)
    as [current_q Hcurrent].
  destruct (Z.gcd_divide_r current_modulus next_modulus)
    as [next_q Hnext].
  rewrite <- Hgcd in Hcurrent, Hnext.
  destruct Hdifference as [difference_q Hdifference].
  assert (Hcurrent_div : current_modulus / gcd = current_q).
  { rewrite Hcurrent. apply Z.div_mul. lia. }
  assert (Hnext_div : next_modulus / gcd = next_q).
  { rewrite Hnext. apply Z.div_mul. lia. }
  assert (Hdifference_div :
      (next_residue - current_answer) / gcd = difference_q).
  { rewrite Hdifference. apply Z.div_mul. lia. }
  rewrite Hcurrent, Hnext in Hbezout.
  rewrite Hnext_div, Hdifference_div in Hnormalized.
  assert (Hunit :
      current_q * x_coefficient + next_q * y_coefficient = 1) by nia.
  unfold CRTReducedMergeEquation.
  rewrite <- Hgcd.
  exists (y_coefficient * difference_q + current_q * quotient).
  rewrite Hcurrent_div, Hnext_div, Hdifference_div.
  assert (Hnormalized' :
      normalized = x_coefficient * difference_q - next_q * quotient) by lia.
  rewrite Hnormalized'.
  replace
    (current_q * (x_coefficient * difference_q - next_q * quotient) +
       next_q * (y_coefficient * difference_q + current_q * quotient))
    with
    ((current_q * x_coefficient + next_q * y_coefficient) * difference_q)
    by ring.
  rewrite Hunit. ring.
Qed.
Lemma crt_lcm_prefix_step__merge_transition :
  forall (residues moduli : list Z)
         (n index answer combined gcd reduced : Z),
    ExtendedCRTInputs residues moduli n ->
    0 <= index < n ->
    0 < combined ->
    CRTPrefixMeaning residues moduli index answer combined ->
    gcd = Z.gcd combined (Znth index moduli 0) ->
    0 < gcd ->
    reduced = Znth index moduli 0 / gcd ->
    CRTLCMPrefix moduli (index + 1) = combined * reduced.
Proof.
  intros residues moduli n index answer combined gcd reduced
    Hinputs Hindex Hcombined_pos Hprefix Hgcd Hgcd_pos Hreduced.
  destruct Hinputs as (Hn & Hresidue_length & Hmoduli_length & Hbounds).
  pose proof (Hbounds index Hindex) as [[Hmodulus_pos Hmodulus_max] Hresidue_bounds].
  assert (Hindex_nat : (Z.to_nat index < length moduli)%nat).
  { apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct, Hmoduli_length. lia. }
  assert (Hsuccessor : Z.to_nat (index + 1) = S (Z.to_nat index)).
  { rewrite Z2Nat.inj_add by lia. simpl. lia. }
  destruct Hprefix as [Hcombined Hcongruences].
  unfold CRTLCMPrefix at 1.
  rewrite Hsuccessor.
  rewrite (firstn_succ_nth__merge_transition
    moduli (Z.to_nat index) 0 Hindex_nat).
  rewrite fold_left_app. simpl.
  unfold CRTLCMPrefix in Hcombined.
  rewrite <- Hcombined.
  unfold Znth in Hgcd, Hreduced.
  subst gcd. subst reduced.
  unfold Z.lcm.
  rewrite Z.abs_eq.
  - reflexivity.
  - assert (Hmodulus_nonneg : 0 <= nth (Z.to_nat index) moduli 0).
    { unfold Znth in Hmodulus_pos. lia. }
    assert (Hgcd_nonneg :
        0 <= Z.gcd combined (nth (Z.to_nat index) moduli 0))
      by apply Z.gcd_nonneg.
    assert (0 <= nth (Z.to_nat index) moduli 0 /
                    Z.gcd combined (nth (Z.to_nat index) moduli 0)).
    { apply Z.div_pos; lia. }
    nia.
Qed.
Lemma crt_prefix_meaning_merge__merge_transition :
  forall (residues moduli : list Z)
         (n index answer combined gcd reduced multiplier : Z),
    ExtendedCRTInputs residues moduli n ->
    ExtendedCRTSystemCompatible residues moduli n ->
    0 <= index < n ->
    0 < combined ->
    CRTPrefixMeaning residues moduli index answer combined ->
    gcd = Z.gcd combined (Znth index moduli 0) ->
    0 < gcd ->
    reduced = Znth index moduli 0 / gcd ->
    0 <= multiplier < reduced ->
    CRTReducedMergeEquation answer combined
      (Znth index residues 0) (Znth index moduli 0) multiplier ->
    CRTPrefixMeaning residues moduli (index + 1)
      (answer + multiplier * combined) (combined * reduced).
Proof.
  intros residues moduli n index answer combined gcd reduced multiplier
    Hinputs Hcompatible Hindex Hcombined_pos Hprefix Hgcd Hgcd_pos
    Hreduced Hmultiplier Hmerge.
  destruct Hprefix as [Hcombined Hprefix_congruences].
  assert (Hnext_combined :
      CRTLCMPrefix moduli (index + 1) = combined * reduced).
  { exact
      (crt_lcm_prefix_step__merge_transition
        residues moduli n index answer combined gcd reduced
        Hinputs Hindex Hcombined_pos
        (conj Hcombined Hprefix_congruences)
        Hgcd Hgcd_pos Hreduced). }
  split.
  - symmetry. exact Hnext_combined.
  - intros old_index Hold_index.
    destruct (Z_lt_ge_dec old_index index) as [Hold | Hnew].
    + specialize (Hprefix_congruences old_index).
      assert (Hold_bounds : 0 <= old_index < index) by lia.
      specialize (Hprefix_congruences Hold_bounds).
      unfold CRTCongruent in Hprefix_congruences.
      destruct Hprefix_congruences as [old_q Hanswer].
      assert (Hmoduli_count : index <= Zlength moduli).
      { destruct Hinputs as (_ & _ & Hmoduli_length & _).
        rewrite Hmoduli_length. lia. }
      pose proof
        (crt_lcm_prefix_multiple__merge_transition
          moduli index old_index Hold_bounds Hmoduli_count) as Hdivides.
      destruct Hdivides as [combined_q Hdivides].
      unfold CRTCongruent.
      exists (old_q + multiplier * combined_q).
      nia.
    + assert (old_index = index) by lia. subst old_index.
      pose proof
        (crt_merge_difference_divisible__merge_transition
          residues moduli n index answer combined Hcompatible
          (conj Hcombined Hprefix_congruences) Hindex) as Hdifference.
      destruct (Z.gcd_divide_l combined (Znth index moduli 0))
        as [combined_q Hcombined_factor].
      destruct (Z.gcd_divide_r combined (Znth index moduli 0))
        as [modulus_q Hmodulus_factor].
      rewrite <- Hgcd in Hcombined_factor, Hmodulus_factor.
      rewrite <- Hgcd in Hdifference.
      destruct Hdifference as [difference_q Hdifference_factor].
      assert (Hcombined_div : combined / gcd = combined_q).
      { rewrite Hcombined_factor. apply Z.div_mul. lia. }
      assert (Hmodulus_div : Znth index moduli 0 / gcd = modulus_q).
      { rewrite Hmodulus_factor. apply Z.div_mul. lia. }
      assert (Hdifference_div :
          (Znth index residues 0 - answer) / gcd = difference_q).
      { rewrite Hdifference_factor. apply Z.div_mul. lia. }
      unfold CRTReducedMergeEquation in Hmerge.
      rewrite <- Hgcd in Hmerge.
      destruct Hmerge as [adjustment Hmerge].
      rewrite Hcombined_div, Hmodulus_div, Hdifference_div in Hmerge.
      unfold CRTCongruent.
      exists (- adjustment).
      nia.
Qed.

Lemma bezout_coefficient_strict__gcd_branch_setup :
  forall lcm modulus gcd x y,
    0 < modulus ->
    gcd = Z.gcd lcm modulus ->
    0 < gcd ->
    Z.rem lcm modulus <> 0 ->
    lcm * x + modulus * y = gcd ->
    Z.abs x <= Z.quot modulus gcd ->
    - Z.quot modulus gcd < x < Z.quot modulus gcd.
Proof.
  intros lcm modulus gcd x y Hmodulus Hgcd Hgcd_pos
    Hnondiv Hbezout Habs.
  pose proof (Z.gcd_divide_l lcm modulus) as Hdivide_l.
  pose proof (Z.gcd_divide_r lcm modulus) as Hdivide_r.
  rewrite <- Hgcd in Hdivide_l, Hdivide_r.
  destruct Hdivide_l as [lcm_q Hlcm].
  destruct Hdivide_r as [modulus_q Hmodulus_factor].
  assert (Hquot : Z.quot modulus gcd = modulus_q).
  {
    rewrite Z.quot_div_exact.
    - rewrite Hmodulus_factor. apply Z.div_mul. lia.
    - lia.
    - exists modulus_q. exact Hmodulus_factor.
  }
  assert (Hmodulus_q_pos : 0 < modulus_q) by nia.
  assert (Hunit : lcm_q * x + modulus_q * y = 1).
  {
    rewrite Hlcm, Hmodulus_factor in Hbezout.
    nia.
  }
  assert (Hmodulus_q_ne_one : modulus_q <> 1).
  {
    intro Hmodulus_q_one.
    apply Hnondiv.
    replace modulus with gcd by nia.
    apply Z.rem_divide.
    - lia.
    - exists lcm_q. exact Hlcm.
  }
  rewrite Hquot in Habs |- *.
  apply Z.abs_le in Habs.
  destruct Habs as [Hlower Hupper].
  split.
  - assert (x <> - modulus_q).
    {
      intro Hx.
      subst x.
      apply Hmodulus_q_ne_one.
      replace (lcm_q * - modulus_q + modulus_q * y)
        with (modulus_q * (y - lcm_q)) in Hunit by ring.
      assert (Hmodulus_q_le_one : modulus_q <= 1).
      {
        apply Z.divide_pos_le.
        - lia.
        - exists (y - lcm_q). rewrite Z.mul_comm. symmetry. exact Hunit.
      }
      lia.
    }
    lia.
  - assert (x <> modulus_q).
    {
      intro Hx.
      subst x.
      apply Hmodulus_q_ne_one.
      replace (lcm_q * modulus_q + modulus_q * y)
        with (modulus_q * (lcm_q + y)) in Hunit by ring.
      assert (Hmodulus_q_le_one : modulus_q <= 1).
      {
        apply Z.divide_pos_le.
        - lia.
        - exists (lcm_q + y). rewrite Z.mul_comm. symmetry. exact Hunit.
      }
      lia.
    }
    lia.
Qed.
