From Coq Require Import ZArith List.
Import ListNotations.
Local Open Scope Z_scope.

(** The frozen external contract for [modular_power] denotes the canonical
    modular value of an integer power. *)
Definition ModularPower
    (base exponent modulus result : Z) : Prop :=
  result = (base ^ exponent) mod modulus.

(** A positive integer is prime when it has no nontrivial divisor.  This
    case-local formulation keeps the public annotation surface independent of
    proof-only number-theory imports. *)
Definition PrimeForLucas (p : Z) : Prop :=
  2 <= p /\
  forall divisor,
    2 <= divisor < p ->
    p mod divisor <> 0.

(** A Pascal-recursive mathematical binomial coefficient.  This is a
    property-level object independent of the multiplicative C helper. *)
Fixpoint LucasNatBinomial (upper lower : nat) : nat :=
  match upper, lower with
  | _, O => 1%nat
  | O, S _ => 0%nat
  | S upper', S lower' =>
      (LucasNatBinomial upper' lower' +
       LucasNatBinomial upper' (S lower'))%nat
  end.

Definition LucasBinomialCoefficient (upper lower : Z) : Z :=
  Z.of_nat
    (LucasNatBinomial (Z.to_nat upper) (Z.to_nat lower)).

Definition BinomialDigitResidue
    (upper lower p result : Z) : Prop :=
  result = LucasBinomialCoefficient upper lower mod p.

Definition LucasBinomialResidue
    (n m p result : Z) : Prop :=
  result = LucasBinomialCoefficient (n + m) n mod p.

(** The helper replaces [lower] by its symmetric, smaller choice before the
    multiplicative loop. *)
Definition DigitEffectiveLower (upper lower : Z) : Z :=
  Z.min lower (upper - lower).

(** A finite mathematical product of [count] consecutive integers beginning
    at [start]. *)
Definition LucasRangeProduct (start count : Z) : Z :=
  fold_right Z.mul 1
    (map (fun offset => start + Z.of_nat offset)
      (seq 0 (Z.to_nat count))).

Definition DigitNumeratorPrefix
    (upper lower processed : Z) : Z :=
  LucasRangeProduct (upper - lower + 1) processed.

Definition DigitDenominatorPrefix (processed : Z) : Z :=
  LucasRangeProduct 1 processed.

(** The precise signed-int safety promise for the digit helper.  It talks
    about mathematical prefix residues rather than simulating C state. *)
Definition DigitBinomialMachineSafe
    (upper original_lower p : Z) : Prop :=
  let lower := DigitEffectiveLower upper original_lower in
  (forall next,
      1 <= next <= lower ->
      0 <=
        (DigitNumeratorPrefix upper lower (next - 1) mod p) *
        (upper - lower + next) <= 2147483647 /\
      0 <=
        (DigitDenominatorPrefix (next - 1) mod p) * next <=
        2147483647) /\
  (forall inverse,
      ModularPower
        (DigitDenominatorPrefix lower mod p) (p - 2) p inverse ->
      0 <=
        (DigitNumeratorPrefix upper lower lower mod p) * inverse <=
        2147483647).

(** The digit at [position] in a nonnegative integer's base-[p]
    representation. *)
Definition LucasDigit (value p : Z) (position : nat) : Z :=
  (value / p ^ Z.of_nat position) mod p.

(** Product, modulo [p], of the first [digits] Lucas digit coefficients. *)
Definition LucasPrefixProduct
    (upper lower p : Z) (digits : nat) : Z :=
  fold_right Z.mul 1
    (map
      (fun position =>
        LucasBinomialCoefficient
          (LucasDigit upper p position)
          (LucasDigit lower p position) mod p)
      (seq 0 digits)) mod p.

(** The input-specific machine-safety promise for every digit that the main
    loop can process. *)
Definition LucasMachineSafe (n m p : Z) : Prop :=
  forall processed : nat,
    let upper_digit := LucasDigit (n + m) p processed in
    let lower_digit := LucasDigit n p processed in
    lower_digit <= upper_digit ->
    DigitBinomialMachineSafe upper_digit lower_digit p /\
    0 <=
      LucasPrefixProduct (n + m) n p processed *
      (LucasBinomialCoefficient upper_digit lower_digit mod p) <=
      2147483647.

(** Internal mathematical state for the multiplicative digit helper. *)
Definition DigitProductProgress
    (upper lower p next numerator denominator : Z) : Prop :=
  numerator = DigitNumeratorPrefix upper lower (next - 1) mod p /\
  denominator = DigitDenominatorPrefix (next - 1) mod p.

(** Internal mathematical state for Lucas digit decomposition.  The
    existential position is a mathematical digit coordinate, not a mirror of
    a C loop counter. *)
Definition LucasProgress
    (original_upper original_lower p
     current_upper current_lower result : Z) : Prop :=
  exists processed : nat,
    current_upper =
      original_upper / p ^ Z.of_nat processed /\
    current_lower =
      original_lower / p ^ Z.of_nat processed /\
    result =
      LucasPrefixProduct original_upper original_lower p processed /\
    LucasBinomialCoefficient original_upper original_lower mod p =
      (result *
       LucasBinomialCoefficient current_upper current_lower) mod p.

From Coq Require Import Lia Ring.
From Coq Require Import Znumtheory PeanoNat Permutation Lia.
From Coq Require Import Lia Arith.Factorial setoid_ring.ArithRing.
From Coq Require Import ZArith.Znumtheory ZArith.Zquot.
Lemma lucas_range_product_zero__digit_product_progress :
  forall start,
    LucasRangeProduct start 0 = 1.
Proof.
  intros start.
  reflexivity.
Qed.
Lemma lucas_range_product_succ__digit_product_progress :
  forall start count,
    0 <= count ->
    LucasRangeProduct start (count + 1) =
      LucasRangeProduct start count * (start + count).
Proof.
  intros start count Hcount.
  unfold LucasRangeProduct.
  rewrite Z2Nat.inj_add by lia.
  simpl Z.to_nat.
  rewrite seq_app.
  simpl.
  rewrite map_app, fold_right_app.
  simpl.
  rewrite Z2Nat.id by lia.
  remember
    (map (fun offset : nat => start + Z.of_nat offset)
      (seq 0 (Z.to_nat count))) as factors.
  clear Heqfactors.
  induction factors as [|factor factors IH]; simpl.
  - rewrite Z.mul_1_r.
    destruct (start + count); reflexivity.
  - rewrite IH.
    rewrite Z.mul_assoc.
    reflexivity.
Qed.
Lemma digit_product_progress_step__digit_product_progress :
  forall upper lower p next numerator denominator,
    p <> 0 ->
    1 <= next ->
    DigitProductProgress upper lower p next numerator denominator ->
    DigitProductProgress upper lower p (next + 1)
      ((numerator * (upper - lower + next)) mod p)
      ((denominator * next) mod p).
Proof.
  intros upper lower p next numerator denominator Hp Hnext Hprogress.
  unfold DigitProductProgress, DigitNumeratorPrefix,
    DigitDenominatorPrefix in *.
  destruct Hprogress as [Hnumerator Hdenominator].
  split.
  - replace (next + 1 - 1) with ((next - 1) + 1) by lia.
    rewrite lucas_range_product_succ__digit_product_progress by lia.
    replace (upper - lower + 1 + (next - 1))
      with (upper - lower + next) by ring.
    rewrite Hnumerator.
    apply Z.mul_mod_idemp_l.
    exact Hp.
  - replace (next + 1 - 1) with ((next - 1) + 1) by lia.
    rewrite lucas_range_product_succ__digit_product_progress by lia.
    replace (1 + (next - 1)) with next by ring.
    rewrite Hdenominator.
    apply Z.mul_mod_idemp_l.
    exact Hp.
Qed.
Lemma prime_for_lucas_prime__digit_final_residue :
  forall p, PrimeForLucas p -> prime p.
Proof.
  intros p [Hp Hnone].
  apply (proj1 (prime_alt p)).
  split; [lia|].
  intros divisor Hrange Hdiv.
  apply (Hnone divisor); [lia|].
  now apply Zdivide_mod.
Qed.
Lemma lucas_nat_binomial_zero__digit_final_residue :
  forall n, LucasNatBinomial n 0 = 1%nat.
Proof.
  now destruct n.
Qed.
Lemma lucas_nat_binomial_one__digit_final_residue :
  forall n, LucasNatBinomial n 1 = n.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - simpl LucasNatBinomial.
    rewrite lucas_nat_binomial_zero__digit_final_residue, IH.
    reflexivity.
Qed.
Lemma lucas_nat_binomial_above__digit_final_residue :
  forall n k, (n < k)%nat -> LucasNatBinomial n k = 0%nat.
Proof.
  induction n as [|n IH]; intros [|k] Hlt; simpl in *; try lia.
  rewrite IH by lia.
  rewrite IH by lia.
  reflexivity.
Qed.
Lemma lucas_nat_binomial_diagonal__digit_final_residue :
  forall n, LucasNatBinomial n n = 1%nat.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - simpl LucasNatBinomial.
    rewrite IH.
    rewrite lucas_nat_binomial_above__digit_final_residue by lia.
    reflexivity.
Qed.
Lemma lucas_nat_binomial_symmetry__digit_final_residue :
  forall n k,
    (k <= n)%nat ->
    LucasNatBinomial n k = LucasNatBinomial n (n - k).
Proof.
  induction n as [|n IH]; intros [|k] Hle.
  - reflexivity.
  - lia.
  - replace (S n - 0)%nat with (S n) by lia.
    rewrite lucas_nat_binomial_zero__digit_final_residue.
    symmetry.
    apply lucas_nat_binomial_diagonal__digit_final_residue.
  - simpl LucasNatBinomial.
    destruct (Nat.eq_dec k n) as [->|Hneq].
    + rewrite Nat.sub_diag.
      simpl LucasNatBinomial.
      rewrite lucas_nat_binomial_diagonal__digit_final_residue.
      rewrite lucas_nat_binomial_above__digit_final_residue by lia.
      reflexivity.
    + assert (Hkn : (k < n)%nat) by lia.
      assert (Hskn : (S k <= n)%nat) by lia.
      replace (n - k)%nat with (S (n - S k)) by lia.
      simpl LucasNatBinomial.
      rewrite <- (IH (S k) Hskn).
      replace (S (n - S k)) with (n - k)%nat by lia.
      rewrite <- (IH k ltac:(lia)).
      lia.
Qed.
Lemma lucas_binomial_symmetry_z__digit_final_residue :
  forall upper lower,
    0 <= lower <= upper ->
    LucasBinomialCoefficient upper lower =
    LucasBinomialCoefficient upper (upper - lower).
Proof.
  intros upper lower Hbounds.
  unfold LucasBinomialCoefficient.
  rewrite Z2Nat.inj_sub by lia.
  apply f_equal.
  apply lucas_nat_binomial_symmetry__digit_final_residue.
  apply Z2Nat.inj_le; lia.
Qed.
Lemma lucas_nat_binomial_step__digit_final_residue :
  forall n k,
    (k < n)%nat ->
    (LucasNatBinomial n (S k) * S k =
     LucasNatBinomial n k * (n - k))%nat.
Proof.
  induction n as [|n IH]; intros [|k] Hlt.
  - lia.
  - lia.
  - simpl LucasNatBinomial.
    rewrite lucas_nat_binomial_zero__digit_final_residue.
    rewrite lucas_nat_binomial_one__digit_final_residue.
    simpl.
    now rewrite Nat.add_0_r, Nat.mul_1_r.
  - simpl LucasNatBinomial.
    pose proof (IH k ltac:(lia)) as IHk.
    destruct (Nat.eq_dec (S k) n) as [Heq|Hneq].
    + subst n.
      assert (Hnear : LucasNatBinomial (S k) k = S k).
      { rewrite lucas_nat_binomial_symmetry__digit_final_residue by lia.
        replace (S k - k)%nat with 1%nat by lia.
        apply lucas_nat_binomial_one__digit_final_residue. }
      rewrite lucas_nat_binomial_diagonal__digit_final_residue.
      rewrite lucas_nat_binomial_above__digit_final_residue by lia.
      rewrite Hnear.
      replace (S k - k)%nat with 1%nat by lia.
      simpl.
      change
        (S (S (k + 0)) =
         ((S k - k) + (k + 1) * (S k - k))%nat).
      replace (S k - k)%nat with 1%nat by lia.
      nia.
    + pose proof (IH (S k) ltac:(lia)) as IHsk.
      nia.
Qed.
Lemma fold_right_Zmul_snoc__digit_final_residue :
  forall l x,
    fold_right Z.mul 1 (l ++ [x]) = fold_right Z.mul 1 l * x.
Proof.
  induction l as [|a l IH]; intros x; simpl.
  - rewrite Z.mul_1_r. now destruct x.
  - rewrite IH. ring.
Qed.
Lemma lucas_range_product_succ_end__digit_final_residue :
  forall start count,
    LucasRangeProduct start (Z.of_nat (S count)) =
    LucasRangeProduct start (Z.of_nat count) *
      (start + Z.of_nat count).
Proof.
  intros start count.
  unfold LucasRangeProduct.
  rewrite !Nat2Z.id.
  rewrite seq_S, map_app.
  simpl map.
  rewrite fold_right_Zmul_snoc__digit_final_residue.
  simpl. ring.
Qed.
Lemma lucas_range_product_succ_start__digit_final_residue :
  forall start count,
    LucasRangeProduct start (Z.of_nat (S count)) =
    start * LucasRangeProduct (start + 1) (Z.of_nat count).
Proof.
  intros start count.
  unfold LucasRangeProduct.
  rewrite !Nat2Z.id.
  simpl seq.
  simpl map.
  simpl fold_right.
  rewrite Z.add_0_r.
  f_equal.
  rewrite <- (seq_shift count 0).
  rewrite map_map.
  f_equal.
  apply map_ext.
  intros offset.
  rewrite Nat2Z.inj_succ.
  lia.
Qed.
Lemma lucas_nat_binomial_range_product__digit_final_residue :
  forall n k,
    (k <= n)%nat ->
    Z.of_nat (LucasNatBinomial n k) *
      LucasRangeProduct 1 (Z.of_nat k) =
    LucasRangeProduct (Z.of_nat (n - k) + 1) (Z.of_nat k).
Proof.
  intros n k.
  revert n.
  induction k as [|k IH]; intros n Hkn.
  - rewrite lucas_nat_binomial_zero__digit_final_residue.
    unfold LucasRangeProduct. simpl. reflexivity.
  - assert (Hklt : (k < n)%nat) by lia.
    pose proof (IH n ltac:(lia)) as IHrange.
    pose proof (lucas_nat_binomial_step__digit_final_residue n k Hklt)
      as Hstep.
    apply (f_equal Z.of_nat) in Hstep.
    rewrite !Nat2Z.inj_mul in Hstep.
    rewrite lucas_range_product_succ_end__digit_final_residue.
    replace (Z.of_nat (n - S k) + 1) with (Z.of_nat (n - k)) by
      (rewrite !Nat2Z.inj_sub by lia; lia).
    rewrite lucas_range_product_succ_start__digit_final_residue.
    replace
      (Z.of_nat (LucasNatBinomial n (S k)) *
       (LucasRangeProduct 1 (Z.of_nat k) * (1 + Z.of_nat k)))
      with
      ((Z.of_nat (LucasNatBinomial n (S k)) * Z.of_nat (S k)) *
       LucasRangeProduct 1 (Z.of_nat k)) by
      (rewrite Nat2Z.inj_succ; ring).
    rewrite Hstep.
    replace
      ((Z.of_nat (LucasNatBinomial n k) * Z.of_nat (n - k)) *
       LucasRangeProduct 1 (Z.of_nat k))
      with
      (Z.of_nat (n - k) *
       (Z.of_nat (LucasNatBinomial n k) *
        LucasRangeProduct 1 (Z.of_nat k))) by ring.
    rewrite IHrange.
    ring.
Qed.
Lemma lucas_binomial_range_product_z__digit_final_residue :
  forall upper lower,
    0 <= lower <= upper ->
    LucasBinomialCoefficient upper lower *
      DigitDenominatorPrefix lower =
    DigitNumeratorPrefix upper lower lower.
Proof.
  intros upper lower Hbounds.
  unfold LucasBinomialCoefficient, DigitDenominatorPrefix,
    DigitNumeratorPrefix.
  pose proof
    (lucas_nat_binomial_range_product__digit_final_residue
      (Z.to_nat upper) (Z.to_nat lower) ltac:(apply Z2Nat.inj_le; lia))
    as Hrange.
  rewrite !Z2Nat.id in Hrange by lia.
  rewrite Nat2Z.inj_sub in Hrange by
    (apply Z2Nat.inj_le; lia).
  rewrite !Z2Nat.id in Hrange by lia.
  exact Hrange.
Qed.
Lemma prime_product_not_divisible__digit_final_residue :
  forall p l,
    prime p ->
    Forall (fun x => 1 <= x < p) l ->
    ~ (p | fold_right Z.mul 1 l).
Proof.
  intros p l Hp Hall.
  induction Hall as [|x l Hx Hall IH]; simpl.
  - intros [q Hq].
    pose proof (prime_ge_2 p Hp).
    destruct (Z_le_gt_dec q 0); nia.
  - intros Hdiv.
    apply prime_mult in Hdiv; [|exact Hp].
    destruct Hdiv as [Hxdiv|Hrest].
    + destruct Hxdiv as [q Hq].
      pose proof (prime_ge_2 p Hp).
      destruct (Z_le_gt_dec q 0); nia.
    + exact (IH Hrest).
Qed.
Lemma digit_factorial_nonzero_mod_prime__digit_final_residue :
  forall lower p,
    0 <= lower < p ->
    PrimeForLucas p ->
    DigitDenominatorPrefix lower mod p <> 0.
Proof.
  intros lower p Hbounds Hprime Hzero.
  pose proof (prime_for_lucas_prime__digit_final_residue p Hprime) as Hp.
  apply
    (prime_product_not_divisible__digit_final_residue p
      (map (fun offset => 1 + Z.of_nat offset)
        (seq 0 (Z.to_nat lower))) Hp).
  - apply Forall_forall.
    intros x Hx.
    apply in_map_iff in Hx.
    destruct Hx as [offset [Hxeq Hoffset]].
    subst x.
    apply in_seq in Hoffset.
    zify; lia.
  - apply Zmod_divide; [lia|].
    unfold DigitDenominatorPrefix, LucasRangeProduct in Hzero.
    exact Hzero.
Qed.
Lemma NoDup_map_Zof_nat_seq__digit_final_residue :
  forall start len,
    NoDup (map Z.of_nat (seq start len)).
Proof.
  intros.
  apply NoDup_map_NoDup_ForallPairs.
  - unfold ForallPairs. intros a b _ _ Heq.
    now apply Nat2Z.inj in Heq.
  - apply seq_NoDup.
Qed.
Lemma in_lucas_residues__digit_final_residue :
  forall p x,
    1 < p ->
    In x (map Z.of_nat (seq 1 (Z.to_nat (p - 1)))) <->
    1 <= x < p.
Proof.
  intros p x Hp.
  rewrite in_map_iff.
  split.
  - intros [n [Hx Hin]].
    subst x.
    apply in_seq in Hin.
    zify; lia.
  - intros Hx.
    exists (Z.to_nat x).
    split.
    + rewrite Z2Nat.id by lia. reflexivity.
    + apply in_seq. zify; lia.
Qed.
Lemma prime_mul_mod_cancel__digit_final_residue :
  forall p a x y,
    prime p -> 0 < a < p -> 1 <= x < p -> 1 <= y < p ->
    (a * x) mod p = (a * y) mod p -> x = y.
Proof.
  intros p a x y Hp Ha Hx Hy Heq.
  pose proof (prime_ge_2 p Hp) as Hp2.
  assert (Hdiv : (p | a * (x - y))).
  { apply Zmod_divide; [lia|].
    replace (a * (x - y)) with (a * x - a * y) by ring.
    rewrite Zminus_mod, Heq, Z.sub_diag.
    apply Z.mod_0_l; lia. }
  assert (Hrel : rel_prime p a).
  { apply rel_prime_sym.
    destruct Hp as [Hpgt Hall].
    apply Hall; lia. }
  pose proof (Gauss p a (x - y) Hdiv Hrel) as Hdivxy.
  destruct Hdivxy as [k Hk].
  assert (-p < x - y < p) by lia.
  subst.
  assert (-1 < k) by (apply (Zmult_lt_reg_r (-1) k p); lia).
  assert (k < 1) by (apply (Zmult_lt_reg_r k 1 p); lia).
  lia.
Qed.
Lemma prime_mul_residue_in_lucas_residues__digit_final_residue :
  forall p a x,
    prime p -> 0 < a < p ->
    In x (map Z.of_nat (seq 1 (Z.to_nat (p - 1)))) ->
    In ((a * x) mod p)
      (map Z.of_nat (seq 1 (Z.to_nat (p - 1)))).
Proof.
  intros p a x Hp Ha Hx.
  pose proof (prime_ge_2 p Hp) as Hp2.
  apply in_lucas_residues__digit_final_residue; [lia|].
  apply in_lucas_residues__digit_final_residue in Hx; [|lia].
  split.
  - assert (Hrel_pa : rel_prime p a).
    { apply rel_prime_sym.
      destruct Hp as [Hpgt Hall]. apply Hall; lia. }
    assert (Hrel_px : rel_prime p x).
    { apply rel_prime_sym.
      destruct Hp as [Hpgt Hall]. apply Hall; lia. }
    pose proof (rel_prime_mult p a x Hrel_pa Hrel_px) as Hrel_p_ax.
    pose proof (Zrel_prime_neq_mod_0 (a * x) p ltac:(lia)
      (rel_prime_sym _ _ Hrel_p_ax)) as Hnz.
    pose proof (Z.mod_pos_bound (a * x) p ltac:(lia)) as Hbound.
    lia.
  - apply Z.mod_pos_bound; lia.
Qed.
Lemma prime_mul_residue_preimage__digit_final_residue :
  forall p a z,
    prime p -> 0 < a < p ->
    In z (map Z.of_nat (seq 1 (Z.to_nat (p - 1)))) ->
    exists x,
      (a * x) mod p = z /\
      In x (map Z.of_nat (seq 1 (Z.to_nat (p - 1)))).
Proof.
  intros p a z Hp Ha Hz.
  pose proof (prime_ge_2 p Hp) as Hp2.
  assert (Hrel_ap : rel_prime a p).
  { destruct Hp as [Hpgt Hall]. apply Hall; lia. }
  pose proof (rel_prime_bezout a p Hrel_ap) as Hbez.
  destruct Hbez as [u v Huv].
  exists ((u * z) mod p).
  assert (Hzrange : 1 <= z < p).
  { apply in_lucas_residues__digit_final_residue in Hz; lia. }
  assert (Hmap : (a * ((u * z) mod p)) mod p = z).
  { rewrite (Z.mul_mod_idemp_r a (u * z) p) by lia.
    replace (a * (u * z)) with ((u * a) * z) by ring.
    assert (((u * a) * z) mod p = z mod p).
    { replace (u * a) with (1 - v * p) by lia.
      replace ((1 - v * p) * z) with (z + (-v * z) * p) by ring.
      rewrite Z.mod_add by lia. reflexivity. }
    rewrite H.
    apply Z.mod_small; lia. }
  split; [exact Hmap|].
  apply in_lucas_residues__digit_final_residue; [lia|].
  pose proof (Z.mod_pos_bound (u * z) p ltac:(lia)) as Hbound.
  split; [|lia].
  destruct (Z.eq_dec ((u * z) mod p) 0) as [Hzero|Hnz]; [|lia].
  rewrite Hzero in Hmap.
  rewrite Z.mul_0_r in Hmap.
  rewrite Z.mod_0_l in Hmap by lia.
  lia.
Qed.
Lemma lucas_residues_mul_permutation__digit_final_residue :
  forall p a,
    prime p -> 0 < a < p ->
    Permutation
      (map (fun x => (a * x) mod p)
        (map Z.of_nat (seq 1 (Z.to_nat (p - 1)))))
      (map Z.of_nat (seq 1 (Z.to_nat (p - 1)))).
Proof.
  intros p a Hp Ha.
  pose proof (prime_ge_2 p Hp) as Hp2.
  apply NoDup_Permutation.
  - apply NoDup_map_NoDup_ForallPairs.
    + unfold ForallPairs. intros x y Hx Hy Heq.
      eapply prime_mul_mod_cancel__digit_final_residue.
      * exact Hp.
      * exact Ha.
      * apply in_lucas_residues__digit_final_residue in Hx; lia.
      * apply in_lucas_residues__digit_final_residue in Hy; lia.
      * exact Heq.
    + apply NoDup_map_Zof_nat_seq__digit_final_residue.
  - apply NoDup_map_Zof_nat_seq__digit_final_residue.
  - intros z.
    rewrite in_map_iff.
    split.
    + intros [x [Hz Hx]].
      subst z.
      now apply prime_mul_residue_in_lucas_residues__digit_final_residue.
    + intros Hz.
      destruct
        (prime_mul_residue_preimage__digit_final_residue p a z Hp Ha Hz)
        as [x [Hmap Hx]].
      exists x. auto.
Qed.
Lemma fold_right_Zmul_permutation__digit_final_residue :
  forall l1 l2,
    Permutation l1 l2 ->
    fold_right Z.mul 1 l1 = fold_right Z.mul 1 l2.
Proof.
  intros l1 l2 Hperm.
  induction Hperm; simpl.
  - reflexivity.
  - now rewrite IHHperm.
  - ring.
  - congruence.
Qed.
Lemma fold_right_Zmul_map_mod__digit_final_residue :
  forall p a l,
    p <> 0 ->
    fold_right Z.mul 1 (map (fun x => (a * x) mod p) l) mod p =
    (a ^ Z.of_nat (length l) * fold_right Z.mul 1 l) mod p.
Proof.
  intros p a l Hp.
  induction l as [|x xs IH].
  - change (1 mod p = (a ^ 0 * 1) mod p).
    rewrite Z.pow_0_r. ring_simplify. reflexivity.
  - simpl.
    change (Z.pow_pos a (Pos.of_succ_nat (length xs))) with
      (a ^ Z.of_nat (S (length xs))).
    rewrite Nat2Z.inj_succ.
    rewrite Z.pow_succ_r by lia.
    rewrite <-
      (Z.mul_mod_idemp_r ((a * x) mod p)
        (fold_right Z.mul 1 (map (fun x0 => (a * x0) mod p) xs)) p)
      by exact Hp.
    rewrite IH.
    rewrite <-
      (Z.mul_mod (a * x) (a ^ Z.of_nat (length xs) *
        fold_right Z.mul 1 xs) p) by exact Hp.
    replace
      ((a * x) * (a ^ Z.of_nat (length xs) * fold_right Z.mul 1 xs))
      with
      ((a * a ^ Z.of_nat (length xs)) *
        (x * fold_right Z.mul 1 xs)) by ring.
    reflexivity.
Qed.
Lemma mod_eq_divide_sub__digit_final_residue :
  forall p x y,
    p <> 0 -> x mod p = y mod p -> (p | x - y).
Proof.
  intros p x y Hp Hxy.
  apply Zmod_divide; [exact Hp|].
  rewrite Zminus_mod, Hxy, Z.sub_diag.
  apply Z.mod_0_l; exact Hp.
Qed.
Lemma divide_sub_mod_eq_one__digit_final_residue :
  forall p x,
    p <> 0 -> (p | x - 1) -> x mod p = 1 mod p.
Proof.
  intros p x Hp Hdiv.
  destruct Hdiv as [k Hk].
  replace x with (1 + k * p) by lia.
  rewrite Z.mod_add by exact Hp.
  reflexivity.
Qed.
Lemma lucas_residues_length__digit_final_residue :
  forall p,
    1 < p ->
    Z.of_nat (length (map Z.of_nat (seq 1 (Z.to_nat (p - 1))))) =
    p - 1.
Proof.
  intros p Hp.
  rewrite length_map, length_seq.
  rewrite Z2Nat.id by lia.
  reflexivity.
Qed.
Lemma fermat_little_prime__digit_final_residue :
  forall p a,
    prime p -> 0 < a < p ->
    a ^ (p - 1) mod p = 1 mod p.
Proof.
  intros p a Hp Ha.
  pose proof (prime_ge_2 p Hp) as Hp2.
  set (residues := map Z.of_nat (seq 1 (Z.to_nat (p - 1)))).
  set (P := fold_right Z.mul 1 residues).
  pose proof
    (lucas_residues_mul_permutation__digit_final_residue p a Hp Ha)
    as Hperm.
  fold residues in Hperm.
  pose proof (fold_right_Zmul_permutation__digit_final_residue _ _ Hperm)
    as Hprod_eq.
  pose proof (fold_right_Zmul_map_mod__digit_final_residue p a residues
    ltac:(lia)) as Hmap_mod.
  rewrite Hprod_eq in Hmap_mod.
  assert (Hlength : Z.of_nat (length residues) = p - 1).
  { subst residues.
    apply lucas_residues_length__digit_final_residue; lia. }
  rewrite Hlength in Hmap_mod.
  fold P in Hmap_mod.
  assert (Hmod : (a ^ (p - 1) * P) mod p = P mod p).
  { symmetry. exact Hmap_mod. }
  assert (Hdiv : (p | (a ^ (p - 1) - 1) * P)).
  { replace ((a ^ (p - 1) - 1) * P)
      with (a ^ (p - 1) * P - P) by ring.
    apply mod_eq_divide_sub__digit_final_residue; [lia|exact Hmod]. }
  assert (Hrel : rel_prime p P).
  { apply prime_rel_prime; [exact Hp|].
    subst P residues.
    apply prime_product_not_divisible__digit_final_residue; [exact Hp|].
    apply Forall_forall.
    intros x Hx.
    apply in_lucas_residues__digit_final_residue in Hx; lia. }
  assert (Hdiv' : (p | a ^ (p - 1) - 1)).
  { replace ((a ^ (p - 1) - 1) * P)
      with (P * (a ^ (p - 1) - 1)) in Hdiv by ring.
    exact (Gauss p P (a ^ (p - 1) - 1) Hdiv Hrel). }
  apply divide_sub_mod_eq_one__digit_final_residue; [lia|exact Hdiv'].
Qed.
Lemma digit_multiplicative_residue__digit_final_residue :
  forall upper lower p numerator denominator inverse,
    0 <= lower <= upper ->
    upper < p ->
    PrimeForLucas p ->
    DigitProductProgress upper lower p (lower + 1)
      numerator denominator ->
    ModularPower denominator (p - 2) p inverse ->
    (numerator * inverse) mod p =
      LucasBinomialCoefficient upper lower mod p.
Proof.
  intros upper lower p numerator denominator inverse
    Hbounds Hupper Hprime Hprogress Hpower.
  pose proof (prime_for_lucas_prime__digit_final_residue p Hprime) as Hp.
  pose proof (prime_ge_2 p Hp) as Hp2.
  destruct Hprogress as [Hnum Hden].
  unfold DigitNumeratorPrefix, DigitDenominatorPrefix in Hnum, Hden.
  replace (lower + 1 - 1) with lower in Hnum, Hden by lia.
  assert (Hlowerp : 0 <= lower < p) by lia.
  assert (Hdennz : denominator <> 0).
  { rewrite Hden.
    apply digit_factorial_nonzero_mod_prime__digit_final_residue;
      assumption. }
  assert (Hdenrange : 0 < denominator < p).
  { pose proof
      (Z.mod_pos_bound (LucasRangeProduct 1 lower) p ltac:(lia)) as Hmodbound.
    rewrite <- Hden in Hmodbound.
    lia. }
  unfold ModularPower in Hpower.
  assert (Hinv : (denominator * inverse) mod p = 1).
  { rewrite Hpower.
    rewrite (Z.mul_mod_idemp_r denominator (denominator ^ (p - 2)) p)
      by lia.
    replace (denominator * denominator ^ (p - 2))
      with (denominator ^ (p - 1)).
    - rewrite
        (fermat_little_prime__digit_final_residue
          p denominator Hp Hdenrange).
      apply Z.mod_small; lia.
    - replace (p - 1) with (Z.succ (p - 2)) by lia.
      rewrite Z.pow_succ_r by lia.
      reflexivity. }
  pose proof
    (lucas_binomial_range_product_z__digit_final_residue
      upper lower Hbounds) as Hproduct.
  unfold DigitNumeratorPrefix, DigitDenominatorPrefix in Hproduct.
  assert
    (Hnumrel :
      numerator =
      (LucasBinomialCoefficient upper lower *
       LucasRangeProduct 1 lower) mod p).
  { rewrite Hnum, Hproduct. reflexivity. }
  rewrite Hnumrel.
  rewrite
    (Z.mul_mod_idemp_l
      (LucasBinomialCoefficient upper lower *
       LucasRangeProduct 1 lower) inverse p) by lia.
  replace
    ((LucasBinomialCoefficient upper lower *
      LucasRangeProduct 1 lower) * inverse)
    with
    (LucasBinomialCoefficient upper lower *
      (LucasRangeProduct 1 lower * inverse))
    by ring.
  rewrite <-
    (Z.mul_mod_idemp_r
      (LucasBinomialCoefficient upper lower)
      (LucasRangeProduct 1 lower * inverse) p) by lia.
  rewrite <-
    (Z.mul_mod_idemp_l (LucasRangeProduct 1 lower) inverse p) by lia.
  rewrite <- Hden.
  rewrite Hinv.
  rewrite Z.mul_1_r.
  reflexivity.
Qed.
Lemma lucas_nat_binomial_gt__lucas_digit_transition :
  forall n k, (n < k)%nat -> LucasNatBinomial n k = 0%nat.
Proof.
  induction n as [|n IH]; intros [|k] H; simpl; try lia.
  rewrite IH by lia.
  rewrite IH by lia.
  lia.
Qed.
Lemma lucas_nat_binomial_diag__lucas_digit_transition :
  forall n, LucasNatBinomial n n = 1%nat.
Proof.
  induction n as [|n IH]; simpl; auto.
  rewrite IH.
  rewrite lucas_nat_binomial_gt__lucas_digit_transition by lia.
  lia.
Qed.
Lemma lucas_nat_binomial_factorial__lucas_digit_transition :
  forall n k, (k <= n)%nat ->
    fact n =
      (LucasNatBinomial n k * fact k * fact (n - k))%nat.
Proof.
  induction n as [|n IH]; intros [|k] Hkn.
  - reflexivity.
  - lia.
  - simpl. lia.
  - simpl LucasNatBinomial.
    destruct (Nat.eq_dec k n) as [->|Hneq].
    + rewrite lucas_nat_binomial_diag__lucas_digit_transition.
      rewrite lucas_nat_binomial_gt__lucas_digit_transition by lia.
      simpl.
      rewrite Nat.sub_diag.
      simpl.
      nia.
    + assert (Hk : (k < n)%nat) by lia.
      pose proof (IH k ltac:(lia)) as IHk.
      pose proof (IH (S k) ltac:(lia)) as IHSk.
      rewrite Nat.sub_succ.
      assert (Hfactk : fact (S k) = (S k * fact k)%nat) by reflexivity.
      assert (Hfactdiff : fact (n - k) =
          ((n - k) * fact (n - S k))%nat).
      { replace (n - k)%nat with (S (n - S k)) by lia.
        simpl fact. lia. }
      rewrite Hfactk, Hfactdiff.
      replace
        ((LucasNatBinomial n k + LucasNatBinomial n (S k)) *
         (S k * fact k) * ((n - k) * fact (n - S k)))%nat
        with
        ((S k) * (LucasNatBinomial n k * fact k * fact (n - k)) +
         (n - k) *
           (LucasNatBinomial n (S k) * fact (S k) * fact (n - S k)))%nat.
      2: { rewrite Hfactk, Hfactdiff. ring. }
      rewrite <- IHk, <- IHSk.
      rewrite <- Nat.mul_add_distr_r.
      replace (S k + (n - k))%nat with (S n) by lia.
      reflexivity.
Qed.
Lemma prime_for_lucas_standard__lucas_digit_transition :
  forall p, PrimeForLucas p -> prime p.
Proof.
  intros p [Hp Hnodiv].
  apply (proj1 (prime_alt p)).
  split; [lia|].
  intros d Hd Hdivide.
  apply (Hnodiv d ltac:(lia)).
  apply Zdivide_mod.
  exact Hdivide.
Qed.
Lemma prime_mod_mul_cancel__lucas_digit_transition :
  forall p a x y,
    prime p -> rel_prime p a ->
    (a * x) mod p = (a * y) mod p ->
    x mod p = y mod p.
Proof.
  intros p a x y Hp Hcop Hmod.
  assert (Hppos : 0 < p) by (pose proof (prime_ge_2 p Hp); lia).
  assert (Hdivprod : (p | a * (x - y))).
  { apply Z.mod_divide; [lia|].
    rewrite Z.mul_sub_distr_l.
    rewrite Zminus_mod.
    rewrite Hmod.
    rewrite Z.sub_diag, Zmod_0_l.
    reflexivity. }
  pose proof (Gauss p a (x - y) Hdivprod Hcop) as Hdiv.
  destruct Hdiv as [q Hq].
  assert (Hx : x = y + q * p) by nia.
  rewrite Hx.
  rewrite Zplus_mod.
  rewrite Zmult_mod.
  rewrite Z_mod_same_full.
  simpl.
  rewrite Z.mul_0_r, Zmod_0_l, Z.add_0_r, Zmod_mod.
  reflexivity.
Qed.
Lemma prime_factorial_rel_prime__lucas_digit_transition :
  forall p r,
    prime p -> 0 <= r < p -> rel_prime p (Z.of_nat (fact (Z.to_nat r))).
Proof.
  intros p r Hp Hr.
  assert (Hrnat : Z.of_nat (Z.to_nat r) = r) by (rewrite Z2Nat.id; lia).
  remember (Z.to_nat r) as rn eqn:Hrn.
  revert r Hr Hrnat Hrn.
  induction rn as [|rn IH]; intros r Hr Hrnat Hrn.
  - simpl. apply rel_prime_sym, rel_prime_1.
  - change (rel_prime p (Z.of_nat ((S rn) * fact rn))).
    rewrite Nat2Z.inj_mul.
    assert (HSrn : Z.of_nat (S rn) = r).
    { exact Hrnat. }
    apply rel_prime_mult.
    + apply rel_prime_sym.
      apply rel_prime_le_prime; [exact Hp|].
      rewrite Nat2Z.inj_succ in HSrn.
      lia.
    + apply IH with (r := Z.of_nat rn).
      * split; [lia|].
        rewrite Nat2Z.inj_succ in HSrn.
        lia.
      * reflexivity.
      * symmetry. apply Nat2Z.id.
Qed.
Lemma prime_factorial_nat_rel_prime__lucas_digit_transition :
  forall p r,
    prime (Z.of_nat p) ->
    (r < p)%nat ->
    rel_prime (Z.of_nat p) (Z.of_nat (fact r)).
Proof.
  intros p r Hp Hr.
  replace (Z.of_nat (fact r)) with
    (Z.of_nat (fact (Z.to_nat (Z.of_nat r)))).
  2: { rewrite Nat2Z.id. reflexivity. }
  apply prime_factorial_rel_prime__lucas_digit_transition; [exact Hp|].
  split; [lia|now apply Nat2Z.inj_lt].
Qed.
Lemma nat_fold_mul_acc__lucas_digit_transition :
  forall l c,
    fold_right Nat.mul c l =
      (fold_right Nat.mul 1%nat l * c)%nat.
Proof.
  induction l as [|x xs IH]; intros c; simpl.
  - ring.
  - rewrite IH. ring.
Qed.
Lemma factorial_as_range_product__lucas_digit_transition :
  forall n,
    fact n =
      fold_right Nat.mul 1%nat (seq 1 n).
Proof.
  induction n as [|n IH].
  - reflexivity.
  - rewrite List.seq_S, List.fold_right_app.
  simpl.
  rewrite nat_fold_mul_acc__lucas_digit_transition.
  rewrite <- IH.
  ring.
Qed.
Lemma nat_range_product_app__lucas_digit_transition :
  forall start n m,
    fold_right Nat.mul 1%nat (seq start (n + m)) =
      (fold_right Nat.mul 1%nat (seq start n) *
       fold_right Nat.mul 1%nat (seq (start + n) m))%nat.
Proof.
  intros start n m.
  rewrite List.seq_app, List.fold_right_app.
  rewrite nat_fold_mul_acc__lucas_digit_transition.
  reflexivity.
Qed.
Lemma nat_mod_mul_congr__lucas_digit_transition :
  forall p a a' b b',
    p <> 0%nat ->
    (a mod p = a' mod p)%nat ->
    (b mod p = b' mod p)%nat ->
    ((a * b) mod p = (a' * b') mod p)%nat.
Proof.
  intros p a a' b b' Hp Ha Hb.
  rewrite Nat.Div0.mul_mod, Nat.Div0.mul_mod by exact Hp.
  rewrite Ha, Hb.
  repeat rewrite Nat.Div0.mod_mod by exact Hp.
  symmetry. apply Nat.Div0.mul_mod.
Qed.
Lemma z_mod_mul_congr__lucas_digit_transition :
  forall p a a' b b',
    a mod p = a' mod p ->
    b mod p = b' mod p ->
    (a * b) mod p = (a' * b') mod p.
Proof.
  intros p a a' b b' Ha Hb.
  rewrite Zmult_mod, Zmult_mod.
  rewrite Ha, Hb.
  repeat rewrite Zmod_mod.
  symmetry. apply Zmult_mod.
Qed.
Lemma rel_prime_nat_power_cast__lucas_digit_transition :
  forall p a n,
    rel_prime p (Z.of_nat a) ->
    rel_prime p (Z.of_nat (Nat.pow a n)).
Proof.
  intros p a n Ha. induction n as [|n IH].
  - simpl. apply rel_prime_sym, rel_prime_1.
  - simpl Nat.pow. rewrite Nat2Z.inj_mul.
    apply rel_prime_mult; assumption.
Qed.
Lemma lucas_nat_binomial_digit_step_core__lucas_digit_transition :
  forall p n k,
    (2 <= p)%nat ->
    prime (Z.of_nat p) ->
    Z.of_nat (LucasNatBinomial n k) mod Z.of_nat p =
      (Z.of_nat (LucasNatBinomial (n / p) (k / p)) *
       Z.of_nat (LucasNatBinomial (n mod p) (k mod p))) mod Z.of_nat p.
Proof.
  intros p n k Hp Hprime.
  set (R := fun start count : nat =>
    fold_right Nat.mul 1%nat (seq start count)).
  set (phi := fun q r : nat => R (q * p + 1)%nat r).
  set (psi := fun q : nat =>
    fold_right Nat.mul 1%nat
      (map (fun i => R (i * p + 1)%nat (p - 1)%nat) (seq 0 q))).
  assert (HpsiS : forall q,
      psi (S q) = (psi q * R (q * p + 1)%nat (p - 1)%nat)%nat).
  { intros q.
    unfold psi.
    rewrite List.seq_S, List.map_app, List.fold_right_app.
    simpl.
    rewrite nat_fold_mul_acc__lucas_digit_transition.
    rewrite Nat.mul_1_r.
    reflexivity. }
  assert (Hfactmult : forall q,
      fact (q * p) = (Nat.pow p q * fact q * psi q)%nat).
  { induction q as [|q IHq].
    - unfold psi. simpl. reflexivity.
    - replace (S q * p)%nat with (q * p + p)%nat by ring.
      rewrite factorial_as_range_product__lucas_digit_transition.
      rewrite nat_range_product_app__lucas_digit_transition.
      rewrite <- factorial_as_range_product__lucas_digit_transition.
      rewrite IHq.
      assert (Hblock :
        fold_right Nat.mul 1%nat (seq (q * p + 1)%nat p) =
          (fold_right Nat.mul 1%nat
             (seq (q * p + 1)%nat (p - 1)%nat) * (S q * p))%nat).
      { replace (seq (q * p + 1)%nat p) with
          (seq (q * p + 1)%nat (S (p - 1))) by (f_equal; lia).
        rewrite List.seq_S, List.fold_right_app.
        simpl.
        rewrite nat_fold_mul_acc__lucas_digit_transition, Nat.mul_1_r.
        replace (q * p + 1 + (p - 1))%nat with (S q * p)%nat by nia.
        reflexivity. }
      replace (1 + q * p)%nat with (q * p + 1)%nat by lia.
      rewrite Hblock.
      rewrite HpsiS.
      simpl Nat.pow.
      change (fact (S q)) with (S q * fact q)%nat.
      change (R (q * p + 1)%nat (p - 1)%nat) with
        (fold_right Nat.mul 1%nat (seq (q * p + 1)%nat (p - 1)%nat)).
      ring. }
  assert (Hfacteuclid : forall q r,
      fact (q * p + r) =
        (Nat.pow p q * fact q * phi q r * psi q)%nat).
  { intros q r.
    rewrite factorial_as_range_product__lucas_digit_transition.
    rewrite nat_range_product_app__lucas_digit_transition.
    rewrite <- factorial_as_range_product__lucas_digit_transition.
    rewrite Hfactmult.
    unfold phi, R.
    replace (1 + q * p)%nat with (q * p + 1)%nat by lia.
    ring. }
  assert (Hphi : forall q r,
      (phi q r mod p = fact r mod p)%nat).
  { intros q r. induction r as [|r IHr].
    - unfold phi, R. simpl. reflexivity.
    - unfold phi, R in *.
      rewrite List.seq_S, List.fold_right_app.
      simpl.
      rewrite nat_fold_mul_acc__lucas_digit_transition, Nat.mul_1_r.
      change (fact (S r)) with (S r * fact r)%nat.
      rewrite Nat.Div0.mul_mod, Nat.Div0.mul_mod.
      rewrite IHr.
      replace (q * p + 1 + r)%nat with (S r + q * p)%nat by ring.
      rewrite Nat.Div0.mod_add by lia.
      rewrite Nat.mul_comm.
      repeat rewrite Nat.Div0.mod_mod by lia.
      rewrite <- Nat.Div0.mul_mod by lia.
      reflexivity.
      all: lia. }
  assert (Hpsi : forall q,
      (psi q mod p = Nat.pow (fact (p - 1)) q mod p)%nat).
  { induction q as [|q IHq].
    - unfold psi. simpl. reflexivity.
    - rewrite HpsiS.
      rewrite Nat.Div0.mul_mod, IHq.
      change (R (q * p + 1)%nat (p - 1)%nat) with (phi q (p - 1)%nat).
      rewrite Hphi.
      simpl Nat.pow.
      rewrite Nat.Div0.mul_mod.
      repeat rewrite Nat.Div0.mod_mod by lia.
      rewrite <- Nat.Div0.mul_mod by lia.
      rewrite Nat.mul_comm.
      reflexivity.
      all: lia. }
  set (N := (n / p)%nat).
  set (n0 := (n mod p)%nat).
  set (K := (k / p)%nat).
  set (k0 := (k mod p)%nat).
  assert (Hn : n = (N * p + n0)%nat).
  { unfold N, n0. rewrite Nat.mul_comm. apply Nat.div_mod. lia. }
  assert (Hk : k = (K * p + k0)%nat).
  { unfold K, k0. rewrite Nat.mul_comm. apply Nat.div_mod. lia. }
  assert (Hn0 : (n0 < p)%nat).
  { unfold n0. apply Nat.mod_upper_bound. lia. }
  assert (Hk0 : (k0 < p)%nat).
  { unfold k0. apply Nat.mod_upper_bound. lia. }
  destruct (le_lt_dec k n) as [Hkn|Hnkbig].
  2: {
    rewrite lucas_nat_binomial_gt__lucas_digit_transition by exact Hnkbig.
    rewrite Nat2Z.inj_0, Zmod_0_l.
    destruct (le_lt_dec K N) as [HKN|HNK].
    - assert (Hdigits : (n0 < k0)%nat) by nia.
      rewrite (lucas_nat_binomial_gt__lucas_digit_transition n0 k0 Hdigits).
      rewrite Nat2Z.inj_0, Z.mul_0_r, Zmod_0_l. reflexivity.
    - rewrite (lucas_nat_binomial_gt__lucas_digit_transition N K HNK).
      rewrite Nat2Z.inj_0, Z.mul_0_l, Zmod_0_l. reflexivity. }
  destruct (le_lt_dec k0 n0) as [Hdigits|Hdigitgt].
  - assert (HKN : (K <= N)%nat) by nia.
    assert (Hdiff : (n - k = (N - K) * p + (n0 - k0))%nat) by nia.
    pose proof (lucas_nat_binomial_factorial__lucas_digit_transition n k Hkn)
      as Hbigfac.
    pose proof (lucas_nat_binomial_factorial__lucas_digit_transition N K HKN)
      as Hsmallfac.
    assert (Hbinwo :
      (phi K k0 * psi K * phi (N - K) (n0 - k0) * psi (N - K) *
       LucasNatBinomial n k =
       LucasNatBinomial N K * phi N n0 * psi N)%nat).
    { rewrite Hdiff in Hbigfac.
      rewrite Hn, Hk in Hbigfac.
      repeat rewrite Hfacteuclid in Hbigfac.
      replace N with (K + (N - K))%nat in Hbigfac by lia.
      rewrite Nat.pow_add_r in Hbigfac.
      replace (K + (N - K))%nat with N in Hbigfac by lia.
      replace (N * p + n0)%nat with n in Hbigfac by nia.
      replace (K * p + k0)%nat with k in Hbigfac by nia.
      rewrite Hsmallfac in Hbigfac.
      pose proof (lt_O_fact K).
      pose proof (lt_O_fact (N - K)).
      assert (Nat.pow p K <> 0)%nat by (apply Nat.pow_nonzero; lia).
      assert (Nat.pow p (N - K) <> 0)%nat by (apply Nat.pow_nonzero; lia).
      assert (0 < Nat.pow p K)%nat by lia.
      assert (0 < Nat.pow p (N - K))%nat by lia.
      assert (Hcommon :
        ((Nat.pow p K * Nat.pow p (N - K) * fact K * fact (N - K)) *
         (LucasNatBinomial N K * phi N n0 * psi N) =
         (Nat.pow p K * Nat.pow p (N - K) * fact K * fact (N - K)) *
         (phi K k0 * psi K * phi (N - K) (n0 - k0) * psi (N - K) *
          LucasNatBinomial n k))%nat).
      { transitivity
          ((Nat.pow p K * Nat.pow p (N - K) * LucasNatBinomial N K *
            fact K * fact (N - K) * phi N n0 * psi N)%nat).
        - ring.
        - transitivity
            ((Nat.pow p K * Nat.pow p (N - K) *
              (LucasNatBinomial N K * fact K * fact (N - K)) *
              phi N n0 * psi N)%nat).
          + ring.
          + transitivity
              ((LucasNatBinomial n k *
                (Nat.pow p K * fact K * phi K k0 * psi K) *
                (Nat.pow p (N - K) * fact (N - K) *
                 phi (N - K) (n0 - k0) * psi (N - K)))%nat).
            * exact Hbigfac.
            * ring. }
      apply Nat.mul_cancel_l in Hcommon.
      symmetry. exact Hcommon.
      all: nia. }
    set (fp := fact (p - 1)).
    set (F := (fact k0 * fact (n0 - k0) * Nat.pow fp N)%nat).
    assert (HA :
      (((phi K k0 * psi K) * phi (N - K) (n0 - k0) * psi (N - K)) mod p =
       (((fact k0 * Nat.pow fp K) * fact (n0 - k0) *
         Nat.pow fp (N - K)) mod p))%nat).
    { repeat apply nat_mod_mul_congr__lucas_digit_transition; try lia.
      - apply Hphi.
      - apply Hpsi.
      - apply Hphi.
      - apply Hpsi. }
    assert (Hpow : (Nat.pow fp K * Nat.pow fp (N - K) = Nat.pow fp N)%nat).
    { rewrite <- Nat.pow_add_r. f_equal. lia. }
    assert (HAF :
      (((phi K k0 * psi K) * phi (N - K) (n0 - k0) * psi (N - K)) mod p =
       F mod p)%nat).
    { transitivity
        ((((fact k0 * Nat.pow fp K) * fact (n0 - k0) *
           Nat.pow fp (N - K)) mod p)%nat); [exact HA|].
      unfold F. rewrite <- Hpow. f_equal. ring. }
    assert (HB :
      ((phi N n0 * psi N) mod p = (fact n0 * Nat.pow fp N) mod p)%nat).
    { apply nat_mod_mul_congr__lucas_digit_transition; try lia.
      - apply Hphi.
      - apply Hpsi. }
    pose proof (lucas_nat_binomial_factorial__lucas_digit_transition
      n0 k0 Hdigits) as Hdigitfac.
    assert (HBF :
      ((phi N n0 * psi N) mod p =
       (LucasNatBinomial n0 k0 * F) mod p)%nat).
    { rewrite HB. unfold F. rewrite Hdigitfac. f_equal. ring. }
    assert (HbinwoAssoc :
      ((((phi K k0 * psi K) * phi (N - K) (n0 - k0) * psi (N - K)) *
        LucasNatBinomial n k) =
       LucasNatBinomial N K * (phi N n0 * psi N))%nat).
    { transitivity
        ((phi K k0 * psi K * phi (N - K) (n0 - k0) * psi (N - K) *
          LucasNatBinomial n k)%nat); [ring|].
      rewrite Hbinwo. ring. }
    pose proof (f_equal (fun x => (x mod p)%nat) HbinwoAssoc) as Hbinmod.
    cbn in Hbinmod.
    assert (Hleft :
      ((((phi K k0 * psi K) * phi (N - K) (n0 - k0) * psi (N - K)) *
         LucasNatBinomial n k) mod p =
       (F * LucasNatBinomial n k) mod p)%nat).
    { apply nat_mod_mul_congr__lucas_digit_transition; [lia|exact HAF|reflexivity]. }
    assert (Hright :
      ((LucasNatBinomial N K * (phi N n0 * psi N)) mod p =
       (LucasNatBinomial N K * (LucasNatBinomial n0 k0 * F)) mod p)%nat).
    { apply nat_mod_mul_congr__lucas_digit_transition; [lia|reflexivity|exact HBF]. }
    assert (Hcong :
      ((F * LucasNatBinomial n k) mod p =
       (F * (LucasNatBinomial N K * LucasNatBinomial n0 k0)) mod p)%nat).
    { rewrite <- Hleft, Hbinmod, Hright. f_equal. ring. }
    assert (HFprime : rel_prime (Z.of_nat p) (Z.of_nat F)).
    { unfold F, fp. repeat rewrite Nat2Z.inj_mul.
      apply rel_prime_mult.
      - apply rel_prime_mult.
        + apply prime_factorial_nat_rel_prime__lucas_digit_transition;
            [exact Hprime|exact Hk0].
        + apply prime_factorial_nat_rel_prime__lucas_digit_transition;
            [exact Hprime|lia].
      - apply rel_prime_nat_power_cast__lucas_digit_transition.
        apply prime_factorial_nat_rel_prime__lucas_digit_transition;
          [exact Hprime|lia]. }
    pose proof (f_equal Z.of_nat Hcong) as HcongZ.
    repeat rewrite Nat2Z.inj_mod in HcongZ.
    repeat rewrite Nat2Z.inj_mul in HcongZ.
    pose proof (prime_mod_mul_cancel__lucas_digit_transition
      (Z.of_nat p) (Z.of_nat F)
      (Z.of_nat (LucasNatBinomial n k))
      (Z.of_nat (LucasNatBinomial N K) * Z.of_nat (LucasNatBinomial n0 k0))
      Hprime HFprime HcongZ) as Hcancel.
    exact Hcancel.
  - assert (HKNlt : (K < N)%nat) by nia.
    set (D := (N - (K + 1))%nat).
    set (rborrow := (p - (k0 - n0))%nat).
    assert (Hrborrow : (rborrow < p)%nat) by (unfold rborrow; lia).
    assert (Hdiff : (n - k = D * p + rborrow)%nat).
    { unfold D, rborrow. nia. }
    pose proof (lucas_nat_binomial_factorial__lucas_digit_transition n k Hkn)
      as Hbigfac.
    pose proof (lucas_nat_binomial_factorial__lucas_digit_transition N K ltac:(lia))
      as Hsmallfac.
    assert (Hbinp :
      (phi K k0 * psi K * phi D rborrow * psi D * LucasNatBinomial n k =
       p * LucasNatBinomial N K * (N - K) * phi N n0 * psi N)%nat).
    { rewrite Hdiff in Hbigfac.
      rewrite Hn, Hk in Hbigfac.
      repeat rewrite Hfacteuclid in Hbigfac.
      replace N with (K + 1 + D)%nat in Hbigfac by (unfold D; lia).
      rewrite Nat.pow_add_r in Hbigfac.
      simpl Nat.pow in Hbigfac.
      rewrite Nat.pow_add_r in Hbigfac.
      replace (K + 1 + D)%nat with N in Hbigfac by (unfold D; lia).
      replace (N * p + n0)%nat with n in Hbigfac by nia.
      replace (K * p + k0)%nat with k in Hbigfac by nia.
      rewrite Hsmallfac in Hbigfac.
      replace (N - K)%nat with (S D) in Hbigfac by (unfold D; lia).
      change (fact (S D)) with (S D * fact D)%nat in Hbigfac.
      replace (S D) with (N - K)%nat in Hbigfac by (unfold D; lia).
      assert (Nat.pow p K <> 0)%nat by (apply Nat.pow_nonzero; lia).
      assert (Nat.pow p D <> 0)%nat by (apply Nat.pow_nonzero; lia).
      pose proof (lt_O_fact K).
      pose proof (lt_O_fact D).
      replace (Nat.pow p 1) with p in Hbigfac by (simpl; ring).
      assert (Hcommon :
        ((Nat.pow p K * Nat.pow p D * fact K * fact D) *
         (p * LucasNatBinomial N K * (N - K) * phi N n0 * psi N) =
         (Nat.pow p K * Nat.pow p D * fact K * fact D) *
         (phi K k0 * psi K * phi D rborrow * psi D *
          LucasNatBinomial n k))%nat).
      { transitivity
          ((Nat.pow p K * p * Nat.pow p D *
            (LucasNatBinomial N K * fact K * ((N - K) * fact D)) *
            phi N n0 * psi N)%nat); [ring|].
        transitivity
          ((LucasNatBinomial n k *
            (Nat.pow p K * fact K * phi K k0 * psi K) *
            (Nat.pow p D * fact D * phi D rborrow * psi D))%nat).
        - exact Hbigfac.
        - ring. }
      apply Nat.mul_cancel_l in Hcommon.
      symmetry. exact Hcommon.
      all: nia. }
    set (fp := fact (p - 1)).
    set (F := (fact k0 * fact rborrow * Nat.pow fp (K + D))%nat).
    assert (HA :
      (((phi K k0 * psi K) * phi D rborrow * psi D) mod p = F mod p)%nat).
    { assert (HA0 :
        (((phi K k0 * psi K) * phi D rborrow * psi D) mod p =
         (((fact k0 * Nat.pow fp K) * fact rborrow * Nat.pow fp D) mod p))%nat).
      { repeat apply nat_mod_mul_congr__lucas_digit_transition; try lia.
        - apply Hphi. - apply Hpsi. - apply Hphi. - apply Hpsi. }
      transitivity
        ((((fact k0 * Nat.pow fp K) * fact rborrow * Nat.pow fp D) mod p)%nat);
        [exact HA0|].
      assert (HpowBD : (Nat.pow fp K * Nat.pow fp D = Nat.pow fp (K + D))%nat).
      { rewrite <- Nat.pow_add_r. reflexivity. }
      unfold F. rewrite <- HpowBD. f_equal. ring. }
    assert (HFprime : rel_prime (Z.of_nat p) (Z.of_nat F)).
    { unfold F, fp. repeat rewrite Nat2Z.inj_mul.
      apply rel_prime_mult.
      - apply rel_prime_mult.
        + apply prime_factorial_nat_rel_prime__lucas_digit_transition;
            [exact Hprime|exact Hk0].
        + apply prime_factorial_nat_rel_prime__lucas_digit_transition;
            [exact Hprime|exact Hrborrow].
      - apply rel_prime_nat_power_cast__lucas_digit_transition.
        apply prime_factorial_nat_rel_prime__lucas_digit_transition;
          [exact Hprime|lia]. }
    pose proof (f_equal (fun x => (x mod p)%nat) Hbinp) as Hbinpmod.
    cbn in Hbinpmod.
    assert (Hzero :
      ((((phi K k0 * psi K) * phi D rborrow * psi D) *
        LucasNatBinomial n k) mod p = 0)%nat).
    { transitivity
        ((phi K k0 * psi K * phi D rborrow * psi D *
          LucasNatBinomial n k) mod p)%nat; [f_equal; ring|].
      rewrite Hbinpmod.
      apply (proj2 (Nat.Div0.mod_divides
        (p * LucasNatBinomial N K * (N - K) * phi N n0 * psi N) p
        )).
      exists (LucasNatBinomial N K * (N - K) * phi N n0 * psi N)%nat.
      ring. }
    assert (HFzero : ((F * LucasNatBinomial n k) mod p = 0)%nat).
    { assert (HC := nat_mod_mul_congr__lucas_digit_transition p
        ((phi K k0 * psi K) * phi D rborrow * psi D) F
        (LucasNatBinomial n k) (LucasNatBinomial n k) ltac:(lia) HA eq_refl).
      rewrite <- HC. exact Hzero. }
    pose proof (f_equal Z.of_nat HFzero) as HFzeroZ.
    rewrite Nat2Z.inj_mod, Nat2Z.inj_mul, Nat2Z.inj_0 in HFzeroZ.
    pose proof (prime_mod_mul_cancel__lucas_digit_transition
      (Z.of_nat p) (Z.of_nat F) (Z.of_nat (LucasNatBinomial n k)) 0
      Hprime HFprime ltac:(rewrite Z.mul_0_r, Zmod_0_l; exact HFzeroZ)) as Hcancel.
    rewrite (lucas_nat_binomial_gt__lucas_digit_transition n0 k0 Hdigitgt).
    rewrite Nat2Z.inj_0, Z.mul_0_r, Zmod_0_l.
    exact Hcancel.
Qed.
Lemma lucas_nat_binomial_digit_step__lucas_digit_transition :
  forall upper lower p,
    0 <= upper -> 0 <= lower ->
    PrimeForLucas p ->
    LucasBinomialCoefficient upper lower mod p =
      (LucasBinomialCoefficient (upper / p) (lower / p) *
       LucasBinomialCoefficient (upper mod p) (lower mod p)) mod p.
Proof.
  intros upper lower p Hupper Hlower Hprime.
  assert (Hp : 2 <= p) by (destruct Hprime; lia).
  pose proof (prime_for_lucas_standard__lucas_digit_transition p Hprime)
    as HprimeZ.
  pose proof (lucas_nat_binomial_digit_step_core__lucas_digit_transition
    (Z.to_nat p) (Z.to_nat upper) (Z.to_nat lower) ltac:(lia)) as Hcore.
  assert (Hpcast : Z.of_nat (Z.to_nat p) = p) by (rewrite Z2Nat.id; lia).
  specialize (Hcore ltac:(rewrite Hpcast; exact HprimeZ)).
  unfold LucasBinomialCoefficient.
  rewrite <- Hpcast.
  rewrite Z2Nat.inj_div by lia.
  rewrite Z2Nat.inj_div by lia.
  rewrite Z2Nat.inj_mod by lia.
  rewrite Z2Nat.inj_mod by lia.
  repeat rewrite Nat2Z.id.
  exact Hcore.
Qed.
Lemma lucas_prefix_product_succ__lucas_digit_transition :
  forall upper lower p processed,
    p <> 0 ->
    LucasPrefixProduct upper lower p (S processed) =
      (LucasPrefixProduct upper lower p processed *
       (LucasBinomialCoefficient
          (LucasDigit upper p processed)
          (LucasDigit lower p processed) mod p)) mod p.
Proof.
  intros upper lower p processed Hp.
  unfold LucasPrefixProduct.
  rewrite List.seq_S, List.map_app, List.fold_right_app.
  simpl.
  rewrite Z.mul_mod_idemp_l by exact Hp.
  f_equal.
  induction (map
    (fun position : nat =>
       LucasBinomialCoefficient (LucasDigit upper p position)
         (LucasDigit lower p position) mod p)
    (seq 0 processed)) as [|x xs IH]; simpl.
  - rewrite Z.mul_1_r.
    destruct (LucasBinomialCoefficient (LucasDigit upper p processed)
      (LucasDigit lower p processed) mod p); reflexivity.
  - rewrite IH, <- Z.mul_assoc. reflexivity.
Qed.
Lemma lucas_progress_advance__lucas_digit_transition :
  forall original_upper original_lower p upper lower result retval,
    0 <= original_upper -> 0 <= original_lower ->
    0 <= upper -> 0 <= lower -> 0 <= result -> 0 <= retval ->
    PrimeForLucas p ->
    BinomialDigitResidue (Z.rem upper p) (Z.rem lower p) p retval ->
    LucasProgress original_upper original_lower p upper lower result ->
    LucasProgress original_upper original_lower p
      (Z.quot upper p) (Z.quot lower p) (Z.rem (result * retval) p).
Proof.
  intros original_upper original_lower p upper lower result retval
    Hou Hol Hu0 Hl0 Hr0 Hv0 Hprime Hdigit Hprogress.
  assert (Hp : 2 <= p) by (destruct Hprime; lia).
  destruct Hprogress as [processed [Hu [Hl [Hr Hres]]]].
  exists (S processed).
  assert (Hpowpos : 0 < p ^ Z.of_nat processed).
  { apply Z.pow_pos_nonneg; lia. }
  assert (Hupperdiv :
    Z.quot upper p = original_upper / p ^ Z.of_nat (S processed)).
  { rewrite Zquot_Zdiv_pos by lia.
    rewrite Hu.
    rewrite Zdiv_Zdiv by lia.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    f_equal. ring. }
  assert (Hlowerdiv :
    Z.quot lower p = original_lower / p ^ Z.of_nat (S processed)).
  { rewrite Zquot_Zdiv_pos by lia.
    rewrite Hl.
    rewrite Zdiv_Zdiv by lia.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    f_equal. ring. }
  repeat split.
  - exact Hupperdiv.
  - exact Hlowerdiv.
  - rewrite lucas_prefix_product_succ__lucas_digit_transition by lia.
    rewrite <- Hr.
    unfold LucasDigit.
    rewrite <- Hu, <- Hl.
    unfold BinomialDigitResidue in Hdigit.
    rewrite Zrem_Zmod_pos in Hdigit by lia.
    rewrite Zrem_Zmod_pos in Hdigit by lia.
    rewrite Zrem_Zmod_pos by nia.
    rewrite Hdigit.
    reflexivity.
  - rewrite Zrem_Zmod_pos by nia.
    rewrite Zquot_Zdiv_pos by lia.
    rewrite Zquot_Zdiv_pos by lia.
    rewrite Hres.
    pose proof (lucas_nat_binomial_digit_step__lucas_digit_transition
      upper lower p Hu0 Hl0 Hprime) as Hstep.
    unfold BinomialDigitResidue in Hdigit.
    rewrite Zrem_Zmod_pos in Hdigit by lia.
    rewrite Zrem_Zmod_pos in Hdigit by lia.
    set (Q := LucasBinomialCoefficient (upper / p) (lower / p)).
    set (D := LucasBinomialCoefficient (upper mod p) (lower mod p)).
    assert (HDmod : D mod p = retval mod p).
    { unfold D. rewrite Hdigit. symmetry. apply Zmod_mod. }
    assert (H1 :
      (result * LucasBinomialCoefficient upper lower) mod p =
      (result * (Q * D)) mod p).
    { apply z_mod_mul_congr__lucas_digit_transition; [reflexivity|].
      unfold Q, D. exact Hstep. }
    assert (H2 : (result * (Q * D)) mod p = ((result * D) * Q) mod p).
    { f_equal. ring. }
    assert (H3 : ((result * D) * Q) mod p = ((result * retval) * Q) mod p).
    { apply z_mod_mul_congr__lucas_digit_transition; [|reflexivity].
      apply z_mod_mul_congr__lucas_digit_transition; [reflexivity|exact HDmod]. }
    rewrite H1, H2, H3.
    unfold Q.
    symmetry. apply Zmult_mod_idemp_l.
Qed.
Lemma lucas_binomial_zero_from_low_digit__lucas_digit_transition :
  forall upper lower p,
    0 <= upper -> 0 <= lower ->
    PrimeForLucas p ->
    Z.rem upper p < Z.rem lower p ->
    LucasBinomialCoefficient upper lower mod p = 0.
Proof.
  intros upper lower p Hu Hl Hprime Hdigit.
  assert (Hp : 2 <= p) by (destruct Hprime; lia).
  rewrite Zrem_Zmod_pos in Hdigit by lia.
  rewrite Zrem_Zmod_pos in Hdigit by lia.
  pose proof (lucas_nat_binomial_digit_step__lucas_digit_transition
    upper lower p Hu Hl Hprime) as Hstep.
  assert (Hnatdigit :
    (Z.to_nat (upper mod p) < Z.to_nat (lower mod p))%nat).
  { apply Z2Nat.inj_lt; pose proof (Z.mod_pos_bound upper p ltac:(lia));
      pose proof (Z.mod_pos_bound lower p ltac:(lia)); lia. }
  unfold LucasBinomialCoefficient in Hstep.
  rewrite (lucas_nat_binomial_gt__lucas_digit_transition
    (Z.to_nat (upper mod p)) (Z.to_nat (lower mod p)) Hnatdigit) in Hstep.
  rewrite Nat2Z.inj_0, Z.mul_0_r, Zmod_0_l in Hstep.
  exact Hstep.
Qed.
Lemma lucas_progress_terminal_residue__lucas_terminal_return :
  forall original_upper original_lower p result,
    0 < p ->
    0 <= result < p ->
    LucasProgress original_upper original_lower p 0 0 result ->
    result = LucasBinomialCoefficient original_upper original_lower mod p.
Proof.
  intros original_upper original_lower p result Hp Hresult Hprogress.
  unfold LucasProgress in Hprogress.
  destruct Hprogress as [processed Hprogress].
  destruct Hprogress as [Hupper Hprogress].
  destruct Hprogress as [Hlower Hprogress].
  destruct Hprogress as [Hstored Hcoef].
  cbn [LucasBinomialCoefficient LucasNatBinomial] in Hcoef.
  rewrite Z.mul_1_r in Hcoef.
  assert (Hmod : result mod p = result).
  { apply Z.mod_small. exact Hresult. }
  rewrite Hmod in Hcoef.
  symmetry.
  exact Hcoef.
Qed.
