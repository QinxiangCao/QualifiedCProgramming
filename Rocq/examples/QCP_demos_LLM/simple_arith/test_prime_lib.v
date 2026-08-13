Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Zquot.
Require Export Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.

Local Open Scope Z_scope.

Definition HasFactorBetween (x lo hi : Z) : Prop :=
  exists k, lo <= k /\ k < hi /\ Z.divide k x.

Lemma no_factor_between_empty : forall x lo hi,
  hi <= lo ->
  ~ HasFactorBetween x lo hi.
Proof.
  unfold HasFactorBetween.
  intros x lo hi Hle [k [? [? _]]].
  lia.
Qed.

Lemma has_factor_between_hit : forall x lo hi d,
  2 <= d ->
  lo <= d ->
  d < x ->
  Z.rem x d = 0 ->
  hi = d + 1 ->
  HasFactorBetween x lo hi.
Proof.
  intros x lo hi d Hd Hlo Hlt Hmod Hhi.
  unfold HasFactorBetween.
  exists d.
  split; [lia |].
  split; [lia |].
  apply Z.rem_divide; lia.
Qed.

Lemma no_factor_between_snoc : forall x lo d,
  2 <= d ->
  lo <= d ->
  Z.rem x d <> 0 ->
  ~ HasFactorBetween x lo d ->
  ~ HasFactorBetween x lo (d + 1).
Proof.
  intros x lo d Hd Hlo Hmod Hnone [k [Hklo [Hkd Hdiv]]].
  destruct (Z.eq_dec k d) as [-> | Hneq].
  - destruct Hdiv as [q Hq].
    apply Hmod.
    apply Z.rem_divide.
    + lia.
    + exists q.
      exact Hq.
  - apply Hnone.
    exists k.
    repeat split; try lia.
    exact Hdiv.
Qed.

Lemma prime_of_no_factor_from_2 : forall x,
  2 <= x ->
  ~ HasFactorBetween x 2 x ->
  prime x.
Proof.
  intros x Hx Hnone.
  apply prime_alt.
  split; [lia |].
  intros n Hn Hdiv.
  apply Hnone.
  unfold HasFactorBetween.
  exists n.
  repeat split; try lia.
  exact Hdiv.
Qed.

Lemma not_prime_of_factor_between_2 : forall x,
  HasFactorBetween x 2 x ->
  ~ prime x.
Proof.
  intros x Hfactor Hprime.
  apply prime_alt in Hprime.
  destruct Hprime as [_ Hprime].
  destruct Hfactor as [k [Hlo [Hhi Hdiv]]].
  apply (Hprime k); lia || exact Hdiv.
Qed.

Lemma not_prime_of_mod_factor : forall x d,
  2 <= d ->
  d < x ->
  Z.rem x d = 0 ->
  ~ prime x.
Proof.
  intros x d Hd Hdx Hmod.
  apply not_prime_of_factor_between_2.
  unfold HasFactorBetween.
  exists d.
  repeat split; try lia.
  apply Z.rem_divide; lia.
Qed.

Lemma not_prime_lt_2 : forall x,
  x < 2 ->
  ~ prime x.
Proof.
  intros x Hlt Hprime.
  pose proof (prime_ge_2 x Hprime).
  lia.
Qed.

Lemma prime_of_no_factor_before_square : forall x d,
  2 <= x ->
  2 <= d ->
  x < d * d ->
  ~ HasFactorBetween x 2 d ->
  prime x.
Proof.
  intros x d Hx Hd Hsquare Hnone.
  apply prime_alt.
  split; [lia |].
  intros n Hn Hdiv.
  destruct (Z_lt_ge_dec n d) as [Hnd | Hdn].
  - apply Hnone.
    unfold HasFactorBetween.
    exists n.
    repeat split; try lia.
    exact Hdiv.
  - destruct Hdiv as [q Hq].
    assert (0 < q).
    {
      destruct (Z_le_gt_dec q 0) as [Hqle | Hqgt]; [| lia].
      assert (q * n <= 0) by nia.
      lia.
    }
    assert (q <> 1).
    {
      intros ->.
      lia.
    }
    assert (2 <= q) by lia.
    assert (q < d).
    {
      destruct (Z_lt_ge_dec q d) as [Hqd | Hdq]; [lia |].
      assert (d * d <= q * n) by nia.
      lia.
    }
    apply Hnone.
    unfold HasFactorBetween.
    exists q.
    repeat split; try lia.
    exists n.
    lia.
Qed.
