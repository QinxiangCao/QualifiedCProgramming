From Coq Require Import ZArith List Znumtheory Sorting.Sorted.
Import ListNotations.
Local Open Scope Z_scope.

(** [PrimeFactorization original factors] is the public mathematical meaning of
    the initialized output segment.  Membership is deliberately bidirectional:
    the segment contains no non-prime/non-divisor and omits no prime divisor of
    [original].  [Sorted Z.le] records the program's increasing trial-divisor
    order, while the product equation fixes multiplicities to the actual prime
    factorization rather than merely listing each distinct divisor once. *)
Definition PrimeFactorization (original : Z) (factors : list Z) : Prop :=
  Forall prime factors /\
  Sorted Z.le factors /\
  fold_right Z.mul 1 factors = original /\
  (forall q : Z,
      In q factors <-> prime q /\ Z.divide q original).

(** Internal mathematical state shared by both trial-division loop heads.
    Machine ranges, [cnt]/list-length bindings, modulo guards, and array
    ownership deliberately remain visible in the C annotation. *)
Definition FactorizationProgress
    (original : Z) (factors : list Z) (remaining candidate : Z) : Prop :=
  fold_right Z.mul 1 factors * remaining = original /\
  Forall prime factors /\
  Sorted Z.le factors /\
  Forall (fun factor => factor <= candidate) factors /\
  (forall d : Z,
      2 <= d < candidate -> ~ Z.divide d remaining).

From Coq Require Import Lia.
Lemma prime_product_exceeds_length__progress_transitions :
  forall factors : list Z,
    Forall prime factors ->
    Zlength factors < fold_right Z.mul 1 factors.
Proof.
  intros factors Hprime.
  induction Hprime as [| factor factors Hfactor Hprime IH].
  - rewrite Zlength_nil. simpl. lia.
  - rewrite Zlength_cons. simpl.
    pose proof (prime_ge_2 factor Hfactor) as Hfactor_ge.
    assert (0 <= Zlength factors) as Hlength_nonneg.
    { rewrite Zlength_correct. lia. }
    nia.
Qed.
Lemma fold_right_mul_snoc__progress_transitions :
  forall (factors : list Z) (factor : Z),
    fold_right Z.mul 1 (factors ++ [factor]) =
    fold_right Z.mul 1 factors * factor.
Proof.
  intros factors factor.
  induction factors as [| head tail IH].
  - change (factor * 1 = 1 * factor).
    now rewrite Z.mul_1_r, Z.mul_1_l.
  - simpl. rewrite IH, Z.mul_assoc. reflexivity.
Qed.
Lemma sorted_snoc_le__progress_transitions :
  forall (factors : list Z) (factor : Z),
    Sorted Z.le factors ->
    Forall (fun x => x <= factor) factors ->
    Sorted Z.le (factors ++ [factor]).
Proof.
  induction factors as [| head tail IH].
  - intros factor _ _. simpl. repeat constructor.
  - intros factor Hsorted Hbound.
    inversion Hsorted as [| head' tail' Htail_sorted Hhead_rel]; subst.
    inversion Hbound as [| head' tail' Hhead_bound Htail_bound]; subst.
    simpl. constructor.
    + apply IH; assumption.
    + destruct tail as [| next rest].
      * constructor. exact Hhead_bound.
      * inversion Hhead_rel; subst. constructor. assumption.
Qed.
Lemma factorization_progress_room__progress_transitions :
  forall (original : Z) (factors : list Z) (remaining candidate : Z),
    2 <= candidate ->
    candidate <= remaining ->
    FactorizationProgress original factors remaining candidate ->
    Zlength factors + 1 < original.
Proof.
  intros original factors remaining candidate Hcandidate Hremaining Hprogress.
  unfold FactorizationProgress in Hprogress.
  destruct Hprogress as [Hproduct [Hprimes _]].
  pose proof
    (prime_product_exceeds_length__progress_transitions factors Hprimes)
    as Hproduct_lower.
  assert (0 <= Zlength factors) as Hlength_nonneg.
  { rewrite Zlength_correct. lia. }
  rewrite <- Hproduct.
  nia.
Qed.
Lemma factorization_progress_extract__progress_transitions :
  forall (original : Z) (factors : list Z) (remaining candidate : Z),
    1 <= remaining ->
    2 <= candidate ->
    candidate <= remaining ->
    Z.rem remaining candidate = 0 ->
    FactorizationProgress original factors remaining candidate ->
    FactorizationProgress original (factors ++ [candidate])
      (Z.quot remaining candidate) candidate /\
    (Z.quot remaining candidate = 1 \/
     candidate <= Z.quot remaining candidate).
Proof.
  intros original factors remaining candidate Hremaining Hcandidate
    Hcandidate_remaining Hmod Hprogress.
  unfold FactorizationProgress in Hprogress.
  destruct Hprogress as
    [Hproduct [Hprimes [Hsorted [Hbounds Hexcluded]]]].
  assert (candidate <> 0) as Hcandidate_nonzero by lia.
  assert (remaining = candidate * Z.quot remaining candidate) as Hdivide_exact.
  { apply (proj2 (Z.quot_exact remaining candidate Hcandidate_nonzero)).
    exact Hmod. }
  assert (prime candidate) as Hcandidate_prime.
  { apply (proj1 (prime_alt candidate)).
    split.
    - lia.
    - intros divisor Hdivisor_bounds Hdivisor_candidate.
      apply (Hexcluded divisor); [lia |].
      destruct Hdivisor_candidate as [quotient Hquotient].
      exists (quotient * Z.quot remaining candidate).
      rewrite Hdivide_exact at 1.
      rewrite Hquotient at 1.
      ring. }
  assert (1 <= Z.quot remaining candidate) as Hquotient_positive by nia.
  assert
    (Z.quot remaining candidate = 1 \/
     candidate <= Z.quot remaining candidate)
    as Hquotient_cases.
  { destruct (Z.eq_dec (Z.quot remaining candidate) 1) as [Heq | Hneq].
    - left. exact Heq.
    - right.
      assert (2 <= Z.quot remaining candidate) as Hquotient_ge by lia.
      destruct (Z_lt_ge_dec (Z.quot remaining candidate) candidate)
        as [Hlt | Hge].
      + exfalso.
        apply (Hexcluded (Z.quot remaining candidate)); [lia |].
        exists candidate.
        exact Hdivide_exact.
      + lia. }
  split.
  - unfold FactorizationProgress.
    repeat split.
    + rewrite fold_right_mul_snoc__progress_transitions.
      rewrite <- Hproduct.
      rewrite Hdivide_exact at 2.
      ring.
    + apply Forall_app. split.
      * exact Hprimes.
      * constructor; [exact Hcandidate_prime | constructor].
    + apply sorted_snoc_le__progress_transitions; assumption.
    + apply Forall_app. split.
      * exact Hbounds.
      * constructor; [lia | constructor].
    + intros divisor Hdivisor_bounds Hdivisor_quotient.
      apply (Hexcluded divisor Hdivisor_bounds).
      destruct Hdivisor_quotient as [quotient Hquotient].
      exists (candidate * quotient).
      rewrite Hdivide_exact, Hquotient. ring.
  - exact Hquotient_cases.
Qed.
Lemma factorization_progress_advance__progress_transitions :
  forall (original : Z) (factors : list Z) (remaining candidate : Z),
    2 <= candidate ->
    Z.rem remaining candidate <> 0 ->
    FactorizationProgress original factors remaining candidate ->
    FactorizationProgress original factors remaining (candidate + 1).
Proof.
  intros original factors remaining candidate Hcandidate Hmod Hprogress.
  assert (candidate <> 0) as Hcandidate_nonzero by lia.
  unfold FactorizationProgress in *.
  destruct Hprogress as
    [Hproduct [Hprimes [Hsorted [Hbounds Hexcluded]]]].
  repeat split.
  - exact Hproduct.
  - exact Hprimes.
  - exact Hsorted.
  - rewrite Forall_forall in Hbounds |- *.
    intros factor Hin.
    specialize (Hbounds factor Hin). lia.
  - intros divisor Hdivisor_bounds Hdivisor_remaining.
    destruct (Z_lt_ge_dec divisor candidate) as [Hlt | Hge].
    + apply (Hexcluded divisor); [lia | exact Hdivisor_remaining].
    + replace divisor with candidate in * by lia.
      apply Hmod.
      apply (proj2 (Z.rem_divide remaining candidate Hcandidate_nonzero)).
      exact Hdivisor_remaining.
Qed.
Lemma prime_divides_factor_product_iff_in__final_result :
  forall (q : Z) (factors : list Z),
    prime q ->
    Forall prime factors ->
    (Z.divide q (fold_right Z.mul 1 factors) <-> In q factors).
Proof.
  intros q factors Hq.
  induction factors as [| a factors IH]; intros Hall.
  - simpl.
    split.
    + intros Hdiv.
      assert (Hq_le_one : q <= 1).
      {
        apply Z.divide_pos_le; [lia | exact Hdiv].
      }
      destruct Hq as [Hq_gt _].
      lia.
    + contradiction.
  - inversion Hall as [| a' factors' Ha Hfactors]; subst.
    simpl.
    split.
    + intros Hdiv.
      destruct (prime_mult q Hq a (fold_right Z.mul 1 factors) Hdiv)
        as [Hdiv_a | Hdiv_factors].
      * left.
        destruct (prime_divisors a Ha q Hdiv_a)
          as [Hq_one | [Hq_neg_one | [Hq_a | Hq_neg_a]]].
        -- pose proof (prime_ge_2 q Hq).
           lia.
        -- pose proof (prime_ge_2 q Hq).
           lia.
        -- lia.
        -- pose proof (prime_ge_2 q Hq).
           pose proof (prime_ge_2 a Ha).
           lia.
      * right.
        apply (proj1 (IH Hfactors)).
        exact Hdiv_factors.
    + intros [Ha_q | Hin].
      * subst a.
        exists (fold_right Z.mul 1 factors).
        ring.
      * destruct (proj2 (IH Hfactors) Hin) as [k Hk].
        exists (a * k).
        nia.
Qed.
Lemma factorization_progress_complete__final_result :
  forall (original : Z) (factors : list Z) (remaining candidate : Z),
    1 <= remaining ->
    (remaining = 1 \/ remaining < candidate) ->
    FactorizationProgress original factors remaining candidate ->
    PrimeFactorization original factors.
Proof.
  intros original factors remaining candidate Hremaining Hfinished Hprogress.
  unfold FactorizationProgress in Hprogress.
  destruct Hprogress as
    [Hproduct [Hprimes [Hsorted [Hfactor_bound Hexcluded]]]].
  assert (Hremaining_one : remaining = 1).
  {
    destruct Hfinished as [Hone | Hlt]; [exact Hone |].
    destruct (Z.eq_dec remaining 1) as [Hone | Hnot_one];
      [exact Hone |].
    exfalso.
    apply (Hexcluded remaining ltac:(lia)).
    exists 1.
    ring.
  }
  subst remaining.
  rewrite Z.mul_1_r in Hproduct.
  unfold PrimeFactorization.
  refine (conj Hprimes (conj Hsorted (conj Hproduct _))).
  intros q.
  split.
  - intros Hin.
    assert (Hq_prime : prime q).
    {
      pose proof Hprimes as Hprimes_forall.
      rewrite Forall_forall in Hprimes_forall.
      apply Hprimes_forall.
      exact Hin.
    }
    split; [exact Hq_prime |].
    rewrite <- Hproduct.
    apply (proj2
      (prime_divides_factor_product_iff_in__final_result
        q factors Hq_prime Hprimes)).
    exact Hin.
  - intros [Hq_prime Hq_divides].
    rewrite <- Hproduct in Hq_divides.
    apply (proj1
      (prime_divides_factor_product_iff_in__final_result
        q factors Hq_prime Hprimes)).
    exact Hq_divides.
Qed.
