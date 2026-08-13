Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.

Import ListNotations.
Local Open Scope Z_scope.

(** Mathematical primality, independent of the concrete sieve arrays. *)
Definition StrictPrime (p : Z) : Prop :=
  1 < p /\
  forall d : Z,
    0 < d ->
    Z.divide d p ->
    d = 1 \/ d = p.

(** [LeastPrimeFactor p k] says [p] is the least prime divisor of [k]. *)
Definition LeastPrimeFactor (p k : Z) : Prop :=
  StrictPrime p /\
  Z.divide p k /\
  forall q : Z,
    StrictPrime q ->
    Z.divide q k ->
    p <= q.

(** Final meaning of a single [flag[k]] entry.  Primes keep their own value;
    composites store their least prime factor. *)
Definition FlagEntryFor (k value : Z) : Prop :=
  (StrictPrime k /\ value = k) \/
  (~ StrictPrime k /\ LeastPrimeFactor value k).

(** Logical position [k - 2] represents the concrete [flag[k]] slot. *)
Definition LeastPrimeFlagList (n : Z) (flags : list Z) : Prop :=
  Zlength flags = n - 1 /\
  forall k : Z,
    2 <= k /\ k <= n ->
    FlagEntryFor k (Znth (k - 2) flags 0).

(** The first [tot] entries of [primes] are exactly the primes not exceeding
    [bound], in increasing order.  Concrete index [pos] is logical [pos - 1]. *)
Definition PrimePrefixList (bound tot : Z) (primes : list Z) : Prop :=
  0 <= tot /\
  (forall pos : Z,
    1 <= pos /\ pos <= tot ->
    StrictPrime (Znth (pos - 1) primes 0) /\
    Znth (pos - 1) primes 0 <= bound) /\
  (forall p : Z,
    2 <= p /\ p <= bound ->
    (StrictPrime p <->
     exists pos : Z,
       1 <= pos /\ pos <= tot /\
       Znth (pos - 1) primes 0 = p)) /\
  (forall p q : Z,
    1 <= p /\ p < q /\ q <= tot ->
    Znth (p - 1) primes 0 < Znth (q - 1) primes 0).

Definition PrimeBounds (n tot : Z) (primes : list Z) : Prop :=
  forall pos : Z,
    1 <= pos /\ pos <= tot ->
    2 <= Znth (pos - 1) primes 0 /\
    Znth (pos - 1) primes 0 <= n.

Definition PriorNonDivisibility
    (current j : Z) (primes : list Z) : Prop :=
  forall pos : Z,
    1 <= pos /\ pos < j ->
    ~ Z.divide (Znth (pos - 1) primes 0) current.

Definition ProductIndex
    (current j : Z) (primes : list Z) : Z :=
  current * Znth (j - 1) primes 0.

Definition FlagValue (flags : list Z) (k : Z) : Z :=
  Znth (k - 2) flags 0.

(** Progress made by the current base inside the Euler inner loop.  Before the
    loop reaches index [j], every in-range product [current * primes[pos]] with
    [pos < j] has already been written and is a sound non-self flag entry. *)
Definition CurrentProductMarked
    (n current pos : Z) (flags primes : list Z) : Prop :=
  2 <= ProductIndex current pos primes /\
  ProductIndex current pos primes <= n ->
  FlagValue flags (ProductIndex current pos primes) =
    Znth (pos - 1) primes 0 /\
  FlagValue flags (ProductIndex current pos primes) <>
    ProductIndex current pos primes /\
  FlagEntryFor (ProductIndex current pos primes)
    (FlagValue flags (ProductIndex current pos primes)).

Definition CurrentBaseProgress
    (n current j : Z) (flags primes : list Z) : Prop :=
  forall pos : Z,
    1 <= pos /\ pos < j ->
    CurrentProductMarked n current pos flags primes.

(** A pair [base, primes[pos]] is exactly the kind of product that an earlier
    Euler-sieve inner loop would have written: [base] was already processed,
    the prime was already known by then, and no smaller processed prime had
    broken that inner loop first. *)
Definition EarlierLinearProduct
    (frontier k tot : Z) (primes : list Z) : Prop :=
  exists base pos : Z,
    2 <= base /\ base < frontier /\
    1 <= pos /\ pos <= tot /\
    Znth (pos - 1) primes 0 <= base /\
    PriorNonDivisibility base pos primes /\
    k = base * Znth (pos - 1) primes 0.

Definition FutureSelfCompleteness
    (frontier k tot : Z) (primes : list Z) : Prop :=
  ~ EarlierLinearProduct frontier k tot primes.

Definition FutureFlagState
    (frontier k tot : Z) (flags primes : list Z) : Prop :=
  (FlagValue flags k <> k -> FlagEntryFor k (FlagValue flags k)) /\
  (FlagValue flags k = k -> FutureSelfCompleteness frontier k tot primes).

(** At an outer-loop boundary, slots up to the current index already have their
    final least-prime-factor meaning.  Future non-self slots are sound marks.
    Future self-valued slots are not arbitrary: they have not been reachable as
    an eligible product of an earlier processed base and known prime.  This is
    the completeness fact needed to classify the successor slot when the outer
    boundary advances. *)
Definition EulerFlagState
    (n frontier tot : Z) (flags primes : list Z) : Prop :=
  Zlength flags = n - 1 /\
  forall k : Z,
    2 <= k /\ k <= n ->
    (k <= frontier -> FlagEntryFor k (FlagValue flags k)) /\
    (frontier < k -> FutureFlagState frontier k tot flags primes).

Definition EulerSieveResult
    (n tot : Z) (flags primes : list Z) : Prop :=
  Zlength flags = n - 1 /\
  Zlength primes = n /\
  0 <= tot /\ tot <= n /\
  LeastPrimeFlagList n flags /\
  PrimePrefixList n tot primes.

(** Initialization loop: all concrete entries before [next] have been written
    to their own index value. *)
Definition EulerInitPrefix (n next : Z) (flags : list Z) : Prop :=
  Zlength flags = n - 1 /\
  forall k : Z,
    2 <= k /\ k < next ->
    Znth (k - 2) flags 0 = k.

(** Outer-loop state before processing [next].  Entries below [next] already
    have their final least-prime-factor meaning; the current slot [next] is
    meaningful too when [next <= n].  Future slots are allowed to remain at
    their initial self value, but any future non-self mark must already be a
    valid least-prime-factor mark.  [primes[1..tot]] lists exactly the primes
    below [next]. *)
Definition EulerOuterState
    (n next tot : Z) (flags primes : list Z) : Prop :=
  EulerFlagState n next tot flags primes /\
  Zlength primes = n /\
  2 <= next /\ next <= n + 1 /\
  0 <= tot /\ tot < next /\
  PrimePrefixList (next - 1) tot primes /\
  PrimeBounds n tot primes.

(** Inner-loop state after [current] has been classified and, if prime, appended
    to the prime prefix.  The current flag slot remains classified throughout
    the loop, future non-self marks remain sound, all current-base products
    before [j] have already been marked, and all primes before [j] are known not
    to divide [current].  If the product guard is already false, the state is
    strong enough to move to the next outer iteration. *)
Definition EulerInnerState
    (n current j tot : Z) (flags primes : list Z) : Prop :=
  EulerFlagState n current tot flags primes /\
  Zlength primes = n /\
  2 <= current /\ current <= n /\
  1 <= j /\ j <= tot /\
  0 < tot /\ tot <= n /\
  tot < current + 1 /\
  PrimePrefixList current tot primes /\
  PrimeBounds current tot primes /\
  CurrentBaseProgress n current j flags primes /\
  PriorNonDivisibility current j primes /\
  (ProductIndex current j primes > n ->
   EulerOuterState n (current + 1) tot flags primes).

(** State immediately after writing [flag[current * primes[j]]].  The written
    product is a sound least-prime-factor mark.  The state also records the two
    possible exits from the just-tested prime: divisibility breaks to the next
    outer state, while non-divisibility makes the [j + 1] inner state valid. *)
Definition EulerInnerMarkedState
    (n current j tot : Z) (flags primes : list Z) : Prop :=
  EulerInnerState n current j tot flags primes /\
  ProductIndex current j primes <= n /\
  FlagEntryFor (ProductIndex current j primes)
    (Znth (j - 1) primes 0) /\
  FlagValue flags (ProductIndex current j primes) =
    Znth (j - 1) primes 0 /\
  CurrentBaseProgress n current (j + 1) flags primes /\
  (Z.divide (Znth (j - 1) primes 0) current ->
   EulerOuterState n (current + 1) tot flags primes) /\
  (~ Z.divide (Znth (j - 1) primes 0) current ->
   EulerInnerState n current (j + 1) tot flags primes).

Require Import Coq.ZArith.Znumtheory.
Require Import Coq.ZArith.Wf_Z.
Lemma StrictPrime_two__core_invariants :
  StrictPrime 2.
Proof.
  unfold StrictPrime.
  split; [lia |].
  intros d Hdpos [q Hq].
  destruct (Z.eq_dec d 1) as [-> | Hneq].
  - left; reflexivity.
  - right.
    assert (d <= 2).
    {
      apply Z.divide_pos_le; [lia |].
      exists q.
      exact Hq.
    }
    lia.
Qed.
Lemma EulerInitPrefix_start__core_invariants :
  forall (n : Z) (flags : list Z),
    Zlength flags = n - 1 ->
    EulerInitPrefix n 2 flags.
Proof.
  intros n flags Hlen.
  split; [exact Hlen |].
  intros k Hrange.
  lia.
Qed.
Lemma EulerInitPrefix_step__core_invariants :
  forall (n i : Z) (flags : list Z),
    i <= n ->
    2 <= i ->
    EulerInitPrefix n i flags ->
    EulerInitPrefix n (i + 1) (replace_Znth (i - 2) i flags).
Proof.
  intros n i flags Hi_le Hi_ge [Hlen Hprefix].
  split.
  - rewrite Zlength_replace_Znth.
    exact Hlen.
  - intros k Hrange.
    destruct (Z.eq_dec k i) as [-> | Hneq].
    + rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
      reflexivity.
    + rewrite Znth_replace_Znth_Diff by (rewrite ?Hlen; lia).
      apply Hprefix.
      lia.
Qed.
Lemma EulerInitPrefix_finish_outer__core_invariants :
  forall (n i : Z) (flags primes : list Z),
    i > n ->
    2 <= n ->
    Zlength primes = n ->
    EulerInitPrefix n i flags ->
    EulerOuterState n 2 0 flags primes.
Proof.
  intros n i flags primes Hi_gt Hn_ge Hprimes_len [Hflags_len Hprefix].
  unfold EulerOuterState.
  split.
  - unfold EulerFlagState.
    split; [exact Hflags_len |].
    intros k Hkrange.
    split.
    + intros Hk_le.
      assert (Hk_eq : k = 2) by lia.
      subst k.
      left.
      split; [apply StrictPrime_two__core_invariants |].
      unfold FlagValue.
      apply Hprefix.
      lia.
    + intros Hk_gt.
      unfold FutureFlagState.
      split.
      * intros Hnonself.
        exfalso.
        apply Hnonself.
        unfold FlagValue.
        apply Hprefix.
        lia.
      * intros _.
        unfold FutureSelfCompleteness, EarlierLinearProduct.
        intros [base [pos [Hbase_ge [Hbase_lt _]]]].
        lia.
  - split; [exact Hprimes_len |].
    split; [lia |].
    split; [lia |].
    split; [lia |].
    split; [lia |].
    split.
    + unfold PrimePrefixList.
      split; [lia |].
      split.
      * intros pos Hpos.
        lia.
      * split.
        -- intros p Hp.
           lia.
        -- intros p q Hpq.
           lia.
    + unfold PrimeBounds.
      intros pos Hpos.
    lia.
Qed.
Lemma prime_to_StrictPrime__core_invariants :
  forall p : Z,
    prime p ->
    StrictPrime p.
Proof.
  intros p Hp.
  pose proof (prime_ge_2 p Hp) as Hp_ge.
  split.
  - lia.
  - intros d Hdpos Hdiv.
    destruct (prime_divisors p Hp d Hdiv) as [Hd | [Hd | [Hd | Hd]]];
      subst; lia.
Qed.
Lemma StrictPrime_to_prime__core_invariants :
  forall p : Z,
    StrictPrime p ->
    prime p.
Proof.
  intros p [Hp_gt Hp_div].
  apply prime_alt.
  unfold prime'.
  split; [exact Hp_gt |].
  intros d Hd_range Hd_div.
  destruct (Hp_div d ltac:(lia) Hd_div) as [-> | ->]; lia.
Qed.
Lemma StrictPrime_divisor_self_or_all__core_invariants :
  forall p q : Z,
    StrictPrime p ->
    StrictPrime q ->
    Z.divide q p ->
    q <= p.
Proof.
  intros p q Hp Hq Hdiv.
  destruct Hp as [Hp_gt Hp_div].
  destruct Hq as [Hq_gt _].
  destruct (Hp_div q ltac:(lia) Hdiv) as [-> | ->]; lia.
Qed.
Lemma EulerOuterState_nonself_first_prime_facts__core_invariants :
  forall (n i tot : Z) (flags primes : list Z),
    Znth (i - 2) flags 0 <> i ->
    i <= n ->
    2 <= i ->
    EulerOuterState n i tot flags primes ->
    1 <= tot /\
    2 <= Znth 0 primes 0 /\
    Znth 0 primes 0 <= i.
Proof.
  intros n i tot flags primes Hnonself Hi_le Hi_ge Houter.
  unfold EulerOuterState in Houter.
  destruct Houter as
    [Hflag_state
     [Hprimes_len [Hnext_ge [Hnext_le [Htot_ge [Htot_lt [Hprefix Hbounds]]]]]]].
  unfold EulerFlagState in Hflag_state.
  destruct Hflag_state as [_ Hflag].
  destruct (Hflag i ltac:(lia)) as [Hclassified _].
  specialize (Hclassified ltac:(lia)).
  unfold FlagValue in Hclassified.
  destruct Hclassified as [[_ Hself] | [_ Hleast]].
  - contradiction.
  - destruct Hleast as [Hleast_prime [Hleast_div Hleast_min]].
    destruct Hleast_prime as [Hleast_gt_one Hleast_divs].
    assert (Hleast_le_i : Znth (i - 2) flags 0 <= i).
    {
      apply Z.divide_pos_le; [lia | exact Hleast_div].
    }
    assert (Hleast_lt_i : Znth (i - 2) flags 0 < i).
    {
      destruct (Z.eq_dec (Znth (i - 2) flags 0) i) as [Heq | Hneq];
        [contradiction | lia].
    }
    unfold PrimePrefixList in Hprefix.
    destruct Hprefix as
      [Htot_nonneg [Hprime_at [Hprime_complete Hsorted]]].
    destruct
      (proj1
         (Hprime_complete (Znth (i - 2) flags 0) ltac:(lia))
         (conj Hleast_gt_one Hleast_divs))
      as [pos [Hpos_ge [Hpos_le Hpos_value]]].
    assert (Htot_pos : 1 <= tot) by lia.
    assert (Hfirst_upper : Znth 0 primes 0 <= i).
    {
      destruct (Z.eq_dec pos 1) as [Hpos_eq | Hpos_neq].
      - replace (pos - 1) with 0 in Hpos_value by lia.
        rewrite Hpos_value.
        lia.
      - assert (Hpos_gt : 1 < pos) by lia.
        specialize (Hsorted 1 pos ltac:(lia)).
        replace (1 - 1) with 0 in Hsorted by lia.
        rewrite Hpos_value in Hsorted.
        lia.
    }
    assert (Hfirst_lower : 2 <= Znth 0 primes 0).
    {
      unfold PrimeBounds in Hbounds.
      specialize (Hbounds 1 ltac:(lia)).
      replace (1 - 1) with 0 in Hbounds by lia.
      lia.
    }
    repeat split; assumption.
Qed.
Lemma PrimeBounds_from_prefix__core_invariants :
  forall (bound tot : Z) (primes : list Z),
    PrimePrefixList bound tot primes ->
    PrimeBounds bound tot primes.
Proof.
  intros bound tot primes [Htot_nonneg [Hprime_at _]].
  unfold PrimeBounds.
  intros pos Hpos.
  specialize (Hprime_at pos Hpos) as [[Hprime_gt _] Hupper].
  lia.
Qed.
Lemma PrimePrefixList_extend_nonprime_current__core_invariants :
  forall (current tot : Z) (primes : list Z),
    PrimePrefixList (current - 1) tot primes ->
    ~ StrictPrime current ->
    PrimePrefixList current tot primes.
Proof.
  intros current tot primes Hprefix Hnot_prime.
  unfold PrimePrefixList in *.
  destruct Hprefix as [Htot_nonneg [Hprime_at [Hcomplete Hsorted]]].
  split; [exact Htot_nonneg |].
  split.
  - intros idx Hidx.
    specialize (Hprime_at idx Hidx) as [Hprime Hupper].
    split; [exact Hprime | lia].
  - split.
    + intros p Hp_range.
    destruct (Z.eq_dec p current) as [-> | Hp_neq].
      * split.
        -- intros Hprime.
           contradiction.
        -- intros [idx [Hidx_ge [Hidx_le Hidx_value]]].
           specialize (Hprime_at idx ltac:(lia)) as [_ Hidx_upper].
           rewrite Hidx_value in Hidx_upper.
           lia.
      * apply Hcomplete.
        lia.
    + exact Hsorted.
Qed.
Lemma EulerOuterState_nonself_current_not_prime__core_invariants :
  forall (n i tot : Z) (flags primes : list Z),
    Znth (i - 2) flags 0 <> i ->
    i <= n ->
    2 <= i ->
    EulerOuterState n i tot flags primes ->
    ~ StrictPrime i.
Proof.
  intros n i tot flags primes Hnonself Hi_le Hi_ge Houter.
  unfold EulerOuterState in Houter.
  destruct Houter as [Hflag_state _].
  unfold EulerFlagState in Hflag_state.
  destruct Hflag_state as [_ Hflag].
  destruct (Hflag i ltac:(lia)) as [Hclassified _].
  specialize (Hclassified ltac:(lia)).
  unfold FlagValue in Hclassified.
  destruct Hclassified as [[Hprime Hself] | [Hnot_prime _]].
  - contradiction.
  - exact Hnot_prime.
Qed.
Lemma least_prime_factor_exists__core_invariants :
  forall k : Z,
    1 < k ->
    exists q : Z, LeastPrimeFactor q k.
Proof.
  intros k Hk_initial_gt.
  assert (Hk_initial_nonneg : 0 <= k) by lia.
  revert Hk_initial_gt.
  pattern k.
  apply Z_lt_induction.
  - intros k0 IH Hk_gt.
    destruct (prime_dec k0) as [Hk_prime | Hk_not_prime].
    + exists k0.
    unfold LeastPrimeFactor.
    split.
      * apply prime_to_StrictPrime__core_invariants.
      exact Hk_prime.
      * split.
        -- exists 1; nia.
        -- intros q Hq_prime Hq_div.
        pose proof (prime_to_StrictPrime__core_invariants k0 Hk_prime)
          as [Hk_pos Hk_div].
        destruct Hq_prime as [Hq_pos _].
        destruct (Hk_div q ltac:(lia) Hq_div) as [Hq_one | Hq_self];
          lia.
    + destruct (not_prime_divide k0 Hk_gt Hk_not_prime) as
      [d [[Hd_gt Hd_lt] Hd_div]].
      destruct Hd_div as [e Hk_eq].
      assert (He_gt : 1 < e) by nia.
      assert (He_lt : e < k0) by nia.
      destruct (IH d ltac:(lia) Hd_gt) as [qd Hqd].
      destruct (IH e ltac:(lia) He_gt) as [qe Hqe].
      destruct Hqd as [Hqd_prime [Hqd_div_d Hqd_min]].
      destruct Hqe as [Hqe_prime [Hqe_div_e Hqe_min]].
      destruct (Z_le_dec qd qe) as [Hqd_le_qe | Hqe_lt_qd].
      * exists qd.
      split.
        -- exact Hqd_prime.
        -- split.
           ++ destruct Hqd_div_d as [a Ha].
           exists (e * a).
           nia.
           ++ intros r Hr_prime Hr_div_k.
           assert (Hr_prime_std : prime r).
           {
             apply StrictPrime_to_prime__core_invariants.
             exact Hr_prime.
           }
           assert (Hr_div_de : Z.divide r (d * e)).
           {
             destruct Hr_div_k as [b Hb].
             exists b.
             nia.
           }
           destruct (prime_mult r Hr_prime_std d e Hr_div_de) as [Hr_div_d | Hr_div_e].
           ** apply Hqd_min; assumption.
           ** specialize (Hqe_min r Hr_prime Hr_div_e).
              lia.
      * exists qe.
      split.
        -- exact Hqe_prime.
        -- split.
           ++ destruct Hqe_div_e as [a Ha].
           exists (d * a).
           nia.
           ++ intros r Hr_prime Hr_div_k.
           assert (Hr_prime_std : prime r).
           {
             apply StrictPrime_to_prime__core_invariants.
             exact Hr_prime.
           }
           assert (Hr_div_de : Z.divide r (d * e)).
           {
             destruct Hr_div_k as [b Hb].
             exists b.
             nia.
           }
           destruct (prime_mult r Hr_prime_std d e Hr_div_de) as [Hr_div_d | Hr_div_e].
           ** specialize (Hqd_min r Hr_prime Hr_div_d).
              lia.
           ** apply Hqe_min; assumption.
  - exact Hk_initial_nonneg.
Qed.
Lemma LeastPrimeFactor_lt_of_not_prime__core_invariants :
  forall q k : Z,
    1 < k ->
    LeastPrimeFactor q k ->
    ~ StrictPrime k ->
    q < k.
Proof.
  intros q k Hk_gt [Hq_prime [Hq_div _]] Hnot_prime.
  destruct (Z.eq_dec q k) as [-> | Hneq].
  - contradiction.
  - assert (q <= k).
    {
      apply Z.divide_pos_le; [lia | exact Hq_div].
    }
    lia.
Qed.
Lemma LeastPrimeFactor_le_complement__core_invariants :
  forall q k b : Z,
    1 < k ->
    LeastPrimeFactor q k ->
    ~ StrictPrime k ->
    k = b * q ->
    q <= b.
Proof.
  intros q k b Hk_gt Hleast Hnot_prime Hk_eq.
  destruct Hleast as [Hq_prime [Hq_div Hq_min]].
  assert (Hq_lt_k : q < k).
  {
    apply (LeastPrimeFactor_lt_of_not_prime__core_invariants q k Hk_gt).
    - split; [exact Hq_prime |].
      split; [exact Hq_div | exact Hq_min].
    - exact Hnot_prime.
  }
  destruct Hq_prime as [Hq_gt_one Hq_divs].
  assert (Hb_gt : 1 < b) by nia.
  destruct (least_prime_factor_exists__core_invariants b Hb_gt) as
    [r [Hr_prime [Hr_div_b _]]].
  assert (Hr_div_k : Z.divide r k).
  {
    destruct Hr_div_b as [a Ha].
    exists (q * a).
    nia.
  }
  specialize (Hq_min r Hr_prime Hr_div_k).
  assert (Hr_le_b : r <= b).
  {
    destruct Hr_div_b as [a Ha].
    apply Z.divide_pos_le; [lia |].
    exists a.
    exact Ha.
  }
  lia.
Qed.
Lemma PrimePrefixList_lookup__core_invariants :
  forall (bound tot p : Z) (primes : list Z),
    PrimePrefixList bound tot primes ->
    2 <= p ->
    p <= bound ->
    StrictPrime p ->
    exists pos : Z,
      1 <= pos /\ pos <= tot /\
      Znth (pos - 1) primes 0 = p.
Proof.
  intros bound tot p primes [_ [_ [Hcomplete _]]] Hp_ge Hp_le Hp_prime.
  apply (proj1 (Hcomplete p ltac:(lia)) Hp_prime).
Qed.
Lemma FutureSelfCompleteness_successor_prime__core_invariants :
  forall (frontier tot : Z) (primes : list Z),
    2 <= frontier ->
    PrimePrefixList frontier tot primes ->
    FutureSelfCompleteness frontier (frontier + 1) tot primes ->
    StrictPrime (frontier + 1).
Proof.
  intros frontier tot primes Hfrontier_ge Hprefix Hfuture.
  destruct (prime_dec (frontier + 1)) as [Hprime | Hnot_prime].
  - apply prime_to_StrictPrime__core_invariants.
    exact Hprime.
  - exfalso.
    assert (Hnot_strict : ~ StrictPrime (frontier + 1)).
    {
      intros Hstrict.
      apply Hnot_prime.
      apply StrictPrime_to_prime__core_invariants.
      exact Hstrict.
    }
    destruct (least_prime_factor_exists__core_invariants (frontier + 1) ltac:(lia))
      as [q Hleast].
    assert (Hq_lt : q < frontier + 1).
    {
      apply (LeastPrimeFactor_lt_of_not_prime__core_invariants q (frontier + 1));
        [lia | exact Hleast | exact Hnot_strict].
    }
    destruct Hleast as [Hq_prime [Hq_div Hq_min]].
    assert (Hq_le_frontier : q <= frontier) by lia.
    destruct
      (PrimePrefixList_lookup__core_invariants frontier tot q primes Hprefix
         ltac:(destruct Hq_prime; lia) Hq_le_frontier Hq_prime)
      as [pos [Hpos_ge [Hpos_le Hpos_value]]].
    destruct Hq_div as [base Hbase_eq].
    assert (Hq_le_base : q <= base).
    {
      apply (LeastPrimeFactor_le_complement__core_invariants q (frontier + 1) base);
        [lia | | exact Hnot_strict | exact Hbase_eq].
      split; [exact Hq_prime |].
      split; [exists base; exact Hbase_eq | exact Hq_min].
    }
    assert (Hbase_ge : 2 <= base) by (destruct Hq_prime; nia).
    assert (Hbase_lt : base < frontier) by (destruct Hq_prime; nia).
    unfold FutureSelfCompleteness, EarlierLinearProduct in Hfuture.
    apply Hfuture.
    exists base, pos.
    split; [lia |].
    split; [lia |].
    split; [lia |].
    split; [lia |].
    split.
    + rewrite Hpos_value.
      exact Hq_le_base.
    + split.
      * unfold PriorNonDivisibility.
      intros prev [Hprev_ge Hprev_lt] Hprev_div_base.
      unfold PrimePrefixList in Hprefix.
      destruct Hprefix as [_ [Hprime_at [_ Hsorted]]].
      specialize (Hprime_at prev ltac:(lia)) as [Hprev_prime Hprev_upper].
      specialize (Hsorted prev pos ltac:(lia)).
      rewrite Hpos_value in Hsorted.
      assert (Hprev_div_k : Z.divide (Znth (prev - 1) primes 0) (frontier + 1)).
      {
        destruct Hprev_div_base as [c Hc].
        exists (q * c).
        nia.
      }
      specialize (Hq_min (Znth (prev - 1) primes 0) Hprev_prime Hprev_div_k).
      lia.
      * rewrite Hpos_value.
        exact Hbase_eq.
Qed.
Lemma PrimePrefixList_first_le__core_invariants :
  forall (bound tot pos : Z) (primes : list Z),
    PrimePrefixList bound tot primes ->
    1 <= pos ->
    pos <= tot ->
    Znth 0 primes 0 <= Znth (pos - 1) primes 0.
Proof.
  intros bound tot pos primes Hprefix Hpos_ge Hpos_le.
  unfold PrimePrefixList in Hprefix.
  destruct Hprefix as [_ [_ [_ Hsorted]]].
  destruct (Z.eq_dec pos 1) as [-> | Hneq].
  - replace (1 - 1) with 0 by lia.
    lia.
  - specialize (Hsorted 1 pos ltac:(lia)).
    replace (1 - 1) with 0 in Hsorted by lia.
    lia.
Qed.
Lemma FutureSelfCompleteness_advance_after_product_exit__core_invariants :
  forall (n frontier k tot : Z) (primes : list Z),
    2 <= frontier ->
    k <= n ->
    frontier + 1 < k ->
    PrimePrefixList frontier tot primes ->
    ProductIndex frontier 1 primes > n ->
    FutureSelfCompleteness frontier k tot primes ->
    FutureSelfCompleteness (frontier + 1) k tot primes.
Proof.
  intros n frontier k tot primes Hfrontier_ge Hk_le_n Hk_gt_next
    Hprefix Hproduct_exit Hold.
  unfold FutureSelfCompleteness, EarlierLinearProduct in *.
  intros [base [pos [Hbase_ge [Hbase_lt [Hpos_ge [Hpos_le
    [Hprime_le_base [Hprior Hproduct]]]]]]]].
  destruct (Z.eq_dec base frontier) as [Hbase_eq | Hbase_neq].
  - subst base.
    assert (Hfirst_le :
      Znth 0 primes 0 <= Znth (pos - 1) primes 0).
    {
      eapply PrimePrefixList_first_le__core_invariants; eauto.
    }
    unfold ProductIndex in Hproduct_exit.
    replace (1 - 1) with 0 in Hproduct_exit by lia.
    assert (0 <= frontier) by lia.
    assert (frontier * Znth 0 primes 0
            <= frontier * Znth (pos - 1) primes 0) by nia.
    assert (frontier * Znth (pos - 1) primes 0 > n) by lia.
    lia.
  - apply Hold.
    exists base, pos.
    repeat split; try lia; assumption.
Qed.
Lemma EulerFlagState_advance_after_product_exit__core_invariants :
  forall (n frontier tot : Z) (flags primes : list Z),
    2 <= frontier ->
    frontier <= n ->
    PrimePrefixList frontier tot primes ->
    ProductIndex frontier 1 primes > n ->
    EulerFlagState n frontier tot flags primes ->
    EulerFlagState n (frontier + 1) tot flags primes.
Proof.
  intros n frontier tot flags primes Hfrontier_ge Hfrontier_le
    Hprefix Hproduct_exit Hflag.
  unfold EulerFlagState in *.
  destruct Hflag as [Hflags_len Hflag].
  split; [exact Hflags_len |].
  intros k Hk_range.
  specialize (Hflag k Hk_range) as [Hclassified Hfuture].
  split.
  - intros Hk_le_next.
    destruct (Z_le_dec k frontier) as [Hk_le_frontier | Hk_gt_frontier].
    + apply Hclassified.
      exact Hk_le_frontier.
    + assert (Hk_eq : k = frontier + 1) by lia.
      subst k.
      specialize (Hfuture ltac:(lia)).
      unfold FutureFlagState in Hfuture.
      destruct Hfuture as [Hnonself_sound Hself_complete].
      destruct (Z.eq_dec (FlagValue flags (frontier + 1)) (frontier + 1))
        as [Hself | Hnonself].
      * left.
        split.
        -- eapply FutureSelfCompleteness_successor_prime__core_invariants;
             eauto.
        -- exact Hself.
      * apply Hnonself_sound.
        exact Hnonself.
  - intros Hk_gt_next.
    specialize (Hfuture ltac:(lia)).
    unfold FutureFlagState in *.
    destruct Hfuture as [Hnonself_sound Hself_complete].
    split.
    + intros Hnonself.
      apply Hnonself_sound.
      exact Hnonself.
    + intros Hself.
      eapply FutureSelfCompleteness_advance_after_product_exit__core_invariants;
        eauto; lia.
Qed.
Lemma EulerOuterState_advance_after_product_exit__core_invariants :
  forall (n current tot : Z) (flags primes : list Z),
    2 <= current ->
    current <= n ->
    EulerOuterState n current tot flags primes ->
    PrimePrefixList current tot primes ->
    ProductIndex current 1 primes > n ->
    EulerOuterState n (current + 1) tot flags primes.
Proof.
  intros n current tot flags primes Hcurrent_ge Hcurrent_le Houter
    Hprefix_current Hproduct_exit.
  unfold EulerOuterState in *.
  destruct Houter as
    [Hflag_state
     [Hprimes_len [Hnext_ge [Hnext_le [Htot_ge [Htot_lt [Hprefix_old Hbounds]]]]]]].
  split.
  - eapply EulerFlagState_advance_after_product_exit__core_invariants;
      eauto.
  - split; [exact Hprimes_len |].
    split; [lia |].
    split; [lia |].
    split; [lia |].
    split; [lia |].
    split.
    + replace (current + 1 - 1) with current by lia.
      exact Hprefix_current.
    + exact Hbounds.
Qed.
Lemma EulerOuterState_nonself_inner_start__core_invariants :
  forall (n current tot : Z) (flags primes : list Z),
    Znth (current - 2) flags 0 <> current ->
    current <= n ->
    2 <= current ->
    EulerOuterState n current tot flags primes ->
    EulerInnerState n current 1 tot flags primes.
Proof.
  intros n current tot flags primes Hnonself Hcurrent_le Hcurrent_ge Houter.
  pose proof Houter as Houter_current.
  pose proof
    (EulerOuterState_nonself_first_prime_facts__core_invariants
       n current tot flags primes Hnonself Hcurrent_le Hcurrent_ge Houter)
    as [Htot_pos _].
  pose proof
    (EulerOuterState_nonself_current_not_prime__core_invariants
       n current tot flags primes Hnonself Hcurrent_le Hcurrent_ge Houter)
    as Hnot_prime_current.
  unfold EulerOuterState in Houter.
  destruct Houter as
    [Hflag_state
     [Hprimes_len [Hnext_ge [Hnext_le [Htot_ge [Htot_lt [Hprefix_old Hbounds_old]]]]]]].
  pose proof
    (PrimePrefixList_extend_nonprime_current__core_invariants
       current tot primes Hprefix_old Hnot_prime_current)
    as Hprefix_current.
  unfold EulerInnerState.
  split; [exact Hflag_state |].
  split; [exact Hprimes_len |].
  split; [lia |].
  split; [lia |].
  split; [lia |].
  split; [lia |].
  split; [lia |].
  split; [lia |].
  split; [lia |].
  split; [exact Hprefix_current |].
  split.
  - apply PrimeBounds_from_prefix__core_invariants.
    exact Hprefix_current.
  - split.
    + unfold CurrentBaseProgress.
      intros pos Hpos.
      lia.
    + split.
      * unfold PriorNonDivisibility.
        intros pos Hpos.
        lia.
      * intros Hproduct_exit.
        eapply (EulerOuterState_advance_after_product_exit__core_invariants
                  n current tot flags primes);
          [exact Hcurrent_ge | exact Hcurrent_le | exact Houter_current |
           exact Hprefix_current | exact Hproduct_exit].
Qed.
Lemma EulerOuterState_self_current_prime__core_invariants :
  forall (n current tot : Z) (flags primes : list Z),
    Znth (current - 2) flags 0 = current ->
    current <= n ->
    2 <= current ->
    EulerOuterState n current tot flags primes ->
    StrictPrime current.
Proof.
  intros n current tot flags primes Hself Hcurrent_le Hcurrent_ge Houter.
  unfold EulerOuterState in Houter.
  destruct Houter as [Hflag_state _].
  unfold EulerFlagState in Hflag_state.
  destruct Hflag_state as [_ Hflag].
  destruct (Hflag current ltac:(lia)) as [Hclassified _].
  specialize (Hclassified ltac:(lia)).
  unfold FlagValue in Hclassified.
  rewrite Hself in Hclassified.
  destruct Hclassified as [[Hprime _] | [Hnot_prime [Hprime _]]].
  - exact Hprime.
  - contradiction.
Qed.
Lemma PrimePrefixList_append_current__core_invariants :
  forall (n current tot : Z) (primes : list Z),
    Zlength primes = n ->
    tot < n ->
    PrimePrefixList (current - 1) tot primes ->
    StrictPrime current ->
    2 <= current ->
    PrimePrefixList current (tot + 1)
      (replace_Znth ((tot + 1) - 1) current primes).
Proof.
  intros n current tot primes Hlen Htot_lt_n Hprefix Hcurrent_prime
    Hcurrent_ge.
  unfold PrimePrefixList in *.
  destruct Hprefix as [Htot_nonneg [Hprime_at [Hcomplete Hsorted]]].
  split; [lia |].
  split.
  - intros pos Hpos.
    destruct (Z.eq_dec pos (tot + 1)) as [Hpos_last | Hpos_old].
    + subst pos.
      rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
      split; [exact Hcurrent_prime | lia].
    + assert (Hpos_le_tot : pos <= tot) by lia.
      rewrite Znth_replace_Znth_Diff by (rewrite ?Hlen; lia).
      specialize (Hprime_at pos ltac:(lia)) as [Hprime Hupper].
      split; [exact Hprime | lia].
  - split.
    + intros p Hp_range.
      split.
      * intros Hp_prime.
        destruct (Z.eq_dec p current) as [-> | Hp_not_current].
        -- exists (tot + 1).
           split; [lia |].
           split; [lia |].
           rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
           reflexivity.
        -- destruct (proj1 (Hcomplete p ltac:(lia)) Hp_prime) as
             [pos [Hpos_ge [Hpos_le Hpos_value]]].
           exists pos.
           split; [exact Hpos_ge |].
           split; [lia |].
           rewrite Znth_replace_Znth_Diff by (rewrite ?Hlen; lia).
           exact Hpos_value.
      * intros [pos [Hpos_ge [Hpos_le Hpos_value]]].
        destruct (Z.eq_dec pos (tot + 1)) as [Hpos_last | Hpos_old].
        -- subst pos.
           rewrite Znth_replace_Znth_Same in Hpos_value
             by (rewrite Hlen; lia).
           rewrite <- Hpos_value.
           exact Hcurrent_prime.
        -- assert (Hpos_le_tot : pos <= tot) by lia.
           rewrite Znth_replace_Znth_Diff in Hpos_value
             by (rewrite ?Hlen; lia).
           specialize (Hprime_at pos ltac:(lia)) as [Hprime _].
           rewrite <- Hpos_value.
           exact Hprime.
    + intros p q Hpq.
      destruct (Z.eq_dec q (tot + 1)) as [Hq_last | Hq_old].
      * subst q.
        assert (Hp_le_tot : p <= tot) by lia.
        rewrite Znth_replace_Znth_Diff by (rewrite ?Hlen; lia).
        rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
        specialize (Hprime_at p ltac:(lia)) as [_ Hp_upper].
        lia.
      * assert (Hp_le_tot : p <= tot) by lia.
        assert (Hq_le_tot : q <= tot) by lia.
        rewrite Znth_replace_Znth_Diff by (rewrite ?Hlen; lia).
        rewrite Znth_replace_Znth_Diff by (rewrite ?Hlen; lia).
        apply Hsorted.
        lia.
Qed.
Lemma EulerFlagState_prime_append_current__core_invariants :
  forall (n current tot : Z) (flags primes : list Z),
    2 <= current ->
    current <= n ->
    Zlength primes = n ->
    tot < n ->
    EulerFlagState n current tot flags primes ->
    EulerFlagState n current (tot + 1) flags
      (replace_Znth ((tot + 1) - 1) current primes).
Proof.
  intros n current tot flags primes Hcurrent_ge Hcurrent_le Hlen Htot_lt_n
    Hflag.
  unfold EulerFlagState in *.
  destruct Hflag as [Hflags_len Hflag].
  split; [exact Hflags_len |].
  intros k Hk_range.
  specialize (Hflag k Hk_range) as [Hclassified Hfuture].
  split.
  - intros Hk_le.
    apply Hclassified.
    exact Hk_le.
  - intros Hk_gt.
    specialize (Hfuture Hk_gt).
    unfold FutureFlagState in *.
    destruct Hfuture as [Hnonself_sound Hself_complete].
    split.
    + intros Hnonself.
      apply Hnonself_sound.
      exact Hnonself.
    + intros Hself.
      specialize (Hself_complete Hself).
      unfold FutureSelfCompleteness, EarlierLinearProduct in *.
      intros [base [pos [Hbase_ge [Hbase_lt [Hpos_ge [Hpos_le
        [Hprime_le_base [Hprior Hproduct]]]]]]]].
      destruct (Z.eq_dec pos (tot + 1)) as [Hpos_last | Hpos_old].
      * subst pos.
        rewrite Znth_replace_Znth_Same in Hprime_le_base
          by (rewrite Hlen; lia).
        lia.
      * assert (Hpos_le_tot : pos <= tot) by lia.
        apply Hself_complete.
        exists base.
        exists pos.
        split; [exact Hbase_ge |].
        split; [exact Hbase_lt |].
        split; [exact Hpos_ge |].
        split; [exact Hpos_le_tot |].
        split.
        -- rewrite Znth_replace_Znth_Diff in Hprime_le_base
             by (rewrite ?Hlen; lia).
           exact Hprime_le_base.
        -- split.
           ++ unfold PriorNonDivisibility in *.
              intros prev Hprev Hdiv.
              apply (Hprior prev Hprev).
              rewrite Znth_replace_Znth_Diff by (rewrite ?Hlen; lia).
              exact Hdiv.
           ++ rewrite Znth_replace_Znth_Diff in Hproduct
                by (rewrite ?Hlen; lia).
              exact Hproduct.
Qed.
Lemma EulerOuterState_self_inner_start__core_invariants :
  forall (n current tot : Z) (flags primes : list Z),
    Znth (current - 2) flags 0 = current ->
    current <= n ->
    2 <= current ->
    EulerOuterState n current tot flags primes ->
    EulerInnerState n current 1 (tot + 1) flags
      (replace_Znth ((tot + 1) - 1) current primes).
Proof.
  intros n current tot flags primes Hself Hcurrent_le Hcurrent_ge Houter.
  pose proof Houter as Houter_current.
  pose proof
    (EulerOuterState_self_current_prime__core_invariants
       n current tot flags primes Hself Hcurrent_le Hcurrent_ge Houter)
    as Hcurrent_prime.
  unfold EulerOuterState in Houter.
  destruct Houter as
    [Hflag_state
     [Hprimes_len [Hnext_ge [Hnext_le [Htot_ge [Htot_lt [Hprefix_old Hbounds_old]]]]]]].
  assert (Htot_lt_n : tot < n) by lia.
  pose proof
    (PrimePrefixList_append_current__core_invariants
       n current tot primes Hprimes_len Htot_lt_n Hprefix_old
       Hcurrent_prime Hcurrent_ge)
    as Hprefix_current.
  pose proof
    (EulerFlagState_prime_append_current__core_invariants
       n current tot flags primes Hcurrent_ge Hcurrent_le Hprimes_len
       Htot_lt_n Hflag_state)
    as Hflag_current.
  assert (Hnew_primes_len :
    Zlength (replace_Znth (tot + 1 - 1) current primes) = n).
  {
    rewrite Zlength_replace_Znth.
    exact Hprimes_len.
  }
  assert (Hbounds_current :
    PrimeBounds current (tot + 1)
      (replace_Znth (tot + 1 - 1) current primes)).
  {
    apply PrimeBounds_from_prefix__core_invariants.
    exact Hprefix_current.
  }
  unfold EulerInnerState.
  split; [exact Hflag_current |].
  split; [exact Hnew_primes_len |].
  split; [lia |].
  split; [lia |].
  split; [lia |].
  split; [lia |].
  split; [lia |].
  split; [lia |].
  split; [lia |].
  split; [exact Hprefix_current |].
  split; [exact Hbounds_current |].
  split.
  - unfold CurrentBaseProgress.
    intros pos Hpos.
    lia.
  - split.
    + unfold PriorNonDivisibility.
      intros pos Hpos.
      lia.
    + intros Hproduct_exit.
      unfold EulerOuterState.
      split.
      * eapply EulerFlagState_advance_after_product_exit__core_invariants;
          [exact Hcurrent_ge | exact Hcurrent_le | exact Hprefix_current |
           exact Hproduct_exit | exact Hflag_current].
      * split; [exact Hnew_primes_len |].
        split; [lia |].
        split; [lia |].
        split; [lia |].
        split; [lia |].
        split.
        -- replace (current + 1 - 1) with current by lia.
           exact Hprefix_current.
        -- unfold PrimeBounds in *.
           intros pos Hpos.
           specialize (Hbounds_current pos Hpos) as [Hlower Hupper].
           lia.
Qed.
Lemma EulerOuterState_self_first_prime_facts__core_invariants :
  forall (n current tot : Z) (flags primes : list Z),
    Znth (current - 2) flags 0 = current ->
    current <= n ->
    2 <= current ->
    EulerOuterState n current tot flags primes ->
    2 <= Znth 0 (replace_Znth ((tot + 1) - 1) current primes) 0 /\
    Znth 0 (replace_Znth ((tot + 1) - 1) current primes) 0 <= current.
Proof.
  intros n current tot flags primes Hself Hcurrent_le Hcurrent_ge Houter.
  pose proof
    (EulerOuterState_self_inner_start__core_invariants
       n current tot flags primes Hself Hcurrent_le Hcurrent_ge Houter)
    as Hinner.
  unfold EulerInnerState in Hinner.
  destruct Hinner as
    [_ [_ [_ [_ [_ [Hone_le_tot [_ [_ [_ [Hprefix_current [Hbounds_current _]]]]]]]]]]].
  specialize (Hbounds_current 1 ltac:(lia)).
  replace (1 - 1) with 0 in Hbounds_current by lia.
  exact Hbounds_current.
Qed.
Lemma StrictPrime_product_not_prime__core_invariants :
  forall a p : Z,
    2 <= a ->
    StrictPrime p ->
    ~ StrictPrime (a * p).
Proof.
  intros a p Ha_ge Hp Hprod_prime.
  destruct Hp as [Hp_gt Hp_divs].
  destruct Hprod_prime as [_ Hprod_divs].
  assert (Hdiv : Z.divide p (a * p)).
  {
    exists a.
    nia.
  }
  destruct (Hprod_divs p ltac:(lia) Hdiv) as [Hp_one | Hp_product];
    nia.
Qed.
Lemma LeastPrimeFactor_current_product__core_invariants :
  forall (current j tot : Z) (primes : list Z),
    2 <= current ->
    1 <= j ->
    j <= tot ->
    PrimePrefixList current tot primes ->
    PriorNonDivisibility current j primes ->
    LeastPrimeFactor (Znth (j - 1) primes 0)
      (current * Znth (j - 1) primes 0).
Proof.
  intros current j tot primes Hcurrent_ge Hj_ge Hj_le Hprefix Hprior.
  unfold PrimePrefixList in Hprefix.
  destruct Hprefix as [Htot_nonneg [Hprime_at_all [Hcomplete Hsorted]]].
  pose proof (Hprime_at_all j ltac:(lia)) as [Hp_prime Hp_upper].
  split; [exact Hp_prime |].
  split.
  - exists current.
    nia.
  - intros q Hq_prime Hq_div_product.
    assert (Hq_prime_std : prime q).
    {
      apply StrictPrime_to_prime__core_invariants.
      exact Hq_prime.
    }
    destruct
      (prime_mult q Hq_prime_std current (Znth (j - 1) primes 0)
         Hq_div_product)
      as [Hq_div_current | Hq_div_selected].
    + assert (Hq_gt : 1 < q) by (destruct Hq_prime; lia).
      assert (Hq_le_current : q <= current).
      {
        apply Z.divide_pos_le; [lia | exact Hq_div_current].
      }
      destruct
        (PrimePrefixList_lookup__core_invariants current tot q
           primes
           (conj Htot_nonneg (conj Hprime_at_all (conj Hcomplete Hsorted)))
           ltac:(lia) Hq_le_current Hq_prime)
        as [pos [Hpos_ge [Hpos_le Hpos_value]]].
      destruct (Z_lt_ge_dec pos j) as [Hpos_lt_j | Hpos_ge_j].
      * specialize (Hprior pos ltac:(lia)).
        rewrite Hpos_value in Hprior.
        contradiction.
      * destruct (Z.eq_dec pos j) as [Hpos_eq | Hpos_neq].
        -- subst pos.
           replace (j - 1) with (j - 1) in Hpos_value by lia.
           rewrite Hpos_value.
           lia.
        -- assert (Hj_lt_pos : j < pos) by lia.
           specialize (Hsorted j pos ltac:(lia)).
           rewrite Hpos_value in Hsorted.
           lia.
    + destruct Hp_prime as [Hp_gt Hp_divs].
      destruct (Hp_divs q ltac:(destruct Hq_prime; lia) Hq_div_selected)
        as [Hq_one | Hq_eq].
      * destruct Hq_prime as [Hq_gt _].
        lia.
      * lia.
Qed.
Lemma FlagEntryFor_current_product__core_invariants :
  forall (current j tot : Z) (primes : list Z),
    2 <= current ->
    1 <= j ->
    j <= tot ->
    PrimePrefixList current tot primes ->
    PriorNonDivisibility current j primes ->
    FlagEntryFor (current * Znth (j - 1) primes 0)
      (Znth (j - 1) primes 0).
Proof.
  intros current j tot primes Hcurrent_ge Hj_ge Hj_le Hprefix Hprior.
  right.
  split.
  - apply StrictPrime_product_not_prime__core_invariants.
    + exact Hcurrent_ge.
    + unfold PrimePrefixList in Hprefix.
      destruct Hprefix as [_ [Hprime_at _]].
      specialize (Hprime_at j ltac:(lia)).
      tauto.
  - eapply LeastPrimeFactor_current_product__core_invariants; eauto.
Qed.
Lemma EulerFlagState_advance_after_inner_product_exit__core_invariants :
  forall (n current j tot : Z) (flags primes : list Z),
    2 <= current ->
    current <= n ->
    1 <= j ->
    j <= tot ->
    PrimePrefixList current tot primes ->
    EulerFlagState n current tot flags primes ->
    CurrentBaseProgress n current j flags primes ->
    ProductIndex current j primes > n ->
    EulerFlagState n (current + 1) tot flags primes.
Proof.
  intros n current j tot flags primes Hcurrent_ge Hcurrent_le Hj_ge Hj_le
    Hprefix Hflag Hprogress Hproduct_exit.
  unfold EulerFlagState in *.
  destruct Hflag as [Hflags_len Hflag].
  split; [exact Hflags_len |].
  intros k Hk_range.
  specialize (Hflag k Hk_range) as [Hclassified Hfuture].
  split.
  - intros Hk_le_next.
    destruct (Z_le_dec k current) as [Hk_le_current | Hk_gt_current].
    + apply Hclassified.
      exact Hk_le_current.
    + assert (Hk_eq : k = current + 1) by lia.
      subst k.
      specialize (Hfuture ltac:(lia)).
      unfold FutureFlagState in Hfuture.
      destruct Hfuture as [Hnonself_sound Hself_complete].
      destruct (Z.eq_dec (FlagValue flags (current + 1)) (current + 1))
        as [Hself | Hnonself].
      * left.
        split.
        -- eapply FutureSelfCompleteness_successor_prime__core_invariants;
             eauto.
        -- exact Hself.
      * apply Hnonself_sound.
        exact Hnonself.
  - intros Hk_gt_next.
    specialize (Hfuture ltac:(lia)).
    unfold FutureFlagState in *.
    destruct Hfuture as [Hnonself_sound Hself_complete].
    split.
    + intros Hnonself.
      apply Hnonself_sound.
      exact Hnonself.
    + intros Hself.
      specialize (Hself_complete Hself).
      unfold FutureSelfCompleteness, EarlierLinearProduct in *.
      intros [base [pos [Hbase_ge [Hbase_lt [Hpos_ge [Hpos_le
        [Hprime_le_base [Hprior Hproduct]]]]]]]].
      destruct (Z.eq_dec base current) as [Hbase_eq | Hbase_neq].
      * subst base.
        destruct (Z_lt_ge_dec pos j) as [Hpos_lt_j | Hpos_ge_j].
        -- specialize (Hprogress pos ltac:(lia)).
           unfold CurrentProductMarked in Hprogress.
           assert (Hprod_range :
             2 <= ProductIndex current pos primes /\
             ProductIndex current pos primes <= n).
           {
             unfold ProductIndex.
             rewrite <- Hproduct.
             exact Hk_range.
           }
           destruct (Hprogress Hprod_range) as [_ [Hnonself _]].
           unfold FlagValue in Hnonself.
           unfold ProductIndex in Hnonself.
           rewrite <- Hproduct in Hnonself.
           contradiction.
        -- assert (Hpos_eq_or_gt : pos = j \/ j < pos) by lia.
           unfold ProductIndex in Hproduct_exit.
           destruct Hpos_eq_or_gt as [-> | Hj_lt_pos].
           ++ rewrite <- Hproduct in Hproduct_exit.
              lia.
           ++ unfold PrimePrefixList in Hprefix.
              destruct Hprefix as [_ [_ [_ Hsorted]]].
              specialize (Hsorted j pos ltac:(lia)).
              assert (0 <= current) by lia.
              assert (current * Znth (j - 1) primes 0
                      < current * Znth (pos - 1) primes 0) by nia.
              assert (current * Znth (pos - 1) primes 0 > n) by lia.
              lia.
      * apply Hself_complete.
        exists base.
        exists pos.
        repeat split; try lia; assumption.
Qed.
Lemma EulerFlagState_advance_after_inner_divide__core_invariants :
  forall (n current j tot : Z) (flags primes : list Z),
    2 <= current ->
    current <= n ->
    1 <= j ->
    j <= tot ->
    PrimePrefixList current tot primes ->
    EulerFlagState n current tot flags primes ->
    CurrentBaseProgress n current (j + 1) flags primes ->
    PriorNonDivisibility current j primes ->
    Z.divide (Znth (j - 1) primes 0) current ->
    EulerFlagState n (current + 1) tot flags primes.
Proof.
  intros n current j tot flags primes Hcurrent_ge Hcurrent_le Hj_ge Hj_le
    Hprefix Hflag Hprogress Hprior Hdivide.
  unfold EulerFlagState in *.
  destruct Hflag as [Hflags_len Hflag].
  split; [exact Hflags_len |].
  intros k Hk_range.
  specialize (Hflag k Hk_range) as [Hclassified Hfuture].
  split.
  - intros Hk_le_next.
    destruct (Z_le_dec k current) as [Hk_le_current | Hk_gt_current].
    + apply Hclassified.
      exact Hk_le_current.
    + assert (Hk_eq : k = current + 1) by lia.
      subst k.
      specialize (Hfuture ltac:(lia)).
      unfold FutureFlagState in Hfuture.
      destruct Hfuture as [Hnonself_sound Hself_complete].
      destruct (Z.eq_dec (FlagValue flags (current + 1)) (current + 1))
        as [Hself | Hnonself].
      * left.
        split.
        -- eapply FutureSelfCompleteness_successor_prime__core_invariants;
             eauto.
        -- exact Hself.
      * apply Hnonself_sound.
        exact Hnonself.
  - intros Hk_gt_next.
    specialize (Hfuture ltac:(lia)).
    unfold FutureFlagState in *.
    destruct Hfuture as [Hnonself_sound Hself_complete].
    split.
    + intros Hnonself.
      apply Hnonself_sound.
      exact Hnonself.
    + intros Hself.
      specialize (Hself_complete Hself).
      unfold FutureSelfCompleteness, EarlierLinearProduct in *.
      intros [base [pos [Hbase_ge [Hbase_lt [Hpos_ge [Hpos_le
        [Hprime_le_base [Hprior_product Hproduct]]]]]]]].
      destruct (Z.eq_dec base current) as [Hbase_eq | Hbase_neq].
      * subst base.
        destruct (Z_lt_ge_dec pos (j + 1)) as [Hpos_before | Hpos_after].
        -- specialize (Hprogress pos ltac:(lia)).
           unfold CurrentProductMarked in Hprogress.
           assert (Hprod_range :
             2 <= ProductIndex current pos primes /\
             ProductIndex current pos primes <= n).
           {
             unfold ProductIndex.
             rewrite <- Hproduct.
             exact Hk_range.
           }
           destruct (Hprogress Hprod_range) as [_ [Hnonself _]].
           unfold FlagValue in Hnonself.
           unfold ProductIndex in Hnonself.
           rewrite <- Hproduct in Hnonself.
           contradiction.
        -- assert (j < pos) by lia.
           unfold PriorNonDivisibility in Hprior_product.
           specialize (Hprior_product j ltac:(lia)).
           contradiction.
      * apply Hself_complete.
        exists base.
        exists pos.
        repeat split; try lia; assumption.
Qed.
Lemma PriorNonDivisibility_nondivide_next_index__core_invariants :
  forall (current j tot : Z) (primes : list Z),
    2 <= current ->
    1 <= j ->
    j <= tot ->
    PrimePrefixList current tot primes ->
    PriorNonDivisibility current j primes ->
    ~ Z.divide (Znth (j - 1) primes 0) current ->
    j + 1 <= tot.
Proof.
  intros current j tot primes Hcurrent_ge Hj_ge Hj_le Hprefix Hprior
    Hnondivide.
  assert (Hexists_divisor :
    exists q : Z, StrictPrime q /\ Z.divide q current /\ q <= current).
  {
    destruct (prime_dec current) as [Hprime | Hnot_prime].
    - exists current.
      split.
      + apply prime_to_StrictPrime__core_invariants.
        exact Hprime.
      + split; [exists 1; nia | lia].
    - destruct
        (least_prime_factor_exists__core_invariants current ltac:(lia))
        as [q [Hq_prime [Hq_div _]]].
      exists q.
      split; [exact Hq_prime |].
      split; [exact Hq_div |].
      destruct Hq_prime as [Hq_gt _].
      apply Z.divide_pos_le; [lia | exact Hq_div].
  }
  destruct Hexists_divisor as [q [Hq_prime [Hq_div Hq_le_current]]].
  destruct
    (PrimePrefixList_lookup__core_invariants current tot q primes Hprefix
       ltac:(destruct Hq_prime; lia) Hq_le_current Hq_prime)
    as [pos [Hpos_ge [Hpos_le Hpos_value]]].
  destruct (Z_lt_ge_dec pos j) as [Hpos_lt | Hpos_ge_j].
  - specialize (Hprior pos ltac:(lia)).
    rewrite Hpos_value in Hprior.
    contradiction.
  - destruct (Z.eq_dec pos j) as [Hpos_eq | Hpos_neq].
    + subst pos.
      replace (j - 1) with (j - 1) in Hpos_value by lia.
      rewrite Hpos_value in Hnondivide.
      contradiction.
    + lia.
Qed.
Lemma EulerInnerState_mark_product__core_invariants :
  forall (n current j tot : Z) (flags primes : list Z),
    2 <= current ->
    current <= n ->
    1 <= j ->
    j <= tot ->
    ProductIndex current j primes <= n ->
    EulerInnerState n current j tot flags primes ->
    EulerInnerMarkedState n current j tot
      (replace_Znth (ProductIndex current j primes - 2)
         (Znth (j - 1) primes 0) flags)
      primes.
Proof.
  intros n current j tot flags primes Hcurrent_ge Hcurrent_le Hj_ge Hj_le
    Hproduct_le Hinner.
  unfold EulerInnerState in Hinner.
  destruct Hinner as
    [Hflag_state
     [Hprimes_len
      [Hcurrent_ge_inner
       [Hcurrent_le_inner
        [Hj_ge_inner
         [Hj_le_inner
          [Htot_pos
           [Htot_le_n
            [Htot_lt_current
             [Hprefix
              [Hbounds
               [Hprogress
                [Hprior Hproduct_exit_old]]]]]]]]]]]]].
  pose proof Hflag_state as Hflag_state_old.
  unfold EulerFlagState in Hflag_state_old.
  destruct Hflag_state_old as [Hflags_len Hflag_all].
  pose proof (Hbounds j ltac:(lia)) as [Hselected_lower Hselected_upper].
  set (selected := Znth (j - 1) primes 0).
  set (product := ProductIndex current j primes).
  set (marked_flags := replace_Znth (product - 2) selected flags).
  assert (Hproduct_eq : product = current * selected).
  {
    unfold product, ProductIndex, selected.
    reflexivity.
  }
  assert (Hproduct_range : 2 <= product /\ product <= n).
  {
    split; [unfold product, ProductIndex, selected; nia | exact Hproduct_le].
  }
  assert (Hproduct_gt_current : current < product).
  {
    unfold product, ProductIndex, selected.
    nia.
  }
  assert (Hselected_neq_product : selected <> product) by nia.
  assert (Hentry :
    FlagEntryFor product selected).
  {
    unfold product, selected.
    eapply FlagEntryFor_current_product__core_invariants; eauto.
  }
  assert (Hflag_marked : EulerFlagState n current tot marked_flags primes).
  {
    unfold EulerFlagState.
    split.
    - unfold marked_flags.
      rewrite Zlength_replace_Znth.
      exact Hflags_len.
    - intros k Hk_range.
      specialize (Hflag_all k Hk_range) as [Hclassified Hfuture].
      split.
      + intros Hk_le_current.
        destruct (Z.eq_dec k product) as [Hk_product | Hk_not_product].
        * subst k.
          lia.
        * unfold FlagValue, marked_flags.
          rewrite Znth_replace_Znth_Diff by lia.
          apply Hclassified.
          exact Hk_le_current.
      + intros Hk_gt_current.
        destruct (Z.eq_dec k product) as [Hk_product | Hk_not_product].
        * subst k.
          unfold FutureFlagState.
          split.
          -- intros _.
             unfold FlagValue, marked_flags.
             rewrite Znth_replace_Znth_Same by (rewrite Hflags_len; lia).
             exact Hentry.
          -- intros Hself.
             unfold FlagValue, marked_flags in Hself.
             rewrite Znth_replace_Znth_Same in Hself
               by (rewrite Hflags_len; lia).
             contradiction.
        * specialize (Hfuture Hk_gt_current).
          unfold FutureFlagState in *.
          destruct Hfuture as [Hnonself_sound Hself_complete].
          split.
          -- intros Hnonself.
             unfold FlagValue, marked_flags in *.
             rewrite Znth_replace_Znth_Diff by lia.
             apply Hnonself_sound.
             rewrite Znth_replace_Znth_Diff in Hnonself
               by lia.
             exact Hnonself.
          -- intros Hself.
             apply Hself_complete.
             unfold FlagValue, marked_flags in *.
             rewrite Znth_replace_Znth_Diff in Hself
               by lia.
             exact Hself.
  }
  assert (Hprogress_marked_j :
    CurrentBaseProgress n current j marked_flags primes).
  {
    unfold CurrentBaseProgress in *.
    intros pos Hpos.
    specialize (Hprogress pos Hpos).
    unfold CurrentProductMarked in *.
    intros Hrange.
    destruct (Hprogress Hrange) as [Hvalue [Hnonself Hentry_old]].
    assert (Hpos_product_neq :
      ProductIndex current pos primes <> product).
    {
      unfold PrimePrefixList in Hprefix.
      destruct Hprefix as [_ [_ [_ Hsorted]]].
      specialize (Hsorted pos j ltac:(lia)).
      unfold ProductIndex, product, selected.
      nia.
    }
    split.
    - unfold FlagValue, marked_flags.
      rewrite Znth_replace_Znth_Diff by lia.
      exact Hvalue.
    - split.
      + unfold FlagValue, marked_flags.
        rewrite Znth_replace_Znth_Diff by lia.
        exact Hnonself.
      + unfold FlagValue, marked_flags.
        rewrite Znth_replace_Znth_Diff by lia.
        exact Hentry_old.
  }
  assert (Hprogress_marked_next :
    CurrentBaseProgress n current (j + 1) marked_flags primes).
  {
    unfold CurrentBaseProgress.
    intros pos Hpos.
    destruct (Z.eq_dec pos j) as [Hpos_eq | Hpos_neq].
    - subst pos.
      unfold CurrentProductMarked.
      intros _.
      split.
      + unfold FlagValue, marked_flags, product, selected.
        rewrite Znth_replace_Znth_Same by (rewrite Hflags_len; lia).
        reflexivity.
      + split.
        * unfold FlagValue, marked_flags, product, selected.
          rewrite Znth_replace_Znth_Same by (rewrite Hflags_len; lia).
          exact Hselected_neq_product.
        * unfold FlagValue, marked_flags, product, selected.
          rewrite Znth_replace_Znth_Same by (rewrite Hflags_len; lia).
          unfold product, selected in Hentry.
          exact Hentry.
    - apply Hprogress_marked_j.
      lia.
  }
  assert (Hinner_marked :
    EulerInnerState n current j tot marked_flags primes).
  {
    unfold EulerInnerState.
    split; [exact Hflag_marked |].
    split; [exact Hprimes_len |].
    split; [lia |].
    split; [lia |].
    split; [lia |].
    split; [lia |].
    split; [lia |].
    split; [lia |].
    split; [lia |].
    split; [exact Hprefix |].
    split; [exact Hbounds |].
    split; [exact Hprogress_marked_j |].
    split; [exact Hprior |].
    intros Hgt.
    lia.
  }
  assert (Hdivide_exit :
    Z.divide selected current ->
    EulerOuterState n (current + 1) tot marked_flags primes).
  {
    intros Hdivide.
    unfold EulerOuterState.
    split.
    - eapply EulerFlagState_advance_after_inner_divide__core_invariants;
        [exact Hcurrent_ge | exact Hcurrent_le | exact Hj_ge | exact Hj_le |
         exact Hprefix | exact Hflag_marked | exact Hprogress_marked_next |
         exact Hprior | unfold selected; exact Hdivide].
    - split; [exact Hprimes_len |].
      split; [lia |].
      split; [lia |].
      split; [lia |].
      split; [lia |].
      split.
      + replace (current + 1 - 1) with current by lia.
        exact Hprefix.
      + unfold PrimeBounds in *.
        intros pos Hpos.
        specialize (Hbounds pos Hpos) as [Hlower Hupper].
        lia.
  }
  assert (Hnondivide_exit :
    ~ Z.divide selected current ->
    EulerInnerState n current (j + 1) tot marked_flags primes).
  {
    intros Hnondivide.
    assert (Hprior_next : PriorNonDivisibility current (j + 1) primes).
    {
      unfold PriorNonDivisibility in *.
      intros pos Hpos.
      destruct (Z.eq_dec pos j) as [Hpos_eq | Hpos_neq].
      - subst pos.
        unfold selected in Hnondivide.
        exact Hnondivide.
      - apply Hprior.
        lia.
    }
    assert (Hj_next_le : j + 1 <= tot).
    {
      eapply (PriorNonDivisibility_nondivide_next_index__core_invariants
                current j tot primes);
        eauto.
    }
    unfold EulerInnerState.
    split; [exact Hflag_marked |].
    split; [exact Hprimes_len |].
    split; [lia |].
    split; [lia |].
    split; [lia |].
    split; [exact Hj_next_le |].
    split; [lia |].
    split; [lia |].
    split; [lia |].
    split; [exact Hprefix |].
    split; [exact Hbounds |].
    split; [exact Hprogress_marked_next |].
    split; [exact Hprior_next |].
    intros Hexit.
    unfold EulerOuterState.
    split.
    - eapply (EulerFlagState_advance_after_inner_product_exit__core_invariants
                n current (j + 1) tot marked_flags primes);
        [exact Hcurrent_ge | exact Hcurrent_le | lia | exact Hj_next_le |
         exact Hprefix | exact Hflag_marked | exact Hprogress_marked_next |
         exact Hexit].
    - split; [exact Hprimes_len |].
      split; [lia |].
      split; [lia |].
      split; [lia |].
      split; [lia |].
      split.
      + replace (current + 1 - 1) with current by lia.
        exact Hprefix.
      + unfold PrimeBounds in *.
        intros pos Hpos.
        specialize (Hbounds pos Hpos) as [Hlower Hupper].
        lia.
  }
  unfold EulerInnerMarkedState.
  split; [exact Hinner_marked |].
  split; [exact Hproduct_le |].
  split.
  - unfold product, selected in Hentry.
    exact Hentry.
  - split.
    + unfold FlagValue, marked_flags, product, selected.
      rewrite Znth_replace_Znth_Same by (rewrite Hflags_len; lia).
      reflexivity.
    + split; [exact Hprogress_marked_next |].
      split.
      * unfold selected in Hdivide_exit.
        exact Hdivide_exit.
      * unfold selected in Hnondivide_exit.
        exact Hnondivide_exit.
Qed.
