Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import AUXLib.ListLib.

Import ListNotations.
Local Open Scope Z_scope.

(** Mathematical primality, independent of any program array or sieve state. *)
Definition StrictPrime (p : Z) : Prop :=
  1 < p /\
  forall d : Z,
    0 < d ->
    Z.divide d p ->
    d = 1 \/ d = p.

(** [HasProperDivisorBelow bound k] says that [k] has a nontrivial positive
    divisor strictly below both [bound] and [k]. *)
Definition HasProperDivisorBelow (bound k : Z) : Prop :=
  exists d : Z,
    2 <= d /\
    d < bound /\
    d < k /\
    Z.divide d k.

(** Exact, two-sided 0/1 interpretation of a mathematical proposition. *)
Definition ExactZeroOne (is_zero : Prop) (value : Z) : Prop :=
  (is_zero /\ value = 0) \/ (~ is_zero /\ value = 1).

(** The required final contents of the concrete segment [f[1]..f[n]].
    Logical position [k - 1] represents the program index [k]. *)
Definition PrimeIndicatorList (n : Z) (values : list Z) : Prop :=
  Zlength values = n /\
  forall k : Z,
    1 <= k <= n ->
    ((StrictPrime k /\ Znth (k - 1) values 0 = 1) \/
     (~ StrictPrime k /\ Znth (k - 1) values 0 = 0)).

(** State of the first initialization loop: all program-owned indices before
    [next] have already been written to one. *)
Definition SieveInitPrefix (n next : Z) (values : list Z) : Prop :=
  Zlength values = n /\
  forall k : Z,
    1 <= k < next ->
    Znth (k - 1) values 0 = 1.

(** At outer-loop bound [bound], an index greater than one is zero exactly
    when it already has a proper divisor below [bound].  Index one is always
    zero. *)
Definition SieveStage (n bound : Z) (values : list Z) : Prop :=
  Zlength values = n /\
  forall k : Z,
    1 <= k <= n ->
    ((k = 1 /\ Znth (k - 1) values 0 = 0) \/
     (2 <= k /\
      ExactZeroOne
        (HasProperDivisorBelow bound k)
        (Znth (k - 1) values 0))).

(** Multiples of [factor] strictly before [next] that the inner loop has
    processed.  Starting at [2 * factor] excludes the factor itself. *)
Definition ProcessedMultiple (factor next k : Z) : Prop :=
  2 * factor <= k /\
  k < next /\
  Z.divide factor k.

(** Inner-loop state: the exact zero set consists of entries eliminated by a
    smaller proper divisor, plus the multiples processed in this inner loop. *)
Definition SieveMarkState
    (n factor next : Z) (values : list Z) : Prop :=
  2 <= factor /\
  2 * factor <= next /\
  Z.divide factor next /\
  Zlength values = n /\
  forall k : Z,
    1 <= k <= n ->
    ((k = 1 /\ Znth (k - 1) values 0 = 0) \/
     (2 <= k /\
      ExactZeroOne
        (HasProperDivisorBelow factor k \/
         ProcessedMultiple factor next k)
        (Znth (k - 1) values 0))).

Lemma StrictPrime_iff_no_proper_divisor :
  forall p : Z,
    1 < p ->
    (StrictPrime p <-> ~ HasProperDivisorBelow p p).
Proof.
  intros p Hp.
  split.
  - intros [_ Hprime] [d [Hd2 [_ [Hdp Hdiv]]]].
    specialize (Hprime d ltac:(lia) Hdiv).
    destruct Hprime; lia.
  - intros Hnone.
    split; [exact Hp |].
    intros d Hdpos Hdiv.
    destruct (Z.eq_dec d 1) as [-> | Hd1].
    + left; reflexivity.
    + right.
      destruct Hdiv as [q Hq].
      assert (2 <= d) by lia.
      assert (0 < q) by nia.
      assert (d <= p) by nia.
      destruct (Z.eq_dec d p) as [Heq | Hneq]; [exact Heq |].
      exfalso.
      apply Hnone.
      exists d.
      repeat split; try lia.
      exists q; exact Hq.
Qed.

Lemma StrictPrime_iff_no_divisor_below :
  forall bound k : Z,
    1 < k ->
    k < bound ->
    (StrictPrime k <-> ~ HasProperDivisorBelow bound k).
Proof.
  intros bound k Hk Hbound.
  split.
  - intros [_ Hprime] [d [Hd2 [_ [Hdk Hdiv]]]].
    specialize (Hprime d ltac:(lia) Hdiv).
    destruct Hprime; lia.
  - intros Hnone.
    apply (proj2 (StrictPrime_iff_no_proper_divisor k Hk)).
    intros [d [Hd2 [_ [Hdk Hdiv]]]].
    apply Hnone.
    exists d.
    repeat split; try lia.
    exact Hdiv.
Qed.

Lemma SieveStage_implies_PrimeIndicatorList :
  forall (n bound : Z) (values : list Z),
    n < bound ->
    SieveStage n bound values ->
    PrimeIndicatorList n values.
Proof.
  intros n bound values Hbound [Hlen Hstage].
  split; [exact Hlen |].
  intros k Hrange.
  specialize (Hstage k Hrange).
  destruct Hstage as [[Hk1 Hvalue] | [Hk2 Hvalue]].
  - subst k.
    right.
    split.
    + unfold StrictPrime; lia.
    + exact Hvalue.
  - pose proof
      (StrictPrime_iff_no_divisor_below bound k ltac:(lia) ltac:(lia))
      as Hprime.
    unfold ExactZeroOne in Hvalue.
    destruct Hvalue as [[Hbad Hzero] | [Hgood Hone]].
    + right.
      split.
      * intros Hstrict.
        exact ((proj1 Hprime Hstrict) Hbad).
      * exact Hzero.
    + left.
      split.
      * exact (proj2 Hprime Hgood).
      * exact Hone.
Qed.

Lemma SieveInitPrefix_start__sieve_invariants :
  forall (n : Z) (values : list Z),
    Zlength values = n ->
    SieveInitPrefix n 1 values.
Proof.
  intros n values Hlen.
  split; [exact Hlen |].
  intros k Hrange.
  lia.
Qed.
Lemma SieveInitPrefix_step__sieve_invariants :
  forall (n next : Z) (values : list Z),
    1 <= next ->
    next <= n ->
    SieveInitPrefix n next values ->
    SieveInitPrefix n (next + 1) (replace_Znth (next - 1) 1 values).
Proof.
  intros n next values Hnext Hnextn [Hlen Hprefix].
  split.
  - rewrite Zlength_replace_Znth.
    exact Hlen.
  - intros k Hrange.
    destruct (Z.eq_dec k next) as [-> | Hneq].
    + rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
      reflexivity.
    + rewrite Znth_replace_Znth_Diff by (rewrite ?Hlen; lia).
      apply Hprefix.
      lia.
Qed.
Lemma SieveInitPrefix_finish__sieve_invariants :
  forall (n next : Z) (values : list Z),
    2 <= n ->
    n < next ->
    next <= n + 1 ->
    SieveInitPrefix n next values ->
    SieveStage n 2
      (replace_Znth (2 - 1) 1 (replace_Znth (1 - 1) 0 values)).
Proof.
  intros n next values Hn Hnext_lower Hnext_upper [Hlen Hprefix].
  assert (Hnext : next = n + 1) by lia.
  subst next.
  split.
  - repeat rewrite Zlength_replace_Znth.
    exact Hlen.
  - intros k Hrange.
    destruct (Z.eq_dec k 1) as [-> | Hk1].
    + left.
      split; [reflexivity |].
      rewrite Znth_replace_Znth_Diff
        by (rewrite ?Zlength_replace_Znth, ?Hlen; lia).
      rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
      reflexivity.
    + right.
      split; [lia |].
      unfold ExactZeroOne.
      right.
      split.
      * intros [d [Hd2 [Hdlt _]]].
        lia.
      * destruct (Z.eq_dec k 2) as [-> | Hk2].
        -- rewrite Znth_replace_Znth_Same
             by (rewrite Zlength_replace_Znth, Hlen; lia).
           reflexivity.
        -- rewrite Znth_replace_Znth_Diff
             by (rewrite ?Zlength_replace_Znth, ?Hlen; lia).
           rewrite Znth_replace_Znth_Diff by (rewrite ?Hlen; lia).
           apply Hprefix.
           lia.
Qed.
Lemma SieveStage_mark_start__sieve_invariants :
  forall (n factor : Z) (values : list Z),
    2 <= factor ->
    factor <= n ->
    SieveStage n factor values ->
    SieveMarkState n factor (factor * 2) values.
Proof.
  intros n factor values Hfactor Hfactorn [Hlen Hstage].
  repeat split.
  - exact Hfactor.
  - nia.
  - exists 2.
    ring.
  - exact Hlen.
  - intros k Hrange.
    specialize (Hstage k Hrange).
    destruct Hstage as [[Hk1 Hvalue] | [Hk2 Hvalue]].
    + left.
      split; assumption.
    + right.
      split; [exact Hk2 |].
      unfold ExactZeroOne in *.
      destruct Hvalue as [[Hbad Hzero] | [Hgood Hone]].
      * left.
        split; [left; exact Hbad | exact Hzero].
      * right.
        split.
        -- intros [Hbad | Hprocessed].
           ++ exact (Hgood Hbad).
           ++ unfold ProcessedMultiple in Hprocessed.
              nia.
        -- exact Hone.
Qed.
Lemma ProcessedMultiple_step_except_current__sieve_invariants :
  forall (factor next k : Z),
    0 < factor ->
    Z.divide factor next ->
    k <> next ->
    (ProcessedMultiple factor (next + factor) k <->
     ProcessedMultiple factor next k).
Proof.
  intros factor next k Hfactor Hnextdiv Hneq.
  unfold ProcessedMultiple.
  split.
  - intros [Hlower [Hupper Hkdiv]].
    repeat split; try assumption.
    destruct Hnextdiv as [a Ha].
    destruct Hkdiv as [b Hb].
    destruct (Z_lt_ge_dec k next) as [Hknext | Hnextk].
    + exact Hknext.
    + exfalso.
      assert (Hnextk_strict : next < k) by lia.
      assert (Hab : a < b).
      {
        apply (proj2 (Z.mul_lt_mono_pos_r factor a b Hfactor)).
        rewrite <- Ha, <- Hb.
        exact Hnextk_strict.
      }
      pose proof
        (Z.mul_le_mono_nonneg_r (a + 1) b factor ltac:(lia) ltac:(lia))
        as Hproduct.
      nia.
  - intros [Hlower [Hupper Hkdiv]].
    repeat split; try assumption.
    lia.
Qed.
Lemma SieveMarkState_step__sieve_invariants :
  forall (n factor next : Z) (values : list Z),
    next <= n ->
    SieveMarkState n factor next values ->
    SieveMarkState n factor (next + factor)
      (replace_Znth (next - 1) 0 values).
Proof.
  intros n factor next values Hnextn
    [Hfactor [Hstart [Hnextdiv [Hlen Hmark]]]].
  repeat split.
  - exact Hfactor.
  - lia.
  - destruct Hnextdiv as [q Hq].
    exists (q + 1).
    nia.
  - rewrite Zlength_replace_Znth.
    exact Hlen.
  - intros k Hrange.
    specialize (Hmark k Hrange).
    destruct Hmark as [[Hk1 Hvalue] | [Hk2 Hvalue]].
    + left.
      split; [exact Hk1 |].
      rewrite Znth_replace_Znth_Diff by (rewrite ?Hlen; lia).
      exact Hvalue.
    + right.
      split; [exact Hk2 |].
      destruct (Z.eq_dec k next) as [-> | Hneq].
      * unfold ExactZeroOne.
        left.
        split.
        -- right.
           unfold ProcessedMultiple.
           repeat split; try lia.
           exact Hnextdiv.
        -- rewrite Znth_replace_Znth_Same by (rewrite Hlen; lia).
           reflexivity.
      * rewrite Znth_replace_Znth_Diff by (rewrite ?Hlen; lia).
        pose proof
          (ProcessedMultiple_step_except_current__sieve_invariants
             factor next k ltac:(lia) Hnextdiv Hneq) as Hprocessed.
        unfold ExactZeroOne in *.
        destruct Hvalue as [[Hold Hzero] | [Hnot_old Hone]].
        -- left.
           split.
           ++ destruct Hold as [Hbad | Hold].
              ** left; exact Hbad.
              ** right; exact (proj2 Hprocessed Hold).
           ++ exact Hzero.
        -- right.
           split.
           ++ intros [Hbad | Hnew].
              ** apply Hnot_old; left; exact Hbad.
              ** apply Hnot_old; right; exact (proj1 Hprocessed Hnew).
           ++ exact Hone.
Qed.
Lemma HasProperDivisorBelow_succ_at_mark_exit__sieve_invariants :
  forall (factor next k : Z),
    2 <= factor ->
    k < next ->
    (HasProperDivisorBelow (factor + 1) k <->
     HasProperDivisorBelow factor k \/ ProcessedMultiple factor next k).
Proof.
  intros factor next k Hfactor Hknext.
  split.
  - intros [d [Hd2 [Hdbound [Hdk Hddiv]]]].
    destruct (Z_lt_ge_dec d factor) as [Hdlt | Hdge].
    + left.
      exists d.
      repeat split; try assumption.
    + right.
      assert (Hd : d = factor) by lia.
      subst d.
      unfold ProcessedMultiple.
      repeat split; try assumption.
      destruct Hddiv as [q Hq].
      assert (Honeq : 1 < q).
      {
        apply (proj2 (Z.mul_lt_mono_pos_r factor 1 q ltac:(lia))).
        rewrite <- Hq.
        nia.
      }
      pose proof
        (Z.mul_le_mono_nonneg_r 2 q factor ltac:(lia) ltac:(lia))
        as Hproduct.
      nia.
  - intros [Hbad | Hprocessed].
    + destruct Hbad as [d [Hd2 [Hdbound [Hdk Hddiv]]]].
      exists d.
      repeat split; try assumption; lia.
    + unfold ProcessedMultiple in Hprocessed.
      destruct Hprocessed as [Hlower [Hupper Hdiv]].
      exists factor.
      repeat split; try assumption; lia.
Qed.
Lemma SieveMarkState_finish__sieve_invariants :
  forall (n factor next : Z) (values : list Z),
    n < next ->
    SieveMarkState n factor next values ->
    SieveStage n (factor + 1) values.
Proof.
  intros n factor next values Hnnext
    [Hfactor [Hstart [Hnextdiv [Hlen Hmark]]]].
  split; [exact Hlen |].
  intros k Hrange.
  specialize (Hmark k Hrange).
  destruct Hmark as [[Hk1 Hvalue] | [Hk2 Hvalue]].
  - left.
    split; assumption.
  - right.
    split; [exact Hk2 |].
    pose proof
      (HasProperDivisorBelow_succ_at_mark_exit__sieve_invariants
         factor next k Hfactor ltac:(lia)) as Htransition.
    unfold ExactZeroOne in *.
    destruct Hvalue as [[Hold Hzero] | [Hnot_old Hone]].
    + left.
      split; [exact (proj2 Htransition Hold) | exact Hzero].
    + right.
      split.
      * intros Hnew.
        exact (Hnot_old (proj1 Htransition Hnew)).
      * exact Hone.
Qed.
Lemma HasProperDivisorBelow_succ_absorbed__sieve_invariants :
  forall (factor k : Z),
    HasProperDivisorBelow factor factor ->
    (HasProperDivisorBelow (factor + 1) k <->
     HasProperDivisorBelow factor k).
Proof.
  intros factor k [small [Hsmall2 [Hsmallfactor [_ Hsmall_div_factor]]]].
  split.
  - intros [d [Hd2 [Hdbound [Hdk Hddiv]]]].
    destruct (Z_lt_ge_dec d factor) as [Hdlt | Hdge].
    + exists d.
      repeat split; try assumption.
    + assert (Hd : d = factor) by lia.
      subst d.
      exists small.
      repeat split; try assumption; try lia.
      destruct Hsmall_div_factor as [q Hq].
      destruct Hddiv as [r Hr].
      exists (q * r).
      nia.
  - intros [d [Hd2 [Hdbound [Hdk Hddiv]]]].
    exists d.
    repeat split; try assumption; lia.
Qed.
Lemma SieveStage_skip_composite__sieve_invariants :
  forall (n factor : Z) (values : list Z),
    2 <= factor ->
    factor <= n ->
    Znth (factor - 1) values 0 <> 1 ->
    SieveStage n factor values ->
    SieveStage n (factor + 1) values.
Proof.
  intros n factor values Hfactor Hfactorn Hvalue_not_one [Hlen Hstage].
  assert (Hfactor_bad : HasProperDivisorBelow factor factor).
  {
    specialize (Hstage factor ltac:(lia)).
    destruct Hstage as [[Hfactor1 _] | [_ Hvalue]].
    - lia.
    - unfold ExactZeroOne in Hvalue.
      destruct Hvalue as [[Hbad _] | [_ Hone]].
      + exact Hbad.
      + exfalso.
        exact (Hvalue_not_one Hone).
  }
  split; [exact Hlen |].
  intros k Hrange.
  specialize (Hstage k Hrange).
  destruct Hstage as [[Hk1 Hvalue] | [Hk2 Hvalue]].
  - left.
    split; assumption.
  - right.
    split; [exact Hk2 |].
    pose proof
      (HasProperDivisorBelow_succ_absorbed__sieve_invariants
         factor k Hfactor_bad) as Htransition.
    unfold ExactZeroOne in *.
    destruct Hvalue as [[Hold Hzero] | [Hnot_old Hone]].
    + left.
      split; [exact (proj2 Htransition Hold) | exact Hzero].
    + right.
      split.
      * intros Hnew.
        exact (Hnot_old (proj1 Htransition Hnew)).
      * exact Hone.
Qed.
