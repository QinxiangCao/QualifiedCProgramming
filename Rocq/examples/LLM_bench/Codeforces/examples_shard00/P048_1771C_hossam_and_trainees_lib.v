Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Local Open Scope Z_scope.
Definition Pre (a : list Z) : Prop := 2 <= Zlength a <= 100000 /\ Forall (fun x => 1 <= x <= 1000000000) a.
Definition Spec (a : list Z) (out : Z) : Prop :=
  (out = 0 \/ out = 1) /\ (out = 1 <->
    exists i j x, 0 <= i < Zlength a /\ 0 <= j < Zlength a /\ i <> j /\ x >= 2 /\
      (x | Znth i a 0) /\ (x | Znth j a 0)).

Require Import Coq.Sorting.Permutation.
Require Import Coq.ZArith.Znumtheory.
Require Import AUXLib.ListLib.

Import ListNotations.

Definition MarkedBefore (bound value : Z) : Prop :=
  exists d, 2 <= d < bound /\ (d | value).

Definition PrimePrefixTable
    (bound : Z) (primes flags : list Z) : Prop :=
  2 <= bound <= 31624 /\
  Zlength flags = 31624 /\
  NoDup primes /\
  Forall prime primes /\
  increasing primes /\
  (forall p, In p primes <-> 2 <= p < bound /\ prime p) /\
  (forall k, 2 <= k <= 31623 ->
     (Znth k flags 0 = 0 <-> ~ MarkedBefore bound k)).

Definition PrimeMarkTable
    (factor next : Z) (primes flags : list Z) : Prop :=
  2 <= factor <= 31623 /\
  factor * factor <= next /\
  Zlength flags = 31624 /\
  NoDup primes /\
  Forall prime primes /\
  increasing primes /\
  (forall p, In p primes <-> 2 <= p < factor + 1 /\ prime p) /\
  (forall k, 2 <= k <= 31623 ->
     (Znth k flags 0 = 0 <->
        ~ (MarkedBefore factor k \/
           (factor | k) /\ factor * factor <= k < next))).

Definition CompletePrimeTable (primes : list Z) : Prop :=
  NoDup primes /\
  Forall prime primes /\
  increasing primes /\
  (forall p, In p primes <-> 2 <= p <= 31623 /\ prime p).

Definition zdividesb (p x : Z) : bool :=
  if Zdivide_dec p x then true else false.

Definition PrimeFactorBagPrefix
    (a : list Z) (upto : Z) (factors : list Z) : Prop :=
  0 <= upto <= Zlength a /\
  Forall prime factors /\
  forall p, prime p ->
    Z.of_nat (count_occ Z.eq_dec factors p) =
    Z.of_nat
      (length
         (filter (zdividesb p) (firstn (Z.to_nat upto) a))).

Definition FactorScanState
    (a primes : list Z) (index tested rem : Z) (factors : list Z) : Prop :=
  exists done picked,
    factors = done ++ picked /\
    PrimeFactorBagPrefix a index done /\
    0 <= index < Zlength a /\
    0 <= tested <= Zlength primes /\
    1 <= rem <= Znth index a 1 /\
    (rem | Znth index a 1) /\
    NoDup picked /\
    Forall prime picked /\
    (forall p, prime p ->
       (In p picked <->
        In p (firstn (Z.to_nat tested) primes) /\
        (p | Znth index a 1))) /\
    (forall p,
       In p (firstn (Z.to_nat tested) primes) -> ~ (p | rem)).

Definition FactorDivideState
    (a primes : list Z) (index tested rem : Z) (factors : list Z) : Prop :=
  exists done picked p,
    factors = done ++ picked ++ [p] /\
    PrimeFactorBagPrefix a index done /\
    0 <= index < Zlength a /\
    0 <= tested < Zlength primes /\
    p = Znth tested primes 0 /\
    prime p /\
    (p | Znth index a 1) /\
    1 <= rem <= Znth index a 1 /\
    (rem | Znth index a 1) /\
    NoDup picked /\
    Forall prime picked /\
    (forall q, prime q ->
       (In q picked <->
        In q (firstn (Z.to_nat tested) primes) /\
        (q | Znth index a 1))) /\
    (forall q,
       In q (firstn (Z.to_nat tested) primes) -> ~ (q | rem)).

Definition DuplicatePrefixState
    (factors : list Z) (upto found : Z) : Prop :=
  0 <= upto <= Zlength factors /\
  (found = 0 \/ found = 1) /\
  (found = 1 <->
    exists i j,
      0 <= i < j /\ j < upto /\
      Znth i factors 0 = Znth j factors 0).

Definition ProperMarkedBefore (bound value : Z) : Prop :=
  exists d, 2 <= d < bound /\ d < value /\ (d | value).

Definition PrimePrefixTable2
    (bound : Z) (primes flags : list Z) : Prop :=
  2 <= bound <= 31624 /\
  Zlength flags = 31624 /\
  NoDup primes /\
  Forall prime primes /\
  increasing primes /\
  (forall p, In p primes <-> 2 <= p < bound /\ prime p) /\
  (forall k, 2 <= k <= 31623 ->
     (Znth k flags 0 = 0 <-> ~ ProperMarkedBefore bound k)).

Definition PrimeMarkTable2
    (factor next : Z) (primes flags : list Z) : Prop :=
  2 <= factor <= 31623 /\
  factor * factor <= next /\
  (factor | next) /\
  Zlength flags = 31624 /\
  NoDup primes /\
  Forall prime primes /\
  increasing primes /\
  (forall p, In p primes <-> 2 <= p < factor + 1 /\ prime p) /\
  (forall k, 2 <= k <= 31623 ->
     (Znth k flags 0 = 0 <->
        ~ (ProperMarkedBefore factor k \/
           (factor | k) /\ factor * factor <= k < next))).

Definition FactorAppendCapacity
    (primes : list Z) (index tested rem count : Z) : Prop :=
  (0 <= tested < Zlength primes /\ (Znth tested primes 0 | rem)) ->
  count + 1 <= index * 10 + 9.

Definition DuplicateScanLoopState
    (factors : list Z) (count cursor found : Z) : Prop :=
  (count = 0 /\ cursor = 1 /\ DuplicatePrefixState factors 0 found) \/
  (1 <= count /\ 1 <= cursor <= count /\
   DuplicatePrefixState factors cursor found).

Definition ResidualPrimeCoverage
    (original rem : Z) (picked : list Z) : Prop :=
  forall p, prime p ->
    ((p | original) <-> In p picked \/ (p | rem)).

Definition FactorScanState2
    (a primes : list Z) (index tested rem : Z) (factors : list Z) : Prop :=
  exists done picked,
    factors = done ++ picked /\
    PrimeFactorBagPrefix a index done /\
    0 <= index < Zlength a /\
    0 <= tested <= Zlength primes /\
    1 <= rem <= Znth index a 1 /\
    (rem | Znth index a 1) /\
    NoDup picked /\
    Forall prime picked /\
    (forall p, prime p ->
       (In p picked <->
        In p (firstn (Z.to_nat tested) primes) /\
        (p | Znth index a 1))) /\
    (forall p,
       In p (firstn (Z.to_nat tested) primes) -> ~ (p | rem)) /\
    ResidualPrimeCoverage (Znth index a 1) rem picked.

Definition FactorDivideState2
    (a primes : list Z) (index tested rem : Z) (factors : list Z) : Prop :=
  exists done picked p,
    factors = done ++ picked ++ [p] /\
    PrimeFactorBagPrefix a index done /\
    0 <= index < Zlength a /\
    0 <= tested < Zlength primes /\
    p = Znth tested primes 0 /\
    prime p /\
    (p | Znth index a 1) /\
    1 <= rem <= Znth index a 1 /\
    (rem | Znth index a 1) /\
    NoDup picked /\
    Forall prime picked /\
    (forall q, prime q ->
       (In q picked <->
        In q (firstn (Z.to_nat tested) primes) /\
        (q | Znth index a 1))) /\
    (forall q,
       In q (firstn (Z.to_nat tested) primes) -> ~ (q | rem)) /\
    ResidualPrimeCoverage (Znth index a 1) rem (picked ++ [p]).

Lemma FactorScanState2_implies_FactorScanState :
  forall a primes index tested rem factors,
    FactorScanState2 a primes index tested rem factors ->
    FactorScanState a primes index tested rem factors.
Proof.
  intros a primes index tested rem factors H.
  unfold FactorScanState2 in H.
  unfold FactorScanState.
  destruct H as
    (done & picked & Hfactors & Hbag & Hindex & Htested & Hrem_bounds &
     Hrem_divides & Hnodup & Hprimes & Hpicked & Hexcluded & Hcoverage).
  exists done, picked.
  repeat (split; [assumption |]).
  assumption.
Qed.

Lemma FactorDivideState2_implies_FactorDivideState :
  forall a primes index tested rem factors,
    FactorDivideState2 a primes index tested rem factors ->
    FactorDivideState a primes index tested rem factors.
Proof.
  intros a primes index tested rem factors H.
  unfold FactorDivideState2 in H.
  unfold FactorDivideState.
  destruct H as
    (done & picked & p & Hfactors & Hbag & Hindex & Htested & Hp & Hprime &
     Hp_divides & Hrem_bounds & Hrem_divides & Hnodup & Hprimes & Hpicked &
     Hexcluded & Hcoverage).
  exists done, picked, p.
  repeat (split; [assumption |]).
  assumption.
Qed.

Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Psatz.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.Zquot.
Lemma complete_prime_table_index_bounds__safety_prime_bounds :
  forall primes j,
    CompletePrimeTable primes ->
    0 <= j < Zlength primes ->
    prime (Znth j primes 0) /\ 2 <= Znth j primes 0 <= 31623.
Proof.
  intros primes j Htable Hj.
  unfold CompletePrimeTable in Htable.
  destruct Htable as (_ & _ & _ & Hcomplete).
  pose proof
    (proj1 (Hcomplete (Znth j primes 0))
       (Znth_In_Zlength primes 0 j Hj)) as [Hbounds Hprime].
  split; assumption.
Qed.
Lemma factor_divide_state_current_prime__safety_prime_bounds :
  forall a primes index tested rem factors,
    FactorDivideState2 a primes index tested rem factors ->
    prime (Znth tested primes 0) /\ Znth tested primes 0 <> 0.
Proof.
  intros a primes index tested rem factors Hstate.
  unfold FactorDivideState2 in Hstate.
  destruct Hstate as
    (done & picked & p & Hfactors & Hbag & Hindex & Htested & Hp & Hprime &
     Hp_divides & Hrem_bounds & Hrem_divides & Hnodup & Hprimes & Hpicked &
     Hexcluded & Hcoverage).
  subst p.
  split; [exact Hprime |].
  pose proof (prime_ge_2 _ Hprime).
  lia.
Qed.
Lemma bounded_prime_square_int64__safety_prime_bounds :
  forall p,
    2 <= p <= 31623 ->
    0 <= p * p <= 2000000000.
Proof.
  intros p Hp.
  split; nia.
Qed.
Lemma increasing_aux_snoc__sieve_construction :
  forall (l : list Z) (x y : Z),
    increasing_aux l x ->
    (forall z, In z l -> z <= y) ->
    x <= y ->
    increasing_aux (l ++ [y]) x.
Proof.
  induction l as [|a l IH]; intros x y Hinc Hall Hxy; simpl in *.
  - auto.
  - destruct Hinc as [Hxa Hinc].
    split; [exact Hxa|].
    apply IH; auto.
Qed.
Lemma increasing_snoc__sieve_construction :
  forall (l : list Z) (y : Z),
    increasing l ->
    (forall x, In x l -> x <= y) ->
    increasing (l ++ [y]).
Proof.
  intros l y Hinc Hall.
  destruct l as [|a l]; simpl in *; auto.
  apply increasing_aux_snoc__sieve_construction; auto.
Qed.
Lemma proper_marked_before_advance_large__sieve_construction :
  forall i k,
    2 <= i ->
    i * i > 31623 ->
    2 <= k <= 31623 ->
    (ProperMarkedBefore (i + 1) k <-> ProperMarkedBefore i k).
Proof.
  intros i k Hi Hsquare Hk. split.
  - intros [d [[Hd2 Hdbound] [Hdk Hddiv]]].
    destruct (Z_lt_ge_dec d i) as [Hdi|Hdi].
    + exists d. repeat split; auto.
    + assert (d = i) by lia. subst d.
      destruct Hddiv as [q Hq].
      assert (1 < q) by nia.
      assert (q < i) by nia.
      exists q. repeat split; try lia.
      exists i. nia.
  - intros [d [[Hd2 Hdi] [Hdk Hddiv]]].
    exists d. repeat split; auto; lia.
Qed.
Lemma proper_marked_before_advance_marked__sieve_construction :
  forall i k,
    ProperMarkedBefore i i ->
    (ProperMarkedBefore (i + 1) k <-> ProperMarkedBefore i k).
Proof.
  intros i k HiMarked. split.
  - intros [d [[Hd2 Hdbound] [Hdk Hddiv]]].
    destruct (Z_lt_ge_dec d i) as [Hdi|Hdi].
    + exists d. repeat split; auto.
    + assert (d = i) by lia. subst d.
      destruct HiMarked as [e [[He2 Hei] [Hei' Hedivi]]].
      destruct Hedivi as [u Hu].
      destruct Hddiv as [v Hv].
      exists e. repeat split; try lia.
      exists (u * v). nia.
  - intros [d [[Hd2 Hdi] [Hdk Hddiv]]].
    exists d. repeat split; auto; lia.
Qed.
Lemma prime_prefix_table2_unmarked_prime__sieve_construction :
  forall bound primes flags,
    PrimePrefixTable2 bound primes flags ->
    2 <= bound <= 31623 ->
    Znth bound flags 0 = 0 ->
    prime bound.
Proof.
  intros bound primes flags Htable Hbound Hzero.
  destruct Htable as [_ [_ [_ [_ [_ [_ Hflags]]]]]].
  specialize (Hflags bound Hbound).
  assert (Hnotmarked : ~ ProperMarkedBefore bound bound).
  { apply (proj1 Hflags). exact Hzero. }
  destruct (prime_dec bound) as [Hp|Hnp]; auto.
  exfalso. apply Hnotmarked.
  destruct (not_prime_divide bound) as [d [[Hd2 Hdlt] Hddiv]]; try lia; auto.
  exists d. repeat split; auto; lia.
Qed.
Lemma prime_prefix_table2_begin_mark__sieve_construction :
  forall factor primes flags,
    PrimePrefixTable2 factor primes flags ->
    2 <= factor <= 31623 ->
    Znth factor flags 0 = 0 ->
    factor * factor <= 31623 ->
    PrimeMarkTable2 factor (factor * factor) (primes ++ [factor]) flags.
Proof.
  intros factor primes flags Htable Hfactor Hzero Hsquare.
  pose proof (prime_prefix_table2_unmarked_prime__sieve_construction
                factor primes flags Htable Hfactor Hzero) as Hprime.
  destruct Htable as [Hbound [Hlen [Hnodup [Hforall [Hinc [Hchar Hflags]]]]]].
  unfold PrimeMarkTable2.
  split; [lia|].
  split; [lia|].
  split; [exists factor; ring|].
  split; [exact Hlen|].
  split.
  - apply NoDup_app.
    + exact Hnodup.
    + constructor; [simpl; tauto|constructor].
    + intros x Hin Hsingle. simpl in Hsingle.
      destruct Hsingle as [Heq|[]]. subst x.
      apply (proj1 (Hchar factor)) in Hin. lia.
  - split.
    + apply Forall_app. split; auto.
    + split.
      * apply increasing_snoc__sieve_construction; auto.
        intros p Hin. apply (proj1 (Hchar p)) in Hin. lia.
      * split.
        -- intros p. rewrite in_app_iff. simpl. rewrite Hchar.
           split.
           ++ intros [[[Hp2 Hplt] Hpp]|[Heq|[]]].
              ** split; [split; lia|exact Hpp].
              ** subst p. split; [split; lia|exact Hprime].
           ++ intros [[Hp2 Hplt] Hpp].
              destruct (Z_lt_ge_dec p factor) as [Hlt|Hge].
              ** left. split; [split; lia|exact Hpp].
              ** right. left. f_equal. lia.
        -- intros k Hk. specialize (Hflags k Hk).
           rewrite Hflags. split.
           ++ intros Hnot [Hproper|[_ Hrange]]; [apply Hnot; exact Hproper|lia].
           ++ intros Hnot Hproper. apply Hnot. left. exact Hproper.
Qed.
Lemma prime_prefix_table2_advance_unmarked__sieve_construction :
  forall factor primes flags,
    PrimePrefixTable2 factor primes flags ->
    2 <= factor <= 31623 ->
    Znth factor flags 0 = 0 ->
    factor * factor > 31623 ->
    PrimePrefixTable2 (factor + 1) (primes ++ [factor]) flags.
Proof.
  intros factor primes flags Htable Hfactor Hzero Hsquare.
  pose proof (prime_prefix_table2_unmarked_prime__sieve_construction
                factor primes flags Htable Hfactor Hzero) as Hprime.
  destruct Htable as [Hbound [Hlen [Hnodup [Hforall [Hinc [Hchar Hflags]]]]]].
  unfold PrimePrefixTable2.
  split; [lia|].
  split; [exact Hlen|].
  split.
  - apply NoDup_app.
    + exact Hnodup.
    + constructor; [simpl; tauto|constructor].
    + intros x Hin Hsingle. simpl in Hsingle.
      destruct Hsingle as [Heq|[]]. subst x.
      apply (proj1 (Hchar factor)) in Hin. lia.
  - split.
    + apply Forall_app. split; auto.
    + split.
      * apply increasing_snoc__sieve_construction; auto.
        intros p Hin. apply (proj1 (Hchar p)) in Hin. lia.
      * split.
        -- intros p. rewrite in_app_iff. simpl. rewrite Hchar.
           split.
           ++ intros [[[Hp2 Hplt] Hpp]|[Heq|[]]].
              ** split; [split; lia|exact Hpp].
              ** subst p. split; [split; lia|exact Hprime].
           ++ intros [[Hp2 Hplt] Hpp].
              destruct (Z_lt_ge_dec p factor) as [Hlt|Hge].
              ** left. split; [split; lia|exact Hpp].
              ** right. left. f_equal. lia.
        -- intros k Hk. specialize (Hflags k Hk).
           rewrite Hflags.
           pose proof (proper_marked_before_advance_large__sieve_construction
             factor k ltac:(lia) Hsquare Hk) as Hequiv.
           tauto.
Qed.
Lemma prime_prefix_table2_advance_marked__sieve_construction :
  forall factor primes flags,
    PrimePrefixTable2 factor primes flags ->
    2 <= factor <= 31623 ->
    Znth factor flags 0 <> 0 ->
    PrimePrefixTable2 (factor + 1) primes flags.
Proof.
  intros factor primes flags Htable Hfactor Hnonzero.
  destruct Htable as [Hbound [Hlen [Hnodup [Hforall [Hinc [Hchar Hflags]]]]]].
  assert (Hmarked : ProperMarkedBefore factor factor).
  { apply NNPP. intros Hnot.
    apply Hnonzero. apply (proj2 (Hflags factor Hfactor)). exact Hnot. }
  unfold PrimePrefixTable2.
  split; [lia|].
  split; [exact Hlen|].
  split; [exact Hnodup|].
  split; [exact Hforall|].
  split; [exact Hinc|].
  split.
  - intros p. rewrite Hchar. split.
    + intros [[Hp2 Hplt] Hpp]. split; [split; lia|exact Hpp].
    + intros [[Hp2 Hplt] Hpp].
      assert (p <> factor).
      { intros Heq. subst p. destruct Hmarked as [d [[Hd2 Hdlt] [_ Hddiv]]].
        pose proof (prime_divisors factor Hpp d Hddiv) as Hd.
        lia. }
      split; [split; lia|exact Hpp].
  - intros k Hk. specialize (Hflags k Hk).
    rewrite Hflags.
    pose proof (proper_marked_before_advance_marked__sieve_construction
      factor k Hmarked) as Hequiv.
    tauto.
Qed.
Lemma bounded_primes_complete__sieve_construction :
  forall p,
    0 <= p <= 31623 ->
    prime p ->
    In p
      (filter
        (fun p =>
          forallb
            (fun q => Z.eqb p q || negb (Z.eqb (p mod q) 0))
            ([2; 3; 5; 7; 11; 13; 17; 19; 23; 29; 31; 37; 41; 43; 47;
             53; 59; 61; 67; 71; 73; 79; 83; 89; 97; 101; 103; 107; 109;
             113; 127; 131; 137; 139; 149; 151; 157; 163; 167; 173]%Z : list Z))
        (map Z.of_nat (seq 0 31624))).
Proof.
  intros p Hp Hprime.
  apply filter_In. split.
  - apply in_map_iff. exists (Z.to_nat p). split.
    + apply Z2Nat.id. lia.
    + apply in_seq. split; [lia|].
      change (Z.to_nat p < Z.to_nat 31624)%nat.
      apply Z2Nat.inj_lt; lia.
  - apply forallb_forall. intros q Hq.
    assert (Hqbound : 2 <= q <= 173) by (simpl in Hq; intuition subst; lia).
    destruct (Z.eq_dec p q) as [Heq|Hneq].
    + subst q. rewrite Z.eqb_refl. reflexivity.
    + apply orb_true_iff. right. apply negb_true_iff. apply Z.eqb_neq.
      intros Hmod.
      assert (Hdiv : (q | p)).
      { apply Zmod_divide; lia. }
      pose proof (prime_divisors p Hprime q Hdiv) as Hcases.
      lia.
Qed.
Lemma bounded_primes_length__sieve_construction :
  (length
    (filter
      (fun p =>
        forallb
          (fun q => Z.eqb p q || negb (Z.eqb (p mod q) 0))
          ([2; 3; 5; 7; 11; 13; 17; 19; 23; 29; 31; 37; 41; 43; 47;
           53; 59; 61; 67; 71; 73; 79; 83; 89; 97; 101; 103; 107; 109;
           113; 127; 131; 137; 139; 149; 151; 157; 163; 167; 173]%Z : list Z))
      (map Z.of_nat (seq 0 31624))) < 3999)%nat.
Proof.
  native_compute. lia.
Qed.
Lemma prime_prefix_table2_capacity__sieve_construction :
  forall bound primes flags,
    PrimePrefixTable2 bound primes flags ->
    Zlength primes + 1 < 4000.
Proof.
  intros bound primes flags Htable.
  destruct Htable as [Hbound [_ [Hnodup [_ [_ [Hchar _]]]]]].
  assert (Hincl : incl primes
    (filter
      (fun p =>
        forallb
          (fun q => Z.eqb p q || negb (Z.eqb (p mod q) 0))
          ([2; 3; 5; 7; 11; 13; 17; 19; 23; 29; 31; 37; 41; 43; 47;
           53; 59; 61; 67; 71; 73; 79; 83; 89; 97; 101; 103; 107; 109;
           113; 127; 131; 137; 139; 149; 151; 157; 163; 167; 173]%Z : list Z))
      (map Z.of_nat (seq 0 31624)))).
  { intros p Hin. apply bounded_primes_complete__sieve_construction.
    - apply (proj1 (Hchar p)) in Hin. lia.
    - apply (proj1 (Hchar p)) in Hin. tauto. }
  pose proof (@NoDup_incl_length Z primes _ Hnodup Hincl) as Hlength.
  pose proof bounded_primes_length__sieve_construction as Hboundlen.
  assert (Hplen : (length primes < 3999)%nat) by lia.
  apply Nat2Z.inj_lt in Hplen.
  change (Z.of_nat (length primes) < 3999) in Hplen.
  rewrite Zlength_correct. lia.
Qed.
Lemma prime_mark_table2_replace_step__sieve_marking_exits :
  forall factor next primes flags,
    next <= 31623 ->
    PrimeMarkTable2 factor next primes flags ->
    PrimeMarkTable2 factor (next + factor) primes (replace_Znth next 1 flags).
Proof.
  intros factor next primes flags Hnext Hmark.
  unfold PrimeMarkTable2 in *.
  destruct Hmark as
      [Hfactor [Hstart [Hdivnext [Hlen [Hnodup [Hall [Hinc [Hprimes Hflags]]]]]]]].
  split; [exact Hfactor |].
  split; [nia |].
  split; [apply Z.divide_add_r; [exact Hdivnext | apply Z.divide_refl] |].
  split; [rewrite Zlength_replace_Znth; exact Hlen |].
  split; [exact Hnodup |].
  split; [exact Hall |].
  split; [exact Hinc |].
  split; [exact Hprimes |].
  intros k Hk.
  destruct (Z.eq_dec k next) as [-> | Hneq].
  - rewrite Znth_replace_Znth_Same by lia.
    split; intros Hcontra.
    + discriminate.
    + exfalso; apply Hcontra.
      right; repeat split; try assumption; nia.
  - rewrite Znth_replace_Znth_Diff by lia.
    rewrite Hflags by assumption.
    assert (Hequiv :
      ProperMarkedBefore factor k \/
        (factor | k) /\ factor * factor <= k < next + factor <->
      ProperMarkedBefore factor k \/
        (factor | k) /\ factor * factor <= k < next).
    { split.
      - intros [Hproper | [Hdivk [Hlo Hhi]]].
        + left; exact Hproper.
        + destruct (Z_lt_ge_dec k next) as [Hlt | Hge].
          * right; repeat split; assumption.
          * exfalso.
            assert (Hdiffdiv : (factor | k - next)).
            { apply Z.divide_sub_r; assumption. }
            destruct Hdiffdiv as [q Hq].
            assert (q = 0) by nia.
            subst q; nia.
      - intros [Hproper | Hinterval].
        + left; exact Hproper.
        + right; destruct Hinterval as [Hd [Hl Hr]].
          repeat split; try assumption; nia. }
    rewrite Hequiv; reflexivity.
Qed.
Lemma prime_mark_table2_finish__sieve_marking_exits :
  forall factor next primes flags,
    31623 < next ->
    PrimeMarkTable2 factor next primes flags ->
    PrimePrefixTable2 (factor + 1) primes flags.
Proof.
  intros factor next primes flags Hnext Hmark.
  unfold PrimeMarkTable2 in Hmark.
  unfold PrimePrefixTable2.
  destruct Hmark as
      [Hfactor [Hstart [Hdivnext [Hlen [Hnodup [Hall [Hinc [Hprimes Hflags]]]]]]]].
  split; [nia |].
  split; [exact Hlen |].
  split; [exact Hnodup |].
  split; [exact Hall |].
  split; [exact Hinc |].
  split; [exact Hprimes |].
  intros k Hk.
  rewrite Hflags by assumption.
  assert (Hequiv :
    ProperMarkedBefore (factor + 1) k <->
    ProperMarkedBefore factor k \/
      (factor | k) /\ factor * factor <= k < next).
  { split.
    - intros [d [[Hdlo Hdhi] [Hdk Hdivd]]].
      destruct (Z_lt_ge_dec d factor) as [Hdf | Hdf].
      + left. exists d; repeat split; assumption.
      + assert (d = factor) by nia; subst d.
        destruct (Z_le_gt_dec (factor * factor) k) as [Hsq | Hsq].
        * right; repeat split; try assumption; nia.
        * left.
          destruct Hdivd as [q Hq].
          exists q.
          repeat split.
          -- nia.
          -- nia.
          -- nia.
          -- exists factor; nia.
    - intros [Hproper | [Hdiv [Hlo Hhi]]].
      + destruct Hproper as [d [[Hdlo Hdhi] [Hdk Hdivd]]].
        exists d; repeat split; try assumption; nia.
      + exists factor; repeat split; try assumption; nia. }
  rewrite Hequiv; reflexivity.
Qed.
Lemma prime_prefix_table2_complete__sieve_marking_exits :
  forall primes flags,
    PrimePrefixTable2 31624 primes flags ->
    CompletePrimeTable primes.
Proof.
  intros primes flags Hprefix.
  unfold PrimePrefixTable2 in Hprefix.
  unfold CompletePrimeTable.
  destruct Hprefix as
      [Hbound [Hlen [Hnodup [Hall [Hinc [Hprimes Hflags]]]]]].
  split; [exact Hnodup |].
  split; [exact Hall |].
  split; [exact Hinc |].
  intros p; rewrite Hprimes.
  assert (p < 31624 <-> p <= 31623) by lia.
  tauto.
Qed.
Lemma prime_factor_bag_prefix_zero__sieve_marking_exits :
  forall a, PrimeFactorBagPrefix a 0 nil.
Proof.
  intros a.
  unfold PrimeFactorBagPrefix.
  split; [split; [lia | apply Zlength_nonneg] |].
  split; [constructor |].
  intros p Hp; reflexivity.
Qed.
Lemma complete_prime_table_Znth_ge_2__factor_scan_divide :
  forall primes tested,
    CompletePrimeTable primes ->
    0 <= tested < Zlength primes ->
    2 <= Znth tested primes 0.
Proof.
  intros primes tested Htable Htested.
  destruct Htable as (_ & Hprimes & _ & _).
  pose proof
    (proj1 (Forall_Znth prime 0 primes) Hprimes tested Htested)
    as Hprime.
  apply prime_ge_2; exact Hprime.
Qed.
Lemma complete_prime_table_mod_zero_divides__factor_scan_divide :
  forall primes tested rem,
    CompletePrimeTable primes ->
    0 <= tested < Zlength primes ->
    Z.rem rem (Znth tested primes 0) = 0 ->
    (Znth tested primes 0 | rem).
Proof.
  intros primes tested rem Htable Htested Hmod.
  apply (proj1
    (Z.rem_divide rem (Znth tested primes 0) ltac:(
      pose proof
        (complete_prime_table_Znth_ge_2__factor_scan_divide
          primes tested Htable Htested);
      lia))).
  exact Hmod.
Qed.
Lemma factor_scan_state2_initial__factor_scan_divide :
  forall a primes index factors,
    PrimeFactorBagPrefix a index factors ->
    0 <= index < Zlength a ->
    1 <= Znth index a 0 ->
    FactorScanState2 a primes index 0 (Znth index a 0) factors.
Proof.
  intros a primes index factors Hprefix Hindex Hpositive.
  assert (Hdefault : Znth index a 0 = Znth index a 1).
  { apply Znth_indep. lia. }
  unfold FactorScanState2.
  exists factors, nil.
  split; [rewrite app_nil_r; reflexivity |].
  split; [exact Hprefix |].
  split; [exact Hindex |].
  split; [split; [lia | apply Zlength_nonneg] |].
  split; [rewrite <- Hdefault; lia |].
  split; [rewrite <- Hdefault; apply Z.divide_refl |].
  split; [constructor |].
  split; [constructor |].
  split.
  - intros p Hprime. simpl. tauto.
  - split.
    + intros p Hin. simpl in Hin. contradiction.
    + unfold ResidualPrimeCoverage.
      intros p Hprime. simpl. rewrite Hdefault. tauto.
Qed.
Lemma factor_scan_state2_append_divisor__factor_scan_divide :
  forall a primes index tested rem factors,
    CompletePrimeTable primes ->
    FactorScanState2 a primes index tested rem factors ->
    0 <= tested < Zlength primes ->
    (Znth tested primes 0 | rem) ->
    FactorDivideState2 a primes index tested rem
      (factors ++ [Znth tested primes 0]).
Proof.
  intros a primes index tested rem factors Htable Hscan Htested Hdivides.
  destruct Htable as (_ & Hprimes & _ & _).
  pose proof
    (proj1 (Forall_Znth prime 0 primes) Hprimes tested Htested)
    as Hprime.
  destruct Hscan as
    (done & picked & Hfactors & Hprefix & Hindex & _ & Hrem_bounds &
     Hrem_divides & Hnodup & Hpicked_primes & Hpicked & Hprior & Hcoverage).
  unfold FactorDivideState2.
  exists done, picked, (Znth tested primes 0).
  split; [rewrite Hfactors, app_assoc; reflexivity |].
  split; [exact Hprefix |].
  split; [exact Hindex |].
  split; [exact Htested |].
  split; [reflexivity |].
  split; [exact Hprime |].
  split; [eapply Z.divide_trans; eauto |].
  split; [exact Hrem_bounds |].
  split; [exact Hrem_divides |].
  split; [exact Hnodup |].
  split; [exact Hpicked_primes |].
  split; [exact Hpicked |].
  split; [exact Hprior |].
  unfold ResidualPrimeCoverage in Hcoverage |- *.
  intros q Hq.
  rewrite Hcoverage by exact Hq.
  split.
  - intros [Hin | Hqrem].
    + left. apply in_or_app. left. exact Hin.
    + right. exact Hqrem.
  - intros [Hin | Hqrem].
    + apply in_app_or in Hin.
      destruct Hin as [Hin | [Heq | []]].
      * left. exact Hin.
      * right. subst q. exact Hdivides.
    + right. exact Hqrem.
Qed.
Lemma factor_divide_state2_reduce__factor_scan_divide :
  forall a primes index tested rem factors,
    FactorDivideState2 a primes index tested rem factors ->
    (Znth tested primes 0 | rem) ->
    FactorDivideState2 a primes index tested
      (Z.quot rem (Znth tested primes 0)) factors.
Proof.
  intros a primes index tested rem factors Hstate Hcurrent_divides.
  destruct Hstate as
    (done & picked & p & Hfactors & Hprefix & Hindex & Htested & Hp &
     Hprime & Hp_original & Hrem_bounds & Hrem_original & Hnodup &
     Hpicked_primes & Hpicked & Hprior & Hcoverage).
  subst p.
  pose proof (prime_ge_2 _ Hprime) as Hprime_positive.
  assert (Hmod : Z.rem rem (Znth tested primes 0) = 0).
  { apply (proj2
      (Z.rem_divide rem (Znth tested primes 0) ltac:(lia))).
    exact Hcurrent_divides. }
  assert (Hrem_eq :
      rem = Znth tested primes 0 *
        (Z.quot rem (Znth tested primes 0))).
  { apply (proj2 (Z_quot_exact_full rem (Znth tested primes 0))).
    exact Hmod. }
  assert (Hquot_positive :
      1 <= Z.quot rem (Znth tested primes 0)) by nia.
  assert (Hquot_le :
      Z.quot rem (Znth tested primes 0) <= rem) by nia.
  assert (Hquot_divides_rem :
      (Z.quot rem (Znth tested primes 0) | rem)).
  { exists (Znth tested primes 0). nia. }
  unfold FactorDivideState2.
  exists done, picked, (Znth tested primes 0).
  split; [exact Hfactors |].
  split; [exact Hprefix |].
  split; [exact Hindex |].
  split; [exact Htested |].
  split; [reflexivity |].
  split; [exact Hprime |].
  split; [exact Hp_original |].
  split; [lia |].
  split; [eapply Z.divide_trans; eauto |].
  split; [exact Hnodup |].
  split; [exact Hpicked_primes |].
  split; [exact Hpicked |].
  split.
  - intros q Hin Hqdivides.
    apply (Hprior q Hin).
    eapply Z.divide_trans; eauto.
  - unfold ResidualPrimeCoverage in Hcoverage |- *.
    intros q Hq.
    rewrite Hcoverage by exact Hq.
    split.
    + intros [Hin | Hqrem].
      * left. exact Hin.
      * rewrite Hrem_eq in Hqrem.
        destruct
          (prime_mult q Hq (Znth tested primes 0)
             (Z.quot rem (Znth tested primes 0)) Hqrem)
          as [Hqcurrent | Hqquot].
        -- left.
           apply in_or_app. right. simpl.
           pose proof
             (prime_divisors (Znth tested primes 0) Hprime q Hqcurrent)
             as Hcases.
           pose proof (prime_ge_2 q Hq) as Hqpositive.
           destruct Hcases as [Hnegone | [Hone | [Heq | Hneg]]];
             try lia.
        -- right. exact Hqquot.
    + intros [Hin | Hqquot].
      * left. exact Hin.
      * right. eapply Z.divide_trans; eauto.
Qed.
Lemma NoDup_firstn__factor_scan_advance :
  forall (A : Type) (n : nat) (l : list A),
    NoDup l -> NoDup (firstn n l).
Proof.
  intros A n. induction n as [|n IH]; intros l Hnodup; simpl.
  - constructor.
  - destruct l as [|a l]; [constructor|].
    inversion Hnodup as [|? ? Hnot Hnd]; subst.
    constructor.
    + intros Hin. apply Hnot.
      rewrite <- (firstn_skipn n l). apply in_or_app. left. exact Hin.
    + apply IH. exact Hnd.
Qed.
Lemma prime_floor_29__factor_scan_advance :
  forall p, prime p -> 24 <= p -> 29 <= p.
Proof.
  intros p Hp Hbound.
  destruct (Z.eq_dec p 24) as [Heq|Hneq24].
  { subst p. pose proof (prime_divisors 24 Hp 2 ltac:(exists 12; lia)); lia. }
  destruct (Z.eq_dec p 25) as [Heq|Hneq25].
  { subst p. pose proof (prime_divisors 25 Hp 5 ltac:(exists 5; lia)); lia. }
  destruct (Z.eq_dec p 26) as [Heq|Hneq26].
  { subst p. pose proof (prime_divisors 26 Hp 2 ltac:(exists 13; lia)); lia. }
  destruct (Z.eq_dec p 27) as [Heq|Hneq27].
  { subst p. pose proof (prime_divisors 27 Hp 3 ltac:(exists 9; lia)); lia. }
  destruct (Z.eq_dec p 28) as [Heq|Hneq28].
  { subst p. pose proof (prime_divisors 28 Hp 2 ltac:(exists 14; lia)); lia. }
  lia.
Qed.
Lemma prime_floor_5__factor_scan_advance :
  forall p, prime p -> 4 <= p -> 5 <= p.
Proof.
  intros p Hp Hbound.
  destruct (Z.eq_dec p 4) as [Heq|Hneq].
  { subst p. pose proof (prime_divisors 4 Hp 2 ltac:(exists 2; lia)); lia. }
  lia.
Qed.
Lemma firstn_Z_succ__factor_scan_advance :
  forall (A : Type) (l : list A) (j : Z) (d : A),
    0 <= j < Zlength l ->
    firstn (Z.to_nat (j + 1)) l =
      firstn (Z.to_nat j) l ++ [Znth j l d].
Proof.
  intros A l j d Hj.
  replace (j + 1) with (Z.succ j) by lia.
  rewrite (Z2Nat.inj_succ j) by lia.
  change (firstn (S (Z.to_nat j)) l =
    firstn (Z.to_nat j) l ++ [nth (Z.to_nat j) l d]).
  apply app_inv_tail with (l := skipn (S (Z.to_nat j)) l).
  rewrite firstn_skipn.
  symmetry.
  rewrite <- app_assoc. simpl.
  apply firstn_skipn_middle.
  apply nth_error_nth'.
  rewrite Zlength_correct in Hj. lia.
Qed.
Lemma NoDup_snoc_notin__factor_scan_advance :
  forall (A : Type) (l : list A) x,
    NoDup (l ++ [x]) -> ~ In x l.
Proof.
  intros A l. induction l as [|a l IH]; intros x Hnodup; simpl; [tauto|].
  inversion Hnodup as [|? ? Hnot Htail]; subst.
  intros [Heq|Hin].
  - subst a. apply Hnot. apply in_or_app. right. simpl; auto.
  - apply (IH x Htail). exact Hin.
Qed.
Lemma factor_divide2_to_scan2_next__factor_scan_advance :
  forall a primes index tested rem factors,
    CompletePrimeTable primes ->
    FactorDivideState2 a primes index tested rem factors ->
    Z.rem rem (Znth tested primes 0) <> 0 ->
    FactorScanState2 a primes index (tested + 1) rem factors.
Proof.
  intros a primes index tested rem factors Htable Hstate Hnondiv.
  destruct Htable as [Hprimes_nodup [Htable_primes [Hinc Hcomplete]]].
  destruct Hstate as
    (done & picked & p & Hfactors & Hbag & Hindex & Htested & Hp & Hprime &
     Hp_original & Hrem_bounds & Hrem_original & Hnodup & Hpicked_primes &
     Hpicked & Hprior & Hcoverage).
  subst p.
  pose proof (firstn_Z_succ__factor_scan_advance
    Z primes tested 0 Htested) as Hfirstn.
  assert (Hprefix_nodup :
      NoDup (firstn (Z.to_nat tested) primes ++ [Znth tested primes 0])).
  { rewrite <- Hfirstn. apply NoDup_firstn__factor_scan_advance.
    exact Hprimes_nodup. }
  assert (Hcurrent_not_prefix :
      ~ In (Znth tested primes 0) (firstn (Z.to_nat tested) primes)).
  { apply NoDup_snoc_notin__factor_scan_advance. exact Hprefix_nodup. }
  assert (Hcurrent_not_picked : ~ In (Znth tested primes 0) picked).
  { intros Hin. apply (proj1 (Hpicked _ Hprime)) in Hin. tauto. }
  assert (Hcurrent_not_rem : ~ (Znth tested primes 0 | rem)).
  { intros Hdiv. apply Hnondiv.
    apply (proj2 (Z.rem_divide rem (Znth tested primes 0)
                    ltac:(pose proof (prime_ge_2 _ Hprime); lia))).
    exact Hdiv. }
  unfold FactorScanState2.
  exists done, (picked ++ [Znth tested primes 0]).
  split; [rewrite Hfactors, app_assoc; reflexivity|].
  split; [exact Hbag|].
  split; [exact Hindex|].
  split; [lia|].
  split; [exact Hrem_bounds|].
  split; [exact Hrem_original|].
  split.
  - apply NoDup_app.
    + exact Hnodup.
    + constructor; [simpl; tauto|constructor].
    + intros q Hq Hsingle. simpl in Hsingle.
      destruct Hsingle as [Heq|[]]. subst q. contradiction.
  - split.
    + apply Forall_app. split; [exact Hpicked_primes|constructor; auto].
    + split.
      * intros q Hqprime. rewrite in_app_iff, Hfirstn, in_app_iff.
        simpl. specialize (Hpicked q Hqprime). split.
        -- intros [Hin|[Heq|[]]].
           ++ apply Hpicked in Hin. destruct Hin as [Hin Hdiv].
              split; [left; exact Hin|exact Hdiv].
           ++ subst q. split; [right; left; reflexivity|exact Hp_original].
        -- intros [[Hin|[Heq|[]]] Hdiv].
           ++ left. apply Hpicked. split; assumption.
           ++ subst q. right; left; reflexivity.
      * split.
        -- intros q Hq. rewrite Hfirstn, in_app_iff in Hq.
           simpl in Hq. destruct Hq as [Hq|[Heq|[]]].
           ++ apply Hprior. exact Hq.
           ++ subst q. exact Hcurrent_not_rem.
        -- exact Hcoverage.
Qed.
Lemma factor_scan2_to_scan2_next__factor_scan_advance :
  forall a primes index tested rem factors,
    CompletePrimeTable primes ->
    FactorScanState2 a primes index tested rem factors ->
    0 <= tested < Zlength primes ->
    Z.rem rem (Znth tested primes 0) <> 0 ->
    FactorScanState2 a primes index (tested + 1) rem factors.
Proof.
  intros a primes index tested rem factors Htable Hstate Htested Hnondiv.
  destruct Htable as [Hprimes_nodup [Htable_primes [Hinc Hcomplete]]].
  destruct Hstate as
    (done & picked & Hfactors & Hbag & Hindex & Htested_old & Hrem_bounds &
     Hrem_original & Hnodup & Hpicked_primes & Hpicked & Hprior & Hcoverage).
  assert (Hcurrent_in : In (Znth tested primes 0) primes).
  { unfold Znth. apply nth_In. rewrite Zlength_correct in Htested. lia. }
  pose proof (proj1 (Hcomplete (Znth tested primes 0)) Hcurrent_in)
    as [_ Hprime].
  pose proof (firstn_Z_succ__factor_scan_advance
    Z primes tested 0 Htested) as Hfirstn.
  assert (Hprefix_nodup :
      NoDup (firstn (Z.to_nat tested) primes ++ [Znth tested primes 0])).
  { rewrite <- Hfirstn. apply NoDup_firstn__factor_scan_advance.
    exact Hprimes_nodup. }
  assert (Hcurrent_not_prefix :
      ~ In (Znth tested primes 0) (firstn (Z.to_nat tested) primes)).
  { apply NoDup_snoc_notin__factor_scan_advance. exact Hprefix_nodup. }
  assert (Hcurrent_not_picked : ~ In (Znth tested primes 0) picked).
  { intros Hin. apply (proj1 (Hpicked _ Hprime)) in Hin. tauto. }
  assert (Hcurrent_not_rem : ~ (Znth tested primes 0 | rem)).
  { intros Hdiv. apply Hnondiv.
    apply (proj2 (Z.rem_divide rem (Znth tested primes 0)
                    ltac:(pose proof (prime_ge_2 _ Hprime); lia))).
    exact Hdiv. }
  assert (Hcurrent_not_original : ~ (Znth tested primes 0 | Znth index a 1)).
  { intros Hdiv. apply (proj1 (Hcoverage _ Hprime)) in Hdiv.
    tauto. }
  unfold FactorScanState2.
  exists done, picked.
  split; [exact Hfactors|].
  split; [exact Hbag|].
  split; [exact Hindex|].
  split; [lia|].
  split; [exact Hrem_bounds|].
  split; [exact Hrem_original|].
  split; [exact Hnodup|].
  split; [exact Hpicked_primes|].
  split.
  - intros q Hqprime. rewrite Hfirstn, in_app_iff. simpl.
    specialize (Hpicked q Hqprime).
    destruct (Z.eq_dec q (Znth tested primes 0)) as [Heq|Hneq].
    + subst q. rewrite Hpicked. tauto.
    + assert (Hneq' : Znth tested primes 0 <> q) by congruence.
      rewrite Hpicked. tauto.
  - split.
    + intros q Hq. rewrite Hfirstn, in_app_iff in Hq.
      simpl in Hq. destruct Hq as [Hq|[Heq|[]]].
      * apply Hprior. exact Hq.
      * subst q. exact Hcurrent_not_rem.
    + exact Hcoverage.
Qed.
Lemma prime_floor_7__factor_scan_advance :
  forall p, prime p -> 6 <= p -> 7 <= p.
Proof.
  intros p Hp Hbound.
  destruct (Z.eq_dec p 6) as [Heq|Hneq].
  { subst p. pose proof (prime_divisors 6 Hp 2 ltac:(exists 3; lia)); lia. }
  lia.
Qed.
Lemma prime_floor_11__factor_scan_advance :
  forall p, prime p -> 8 <= p -> 11 <= p.
Proof.
  intros p Hp Hbound.
  destruct (Z.eq_dec p 8) as [Heq|Hneq8].
  { subst p. pose proof (prime_divisors 8 Hp 2 ltac:(exists 4; lia)); lia. }
  destruct (Z.eq_dec p 9) as [Heq|Hneq9].
  { subst p. pose proof (prime_divisors 9 Hp 3 ltac:(exists 3; lia)); lia. }
  destruct (Z.eq_dec p 10) as [Heq|Hneq10].
  { subst p. pose proof (prime_divisors 10 Hp 2 ltac:(exists 5; lia)); lia. }
  lia.
Qed.
Lemma prime_floor_13__factor_scan_advance :
  forall p, prime p -> 12 <= p -> 13 <= p.
Proof.
  intros p Hp Hbound.
  destruct (Z.eq_dec p 12) as [Heq|Hneq].
  { subst p. pose proof (prime_divisors 12 Hp 2 ltac:(exists 6; lia)); lia. }
  lia.
Qed.
Lemma prime_floor_17__factor_scan_advance :
  forall p, prime p -> 14 <= p -> 17 <= p.
Proof.
  intros p Hp Hbound.
  destruct (Z.eq_dec p 14) as [Heq|Hneq14].
  { subst p. pose proof (prime_divisors 14 Hp 2 ltac:(exists 7; lia)); lia. }
  destruct (Z.eq_dec p 15) as [Heq|Hneq15].
  { subst p. pose proof (prime_divisors 15 Hp 3 ltac:(exists 5; lia)); lia. }
  destruct (Z.eq_dec p 16) as [Heq|Hneq16].
  { subst p. pose proof (prime_divisors 16 Hp 2 ltac:(exists 8; lia)); lia. }
  lia.
Qed.
Lemma prime_floor_19__factor_scan_advance :
  forall p, prime p -> 18 <= p -> 19 <= p.
Proof.
  intros p Hp Hbound.
  destruct (Z.eq_dec p 18) as [Heq|Hneq].
  { subst p. pose proof (prime_divisors 18 Hp 2 ltac:(exists 9; lia)); lia. }
  lia.
Qed.
Lemma prime_floor_23__factor_scan_advance :
  forall p, prime p -> 20 <= p -> 23 <= p.
Proof.
  intros p Hp Hbound.
  destruct (Z.eq_dec p 20) as [Heq|Hneq20].
  { subst p. pose proof (prime_divisors 20 Hp 2 ltac:(exists 10; lia)); lia. }
  destruct (Z.eq_dec p 21) as [Heq|Hneq21].
  { subst p. pose proof (prime_divisors 21 Hp 3 ltac:(exists 7; lia)); lia. }
  destruct (Z.eq_dec p 22) as [Heq|Hneq22].
  { subst p. pose proof (prime_divisors 22 Hp 2 ltac:(exists 11; lia)); lia. }
  lia.
Qed.
Lemma prime_not_divide_distinct_prime__factor_scan_advance :
  forall p q, prime p -> prime q -> p <> q -> ~ (p | q).
Proof.
  intros p q Hp Hq Hneq Hdiv.
  pose proof (prime_divisors q Hq p Hdiv) as Hcases.
  pose proof (prime_ge_2 p Hp).
  pose proof (prime_ge_2 q Hq).
  lia.
Qed.
Lemma prime_rel_prime_product__factor_scan_advance :
  forall p l,
    prime p -> Forall prime l -> ~ In p l ->
    rel_prime p (fold_right Z.mul 1 l).
Proof.
  intros p l Hp Hprimes Hnotin.
  induction l as [|q l IH].
  - simpl. apply rel_prime_sym. apply rel_prime_1.
  - inversion Hprimes as [|? ? Hq Htail]; subst.
    simpl in Hnotin. apply Decidable.not_or in Hnotin.
    destruct Hnotin as [Hpq Hnotin].
    simpl. apply rel_prime_mult.
    + apply prime_rel_prime; [exact Hp|].
      apply prime_not_divide_distinct_prime__factor_scan_advance; auto.
    + apply IH; auto.
Qed.
Lemma product_distinct_primes_divides__factor_scan_advance :
  forall l x,
    NoDup l -> Forall prime l ->
    (forall p, In p l -> (p | x)) ->
    (fold_right Z.mul 1 l | x).
Proof.
  intros l x Hnodup Hprimes Hall.
  induction l as [|p l IH].
  - simpl. apply Z.divide_1_l.
  - inversion Hnodup as [|? ? Hnotin Hnodup']; subst.
    inversion Hprimes as [|? ? Hp Hprimes']; subst.
    simpl.
    assert (Hrest : (fold_right Z.mul 1 l | x)).
    { apply IH; auto. intros q Hq. apply Hall. simpl; auto. }
    assert (Hpdiv : (p | x)) by (apply Hall; simpl; auto).
    assert (Hrel : rel_prime p (fold_right Z.mul 1 l)).
    { apply prime_rel_prime_product__factor_scan_advance; auto. }
    destruct Hrest as [k Hx].
    rewrite Hx in Hpdiv.
    rewrite Z.mul_comm in Hpdiv.
    pose proof (Gauss p (fold_right Z.mul 1 l) k Hpdiv Hrel) as Hpk.
    destruct Hpk as [q Hq].
    exists q. rewrite Hx, Hq. ring.
Qed.
Lemma increasing_nodup_prime_ten_product__factor_scan_advance :
  forall l,
    increasing l -> NoDup l -> Forall prime l ->
    (10 <= length l)%nat ->
    1000000000 < fold_right Z.mul 1 (firstn 10 l).
Proof.
  intros l Hinc Hnodup Hprimes Hlength.
  destruct l as [|p0 [|p1 [|p2 [|p3 [|p4 [|p5 [|p6 [|p7 [|p8 [|p9 rest]]]]]]]]]];
    simpl in Hlength; try lia.
  simpl in Hinc, Hnodup, Hprimes |- *.
  destruct Hinc as [H01 [H12 [H23 [H34 [H45 [H56 [H67 [H78 [H89 Hinc]]]]]]]]].
  inversion Hnodup as [|? ? Hn0 Hnd1]; subst.
  inversion Hnd1 as [|? ? Hn1 Hnd2]; subst.
  inversion Hnd2 as [|? ? Hn2 Hnd3]; subst.
  inversion Hnd3 as [|? ? Hn3 Hnd4]; subst.
  inversion Hnd4 as [|? ? Hn4 Hnd5]; subst.
  inversion Hnd5 as [|? ? Hn5 Hnd6]; subst.
  inversion Hnd6 as [|? ? Hn6 Hnd7]; subst.
  inversion Hnd7 as [|? ? Hn7 Hnd8]; subst.
  inversion Hnd8 as [|? ? Hn8 Hnd9]; subst.
  inversion Hprimes as [|? ? Hp0 Hps1]; subst.
  inversion Hps1 as [|? ? Hp1 Hps2]; subst.
  inversion Hps2 as [|? ? Hp2 Hps3]; subst.
  inversion Hps3 as [|? ? Hp3 Hps4]; subst.
  inversion Hps4 as [|? ? Hp4 Hps5]; subst.
  inversion Hps5 as [|? ? Hp5 Hps6]; subst.
  inversion Hps6 as [|? ? Hp6 Hps7]; subst.
  inversion Hps7 as [|? ? Hp7 Hps8]; subst.
  inversion Hps8 as [|? ? Hp8 Hps9]; subst.
  inversion Hps9 as [|? ? Hp9 Hps]; subst.
  assert (H01' : p0 < p1) by (simpl in Hn0; intuition).
  assert (H12' : p1 < p2) by (simpl in Hn1; intuition).
  assert (H23' : p2 < p3) by (simpl in Hn2; intuition).
  assert (H34' : p3 < p4) by (simpl in Hn3; intuition).
  assert (H45' : p4 < p5) by (simpl in Hn4; intuition).
  assert (H56' : p5 < p6) by (simpl in Hn5; intuition).
  assert (H67' : p6 < p7) by (simpl in Hn6; intuition).
  assert (H78' : p7 < p8) by (simpl in Hn7; intuition).
  assert (H89' : p8 < p9) by (simpl in Hn8; intuition).
  pose proof (prime_ge_2 p0 Hp0) as Hp0b.
  assert (Hp1b : 3 <= p1) by lia.
  assert (Hp2b : 5 <= p2).
  { apply prime_floor_5__factor_scan_advance; auto; lia. }
  assert (Hp3b : 7 <= p3).
  { apply prime_floor_7__factor_scan_advance; auto; lia. }
  assert (Hp4b : 11 <= p4).
  { apply prime_floor_11__factor_scan_advance; auto; lia. }
  assert (Hp5b : 13 <= p5).
  { apply prime_floor_13__factor_scan_advance; auto; lia. }
  assert (Hp6b : 17 <= p6).
  { apply prime_floor_17__factor_scan_advance; auto; lia. }
  assert (Hp7b : 19 <= p7).
  { apply prime_floor_19__factor_scan_advance; auto; lia. }
  assert (Hp8b : 23 <= p8).
  { apply prime_floor_23__factor_scan_advance; auto; lia. }
  assert (Hp9b : 29 <= p9).
  { apply prime_floor_29__factor_scan_advance; auto; lia. }
  nia.
Qed.
Lemma increasing_prime_divisors_length__factor_scan_advance :
  forall l x,
    increasing l -> NoDup l -> Forall prime l ->
    (forall p, In p l -> (p | x)) ->
    1 <= x <= 1000000000 ->
    (length l <= 9)%nat.
Proof.
  intros l x Hinc Hnodup Hprimes Hdiv Hx.
  destruct (le_lt_dec 10 (length l)) as [Hten|Hshort]; [|lia].
  pose proof (increasing_nodup_prime_ten_product__factor_scan_advance
                l Hinc Hnodup Hprimes Hten) as Hprodlarge.
  assert (Hfirst_nodup : NoDup (firstn 10 l)).
  { apply NoDup_firstn__factor_scan_advance. exact Hnodup. }
  assert (Hfirst_primes : Forall prime (firstn 10 l)).
  { rewrite Forall_forall in Hprimes |- *.
    intros p Hp. apply Hprimes.
    rewrite <- (firstn_skipn 10 l). apply in_or_app. left. exact Hp. }
  assert (Hfirst_div : forall p, In p (firstn 10 l) -> (p | x)).
  { intros p Hp. apply Hdiv.
    rewrite <- (firstn_skipn 10 l). apply in_or_app. left. exact Hp. }
  pose proof (product_distinct_primes_divides__factor_scan_advance
                (firstn 10 l) x Hfirst_nodup Hfirst_primes Hfirst_div)
    as [q Hq].
  assert (Hproduct_positive : 0 < fold_right Z.mul 1 (firstn 10 l)) by lia.
  assert (Hqpositive : 1 <= q) by nia.
  nia.
Qed.
Lemma sum_count_occ_notin__factor_scan_advance :
  forall a u l,
    ~ In a u ->
    fold_right Nat.add 0%nat (map (count_occ Z.eq_dec (a :: l)) u) =
    fold_right Nat.add 0%nat (map (count_occ Z.eq_dec l) u).
Proof.
  intros a u. induction u as [|b u IH]; intros l Hnot; simpl; [reflexivity|].
  assert (Hab : a <> b) by (intro Heq; apply Hnot; subst; simpl; auto).
  assert (Hnotu : ~ In a u) by (intro Hin; apply Hnot; simpl; auto).
  destruct (Z.eq_dec a b); [contradiction|].
  f_equal. apply IH. exact Hnotu.
Qed.
Lemma sum_count_occ_cons__factor_scan_advance :
  forall a u l,
    NoDup u -> In a u ->
    fold_right Nat.add 0%nat (map (count_occ Z.eq_dec (a :: l)) u) =
    S (fold_right Nat.add 0%nat (map (count_occ Z.eq_dec l) u)).
Proof.
  intros a u. induction u as [|b u IH]; intros l Hnodup Hin; simpl in Hin |- *.
  - contradiction.
  - inversion Hnodup as [|? ? Hbnot Hnd]; subst.
    destruct Hin as [Heq|Hin].
    + subst b. destruct (Z.eq_dec a a); [|contradiction].
      pose proof (sum_count_occ_notin__factor_scan_advance a u l Hbnot) as Htail.
      simpl in Htail.
      rewrite Htail. reflexivity.
    + assert (Hab : a <> b) by (intro Heq; subst; contradiction).
      destruct (Z.eq_dec a b); [contradiction|].
      pose proof (IH l Hnd Hin) as Htail. simpl in Htail.
      rewrite Htail. apply Nat.add_succ_r.
Qed.
Lemma sum_count_occ_nil__factor_scan_advance :
  forall u,
    fold_right Nat.add 0%nat (map (count_occ Z.eq_dec []) u) = 0%nat.
Proof.
  induction u; simpl; auto.
Qed.
Lemma length_as_sum_count_occ__factor_scan_advance :
  forall l u,
    NoDup u ->
    (forall a, In a l -> In a u) ->
    length l = fold_right Nat.add 0%nat (map (count_occ Z.eq_dec l) u).
Proof.
  intros l. induction l as [|a l IH]; intros u Hnodup Hcover.
  - simpl. symmetry. apply sum_count_occ_nil__factor_scan_advance.
  - rewrite sum_count_occ_cons__factor_scan_advance.
    + simpl. f_equal. apply IH; [exact Hnodup|].
      intros q Hq. apply Hcover. simpl; auto.
    + exact Hnodup.
    + apply Hcover. simpl; auto.
Qed.
Lemma sum_filter_cons__factor_scan_advance :
  forall (u vals : list Z) (x : Z) (f : Z -> Z -> bool),
    fold_right Nat.add 0%nat
      (map (fun p => length (filter (fun y => f p y) (x :: vals))) u) =
    (length (filter (fun p => f p x) u) +
     fold_right Nat.add 0%nat
       (map (fun p => length (filter (fun y => f p y) vals)) u))%nat.
Proof.
  intros u. induction u as [|p u IH]; intros vals x f; simpl; [reflexivity|].
  destruct (f p x); simpl;
    pose proof (IH vals x f) as Htail; simpl in Htail; rewrite Htail; lia.
Qed.
Lemma transpose_filter_counts__factor_scan_advance :
  forall (u vals : list Z) (f : Z -> Z -> bool),
    fold_right Nat.add 0%nat
      (map (fun p => length (filter (fun x => f p x) vals)) u) =
    fold_right Nat.add 0%nat
      (map (fun x => length (filter (fun p => f p x) u)) vals).
Proof.
  intros u vals. induction vals as [|x vals IH]; intros f.
  - simpl. induction u; simpl; auto.
  - rewrite sum_filter_cons__factor_scan_advance. simpl.
    rewrite IH. reflexivity.
Qed.
Lemma zdividesb_true_iff__factor_scan_advance :
  forall p x, zdividesb p x = true <-> (p | x).
Proof.
  intros p x. unfold zdividesb. destruct (Zdivide_dec p x) as [Hdiv|Hnot].
  - split; intro; [exact Hdiv|reflexivity].
  - split; intro H; [discriminate|contradiction].
Qed.
Lemma distinct_prime_divisors_length__factor_scan_advance :
  forall l x,
    NoDup l -> Forall prime l ->
    (forall p, In p l -> (p | x)) ->
    1 <= x <= 1000000000 ->
    (length l <= 9)%nat.
Proof.
  intros l x Hnodup Hprimes Hdiv Hx.
  pose proof (sort_list_perm l) as Hperm.
  rewrite (Permutation_length Hperm).
  apply (increasing_prime_divisors_length__factor_scan_advance (sort l) x).
  - apply sort_list_increasing.
  - eapply Permutation_NoDup; [exact Hperm|exact Hnodup].
  - eapply Permutation_Forall; [exact Hperm|exact Hprimes].
  - intros p Hin. apply Hdiv. eapply Permutation_in; [apply Permutation_sym; exact Hperm|exact Hin].
  - exact Hx.
Qed.
Lemma prime_filter_length__factor_scan_advance :
  forall u x,
    NoDup u -> Forall prime u ->
    1 <= x <= 1000000000 ->
    (length (filter (fun p => zdividesb p x) u) <= 9)%nat.
Proof.
  intros u x Hnodup Hprimes Hx.
  apply distinct_prime_divisors_length__factor_scan_advance with (x := x).
  - apply NoDup_filter. exact Hnodup.
  - rewrite Forall_forall in Hprimes |- *.
    intros p Hin. apply filter_In in Hin. apply Hprimes. tauto.
  - intros p Hin. apply filter_In in Hin.
    apply zdividesb_true_iff__factor_scan_advance. tauto.
  - exact Hx.
Qed.
Lemma sum_prime_filter_bound__factor_scan_advance :
  forall vals u,
    Forall (fun x => 1 <= x <= 1000000000) vals ->
    NoDup u -> Forall prime u ->
    (fold_right Nat.add 0%nat
       (map (fun x => length (filter (fun p => zdividesb p x) u)) vals)
     <= length vals * 9)%nat.
Proof.
  intros vals u Hvals Hnodup Hprimes.
  induction Hvals as [|x vals Hx Hvals IH]; simpl; [lia|].
  pose proof (prime_filter_length__factor_scan_advance u x Hnodup Hprimes Hx).
  lia.
Qed.
Lemma sum_counts_to_filters__factor_scan_advance :
  forall u factors vals,
    Forall prime u ->
    (forall p, prime p ->
      Z.of_nat (count_occ Z.eq_dec factors p) =
      Z.of_nat (length (filter (zdividesb p) vals))) ->
    fold_right Nat.add 0%nat (map (count_occ Z.eq_dec factors) u) =
    fold_right Nat.add 0%nat
      (map (fun p => length (filter (zdividesb p) vals)) u).
Proof.
  intros u factors vals Hprimes Hcounts.
  induction Hprimes as [|p u Hp Hprimes IH]; simpl; [reflexivity|].
  f_equal.
  - apply Nat2Z.inj. apply Hcounts. exact Hp.
  - exact IH.
Qed.
Lemma prime_factor_bag_length_bound__factor_scan_advance :
  forall a index factors,
    PrimeFactorBagPrefix a index factors ->
    Forall (fun x => 1 <= x <= 1000000000) a ->
    Zlength factors <= index * 9.
Proof.
  intros a index factors Hbag Ha.
  destruct Hbag as [Hindex [Hfactor_primes Hcounts]].
  set (u := nodup Z.eq_dec factors).
  set (vals := firstn (Z.to_nat index) a).
  assert (Hu_nodup : NoDup u).
  { unfold u. apply NoDup_nodup. }
  assert (Hu_cover : forall p, In p factors -> In p u).
  { intros p Hp. unfold u. rewrite nodup_In. exact Hp. }
  assert (Hu_primes : Forall prime u).
  { rewrite Forall_forall in Hfactor_primes |- *.
    intros p Hp. apply Hfactor_primes.
    unfold u in Hp. rewrite nodup_In in Hp. exact Hp. }
  assert (Hvals_bounds : Forall (fun x => 1 <= x <= 1000000000) vals).
  { rewrite Forall_forall in Ha |- *.
    intros x Hx. apply Ha. unfold vals in Hx.
    rewrite <- (firstn_skipn (Z.to_nat index) a).
    apply in_or_app. left. exact Hx. }
  assert (Hlength_sum :
      length factors =
      fold_right Nat.add 0%nat (map (count_occ Z.eq_dec factors) u)).
  { apply length_as_sum_count_occ__factor_scan_advance; assumption. }
  assert (Hsum_rewrite :
      fold_right Nat.add 0%nat (map (count_occ Z.eq_dec factors) u) =
      fold_right Nat.add 0%nat
        (map (fun p => length (filter (zdividesb p) vals)) u)).
  { apply sum_counts_to_filters__factor_scan_advance; [exact Hu_primes|].
    intros p Hp. unfold vals. apply Hcounts. exact Hp. }
  assert (Hnat : (length factors <= length vals * 9)%nat).
  { rewrite Hlength_sum, Hsum_rewrite.
    change
      (fold_right Nat.add 0%nat
        (map (fun p => length (filter (fun x => zdividesb p x) vals)) u)
       <= length vals * 9)%nat.
    rewrite (transpose_filter_counts__factor_scan_advance
      u vals (fun p x => zdividesb p x)).
    apply sum_prime_filter_bound__factor_scan_advance; assumption. }
  assert (Hindex_nat : (Z.to_nat index <= length a)%nat).
  { apply Nat2Z.inj_le.
    rewrite Z2Nat.id by lia. rewrite <- Zlength_correct. lia. }
  assert (Hvals_length : length vals = Z.to_nat index).
  { unfold vals. rewrite firstn_length, Nat.min_l by exact Hindex_nat.
    reflexivity. }
  apply Nat2Z.inj_le in Hnat.
  rewrite Nat2Z.inj_mul in Hnat.
  rewrite Hvals_length, Z2Nat.id in Hnat by lia.
  rewrite Zlength_correct. exact Hnat.
Qed.
Lemma factor_scan2_capacity_next__factor_scan_advance :
  forall a primes index tested rem factors count,
    CompletePrimeTable primes ->
    FactorScanState2 a primes index tested rem factors ->
    Forall (fun x => 1 <= x <= 1000000000) a ->
    count = Zlength factors ->
    FactorAppendCapacity primes index tested rem count.
Proof.
  intros a primes index tested rem factors count Htable Hstate Ha Hcount.
  destruct Htable as [Hprimes_nodup [Htable_primes [Hinc Hcomplete]]].
  destruct Hstate as
    (done & picked & Hfactors & Hbag & Hindex & Htested & Hrem_bounds &
     Hrem_original & Hpicked_nodup & Hpicked_primes & Hpicked & Hprior &
     Hcoverage).
  unfold FactorAppendCapacity. intros [Htested_strict Hcurrent_rem].
  assert (Hcurrent_in : In (Znth tested primes 0) primes).
  { unfold Znth. apply nth_In. rewrite Zlength_correct in Htested_strict. lia. }
  pose proof (proj1 (Hcomplete (Znth tested primes 0)) Hcurrent_in)
    as [_ Hcurrent_prime].
  assert (Hcurrent_not_picked : ~ In (Znth tested primes 0) picked).
  { intros Hin. apply (proj1 (Hpicked _ Hcurrent_prime)) in Hin.
    destruct Hin as [Hin _]. apply (Hprior _ Hin). exact Hcurrent_rem. }
  assert (Hselected_nodup :
      NoDup (picked ++ [Znth tested primes 0])).
  { apply NoDup_app.
    - exact Hpicked_nodup.
    - constructor; [simpl; tauto|constructor].
    - intros q Hq Hsingle. simpl in Hsingle.
      destruct Hsingle as [Heq|[]]. subst q. contradiction. }
  assert (Hselected_primes :
      Forall prime (picked ++ [Znth tested primes 0])).
  { apply Forall_app. split; [exact Hpicked_primes|constructor; auto]. }
  assert (Hselected_divides :
      forall p, In p (picked ++ [Znth tested primes 0]) ->
        (p | Znth index a 1)).
  { intros p Hin. apply in_app_iff in Hin. simpl in Hin.
    destruct Hin as [Hin|[Heq|[]]].
    - assert (Hpprime : prime p).
      { rewrite Forall_forall in Hpicked_primes. apply Hpicked_primes. exact Hin. }
      destruct (proj1 (Hpicked p Hpprime) Hin) as [_ Hpdiv]. exact Hpdiv.
    - subst p. eapply Z.divide_trans; [exact Hcurrent_rem|exact Hrem_original]. }
  assert (Horiginal_bounds : 1 <= Znth index a 1 <= 1000000000).
  { rewrite Forall_forall in Ha. apply Ha.
    unfold Znth. apply nth_In. rewrite Zlength_correct in Hindex. lia. }
  pose proof (distinct_prime_divisors_length__factor_scan_advance
    (picked ++ [Znth tested primes 0]) (Znth index a 1)
    Hselected_nodup Hselected_primes Hselected_divides Horiginal_bounds)
    as Hselected_nat.
  assert (Hselected :
      Zlength (picked ++ [Znth tested primes 0]) <= 9).
  { rewrite Zlength_correct.
    change (Z.of_nat (length (picked ++ [Znth tested primes 0])) <= Z.of_nat 9).
    apply Nat2Z.inj_le. exact Hselected_nat. }
  pose proof (prime_factor_bag_length_bound__factor_scan_advance
    a index done Hbag Ha) as Hdone.
  rewrite Zlength_app in Hselected.
  change (Zlength picked + 1 <= 9) in Hselected.
  rewrite Hcount, Hfactors, Zlength_app.
  lia.
Qed.
Lemma pointwise_bounds_Forall__factor_scan_advance :
  forall a,
    (forall k, 0 <= k < Zlength a ->
      1 <= Znth k a 0 <= 1000000000) ->
    Forall (fun x => 1 <= x <= 1000000000) a.
Proof.
  intros a Hbounds. rewrite Forall_forall. intros x Hin.
  destruct (In_nth a x 0 Hin) as [n [Hn Heq]].
  specialize (Hbounds (Z.of_nat n)).
  assert (Hrange : 0 <= Z.of_nat n < Zlength a).
  { rewrite Zlength_correct. lia. }
  specialize (Hbounds Hrange).
  unfold Znth in Hbounds. rewrite Nat2Z.id in Hbounds.
  rewrite Heq in Hbounds. exact Hbounds.
Qed.
Lemma prime_divisor_exists__duplicate_init_result :
  forall x, 1 < x -> exists p, prime p /\ (p | x).
Proof.
  intros x Hx.
  assert (Hnonneg : 0 <= x) by lia.
  revert Hx.
  pattern x.
  apply Z_lt_induction.
  intros y IH Hy.
  destruct (prime_dec y) as [Hprime | Hnotprime].
  - exists y. split; [exact Hprime | apply Z.divide_refl].
  - destruct (not_prime_divide y Hy Hnotprime)
      as [d [[Hd_lower Hd_upper] Hd_divides]].
    destruct (IH d ltac:(lia) Hd_lower) as [p [Hp Hpd]].
    exists p. split; [exact Hp |].
    eapply Z.divide_trans; eauto.
  - exact Hnonneg.
Qed.
Lemma increasing_Znth_le__duplicate_loop :
  forall l i j,
    increasing l ->
    0 <= i <= j ->
    j < Zlength l ->
    Znth i l 0 <= Znth j l 0.
Proof.
  induction l as [| a l IH]; intros i j Hinc Hij Hj.
  - rewrite Zlength_nil in Hj. lia.
  - rewrite Zlength_cons in Hj.
    destruct (Z.eq_dec i 0) as [-> | Hi0].
    + destruct (Z.eq_dec j 0) as [-> | Hj0].
      * lia.
      * rewrite Znth0_cons, Znth_cons by lia.
        eapply increasing_aux_head_le_all_In; [exact Hinc |].
        unfold Znth.
        apply nth_In.
        rewrite Zlength_correct in Hj.
        lia.
    + rewrite !Znth_cons by lia.
      apply IH.
      * eapply increasing_aux_tail_increasing; exact Hinc.
      * lia.
      * rewrite Zlength_correct in Hj |- *.
        lia.
Qed.
Lemma composite_small_prime_divisor__factor_item_finish :
  forall n,
    1 < n <= 1000000000 ->
    ~ prime n ->
    exists p, prime p /\ (p | n) /\ p * p <= n.
Proof.
  intros n Hn Hnotprime.
  destruct (not_prime_divide n ltac:(lia) Hnotprime)
    as [d [[Hd_lower Hd_upper] Hd_divides]].
  destruct Hd_divides as [k Hn_eq].
  assert (Hk : 1 < k) by nia.
  destruct (Z_le_gt_dec (d * d) n) as [Hd_square | Hd_square].
  - destruct (prime_divisor_exists__duplicate_init_result d Hd_lower)
      as [p [Hp Hpd]].
    assert (Hp_ge : 2 <= p) by (apply prime_ge_2; exact Hp).
    destruct Hpd as [u Hd_eq].
    assert (Hu : 1 <= u) by nia.
    exists p. split; [exact Hp |].
    split.
    + exists (u * k). nia.
    + assert (Hp_le_d : p <= d) by nia.
      eapply Z.le_trans; [| exact Hd_square].
      apply Zmult_le_compat; lia.
  - assert (Hk_square : k * k <= n) by nia.
    destruct (prime_divisor_exists__duplicate_init_result k Hk)
      as [p [Hp Hpk]].
    assert (Hp_ge : 2 <= p) by (apply prime_ge_2; exact Hp).
    destruct Hpk as [u Hk_eq].
    assert (Hu : 1 <= u) by nia.
    exists p. split; [exact Hp |].
    split.
    + exists (d * u). nia.
    + assert (Hp_le_k : p <= k) by nia.
      eapply Z.le_trans; [| exact Hk_square].
      apply Zmult_le_compat; lia.
Qed.
Lemma residual_prime_exhausted__factor_item_finish :
  forall primes tested rem,
    CompletePrimeTable primes ->
    0 <= tested <= Zlength primes ->
    (forall p, In p (firstn (Z.to_nat tested) primes) -> ~ (p | rem)) ->
    1 < rem <= 1000000000 ->
    tested >= Zlength primes ->
    prime rem.
Proof.
  intros primes tested rem Htable Htested Hexcluded Hrem Hexhausted.
  destruct (prime_dec rem) as [Hprime | Hnotprime]; [exact Hprime |].
  destruct (composite_small_prime_divisor__factor_item_finish rem Hrem Hnotprime)
    as [p [Hp [Hpdiv Hpsquare]]].
  assert (Hp_bounds : 2 <= p <= 31623).
  { split; [apply prime_ge_2; exact Hp | nia]. }
  destruct Htable as (_ & _ & _ & Hcomplete).
  assert (Hin : In p primes).
  { apply (proj2 (Hcomplete p)). split; assumption. }
  assert (Hfirstn : firstn (Z.to_nat tested) primes = primes).
  { apply firstn_all2.
    apply (proj2 (Nat2Z.inj_le _ _)).
    rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct.
    lia. }
  exfalso. apply (Hexcluded p).
  - rewrite Hfirstn. exact Hin.
  - exact Hpdiv.
Qed.
Lemma complete_prime_before_index__factor_item_finish :
  forall primes j q,
    CompletePrimeTable primes ->
    0 <= j < Zlength primes ->
    prime q ->
    2 <= q <= 31623 ->
    q < Znth j primes 0 ->
    In q (firstn (Z.to_nat j) primes).
Proof.
  intros primes j q Htable Hj Hq Hqbounds Hlt.
  destruct Htable as (Hnodup & Hforall & Hinc & Hcomplete).
  assert (Hqin : In q primes).
  { apply (proj2 (Hcomplete q)). split; assumption. }
  destruct (@In_nth Z primes q 0 Hqin) as [k [Hk Hnth]].
  assert (HkZ : 0 <= Z.of_nat k < Zlength primes).
  { rewrite Zlength_correct. lia. }
  assert (HqZnth : Znth (Z.of_nat k) primes 0 = q).
  { unfold Znth. rewrite Nat2Z.id. exact Hnth. }
  assert (Hkj : Z.of_nat k < j).
  { destruct (Z_lt_ge_dec (Z.of_nat k) j) as [Hyes | Hno]; [exact Hyes |].
    pose proof
      (increasing_Znth_le__duplicate_loop primes j (Z.of_nat k)
         Hinc ltac:(lia) ltac:(lia)) as Horder.
    rewrite HqZnth in Horder. lia. }
  assert (Hknat : (k < Z.to_nat j)%nat).
  { apply (proj2 (Nat2Z.inj_lt _ _)).
    rewrite Z2Nat.id by lia.
    exact Hkj. }
  assert (Hprefix_length :
      length (firstn (Z.to_nat j) primes) = Z.to_nat j).
  { apply firstn_length_le.
    apply (proj2 (Nat2Z.inj_le _ _)).
    rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct. lia. }
  pose proof
    (nth_In (firstn (Z.to_nat j) primes) 0
       ltac:(rewrite Hprefix_length; exact Hknat)) as Hinprefix.
  rewrite nth_firstn in Hinprefix by exact Hknat.
  rewrite Hnth in Hinprefix.
  exact Hinprefix.
Qed.
Lemma residual_prime_square_cutoff__factor_item_finish :
  forall primes tested rem,
    CompletePrimeTable primes ->
    0 <= tested < Zlength primes ->
    (forall p, In p (firstn (Z.to_nat tested) primes) -> ~ (p | rem)) ->
    1 < rem <= 1000000000 ->
    Znth tested primes 0 * Znth tested primes 0 > rem ->
    prime rem.
Proof.
  intros primes tested rem Htable Htested Hexcluded Hrem Hcutoff.
  destruct (prime_dec rem) as [Hprime | Hnotprime]; [exact Hprime |].
  destruct (composite_small_prime_divisor__factor_item_finish rem Hrem Hnotprime)
    as [q [Hq [Hqdiv Hqsquare]]].
  assert (Hq_bounds : 2 <= q <= 31623).
  { split; [apply prime_ge_2; exact Hq | nia]. }
  assert (Hcurrent_prime : prime (Znth tested primes 0)).
  { destruct Htable as (_ & Hforall & _ & _).
    apply (proj1 (Forall_Znth prime 0 primes)); assumption. }
  assert (Hcurrent_ge : 2 <= Znth tested primes 0).
  { apply prime_ge_2; exact Hcurrent_prime. }
  assert (Hq_lt : q < Znth tested primes 0) by nia.
  assert (Hqin : In q (firstn (Z.to_nat tested) primes)).
  { eapply complete_prime_before_index__factor_item_finish; eauto. }
  exfalso. apply (Hexcluded q Hqin Hqdiv).
Qed.
Lemma firstn_succ_Znth__factor_item_finish :
  forall (l : list Z) i d,
    0 <= i < Zlength l ->
    firstn (Z.to_nat (i + 1)) l =
      firstn (Z.to_nat i) l ++ [Znth i l d].
Proof.
  intros l i d Hi.
  assert (Hsucc : Z.to_nat (i + 1) = S (Z.to_nat i)) by lia.
  rewrite Hsucc.
  unfold Znth.
  remember (Z.to_nat i) as n eqn:Hn.
  assert (Hnat : (n < length l)%nat).
  { subst n. apply (proj2 (Nat2Z.inj_lt _ _)).
    rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct. lia. }
  clear Hsucc Hn i Hi.
  revert n Hnat.
  induction l as [|x l IH]; intros n Hnat.
  - simpl in Hnat. lia.
  - destruct n as [|n].
    + reflexivity.
    + simpl. f_equal.
      apply IH.
      simpl in Hnat. lia.
Qed.
Lemma prime_factor_bag_prefix_next__factor_item_finish :
  forall a index done picked,
    PrimeFactorBagPrefix a index done ->
    0 <= index < Zlength a ->
    NoDup picked ->
    Forall prime picked ->
    (forall p, prime p ->
       (In p picked <-> (p | Znth index a 1))) ->
    PrimeFactorBagPrefix a (index + 1) (done ++ picked).
Proof.
  intros a index done picked Hbag Hindex Hnodup Hprimes Hpicked.
  destruct Hbag as [Hbounds [Hdone_primes Hcounts]].
  unfold PrimeFactorBagPrefix.
  split; [lia |].
  split.
  - apply Forall_app. split; assumption.
  - intros p Hp.
    specialize (Hcounts p Hp).
    rewrite count_occ_app.
    rewrite (firstn_succ_Znth__factor_item_finish a index 1 Hindex).
    rewrite filter_app, length_app.
    rewrite !Nat2Z.inj_add.
    rewrite Hcounts.
    f_equal.
    unfold zdividesb.
    destruct (Zdivide_dec p (Znth index a 1)) as [Hdiv | Hnotdiv].
    + assert (Hin : In p picked) by (apply (proj2 (Hpicked p Hp)); exact Hdiv).
      rewrite (proj1 (NoDup_count_occ' Z.eq_dec picked) Hnodup p Hin).
      simpl. destruct (Zdivide_dec p (Znth index a 1)); [reflexivity | contradiction].
    + assert (Hnotin : ~ In p picked).
      { intro Hin. apply Hnotdiv. apply (proj1 (Hpicked p Hp)); exact Hin. }
      apply (proj1 (count_occ_not_In Z.eq_dec picked p)) in Hnotin.
      rewrite Hnotin.
      simpl. destruct (Zdivide_dec p (Znth index a 1)); [contradiction | reflexivity].
Qed.
Lemma factor_scan2_residual_complete__factor_item_finish :
  forall a primes index tested rem factors,
    FactorScanState2 a primes index tested rem factors ->
    prime rem ->
    PrimeFactorBagPrefix a (index + 1) (factors ++ [rem]).
Proof.
  intros a primes index tested rem factors Hscan Hrem_prime.
  destruct Hscan as
    (done & picked & Hfactors & Hbag & Hindex & Htested & Hrem_bounds &
     Hrem_divides & Hnodup & Hprimes & Hpicked & Hexcluded & Hcoverage).
  rewrite Hfactors.
  replace ((done ++ picked) ++ [rem]) with (done ++ (picked ++ [rem]))
    by apply app_assoc.
  apply prime_factor_bag_prefix_next__factor_item_finish.
  - exact Hbag.
  - exact Hindex.
  - apply NoDup_app.
    + exact Hnodup.
    + constructor; [simpl; tauto | constructor].
    + intros q Hqin Hsingle.
      simpl in Hsingle. destruct Hsingle as [-> | []].
      apply (Hexcluded q).
      * apply (proj1 (Hpicked q Hrem_prime)); exact Hqin.
      * apply Z.divide_refl.
  - apply Forall_app. split; [exact Hprimes | constructor; auto].
  - intros p Hp. rewrite in_app_iff. simpl.
    specialize (Hcoverage p Hp).
    split.
    + intros [Hin | [Heq | []]].
      * apply (proj2 Hcoverage). left; exact Hin.
      * subst p. apply (proj2 Hcoverage). right. apply Z.divide_refl.
    + intro Hpdiv.
      apply (proj1 Hcoverage) in Hpdiv.
      destruct Hpdiv as [Hin | Hpdiv].
      * left; exact Hin.
      * right; left.
        pose proof (prime_divisors rem Hrem_prime p Hpdiv) as Hcases.
        pose proof (prime_ge_2 p Hp) as Hp_ge.
        lia.
Qed.
Lemma factor_scan2_unit_complete__factor_item_finish :
  forall a primes index tested rem factors,
    FactorScanState2 a primes index tested rem factors ->
    rem = 1 ->
    PrimeFactorBagPrefix a (index + 1) factors.
Proof.
  intros a primes index tested rem factors Hscan Hunit.
  destruct Hscan as
    (done & picked & Hfactors & Hbag & Hindex & Htested & Hrem_bounds &
     Hrem_divides & Hnodup & Hprimes & Hpicked & Hexcluded & Hcoverage).
  rewrite Hfactors.
  apply prime_factor_bag_prefix_next__factor_item_finish.
  - exact Hbag.
  - exact Hindex.
  - exact Hnodup.
  - exact Hprimes.
  - intros p Hp. specialize (Hcoverage p Hp). rewrite Hunit in Hcoverage.
    split.
    + intro Hin. apply (proj2 Hcoverage). left; exact Hin.
    + intro Hpdiv. apply (proj1 Hcoverage) in Hpdiv.
      destruct Hpdiv as [Hin | Hpdiv]; [exact Hin |].
      apply Z.divide_1_r in Hpdiv.
      pose proof (prime_ge_2 p Hp).
      destruct Hpdiv; lia.
Qed.
Lemma zdividesb_true__duplicate_init_result :
  forall p x, zdividesb p x = true <-> (p | x).
Proof.
  intros p x. unfold zdividesb.
  destruct (Zdivide_dec p x) as [Hdiv | Hnot].
  - tauto.
  - split; [discriminate | contradiction].
Qed.
Lemma two_occurrences_nat_count_occ__duplicate_init_result :
  forall (A : Type) (dec : forall x y : A, {x = y} + {x <> y})
         (l : list A) (x d : A) (i j : nat),
    (i < j)%nat ->
    (j < length l)%nat ->
    nth i l d = x ->
    nth j l d = x ->
    (2 <= count_occ dec l x)%nat.
Proof.
  intros A dec l.
  induction l as [|a l IH]; intros x d i j Hij Hj Hix Hjx; [simpl in Hj; lia |].
  destruct i as [|i].
  - destruct j as [|j]; [lia |].
    simpl in Hix, Hjx, Hj. subst a.
    simpl. destruct (dec x x) as [_ | Hneq]; [|contradiction].
    assert (Hin : In x l).
    { rewrite <- Hjx. apply nth_In. lia. }
    pose proof (proj1 (count_occ_In dec l x) Hin) as Hnonzero.
    lia.
  - destruct j as [|j]; [lia |].
    simpl in Hix, Hjx, Hj, Hij.
    simpl. destruct (dec a x) as [Heq | Hneq].
    + assert (Hin : In x l).
      { rewrite <- Hix. apply nth_In. lia. }
      pose proof (proj1 (count_occ_In dec l x) Hin) as Hnonzero.
      lia.
    + eapply IH with (i := i) (j := j) (d := d);
        [lia | lia | exact Hix | exact Hjx].
Qed.
Lemma count_occ_two_occurrences_nat__duplicate_init_result :
  forall (A : Type) (dec : forall x y : A, {x = y} + {x <> y})
         (l : list A) (x d : A),
    (2 <= count_occ dec l x)%nat ->
    exists i j : nat,
      (i < j)%nat /\ (j < length l)%nat /\
      nth i l d = x /\ nth j l d = x.
Proof.
  intros A dec l.
  induction l as [|a l IH]; intros x d Hcount; [simpl in Hcount; lia |].
  simpl in Hcount.
  destruct (dec a x) as [Heq | Hneq].
  - subst a.
    assert (Hpositive : (count_occ dec l x > 0)%nat) by lia.
    apply (proj2 (count_occ_In dec l x)) in Hpositive.
    destruct (@In_nth A l x d Hpositive) as [j [Hj Hnth]].
    exists 0%nat, (S j). simpl. repeat split; auto; lia.
  - destruct (IH x d ltac:(lia)) as [i [j [Hij [Hj [Hi_eq Hj_eq]]]]].
    exists (S i), (S j). simpl. repeat split; auto; lia.
Qed.
Lemma two_occurrences_count_occ__duplicate_init_result :
  forall (A : Type) (dec : forall x y : A, {x = y} + {x <> y})
         (l : list A) (x d : A),
    (exists i j : Z,
       0 <= i < j /\ j < Zlength l /\
       Znth i l d = x /\ Znth j l d = x) <->
    (2 <= count_occ dec l x)%nat.
Proof.
  intros A dec l x d. split.
  - intros [i [j [[Hi0 Hij] [Hjlen [Hi_eq Hj_eq]]]]].
    eapply two_occurrences_nat_count_occ__duplicate_init_result
      with (i := Z.to_nat i) (j := Z.to_nat j) (d := d).
    + lia.
    + rewrite Zlength_correct in Hjlen. lia.
    + unfold Znth in Hi_eq. exact Hi_eq.
    + unfold Znth in Hj_eq. exact Hj_eq.
  - intro Hcount.
    destruct (count_occ_two_occurrences_nat__duplicate_init_result
                A dec l x d Hcount)
      as [i [j [Hij [Hjlen [Hi_eq Hj_eq]]]]].
    exists (Z.of_nat i), (Z.of_nat j).
    rewrite Zlength_correct. repeat split; try lia.
    + unfold Znth. rewrite Nat2Z.id. exact Hi_eq.
    + unfold Znth. rewrite Nat2Z.id. exact Hj_eq.
Qed.
Lemma Znth_map_in_range__duplicate_init_result :
  forall (A B : Type) (f : A -> B) (l : list A) (i : Z)
         (da : A) (db : B),
    0 <= i < Zlength l ->
    Znth i (map f l) db = f (Znth i l da).
Proof.
  intros A B f l i da db Hi.
  rewrite (Znth_indep (map f l) i db (f da)).
  - unfold Znth. apply map_nth.
  - rewrite Zlength_correct, length_map. rewrite Zlength_correct in Hi. lia.
Qed.
Lemma filter_length_count_true__duplicate_init_result :
  forall (f : Z -> bool) (l : list Z),
    length (filter f l) = count_occ Bool.bool_dec (map f l) true.
Proof.
  intros f l. induction l as [|x l IH]; [reflexivity |].
  simpl. destruct (f x); simpl; rewrite IH; reflexivity.
Qed.
Lemma filter_two_indices__duplicate_init_result :
  forall (f : Z -> bool) (l : list Z),
    (2 <= length (filter f l))%nat <->
    exists i j : Z,
      0 <= i < j /\ j < Zlength l /\
      f (Znth i l 0) = true /\ f (Znth j l 0) = true.
Proof.
  intros f l. rewrite filter_length_count_true__duplicate_init_result.
  split.
  - intro Hcount.
    apply (proj2 (two_occurrences_count_occ__duplicate_init_result
                    bool Bool.bool_dec (map f l) true false)) in Hcount.
    destruct Hcount as [i [j [[Hi0 Hij] [Hjlen [Hi_eq Hj_eq]]]]].
    exists i, j.
    rewrite Zlength_correct, length_map in Hjlen.
    assert (Hi_bounds : 0 <= i < Zlength l) by
      (rewrite Zlength_correct; lia).
    assert (Hj_bounds : 0 <= j < Zlength l) by
      (rewrite Zlength_correct; lia).
    repeat split; try lia.
    + rewrite (Znth_map_in_range__duplicate_init_result
                 Z bool f l i 0 false) in Hi_eq by exact Hi_bounds.
      exact Hi_eq.
    + rewrite (Znth_map_in_range__duplicate_init_result
                 Z bool f l j 0 false) in Hj_eq by exact Hj_bounds.
      exact Hj_eq.
  - intros [i [j [[Hi0 Hij] [Hjlen [Hi_eq Hj_eq]]]]].
    assert (Hi_bounds : 0 <= i < Zlength l) by lia.
    assert (Hj_bounds : 0 <= j < Zlength l) by lia.
    apply (proj1 (two_occurrences_count_occ__duplicate_init_result
                    bool Bool.bool_dec (map f l) true false)).
    exists i, j.
    rewrite Zlength_correct, length_map.
    repeat split; try lia.
    + rewrite Zlength_correct in Hjlen. exact Hjlen.
    + rewrite (Znth_map_in_range__duplicate_init_result
                 Z bool f l i 0 false) by exact Hi_bounds.
      exact Hi_eq.
    + rewrite (Znth_map_in_range__duplicate_init_result
                 Z bool f l j 0 false) by exact Hj_bounds.
      exact Hj_eq.
Qed.
Lemma prime_factor_bag_prefix_permutation__duplicate_init_result :
  forall a upto factors sorted,
    Permutation factors sorted ->
    PrimeFactorBagPrefix a upto factors ->
    PrimeFactorBagPrefix a upto sorted.
Proof.
  intros a upto factors sorted Hperm [Hbounds [Hprimes Hcounts]].
  unfold PrimeFactorBagPrefix.
  split; [exact Hbounds |].
  split.
  - eapply Permutation_Forall; eauto.
  - intros p Hp.
    rewrite <- (proj1 (Permutation_count_occ Z.eq_dec factors sorted) Hperm p).
    apply Hcounts; exact Hp.
Qed.
Lemma duplicate_scan_loop_initial__duplicate_init_result :
  forall factors count,
    Zlength factors = count ->
    0 <= count ->
    DuplicateScanLoopState factors count 1 0.
Proof.
  intros factors count Hlength Hcount.
  destruct (Z.eq_dec count 0) as [Hzero | Hnonzero].
  - left.
    split; [exact Hzero |].
    split; [reflexivity |].
    unfold DuplicatePrefixState.
    split; [rewrite Hlength; lia |].
    split; [left; reflexivity |].
    split.
    + discriminate.
    + intros [i [j [[Hi Hij] [Hj Heq]]]]. lia.
  - right.
    split; [lia |].
    split; [lia |].
    unfold DuplicatePrefixState.
    split; [rewrite Hlength; lia |].
    split; [left; reflexivity |].
    split.
    + discriminate.
    + intros [i [j [[Hi Hij] [Hj Heq]]]]. lia.
Qed.
Lemma duplicate_scan_loop_exit__duplicate_init_result :
  forall factors count cursor found,
    count <= cursor ->
    DuplicateScanLoopState factors count cursor found ->
    DuplicatePrefixState factors count found.
Proof.
  intros factors count cursor found Hexit Hstate.
  destruct Hstate as [[Hcount [Hcursor Hprefix]] |
                      [Hcount [Hcursor Hprefix]]].
  - subst count. exact Hprefix.
  - assert (cursor = count) by lia.
    subst cursor. exact Hprefix.
Qed.
Lemma prime_factor_duplicate_spec__duplicate_init_result :
  forall a factors count found,
    Zlength factors = count ->
    PrimeFactorBagPrefix a (Zlength a) factors ->
    DuplicatePrefixState factors count found ->
    Spec a found.
Proof.
  intros a factors count found Hlength Hbag Hstate.
  destruct Hbag as [_ [Hprimes Hcounts]].
  destruct Hstate as [_ [Hfound Hduplicate]].
  unfold Spec. split; [exact Hfound |].
  split.
  - intro Hfound_one.
    apply (proj1 Hduplicate) in Hfound_one.
    destruct Hfound_one as [fi [fj [[Hfi0 Hfij] [Hfjcount Hequal]]]].
    set (p := Znth fi factors 0).
    assert (Hp : prime p).
    { rewrite Forall_forall in Hprimes.
      apply Hprimes. subst p. unfold Znth. apply nth_In.
      rewrite Zlength_correct in Hlength. lia. }
    assert (Hfactor_count : (2 <= count_occ Z.eq_dec factors p)%nat).
    { apply (proj1 (two_occurrences_count_occ__duplicate_init_result
                      Z Z.eq_dec factors p 0)).
      exists fi, fj. repeat split; try lia.
    }
    specialize (Hcounts p Hp).
    rewrite Zlength_correct, Nat2Z.id, firstn_all in Hcounts.
    assert (Hfilter_count : (2 <= length (filter (zdividesb p) a))%nat) by lia.
    apply (proj1 (filter_two_indices__duplicate_init_result
                    (zdividesb p) a)) in Hfilter_count.
    destruct Hfilter_count as [ai [aj [[Hai0 Haij] [Hajlen [Hai_div Haj_div]]]]].
    exists ai, aj, p. repeat split; try lia.
    + pose proof (prime_ge_2 p Hp). lia.
    + apply (proj1 (zdividesb_true__duplicate_init_result p (Znth ai a 0))).
      exact Hai_div.
    + apply (proj1 (zdividesb_true__duplicate_init_result p (Znth aj a 0))).
      exact Haj_div.
  - intros [ai [aj [x [[Hai0 Hailen] [[Haj0 Hajlen]
             [Hdistinct [Hx_ge [Hx_div_i Hx_div_j]]]]]]]].
    destruct (prime_divisor_exists__duplicate_init_result x ltac:(lia))
      as [p [Hp Hp_div_x]].
    assert (Hp_div_i : (p | Znth ai a 0)).
    { eapply Z.divide_trans with (m := x); [exact Hp_div_x | exact Hx_div_i]. }
    assert (Hp_div_j : (p | Znth aj a 0)).
    { eapply Z.divide_trans with (m := x); [exact Hp_div_x | exact Hx_div_j]. }
    assert (Hfilter_count : (2 <= length (filter (zdividesb p) a))%nat).
    { apply (proj2 (filter_two_indices__duplicate_init_result
                      (zdividesb p) a)).
      destruct (Z_lt_ge_dec ai aj) as [Hlt | Hge].
      - exists ai, aj. repeat split; try lia;
          apply (proj2 (zdividesb_true__duplicate_init_result _ _)); assumption.
      - assert (Hlt : aj < ai) by lia.
        exists aj, ai. repeat split; try lia;
          apply (proj2 (zdividesb_true__duplicate_init_result _ _)); assumption. }
    specialize (Hcounts p Hp).
    rewrite Zlength_correct, Nat2Z.id, firstn_all in Hcounts.
    assert (Hfactor_count : (2 <= count_occ Z.eq_dec factors p)%nat) by lia.
    apply (proj2 (two_occurrences_count_occ__duplicate_init_result
                    Z Z.eq_dec factors p 0)) in Hfactor_count.
    apply (proj2 Hduplicate).
    destruct Hfactor_count as [fi [fj [[Hfi0 Hfij] [Hfjlen [Hfi_eq Hfj_eq]]]]].
    exists fi, fj. repeat split; try lia.
Qed.
Lemma duplicate_scan_equal_step__duplicate_loop :
  forall factors count i found,
    Zlength factors = count ->
    DuplicateScanLoopState factors count i found ->
    1 <= i ->
    i < count ->
    Znth i factors 0 = Znth (i - 1) factors 0 ->
    DuplicateScanLoopState factors count (i + 1) 1.
Proof.
  intros factors count i found Hlen Hscan Hi Hicount Hequal.
  unfold DuplicateScanLoopState in *.
  destruct Hscan as [[Hcount0 [Hcursor Hprefix]] |
                     [Hcountpos [Hcursor Hprefix]]].
  - lia.
  - right.
    split; [exact Hcountpos |].
    split; [lia |].
    unfold DuplicatePrefixState.
    split; [rewrite Hlen; lia |].
    split; [right; reflexivity |].
    split.
    + intros _.
      exists (i - 1), i.
      repeat split; try lia.
    + intros _; reflexivity.
Qed.
Lemma duplicate_scan_unequal_step__duplicate_loop :
  forall factors count i found,
    Zlength factors = count ->
    increasing factors ->
    DuplicateScanLoopState factors count i found ->
    1 <= i ->
    i < count ->
    Znth i factors 0 <> Znth (i - 1) factors 0 ->
    DuplicateScanLoopState factors count (i + 1) found.
Proof.
  intros factors count i found Hlen Hinc Hscan Hi Hicount Hneq.
  unfold DuplicateScanLoopState in *.
  destruct Hscan as [[Hcount0 [Hcursor Hprefix]] |
                     [Hcountpos [Hcursor Hprefix]]].
  - lia.
  - right.
    split; [exact Hcountpos |].
    split; [lia |].
    unfold DuplicatePrefixState in *.
    destruct Hprefix as [Hbounds [Hfound Hdup]].
    split; [lia |].
    split; [exact Hfound |].
    split.
    + intros Hfound1.
      apply (proj1 Hdup) in Hfound1.
      destruct Hfound1 as [x [y [Hxy [Hyi Heq]]]].
      exists x, y.
      repeat split; try lia; exact Heq.
    + intros [x [y [Hxy [Hynew Heq]]]].
      apply (proj2 Hdup).
      destruct (Z_lt_dec y i) as [Hyi | Hnyi].
      * exists x, y.
        repeat split; try lia; exact Heq.
      * assert (Hy : y = i) by lia.
        subst y.
        pose proof
          (increasing_Znth_le__duplicate_loop factors (i - 1) i
             Hinc ltac:(lia) ltac:(rewrite Hlen; lia)) as Hprev.
        pose proof
          (increasing_Znth_le__duplicate_loop factors x (i - 1)
             Hinc ltac:(lia) ltac:(rewrite Hlen; lia)) as Hx.
        exfalso.
        lia.
Qed.
