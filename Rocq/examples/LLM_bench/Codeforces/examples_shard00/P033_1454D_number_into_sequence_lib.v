Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Local Open Scope Z_scope.

Definition ValidFactorSequence (n : Z) (a : list Z) : Prop :=
  0 < Zlength a /\ Forall (fun x => x > 1) a /\
  fold_right Z.mul 1 a = n /\
  forall i, 0 <= i < Zlength a - 1 -> (Znth i a 0 | Znth (i + 1) a 0).

Definition Pre (n : Z) : Prop := 2 <= n <= 10000000000.

Definition Spec (n : Z) (out : list Z) : Prop :=
  ValidFactorSequence n out /\
  max_value_of_subset Z.le (ValidFactorSequence n)
    (fun candidate => Zlength candidate) (Zlength out).

Definition FactorSearchState
    (n value p best_prime best_exp : Z) : Prop :=
  2 <= n <= 10000000000 /\
  1 <= value <= n /\
  2 <= p <= 100001 /\
  p * p <= 1000000000000000000 /\
  1 <= best_exp <= 64 /\
  2 <= best_prime <= n /\
  Z.divide value n /\
  Z.divide (Z.pow best_prime best_exp) n /\
  (forall q k,
      2 <= q < p ->
      1 <= k ->
      Z.divide (Z.pow q k) n ->
      k <= best_exp).

Definition FactorExtractState
    (n value p e best_prime best_exp : Z) : Prop :=
  2 <= n <= 10000000000 /\
  1 <= value <= n /\
  2 <= p <= 100001 /\
  0 <= e <= 64 /\
  1 <= best_exp <= 64 /\
  2 <= best_prime <= n /\
  Z.divide (value * Z.pow p e) n /\
  Z.divide (Z.pow best_prime best_exp) n.

Definition BestPowerChoice (n best_prime best_exp : Z) : Prop :=
  2 <= n <= 10000000000 /\
  1 <= best_exp <= 64 /\
  2 <= best_prime <= n /\
  exists result,
    Zlength result = best_exp /\
    (forall i, 0 <= i < best_exp - 1 -> Znth i result 0 = best_prime) /\
    ValidFactorSequence n result /\
    Spec n result.

Definition OutputPrefixState
    (n best_prime best_exp i rest : Z) (written : list Z) : Prop :=
  BestPowerChoice n best_prime best_exp /\
  0 <= i < best_exp /\
  1 <= rest <= n /\
  Zlength written = i /\
  (forall j, 0 <= j < i -> Znth j written 0 = best_prime) /\
  rest * Z.pow best_prime i = n.

Definition FinalOutputSequence
    (n best_prime best_exp rest : Z) (result : list Z) : Prop :=
  BestPowerChoice n best_prime best_exp /\
  1 <= rest <= n /\
  Zlength result = best_exp /\
  (forall j, 0 <= j < best_exp - 1 -> Znth j result 0 = best_prime) /\
  Znth (best_exp - 1) result 0 = rest /\
  rest * Z.pow best_prime (best_exp - 1) = n /\
  Spec n result.

Require Import Coq.Sorting.Permutation.
Require Import Coq.ZArith.Znumtheory.
Import ListNotations.

Definition FactorProfileProduct (ps es : list Z) : Z :=
  fold_right Z.mul 1
    (map (fun i => Z.pow (Znth i ps 1) (Znth i es 0))
         (Zrange 0 (Zlength ps))).

Definition FactorProfileShape (p : Z) (ps es : list Z) : Prop :=
  Zlength ps = Zlength es /\
  NoDup ps /\
  Forall prime ps /\
  (forall i, 0 <= i < Zlength ps -> 2 <= Znth i ps 1 < p) /\
  (forall i, 0 <= i < Zlength es -> 1 <= Znth i es 0 <= 64).

Definition FactorSearchProfile
    (n value p best_prime best_exp : Z) (ps es : list Z) : Prop :=
  FactorSearchState n value p best_prime best_exp /\
  FactorProfileShape p ps es /\
  n = value * FactorProfileProduct ps es /\
  (forall q, 2 <= q < p -> ~ Z.divide q value) /\
  (forall i, 0 <= i < Zlength es -> Znth i es 0 <= best_exp) /\
  (best_exp = 1 \/
    exists i, 0 <= i < Zlength es /\ Znth i ps 1 = best_prime /\
      Znth i es 0 = best_exp) /\
  (forall q k,
      p <= q ->
      1 <= k ->
      Z.divide (Z.pow q k) n ->
      k <= best_exp \/ Z.divide (Z.pow q k) value) /\
  (value mod p <> 0 ->
    forall k, 1 <= k -> Z.divide (Z.pow p k) n -> k <= best_exp) /\
  (value mod p <> 0 -> p + 1 <= 100001) /\
  (p * p > value -> BestPowerChoice n best_prime best_exp).

Definition FactorExtractOrigin
    (n value p e best_prime best_exp : Z) (ps es : list Z) : Prop :=
  prime p /\
  FactorSearchProfile n (value * Z.pow p e) p best_prime best_exp ps es.

Definition FactorExtractGuard (value p e : Z) : Prop :=
  p * p <= value * Z.pow p e.

Definition FactorExtractProfile
    (n value p e best_prime best_exp : Z) (ps es : list Z) : Prop :=
  FactorExtractState n value p e best_prime best_exp /\
  FactorExtractOrigin n value p e best_prime best_exp ps es /\
  FactorProfileShape p ps es /\
  n = value * Z.pow p e * FactorProfileProduct ps es /\
  (forall i, 0 <= i < Zlength es -> Znth i es 0 <= best_exp) /\
  (best_exp = 1 \/
    exists i, 0 <= i < Zlength es /\ Znth i ps 1 = best_prime /\
      Znth i es 0 = best_exp) /\
  (value mod p <> 0 -> p <= n) /\
  (value mod p <> 0 -> p + 1 <= 100001) /\
  (value mod p <> 0 ->
    e > best_exp ->
    FactorSearchProfile n value (p + 1) p e (ps ++ [p]) (es ++ [e])) /\
  (value mod p <> 0 ->
    e <= best_exp ->
    FactorSearchProfile n value (p + 1) best_prime best_exp
      (ps ++ [p]) (es ++ [e])).

Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.Zpow_facts.

Lemma fold_mul_positive__search_initialization :
  forall l,
    Forall (fun x => 1 <= x) l ->
    1 <= fold_right Z.mul 1 l.
Proof.
  intros l Hpositive.
  induction Hpositive; simpl; nia.
Qed.

Lemma FactorProfileProduct_positive__search_initialization :
  forall p ps es,
    FactorProfileShape p ps es ->
    1 <= FactorProfileProduct ps es.
Proof.
  intros p ps es Hshape.
  destruct Hshape as (Hlen & Hnodup & Hprimes & Hprime_bounds & Hexps).
  unfold FactorProfileProduct.
  apply fold_mul_positive__search_initialization.
  apply Forall_forall.
  intros x Hxin.
  apply in_map_iff in Hxin.
  destruct Hxin as (i & <- & Hi).
  apply <- In_Zrange in Hi.
  pose proof (proj1 (Forall_Znth prime 1 ps) Hprimes i Hi) as Hprime.
  pose proof (prime_ge_2 _ Hprime) as Hbase.
  specialize (Hexps i).
  assert (0 <= i < Zlength es) by lia.
  specialize (Hexps H).
  pose proof
    (Z.pow_pos_nonneg (Znth i ps 1) (Znth i es 0)
      ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma factor_extract_core_step__search_initialization :
  forall n value p e best_prime best_exp ps es,
    value mod p = 0 ->
    FactorExtractState n value p e best_prime best_exp ->
    FactorExtractOrigin n value p e best_prime best_exp ps es ->
    FactorExtractState n (value / p) p (e + 1) best_prime best_exp /\
    FactorExtractOrigin n (value / p) p (e + 1)
      best_prime best_exp ps es.
Proof.
  intros n value p e best_prime best_exp ps es Hmod Hstate Horigin.
  unfold FactorExtractState in Hstate.
  destruct Hstate as
    (Hn & Hvalue & Hp & He & Hbest_exp & Hbest_prime & Hscale_div & Hbest_div).
  unfold FactorExtractOrigin in Horigin.
  destruct Horigin as (Hprime & Hsearch).
  assert (Hquot : value = p * (value / p)).
  { pose proof (Z.div_mod value p ltac:(lia)) as Hdivmod.
    rewrite Hmod in Hdivmod. nia. }
  assert (Hqpos : 1 <= value / p) by nia.
  assert (Hqbound : value / p <= n) by nia.
  assert (Hshape : FactorProfileShape p ps es).
  { exact (proj1 (proj2 Hsearch)). }
  assert (Hfactor : n = value * Z.pow p e * FactorProfileProduct ps es).
  { exact (proj1 (proj2 (proj2 Hsearch))). }
  assert (Hproduct : 1 <= FactorProfileProduct ps es).
  { apply FactorProfileProduct_positive__search_initialization with p.
    exact Hshape. }
  assert (Henext : e + 1 <= 64).
  { destruct (Z_lt_ge_dec e 64) as [Helt | Hegen]; [lia |].
    assert (e = 64) by lia. subst e.
    assert (Hpow : Z.pow 2 64 <= Z.pow p 64).
    { apply Zpower_le_monotone3; [lia |]. split; lia. }
    change (18446744073709551616 <= Z.pow p 64) in Hpow.
    nia. }
  assert (Hscale :
      (value / p) * Z.pow p (e + 1) = value * Z.pow p e).
  { replace (e + 1) with (Z.succ e) by lia.
    rewrite Z.pow_succ_r by lia.
    assert ((value / p) * p = value) by nia.
    nia. }
  split.
  - unfold FactorExtractState.
    split; [exact Hn |].
    split; [split; assumption |].
    split; [exact Hp |].
    split; [split; lia |].
    split; [exact Hbest_exp |].
    split; [exact Hbest_prime |].
    split.
    + rewrite Hscale. exact Hscale_div.
    + exact Hbest_div.
  - unfold FactorExtractOrigin.
    split; [exact Hprime |].
    rewrite Hscale.
    exact Hsearch.
Qed.

Lemma factor_extract_guard_step__search_initialization :
  forall value p e,
    2 <= p ->
    value mod p = 0 ->
    0 <= e ->
    FactorExtractGuard value p e ->
    FactorExtractGuard (value / p) p (e + 1).
Proof.
  intros value p e Hp Hmod He Hguard.
  assert (Hquot : value = p * (value / p)).
  { pose proof (Z.div_mod value p ltac:(lia)) as Hdivmod.
    rewrite Hmod in Hdivmod. nia. }
  assert (Hscale :
      (value / p) * Z.pow p (e + 1) = value * Z.pow p e).
  { replace (e + 1) with (Z.succ e) by lia.
    rewrite Z.pow_succ_r by lia.
    assert ((value / p) * p = value) by nia.
    nia. }
  unfold FactorExtractGuard in *.
  rewrite Hscale.
  exact Hguard.
Qed.

Lemma factor_extract_exit_positive__search_initialization :
  forall value p e,
    0 <= e ->
    (e = 0 -> value mod p = 0) ->
    value mod p <> 0 ->
    1 <= e.
Proof.
  intros value p e He Hzero Hmod.
  assert (e <> 0).
  { intro Heq. apply Hmod. apply Hzero. exact Heq. }
  lia.
Qed.

Lemma fold_mul_app__search_initialization :
  forall l1 l2,
    fold_right Z.mul 1 (l1 ++ l2) =
    fold_right Z.mul 1 l1 * fold_right Z.mul 1 l2.
Proof.
  induction l1 as [|x l1 IH]; intros l2.
  - change (fold_right Z.mul 1 l2 = 1 * fold_right Z.mul 1 l2).
    ring.
  - simpl. rewrite IH. ring.
Qed.

Lemma Zrange_zero_succ__search_initialization :
  forall k, 0 <= k -> Zrange 0 (k + 1) = Zrange 0 k ++ [k].
Proof.
  intros k Hk. unfold Zrange.
  replace (Z.to_nat (k + 1 - 0)) with (Z.to_nat (k - 0) + 1)%nat by lia.
  rewrite Zrange_aux_app. simpl.
  replace (k - 0) with k by lia.
  rewrite Z2Nat.id by lia.
  reflexivity.
Qed.

Lemma FactorProfileProduct_app_single__search_initialization :
  forall ps es p e,
    Zlength ps = Zlength es ->
    FactorProfileProduct (ps ++ [p]) (es ++ [e]) =
    FactorProfileProduct ps es * Z.pow p e.
Proof.
  intros ps es p e Hlen.
  unfold FactorProfileProduct.
  rewrite Zlength_app_cons, Zrange_zero_succ__search_initialization
    by (pose proof (Zlength_nonneg ps); lia).
  rewrite map_app, fold_mul_app__search_initialization. simpl.
  f_equal.
  - apply f_equal.
    apply map_ext_in. intros i Hi.
    apply <- In_Zrange in Hi.
    rewrite !app_Znth1 by lia. reflexivity.
  - rewrite !app_Znth2 by lia.
    rewrite Hlen. replace (Zlength es - Zlength es) with 0 by lia.
    replace (Zlength ps - Zlength ps) with 0 by lia.
    rewrite !Znth0_cons. ring.
Qed.

Lemma FactorProfileShape_app_single__search_initialization :
  forall p ps es e,
    FactorProfileShape p ps es ->
    prime p ->
    1 <= e <= 64 ->
    FactorProfileShape (p + 1) (ps ++ [p]) (es ++ [e]).
Proof.
  intros p ps es e Hshape Hprime He.
  destruct Hshape as (Hlen & Hnodup & Hprimes & Hprime_bounds & Hexps).
  unfold FactorProfileShape.
  split.
  - rewrite !Zlength_app_cons. lia.
  - split.
    + apply NoDup_app.
      * exact Hnodup.
      * constructor; [simpl; tauto | constructor].
      * intros q Hqps Hqsingle.
        simpl in Hqsingle.
        destruct Hqsingle as [Heq | Hfalse]; [subst q | contradiction].
        assert (Hlt_all : Forall (fun q => q < p) ps).
        { apply (proj2 (Forall_Znth (fun q => q < p) 1 ps)).
          intros i Hi. exact (proj2 (Hprime_bounds i Hi)). }
        pose proof
          (proj1 (Forall_forall (fun q => q < p) ps) Hlt_all p Hqps) as Hlt.
        exact (Z.lt_irrefl p Hlt).
    + split.
      * apply Forall_app. split; [exact Hprimes |].
        constructor; [exact Hprime | constructor].
      * split.
        -- intros i Hi.
           rewrite Zlength_app_cons in Hi.
           destruct (Z_lt_ge_dec i (Zlength ps)) as [Hil | Hige].
           ++ rewrite app_Znth1 by lia.
              specialize (Hprime_bounds i). lia.
           ++ assert (i = Zlength ps) by lia. subst i.
              rewrite app_Znth2 by lia.
              replace (Zlength ps - Zlength ps) with 0 by lia.
              rewrite Znth0_cons.
              pose proof (prime_ge_2 _ Hprime). lia.
        -- intros i Hi.
           rewrite Zlength_app_cons in Hi.
           destruct (Z_lt_ge_dec i (Zlength es)) as [Hil | Hige].
           ++ rewrite app_Znth1 by lia. apply Hexps. lia.
           ++ assert (i = Zlength es) by lia. subst i.
              rewrite app_Znth2 by lia.
              replace (Zlength es - Zlength es) with 0 by lia.
              rewrite Znth0_cons. exact He.
Qed.

Lemma factor_extract_profile_from_successors__search_initialization :
  forall n value p e best_prime best_exp ps es,
    value mod p <> 0 ->
    1 <= e ->
    FactorExtractGuard value p e ->
    FactorExtractState n value p e best_prime best_exp ->
    FactorExtractOrigin n value p e best_prime best_exp ps es ->
    (e > best_exp ->
      FactorSearchProfile n value (p + 1) p e
        (ps ++ [p]) (es ++ [e])) ->
    (e <= best_exp ->
      FactorSearchProfile n value (p + 1) best_prime best_exp
        (ps ++ [p]) (es ++ [e])) ->
    FactorExtractProfile n value p e best_prime best_exp ps es.
Proof.
  intros n value p e best_prime best_exp ps es
    Hmod He Hguard Hstate Horigin Hsuccess_gt Hsuccess_le.
  pose proof Hstate as Hstate_copy.
  unfold FactorExtractState in Hstate_copy.
  destruct Hstate_copy as
    (Hn & Hvalue & Hp & He_bound & Hbest_exp & Hbest_prime &
     Hscale_div & Hbest_div).
  pose proof Horigin as Horigin_copy.
  unfold FactorExtractOrigin in Horigin_copy.
  destruct Horigin_copy as (Hprime & Hsearch).
  pose proof Hsearch as Hsearch_copy.
  unfold FactorSearchProfile in Hsearch_copy.
  destruct Hsearch_copy as
    (Hsearch_state & Hshape & Hfactor & Hnondividing & Hes_bound &
     Hbest_attained & Hfuture & Hat_candidate & Hnext_bound & Hfinish).
  assert (Hproduct_positive : 1 <= FactorProfileProduct ps es).
  { apply FactorProfileProduct_positive__search_initialization with p.
    exact Hshape. }
  assert (Hp_le_n : p <= n).
  { unfold FactorExtractGuard in Hguard. nia. }
  assert (Hp_next : p + 1 <= 100001).
  { unfold FactorExtractGuard in Hguard. nia. }
  unfold FactorExtractProfile.
  split; [exact Hstate |].
  split; [exact Horigin |].
  split; [exact Hshape |].
  split; [nia |].
  split; [exact Hes_bound |].
  split; [exact Hbest_attained |].
  split; [intros _; exact Hp_le_n |].
  split; [intros _; exact Hp_next |].
  split.
  - intros _ Hgt. apply Hsuccess_gt. exact Hgt.
  - intros _ Hle. apply Hsuccess_le. exact Hle.
Qed.

Require Import Coq.ZArith.Zquot.
Lemma best_power_choice_small__search_initialization :
  forall n,
    2 <= n < 4 ->
    BestPowerChoice n n 1.
Proof.
  intros n Hn.
  assert (Hvalid : ValidFactorSequence n [n]).
  { unfold ValidFactorSequence.
    split.
    - rewrite Zlength_cons, Zlength_nil. lia.
    - split.
      + constructor; [lia | constructor].
      + split.
        * simpl. ring.
        * intros i Hi.
          rewrite Zlength_cons, Zlength_nil in Hi. lia. }
  unfold BestPowerChoice.
  repeat split; try lia.
  exists [n].
  split.
  - change (1 = 1). reflexivity.
  - split.
    + intros i Hi. lia.
    + split; [exact Hvalid |].
      unfold Spec.
      split; [exact Hvalid |].
      unfold MaxMin.max_value_of_subset, MaxMin.max_object_of_subset.
      exists [n].
      split.
      * split; [exact Hvalid |].
        intros candidate Hcandidate.
        destruct Hcandidate as
          (Hnonempty & Hpositive & Hproduct & Hchain).
        destruct candidate as [|a candidate].
        -- rewrite Zlength_nil in Hnonempty. lia.
        -- destruct candidate as [|b tail].
           ++ change (1 <= 1). lia.
           ++ inversion Hpositive as [|a' candidate' Ha Hpositive_tail].
              inversion Hpositive_tail as [|b' tail' Hb Hpositive_rest].
              subst a' candidate' b' tail'.
              assert (Hrest_positive :
                  Forall (fun x => 1 <= x) tail).
              { rewrite Forall_forall in Hpositive_rest |- *.
                intros x Hx.
                specialize (Hpositive_rest x Hx). lia. }
              pose proof
                (fold_mul_positive__search_initialization
                  tail Hrest_positive) as Hfold.
              simpl in Hproduct.
              nia.
      * reflexivity.
Qed.
Lemma factor_search_profile_initial__search_initialization :
  forall n,
    2 <= n <= 10000000000 ->
    FactorSearchState n n 2 n 1 /\
    FactorSearchProfile n n 2 n 1 [] [].
Proof.
  intros n Hn.
  assert (Hstate : FactorSearchState n n 2 n 1).
  { unfold FactorSearchState.
    repeat split; try lia.
    - apply Z.divide_refl.
    - rewrite Z.pow_1_r. apply Z.divide_refl. }
  assert (Hshape : FactorProfileShape 2 [] []).
  { unfold FactorProfileShape.
    split; [reflexivity |].
    split; [constructor |].
    split; [constructor |].
    split.
    - intros i Hi. rewrite Zlength_nil in Hi. lia.
    - intros i Hi. rewrite Zlength_nil in Hi. lia. }
  split; [exact Hstate |].
  unfold FactorSearchProfile.
  apply conj; [exact Hstate |].
  apply conj; [exact Hshape |].
  apply conj.
  - unfold FactorProfileProduct. simpl. ring.
  - apply conj.
    + intros q Hq. lia.
    + apply conj.
      * intros i Hi. rewrite Zlength_nil in Hi. lia.
      * apply conj.
        -- left. reflexivity.
        -- apply conj.
           ++ intros q k Hq Hk Hdivide. right. exact Hdivide.
           ++ apply conj.
              ** intros Hmod k Hk Hdivide.
                 exfalso. apply Hmod.
                 apply (proj2 (Z.mod_divide n 2 ltac:(lia))).
                 eapply Z.divide_trans with (m := Z.pow 2 k).
                 --- apply Zpower_divide. lia.
                 --- exact Hdivide.
              ** apply conj.
                 --- intros _. lia.
                 --- intros Hsmall.
                     apply best_power_choice_small__search_initialization.
                     lia.
Qed.
Lemma search_profile_divisor_prime__search_initialization :
  forall n value p best_prime best_exp ps es,
    value mod p = 0 ->
    FactorSearchProfile n value p best_prime best_exp ps es ->
    prime p.
Proof.
  intros n value p best_prime best_exp ps es Hmod Hprofile.
  pose proof Hprofile as Hprofile_data.
  unfold FactorSearchProfile in Hprofile_data.
  destruct Hprofile_data as
    (Hstate & Hshape & Hfactor & Hnondividing & Hes_bound &
     Hbest_attained & Hfuture & Hat_candidate & Hnext_bound & Hfinish).
  pose proof Hstate as Hstate_data.
  unfold FactorSearchState in Hstate_data.
  destruct Hstate_data as
    (Hn & Hvalue & Hp & Hpsquare & Hbest_exp & Hbest_prime &
     Hvalue_div & Hbest_div & Hpast).
  destruct (prime_dec p) as [Hprime | Hnot_prime]; [exact Hprime |].
  exfalso.
  destruct (not_prime_divide p ltac:(lia) Hnot_prime)
    as (q & Hq & Hq_divides_p).
  apply (Hnondividing q ltac:(lia)).
  eapply Z.divide_trans; [exact Hq_divides_p |].
  apply (proj1 (Z.mod_divide value p ltac:(lia))).
  exact Hmod.
Qed.
Lemma factor_extract_initial__search_initialization :
  forall n value p best_prime best_exp ps es,
    Z.rem value p = 0 ->
    p * p <= value ->
    FactorSearchProfile n value p best_prime best_exp ps es ->
    FactorExtractGuard value p 0 /\
    FactorExtractState n value p 0 best_prime best_exp /\
    FactorExtractOrigin n value p 0 best_prime best_exp ps es.
Proof.
  intros n value p best_prime best_exp ps es Hrem Hguard Hprofile.
  pose proof Hprofile as Hprofile_data.
  unfold FactorSearchProfile in Hprofile_data.
  destruct Hprofile_data as
    (Hstate & Hshape & Hfactor & Hnondividing & Hes_bound &
     Hbest_attained & Hfuture & Hat_candidate & Hnext_bound & Hfinish).
  pose proof Hstate as Hstate_data.
  unfold FactorSearchState in Hstate_data.
  destruct Hstate_data as
    (Hn & Hvalue & Hp & Hpsquare & Hbest_exp & Hbest_prime &
     Hvalue_div & Hbest_div & Hpast).
  assert (Hmod : value mod p = 0).
  { apply (proj1 (Zrem_Zmod_zero value p ltac:(lia))).
    exact Hrem. }
  assert (Hprime : prime p).
  { eapply search_profile_divisor_prime__search_initialization; eauto. }
  split.
  - unfold FactorExtractGuard. rewrite Z.pow_0_r, Z.mul_1_r.
    exact Hguard.
  - split.
    + unfold FactorExtractState.
      repeat split; try lia; try assumption.
      rewrite Z.pow_0_r, Z.mul_1_r. exact Hvalue_div.
    + unfold FactorExtractOrigin.
      split; [exact Hprime |].
      rewrite Z.pow_0_r, Z.mul_1_r.
      exact Hprofile.
Qed.
Lemma chain_tail__search_transitions :
  forall a l,
    (forall i, 0 <= i < Zlength (a :: l) - 1 ->
      (Znth i (a :: l) 0 | Znth (i + 1) (a :: l) 0)) ->
    forall i, 0 <= i < Zlength l - 1 ->
      (Znth i l 0 | Znth (i + 1) l 0).
Proof.
  intros a l Hchain i Hi.
  specialize (Hchain (i + 1)).
  rewrite Zlength_cons in Hchain.
  assert (0 <= i + 1 < Z.succ (Zlength l) - 1) by lia.
  specialize (Hchain H).
  rewrite !Znth_cons in Hchain by lia.
  replace (i + 1 - 1) with i in Hchain by lia.
  replace (i + 1 + 1 - 1) with (i + 1) in Hchain by lia.
  exact Hchain.
Qed.
Lemma chain_head_divides_all__search_transitions :
  forall a l,
    (forall i, 0 <= i < Zlength (a :: l) - 1 ->
      (Znth i (a :: l) 0 | Znth (i + 1) (a :: l) 0)) ->
    Forall (fun x => (a | x)) (a :: l).
Proof.
  intros a l. revert a.
  induction l as [|b l IH]; intros a Hchain.
  - constructor; [apply Z.divide_refl | constructor].
  - assert (Hab : (a | b)).
    { specialize (Hchain 0).
      rewrite Zlength_cons in Hchain.
      apply Hchain; clear Hchain.
      rewrite Zlength_cons. pose proof (Zlength_nonneg l). lia. }
    assert (Htail : forall i, 0 <= i < Zlength (b :: l) - 1 ->
      (Znth i (b :: l) 0 | Znth (i + 1) (b :: l) 0)).
    { apply chain_tail__search_transitions with (a := a). exact Hchain. }
    pose proof (IH b Htail) as Hall.
    constructor; [apply Z.divide_refl |].
    eapply Forall_impl; [|exact Hall].
    intros x Hbx. eapply Z.divide_trans; eauto.
Qed.
Lemma pow_Zlength_divides_product__search_transitions :
  forall q l,
    Forall (fun x => (q | x)) l ->
    (Z.pow q (Zlength l) | fold_right Z.mul 1 l).
Proof.
  intros q l Hall.
  induction Hall as [|x l Hqx Hall IH].
  - simpl. apply Z.divide_refl.
  - destruct Hqx as [u Hu].
    destruct IH as [v Hv].
    exists (u * v).
    rewrite Zlength_cons, Z.pow_succ_r by apply Zlength_nonneg.
    simpl. rewrite Hu, Hv. ring.
Qed.
Lemma fold_mul_repeat__search_transitions :
  forall x k acc,
    fold_right Z.mul acc (repeat x k) =
      Z.pow x (Z.of_nat k) * acc.
Proof.
  intros x k acc. rewrite <- Zpower_nat_Z.
  induction k as [|k IH]; simpl.
  - destruct acc; reflexivity.
  - rewrite IH. ring.
Qed.
Lemma valid_repeat_last__search_transitions :
  forall bp c k,
    2 <= bp ->
    1 <= c ->
    ValidFactorSequence (Z.pow bp (Z.of_nat (S k)) * c)
      (repeat bp k ++ [bp * c]).
Proof.
  intros bp c k Hbp Hc.
  assert (Hplen : Zlength (repeat bp k) = Z.of_nat k).
  { rewrite Zlength_correct, repeat_length. reflexivity. }
  unfold ValidFactorSequence.
  repeat split.
  - rewrite Zlength_app, Hplen, Zlength_cons, Zlength_nil. lia.
  - apply Forall_app. split.
    + apply Forall_forall. intros x Hx.
      apply repeat_spec in Hx. subst x. lia.
    + constructor; [nia | constructor].
  - rewrite fold_right_app.
    change (fold_right Z.mul (bp * c * 1) (repeat bp k) =
      Z.pow bp (Z.of_nat (S k)) * c).
    rewrite fold_mul_repeat__search_transitions.
    rewrite Z.mul_1_r.
    rewrite <- Zpower_nat_Z with (n := k).
    rewrite <- Zpower_nat_Z with (n := S k).
    simpl.
    ring.
  - intros i Hi.
    rewrite Zlength_app, Hplen, Zlength_cons, Zlength_nil in Hi.
    rewrite app_Znth1 by (rewrite Hplen; lia).
    rewrite Znth_repeat_lt by lia.
    destruct (Z_lt_ge_dec (i + 1) (Z.of_nat k)) as [Hin | Hlast].
    + rewrite app_Znth1 by (rewrite Hplen; lia).
      rewrite Znth_repeat_lt by lia. apply Z.divide_refl.
    + rewrite app_Znth2 by (rewrite Hplen; lia).
      rewrite Hplen.
      assert (i + 1 = Z.of_nat k) by lia.
      rewrite H.
      replace (Z.of_nat k - Z.of_nat k) with 0 by lia.
      rewrite Znth0_cons. exists c. ring.
Qed.
Lemma best_power_choice_of_global_bound__search_transitions :
  forall n best_prime best_exp,
    2 <= n <= 10000000000 ->
    1 <= best_exp <= 64 ->
    2 <= best_prime <= n ->
    Z.divide (Z.pow best_prime best_exp) n ->
    (forall q k,
      2 <= q ->
      1 <= k ->
      Z.divide (Z.pow q k) n ->
      k <= best_exp) ->
    BestPowerChoice n best_prime best_exp.
Proof.
  intros n best_prime best_exp Hn Hexp Hprime Hbest_div Hglobal.
  destruct Hbest_div as [c Hfactor].
  assert (Hpowpos : 0 < Z.pow best_prime best_exp).
  { apply Z.pow_pos_nonneg; lia. }
  assert (Hc : 1 <= c) by nia.
  set (k := Z.to_nat (best_exp - 1)).
  set (result := repeat best_prime k ++ [best_prime * c]).
  assert (Hk : Z.of_nat k = best_exp - 1).
  { unfold k. apply Z2Nat.id. lia. }
  assert (Hks : Z.of_nat (S k) = best_exp).
  { rewrite Nat2Z.inj_succ, Hk. lia. }
  assert (Hresult_len : Zlength result = best_exp).
  { unfold result. rewrite Zlength_app, Zlength_correct, repeat_length,
      Zlength_cons, Zlength_nil, Hk. lia. }
  assert (Hresult_valid : ValidFactorSequence n result).
  { rewrite Hfactor.
    replace best_exp with (Z.of_nat (S k)) by exact Hks.
    rewrite Z.mul_comm with (n := c)
      (m := Z.pow best_prime (Z.of_nat (S k))).
    unfold result.
    apply valid_repeat_last__search_transitions; lia. }
  unfold BestPowerChoice.
  repeat split; try lia.
  exists result.
  split; [exact Hresult_len |].
  split.
  - intros i Hi.
    unfold result.
    rewrite app_Znth1.
    + apply Znth_repeat_lt. lia.
    + rewrite Zlength_correct, repeat_length, Hk. lia.
  - split; [exact Hresult_valid |].
    unfold Spec. split; [exact Hresult_valid |].
    unfold MaxMin.max_value_of_subset, MaxMin.max_object_of_subset.
    exists result. split.
    + split; [exact Hresult_valid |].
      intros candidate Hcandidate.
      destruct Hcandidate as
        (Hcandidate_len & Hcandidate_pos & Hcandidate_prod & Hcandidate_chain).
      destruct candidate as [|x tail].
      { rewrite Zlength_nil in Hcandidate_len. lia. }
      assert (Hx : 2 <= x).
      { inversion Hcandidate_pos; lia. }
      assert (Hpower_div :
        Z.divide (Z.pow x (Zlength (x :: tail))) n).
      { rewrite <- Hcandidate_prod.
        apply pow_Zlength_divides_product__search_transitions.
        apply chain_head_divides_all__search_transitions.
        exact Hcandidate_chain. }
      specialize (Hglobal x (Zlength (x :: tail)) Hx
        ltac:(rewrite Zlength_cons; pose proof (Zlength_nonneg tail); lia)
        Hpower_div).
      rewrite Hresult_len. exact Hglobal.
    + reflexivity.
Qed.
Lemma pow_divide_pow__extraction_lifecycle :
  forall a b k,
    0 <= k ->
    Z.divide a b ->
    Z.divide (Z.pow a k) (Z.pow b k).
Proof.
  intros a b k Hk [c Hc].
  exists (Z.pow c k).
  rewrite Hc, Z.pow_mul_l by exact Hk.
  ring.
Qed.
Lemma prime_power_exponent_bound__extraction_lifecycle :
  forall p value k e,
    prime p ->
    ~ Z.divide p value ->
    0 <= e ->
    1 <= k ->
    Z.divide (Z.pow p k) (value * Z.pow p e) ->
    k <= e.
Proof.
  intros p value k e Hprime Hnot_div He Hk Hdiv.
  destruct (Z_le_gt_dec k e) as [Hle | Hgt]; [exact Hle |].
  assert (Hp : 2 <= p) by (apply prime_ge_2; exact Hprime).
  assert (Hpow_e_pos : 0 < Z.pow p e).
  { apply Z.pow_pos_nonneg; lia. }
  assert (Hstep_div : Z.divide (Z.pow p (e + 1)) (Z.pow p k)).
  { exists (Z.pow p (k - (e + 1))).
    rewrite <- Z.pow_add_r by lia.
    f_equal. lia. }
  assert (Hlarge_div :
      Z.divide (Z.pow p (e + 1)) (value * Z.pow p e)).
  { eapply Z.divide_trans; eauto. }
  destruct Hlarge_div as [c Hc].
  exfalso. apply Hnot_div.
  exists c.
  replace (e + 1) with (Z.succ e) in Hc by lia.
  rewrite Z.pow_succ_r in Hc by lia.
  apply Z.mul_reg_r with (p := Z.pow p e).
  - lia.
  - rewrite Hc. ring.
Qed.
Lemma factor_extract_successor_profile_build__extraction_lifecycle :
  forall n value p e best_prime best_exp ps es next_prime next_exp,
    value mod p <> 0 ->
    1 <= e ->
    FactorExtractGuard value p e ->
    FactorExtractState n value p e best_prime best_exp ->
    FactorExtractOrigin n value p e best_prime best_exp ps es ->
    best_exp <= next_exp ->
    e <= next_exp ->
    1 <= next_exp <= 64 ->
    2 <= next_prime <= n ->
    Z.divide (Z.pow next_prime next_exp) n ->
    (next_exp = 1 \/
      exists i, 0 <= i < Zlength (es ++ [e]) /\
        Znth i (ps ++ [p]) 1 = next_prime /\
        Znth i (es ++ [e]) 0 = next_exp) ->
    FactorSearchProfile n value (p + 1) next_prime next_exp
      (ps ++ [p]) (es ++ [e]).
Proof.
  intros n value p e best_prime best_exp ps es next_prime next_exp
    Hmod He Hguard Hstate Horigin Hbest_le He_le Hnext_exp
    Hnext_prime Hnext_div Hnext_attained.
  pose proof Hstate as Hstate_data.
  unfold FactorExtractState in Hstate_data.
  destruct Hstate_data as
    (Hn & Hvalue & Hp & He_bounds & Hbest_exp & Hbest_prime &
     Hscale_div & Hbest_div).
  pose proof Horigin as Horigin_data.
  unfold FactorExtractOrigin in Horigin_data.
  destruct Horigin_data as (Hprime & Hsearch).
  pose proof Hsearch as Hsearch_data.
  unfold FactorSearchProfile in Hsearch_data.
  destruct Hsearch_data as
    (Hsearch_state & Hshape & Hfactor & Hnondividing & Hes_bound &
     Hbest_attained & Hfuture & Hat_candidate & Hnext_bound & Hfinish).
  pose proof Hsearch_state as Hsearch_state_data.
  unfold FactorSearchState in Hsearch_state_data.
  destruct Hsearch_state_data as
    (_ & _ & _ & _ & _ & _ & _ & _ & Hpast).
  destruct Hshape as
    (Hlen & Hnodup & Hprimes & Hprime_bounds & Hexps).
  assert (Hp_not_div_value : ~ Z.divide p value).
  { intro Hpdiv.
    apply Hmod.
    apply (proj2 (Z.mod_divide value p ltac:(lia))).
    exact Hpdiv. }
  assert (Hshape_original : FactorProfileShape p ps es).
  { unfold FactorProfileShape.
    split; [exact Hlen |].
    split; [exact Hnodup |].
    split; [exact Hprimes |].
    split; [exact Hprime_bounds | exact Hexps]. }
  assert (Hproduct_positive : 1 <= FactorProfileProduct ps es).
  { apply FactorProfileProduct_positive__search_initialization with p.
    exact Hshape_original. }
  assert (Hp_le_n : p <= n).
  { unfold FactorExtractGuard in Hguard. nia. }
  assert (Hp_not_100001 : p <> 100001).
  { intro Heq. subst p.
    pose proof (prime_divisors 100001 Hprime 11) as Hdivisors.
    specialize (Hdivisors ltac:(exists 9091; ring)).
    lia. }
  assert (Hp_not_100000 : p <> 100000).
  { intro Heq. subst p.
    pose proof (prime_divisors 100000 Hprime 2) as Hdivisors.
    specialize (Hdivisors ltac:(exists 50000; ring)).
    lia. }
  assert (Hp_next : p + 1 <= 100001) by lia.
  assert (Hp_after_next : p + 2 <= 100001) by lia.
  assert (Hvalue_div : Z.divide value n).
  { eapply Z.divide_trans; [|exact Hscale_div].
    exists (Z.pow p e). ring. }
  assert (Hpower_bound_at_p :
      forall k,
        1 <= k ->
        Z.divide (Z.pow p k) n ->
        k <= next_exp).
  { intros k Hk Hpower_div.
    destruct (Hfuture p k ltac:(lia) Hk Hpower_div)
      as [Hbound | Htotal_div].
    - lia.
    - pose proof (prime_power_exponent_bound__extraction_lifecycle
        p value k e Hprime Hp_not_div_value ltac:(lia) Hk Htotal_div).
      lia. }
  assert (Hpast_next :
      forall q k,
        2 <= q < p + 1 ->
        1 <= k ->
        Z.divide (Z.pow q k) n ->
        k <= next_exp).
  { intros q k Hq Hk Hpower_div.
    destruct (Z_lt_ge_dec q p) as [Hlt | Hge].
    - pose proof (Hpast q k ltac:(lia) Hk Hpower_div). lia.
    - assert (q = p) by lia. subst q.
      apply Hpower_bound_at_p; assumption. }
  assert (Hstate_next :
      FactorSearchState n value (p + 1) next_prime next_exp).
  { unfold FactorSearchState.
    split; [exact Hn |].
    split; [exact Hvalue |].
    split; [lia |].
    split; [nia |].
    split; [exact Hnext_exp |].
    split; [exact Hnext_prime |].
    split; [exact Hvalue_div |].
    split; [exact Hnext_div | exact Hpast_next]. }
  assert (Hshape_next :
      FactorProfileShape (p + 1) (ps ++ [p]) (es ++ [e])).
  { apply FactorProfileShape_app_single__search_initialization.
    - exact Hshape_original.
    - exact Hprime.
    - split; [exact He | lia]. }
  assert (Hfactor_next :
      n = value * FactorProfileProduct (ps ++ [p]) (es ++ [e])).
  { rewrite FactorProfileProduct_app_single__search_initialization by exact Hlen.
    rewrite Hfactor. ring. }
  assert (Hnondividing_next :
      forall q, 2 <= q < p + 1 -> ~ Z.divide q value).
  { intros q Hq Hqdiv.
    destruct (Z_lt_ge_dec q p) as [Hlt | Hge].
    - apply (Hnondividing q ltac:(lia)).
      destruct Hqdiv as [c Hc].
      exists (c * Z.pow p e).
      rewrite Hc. ring.
    - assert (q = p) by lia. subst q.
      exact (Hp_not_div_value Hqdiv). }
  assert (Hexps_next :
      forall i,
        0 <= i < Zlength (es ++ [e]) ->
        Znth i (es ++ [e]) 0 <= next_exp).
  { intros i Hi.
    rewrite Zlength_app_cons in Hi.
    destruct (Z_lt_ge_dec i (Zlength es)) as [Hlt | Hge].
    - rewrite app_Znth1 by lia.
      pose proof (Hes_bound i ltac:(lia)). lia.
    - assert (i = Zlength es) by lia. subst i.
      rewrite app_Znth2 by lia.
      replace (Zlength es - Zlength es) with 0 by lia.
      rewrite Znth0_cons. exact He_le. }
  assert (Hfuture_next :
      forall q k,
        p + 1 <= q ->
        1 <= k ->
        Z.divide (Z.pow q k) n ->
        k <= next_exp \/ Z.divide (Z.pow q k) value).
  { intros q k Hq Hk Hpower_div.
    destruct (Hfuture q k ltac:(lia) Hk Hpower_div)
      as [Hbound | Htotal_div].
    - left. lia.
    - destruct (Zdivide_dec p q) as [Hpq | Hpq].
      + left.
        assert (Hp_power_div :
            Z.divide (Z.pow p k) (value * Z.pow p e)).
        { eapply Z.divide_trans; [|exact Htotal_div].
          apply pow_divide_pow__extraction_lifecycle; [lia | exact Hpq]. }
        pose proof (prime_power_exponent_bound__extraction_lifecycle
          p value k e Hprime Hp_not_div_value ltac:(lia) Hk Hp_power_div).
        lia.
      + right.
        apply (Gauss (Z.pow q k) (Z.pow p e) value).
        * rewrite Z.mul_comm. exact Htotal_div.
        * apply rel_prime_Zpower; [lia | lia |].
          apply rel_prime_sym.
          apply prime_rel_prime; assumption. }
  assert (Hat_candidate_next :
      value mod (p + 1) <> 0 ->
      forall k,
        1 <= k ->
        Z.divide (Z.pow (p + 1) k) n ->
        k <= next_exp).
  { intros Hmod_next k Hk Hpower_div.
    destruct (Hfuture_next (p + 1) k ltac:(lia) Hk Hpower_div)
      as [Hbound | Hvalue_power]; [exact Hbound |].
    exfalso. apply Hmod_next.
    apply (proj2 (Z.mod_divide value (p + 1) ltac:(lia))).
    eapply Z.divide_trans; [|exact Hvalue_power].
    exact (Zpower_divide (p + 1) k ltac:(lia)). }
  assert (Hfinish_next :
      (p + 1) * (p + 1) > value ->
      BestPowerChoice n next_prime next_exp).
  { intros Hcross.
    apply best_power_choice_of_global_bound__search_transitions.
    - exact Hn.
    - exact Hnext_exp.
    - exact Hnext_prime.
    - exact Hnext_div.
    - intros q k Hq Hk Hpower_div.
      destruct (Z_lt_ge_dec q (p + 1)) as [Hlt | Hge].
      + eapply Hpast_next; eauto; lia.
      + destruct (Hfuture_next q k ltac:(lia) Hk Hpower_div)
          as [Hbound | Hvalue_power]; [exact Hbound |].
        destruct (Z_le_gt_dec k 1) as [Hone | Htwo]; [lia |].
        assert (Hpower_positive : 0 < Z.pow q k).
        { apply Z.pow_pos_nonneg; lia. }
        assert (Hpower_le_value : Z.pow q k <= value).
        { apply Z.divide_pos_le; [lia | exact Hvalue_power]. }
        assert (Hsquare_le_power : q * q <= Z.pow q k).
        { replace (q * q) with (Z.pow q 2) by ring.
          apply Z.pow_le_mono_r; lia. }
        nia. }
  unfold FactorSearchProfile.
  split; [exact Hstate_next |].
  split; [exact Hshape_next |].
  split; [exact Hfactor_next |].
  split; [exact Hnondividing_next |].
  split; [exact Hexps_next |].
  split; [exact Hnext_attained |].
  split; [exact Hfuture_next |].
  split; [exact Hat_candidate_next |].
  split.
  - intros _. lia.
  - exact Hfinish_next.
Qed.
Lemma factor_extract_successor_profiles__extraction_lifecycle :
  forall n value p e best_prime best_exp ps es,
    value mod p <> 0 ->
    1 <= e ->
    FactorExtractGuard value p e ->
    FactorExtractState n value p e best_prime best_exp ->
    FactorExtractOrigin n value p e best_prime best_exp ps es ->
    (e > best_exp ->
      FactorSearchProfile n value (p + 1) p e
        (ps ++ [p]) (es ++ [e])) /\
    (e <= best_exp ->
      FactorSearchProfile n value (p + 1) best_prime best_exp
        (ps ++ [p]) (es ++ [e])).
Proof.
  intros n value p e best_prime best_exp ps es
    Hmod He Hguard Hstate Horigin.
  pose proof Hstate as Hstate_data.
  unfold FactorExtractState in Hstate_data.
  destruct Hstate_data as
    (Hn & Hvalue & Hp & He_bounds & Hbest_exp & Hbest_prime &
     Hscale_div & Hbest_div).
  pose proof Horigin as Horigin_data.
  unfold FactorExtractOrigin in Horigin_data.
  destruct Horigin_data as (Hprime & Hsearch).
  pose proof Hsearch as Hsearch_data.
  unfold FactorSearchProfile in Hsearch_data.
  destruct Hsearch_data as
    (Hsearch_state & Hshape & Hfactor & Hnondividing & Hes_bound &
     Hbest_attained & Hfuture & Hat_candidate & Hnext_bound & Hfinish).
  unfold FactorProfileShape in Hshape.
  destruct Hshape as (Hlen & Hnodup & Hprimes & Hprime_bounds & Hexps).
  assert (Hp_power_div : Z.divide (Z.pow p e) n).
  { eapply Z.divide_trans; [|exact Hscale_div].
    exists value. ring. }
  assert (Hproduct_positive : 1 <= FactorProfileProduct ps es).
  { apply FactorProfileProduct_positive__search_initialization with p.
    unfold FactorProfileShape.
    split; [exact Hlen |].
    split; [exact Hnodup |].
    split; [exact Hprimes |].
    split; [exact Hprime_bounds | exact Hexps]. }
  assert (Hp_le_n : p <= n).
  { unfold FactorExtractGuard in Hguard. nia. }
  split.
  - intros Hgt.
    apply factor_extract_successor_profile_build__extraction_lifecycle
      with (best_prime := best_prime) (best_exp := best_exp).
    + exact Hmod.
    + exact He.
    + exact Hguard.
    + exact Hstate.
    + exact Horigin.
    + lia.
    + lia.
    + split; [exact He | lia].
    + split; [pose proof (prime_ge_2 _ Hprime); lia | exact Hp_le_n].
    + exact Hp_power_div.
    + right. exists (Zlength es).
      split.
      * rewrite Zlength_app_cons. pose proof (Zlength_nonneg es). lia.
      * split.
        -- rewrite app_Znth2 by lia.
           rewrite Hlen.
           replace (Zlength es - Zlength es) with 0 by lia.
           rewrite Znth0_cons. reflexivity.
        -- rewrite app_Znth2 by lia.
           replace (Zlength es - Zlength es) with 0 by lia.
           rewrite Znth0_cons. reflexivity.
  - intros Hle.
    apply factor_extract_successor_profile_build__extraction_lifecycle
      with (best_prime := best_prime) (best_exp := best_exp).
    + exact Hmod.
    + exact He.
    + exact Hguard.
    + exact Hstate.
    + exact Horigin.
    + lia.
    + exact Hle.
    + exact Hbest_exp.
    + exact Hbest_prime.
    + exact Hbest_div.
    + destruct Hbest_attained as [Hone | Hattained].
      * left. exact Hone.
      * right.
        destruct Hattained as (i & Hi & Hprime_i & Hexp_i).
        exists i. split.
        -- rewrite Zlength_app_cons. lia.
        -- split.
           ++ rewrite app_Znth1 by lia. exact Hprime_i.
           ++ rewrite app_Znth1 by lia. exact Hexp_i.
Qed.
Lemma factor_search_profile_skip__search_transitions :
  forall n value p best_prime best_exp ps es,
    value mod p <> 0 ->
    p * p <= value ->
    FactorSearchProfile n value p best_prime best_exp ps es ->
    FactorSearchProfile n value (p + 1) best_prime best_exp ps es.
Proof.
  intros n value p best_prime best_exp ps es Hmod Hguard Hprofile.
  unfold FactorSearchProfile in Hprofile.
  destruct Hprofile as
    (Hstate & Hshape & Hfactor & Hnodiv & Hexp_bound & Hmax &
     Hfuture & Hp_power & Hp_next & Hterminal).
  unfold FactorSearchState in Hstate.
  destruct Hstate as
    (Hn & Hvalue & Hp & Hpsquare & Hbest_exp & Hbest_prime &
     Hvalue_div & Hbest_div & Hpast).
  assert (Hp_not_div : ~ Z.divide p value).
  { intro Hpdiv. apply Hmod.
    apply (proj2 (Z.mod_divide value p ltac:(lia))). exact Hpdiv. }
  assert (Hnext : p + 1 <= 100001) by (apply Hp_next; exact Hmod).
  assert (Hnext_square :
    (p + 1) * (p + 1) <= 1000000000000000000) by nia.
  assert (Hstate_next :
    FactorSearchState n value (p + 1) best_prime best_exp).
  { unfold FactorSearchState.
    repeat split; try lia; try assumption.
    intros q k Hq Hk Hqdiv.
    destruct (Z_lt_ge_dec q p) as [Hlt | Hge].
    - eapply Hpast; eauto; lia.
    - assert (q = p) by lia. subst q.
      apply Hp_power; assumption. }
  assert (Hshape_next : FactorProfileShape (p + 1) ps es).
  { unfold FactorProfileShape in *.
    destruct Hshape as (Hlen & Hnodup & Hprimes & Hprime_bounds & Hexps).
    refine (conj Hlen (conj Hnodup (conj Hprimes (conj _ Hexps)))).
    intros j Hj. specialize (Hprime_bounds j Hj). lia. }
  assert (Hnodiv_next :
    forall q, 2 <= q < p + 1 -> ~ Z.divide q value).
  { intros q Hq.
    destruct (Z_lt_ge_dec q p) as [Hlt | Hge].
    + apply Hnodiv. lia.
    + assert (q = p) by lia. subst q. exact Hp_not_div. }
  assert (Hfuture_next :
    forall q k,
      p + 1 <= q ->
      1 <= k ->
      Z.divide (Z.pow q k) n ->
      k <= best_exp \/ Z.divide (Z.pow q k) value).
  { intros q k Hq Hk Hqdiv.
    exact (Hfuture q k ltac:(lia) Hk Hqdiv). }
  assert (Hpower_next :
    value mod (p + 1) <> 0 ->
    forall k,
      1 <= k -> Z.divide (Z.pow (p + 1) k) n -> k <= best_exp).
  { intros Hmod_next k Hk Hqdiv.
    destruct (Hfuture (p + 1) k ltac:(lia) Hk Hqdiv)
      as [Hbound | Hpow_value]; [exact Hbound |].
    exfalso. apply Hmod_next.
    apply (proj2 (Z.mod_divide value (p + 1) ltac:(lia))).
    eapply Z.divide_trans; [|exact Hpow_value].
    replace k with (Z.succ (k - 1)) by lia.
    rewrite Z.pow_succ_r by lia.
    apply Z.divide_factor_l. }
  assert (Hbound_next :
    value mod (p + 1) <> 0 -> p + 1 + 1 <= 100001).
  { intros _.
    assert (p <= 99999).
    { destruct (Z_le_gt_dec p 99999) as [Hsmall | Hlarge];
        [exact Hsmall | exfalso].
      assert (p = 100000) by lia. subst p.
      apply Hmod.
      apply (proj2 (Z.mod_divide value 100000 ltac:(lia))).
      exists 100000. nia. }
    lia. }
  assert (Hterminal_next :
    (p + 1) * (p + 1) > value ->
    BestPowerChoice n best_prime best_exp).
  { intros Hcross.
    apply best_power_choice_of_global_bound__search_transitions.
    + exact Hn.
    + exact Hbest_exp.
    + exact Hbest_prime.
    + exact Hbest_div.
    + intros q k Hq Hk Hqdiv.
      destruct (Z_lt_ge_dec q p) as [Hlt | Hge].
      * eapply Hpast; eauto; lia.
      * destruct (Hfuture q k ltac:(lia) Hk Hqdiv)
          as [Hbound | Hpow_value]; [exact Hbound |].
        destruct (Z_le_gt_dec k best_exp) as [Hbound | Hlarge];
          [exact Hbound |].
        destruct (Z.eq_dec q p) as [Heq | Hneq].
        -- subst q. exfalso. apply Hp_not_div.
           eapply Z.divide_trans; [|exact Hpow_value].
           replace k with (Z.succ (k - 1)) by lia.
           rewrite Z.pow_succ_r by lia.
           apply Z.divide_factor_l.
        -- assert (p + 1 <= q) by lia.
           assert (Hpow_positive : 0 < Z.pow q k).
           { apply Z.pow_pos_nonneg; lia. }
           assert (Hpow_le_value : Z.pow q k <= value).
           { apply Z.divide_pos_le; [lia | exact Hpow_value]. }
           assert (Hsquare_le_pow : q * q <= Z.pow q k).
           { replace (q * q) with (Z.pow q 2) by ring.
             apply Z.pow_le_mono_r; lia. }
           assert ((p + 1) * (p + 1) <= q * q) by nia.
           nia. }
  unfold FactorSearchProfile.
  apply conj; [exact Hstate_next |].
  apply conj; [exact Hshape_next |].
  apply conj; [exact Hfactor |].
  apply conj; [exact Hnodiv_next |].
  apply conj; [exact Hexp_bound |].
  apply conj; [exact Hmax |].
  apply conj; [exact Hfuture_next |].
  apply conj; [exact Hpower_next |].
  apply conj; [exact Hbound_next | exact Hterminal_next].
Qed.
Lemma fold_mul_prefix_factor__output_construction :
  forall (l : list Z) x k,
    0 <= k <= Zlength l ->
    (forall j, 0 <= j < k -> Znth j l 0 = x) ->
    exists q, fold_right Z.mul 1 l = Z.pow x k * q.
Proof.
  intros l x k Hk Hprefix.
  remember (Z.to_nat k) as m eqn:Hm.
  assert (Hk_nat : k = Z.of_nat m) by lia.
  rewrite Hk_nat in Hk, Hprefix |- *.
  clear k Hk_nat Hm.
  revert l Hk Hprefix.
  induction m as [|m IH]; intros l Hk Hprefix.
  - exists (fold_right Z.mul 1 l).
    rewrite Z.pow_0_r, Z.mul_1_l. reflexivity.
  - destruct l as [|a l].
    + rewrite Zlength_nil in Hk. lia.
    + assert (Ha : a = x).
      { specialize (Hprefix 0 ltac:(lia)).
        rewrite Znth0_cons in Hprefix.
        exact Hprefix. }
      assert (Htail_len : 0 <= Z.of_nat m <= Zlength l).
      { rewrite Zlength_cons in Hk. lia. }
      assert (Htail_prefix :
          forall j, 0 <= j < Z.of_nat m -> Znth j l 0 = x).
      { intros j Hj.
        specialize (Hprefix (j + 1) ltac:(lia)).
        rewrite Znth_cons in Hprefix by lia.
        replace (j + 1 - 1) with j in Hprefix by lia.
        exact Hprefix. }
      destruct (IH l Htail_len Htail_prefix) as (q & Hfactor).
      exists q.
      change (a * fold_right Z.mul 1 l = Z.pow x (Z.of_nat (S m)) * q).
      rewrite Ha, Hfactor, Nat2Z.inj_succ.
      rewrite Z.pow_succ_r by lia.
      ring.
Qed.
Lemma output_prefix_step__output_construction :
  forall n best_prime best_exp i rest written,
    i + 1 < best_exp ->
    OutputPrefixState n best_prime best_exp i rest written ->
    OutputPrefixState n best_prime best_exp (i + 1) (rest / best_prime)
      (written ++ [best_prime]) /\
    rest / best_prime <= n /\
    1 <= rest / best_prime.
Proof.
  intros n best_prime best_exp i rest written Hnext Hstate.
  destruct Hstate as
    (Hchoice & Hi & Hrest & Hwritten_len & Hwritten_prefix & Hproduct).
  pose proof Hchoice as Hchoice_data.
  unfold BestPowerChoice in Hchoice_data.
  destruct Hchoice_data as
    (Hn & Hbest_exp & Hbest_prime & result & Hresult_len &
     Hresult_prefix & Hvalid & Hspec).
  destruct Hvalid as (Hresult_nonempty & Hresult_entries & Hresult_product & Hchain).
  destruct (fold_mul_prefix_factor__output_construction
      result best_prime (i + 1)) as (q & Hfactor).
  - rewrite Hresult_len. lia.
  - intros j Hj. apply Hresult_prefix. lia.
  - rewrite Hresult_product in Hfactor.
    assert (Hpow_pos : 0 < Z.pow best_prime i).
    { apply Z.pow_pos_nonneg; lia. }
    replace (i + 1) with (Z.succ i) in Hfactor by lia.
    rewrite Z.pow_succ_r in Hfactor by lia.
    assert (Hrest_eq : rest = best_prime * q) by nia.
    assert (Hquot : rest / best_prime = q).
    { rewrite Hrest_eq, Z.mul_comm, Z.div_mul by lia. reflexivity. }
    assert (Hqpos : 1 <= q) by nia.
    assert (Hqbound : q <= n) by nia.
    split.
    + unfold OutputPrefixState.
      split; [exact Hchoice |].
      split; [lia |].
      split; [rewrite Hquot; lia |].
      split.
      * rewrite Zlength_app, Zlength_cons, Zlength_nil, Hwritten_len. lia.
      * split.
        -- intros j Hj.
           destruct (Z_lt_ge_dec j i) as [Hji | Hji].
           ++ rewrite app_Znth1 by lia. apply Hwritten_prefix. lia.
           ++ assert (j = i) by lia. subst j.
              rewrite app_Znth2 by lia.
              rewrite Hwritten_len.
              replace (i - i) with 0 by lia.
              apply Znth0_cons.
        -- rewrite Hquot.
           replace (i + 1) with (Z.succ i) by lia.
           rewrite Z.pow_succ_r by lia.
           nia.
    + rewrite Hquot. split; assumption.
Qed.
Lemma uniform_fold_power__final_result :
  forall (l : list Z) p acc,
    (forall j, 0 <= j < Zlength l -> Znth j l 0 = p) ->
    fold_right Z.mul acc l = Z.pow p (Zlength l) * acc.
Proof.
  intros l.
  induction l as [|a l IH]; intros p acc Huniform.
  - cbn [fold_right].
    rewrite Zlength_nil, Z.pow_0_r, Z.mul_1_l.
    reflexivity.
  - pose proof (Zlength_nonneg l) as Hlen_nonneg.
    assert (Ha : a = p).
    { specialize (Huniform 0 ltac:(rewrite Zlength_cons; lia)).
      rewrite Znth0_cons in Huniform.
      exact Huniform. }
    subst a.
    assert (Htail : forall j, 0 <= j < Zlength l -> Znth j l 0 = p).
    { intros j Hj.
      specialize (Huniform (j + 1) ltac:(rewrite Zlength_cons; lia)).
      rewrite Znth_cons in Huniform by lia.
      replace (j + 1 - 1) with j in Huniform by lia.
      exact Huniform. }
    simpl.
    rewrite (IH p acc Htail).
    rewrite Zlength_cons.
    replace (1 + Zlength l) with (Z.succ (Zlength l)) by lia.
    rewrite Z.pow_succ_r by apply Zlength_nonneg.
    ring.
Qed.
Lemma final_output_from_prefix__final_result :
  forall n best_prime best_exp rest written,
    BestPowerChoice n best_prime best_exp ->
    OutputPrefixState n best_prime best_exp (best_exp - 1) rest written ->
    FinalOutputSequence n best_prime best_exp rest (written ++ [rest]) /\
    Spec n (written ++ [rest]).
Proof.
  intros n best_prime best_exp rest written Hchoice Hprefix.
  pose proof Hchoice as Hchoice_data.
  unfold BestPowerChoice in Hchoice_data.
  destruct Hchoice_data as
    (Hn & Hbest_exp & Hbest_prime & result & Hresult_len &
     Hresult_prefix & Hresult_valid & Hresult_spec).
  pose proof (proj1 Hbest_exp) as Hbest_exp_lo.
  pose proof (proj2 Hbest_exp) as Hbest_exp_hi.
  pose proof Hprefix as Hprefix_data.
  unfold OutputPrefixState in Hprefix_data.
  destruct Hprefix_data as
    (_ & Hindex & Hrest & Hwritten_len & Hwritten_prefix & Hproduct).
  destruct (list_snoc_destruct result) as [Hnil | (last & result_prefix & Hsnoc)].
  - subst result.
    rewrite Zlength_nil in Hresult_len.
    lia.
  - subst result.
    assert (Hresult_prefix_len : Zlength result_prefix = best_exp - 1).
    { rewrite Zlength_app_cons in Hresult_len. lia. }
    assert (Hresult_prefix_uniform :
        forall j, 0 <= j < Zlength result_prefix ->
          Znth j result_prefix 0 = best_prime).
    { intros j Hj.
      specialize (Hresult_prefix j ltac:(lia)).
      rewrite app_Znth1 in Hresult_prefix by lia.
      exact Hresult_prefix. }
    assert (Hprefixes_equal : result_prefix = written).
    { apply (proj2 (list_eq_ext result_prefix written 0)).
      split.
      - lia.
      - intros j Hj.
        rewrite Hresult_prefix_uniform by exact Hj.
        symmetry.
        apply Hwritten_prefix.
        lia. }
    subst result_prefix.
    unfold ValidFactorSequence in Hresult_valid.
    destruct Hresult_valid as
      (Hnonempty & Hfactors & Hresult_product & Hdivides).
    assert (Hwritten_fold :
        fold_right Z.mul last written =
          Z.pow best_prime (best_exp - 1) * last).
    { rewrite (uniform_fold_power__final_result written best_prime last).
      - rewrite Hwritten_len. reflexivity.
      - intros j Hj. apply Hwritten_prefix. lia. }
    rewrite fold_right_app in Hresult_product.
    cbn [fold_right] in Hresult_product.
    rewrite Z.mul_1_r in Hresult_product.
    rewrite Hwritten_fold in Hresult_product.
    assert (Hpow_positive : 0 < Z.pow best_prime (best_exp - 1)).
    { apply Z.pow_pos_nonneg; lia. }
    assert (Hlast : last = rest) by nia.
    subst last.
    split.
    + unfold FinalOutputSequence.
      split; [exact Hchoice |].
      split; [exact Hrest |].
      split.
      * rewrite Zlength_app_cons. lia.
      * split.
        -- intros j Hj.
           rewrite app_Znth1 by lia.
           apply Hwritten_prefix. lia.
        -- split.
           ++ rewrite app_Znth2 by lia.
              rewrite Hwritten_len.
              replace (best_exp - 1 - (best_exp - 1)) with 0 by lia.
              reflexivity.
           ++ split; [exact Hproduct | exact Hresult_spec].
    + exact Hresult_spec.
Qed.
