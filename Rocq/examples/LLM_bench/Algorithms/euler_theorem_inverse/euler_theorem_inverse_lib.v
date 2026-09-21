From Coq Require Import ZArith List.
Import ListNotations.
Local Open Scope Z_scope.

Require Import
  SimpleC.EE.LLM_bench.Algorithms.modular_power.modular_power_lib.

(** The canonical Euler totient is the cardinality of the positive residues
    [1, n] that are coprime to [n].  This finite count is independent of the
    trial-division implementation used by the C program. *)
Require Import AUXLib.ListLib SumLib.ZRange.

Definition EulerTotientValue (n : Z) : Z :=
  Zlength (filter (fun k : Z => Z.eqb (Z.gcd k n) 1) (Zrange 1 (n + 1))).

(** Compatibility with the original counting helpers, whose internal
    natural-number enumeration is retained only for proof reuse. *)
Definition EulerTotientCountLegacy (n : Z) : Z :=
  Z.of_nat
    (length
       (filter
          (fun k : nat => Z.eqb (Z.gcd (Z.of_nat k) n) 1)
          (seq 1 (Z.to_nat n)))).

From Coq Require Import Lia Sorting.Permutation.
Lemma EulerTotientValue_compat n :
  EulerTotientValue n = EulerTotientCountLegacy n.
Proof.
  unfold EulerTotientValue, EulerTotientCountLegacy.
  assert (Henum : Zrange 1 (n + 1) = map Z.of_nat (seq 1 (Z.to_nat n))).
  { unfold Zrange. replace (n + 1 - 1) with n by lia.
    generalize (Z.to_nat n). intros count.
    change 1 with (Z.of_nat 1).
    generalize 1%nat. intros offset.
    revert offset. induction count as [|count IH]; intros offset; cbn [seq map Zrange_aux].
    - reflexivity.
    - f_equal. replace (Z.of_nat offset + 1) with (Z.of_nat (S offset)) by lia.
      apply IH. }
  rewrite Henum, Zlength_correct.
  generalize (seq 1 (Z.to_nat n)); intros l.
  induction l as [|k l IH]; cbn [filter map length]; [reflexivity|].
  destruct (Z.eqb (Z.gcd (Z.of_nat k) n) 1); cbn [length].
  - rewrite !Nat2Z.inj_succ. f_equal. exact IH.
  - exact IH.
Qed.

Definition EulerPhi (n result : Z) : Prop :=
  result = EulerTotientValue n.

(** The public result states the inverse equation, independently of the
    totient computation and modular exponentiation used to obtain it. *)
Definition EulerTheoremInverse
    (value modulus inverse : Z) : Prop :=
  (value * inverse) mod modulus = 1.

(** The residual state isolates the mathematical work still carried by the
    unprocessed factor [remaining].  Besides the totient identity, divisibility
    records the accumulator's reachable factorization shape: every unprocessed
    factor still present in [remaining] is also present in [result]. *)
Definition EulerPhiResidual
    (original remaining result : Z) : Prop :=
  Z.divide remaining result /\
  forall original_phi remaining_phi,
    EulerPhi original original_phi ->
    EulerPhi remaining remaining_phi ->
    original_phi * remaining = result * remaining_phi.

(** Mathematical primality, stated without extending the spec-stage import
    surface. *)
Definition EulerPrime (p : Z) : Prop :=
  1 < p /\
  forall d,
    0 < d ->
    Z.divide d p ->
    d = 1 \/ d = p.

(** No prime below the trial-division frontier remains in the residual. *)
Definition NoPrimeDivisorBelow (frontier remaining : Z) : Prop :=
  forall p,
    EulerPrime p ->
    p < frontier ->
    ~ Z.divide p remaining.

(** Stable mathematical meaning of the outer factor scan.  The residual state
    carries both reachability/divisibility and totient semantics; runtime
    ranges and multiplication safety deliberately remain in the C invariant. *)
Definition EulerPhiProgress
    (original frontier remaining result : Z) : Prop :=
  EulerPhiResidual original remaining result /\
  NoPrimeDivisorBelow frontier remaining.

(** Semantic completion interface for one prime-removal phase.  It quantifies
    every factor-free terminal reachable from [current] by removing a
    nonnegative power of [factor].  This descendant-closed formulation is
    preserved by exact division and supplies the canonical totient transition
    at loop exit. *)
Definition EulerPhiFactorCompletion
    (original factor current result : Z) : Prop :=
  forall terminal removed,
    0 <= removed ->
    current = terminal * factor ^ removed ->
    terminal mod factor <> 0 ->
    EulerPhiResidual original terminal
      ((result / factor) * (factor - 1)).

(** Proof-only arithmetic support for the structural transport lemmas below. *)
Require Import Coq.micromega.Lia.
Require Import Coq.setoid_ring.Ring.

(** Exact division preserves every terminal descendant: a decomposition of the
    quotient with exponent [removed] is a decomposition of the pre-state with
    exponent [removed + 1]. *)
Lemma EulerPhiFactorCompletion_divide :
  forall original factor current result,
    factor <> 0 ->
    current mod factor = 0 ->
    EulerPhiFactorCompletion original factor current result ->
    EulerPhiFactorCompletion
      original factor (current / factor) result.
Proof.
  intros original factor current result Hfactor Hmod Hcompletion.
  intros terminal removed Hremoved Hquotient Hterminal.
  apply (Hcompletion terminal (Z.succ removed)); try lia.
  pose proof (Z.div_mod current factor Hfactor) as Hdecomp.
  rewrite Hmod in Hdecomp.
  rewrite Hquotient in Hdecomp.
  rewrite Z.pow_succ_r by lia.
  nia.
Qed.

(** While one distinct prime factor is being removed, [before] records the
    outer residual and [removed] records only the mathematical multiplicity
    already stripped from it.  The completion component makes the canonical
    prime-power totient effect explicit rather than asking the exit proof to
    reconstruct a semantic relation absent from the invariant. *)
Definition EulerPhiRemovalProgress
    (original factor current result : Z) : Prop :=
  exists before removed,
    0 <= removed /\
    before = current * factor ^ removed /\
    Z.divide factor before /\
    Z.divide factor result /\
    EulerPhiProgress original factor before result /\
    EulerPhiFactorCompletion original factor current result.

(** The factor-completion phase consumes the invariant's semantic interface by
    choosing the current value itself with exponent zero. *)
Lemma EulerPhiRemovalProgress_complete :
  forall original factor current result,
    EulerPhiRemovalProgress original factor current result ->
    current mod factor <> 0 ->
    EulerPhiResidual original current
      ((result / factor) * (factor - 1)).
Proof.
  intros original factor current result Hprogress Hfree.
  destruct Hprogress as
      [before [removed
        [_ [_ [_ [_ [_ Hcompletion]]]]]]].
  apply (Hcompletion current 0).
  - lia.
  - ring.
  - exact Hfree.
Qed.

(** Stable square-and-multiply state for this case's local helper. *)
Definition EulerModularPowerProgress
    (original_base original_exponent modulus
     current_base remaining_exponent accumulator : Z) : Prop :=
  (accumulator * current_base ^ remaining_exponent) mod modulus =
  (original_base ^ original_exponent) mod modulus.

(** Forward the dependency's public relation to generated clients while
    preserving the frozen [Require Import] dependency row. *)
Notation ModularPower :=
  SimpleC.EE.LLM_bench.Algorithms.modular_power.modular_power_lib.ModularPower
  (only parsing).

From Coq Require Import Lia Psatz ZArith.Znumtheory ZArith.Zpow_facts
  Sorting.Permutation.
From Coq Require Import Lia Psatz ZArith.Znumtheory ZArith.Zquot.
From Coq Require Import ZArith.Znumtheory Sorting.Permutation.
Lemma euler_prime_from_prime__euler_phi_final_results :
  forall p,
    prime p -> EulerPrime p.
Proof.
  intros p Hp.
  pose proof (prime_ge_2 p Hp) as Hp_ge.
  split; [lia |].
  intros d Hdpos Hdivide.
  destruct (prime_divisors p Hp d Hdivide)
    as [Hd | [Hd | [Hd | Hd]]]; subst; lia.
Qed.
Lemma euler_prime_divisor_exists__euler_phi_final_results :
  forall k,
    1 < k ->
    exists q, prime q /\ Z.divide q k.
Proof.
  intros k Hk_initial.
  assert (Hk_nonnegative : 0 <= k) by lia.
  revert Hk_initial.
  pattern k.
  apply Z_lt_induction.
  - intros k0 IH Hk_gt.
    destruct (prime_dec k0) as [Hprime | Hnot_prime].
  + exists k0.
    split; [exact Hprime |].
    exists 1.
    nia.
  + destruct (not_prime_divide k0 Hk_gt Hnot_prime)
      as [d [[Hd_gt Hd_lt] Hd_divide]].
    destruct (IH d ltac:(lia) Hd_gt) as [q [Hq_prime Hq_divide_d]].
    exists q.
    split; [exact Hq_prime |].
    destruct Hq_divide_d as [a Ha].
    destruct Hd_divide as [b Hb].
    exists (a * b).
    nia.
  - exact Hk_nonnegative.
Qed.
Lemma euler_residue_bounds__inverse_final_result :
  forall n k,
    2 <= n ->
    In k
      (filter
         (fun j : nat => Z.eqb (Z.gcd (Z.of_nat j) n) 1)
         (seq 1 (Z.to_nat n))) ->
    1 <= Z.of_nat k < n /\ Z.gcd (Z.of_nat k) n = 1.
Proof.
  intros n k Hn Hin.
  apply filter_In in Hin.
  destruct Hin as [Hin Hcoprime].
  apply in_seq in Hin.
  apply Z.eqb_eq in Hcoprime.
  assert (Hkle : Z.of_nat k <= n).
  {
    rewrite <- (Z2Nat.id n) by lia.
    apply Nat2Z.inj_le.
    lia.
  }
  assert (Hkneq : Z.of_nat k <> n).
  {
    intro Heq.
    rewrite Heq, Z.gcd_diag, Z.abs_eq in Hcoprime by lia.
    lia.
  }
  split.
  - split.
    + change (Z.of_nat 1 <= Z.of_nat k).
      apply Nat2Z.inj_le.
      lia.
    + lia.
  - exact Hcoprime.
Qed.
Lemma euler_factor_prime__euler_phi_setup_removal :
  forall factor value,
    2 <= factor ->
    Z.divide factor value ->
    NoPrimeDivisorBelow factor value ->
    prime factor.
Proof.
  intros factor value Hfactor Hfactor_value Hno_small.
  destruct (prime_dec factor) as [Hprime | Hnot_prime]; [exact Hprime |].
  destruct (not_prime_divide factor ltac:(lia) Hnot_prime)
    as [d [[Hd_gt Hd_lt] Hd_factor]].
  destruct (euler_prime_divisor_exists__euler_phi_final_results d Hd_gt)
    as [q [Hq_prime Hq_d]].
  exfalso.
  apply
    (Hno_small q
       (euler_prime_from_prime__euler_phi_final_results q Hq_prime)).
  - apply Z.divide_pos_le in Hq_d; [lia |].
    apply prime_ge_2 in Hq_prime.
    lia.
  - destruct Hq_d as [a Ha].
    destruct Hd_factor as [b Hb].
    destruct Hfactor_value as [c Hc].
    exists (a * b * c).
    nia.
Qed.
Lemma euler_prime_power_relprime_iff__euler_phi_setup_removal :
  forall p exponent x,
    prime p ->
    1 <= exponent ->
    (Z.gcd x (p ^ exponent) = 1 <-> x mod p <> 0).
Proof.
  intros p exponent x Hp Hexponent.
  pose proof (prime_ge_2 p Hp) as Hp_ge.
  split.
  - intro Hgcd.
    apply Zgcd_1_rel_prime in Hgcd.
    intro Hmod.
    assert (Hp_x : Z.divide p x).
    { apply Z.mod_divide; lia. }
    assert (Hrel_power_x : rel_prime (p ^ exponent) x).
    { apply rel_prime_sym. exact Hgcd. }
    assert (Hrel_p_x : rel_prime p x).
    {
      eapply rel_prime_div; [exact Hrel_power_x |].
      apply Zpower_divide.
      lia.
    }
    destruct (rel_prime_bezout p x Hrel_p_x) as [u v Hbezout].
    destruct Hp_x as [q Hq].
    assert (Hp_one : Z.divide p 1).
    {
      exists (u + v * q).
      rewrite <- Hbezout, Hq.
      ring.
    }
    pose proof (Zdivide_bounds p 1 Hp_one ltac:(lia)) as Hbound.
    rewrite Z.abs_eq in Hbound by lia.
    simpl in Hbound.
    lia.
  - intro Hmod.
    apply Zgcd_1_rel_prime.
    apply rel_prime_Zpower_r; [lia |].
    apply rel_prime_sym.
    apply prime_rel_prime; [exact Hp |].
    intro Hp_x.
    apply Hmod.
    apply Zdivide_mod.
    exact Hp_x.
Qed.
Lemma euler_prime_power_multiple_count__euler_phi_setup_removal :
  forall p exponent,
    prime p ->
    1 <= exponent ->
    length
      (filter
         (fun j : nat => Z.eqb (Z.of_nat j mod p) 0)
         (seq 1 (Z.to_nat (p ^ exponent)))) =
    Z.to_nat (p ^ (exponent - 1)).
Proof.
  intros p exponent Hp Hexponent.
  pose proof (prime_ge_2 p Hp) as Hp_ge.
  assert (Hpower : p ^ exponent = p * p ^ (exponent - 1)).
  {
    replace exponent with ((exponent - 1) + 1) at 1 by lia.
    rewrite Z.pow_add_r by lia.
    rewrite Z.pow_1_r.
    ring.
  }
  transitivity
    (length
       (map
          (fun j : nat => Z.to_nat (p * Z.of_nat j))
          (seq 1 (Z.to_nat (p ^ (exponent - 1)))))).
  2: { rewrite length_map, length_seq. reflexivity. }
  apply Permutation_length.
  apply NoDup_Permutation.
  - apply NoDup_filter.
    apply seq_NoDup.
  - apply NoDup_map_NoDup_ForallPairs.
    + intros x y Hx Hy Heq.
      apply Nat2Z.inj.
      apply (f_equal Z.of_nat) in Heq.
      rewrite !Z2Nat.id in Heq by
        (apply Z.mul_nonneg_nonneg; [lia | apply Nat2Z.is_nonneg]).
      nia.
    + apply seq_NoDup.
  - intros x.
    split.
    + intro Hx.
      apply filter_In in Hx.
      destruct Hx as [Hx_range Hx_mod].
      apply in_seq in Hx_range.
      apply Z.eqb_eq in Hx_mod.
      assert (Hx_bounds : 1 <= Z.of_nat x <= p ^ exponent).
      {
        split.
        - change (Z.of_nat 1 <= Z.of_nat x).
          apply Nat2Z.inj_le.
          lia.
        - rewrite <- (Z2Nat.id (p ^ exponent)) by
            (apply Z.pow_nonneg; lia).
          apply Nat2Z.inj_le.
          lia.
      }
      pose proof (Z.div_mod (Z.of_nat x) p ltac:(lia)) as Hdivision.
      rewrite Hx_mod, Z.add_0_r in Hdivision.
      apply in_map_iff.
      exists (Z.to_nat (Z.of_nat x / p)).
      split.
      * apply Nat2Z.inj.
        rewrite !Z2Nat.id by nia.
        nia.
      * apply in_seq.
        assert (Hquotient : 1 <= Z.of_nat x / p <= p ^ (exponent - 1)).
        {
          split.
          - nia.
          - apply Z.div_le_upper_bound; [lia |].
            rewrite <- Hpower.
            exact (proj2 Hx_bounds).
        }
        split.
        -- apply (proj2 (Nat2Z.inj_le 1 (Z.to_nat (Z.of_nat x / p)))).
           rewrite Z2Nat.id by nia.
           simpl.
           lia.
        -- rewrite <- (Z2Nat.id (p ^ (exponent - 1))) by
             (apply Z.pow_nonneg; lia).
           apply Nat2Z.inj_lt.
           rewrite Z2Nat.id by nia.
           lia.
    + intro Hx.
      apply in_map_iff in Hx.
      destruct Hx as [y [Hxy Hy]].
      subst x.
      apply in_seq in Hy.
      apply filter_In.
      split.
      * apply in_seq.
        assert (Hy_bounds : 1 <= Z.of_nat y <= p ^ (exponent - 1)).
        {
          split.
          - change (Z.of_nat 1 <= Z.of_nat y).
            apply Nat2Z.inj_le.
            lia.
          - rewrite <- (Z2Nat.id (p ^ (exponent - 1))) by
              (apply Z.pow_nonneg; lia).
            apply Nat2Z.inj_le.
            lia.
        }
        assert (Hproduct_bounds :
          1 <= p * Z.of_nat y <= p ^ exponent) by nia.
        split.
        -- apply (proj2 (Nat2Z.inj_le 1 (Z.to_nat (p * Z.of_nat y)))).
           rewrite Z2Nat.id by nia.
           simpl.
           lia.
        -- rewrite <- (Z2Nat.id (p ^ exponent)) by
             (apply Z.pow_nonneg; lia).
           apply Nat2Z.inj_lt.
           rewrite Z2Nat.id by nia.
           lia.
      * apply Z.eqb_eq.
        rewrite Z2Nat.id by
          (apply Z.mul_nonneg_nonneg; [lia | apply Nat2Z.is_nonneg]).
        apply Zdivide_mod.
        exists (Z.of_nat y).
        ring.
Qed.
Lemma euler_totient_prime_power__euler_phi_setup_removal :
  forall p exponent,
    prime p ->
    1 <= exponent ->
    EulerTotientValue (p ^ exponent) =
      p ^ (exponent - 1) * (p - 1).
Proof.
  intros p exponent Hp Hexponent.
  pose proof (prime_ge_2 p Hp) as Hp_ge.
  assert (Hpower : p ^ exponent = p * p ^ (exponent - 1)).
  {
    replace exponent with ((exponent - 1) + 1) at 1 by lia.
    rewrite Z.pow_add_r by lia.
    rewrite Z.pow_1_r.
    ring.
  }
  rewrite !EulerTotientValue_compat. unfold EulerTotientCountLegacy.
  rewrite
    (filter_ext_in
       (fun j : nat => Z.eqb (Z.gcd (Z.of_nat j) (p ^ exponent)) 1)
       (fun j : nat => negb (Z.eqb (Z.of_nat j mod p) 0))
       (seq 1 (Z.to_nat (p ^ exponent)))).
  2: {
    intros x Hx.
    pose proof
      (euler_prime_power_relprime_iff__euler_phi_setup_removal
         p exponent (Z.of_nat x) Hp Hexponent) as Hiff.
    destruct (Z.eqb (Z.gcd (Z.of_nat x) (p ^ exponent)) 1) eqn:Hgcd;
      destruct (Z.eqb (Z.of_nat x mod p) 0) eqn:Hmod; simpl; auto.
    - apply Z.eqb_eq in Hgcd.
      apply Z.eqb_eq in Hmod.
      exfalso.
      apply (proj1 Hiff Hgcd).
      exact Hmod.
    - apply Z.eqb_neq in Hgcd.
      apply Z.eqb_neq in Hmod.
      exfalso.
      apply Hgcd.
      apply (proj2 Hiff Hmod).
  }
  pose proof
    (filter_length
       (fun j : nat => Z.eqb (Z.of_nat j mod p) 0)
       (seq 1 (Z.to_nat (p ^ exponent)))) as Hpartition.
  rewrite
    euler_prime_power_multiple_count__euler_phi_setup_removal
      in Hpartition by assumption.
  rewrite length_seq in Hpartition.
  assert
    (Hlength :
      length
        (filter
           (fun j : nat => negb (Z.eqb (Z.of_nat j mod p) 0))
           (seq 1 (Z.to_nat (p ^ exponent)))) =
      (Z.to_nat (p ^ exponent) -
       Z.to_nat (p ^ (exponent - 1)))%nat) by lia.
  rewrite Hlength.
  rewrite Nat2Z.inj_sub.
  - rewrite !Z2Nat.id by (apply Z.pow_nonneg; lia).
    nia.
  - apply Z2Nat.inj_le.
    + apply Z.pow_nonneg; lia.
    + apply Z.pow_nonneg; lia.
    + rewrite Hpower.
      assert (0 <= p ^ (exponent - 1)) by (apply Z.pow_nonneg; lia).
      nia.
Qed.
Lemma euler_relprime_product_divide__euler_phi_setup_removal :
  forall a b x,
    rel_prime a b ->
    Z.divide a x ->
    Z.divide b x ->
    Z.divide (a * b) x.
Proof.
  intros a b x Hab Ha Hb.
  destruct Ha as [q Hq].
  assert (Hbq : Z.divide b q).
  {
    apply Gauss with a.
    - destruct Hb as [r Hr].
      exists r.
      nia.
    - apply rel_prime_sym.
      exact Hab.
  }
  destruct Hbq as [r Hr].
  exists r.
  nia.
Qed.
Lemma euler_list_prod_nodup__euler_phi_setup_removal :
  forall (A B : Type) (l1 : list A) (l2 : list B),
    NoDup l1 ->
    NoDup l2 ->
    NoDup (list_prod l1 l2).
Proof.
  intros A B l1.
  induction l1 as [|x l1 IH]; intros l2 Hl1 Hl2; simpl.
  - constructor.
  - inversion Hl1 as [| ? ? Hx Hl1']; subst.
    apply NoDup_app.
    + apply NoDup_map_NoDup_ForallPairs.
      * intros y1 y2 Hy1 Hy2 Heq.
        inversion Heq.
        reflexivity.
      * exact Hl2.
    + apply IH; assumption.
    + intros pair Hpair_map Hpair_product.
      apply in_map_iff in Hpair_map.
      destruct Hpair_map as [y [Hpair Hy]].
      subst pair.
      apply in_prod_iff in Hpair_product.
      destruct Hpair_product as [Hxl1 Hyl2].
      contradiction.
Qed.
Lemma euler_residue_mod_member__euler_phi_setup_removal :
  forall total modulus k,
    2 <= total ->
    2 <= modulus ->
    Z.divide modulus total ->
    In k
      (filter
         (fun j : nat => Z.eqb (Z.gcd (Z.of_nat j) total) 1)
         (seq 1 (Z.to_nat total))) ->
    In (Z.to_nat (Z.of_nat k mod modulus))
      (filter
         (fun j : nat => Z.eqb (Z.gcd (Z.of_nat j) modulus) 1)
         (seq 1 (Z.to_nat modulus))).
Proof.
  intros total modulus k Htotal Hmodulus Hdivide Hk.
  pose proof
    (euler_residue_bounds__inverse_final_result total k Htotal Hk)
    as [[Hk_pos Hk_lt] Hk_gcd].
  apply Zgcd_1_rel_prime in Hk_gcd.
  assert (Hrel_modulus_k : rel_prime modulus (Z.of_nat k)).
  {
    eapply rel_prime_div.
    - apply rel_prime_sym.
      exact Hk_gcd.
    - exact Hdivide.
  }
  assert (Hrel_remainder :
    rel_prime (Z.of_nat k mod modulus) modulus).
  {
    apply rel_prime_mod; [lia |].
    apply rel_prime_sym.
    exact Hrel_modulus_k.
  }
  pose proof (Z.mod_pos_bound (Z.of_nat k) modulus ltac:(lia))
    as Hremainder_bounds.
  assert (Hremainder_pos : 0 < Z.of_nat k mod modulus).
  {
    pose proof
      (Zrel_prime_neq_mod_0 (Z.of_nat k) modulus ltac:(lia)
         (rel_prime_sym _ _ Hrel_modulus_k)) as Hnonzero.
    lia.
  }
  apply filter_In.
  split.
  - apply in_seq.
    split.
    + apply (proj2
        (Nat2Z.inj_le 1 (Z.to_nat (Z.of_nat k mod modulus)))).
      rewrite Z2Nat.id by lia.
      simpl.
      lia.
    + assert
        (Hnat_lt :
          (Z.to_nat (Z.of_nat k mod modulus) < Z.to_nat modulus)%nat).
      {
        apply
          (proj1
             (Z2Nat.inj_lt (Z.of_nat k mod modulus) modulus
                ltac:(lia) ltac:(lia))).
        lia.
      }
      lia.
  - apply Z.eqb_eq.
    rewrite Z2Nat.id by lia.
    apply Zgcd_1_rel_prime.
    exact Hrel_remainder.
Qed.
Lemma euler_crt_solution_mod_left__euler_phi_setup_removal :
  forall a b x y u v,
    2 <= a ->
    2 <= b ->
    0 <= x < a ->
    u * a + v * b = 1 ->
    ((x * (v * b) + y * (u * a)) mod (a * b)) mod a = x.
Proof.
  intros a b x y u v Ha Hb Hx Hbezout.
  rewrite <-
    (Zmod_div_mod a (a * b) (x * (v * b) + y * (u * a))).
  - apply Zdivide_mod_minus; [exact Hx |].
    exists (u * (y - x)).
    assert (Hv : v * b = 1 - u * a) by lia.
    rewrite Hv.
    ring.
  - lia.
  - nia.
  - exists b.
    ring.
Qed.
Lemma euler_crt_solution_mod_right__euler_phi_setup_removal :
  forall a b x y u v,
    2 <= a ->
    2 <= b ->
    0 <= y < b ->
    u * a + v * b = 1 ->
    ((x * (v * b) + y * (u * a)) mod (a * b)) mod b = y.
Proof.
  intros a b x y u v Ha Hb Hy Hbezout.
  rewrite <-
    (Zmod_div_mod b (a * b) (x * (v * b) + y * (u * a))).
  - apply Zdivide_mod_minus; [exact Hy |].
    exists (v * (x - y)).
    assert (Hu : u * a = 1 - v * b) by lia.
    rewrite Hu.
    ring.
  - lia.
  - nia.
  - exists a.
    ring.
Qed.
Lemma euler_crt_residue_pair_injective__euler_phi_setup_removal :
  forall a b x y,
    2 <= a ->
    2 <= b ->
    rel_prime a b ->
    In x
      (filter
         (fun j : nat => Z.eqb (Z.gcd (Z.of_nat j) (a * b)) 1)
         (seq 1 (Z.to_nat (a * b)))) ->
    In y
      (filter
         (fun j : nat => Z.eqb (Z.gcd (Z.of_nat j) (a * b)) 1)
         (seq 1 (Z.to_nat (a * b)))) ->
    (Z.to_nat (Z.of_nat x mod a), Z.to_nat (Z.of_nat x mod b)) =
    (Z.to_nat (Z.of_nat y mod a), Z.to_nat (Z.of_nat y mod b)) ->
    x = y.
Proof.
  intros a b x y Ha Hb Hab Hx Hy Heq.
  pose proof
    (euler_residue_bounds__inverse_final_result (a * b) x ltac:(nia) Hx)
    as [[Hx_pos Hx_lt] Hx_gcd].
  pose proof
    (euler_residue_bounds__inverse_final_result (a * b) y ltac:(nia) Hy)
    as [[Hy_pos Hy_lt] Hy_gcd].
  inversion Heq as [[Hmod_a Hmod_b]].
  assert (Hmod_a_Z : Z.of_nat x mod a = Z.of_nat y mod a).
  {
    apply (f_equal Z.of_nat) in Hmod_a.
    rewrite !Z2Nat.id in Hmod_a by
      (pose proof (Z.mod_pos_bound (Z.of_nat x) a ltac:(lia));
       pose proof (Z.mod_pos_bound (Z.of_nat y) a ltac:(lia)); lia).
    exact Hmod_a.
  }
  assert (Hmod_b_Z : Z.of_nat x mod b = Z.of_nat y mod b).
  {
    apply (f_equal Z.of_nat) in Hmod_b.
    rewrite !Z2Nat.id in Hmod_b by
      (pose proof (Z.mod_pos_bound (Z.of_nat x) b ltac:(lia));
       pose proof (Z.mod_pos_bound (Z.of_nat y) b ltac:(lia)); lia).
    exact Hmod_b.
  }
  assert (Hdivide_a : Z.divide a (Z.of_nat x - Z.of_nat y)).
  {
    apply Z.mod_divide; [lia |].
    rewrite Zminus_mod, Hmod_a_Z, Z.sub_diag, Z.mod_0_l by lia.
    reflexivity.
  }
  assert (Hdivide_b : Z.divide b (Z.of_nat x - Z.of_nat y)).
  {
    apply Z.mod_divide; [lia |].
    rewrite Zminus_mod, Hmod_b_Z, Z.sub_diag, Z.mod_0_l by lia.
    reflexivity.
  }
  pose proof
    (euler_relprime_product_divide__euler_phi_setup_removal
       a b (Z.of_nat x - Z.of_nat y) Hab Hdivide_a Hdivide_b)
    as Hdivide_product.
  destruct Hdivide_product as [q Hq].
  assert (q = 0) by nia.
  subst q.
  apply Nat2Z.inj.
  nia.
Qed.
Lemma euler_totient_multiplicative__euler_phi_setup_removal :
  forall a b,
    2 <= a ->
    2 <= b ->
    rel_prime a b ->
    EulerTotientValue (a * b) =
      EulerTotientValue a * EulerTotientValue b.
Proof.
  intros a b Ha Hb Hab.
  destruct (rel_prime_bezout a b Hab) as [u v Hbezout].
  set
    (lab :=
      filter
        (fun j : nat => Z.eqb (Z.gcd (Z.of_nat j) (a * b)) 1)
        (seq 1 (Z.to_nat (a * b)))).
  set
    (la :=
      filter
        (fun j : nat => Z.eqb (Z.gcd (Z.of_nat j) a) 1)
        (seq 1 (Z.to_nat a))).
  set
    (lb :=
      filter
        (fun j : nat => Z.eqb (Z.gcd (Z.of_nat j) b) 1)
        (seq 1 (Z.to_nat b))).
  set
    (residue_pair :=
      fun k : nat =>
        (Z.to_nat (Z.of_nat k mod a),
         Z.to_nat (Z.of_nat k mod b))).
  assert (Hlab_nodup : NoDup lab).
  {
    unfold lab.
    apply NoDup_filter.
    apply seq_NoDup.
  }
  assert (Hla_nodup : NoDup la).
  {
    unfold la.
    apply NoDup_filter.
    apply seq_NoDup.
  }
  assert (Hlb_nodup : NoDup lb).
  {
    unfold lb.
    apply NoDup_filter.
    apply seq_NoDup.
  }
  assert (Hmap_nodup : NoDup (map residue_pair lab)).
  {
    apply NoDup_map_NoDup_ForallPairs.
    - intros x y Hx Hy Hxy.
      unfold residue_pair in Hxy.
      unfold lab in Hx, Hy.
      exact
        (euler_crt_residue_pair_injective__euler_phi_setup_removal
           a b x y Ha Hb Hab Hx Hy Hxy).
    - exact Hlab_nodup.
  }
  assert (Hproduct_nodup : NoDup (list_prod la lb)).
  {
    apply euler_list_prod_nodup__euler_phi_setup_removal;
      assumption.
  }
  assert (Hforward : incl (map residue_pair lab) (list_prod la lb)).
  {
    intros pair Hpair.
    apply in_map_iff in Hpair.
    destruct Hpair as [k [Hpair Hk]].
    subst pair.
    apply in_prod.
    - unfold la, lab in *.
      assert (Hdivide_a : Z.divide a (a * b)).
      { exists b. ring. }
      exact
        (euler_residue_mod_member__euler_phi_setup_removal
           (a * b) a k ltac:(nia) Ha Hdivide_a Hk).
    - unfold lb, lab in *.
      assert (Hdivide_b : Z.divide b (a * b)).
      { exists a. ring. }
      exact
        (euler_residue_mod_member__euler_phi_setup_removal
           (a * b) b k ltac:(nia) Hb Hdivide_b Hk).
  }
  assert (Hbackward : incl (list_prod la lb) (map residue_pair lab)).
  {
    intros pair Hpair.
    destruct pair as [x y].
    apply in_prod_iff in Hpair.
    destruct Hpair as [Hx Hy].
    pose proof
      (euler_residue_bounds__inverse_final_result a x Ha ltac:(
         unfold la in Hx; exact Hx)) as [[Hx_pos Hx_lt] Hx_gcd].
    pose proof
      (euler_residue_bounds__inverse_final_result b y Hb ltac:(
         unfold lb in Hy; exact Hy)) as [[Hy_pos Hy_lt] Hy_gcd].
    set
      (z :=
        (Z.of_nat x * (v * b) + Z.of_nat y * (u * a)) mod (a * b)).
    assert (Hz_mod_a : z mod a = Z.of_nat x).
    {
      unfold z.
      exact
        (euler_crt_solution_mod_left__euler_phi_setup_removal
           a b (Z.of_nat x) (Z.of_nat y) u v Ha Hb ltac:(lia) Hbezout).
    }
    assert (Hz_mod_b : z mod b = Z.of_nat y).
    {
      unfold z.
      exact
        (euler_crt_solution_mod_right__euler_phi_setup_removal
           a b (Z.of_nat x) (Z.of_nat y) u v Ha Hb ltac:(lia) Hbezout).
    }
    assert (Hz_bounds : 0 <= z < a * b).
    {
      unfold z.
      apply Z.mod_pos_bound.
      nia.
    }
    assert (Hz_pos : 0 < z).
    {
      destruct (Z.eq_dec z 0) as [Hz_zero | Hz_nonzero]; [|lia].
      rewrite Hz_zero in Hz_mod_a.
      rewrite Z.mod_0_l in Hz_mod_a by lia.
      lia.
    }
    assert (Hz_rel_a : rel_prime z a).
    {
      apply rel_prime_mod_rev; [lia |].
      rewrite Hz_mod_a.
      apply Zgcd_1_rel_prime.
      exact Hx_gcd.
    }
    assert (Hz_rel_b : rel_prime z b).
    {
      apply rel_prime_mod_rev; [lia |].
      rewrite Hz_mod_b.
      apply Zgcd_1_rel_prime.
      exact Hy_gcd.
    }
    assert (Hz_rel_product : rel_prime z (a * b)).
    {
      apply rel_prime_mult; assumption.
    }
    apply in_map_iff.
    exists (Z.to_nat z).
    split.
    - unfold residue_pair.
      rewrite Z2Nat.id by lia.
      rewrite Hz_mod_a, Hz_mod_b.
      rewrite !Nat2Z.id.
      reflexivity.
    - unfold lab.
      apply filter_In.
      split.
      + apply in_seq.
        split.
        * apply (proj2 (Nat2Z.inj_le 1 (Z.to_nat z))).
          rewrite Z2Nat.id by lia.
          simpl.
          lia.
        * rewrite <- (Z2Nat.id (a * b)) by nia.
          apply Nat2Z.inj_lt.
          rewrite Z2Nat.id by lia.
          lia.
      + apply Z.eqb_eq.
        rewrite Z2Nat.id by lia.
        apply Zgcd_1_rel_prime.
        exact Hz_rel_product.
  }
  assert (Hpermutation :
    Permutation (map residue_pair lab) (list_prod la lb)).
  {
    apply NoDup_Permutation; [exact Hmap_nodup | exact Hproduct_nodup |].
    intro pair.
    split; [apply Hforward | apply Hbackward].
  }
  pose proof (Permutation_length Hpermutation) as Hlength.
  rewrite length_map, length_prod in Hlength.
  rewrite !EulerTotientValue_compat. unfold EulerTotientCountLegacy, lab, la, lb in *.
  rewrite Hlength.
  apply Nat2Z.inj_mul.
Qed.
Lemma euler_totient_coprime_prime_power__euler_phi_setup_removal :
  forall terminal factor exponent,
    1 <= terminal ->
    prime factor ->
    1 <= exponent ->
    ~ Z.divide factor terminal ->
    EulerTotientValue (terminal * factor ^ exponent) =
      EulerTotientValue terminal *
        (factor ^ (exponent - 1) * (factor - 1)).
Proof.
  intros terminal factor exponent Hterminal Hfactor Hexponent Hfactor_free.
  pose proof (prime_ge_2 factor Hfactor) as Hfactor_ge.
  assert (Hpower_decomposition :
    factor ^ exponent = factor * factor ^ (exponent - 1)).
  {
    replace exponent with ((exponent - 1) + 1) at 1 by lia.
    rewrite Z.pow_add_r by lia.
    rewrite Z.pow_1_r.
    ring.
  }
  assert (Hpower_tail_pos : 0 < factor ^ (exponent - 1)).
  { apply Z.pow_pos_nonneg; lia. }
  destruct (Z.eq_dec terminal 1) as [Hterminal_one | Hterminal_not_one].
  - subst terminal.
    assert (Hphi_one : EulerTotientValue 1 = 1) by reflexivity.
    rewrite Z.mul_1_l, Hphi_one, Z.mul_1_l.
    apply euler_totient_prime_power__euler_phi_setup_removal;
      assumption.
  - assert (Hterminal_ge : 2 <= terminal) by lia.
    assert (Hrel_factor_terminal : rel_prime factor terminal).
    { apply prime_rel_prime; assumption. }
    assert (Hrel_terminal_power :
      rel_prime terminal (factor ^ exponent)).
    {
      apply rel_prime_Zpower_r; [lia |].
      apply rel_prime_sym.
      exact Hrel_factor_terminal.
    }
    rewrite
      euler_totient_multiplicative__euler_phi_setup_removal
        by (try assumption; rewrite Hpower_decomposition; nia).
    rewrite
      euler_totient_prime_power__euler_phi_setup_removal
        by assumption.
    ring.
Qed.
Lemma euler_phi_removal_start__euler_phi_setup_removal :
  forall original factor current result,
    2 <= original ->
    1 <= current ->
    1 <= result ->
    2 <= factor ->
    current mod factor = 0 ->
    EulerPhiProgress original factor current result ->
    EulerPhiRemovalProgress original factor current result.
Proof.
  intros original factor current result Horiginal Hcurrent Hresult_pos
    Hfactor Hmod Hprogress.
  destruct Hprogress as [Hresidual Hno_small].
  destruct Hresidual as [Hcurrent_result Hsemantic].
  assert (Hfactor_current : Z.divide factor current).
  { apply Z.mod_divide; lia. }
  assert (Hfactor_prime : prime factor).
  {
    apply euler_factor_prime__euler_phi_setup_removal
      with (value := current); assumption.
  }
  assert (Hfactor_result : Z.divide factor result).
  {
    destruct Hfactor_current as [a Ha].
    destruct Hcurrent_result as [q Hq].
    exists (a * q).
    nia.
  }
  exists current, 0.
  split; [lia |].
  split.
  - simpl.
    ring.
  - split; [exact Hfactor_current |].
    split; [exact Hfactor_result |].
    split.
    + split.
      * split; [exact Hcurrent_result | exact Hsemantic].
      * exact Hno_small.
    + unfold EulerPhiFactorCompletion.
      intros terminal removed Hremoved Hdecomposition Hterminal_free.
      assert (Hremoved_pos : 1 <= removed).
      {
        destruct (Z.eq_dec removed 0) as [Hremoved_zero | Hremoved_nonzero];
          [|lia].
        subst removed.
        simpl in Hdecomposition.
        rewrite Z.mul_1_r in Hdecomposition.
        subst current.
        contradiction.
      }
      assert (Hpower_decomposition :
        factor ^ removed = factor * factor ^ (removed - 1)).
      {
        replace removed with ((removed - 1) + 1) at 1 by lia.
        rewrite Z.pow_add_r by lia.
        rewrite Z.pow_1_r.
        ring.
      }
      assert (Hpower_tail_pos : 0 < factor ^ (removed - 1)).
      { apply Z.pow_pos_nonneg; lia. }
      assert (Hpower_pos : 0 < factor ^ removed).
      { rewrite Hpower_decomposition. nia. }
      assert (Hterminal_pos : 1 <= terminal) by nia.
      assert (Hfactor_terminal : ~ Z.divide factor terminal).
      {
        intro Hdivide.
        apply Hterminal_free.
        apply Zdivide_mod.
        exact Hdivide.
      }
      assert (Htotient :
        EulerTotientValue current =
          EulerTotientValue terminal *
            (factor ^ (removed - 1) * (factor - 1))).
      {
        rewrite Hdecomposition.
        apply euler_totient_coprime_prime_power__euler_phi_setup_removal;
          assumption.
      }
      destruct Hcurrent_result as [q Hresult_decomposition].
      assert (Hresult_expanded :
        result = terminal * factor ^ removed * q) by nia.
      assert (Hresult_div_factor :
        result / factor = terminal * factor ^ (removed - 1) * q).
      {
        symmetry.
        apply Zdiv_unique with (r := 0).
        - lia.
        - rewrite Hresult_expanded, Hpower_decomposition.
          ring.
      }
      unfold EulerPhiResidual.
      split.
      * exists (factor ^ (removed - 1) * q * (factor - 1)).
        rewrite Hresult_div_factor.
        ring.
      * intros original_phi terminal_phi Hphi_original Hphi_terminal.
        specialize
          (Hsemantic original_phi (EulerTotientValue current)
             Hphi_original ltac:(unfold EulerPhi; reflexivity)).
        assert (Hcancel :
          original_phi * current =
            (q * EulerTotientValue current) * current).
        {
          rewrite Hresult_decomposition in Hsemantic.
          nia.
        }
        assert (Horiginal_phi :
          original_phi = q * EulerTotientValue current).
        {
          apply Z.mul_reg_r with current.
          - lia.
          - exact Hcancel.
        }
        unfold EulerPhi in Hphi_terminal.
        subst terminal_phi.
        rewrite Horiginal_phi, Htotient, Hresult_div_factor.
        ring.
Qed.
Lemma euler_prime_two__euler_phi_factor_completion :
  EulerPrime 2.
Proof.
  unfold EulerPrime.
  split; [lia |].
  intros d Hd [q Hq].
  assert (0 < q) by nia.
  assert (d = 1 \/ d = 2) by nia.
  exact H0.
Qed.
Lemma euler_exact_positive_quotient_bounds__euler_phi_factor_completion :
  forall result factor,
    1 <= result ->
    2 <= factor ->
    Z.divide factor result ->
    1 <= Z.quot result factor /\
    0 <= Z.quot result factor * (factor - 1) /\
    Z.quot result factor * (factor - 1) <= result.
Proof.
  intros result factor Hresult Hfactor [q Hq].
  rewrite Hq, Z.quot_mul by lia.
  nia.
Qed.
Lemma euler_progress_advance_nondivisor__euler_phi_factor_completion :
  forall original factor remaining result,
    2 <= factor ->
    Z.rem remaining factor <> 0 ->
    EulerPhiProgress original factor remaining result ->
    EulerPhiProgress original (factor + 1) remaining result.
Proof.
  intros original factor remaining result Hfactor Hrem Hprogress.
  destruct Hprogress as [Hresidual Hbelow].
  split; [exact Hresidual |].
  unfold NoPrimeDivisorBelow in *.
  intros p Hprime Hlt Hdivide.
  destruct (Z_lt_ge_dec p factor) as [Hstrict | Hge].
  - apply (Hbelow p Hprime Hstrict Hdivide).
  - replace p with factor in * by lia.
    apply Hrem.
    apply (proj2 (Z.rem_divide remaining factor ltac:(lia))).
    exact Hdivide.
Qed.
Lemma euler_completed_progress__euler_phi_factor_completion :
  forall original factor current result,
    1 <= current ->
    1 <= result ->
    2 <= factor ->
    Z.rem current factor <> 0 ->
    EulerPhiRemovalProgress original factor current result ->
    EulerPhiProgress original (factor + 1) current
      (Z.quot result factor * (factor - 1)).
Proof.
  intros original factor current result
    Hcurrent Hresult Hfactor Hrem Hremoval.
  assert (Hmod : current mod factor <> 0).
  {
    rewrite <- Z.rem_mod_nonneg by lia.
    exact Hrem.
  }
  pose proof
    (EulerPhiRemovalProgress_complete
       original factor current result Hremoval Hmod)
    as Hresidual.
  rewrite <- Z.quot_div_nonneg in Hresidual by lia.
  split; [exact Hresidual |].
  destruct Hremoval as
      [before [removed
        [Hremoved [Hbefore
          [Hfactor_before [Hfactor_result
            [[Hbefore_residual Hbelow] Hcompletion]]]]]]].
  unfold NoPrimeDivisorBelow in *.
  intros p Hprime Hlt Hdivide.
  destruct (Z_lt_ge_dec p factor) as [Hstrict | Hge].
  - apply (Hbelow p Hprime Hstrict).
    destruct Hdivide as [q Hq].
    exists (q * factor ^ removed).
    rewrite Hbefore, Hq.
    ring.
  - replace p with factor in * by lia.
    apply Hrem.
    apply (proj2 (Z.rem_divide current factor ltac:(lia))).
    exact Hdivide.
Qed.
Lemma euler_active_frontier_bound__euler_phi_factor_completion :
  forall original factor current result,
    2 <= factor ->
    factor <= 216 ->
    EulerPhiRemovalProgress original factor current result ->
    factor + 1 <= 216.
Proof.
  intros original factor current result Hfactor Hbound Hremoval.
  destruct (Z.eq_dec factor 216) as [Heq | Hneq]; [|lia].
  subst factor.
  destruct Hremoval as
      [before [removed
        [Hremoved [Hbefore
          [Hfactor_before [Hfactor_result
            [[Hbefore_residual Hbelow] Hcompletion]]]]]]].
  exfalso.
  apply
    (Hbelow 2
       euler_prime_two__euler_phi_factor_completion ltac:(lia)).
  destruct Hfactor_before as [q Hq].
  exists (108 * q).
  nia.
Qed.
Lemma euler_prime_to_prime__euler_phi_final_results :
  forall p,
    EulerPrime p -> prime p.
Proof.
  intros p [Hp_gt Hp_divisors].
  apply prime_alt.
  unfold prime'.
  split; [exact Hp_gt |].
  intros d Hd_range Hd_divide.
  destruct (Hp_divisors d ltac:(lia) Hd_divide) as [-> | ->]; lia.
Qed.
Lemma euler_remaining_prime__euler_phi_final_results :
  forall frontier remaining,
    1 < remaining ->
    2 <= frontier ->
    frontier * frontier > remaining ->
    NoPrimeDivisorBelow frontier remaining ->
    EulerPrime remaining.
Proof.
  intros frontier remaining Hremaining_gt Hfrontier Hsquare Hno_small.
  destruct (prime_dec remaining) as [Hprime | Hnot_prime].
  - apply euler_prime_from_prime__euler_phi_final_results.
    exact Hprime.
  - exfalso.
    destruct (not_prime_divide remaining Hremaining_gt Hnot_prime)
      as [d [[Hd_gt Hd_lt] Hd_divide]].
    destruct Hd_divide as [e Hremaining].
    assert (He_gt : 1 < e) by nia.
    destruct (Z_lt_ge_dec d frontier) as [Hd_frontier | Hd_frontier].
    + destruct
        (euler_prime_divisor_exists__euler_phi_final_results d Hd_gt)
        as [q [Hq_prime Hq_divide]].
      apply
        (Hno_small q
           (euler_prime_from_prime__euler_phi_final_results q Hq_prime)).
      * apply Z.divide_pos_le in Hq_divide; [nia |].
        apply prime_ge_2 in Hq_prime.
        lia.
      * destruct Hq_divide as [a Ha].
        exists (a * e).
        nia.
    + assert (He_frontier : e < frontier) by nia.
      destruct
        (euler_prime_divisor_exists__euler_phi_final_results e He_gt)
        as [q [Hq_prime Hq_divide]].
      apply
        (Hno_small q
           (euler_prime_from_prime__euler_phi_final_results q Hq_prime)).
      * apply Z.divide_pos_le in Hq_divide; [nia |].
        apply prime_ge_2 in Hq_prime.
        lia.
      * destruct Hq_divide as [a Ha].
        exists (d * a).
        nia.
Qed.
Lemma euler_filter_all_true__euler_phi_final_results :
  forall (A : Type) (f : A -> bool) (l : list A),
    (forall x, In x l -> f x = true) ->
    filter f l = l.
Proof.
  intros A f l.
  induction l as [| a l IH]; intros Hall; simpl.
  - reflexivity.
  - rewrite Hall by (left; reflexivity).
    f_equal.
    apply IH.
    intros x Hx.
    apply Hall.
    right.
    exact Hx.
Qed.
Lemma euler_totient_of_prime__euler_phi_final_results :
  forall p,
    prime p ->
    EulerTotientValue p = p - 1.
Proof.
  intros p Hp.
  pose proof (prime_ge_2 p Hp) as Hp_ge.
  rewrite !EulerTotientValue_compat. unfold EulerTotientCountLegacy.
  assert (Hnat : Z.of_nat (Z.to_nat p) = p).
  { rewrite Z2Nat.id; lia. }
  remember (Z.to_nat p) as n eqn:Hn.
  destruct n as [| m].
  - simpl in Hnat.
    lia.
  - assert (Hseq : seq 1 (S m) = seq 1 m ++ [S m]).
    {
      replace (S m) with (m + 1)%nat at 1 by lia.
      rewrite seq_app.
      replace (1 + m)%nat with (S m) by lia.
      simpl.
      reflexivity.
    }
    assert
      (Hfilter :
        filter
          (fun k : nat => Z.eqb (Z.gcd (Z.of_nat k) p) 1)
          (seq 1 m) = seq 1 m).
    {
      apply euler_filter_all_true__euler_phi_final_results.
      intros k Hk.
      apply in_seq in Hk.
      apply Z.eqb_eq.
      apply Zgcd_1_rel_prime.
      apply rel_prime_le_prime; [exact Hp |].
      split.
      - assert (Hk_positive : (0 < k)%nat) by lia.
        apply Nat2Z.inj_lt in Hk_positive.
        simpl in Hk_positive.
        lia.
      - assert (Hk_less : (k < S m)%nat) by lia.
        apply Nat2Z.inj_lt in Hk_less.
        rewrite Hnat in Hk_less.
        exact Hk_less.
    }
    assert (Hgcd : Z.gcd p p = p).
    {
      apply Z.divide_antisym_nonneg.
      - apply Z.gcd_nonneg.
      - lia.
      - apply Z.gcd_divide_l.
      - apply Z.gcd_greatest; apply Z.divide_refl.
    }
    assert
      (Hlast : Z.eqb (Z.gcd (Z.of_nat (S m)) p) 1 = false).
    {
      rewrite Hnat, Hgcd.
      apply Z.eqb_neq.
      lia.
    }
    rewrite Hseq, filter_app, Hfilter.
    cbn [filter].
    rewrite Hlast.
    cbn.
    rewrite app_nil_r, length_seq.
    rewrite Nat2Z.inj_succ in Hnat.
    lia.
Qed.
Lemma euler_progress_terminal_prime__euler_phi_final_results :
  forall original frontier remaining result,
    1 < remaining ->
    2 <= frontier ->
    frontier * frontier > remaining ->
    EulerPhiProgress original frontier remaining result ->
    EulerPhi original (Z.quot result remaining * (remaining - 1)).
Proof.
  intros original frontier remaining result Hremaining Hfrontier Hsquare Hprogress.
  destruct Hprogress as [[Hdivide Hresidual] Hno_small].
  assert (Hprime : EulerPrime remaining).
  {
    apply euler_remaining_prime__euler_phi_final_results
      with (frontier := frontier); assumption.
  }
  assert (Hprime_std : prime remaining).
  {
    apply euler_prime_to_prime__euler_phi_final_results.
    exact Hprime.
  }
  assert (Hremaining_phi : EulerPhi remaining (remaining - 1)).
  {
    unfold EulerPhi.
    symmetry.
    apply euler_totient_of_prime__euler_phi_final_results.
    exact Hprime_std.
  }
  unfold EulerPhi.
  specialize
    (Hresidual (EulerTotientValue original) (remaining - 1)
       ltac:(unfold EulerPhi; reflexivity) Hremaining_phi).
  destruct Hdivide as [q Hresult].
  rewrite Hresult, Z.quot_mul by lia.
  nia.
Qed.
Lemma euler_progress_terminal_one__euler_phi_final_results :
  forall original frontier remaining result,
    remaining = 1 ->
    EulerPhiProgress original frontier remaining result ->
    EulerPhi original result.
Proof.
  intros original frontier remaining result Hremaining Hprogress.
  subst remaining.
  destruct Hprogress as [[_ Hresidual] _].
  unfold EulerPhi.
  specialize
    (Hresidual (EulerTotientValue original) 1
       ltac:(unfold EulerPhi; reflexivity)
       ltac:(unfold EulerPhi, EulerTotientValue; reflexivity)).
  rewrite Z.mul_1_r, Z.mul_1_r in Hresidual.
  symmetry.
  exact Hresidual.
Qed.
Lemma euler_modular_progress_odd_step__modular_power_loop :
  forall original_base original_exponent modulus base exponent accumulator,
    0 < modulus ->
    0 < exponent ->
    exponent mod 2 = 1 ->
    EulerModularPowerProgress
      original_base original_exponent modulus base exponent accumulator ->
    EulerModularPowerProgress
      original_base original_exponent modulus
      ((base * base) mod modulus) (exponent / 2)
      ((accumulator * base) mod modulus).
Proof.
  intros original_base original_exponent modulus base exponent accumulator
    Hmodulus Hexponent Hodd Hprogress.
  unfold EulerModularPowerProgress in *.
  eapply modular_power_progress_odd_step__loop_transitions; eauto; lia.
Qed.
Lemma euler_modular_progress_even_step__modular_power_loop :
  forall original_base original_exponent modulus base exponent accumulator,
    0 < modulus ->
    0 < exponent ->
    exponent mod 2 <> 1 ->
    EulerModularPowerProgress
      original_base original_exponent modulus base exponent accumulator ->
    EulerModularPowerProgress
      original_base original_exponent modulus
      ((base * base) mod modulus) (exponent / 2) accumulator.
Proof.
  intros original_base original_exponent modulus base exponent accumulator
    Hmodulus Hexponent Hnotodd Hprogress.
  pose proof (Z.mod_pos_bound exponent 2 ltac:(lia)) as Hparity.
  assert (Heven : exponent mod 2 = 0) by lia.
  unfold EulerModularPowerProgress in *.
  eapply modular_power_progress_even_step__loop_transitions; eauto; lia.
Qed.
Lemma bounded_residue_product_int__modular_power_loop :
  forall modulus x y,
    2 <= modulus ->
    modulus <= 46341 ->
    0 <= x ->
    x < modulus ->
    0 <= y ->
    y < modulus ->
    0 <= x * y /\ x * y <= 2147483647.
Proof.
  intros modulus x y Hmodulus_min Hmodulus_max
    Hx_min Hx_max Hy_min Hy_max.
  nia.
Qed.
Lemma euler_modular_progress_zero_finish__modular_power_final :
  forall original_base original_exponent modulus current_base accumulator,
    0 <= accumulator ->
    accumulator < modulus ->
    EulerModularPowerProgress
      original_base original_exponent modulus current_base 0 accumulator ->
    ModularPower original_base original_exponent modulus accumulator.
Proof.
  intros original_base original_exponent modulus current_base accumulator
    Hacc_nonnegative Hacc_bounded Hprogress.
  unfold EulerModularPowerProgress in Hprogress.
  unfold ModularPower.
  cbn in Hprogress.
  rewrite Z.mod_small in Hprogress by lia.
  lia.
Qed.
Lemma euler_coprime_residue_member__inverse_final_result :
  forall n x,
    2 <= n ->
    0 < x < n ->
    Z.gcd x n = 1 ->
    In (Z.to_nat x)
      (filter
         (fun j : nat => Z.eqb (Z.gcd (Z.of_nat j) n) 1)
         (seq 1 (Z.to_nat n))).
Proof.
  intros n x Hn Hx Hgcd.
  apply filter_In.
  split.
  - apply in_seq.
    assert (Hnatpos : (1 <= Z.to_nat x)%nat).
    {
      apply (proj1 (Z2Nat.inj_le 1 x ltac:(lia) ltac:(lia)));
        simpl; lia.
    }
    assert (Hnatlt : (Z.to_nat x < Z.to_nat n)%nat).
    {
      apply (proj1 (Z2Nat.inj_lt x n ltac:(lia) ltac:(lia)));
        lia.
    }
    lia.
  - apply Z.eqb_eq.
    rewrite Z2Nat.id by lia.
    exact Hgcd.
Qed.
Lemma euler_residue_map_member__inverse_final_result :
  forall n a k,
    2 <= n ->
    Z.gcd a n = 1 ->
    In k
      (filter
         (fun j : nat => Z.eqb (Z.gcd (Z.of_nat j) n) 1)
         (seq 1 (Z.to_nat n))) ->
    In (Z.to_nat ((a * Z.of_nat k) mod n))
      (filter
         (fun j : nat => Z.eqb (Z.gcd (Z.of_nat j) n) 1)
         (seq 1 (Z.to_nat n))).
Proof.
  intros n a k Hn Hagcd Hk.
  pose proof
    (euler_residue_bounds__inverse_final_result n k Hn Hk)
    as [[Hkpos Hklt] Hkgcd].
  set (r := (a * Z.of_nat k) mod n).
  assert (Hrbound : 0 <= r < n).
  {
    unfold r.
    apply Z.mod_pos_bound.
    lia.
  }
  assert (Hrgcd : Z.gcd r n = 1).
  {
    apply Zgcd_1_rel_prime.
    unfold r.
    apply rel_prime_mod; [lia |].
    apply rel_prime_sym.
    apply rel_prime_mult.
    - apply rel_prime_sym.
      apply Zgcd_1_rel_prime.
      exact Hagcd.
    - apply rel_prime_sym.
      apply Zgcd_1_rel_prime.
      exact Hkgcd.
  }
  assert (Hrpos : 0 < r).
  {
    destruct Hrbound as [Hrnonneg Hrlt].
    destruct (Z.eq_dec r 0) as [-> | Hne]; [|lia].
    rewrite Z.gcd_0_l, Z.abs_eq in Hrgcd by lia.
    lia.
  }
  apply filter_In.
  split.
  - apply in_seq.
    assert (Hnatpos : (1 <= Z.to_nat r)%nat).
    {
      apply (proj1 (Z2Nat.inj_le 1 r ltac:(lia) ltac:(lia)));
        simpl; lia.
    }
    assert (Hnatlt : (Z.to_nat r < Z.to_nat n)%nat).
    {
      apply (proj1 (Z2Nat.inj_lt r n ltac:(lia) ltac:(lia)));
        lia.
    }
    lia.
  - apply Z.eqb_eq.
    rewrite Z2Nat.id by lia.
    exact Hrgcd.
Qed.
Lemma euler_residue_map_injective__inverse_final_result :
  forall n a x y,
    2 <= n ->
    Z.gcd a n = 1 ->
    In x
      (filter
         (fun j : nat => Z.eqb (Z.gcd (Z.of_nat j) n) 1)
         (seq 1 (Z.to_nat n))) ->
    In y
      (filter
         (fun j : nat => Z.eqb (Z.gcd (Z.of_nat j) n) 1)
         (seq 1 (Z.to_nat n))) ->
    Z.to_nat ((a * Z.of_nat x) mod n) =
    Z.to_nat ((a * Z.of_nat y) mod n) ->
    x = y.
Proof.
  intros n a x y Hn Hagcd Hx Hy Heq.
  pose proof
    (euler_residue_bounds__inverse_final_result n x Hn Hx)
    as [[Hxpos Hxlt] Hxgcd].
  pose proof
    (euler_residue_bounds__inverse_final_result n y Hn Hy)
    as [[Hypos Hylt] Hygcd].
  assert (Hmods :
    (a * Z.of_nat x) mod n = (a * Z.of_nat y) mod n).
  {
    apply (f_equal Z.of_nat) in Heq.
    rewrite !Z2Nat.id in Heq by
      (pose proof (Z.mod_pos_bound (a * Z.of_nat x) n ltac:(lia));
       pose proof (Z.mod_pos_bound (a * Z.of_nat y) n ltac:(lia));
       lia).
    exact Heq.
  }
  assert (Hdivmul : Z.divide n (a * (Z.of_nat x - Z.of_nat y))).
  {
    replace (a * (Z.of_nat x - Z.of_nat y))
      with (a * Z.of_nat x - a * Z.of_nat y) by ring.
    apply Z.mod_divide; [lia |].
    rewrite Zminus_mod, Hmods, Z.sub_diag, Z.mod_0_l by lia.
    reflexivity.
  }
  assert (Hdiv : Z.divide n (Z.of_nat x - Z.of_nat y)).
  {
    eapply Gauss.
    - exact Hdivmul.
    - apply rel_prime_sym.
      apply Zgcd_1_rel_prime.
      exact Hagcd.
  }
  destruct Hdiv as [q Hq].
  assert (q = 0) by nia.
  subst q.
  apply Nat2Z.inj.
  nia.
Qed.
Lemma euler_residue_map_nodup__inverse_final_result :
  forall n a,
    2 <= n ->
    Z.gcd a n = 1 ->
    NoDup
      (map
         (fun k : nat => Z.to_nat ((a * Z.of_nat k) mod n))
         (filter
            (fun j : nat => Z.eqb (Z.gcd (Z.of_nat j) n) 1)
            (seq 1 (Z.to_nat n)))).
Proof.
  intros n a Hn Hagcd.
  apply NoDup_map_NoDup_ForallPairs.
  - intros x y Hx Hy Heq.
    eapply euler_residue_map_injective__inverse_final_result; eauto.
  - apply NoDup_filter.
    apply seq_NoDup.
Qed.
Lemma euler_residue_map_permutation__inverse_final_result :
  forall n a,
    2 <= n ->
    Z.gcd a n = 1 ->
    Permutation
      (map
         (fun k : nat => Z.to_nat ((a * Z.of_nat k) mod n))
         (filter
            (fun j : nat => Z.eqb (Z.gcd (Z.of_nat j) n) 1)
            (seq 1 (Z.to_nat n))))
      (filter
         (fun j : nat => Z.eqb (Z.gcd (Z.of_nat j) n) 1)
         (seq 1 (Z.to_nat n))).
Proof.
  intros n a Hn Hagcd.
  apply NoDup_Permutation_bis.
  - apply euler_residue_map_nodup__inverse_final_result; assumption.
  - rewrite length_map.
    apply Nat.le_refl.
  - intros x Hx.
    apply in_map_iff in Hx.
    destruct Hx as [k [Hx Hk]].
    subst x.
    eapply euler_residue_map_member__inverse_final_result; eauto.
Qed.
Lemma euler_product_permutation__inverse_final_result :
  forall l1 l2,
    Permutation l1 l2 ->
    fold_right (fun k acc => Z.of_nat k * acc) 1 l1 =
    fold_right (fun k acc => Z.of_nat k * acc) 1 l2.
Proof.
  intros l1 l2 Hperm.
  induction Hperm; simpl; try ring; congruence.
Qed.
Lemma euler_mapped_product_mod__inverse_final_result :
  forall n a l,
    0 < n ->
    (fold_right (fun k acc => Z.of_nat k * acc) 1
       (map (fun k : nat => Z.to_nat ((a * Z.of_nat k) mod n)) l)) mod n =
    (a ^ Z.of_nat (length l) *
       fold_right (fun k acc => Z.of_nat k * acc) 1 l) mod n.
Proof.
  intros n a l Hn.
  induction l as [|k l IH].
  - simpl.
    reflexivity.
  - simpl map.
    simpl fold_right.
    change (length (k :: l)) with (S (length l)).
    rewrite Nat2Z.inj_succ.
    rewrite Z.pow_succ_r by lia.
    rewrite Z2Nat.id by
      (pose proof (Z.mod_pos_bound (a * Z.of_nat k) n ltac:(lia)); lia).
    transitivity
      (((a * Z.of_nat k) *
          (a ^ Z.of_nat (length l) *
             fold_right (fun j acc => Z.of_nat j * acc) 1 l)) mod n).
    + rewrite Z.mul_mod by lia.
      rewrite Z.mod_mod by lia.
      rewrite IH.
      rewrite <- Z.mul_mod by lia.
      reflexivity.
    + apply (f_equal (fun z => z mod n)).
      ring.
Qed.
Lemma euler_residue_product_coprime__inverse_final_result :
  forall n l,
    (forall k, In k l -> Z.gcd (Z.of_nat k) n = 1) ->
    rel_prime
      (fold_right (fun k acc => Z.of_nat k * acc) 1 l) n.
Proof.
  intros n l.
  induction l as [|k l IH]; intros Hall.
  - simpl.
    apply rel_prime_1.
  - simpl.
    apply rel_prime_sym.
    apply rel_prime_mult.
    + apply rel_prime_sym.
      apply Zgcd_1_rel_prime.
      apply Hall.
      left.
      reflexivity.
    + apply rel_prime_sym.
      apply IH.
      intros j Hj.
      apply Hall.
      right.
      exact Hj.
Qed.
Lemma euler_power_totient_mod__inverse_final_result :
  forall a n,
    0 < a ->
    a < n ->
    2 <= n ->
    Z.gcd a n = 1 ->
    (a ^ EulerTotientValue n) mod n = 1.
Proof.
  intros a n Ha Han Hn Hagcd.
  rewrite !EulerTotientValue_compat. unfold EulerTotientCountLegacy.
  set (residues :=
    filter
      (fun k : nat => Z.eqb (Z.gcd (Z.of_nat k) n) 1)
      (seq 1 (Z.to_nat n))).
  set (product :=
    fold_right (fun k acc => Z.of_nat k * acc) 1 residues).
  pose proof
    (euler_residue_map_permutation__inverse_final_result n a Hn Hagcd)
    as Hperm.
  fold residues in Hperm.
  pose proof
    (euler_product_permutation__inverse_final_result _ _ Hperm)
    as Hproduct.
  fold product in Hproduct.
  pose proof
    (euler_mapped_product_mod__inverse_final_result n a residues ltac:(lia))
    as Hmapped.
  fold product in Hmapped.
  rewrite Hproduct in Hmapped.
  assert (Hdivprod :
    Z.divide n ((a ^ Z.of_nat (length residues) - 1) * product)).
  {
    replace ((a ^ Z.of_nat (length residues) - 1) * product)
      with (a ^ Z.of_nat (length residues) * product - product) by ring.
    apply Z.mod_divide; [lia |].
    rewrite Zminus_mod, <- Hmapped, Z.sub_diag, Z.mod_0_l by lia.
    reflexivity.
  }
  assert (Hproduct_coprime : rel_prime n product).
  {
    apply rel_prime_sym.
    unfold product.
    apply euler_residue_product_coprime__inverse_final_result.
    intros k Hk.
    unfold residues in Hk.
    pose proof
      (euler_residue_bounds__inverse_final_result n k Hn Hk)
      as [_ Hkgcd].
    exact Hkgcd.
  }
  assert (Hdivpower :
    Z.divide n (a ^ Z.of_nat (length residues) - 1)).
  {
    eapply Gauss.
    - replace (product * (a ^ Z.of_nat (length residues) - 1))
        with ((a ^ Z.of_nat (length residues) - 1) * product) by ring.
      exact Hdivprod.
    - exact Hproduct_coprime.
  }
  apply Zdivide_mod_minus.
  - lia.
  - exact Hdivpower.
Qed.
Lemma euler_totient_inverse_theorem__inverse_final_result :
  forall a n phi inverse,
    0 < a ->
    a < n ->
    2 <= n ->
    Z.gcd a n = 1 ->
    EulerPhi n phi ->
    ModularPower a (phi - 1) n inverse ->
    (a * inverse) mod n = 1 /\
    EulerTheoremInverse a n inverse.
Proof.
  intros a n phi inverse Ha Han Hn Hagcd Hphi Hpower.
  assert (Hphipos : 1 <= phi).
  {
    unfold EulerPhi in Hphi. rewrite EulerTotientValue_compat in Hphi. unfold EulerTotientCountLegacy in Hphi.
    subst phi.
    assert (Hin :
      In (Z.to_nat a)
        (filter
           (fun j : nat => Z.eqb (Z.gcd (Z.of_nat j) n) 1)
           (seq 1 (Z.to_nat n)))).
    {
      apply euler_coprime_residue_member__inverse_final_result; auto; lia.
    }
    destruct
      (filter
         (fun j : nat => Z.eqb (Z.gcd (Z.of_nat j) n) 1)
         (seq 1 (Z.to_nat n))) as [|k l] eqn:Hresidues.
    - contradiction.
    - simpl.
      lia.
  }
  assert (Hinverse : (a * inverse) mod n = 1).
  {
    unfold ModularPower in Hpower.
    rewrite Hpower.
    replace a with (a mod n) at 1 by
      (apply Z.mod_small; lia).
    rewrite <- Z.mul_mod by lia.
    replace (a * a ^ (phi - 1)) with (a ^ phi).
    - unfold EulerPhi in Hphi.
      rewrite Hphi.
      apply euler_power_totient_mod__inverse_final_result; assumption.
    - rewrite <- Z.pow_succ_r by lia.
      replace (phi - 1 + 1) with phi by ring.
      f_equal.
      lia.
  }
  split.
  - exact Hinverse.
  - exact Hinverse.
Qed.
