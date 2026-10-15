Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.ZArith.Zpow_facts.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.micromega.Lia.
Require Import SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition CatchesAll (m x : Z) (traps : list Z) : Prop :=
  NoDup traps /\ Forall (fun r => 0 <= r < m) traps /\
  forall start, 0 <= start < m -> exists t room, t >= 0 /\ room = start * Z.pow x t mod m /\ In room traps.
Definition Pre (m x : Z) : Prop :=
  (* Stated explicitly in the P090 solver Require, so dropped here:
       2<=m<=Z.pow 10 14 /\ 1<=x<m /\ *)
  Z.gcd x m = 1.
Definition Spec (m x out : Z) : Prop :=
  min_value_of_subset Z.le (fun v => exists traps, CatchesAll m x traps /\ v = Zlength traps) (fun x => x) out.

(** Mathematical interface used by the annotated implementation.  The
    definitions below describe number-theoretic objects and stable program
    states; none of them executes the C control flow. *)

Fixpoint coprime_count (n : Z) (fuel : nat) : Z :=
  match fuel with
  | O => 0
  | S k =>
      coprime_count n k +
      if Z.eqb (Z.gcd (Z.of_nat (S k)) n) 1 then 1 else 0
  end.

Definition EulerPhi (n : Z) : Z := coprime_count n (Z.to_nat n).

Fixpoint order_search (x n k : Z) (fuel : nat) : Z :=
  match fuel with
  | O => 1
  | S fuel' =>
      if Z.eqb (Z.pow x k mod n) 1
      then k
      else order_search x n (k + 1) fuel'
  end.

Definition Ord (x n : Z) : Z :=
  if Z.eqb n 1 then 1
  else order_search (x mod n) n 1 (Z.to_nat (EulerPhi n)).

Definition IsPrime (p : Z) : Prop :=
  1 < p /\
  forall q, 1 < q < p -> p mod q <> 0.

Definition CycleTerm (x d : Z) : Z :=
  if Z.eqb d 1 then 0 else EulerPhi d / Ord (x mod d) d.

Fixpoint sum_nat_range (first count : nat) (f : nat -> Z) : Z :=
  match count with
  | O => 0
  | S count' => f first + sum_nat_range (S first) count' f
  end.

Fixpoint walk_suffix_lists (pr pe : list Z) (x d : Z) : Z :=
  match pr, pe with
  | p :: pr', exponent :: pe' =>
      sum_nat_range 0 (S (Z.to_nat exponent))
        (fun e => walk_suffix_lists pr' pe' x (d * Z.pow p (Z.of_nat e)))
  | _, _ => CycleTerm x d
  end.

Definition WalkSuffix (pr pe : list Z) (x i d : Z) : Z :=
  walk_suffix_lists (skipn (Z.to_nat i) pr) (skipn (Z.to_nat i) pe) x d.

Definition WalkExpSuffix
    (pr pe : list Z) (x i next_e d : Z) : Z :=
  let exponent := Znth i pe 0 in
  sum_nat_range (Z.to_nat next_e)
    (Z.to_nat (exponent - next_e + 1))
    (fun e =>
       WalkSuffix pr pe x (i + 1)
         (d * Z.pow (Znth i pr 0) (Z.of_nat e))).

Definition WalkLoopState
    (pr pe : list Z) (x i d before current next_e : Z) : Prop :=
  current + WalkExpSuffix pr pe x i next_e d =
  before + WalkSuffix pr pe x i d.

Definition WalkGlobalBounds (m x : Z) : Prop :=
  2 <= m <= 100000000000000 /\
  1 <= x < m /\
  Z.gcd x m = 1.

Definition WalkMachineBounds (m d phi ord : Z) : Prop :=
  0 < d <= m /\ 0 < phi <= m /\ 0 < ord <= m.

Definition WalkBudget (m before work : Z) : Prop :=
  0 <= before /\ 0 <= work /\ before + work <= m.

Definition WalkPendingState
    (pr pe : list Z) (m x i d before current next_e : Z) : Prop :=
  WalkLoopState pr pe x i d before current next_e /\
  WalkBudget m current (WalkExpSuffix pr pe x i next_e d).

Definition WalkExponentState
    (m p exponent max_exponent pk ph : Z) : Prop :=
  2 <= p <= m /\
  1 <= exponent <= max_exponent + 1 /\
  1 <= pk <= m /\ 1 <= ph <= m /\
  pk = Z.pow p (exponent - 1) /\
  ph = EulerPhi pk.

Definition MulLoopState (a0 b0 modulus a b r : Z) : Prop :=
  (r + a * b) mod modulus = (a0 * b0) mod modulus.

Definition PowLoopState (base exponent modulus b e r : Z) : Prop :=
  (r * Z.pow b e) mod modulus = Z.pow base exponent mod modulus.

Definition GcdLoopState (a0 b0 a b : Z) : Prop :=
  Z.gcd a b = Z.gcd a0 b0.

Definition OrderInput (x modulus phi : Z) : Prop :=
  1 < modulus /\
  phi = EulerPhi modulus /\
  Z.gcd x modulus = 1 /\
  0 < phi <= modulus /\
  0 < Ord x modulus /\
  (Ord x modulus | phi) /\
  Z.pow x phi mod modulus = 1.

Definition OrderResult (x modulus result : Z) : Prop :=
  result = Ord x modulus /\
  0 < result /\
  (result | EulerPhi modulus) /\
  Z.pow x result mod modulus = 1.

Definition OrderTrialState
    (x modulus phi q t ord : Z) : Prop :=
  OrderInput x modulus phi /\
  0 < t /\ t <= phi /\ (t | phi) /\
  0 < ord /\ ord <= phi /\ (ord | phi) /\
  (Ord x modulus | ord) /\
  Z.pow x ord mod modulus = 1 /\
  forall prime, IsPrime prime -> prime < q -> t mod prime <> 0.

Definition OrderFactorState
    (x modulus phi q t ord : Z) : Prop :=
  OrderTrialState x modulus phi q t ord /\ IsPrime q.

Definition OrderStripState
    (x modulus phi q t ord : Z) : Prop :=
  OrderFactorState x modulus phi q t ord /\ t mod q <> 0.

Fixpoint factor_product (pr pe : list Z) : Z :=
  match pr, pe with
  | p :: pr', e :: pe' => Z.pow p e * factor_product pr' pe'
  | _, _ => 1
  end.

Definition FactorPrefix
    (m candidate remainder : Z) (pr pe : list Z) : Prop :=
  Zlength pr = Zlength pe /\
  0 <= Zlength pr <= 64 /\
  2 <= candidate /\
  0 < remainder <= m /\
  m = factor_product pr pe * remainder /\
  (forall k, 0 <= k < Zlength pr ->
     IsPrime (Znth k pr 0) /\
     1 <= Znth k pe 0 /\
     Znth k pr 0 < candidate) /\
  (forall prime, IsPrime prime -> prime < candidate ->
     remainder mod prime <> 0).

Definition TrialState
    (m candidate remainder : Z) (pr pe : list Z) : Prop :=
  FactorPrefix m candidate remainder pr pe.

Definition FactorAtPrime
    (m candidate original_remainder remainder exponent : Z)
    (pr pe : list Z) : Prop :=
  FactorPrefix m candidate original_remainder pr pe /\
  IsPrime candidate /\
  original_remainder mod candidate = 0 /\
  0 <= exponent /\
  original_remainder = Z.pow candidate exponent * remainder /\
  0 < remainder <= original_remainder.

Definition ValidFactorTable (m : Z) (pr pe : list Z) : Prop :=
  Zlength pr = Zlength pe /\
  0 <= Zlength pr <= 64 /\
  m = factor_product pr pe /\
  (forall k, 0 <= k < Zlength pr ->
     IsPrime (Znth k pr 0) /\ 1 <= Znth k pe 0) /\
  (forall j k,
     0 <= j /\ j < k /\ k < Zlength pr ->
     Znth j pr 0 < Znth k pr 0).

Inductive PrefixSelected (pr pe : list Z) : Z -> Z -> Prop :=
| prefix_selected_zero :
    PrefixSelected pr pe 0 1
| prefix_selected_step : forall i d e,
    PrefixSelected pr pe i d ->
    0 <= i < Zlength pr ->
    0 <= e <= Znth i pe 0 ->
    PrefixSelected pr pe (i + 1)
      (d * Z.pow (Znth i pr 0) e).

Definition PrefixChoice
    (pr pe : list Z) (x i d phi ord : Z) : Prop :=
  Zlength pr = Zlength pe /\
  0 <= i <= Zlength pr /\
  PrefixSelected pr pe i d /\
  0 < d /\ 0 < phi /\ 0 < ord /\
  phi = EulerPhi d /\ ord = Ord x d /\ Z.gcd x d = 1.

Definition PrimePowerTransition
    (x d phi ord p e pk ph o g next_d next_phi next_ord : Z) : Prop :=
  0 < d /\ 1 < p /\ 1 <= e /\
  pk = Z.pow p e /\
  ph = EulerPhi pk /\
  o = Ord (x mod pk) pk /\
  g = Z.gcd ord o /\
  next_d = d * pk /\
  next_phi = phi * ph /\
  next_ord = ord / g * o /\
  Z.gcd d pk = 1 /\
  EulerPhi next_d = EulerPhi d * EulerPhi pk /\
  Ord x next_d = next_ord /\
  0 < next_d /\ 0 < next_phi /\ 0 < next_ord.

Definition CycleAnswer (m x total : Z) : Prop :=
  0 <= total <= m /\ Spec m x (total + 1).

Definition DivisorCycleSum (m x total : Z) : Prop :=
  min_value_of_subset Z.le
    (fun v => exists traps, CatchesAll m x traps /\ v = Zlength traps)
    (fun z => z) (total + 1).

(** Projection/transition interface.  The difficult facts remain explicit
    premises; these lemmas never manufacture number theory. *)

Lemma order_input_phi x modulus phi :
  OrderInput x modulus phi -> phi = EulerPhi modulus.
Proof. intros (_ & H & _); exact H. Qed.

Lemma order_input_positive x modulus phi :
  OrderInput x modulus phi -> 0 < phi /\ 0 < Ord x modulus.
Proof. intros (_ & _ & _ & Hphi & Hord & _); tauto. Qed.

Lemma order_result_positive x modulus result :
  OrderResult x modulus result -> 0 < result.
Proof. intros (_ & H & _); exact H. Qed.

Lemma order_result_divides_phi x modulus result :
  OrderResult x modulus result -> (result | EulerPhi modulus).
Proof. intros (_ & _ & H & _); exact H. Qed.

Lemma order_factor_completed x modulus phi q t ord :
  OrderFactorState x modulus phi q t ord ->
  t mod q <> 0 ->
  OrderStripState x modulus phi q t ord.
Proof. unfold OrderStripState; tauto. Qed.

Lemma order_strip_advance x modulus phi q t ord :
  OrderStripState x modulus phi q t ord ->
  OrderTrialState x modulus phi (q + 1) t ord.
Proof.
  intros [[Htrial Hqprime] Hqdone].
  unfold OrderTrialState in Htrial |-.
  destruct Htrial as
      (Hinput & Htpos & Htle & Htdiv & Hordpos & Hordle & Horddiv &
       Htrueord & Hpow & Hsmaller).
  split; [exact Hinput |].
  split; [exact Htpos |].
  split; [exact Htle |].
  split; [exact Htdiv |].
  split; [exact Hordpos |].
  split; [exact Hordle |].
  split; [exact Horddiv |].
  split; [exact Htrueord |].
  split; [exact Hpow |].
  intros prime Hprime Hbelow.
  destruct (Z.lt_ge_cases prime q) as [Hlt | Hge].
  - apply Hsmaller; assumption.
  - assert (prime = q) by lia.
    subst prime; exact Hqdone.
Qed.

Lemma walk_global_coprime m x :
  WalkGlobalBounds m x -> Z.gcd x m = 1.
Proof. intros (_ & _ & H); exact H. Qed.

Lemma walk_exponent_phi m p exponent max_exponent pk ph :
  WalkExponentState m p exponent max_exponent pk ph ->
  ph = EulerPhi pk.
Proof. intros (_ & _ & _ & _ & _ & H); exact H. Qed.

Lemma factor_at_prime_is_prime m p t0 t e prs pes :
  FactorAtPrime m p t0 t e prs pes -> IsPrime p.
Proof. intros (_ & H & _); exact H. Qed.

Lemma factor_at_prime_exit_positive m p t0 t e prs pes :
  FactorAtPrime m p t0 t e prs pes ->
  t mod p <> 0 ->
  1 <= e.
Proof.
  intros (_ & _ & Hentry_divides & He_nonneg & Hdecomp & _) Hexit.
  assert (e <> 0).
  { intro Heq; subst e.
    rewrite Z.pow_0_r, Z.mul_1_l in Hdecomp.
    rewrite Hdecomp in Hentry_divides.
    exact (Hexit Hentry_divides). }
  lia.
Qed.

Lemma valid_factor_table_lengths m prs pes :
  ValidFactorTable m prs pes -> Zlength prs = Zlength pes.
Proof. intros (H & _); exact H. Qed.

Lemma prefix_choice_positive prs pes x i d phi ord :
  PrefixChoice prs pes x i d phi ord -> 0 < d /\ 0 < phi /\ 0 < ord.
Proof. intros (_ & _ & _ & Hd & Hp & Ho & _); tauto. Qed.

Lemma prefix_choice_selected prs pes x i d phi ord :
  PrefixChoice prs pes x i d phi ord -> PrefixSelected prs pes i d.
Proof. intros (_ & _ & H & _); exact H. Qed.

Lemma prefix_selected_extend prs pes i d e :
  PrefixSelected prs pes i d ->
  0 <= i < Zlength prs ->
  0 <= e <= Znth i pes 0 ->
  PrefixSelected prs pes (i + 1) (d * Z.pow (Znth i prs 0) e).
Proof. exact (prefix_selected_step prs pes i d e). Qed.

Lemma prime_power_transition_values
    x d phi ord p e pk ph o g next_d next_phi next_ord :
  PrimePowerTransition x d phi ord p e pk ph o g next_d next_phi next_ord ->
  next_d = d * pk /\ next_phi = phi * ph /\ next_ord = ord / g * o.
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & Hd & Hp & Ho & _).
  tauto.
Qed.

Lemma walk_exp_suffix_zero pr pe x i d :
  Znth i pe 0 < 0 -> WalkExpSuffix pr pe x i 0 d = 0.
Proof.
  intros Hneg. unfold WalkExpSuffix.
  replace (Z.to_nat (Znth i pe 0 - 0 + 1)) with 0%nat by lia.
  reflexivity.
Qed.

Lemma walk_exp_suffix_exhausted pr pe x i d next_e :
  Znth i pe 0 < next_e ->
  WalkExpSuffix pr pe x i next_e d = 0.
Proof.
  intros Hexhausted. unfold WalkExpSuffix.
  replace (Z.to_nat (Znth i pe 0 - next_e + 1)) with 0%nat by lia.
  reflexivity.
Qed.

Lemma walk_pending_terminal pr pe m x i d before current next_e :
  WalkPendingState pr pe m x i d before current next_e ->
  Znth i pe 0 < next_e ->
  current = before + WalkSuffix pr pe x i d.
Proof.
  intros [Hconserve _] Hexhausted.
  unfold WalkLoopState in Hconserve.
  rewrite (walk_exp_suffix_exhausted pr pe x i d next_e Hexhausted)
    in Hconserve.
  lia.
Qed.

Lemma cycle_answer_to_spec m x total :
  CycleAnswer m x total -> Spec m x (total + 1).
Proof. intros (_ & H); exact H. Qed.

(** Consumer-designed order states.  These are deliberately parallel to the
    earlier trial/factor/strip predicates: the original declarations remain
    available, while the C order loop uses this strengthened family.  The
    ghost [excess] satisfies [ord = Ord * excess], and prime support records
    that every still-removable excess prime is present in the unprocessed
    remainder (apart from the one active prime during stripping). *)

Definition OrderCore
    (x modulus phi ord excess : Z) : Prop :=
  OrderInput x modulus phi /\
  0 < ord /\ ord <= phi /\ (ord | phi) /\
  0 < excess /\
  ord = Ord x modulus * excess /\
  Z.pow x ord mod modulus = 1.

Definition PrimeSupport (excess remainder : Z) : Prop :=
  forall p, IsPrime p -> (p | excess) -> (p | remainder).

Definition PrimeSupportExcept (excess active remainder : Z) : Prop :=
  forall p, IsPrime p -> (p | excess) -> p = active \/ (p | remainder).

Definition NoPrimeBelow (candidate remainder : Z) : Prop :=
  forall p, IsPrime p -> p < candidate -> remainder mod p <> 0.

Definition OrderTrialStateEx
    (x modulus phi candidate remainder ord : Z) : Prop :=
  OrderInput x modulus phi /\
  0 < remainder /\ remainder <= phi /\ (remainder | phi) /\
  NoPrimeBelow candidate remainder /\
  exists excess,
    OrderCore x modulus phi ord excess /\
    PrimeSupport excess remainder.

Definition OrderFactorStateEx
    (x modulus phi active remainder ord : Z) : Prop :=
  OrderInput x modulus phi /\
  IsPrime active /\
  0 < remainder /\ remainder <= phi /\ (remainder | phi) /\
  NoPrimeBelow active remainder /\
  exists excess,
    OrderCore x modulus phi ord excess /\
    PrimeSupportExcept excess active remainder.

Definition OrderStripStateEx
    (x modulus phi active remainder ord : Z) : Prop :=
  OrderFactorStateEx x modulus phi active remainder ord /\
  remainder mod active <> 0.

Definition OrderFinalStateEx
    (x modulus phi active ord : Z) : Prop :=
  OrderInput x modulus phi /\
  IsPrime active /\
  exists excess,
    OrderCore x modulus phi ord excess /\
    (forall p, IsPrime p -> (p | excess) -> p = active).

Definition OrderPowerLaw (x modulus : Z) : Prop :=
  forall k, 0 <= k ->
    (Z.pow x k mod modulus = 1 <-> (Ord x modulus | k)).

Lemma order_ex_prime_positive p : IsPrime p -> 1 < p.
Proof. intros [Hp _]; exact Hp. Qed.

Lemma order_ex_is_prime_iff_std p : IsPrime p <-> prime p.
Proof.
  rewrite <- prime_alt.
  unfold IsPrime, prime'.
  split.
  - intros [Hp Htest].
    split; [exact Hp |].
    intros q [Hq Hqp] Hdiv.
    specialize (Htest q (conj Hq Hqp)).
    apply Htest.
    apply (proj2 (Z.mod_divide p q ltac:(lia))); exact Hdiv.
  - intros [Hp Htest].
    split; [exact Hp |].
    intros q [Hq Hqp] Hmod.
    apply (Htest q (conj Hq Hqp)).
    apply (proj1 (Z.mod_divide p q ltac:(lia))); exact Hmod.
Qed.

Lemma order_ex_std_prime_factor_exists :
  forall n, 1 < n -> exists p, prime p /\ (p | n).
Proof.
  intro n.
  refine (well_founded_induction_type
            (Z.lt_wf 2)
            (fun a => 1 < a -> exists p, prime p /\ (p | a))
            _ n).
  intros a IH Ha.
  destruct (prime_dec a) as [Hprime | Hnotprime].
  - exists a; split; [exact Hprime | apply Z.divide_refl].
  - destruct (not_prime_divide a Ha Hnotprime)
      as [d [[Hdpos Hdlt] Hddiv]].
    destruct (IH d ltac:(lia) Hdpos) as [p [Hpprime Hpdiv]].
    exists p; split; [exact Hpprime |].
    eapply Z.divide_trans; eauto.
Qed.

Lemma order_ex_prime_factor_exists :
  forall n, 1 < n -> exists p, IsPrime p /\ (p | n).
Proof.
  intros n Hn.
  destruct (order_ex_std_prime_factor_exists n Hn) as [p [Hp Hdiv]].
  exists p; split; [apply order_ex_is_prime_iff_std; exact Hp | exact Hdiv].
Qed.

Lemma order_ex_prime_divisor_product :
  forall p a b, IsPrime p -> (p | a * b) -> (p | a) \/ (p | b).
Proof.
  intros p a b Hp Hdiv.
  eapply prime_mult; [apply order_ex_is_prime_iff_std; exact Hp | exact Hdiv].
Qed.

Lemma order_ex_prime_divisor_of_prime :
  forall p q, IsPrime p -> IsPrime q -> (p | q) -> p = q.
Proof.
  intros p q Hp Hq Hdiv.
  eapply prime_div_prime.
  - apply order_ex_is_prime_iff_std; exact Hp.
  - apply order_ex_is_prime_iff_std; exact Hq.
  - exact Hdiv.
Qed.

Lemma order_ex_no_prime_below_not_divides candidate remainder p :
  NoPrimeBelow candidate remainder ->
  IsPrime p ->
  p < candidate ->
  ~ (p | remainder).
Proof.
  intros Hnone Hp Hlt Hdiv.
  specialize (Hnone p Hp Hlt).
  apply Hnone.
  apply (proj2 (Z.mod_divide remainder p ltac:(
    pose proof (order_ex_prime_positive p Hp); lia))); exact Hdiv.
Qed.

Lemma order_ex_smallest_remaining_prime candidate remainder :
  2 <= candidate ->
  0 < remainder ->
  NoPrimeBelow candidate remainder ->
  remainder mod candidate = 0 ->
  IsPrime candidate.
Proof.
  intros Hcandidate Hremainder Hnone Hmod.
  split; [lia |].
  intros q [Hqpos Hqlt] Hqmod.
  assert (Hq0 : q <> 0) by lia.
  assert (Hqdivcandidate : (q | candidate)).
  { apply (proj1 (Z.mod_divide candidate q Hq0)); exact Hqmod. }
  destruct (order_ex_prime_factor_exists q Hqpos) as [p [Hp Hpdivq]].
  assert (Hp_le_q : p <= q).
  { eapply Z.divide_pos_le; eauto; lia. }
  assert (Hcandidate_div_remainder : (candidate | remainder)).
  { apply (proj1 (Z.mod_divide remainder candidate ltac:(lia))); exact Hmod. }
  assert (Hpdivremainder : (p | remainder)).
  { eapply Z.divide_trans; [exact Hpdivq |].
    eapply Z.divide_trans; eauto. }
  eapply (order_ex_no_prime_below_not_divides candidate remainder p);
    eauto; lia.
Qed.

Lemma order_ex_residual_remainder_prime candidate remainder :
  2 <= candidate ->
  1 < remainder ->
  candidate * candidate > remainder ->
  NoPrimeBelow candidate remainder ->
  IsPrime remainder.
Proof.
  intros Hcandidate Hremainder Hguard Hnone.
  split; [exact Hremainder |].
  intros q [Hqpos Hqlt] Hqmod.
  assert (Hq0 : q <> 0) by lia.
  assert (Hqdiv : (q | remainder)).
  { apply (proj1 (Z.mod_divide remainder q Hq0)); exact Hqmod. }
  destruct Hqdiv as [cofactor Hfactorization].
  assert (Hcofactor : 1 < cofactor) by nia.
  assert (Hsmall : q < candidate \/ cofactor < candidate) by nia.
  destruct Hsmall as [Hqsmall | Hcofsmall].
  - destruct (order_ex_prime_factor_exists q Hqpos) as [p [Hp Hpdiv]].
    assert (Hp_le_q : p <= q).
    { eapply Z.divide_pos_le; eauto; lia. }
    assert (Hqdivremainder : (q | remainder)).
    { exists cofactor; exact Hfactorization. }
    assert (Hpdivremainder : (p | remainder)).
    { eapply Z.divide_trans; [exact Hpdiv | exact Hqdivremainder]. }
    eapply (order_ex_no_prime_below_not_divides candidate remainder p);
      eauto; lia.
  - destruct (order_ex_prime_factor_exists cofactor Hcofactor)
      as [p [Hp Hpdiv]].
    assert (Hp_le_cofactor : p <= cofactor).
    { eapply Z.divide_pos_le; eauto; lia. }
    assert (Hcofactordiv : (cofactor | remainder)).
    { exists q; nia. }
    assert (Hpdivremainder : (p | remainder)).
    { eapply Z.divide_trans; [exact Hpdiv | exact Hcofactordiv]. }
    eapply (order_ex_no_prime_below_not_divides candidate remainder p);
      eauto; lia.
Qed.

Lemma order_ex_pow_mod_base_nat a modulus n :
  modulus <> 0 ->
  Z.pow (a mod modulus) (Z.of_nat n) mod modulus =
  Z.pow a (Z.of_nat n) mod modulus.
Proof.
  intros Hmodulus.
  induction n as [|n IH].
  - cbn. reflexivity.
  - rewrite Nat2Z.inj_succ.
    rewrite !Z.pow_succ_r by apply Nat2Z.is_nonneg.
    rewrite (Z.mul_mod
      (a mod modulus) (Z.pow (a mod modulus) (Z.of_nat n))
      modulus Hmodulus).
    rewrite (Z.mul_mod
      a (Z.pow a (Z.of_nat n)) modulus Hmodulus).
    rewrite IH.
    rewrite Z.mod_mod by exact Hmodulus.
    reflexivity.
Qed.

Lemma order_ex_pow_mod_base a modulus exponent :
  modulus <> 0 ->
  0 <= exponent ->
  Z.pow (a mod modulus) exponent mod modulus =
  Z.pow a exponent mod modulus.
Proof.
  intros Hmodulus Hexponent.
  rewrite <- (Z2Nat.id exponent Hexponent).
  apply order_ex_pow_mod_base_nat; exact Hmodulus.
Qed.

Lemma order_ex_pow_add_mod_left_one a modulus left right :
  1 < modulus ->
  0 <= left ->
  0 <= right ->
  Z.pow a left mod modulus = 1 ->
  Z.pow a (left + right) mod modulus =
  Z.pow a right mod modulus.
Proof.
  intros Hmodulus Hleft Hright Hone.
  rewrite Z.pow_add_r by assumption.
  rewrite Z.mul_mod by lia.
  rewrite Hone.
  replace (1 * (Z.pow a right mod modulus))
    with (Z.pow a right mod modulus) by ring.
  apply Z.mod_mod; lia.
Qed.

Lemma order_ex_pow_multiple_mod_one a modulus period multiplier :
  1 < modulus ->
  0 <= period ->
  0 <= multiplier ->
  Z.pow a period mod modulus = 1 ->
  Z.pow a (period * multiplier) mod modulus = 1.
Proof.
  intros Hmodulus Hperiod Hmultiplier Hone.
  rewrite Z.pow_mul_r by assumption.
  rewrite <- (order_ex_pow_mod_base
    (Z.pow a period) modulus multiplier ltac:(lia) Hmultiplier).
  rewrite Hone.
  rewrite Z.pow_1_l by exact Hmultiplier.
  apply Z.mod_small; lia.
Qed.

Lemma order_ex_pow_divmod_remainder a modulus period exponent :
  1 < modulus ->
  0 < period ->
  0 <= exponent ->
  Z.pow a period mod modulus = 1 ->
  Z.pow a exponent mod modulus =
  Z.pow a (exponent mod period) mod modulus.
Proof.
  intros Hmodulus Hperiod Hexponent Hperiodpow.
  pose proof (Z.div_mod exponent period ltac:(lia)) as Hdecompose.
  pose proof (Z.mod_pos_bound exponent period Hperiod) as Hrem.
  pose proof (Z.div_pos exponent period Hexponent Hperiod) as Hquotient.
  rewrite Hdecompose at 1.
  apply order_ex_pow_add_mod_left_one; try lia.
  apply (order_ex_pow_multiple_mod_one
    a modulus period (exponent / period)); try lia; assumption.
Qed.

Lemma order_ex_search_minimal base modulus start fuel candidate :
  1 <= start ->
  start <= candidate < order_search base modulus start fuel ->
  Z.pow base candidate mod modulus <> 1.
Proof.
  revert start candidate.
  induction fuel as [|fuel IH]; intros start candidate Hstart Hrange.
  - cbn [order_search] in Hrange; lia.
  - cbn [order_search] in Hrange.
    destruct (Z.eqb (Z.pow base start mod modulus) 1)
      eqn:Hcurrent.
    + lia.
    + apply Z.eqb_neq in Hcurrent.
      destruct (Z.eq_dec candidate start) as [Heq | Hneq].
      * subst candidate; exact Hcurrent.
      * apply (IH (start + 1) candidate); [lia |].
        split; [lia | exact (proj2 Hrange)].
Qed.

Lemma order_ex_search_terminal_spec base modulus start fuel :
  1 <= start ->
  Z.pow base (start + Z.of_nat fuel) mod modulus = 1 ->
  let result := order_search base modulus start (S fuel) in
  start <= result <= start + Z.of_nat fuel /\
  Z.pow base result mod modulus = 1.
Proof.
  revert start.
  induction fuel as [|fuel IH]; intros start Hstart Hterminal.
  - cbn [order_search] in *.
    destruct (Z.eqb (Z.pow base start mod modulus) 1)
      eqn:Hcurrent.
    + apply Z.eqb_eq in Hcurrent.
      split; [lia | exact Hcurrent].
    + apply Z.eqb_neq in Hcurrent.
      exfalso; apply Hcurrent.
      replace (start + Z.of_nat 0) with start in Hterminal by ring.
      exact Hterminal.
  - cbn [order_search].
    destruct (Z.eqb (Z.pow base start mod modulus) 1)
      eqn:Hcurrent.
    + apply Z.eqb_eq in Hcurrent.
      split; [lia | exact Hcurrent].
    + assert (Hterminal' :
        Z.pow base (start + 1 + Z.of_nat fuel) mod modulus = 1).
      { rewrite Nat2Z.inj_succ in Hterminal.
        replace (start + 1 + Z.of_nat fuel)
          with (start + Z.succ (Z.of_nat fuel)) by lia.
        exact Hterminal. }
      destruct (IH (start + 1) ltac:(lia) Hterminal')
        as [Hbounds Hsound].
      change
        (start <= order_search base modulus (start + 1) (S fuel) <=
           start + Z.of_nat (S fuel) /\
         Z.pow base (order_search base modulus (start + 1) (S fuel))
           mod modulus = 1).
      split; [rewrite Nat2Z.inj_succ; lia | exact Hsound].
Qed.

Lemma order_ex_ord_search_exact x modulus phi :
  OrderInput x modulus phi ->
  1 <= Ord x modulus <= phi /\
  Z.pow x (Ord x modulus) mod modulus = 1 /\
  (forall candidate,
      1 <= candidate < Ord x modulus ->
      Z.pow x candidate mod modulus <> 1).
Proof.
  intros Hinput.
  unfold OrderInput in Hinput.
  destruct Hinput as
      (Hmodulus & Hphi & Hgcd & Hphibounds & Hordpos & Hordphi & Hphipow).
  unfold Ord.
  assert (Hmodulus_neq : Z.eqb modulus 1 = false).
  { apply Z.eqb_neq; lia. }
  rewrite Hmodulus_neq.
  rewrite <- Hphi.
  remember (Z.to_nat phi) as count eqn:Hcount.
  assert (Hcount_value : Z.of_nat count = phi).
  { rewrite Hcount; apply Z2Nat.id; lia. }
  destruct count as [|fuel].
  - cbn in Hcount_value; lia.
  - assert (Hterminal_exponent : 1 + Z.of_nat fuel = phi).
    { rewrite Nat2Z.inj_succ in Hcount_value; lia. }
    assert (Hterminal :
      Z.pow (x mod modulus) (1 + Z.of_nat fuel) mod modulus = 1).
    { rewrite Hterminal_exponent.
      rewrite order_ex_pow_mod_base by lia.
      exact Hphipow. }
    destruct (order_ex_search_terminal_spec
                (x mod modulus) modulus 1 fuel ltac:(lia) Hterminal)
      as [Hbounds Hsound].
    split.
    + rewrite Hterminal_exponent in Hbounds; exact Hbounds.
    + split.
      * rewrite <- (order_ex_pow_mod_base x modulus
                      (order_search (x mod modulus) modulus 1 (S fuel)))
          by lia.
        exact Hsound.
      * intros candidate Hcandidate Hcandidatepow.
        eapply (order_ex_search_minimal
                  (x mod modulus) modulus 1 (S fuel) candidate);
          try eassumption; try lia.
        rewrite order_ex_pow_mod_base by lia.
        exact Hcandidatepow.
Qed.

Lemma order_ex_minimal_success_divides
    x modulus period exponent :
  1 < modulus ->
  0 < period ->
  Z.pow x period mod modulus = 1 ->
  (forall candidate,
      1 <= candidate < period ->
      Z.pow x candidate mod modulus <> 1) ->
  0 <= exponent ->
  Z.pow x exponent mod modulus = 1 ->
  (period | exponent).
Proof.
  intros Hmodulus Hperiod Hperiodpow Hminimal Hexponent Hexponentpow.
  pose proof (Z.mod_pos_bound exponent period Hperiod) as Hremainder.
  assert (Hremainderpow :
    Z.pow x (exponent mod period) mod modulus = 1).
  { rewrite <- (order_ex_pow_divmod_remainder
                  x modulus period exponent
                  Hmodulus Hperiod Hexponent Hperiodpow).
    exact Hexponentpow. }
  destruct (Z.eq_dec (exponent mod period) 0) as [Hzero | Hnonzero].
  - apply (proj1 (Z.mod_divide exponent period ltac:(lia))); exact Hzero.
  - exfalso.
    eapply (Hminimal (exponent mod period)); [lia | exact Hremainderpow].
Qed.

Lemma order_ex_success_of_period_divides
    x modulus period exponent :
  1 < modulus ->
  0 < period ->
  Z.pow x period mod modulus = 1 ->
  0 <= exponent ->
  (period | exponent) ->
  Z.pow x exponent mod modulus = 1.
Proof.
  intros Hmodulus Hperiod Hperiodpow Hexponent [multiplier Heq].
  assert (Hmultiplier : 0 <= multiplier) by nia.
  rewrite Heq.
  rewrite Z.mul_comm.
  apply order_ex_pow_multiple_mod_one; try lia; assumption.
Qed.

Lemma order_input_power_law x modulus phi :
  OrderInput x modulus phi -> OrderPowerLaw x modulus.
Proof.
  intros Hinput.
  pose proof Hinput as Hbounds.
  unfold OrderInput in Hbounds.
  destruct Hbounds as
      (Hmodulus & Hphi & Hgcd & Hphibounds & Hordpos & Hordphi & Hphipow).
  destruct (order_ex_ord_search_exact x modulus phi Hinput)
    as [Hordbounds [Hordpow Hminimal]].
  unfold OrderPowerLaw.
  intros exponent Hexponent.
  split.
  - intros Hexponentpow.
    eapply order_ex_minimal_success_divides; eauto; lia.
  - intros Hdivides.
    eapply order_ex_success_of_period_divides; eauto; lia.
Qed.

Lemma order_ex_no_prime_below_two remainder : NoPrimeBelow 2 remainder.
Proof.
  intros p Hp Hlt.
  pose proof (order_ex_prime_positive p Hp).
  lia.
Qed.

Lemma order_ex_no_prime_below_divisor candidate remainder remainder' :
  NoPrimeBelow candidate remainder ->
  (remainder' | remainder) ->
  NoPrimeBelow candidate remainder'.
Proof.
  intros Hnone Hdiv p Hp Hlt Hmod.
  assert (Hp0 : p <> 0) by (pose proof (order_ex_prime_positive p Hp); lia).
  assert (Hpdiv_next : (p | remainder')).
  { apply (proj1 (Z.mod_divide remainder' p Hp0)); exact Hmod. }
  assert (Hpdiv : (p | remainder)).
  { eapply Z.divide_trans; eauto. }
  specialize (Hnone p Hp Hlt).
  apply Hnone.
  apply (proj2 (Z.mod_divide remainder p Hp0)); exact Hpdiv.
Qed.

Lemma order_ex_no_prime_below_advance candidate remainder :
  NoPrimeBelow candidate remainder ->
  remainder mod candidate <> 0 ->
  NoPrimeBelow (candidate + 1) remainder.
Proof.
  intros Hnone Hcandidate p Hp Hlt.
  destruct (Z.lt_trichotomy p candidate) as [Hpc | [Heq | Hcp]].
  - apply Hnone; assumption.
  - subst p; exact Hcandidate.
  - lia.
Qed.

Lemma order_ex_core_excess_divides_ord x modulus phi ord excess p :
  OrderCore x modulus phi ord excess ->
  (p | excess) ->
  (p | ord).
Proof.
  intros (_ & _ & _ & _ & _ & Heq & _) [k Hk].
  exists (Ord x modulus * k).
  rewrite Heq, Hk; ring.
Qed.

Lemma order_ex_core_reduce
    x modulus phi ord excess active ord' :
  OrderPowerLaw x modulus ->
  OrderCore x modulus phi ord excess ->
  IsPrime active ->
  ord = active * ord' ->
  Z.pow x ord' mod modulus = 1 ->
  exists excess',
    excess = active * excess' /\
    OrderCore x modulus phi ord' excess'.
Proof.
  intros Hpower Hcore Hactive Hord Hpow.
  destruct Hcore as
      (Hinput & Hordpos & Hordle & Hordphi & Hexpos & Hexeq & Hordpow).
  pose proof (order_ex_prime_positive active Hactive) as Hactivepos.
  assert (Hord'pos : 0 < ord') by nia.
  assert (HOpos : 0 < Ord x modulus).
  { unfold OrderInput in Hinput; tauto. }
  assert (HOdiv : (Ord x modulus | ord')).
  { apply (proj1 (Hpower ord' ltac:(lia))); exact Hpow. }
  destruct HOdiv as [excess' Hexcess'].
  assert (Hexcess'_pos : 0 < excess') by nia.
  assert (Hexfactor : excess = active * excess') by nia.
  assert (Hord'divord : (ord' | ord)).
  { exists active; nia. }
  assert (Hord'phi : (ord' | phi)).
  { eapply Z.divide_trans; eauto. }
  exists excess'.
  split; [exact Hexfactor |].
  unfold OrderCore.
  split; [exact Hinput |].
  repeat split.
  - exact Hord'pos.
  - eapply Z.divide_pos_le; eauto; lia.
  - exact Hord'phi.
  - exact Hexcess'_pos.
  - nia.
  - exact Hpow.
Qed.

Lemma order_ex_core_irreducible_from_ord
    x modulus phi ord excess active :
  OrderCore x modulus phi ord excess ->
  ~ (active | ord) ->
  ~ (active | excess).
Proof.
  intros Hcore Hnotord Hexdiv.
  apply Hnotord.
  eapply order_ex_core_excess_divides_ord; eauto.
Qed.

Lemma order_ex_core_irreducible_from_pow_failure
    x modulus phi ord excess active quotient :
  OrderPowerLaw x modulus ->
  OrderCore x modulus phi ord excess ->
  IsPrime active ->
  ord = active * quotient ->
  Z.pow x quotient mod modulus <> 1 ->
  ~ (active | excess).
Proof.
  intros Hpower Hcore Hactive Hord Hpowfail [k Hk].
  destruct Hcore as
      (Hinput & Hordpos & Hordle & Hordphi & Hexpos & Hexeq & Hordpow).
  assert (Hactivepos : 1 < active) by (apply order_ex_prime_positive; exact Hactive).
  assert (HOpos : 0 < Ord x modulus).
  { unfold OrderInput in Hinput; tauto. }
  assert (Hquotient : quotient = Ord x modulus * k) by nia.
  apply Hpowfail.
  apply (proj2 (Hpower quotient ltac:(nia))).
  exists k; nia.
Qed.

Lemma order_trial_init_ex x modulus phi :
  OrderInput x modulus phi ->
  OrderTrialStateEx x modulus phi 2 phi phi.
Proof.
  intros Hinput.
  pose proof Hinput as Hinput_core.
  unfold OrderInput in Hinput.
  destruct Hinput as
      (Hmodulus & Hphi & Hgcd & Hphibounds & HOpos & HOdiv & Hpow).
  destruct HOdiv as [excess Hexeq].
  assert (Hexpos : 0 < excess) by nia.
  unfold OrderTrialStateEx.
  split; [exact Hinput_core |].
  repeat split.
  - lia.
  - lia.
  - exists 1; ring.
  - apply order_ex_no_prime_below_two.
  - exists excess; split.
    + unfold OrderCore.
      split; [exact Hinput_core |].
      repeat split.
      * lia.
      * lia.
      * exists 1; ring.
      * exact Hexpos.
      * nia.
      * exact Hpow.
    + intros p Hp [k Hk].
      exists (Ord x modulus * k).
      rewrite Hexeq, Hk; ring.
Qed.

Lemma order_trial_skip_ex x modulus phi candidate remainder ord :
  OrderTrialStateEx x modulus phi candidate remainder ord ->
  remainder mod candidate <> 0 ->
  OrderTrialStateEx x modulus phi (candidate + 1) remainder ord.
Proof.
  intros (Hinput & Hrpos & Hrle & Hrphi & Hnone & Hexcess) Hmod.
  unfold OrderTrialStateEx.
  split; [exact Hinput |].
  split; [exact Hrpos |].
  split; [exact Hrle |].
  split; [exact Hrphi |].
  split.
  - eapply order_ex_no_prime_below_advance; eauto.
  - exact Hexcess.
Qed.

Lemma order_trial_enter_factor_ex
    x modulus phi candidate remainder ord :
  2 <= candidate ->
  OrderTrialStateEx x modulus phi candidate remainder ord ->
  remainder mod candidate = 0 ->
  OrderFactorStateEx x modulus phi candidate remainder ord.
Proof.
  intros Hcandidate
    (Hinput & Hrpos & Hrle & Hrphi & Hnone &
     [excess [Hcore Hsupport]]) Hmod.
  assert (Hprime : IsPrime candidate).
  { eapply order_ex_smallest_remaining_prime; eauto. }
  unfold OrderFactorStateEx.
  split; [exact Hinput |].
  split; [exact Hprime |].
  split; [exact Hrpos |].
  split; [exact Hrle |].
  split; [exact Hrphi |].
  split; [exact Hnone |].
  exists excess; split; [exact Hcore |].
  intros p Hp Hpdiv; right; eapply Hsupport; eauto.
Qed.

Lemma order_factor_step_ex
    x modulus phi active remainder remainder' ord :
  OrderFactorStateEx x modulus phi active remainder ord ->
  remainder = active * remainder' ->
  OrderFactorStateEx x modulus phi active remainder' ord.
Proof.
  intros
    (Hinput & Hactive & Hrpos & Hrle & Hrphi & Hnone &
     [excess [Hcore Hsupport]]) Hrem.
  pose proof (order_ex_prime_positive active Hactive) as Hactivepos.
  assert (Hr'pos : 0 < remainder') by nia.
  assert (Hr'divr : (remainder' | remainder)).
  { exists active; nia. }
  assert (Hr'phi : (remainder' | phi)).
  { eapply Z.divide_trans; eauto. }
  assert (Hr'le : remainder' <= phi).
  { eapply Z.divide_pos_le; eauto. nia. }
  assert (Hnone' : NoPrimeBelow active remainder').
  { eapply order_ex_no_prime_below_divisor; eauto. }
  unfold OrderFactorStateEx.
  split; [exact Hinput |].
  split; [exact Hactive |].
  split; [exact Hr'pos |].
  split; [exact Hr'le |].
  split; [exact Hr'phi |].
  split; [exact Hnone' |].
  exists excess; split; [exact Hcore |].
  intros p Hp Hpdiv.
  specialize (Hsupport p Hp Hpdiv).
  destruct Hsupport as [Heq | Hpr].
  - left; exact Heq.
  - rewrite Hrem in Hpr.
    destruct (order_ex_prime_divisor_product p active remainder' Hp Hpr)
      as [Hpactive | Hpr'].
    + left; eapply order_ex_prime_divisor_of_prime; eauto.
    + right; exact Hpr'.
Qed.

Lemma order_factor_completed_ex x modulus phi active remainder ord :
  OrderFactorStateEx x modulus phi active remainder ord ->
  remainder mod active <> 0 ->
  OrderStripStateEx x modulus phi active remainder ord.
Proof. unfold OrderStripStateEx; tauto. Qed.

Lemma order_strip_step_ex
    x modulus phi active remainder ord ord' :
  OrderStripStateEx x modulus phi active remainder ord ->
  ord = active * ord' ->
  Z.pow x ord' mod modulus = 1 ->
  OrderStripStateEx x modulus phi active remainder ord'.
Proof.
  intros
    [(Hinput & Hactive & Hrpos & Hrle & Hrphi & Hnone &
      [excess [Hcore Hsupport]]) Hremmod]
    Hord Hpow.
  pose proof (order_input_power_law x modulus phi Hinput) as Hpower.
  destruct (order_ex_core_reduce x modulus phi ord excess active ord'
              Hpower Hcore Hactive Hord Hpow)
    as [excess' [Hexfactor Hcore']].
  unfold OrderStripStateEx, OrderFactorStateEx.
  split; [| exact Hremmod].
  split; [exact Hinput |].
  split; [exact Hactive |].
  split; [exact Hrpos |].
  split; [exact Hrle |].
  split; [exact Hrphi |].
  split; [exact Hnone |].
  exists excess'; split; [exact Hcore' |].
  intros p Hp [k Hk].
  apply Hsupport; try assumption.
  exists (active * k).
  rewrite Hexfactor, Hk; ring.
Qed.

Lemma order_strip_exit_nodiv_ex
    x modulus phi active remainder ord :
  OrderStripStateEx x modulus phi active remainder ord ->
  ~ (active | ord) ->
  OrderTrialStateEx x modulus phi (active + 1) remainder ord.
Proof.
  intros
    [(Hinput & Hactive & Hrpos & Hrle & Hrphi & Hnone &
      [excess [Hcore Hsupport]]) Hremmod] Hnotord.
  assert (Hnotexcess : ~ (active | excess)).
  { eapply order_ex_core_irreducible_from_ord; eauto. }
  unfold OrderTrialStateEx.
  split; [exact Hinput |].
  split; [exact Hrpos |].
  split; [exact Hrle |].
  split; [exact Hrphi |].
  split.
  - eapply order_ex_no_prime_below_advance; eauto.
  - exists excess; split; [exact Hcore |].
    intros p Hp Hpdiv.
    destruct (Hsupport p Hp Hpdiv) as [Heq | Hpr]; [| exact Hpr].
    subst p; contradiction.
Qed.

Lemma order_strip_exit_pow_failure_ex
    x modulus phi active remainder ord quotient :
  OrderStripStateEx x modulus phi active remainder ord ->
  ord = active * quotient ->
  Z.pow x quotient mod modulus <> 1 ->
  OrderTrialStateEx x modulus phi (active + 1) remainder ord.
Proof.
  intros
    [(Hinput & Hactive & Hrpos & Hrle & Hrphi & Hnone &
      [excess [Hcore Hsupport]]) Hremmod] Hord Hpowfail.
  pose proof (order_input_power_law x modulus phi Hinput) as Hpower.
  assert (Hnotexcess : ~ (active | excess)).
  { eapply order_ex_core_irreducible_from_pow_failure; eauto. }
  unfold OrderTrialStateEx.
  split; [exact Hinput |].
  split; [exact Hrpos |].
  split; [exact Hrle |].
  split; [exact Hrphi |].
  split.
  - eapply order_ex_no_prime_below_advance; eauto.
  - exists excess; split; [exact Hcore |].
    intros p Hp Hpdiv.
    destruct (Hsupport p Hp Hpdiv) as [Heq | Hpr]; [| exact Hpr].
    subst p; contradiction.
Qed.

Lemma order_ex_core_unit_result x modulus phi ord :
  OrderCore x modulus phi ord 1 ->
  OrderResult x modulus ord.
Proof.
  intros (Hinput & Hordpos & Hordle & Hordphi & Hone & Heq & Hpow).
  unfold OrderInput in Hinput.
  destruct Hinput as
      (Hmodulus & Hphi & Hgcd & Hphibounds & HOpos & HOphi & HEuler).
  assert (Hord : ord = Ord x modulus) by nia.
  unfold OrderResult.
  repeat split.
  - exact Hord.
  - exact Hordpos.
  - rewrite <- Hphi; rewrite Hord; exact HOphi.
  - exact Hpow.
Qed.

Lemma order_ex_support_empty_is_unit excess :
  0 < excess ->
  PrimeSupport excess 1 ->
  excess = 1.
Proof.
  intros Hexpos Hsupport.
  destruct (Z_lt_le_dec 1 excess) as [Hgt | Hle]; [| lia].
  destruct (order_ex_prime_factor_exists excess Hgt) as [p [Hp Hpdiv]].
  specialize (Hsupport p Hp Hpdiv).
  destruct Hsupport as [k Hk].
  pose proof (order_ex_prime_positive p Hp).
  assert (0 < k) by nia.
  nia.
Qed.

Lemma order_trial_exit_exhausted_ex x modulus phi candidate ord :
  OrderTrialStateEx x modulus phi candidate 1 ord ->
  OrderResult x modulus ord.
Proof.
  intros
    (Hinput & Hrpos & Hrle & Hrphi & Hnone &
     [excess [Hcore Hsupport]]).
  assert (Hexcess : excess = 1).
  { eapply order_ex_support_empty_is_unit; eauto.
    unfold OrderCore in Hcore; tauto. }
  subst excess.
  eapply order_ex_core_unit_result; eauto.
Qed.

Lemma order_trial_enter_final_ex
    x modulus phi candidate remainder ord :
  2 <= candidate ->
  1 < remainder ->
  candidate * candidate > remainder ->
  OrderTrialStateEx x modulus phi candidate remainder ord ->
  OrderFinalStateEx x modulus phi remainder ord.
Proof.
  intros Hcandidate Hrgt Hguard
    (Hinput & Hrpos & Hrle & Hrphi & Hnone &
     [excess [Hcore Hsupport]]).
  assert (Hrprime : IsPrime remainder).
  { eapply order_ex_residual_remainder_prime; eauto. }
  unfold OrderFinalStateEx.
  split; [exact Hinput |].
  split; [exact Hrprime |].
  exists excess; split; [exact Hcore |].
  intros p Hp Hpdiv.
  eapply order_ex_prime_divisor_of_prime; eauto.
Qed.

Lemma order_final_step_ex x modulus phi active ord ord' :
  OrderFinalStateEx x modulus phi active ord ->
  ord = active * ord' ->
  Z.pow x ord' mod modulus = 1 ->
  OrderFinalStateEx x modulus phi active ord'.
Proof.
  intros (Hinput & Hactive & [excess [Hcore Hsupport]]) Hord Hpow.
  pose proof (order_input_power_law x modulus phi Hinput) as Hpower.
  destruct (order_ex_core_reduce x modulus phi ord excess active ord'
              Hpower Hcore Hactive Hord Hpow)
    as [excess' [Hexfactor Hcore']].
  unfold OrderFinalStateEx.
  split; [exact Hinput |].
  split; [exact Hactive |].
  exists excess'; split; [exact Hcore' |].
  intros p Hp [k Hk].
  apply Hsupport; try assumption.
  exists (active * k).
  rewrite Hexfactor, Hk; ring.
Qed.

Lemma order_ex_support_only_irreducible_is_unit excess active :
  0 < excess ->
  (forall p, IsPrime p -> (p | excess) -> p = active) ->
  ~ (active | excess) ->
  excess = 1.
Proof.
  intros Hexpos Hsupport Hnotactive.
  destruct (Z_lt_le_dec 1 excess) as [Hgt | Hle]; [| lia].
  destruct (order_ex_prime_factor_exists excess Hgt) as [p [Hp Hpdiv]].
  specialize (Hsupport p Hp Hpdiv).
  subst p; contradiction.
Qed.

Lemma order_final_exit_nodiv_ex x modulus phi active ord :
  OrderFinalStateEx x modulus phi active ord ->
  ~ (active | ord) ->
  OrderResult x modulus ord.
Proof.
  intros (Hinput & Hactive & [excess [Hcore Hsupport]]) Hnotord.
  assert (Hnotexcess : ~ (active | excess)).
  { eapply order_ex_core_irreducible_from_ord; eauto. }
  assert (Hexcess : excess = 1).
  { eapply order_ex_support_only_irreducible_is_unit; eauto.
    unfold OrderCore in Hcore; tauto. }
  subst excess.
  eapply order_ex_core_unit_result; eauto.
Qed.

Lemma order_final_exit_pow_failure_ex
    x modulus phi active ord quotient :
  OrderFinalStateEx x modulus phi active ord ->
  ord = active * quotient ->
  Z.pow x quotient mod modulus <> 1 ->
  OrderResult x modulus ord.
Proof.
  intros (Hinput & Hactive & [excess [Hcore Hsupport]]) Hord Hpowfail.
  pose proof (order_input_power_law x modulus phi Hinput) as Hpower.
  assert (Hnotexcess : ~ (active | excess)).
  { eapply order_ex_core_irreducible_from_pow_failure; eauto. }
  assert (Hexcess : excess = 1).
  { eapply order_ex_support_only_irreducible_is_unit; eauto.
    unfold OrderCore in Hcore; tauto. }
  subst excess.
  eapply order_ex_core_unit_result; eauto.
Qed.

(** VC-facing wrappers for the exact C guards and quotient assignments. *)

Lemma order_factor_step_div_ex
    x modulus phi active remainder ord :
  OrderFactorStateEx x modulus phi active remainder ord ->
  remainder mod active = 0 ->
  OrderFactorStateEx x modulus phi active (remainder / active) ord.
Proof.
  intros Hstate Hmod.
  apply (order_factor_step_ex x modulus phi active remainder
           (remainder / active) ord Hstate).
  pose proof (order_ex_prime_positive active) as Hpositive.
  unfold OrderFactorStateEx in Hstate.
  destruct Hstate as (_ & Hprime & _).
  specialize (Hpositive Hprime).
  pose proof (Z.div_mod remainder active ltac:(lia)) as Hdivision.
  nia.
Qed.

Lemma order_strip_step_div_ex
    x modulus phi active remainder ord :
  OrderStripStateEx x modulus phi active remainder ord ->
  ord mod active = 0 ->
  Z.pow x (ord / active) mod modulus = 1 ->
  OrderStripStateEx x modulus phi active remainder (ord / active).
Proof.
  intros Hstate Hmod Hpow.
  apply (order_strip_step_ex x modulus phi active remainder ord
           (ord / active) Hstate); [| exact Hpow].
  unfold OrderStripStateEx, OrderFactorStateEx in Hstate.
  destruct Hstate as [(_ & Hprime & _) _].
  pose proof (order_ex_prime_positive active Hprime).
  pose proof (Z.div_mod ord active ltac:(lia)) as Hdivision.
  nia.
Qed.

Lemma order_strip_exit_mod_ex
    x modulus phi active remainder ord :
  OrderStripStateEx x modulus phi active remainder ord ->
  ord mod active <> 0 ->
  OrderTrialStateEx x modulus phi (active + 1) remainder ord.
Proof.
  intros Hstate Hmod.
  apply order_strip_exit_nodiv_ex; [exact Hstate |].
  intro Hdiv.
  unfold OrderStripStateEx, OrderFactorStateEx in Hstate.
  destruct Hstate as [(_ & Hprime & _) _].
  apply Hmod.
  apply (proj2 (Z.mod_divide ord active ltac:(
    pose proof (order_ex_prime_positive active Hprime); lia)));
    exact Hdiv.
Qed.

Lemma order_strip_exit_power_ex
    x modulus phi active remainder ord retval :
  OrderStripStateEx x modulus phi active remainder ord ->
  ord mod active = 0 ->
  retval = Z.pow x (ord / active) mod modulus ->
  retval <> 1 ->
  OrderTrialStateEx x modulus phi (active + 1) remainder ord.
Proof.
  intros Hstate Hmod Hretval Hfailure.
  apply (order_strip_exit_pow_failure_ex x modulus phi active remainder ord
           (ord / active) Hstate).
  - unfold OrderStripStateEx, OrderFactorStateEx in Hstate.
    destruct Hstate as [(_ & Hprime & _) _].
    pose proof (order_ex_prime_positive active Hprime).
    pose proof (Z.div_mod ord active ltac:(lia)) as Hdivision.
    nia.
  - rewrite <- Hretval; exact Hfailure.
Qed.

(** Consumer-driven number-theory and transition closure, transplanted from
    the independently kernel-checked lemma_staging graph.  Each source is kept
    in its original module boundary and exported for generated VC consumers. *)

Module P090_OrderExcess.

Local Open Scope Z_scope.

Module P090_OrderExcess.

(** The definitions in this module are deliberately namespaced staging
    replacements.  [excess] is the mathematical quotient [ord / Ord], but the
    invariant records it by multiplication so no division side condition is
    hidden in a state predicate. *)

Definition OrderCore
    (x modulus phi ord excess : Z) : Prop :=
  OrderInput x modulus phi /\
  0 < ord /\ ord <= phi /\ (ord | phi) /\
  0 < excess /\
  ord = Ord x modulus * excess /\
  Z.pow x ord mod modulus = 1.

Definition PrimeSupport (excess remainder : Z) : Prop :=
  forall p, IsPrime p -> (p | excess) -> (p | remainder).

Definition PrimeSupportExcept (excess active remainder : Z) : Prop :=
  forall p, IsPrime p -> (p | excess) -> p = active \/ (p | remainder).

Definition NoPrimeBelow (candidate remainder : Z) : Prop :=
  forall p, IsPrime p -> p < candidate -> remainder mod p <> 0.

Definition OrderTrialStateEx
    (x modulus phi candidate remainder ord : Z) : Prop :=
  OrderInput x modulus phi /\
  0 < remainder /\ remainder <= phi /\ (remainder | phi) /\
  NoPrimeBelow candidate remainder /\
  exists excess,
    OrderCore x modulus phi ord excess /\
    PrimeSupport excess remainder.

Definition OrderFactorStateEx
    (x modulus phi active remainder ord : Z) : Prop :=
  OrderInput x modulus phi /\
  IsPrime active /\
  0 < remainder /\ remainder <= phi /\ (remainder | phi) /\
  NoPrimeBelow active remainder /\
  exists excess,
    OrderCore x modulus phi ord excess /\
    PrimeSupportExcept excess active remainder.

Definition OrderStripStateEx
    (x modulus phi active remainder ord : Z) : Prop :=
  OrderFactorStateEx x modulus phi active remainder ord /\
  remainder mod active <> 0.

Definition OrderFinalStateEx
    (x modulus phi active ord : Z) : Prop :=
  OrderInput x modulus phi /\
  IsPrime active /\
  exists excess,
    OrderCore x modulus phi ord excess /\
    (forall p, IsPrime p -> (p | excess) -> p = active).

(** Explicit interfaces for the foundational number theory that is not proved
    by this staging file.  They are never fields of the program-state
    predicates: every lemma that needs one takes it as a visible hypothesis. *)

Definition OrderPowerLaw (x modulus : Z) : Prop :=
  forall k, 0 <= k ->
    (Z.pow x k mod modulus = 1 <-> (Ord x modulus | k)).

Definition PrimeFactorExistsLaw : Prop :=
  forall n, 1 < n -> exists p, IsPrime p /\ (p | n).

Definition PrimeDivisorProductLaw : Prop :=
  forall p a b, IsPrime p -> (p | a * b) -> (p | a) \/ (p | b).

Definition PrimeDivisorOfPrimeLaw : Prop :=
  forall p q, IsPrime p -> IsPrime q -> (p | q) -> p = q.

Definition SmallestRemainingDivisorPrimeLaw : Prop :=
  forall candidate remainder,
    2 <= candidate ->
    0 < remainder ->
    NoPrimeBelow candidate remainder ->
    remainder mod candidate = 0 ->
    IsPrime candidate.

Definition ResidualRemainderPrimeLaw : Prop :=
  forall candidate remainder,
    2 <= candidate ->
    1 < remainder ->
    candidate * candidate > remainder ->
    NoPrimeBelow candidate remainder ->
    IsPrime remainder.

Lemma prime_positive p : IsPrime p -> 1 < p.
Proof. intros [Hp _]; exact Hp. Qed.

Lemma no_prime_below_two remainder : NoPrimeBelow 2 remainder.
Proof.
  intros p Hp Hlt.
  pose proof (prime_positive p Hp).
  lia.
Qed.

Lemma no_prime_below_divisor candidate remainder remainder' :
  NoPrimeBelow candidate remainder ->
  (remainder' | remainder) ->
  NoPrimeBelow candidate remainder'.
Proof.
  intros Hnone Hdiv p Hp Hlt Hmod.
  assert (Hp0 : p <> 0) by (pose proof (prime_positive p Hp); lia).
  assert (Hpdiv_next : (p | remainder')).
  { apply (proj1 (Z.mod_divide remainder' p Hp0)); exact Hmod. }
  assert (Hpdiv : (p | remainder)).
  { eapply Z.divide_trans; eauto. }
  specialize (Hnone p Hp Hlt).
  apply Hnone.
  apply (proj2 (Z.mod_divide remainder p Hp0)); exact Hpdiv.
Qed.

Lemma no_prime_below_advance candidate remainder :
  NoPrimeBelow candidate remainder ->
  remainder mod candidate <> 0 ->
  NoPrimeBelow (candidate + 1) remainder.
Proof.
  intros Hnone Hcandidate p Hp Hlt.
  destruct (Z.lt_trichotomy p candidate) as [Hpc | [Heq | Hcp]].
  - apply Hnone; assumption.
  - subst p; exact Hcandidate.
  - lia.
Qed.

Lemma order_core_order_divides x modulus phi ord excess :
  OrderCore x modulus phi ord excess -> (Ord x modulus | ord).
Proof.
  intros (_ & _ & _ & _ & _ & Heq & _).
  exists excess; nia.
Qed.

Lemma order_core_excess_divides_ord x modulus phi ord excess p :
  OrderCore x modulus phi ord excess ->
  (p | excess) ->
  (p | ord).
Proof.
  intros (_ & _ & _ & _ & _ & Heq & _) [k Hk].
  exists (Ord x modulus * k).
  rewrite Heq, Hk; ring.
Qed.

Lemma order_core_reduce
    x modulus phi ord excess active ord' :
  OrderPowerLaw x modulus ->
  OrderCore x modulus phi ord excess ->
  IsPrime active ->
  ord = active * ord' ->
  Z.pow x ord' mod modulus = 1 ->
  exists excess',
    excess = active * excess' /\
    OrderCore x modulus phi ord' excess'.
Proof.
  intros Hpower Hcore Hactive Hord Hpow.
  destruct Hcore as
      (Hinput & Hordpos & Hordle & Hordphi & Hexpos & Hexeq & Hordpow).
  pose proof (prime_positive active Hactive) as Hactivepos.
  assert (Hord'pos : 0 < ord') by nia.
  assert (HOpos : 0 < Ord x modulus).
  { unfold OrderInput in Hinput; tauto. }
  assert (HOdiv : (Ord x modulus | ord')).
  { apply (proj1 (Hpower ord' ltac:(lia))); exact Hpow. }
  destruct HOdiv as [excess' Hexcess'].
  assert (Hexcess'_pos : 0 < excess') by nia.
  assert (Hexfactor : excess = active * excess') by nia.
  assert (Hord'divord : (ord' | ord)).
  { exists active; nia. }
  assert (Hord'phi : (ord' | phi)).
  { eapply Z.divide_trans; eauto. }
  exists excess'.
  split; [exact Hexfactor |].
  unfold OrderCore.
  split; [exact Hinput |].
  repeat split.
  - exact Hord'pos.
  - eapply Z.divide_pos_le; eauto; lia.
  - exact Hord'phi.
  - exact Hexcess'_pos.
  - nia.
  - exact Hpow.
Qed.

Lemma order_core_excess_irreducible_from_ord
    x modulus phi ord excess active :
  OrderCore x modulus phi ord excess ->
  ~ (active | ord) ->
  ~ (active | excess).
Proof.
  intros Hcore Hnotord Hexdiv.
  apply Hnotord.
  eapply order_core_excess_divides_ord; eauto.
Qed.

Lemma order_core_excess_irreducible_from_pow_failure
    x modulus phi ord excess active quotient :
  OrderPowerLaw x modulus ->
  OrderCore x modulus phi ord excess ->
  IsPrime active ->
  ord = active * quotient ->
  Z.pow x quotient mod modulus <> 1 ->
  ~ (active | excess).
Proof.
  intros Hpower Hcore Hactive Hord Hpowfail [k Hk].
  destruct Hcore as
      (Hinput & Hordpos & Hordle & Hordphi & Hexpos & Hexeq & Hordpow).
  assert (Hactivepos : 1 < active) by (apply prime_positive; exact Hactive).
  assert (HOpos : 0 < Ord x modulus).
  { unfold OrderInput in Hinput; tauto. }
  assert (Hquotient : quotient = Ord x modulus * k) by nia.
  apply Hpowfail.
  apply (proj2 (Hpower quotient ltac:(nia))).
  exists k; nia.
Qed.

Lemma order_trial_init x modulus phi :
  OrderInput x modulus phi ->
  OrderTrialStateEx x modulus phi 2 phi phi.
Proof.
  intros Hinput.
  pose proof Hinput as Hinput_core.
  unfold OrderInput in Hinput.
  destruct Hinput as
      (Hmodulus & Hphi & Hgcd & Hphibounds & HOpos & HOdiv & Hpow).
  destruct HOdiv as [excess Hexeq].
  assert (Hexpos : 0 < excess) by nia.
  unfold OrderTrialStateEx.
  split; [exact Hinput_core |].
  repeat split.
  - lia.
  - lia.
  - exists 1; ring.
  - apply no_prime_below_two.
  - exists excess; split.
    + unfold OrderCore.
      split; [exact Hinput_core |].
      repeat split.
      * lia.
      * lia.
      * exists 1; ring.
      * exact Hexpos.
      * nia.
      * exact Hpow.
    + intros p Hp [k Hk].
      exists (Ord x modulus * k).
      rewrite Hexeq, Hk; ring.
Qed.

Lemma order_trial_skip x modulus phi candidate remainder ord :
  OrderTrialStateEx x modulus phi candidate remainder ord ->
  remainder mod candidate <> 0 ->
  OrderTrialStateEx x modulus phi (candidate + 1) remainder ord.
Proof.
  intros (Hinput & Hrpos & Hrle & Hrphi & Hnone & Hexcess) Hmod.
  unfold OrderTrialStateEx.
  split; [exact Hinput |].
  split; [exact Hrpos |].
  split; [exact Hrle |].
  split; [exact Hrphi |].
  split.
  - eapply no_prime_below_advance; eauto.
  - exact Hexcess.
Qed.

Lemma order_trial_enter_factor
    x modulus phi candidate remainder ord :
  SmallestRemainingDivisorPrimeLaw ->
  2 <= candidate ->
  OrderTrialStateEx x modulus phi candidate remainder ord ->
  remainder mod candidate = 0 ->
  OrderFactorStateEx x modulus phi candidate remainder ord.
Proof.
  intros Hsmall Hcandidate
    (Hinput & Hrpos & Hrle & Hrphi & Hnone &
     [excess [Hcore Hsupport]]) Hmod.
  assert (Hprime : IsPrime candidate).
  { eapply Hsmall; eauto. }
  unfold OrderFactorStateEx.
  split; [exact Hinput |].
  split; [exact Hprime |].
  split; [exact Hrpos |].
  split; [exact Hrle |].
  split; [exact Hrphi |].
  split; [exact Hnone |].
  exists excess; split; [exact Hcore |].
  intros p Hp Hpdiv; right; eapply Hsupport; eauto.
Qed.

Lemma order_factor_step
    x modulus phi active remainder remainder' ord :
  PrimeDivisorProductLaw ->
  PrimeDivisorOfPrimeLaw ->
  OrderFactorStateEx x modulus phi active remainder ord ->
  remainder = active * remainder' ->
  OrderFactorStateEx x modulus phi active remainder' ord.
Proof.
  intros Hproduct Hprime_divisor
    (Hinput & Hactive & Hrpos & Hrle & Hrphi & Hnone &
     [excess [Hcore Hsupport]]) Hrem.
  pose proof (prime_positive active Hactive) as Hactivepos.
  assert (Hr'pos : 0 < remainder') by nia.
  assert (Hr'divr : (remainder' | remainder)).
  { exists active; nia. }
  assert (Hr'phi : (remainder' | phi)).
  { eapply Z.divide_trans; eauto. }
  assert (Hr'le : remainder' <= phi).
  { eapply Z.divide_pos_le; eauto. nia. }
  assert (Hnone' : NoPrimeBelow active remainder').
  { eapply no_prime_below_divisor; eauto. }
  unfold OrderFactorStateEx.
  split; [exact Hinput |].
  split; [exact Hactive |].
  split; [exact Hr'pos |].
  split; [exact Hr'le |].
  split; [exact Hr'phi |].
  split; [exact Hnone' |].
  exists excess; split; [exact Hcore |].
  intros p Hp Hpdiv.
  specialize (Hsupport p Hp Hpdiv).
  destruct Hsupport as [Heq | Hpr].
  - left; exact Heq.
  - rewrite Hrem in Hpr.
    destruct (Hproduct p active remainder' Hp Hpr) as [Hpactive | Hpr'].
    + left; eapply Hprime_divisor; eauto.
    + right; exact Hpr'.
Qed.

Lemma order_factor_completed x modulus phi active remainder ord :
  OrderFactorStateEx x modulus phi active remainder ord ->
  remainder mod active <> 0 ->
  OrderStripStateEx x modulus phi active remainder ord.
Proof. unfold OrderStripStateEx; tauto. Qed.

Lemma order_strip_step
    x modulus phi active remainder ord ord' :
  OrderPowerLaw x modulus ->
  OrderStripStateEx x modulus phi active remainder ord ->
  ord = active * ord' ->
  Z.pow x ord' mod modulus = 1 ->
  OrderStripStateEx x modulus phi active remainder ord'.
Proof.
  intros Hpower
    [(Hinput & Hactive & Hrpos & Hrle & Hrphi & Hnone &
      [excess [Hcore Hsupport]]) Hremmod]
    Hord Hpow.
  destruct (order_core_reduce x modulus phi ord excess active ord'
              Hpower Hcore Hactive Hord Hpow)
    as [excess' [Hexfactor Hcore']].
  unfold OrderStripStateEx, OrderFactorStateEx.
  split; [| exact Hremmod].
  split; [exact Hinput |].
  split; [exact Hactive |].
  split; [exact Hrpos |].
  split; [exact Hrle |].
  split; [exact Hrphi |].
  split; [exact Hnone |].
  exists excess'; split; [exact Hcore' |].
  intros p Hp [k Hk].
  apply Hsupport; try assumption.
  exists (active * k).
  rewrite Hexfactor, Hk; ring.
Qed.

Lemma order_strip_exit_nodiv
    x modulus phi active remainder ord :
  OrderStripStateEx x modulus phi active remainder ord ->
  ~ (active | ord) ->
  OrderTrialStateEx x modulus phi (active + 1) remainder ord.
Proof.
  intros
    [(Hinput & Hactive & Hrpos & Hrle & Hrphi & Hnone &
      [excess [Hcore Hsupport]]) Hremmod] Hnotord.
  assert (Hnotexcess : ~ (active | excess)).
  { eapply order_core_excess_irreducible_from_ord; eauto. }
  unfold OrderTrialStateEx.
  split; [exact Hinput |].
  split; [exact Hrpos |].
  split; [exact Hrle |].
  split; [exact Hrphi |].
  split.
  - eapply no_prime_below_advance; eauto.
  - exists excess; split; [exact Hcore |].
    intros p Hp Hpdiv.
    destruct (Hsupport p Hp Hpdiv) as [Heq | Hpr]; [| exact Hpr].
    subst p; contradiction.
Qed.

Lemma order_strip_exit_pow_failure
    x modulus phi active remainder ord quotient :
  OrderPowerLaw x modulus ->
  OrderStripStateEx x modulus phi active remainder ord ->
  ord = active * quotient ->
  Z.pow x quotient mod modulus <> 1 ->
  OrderTrialStateEx x modulus phi (active + 1) remainder ord.
Proof.
  intros Hpower
    [(Hinput & Hactive & Hrpos & Hrle & Hrphi & Hnone &
      [excess [Hcore Hsupport]]) Hremmod] Hord Hpowfail.
  assert (Hnotexcess : ~ (active | excess)).
  { eapply order_core_excess_irreducible_from_pow_failure; eauto. }
  unfold OrderTrialStateEx.
  split; [exact Hinput |].
  split; [exact Hrpos |].
  split; [exact Hrle |].
  split; [exact Hrphi |].
  split.
  - eapply no_prime_below_advance; eauto.
  - exists excess; split; [exact Hcore |].
    intros p Hp Hpdiv.
    destruct (Hsupport p Hp Hpdiv) as [Heq | Hpr]; [| exact Hpr].
    subst p; contradiction.
Qed.

Lemma order_core_unit_result x modulus phi ord :
  OrderCore x modulus phi ord 1 ->
  OrderResult x modulus ord.
Proof.
  intros (Hinput & Hordpos & Hordle & Hordphi & Hone & Heq & Hpow).
  unfold OrderInput in Hinput.
  destruct Hinput as
      (Hmodulus & Hphi & Hgcd & Hphibounds & HOpos & HOphi & HEuler).
  assert (Hord : ord = Ord x modulus) by nia.
  unfold OrderResult.
  repeat split.
  - exact Hord.
  - exact Hordpos.
  - rewrite <- Hphi; rewrite Hord; exact HOphi.
  - exact Hpow.
Qed.

Lemma support_empty_is_unit excess :
  PrimeFactorExistsLaw ->
  0 < excess ->
  PrimeSupport excess 1 ->
  excess = 1.
Proof.
  intros Hfactor Hexpos Hsupport.
  destruct (Z_lt_le_dec 1 excess) as [Hgt | Hle]; [| lia].
  destruct (Hfactor excess Hgt) as [p [Hp Hpdiv]].
  specialize (Hsupport p Hp Hpdiv).
  destruct Hsupport as [k Hk].
  pose proof (prime_positive p Hp).
  assert (0 < k) by nia.
  nia.
Qed.

Lemma order_trial_exit_exhausted x modulus phi candidate ord :
  PrimeFactorExistsLaw ->
  OrderTrialStateEx x modulus phi candidate 1 ord ->
  OrderResult x modulus ord.
Proof.
  intros Hfactor
    (Hinput & Hrpos & Hrle & Hrphi & Hnone &
     [excess [Hcore Hsupport]]).
  assert (Hexcess : excess = 1).
  { eapply support_empty_is_unit; eauto.
    unfold OrderCore in Hcore; tauto. }
  subst excess.
  eapply order_core_unit_result; eauto.
Qed.

Lemma order_trial_enter_final
    x modulus phi candidate remainder ord :
  ResidualRemainderPrimeLaw ->
  PrimeDivisorOfPrimeLaw ->
  2 <= candidate ->
  1 < remainder ->
  candidate * candidate > remainder ->
  OrderTrialStateEx x modulus phi candidate remainder ord ->
  OrderFinalStateEx x modulus phi remainder ord.
Proof.
  intros Hresidual Hprime_divisor Hcandidate Hrgt Hguard
    (Hinput & Hrpos & Hrle & Hrphi & Hnone &
     [excess [Hcore Hsupport]]).
  assert (Hrprime : IsPrime remainder).
  { eapply Hresidual; eauto. }
  unfold OrderFinalStateEx.
  split; [exact Hinput |].
  split; [exact Hrprime |].
  exists excess; split; [exact Hcore |].
  intros p Hp Hpdiv.
  eapply Hprime_divisor; eauto.
Qed.

Lemma order_final_step x modulus phi active ord ord' :
  OrderPowerLaw x modulus ->
  OrderFinalStateEx x modulus phi active ord ->
  ord = active * ord' ->
  Z.pow x ord' mod modulus = 1 ->
  OrderFinalStateEx x modulus phi active ord'.
Proof.
  intros Hpower (Hinput & Hactive & [excess [Hcore Hsupport]]) Hord Hpow.
  destruct (order_core_reduce x modulus phi ord excess active ord'
              Hpower Hcore Hactive Hord Hpow)
    as [excess' [Hexfactor Hcore']].
  unfold OrderFinalStateEx.
  split; [exact Hinput |].
  split; [exact Hactive |].
  exists excess'; split; [exact Hcore' |].
  intros p Hp [k Hk].
  apply Hsupport; try assumption.
  exists (active * k).
  rewrite Hexfactor, Hk; ring.
Qed.

Lemma support_only_irreducible_is_unit excess active :
  PrimeFactorExistsLaw ->
  0 < excess ->
  (forall p, IsPrime p -> (p | excess) -> p = active) ->
  ~ (active | excess) ->
  excess = 1.
Proof.
  intros Hfactor Hexpos Hsupport Hnotactive.
  destruct (Z_lt_le_dec 1 excess) as [Hgt | Hle]; [| lia].
  destruct (Hfactor excess Hgt) as [p [Hp Hpdiv]].
  specialize (Hsupport p Hp Hpdiv).
  subst p; contradiction.
Qed.

Lemma order_final_exit_nodiv x modulus phi active ord :
  PrimeFactorExistsLaw ->
  OrderFinalStateEx x modulus phi active ord ->
  ~ (active | ord) ->
  OrderResult x modulus ord.
Proof.
  intros Hfactor (Hinput & Hactive & [excess [Hcore Hsupport]]) Hnotord.
  assert (Hnotexcess : ~ (active | excess)).
  { eapply order_core_excess_irreducible_from_ord; eauto. }
  assert (Hexcess : excess = 1).
  { eapply support_only_irreducible_is_unit; eauto.
    unfold OrderCore in Hcore; tauto. }
  subst excess.
  eapply order_core_unit_result; eauto.
Qed.

Lemma order_final_exit_pow_failure
    x modulus phi active ord quotient :
  PrimeFactorExistsLaw ->
  OrderPowerLaw x modulus ->
  OrderFinalStateEx x modulus phi active ord ->
  ord = active * quotient ->
  Z.pow x quotient mod modulus <> 1 ->
  OrderResult x modulus ord.
Proof.
  intros Hfactor Hpower
    (Hinput & Hactive & [excess [Hcore Hsupport]]) Hord Hpowfail.
  assert (Hnotexcess : ~ (active | excess)).
  { eapply order_core_excess_irreducible_from_pow_failure; eauto. }
  assert (Hexcess : excess = 1).
  { eapply support_only_irreducible_is_unit; eauto.
    unfold OrderCore in Hcore; tauto. }
  subst excess.
  eapply order_core_unit_result; eauto.
Qed.

End P090_OrderExcess.
End P090_OrderExcess.
Export P090_OrderExcess.

Module P090_OrderFoundations.

Local Open Scope Z_scope.

Import P090_OrderExcess.P090_OrderExcess.

Module P090_OrderFoundations.

(** The unqualified [OrderPowerLaw] is false: it has no coprimality
    hypothesis.  The concrete failure below uses exponent one. *)

Theorem order_power_law_0_2_counterexample :
  Z.pow 0 1 mod 2 <> 1 /\ (Ord 0 2 | 1).
Proof.
  split.
  - vm_compute; discriminate.
  - exists 1; vm_compute; reflexivity.
Qed.

Theorem order_power_law_falsified : ~ OrderPowerLaw 0 2.
Proof.
  intros Hlaw.
  specialize (Hlaw 1 ltac:(lia)).
  destruct order_power_law_0_2_counterexample as [Hpow Hdiv].
  apply Hpow.
  apply (proj2 Hlaw); exact Hdiv.
Qed.

(** The case-local primality predicate is extensionally the standard Rocq
    integer primality predicate. *)

Lemma is_prime_iff_std p : IsPrime p <-> prime p.
Proof.
  rewrite <- prime_alt.
  unfold IsPrime, prime'.
  split.
  - intros [Hp Htest].
    split; [exact Hp |].
    intros q [Hq Hqp] Hdiv.
    specialize (Htest q (conj Hq Hqp)).
    apply Htest.
    apply (proj2 (Z.mod_divide p q ltac:(lia))); exact Hdiv.
  - intros [Hp Htest].
    split; [exact Hp |].
    intros q [Hq Hqp] Hmod.
    apply (Htest q (conj Hq Hqp)).
    apply (proj1 (Z.mod_divide p q ltac:(lia))); exact Hmod.
Qed.

Lemma std_prime_factor_exists :
  forall n, 1 < n -> exists p, prime p /\ (p | n).
Proof.
  intro n.
  refine (well_founded_induction_type
            (Z.lt_wf 2)
            (fun a => 1 < a -> exists p, prime p /\ (p | a))
            _ n).
  intros a IH Ha.
  destruct (prime_dec a) as [Hprime | Hnotprime].
  - exists a; split; [exact Hprime | apply Z.divide_refl].
  - destruct (not_prime_divide a Ha Hnotprime)
      as [d [[Hdpos Hdlt] Hddiv]].
    destruct (IH d ltac:(lia) Hdpos) as [p [Hpprime Hpdiv]].
    exists p; split; [exact Hpprime |].
    eapply Z.divide_trans; eauto.
Qed.

Theorem prime_factor_exists_law : PrimeFactorExistsLaw.
Proof.
  unfold PrimeFactorExistsLaw.
  intros n Hn.
  destruct (std_prime_factor_exists n Hn) as [p [Hp Hdiv]].
  exists p; split; [apply is_prime_iff_std; exact Hp | exact Hdiv].
Qed.

Theorem prime_divisor_product_law : PrimeDivisorProductLaw.
Proof.
  unfold PrimeDivisorProductLaw.
  intros p a b Hp Hdiv.
  eapply prime_mult; [apply is_prime_iff_std; exact Hp | exact Hdiv].
Qed.

Theorem prime_divisor_of_prime_law : PrimeDivisorOfPrimeLaw.
Proof.
  unfold PrimeDivisorOfPrimeLaw.
  intros p q Hp Hq Hdiv.
  eapply prime_div_prime.
  - apply is_prime_iff_std; exact Hp.
  - apply is_prime_iff_std; exact Hq.
  - exact Hdiv.
Qed.

Lemma no_prime_below_not_divides candidate remainder p :
  NoPrimeBelow candidate remainder ->
  IsPrime p ->
  p < candidate ->
  ~ (p | remainder).
Proof.
  intros Hnone Hp Hlt Hdiv.
  specialize (Hnone p Hp Hlt).
  apply Hnone.
  apply (proj2 (Z.mod_divide remainder p ltac:(
    pose proof (prime_positive p Hp); lia))); exact Hdiv.
Qed.

Theorem smallest_remaining_divisor_prime_law :
  SmallestRemainingDivisorPrimeLaw.
Proof.
  unfold SmallestRemainingDivisorPrimeLaw.
  intros candidate remainder Hcandidate Hremainder Hnone Hmod.
  split; [lia |].
  intros q [Hqpos Hqlt] Hqmod.
  assert (Hq0 : q <> 0) by lia.
  assert (Hqdivcandidate : (q | candidate)).
  { apply (proj1 (Z.mod_divide candidate q Hq0)); exact Hqmod. }
  destruct (prime_factor_exists_law q Hqpos) as [p [Hp Hpdivq]].
  assert (Hp_le_q : p <= q).
  { eapply Z.divide_pos_le; eauto; lia. }
  assert (Hcandidate_div_remainder : (candidate | remainder)).
  { apply (proj1 (Z.mod_divide remainder candidate ltac:(lia))); exact Hmod. }
  assert (Hpdivremainder : (p | remainder)).
  { eapply Z.divide_trans; [exact Hpdivq |].
    eapply Z.divide_trans; eauto. }
  eapply (no_prime_below_not_divides candidate remainder p);
    eauto; lia.
Qed.

Theorem residual_remainder_prime_law : ResidualRemainderPrimeLaw.
Proof.
  unfold ResidualRemainderPrimeLaw.
  intros candidate remainder Hcandidate Hremainder Hguard Hnone.
  split; [exact Hremainder |].
  intros q [Hqpos Hqlt] Hqmod.
  assert (Hq0 : q <> 0) by lia.
  assert (Hqdiv : (q | remainder)).
  { apply (proj1 (Z.mod_divide remainder q Hq0)); exact Hqmod. }
  destruct Hqdiv as [cofactor Hfactorization].
  assert (Hcofactor : 1 < cofactor) by nia.
  assert (Hsmall : q < candidate \/ cofactor < candidate) by nia.
  destruct Hsmall as [Hqsmall | Hcofsmall].
  - destruct (prime_factor_exists_law q Hqpos) as [p [Hp Hpdiv]].
    assert (Hp_le_q : p <= q).
    { eapply Z.divide_pos_le; eauto; lia. }
    assert (Hqdivremainder : (q | remainder)).
    { exists cofactor; exact Hfactorization. }
    assert (Hpdivremainder : (p | remainder)).
    { eapply Z.divide_trans; [exact Hpdiv | exact Hqdivremainder]. }
    eapply (no_prime_below_not_divides candidate remainder p);
      eauto; lia.
  - destruct (prime_factor_exists_law cofactor Hcofactor)
      as [p [Hp Hpdiv]].
    assert (Hp_le_cofactor : p <= cofactor).
    { eapply Z.divide_pos_le; eauto; lia. }
    assert (Hcofactordiv : (cofactor | remainder)).
    { exists q; nia. }
    assert (Hpdivremainder : (p | remainder)).
    { eapply Z.divide_trans; [exact Hpdiv | exact Hcofactordiv]. }
    eapply (no_prime_below_not_divides candidate remainder p);
      eauto; lia.
Qed.

End P090_OrderFoundations.
End P090_OrderFoundations.
Export P090_OrderFoundations.

Module P090_OrderExact.

Local Open Scope Z_scope.

Import P090_OrderExcess.P090_OrderExcess.

Module P090_OrderExact.

Lemma pow_mod_base_nat a modulus n :
  modulus <> 0 ->
  Z.pow (a mod modulus) (Z.of_nat n) mod modulus =
  Z.pow a (Z.of_nat n) mod modulus.
Proof.
  intros Hmodulus.
  induction n as [|n IH].
  - cbn. reflexivity.
  - rewrite Nat2Z.inj_succ.
    rewrite !Z.pow_succ_r by apply Nat2Z.is_nonneg.
    rewrite (Z.mul_mod
      (a mod modulus) (Z.pow (a mod modulus) (Z.of_nat n))
      modulus Hmodulus).
    rewrite (Z.mul_mod
      a (Z.pow a (Z.of_nat n)) modulus Hmodulus).
    rewrite IH.
    rewrite Z.mod_mod by exact Hmodulus.
    reflexivity.
Qed.

Lemma pow_mod_base a modulus exponent :
  modulus <> 0 ->
  0 <= exponent ->
  Z.pow (a mod modulus) exponent mod modulus =
  Z.pow a exponent mod modulus.
Proof.
  intros Hmodulus Hexponent.
  rewrite <- (Z2Nat.id exponent Hexponent).
  apply pow_mod_base_nat; exact Hmodulus.
Qed.

Lemma pow_add_mod_left_one a modulus left right :
  1 < modulus ->
  0 <= left ->
  0 <= right ->
  Z.pow a left mod modulus = 1 ->
  Z.pow a (left + right) mod modulus =
  Z.pow a right mod modulus.
Proof.
  intros Hmodulus Hleft Hright Hone.
  rewrite Z.pow_add_r by assumption.
  rewrite Z.mul_mod by lia.
  rewrite Hone.
  replace (1 * (Z.pow a right mod modulus))
    with (Z.pow a right mod modulus) by ring.
  apply Z.mod_mod; lia.
Qed.

Lemma pow_multiple_mod_one a modulus period multiplier :
  1 < modulus ->
  0 <= period ->
  0 <= multiplier ->
  Z.pow a period mod modulus = 1 ->
  Z.pow a (period * multiplier) mod modulus = 1.
Proof.
  intros Hmodulus Hperiod Hmultiplier Hone.
  rewrite Z.pow_mul_r by assumption.
  rewrite <- (pow_mod_base
    (Z.pow a period) modulus multiplier ltac:(lia) Hmultiplier).
  rewrite Hone.
  rewrite Z.pow_1_l by exact Hmultiplier.
  apply Z.mod_small; lia.
Qed.

Lemma pow_divmod_remainder a modulus period exponent :
  1 < modulus ->
  0 < period ->
  0 <= exponent ->
  Z.pow a period mod modulus = 1 ->
  Z.pow a exponent mod modulus =
  Z.pow a (exponent mod period) mod modulus.
Proof.
  intros Hmodulus Hperiod Hexponent Hperiodpow.
  pose proof (Z.div_mod exponent period ltac:(lia)) as Hdecompose.
  pose proof (Z.mod_pos_bound exponent period Hperiod) as Hrem.
  pose proof (Z.div_pos exponent period Hexponent Hperiod) as Hquotient.
  rewrite Hdecompose at 1.
  apply pow_add_mod_left_one; try lia.
  apply (pow_multiple_mod_one
    a modulus period (exponent / period)); try lia; assumption.
Qed.

Lemma order_search_minimal base modulus start fuel candidate :
  1 <= start ->
  start <= candidate < order_search base modulus start fuel ->
  Z.pow base candidate mod modulus <> 1.
Proof.
  revert start candidate.
  induction fuel as [|fuel IH]; intros start candidate Hstart Hrange.
  - cbn [order_search] in Hrange; lia.
  - cbn [order_search] in Hrange.
    destruct (Z.eqb (Z.pow base start mod modulus) 1)
      eqn:Hcurrent.
    + lia.
    + apply Z.eqb_neq in Hcurrent.
      destruct (Z.eq_dec candidate start) as [Heq | Hneq].
      * subst candidate; exact Hcurrent.
      * apply (IH (start + 1) candidate); [lia |].
        split; [lia | exact (proj2 Hrange)].
Qed.

Lemma order_search_terminal_spec base modulus start fuel :
  1 <= start ->
  Z.pow base (start + Z.of_nat fuel) mod modulus = 1 ->
  let result := order_search base modulus start (S fuel) in
  start <= result <= start + Z.of_nat fuel /\
  Z.pow base result mod modulus = 1.
Proof.
  revert start.
  induction fuel as [|fuel IH]; intros start Hstart Hterminal.
  - cbn [order_search] in *.
    destruct (Z.eqb (Z.pow base start mod modulus) 1)
      eqn:Hcurrent.
    + apply Z.eqb_eq in Hcurrent.
      split; [lia | exact Hcurrent].
    + apply Z.eqb_neq in Hcurrent.
      exfalso; apply Hcurrent.
      replace (start + Z.of_nat 0) with start in Hterminal by ring.
      exact Hterminal.
  - cbn [order_search].
    destruct (Z.eqb (Z.pow base start mod modulus) 1)
      eqn:Hcurrent.
    + apply Z.eqb_eq in Hcurrent.
      split; [lia | exact Hcurrent].
    + assert (Hterminal' :
        Z.pow base (start + 1 + Z.of_nat fuel) mod modulus = 1).
      { rewrite Nat2Z.inj_succ in Hterminal.
        replace (start + 1 + Z.of_nat fuel)
          with (start + Z.succ (Z.of_nat fuel)) by lia.
        exact Hterminal. }
      destruct (IH (start + 1) ltac:(lia) Hterminal')
        as [Hbounds Hsound].
      change
        (start <= order_search base modulus (start + 1) (S fuel) <=
           start + Z.of_nat (S fuel) /\
         Z.pow base (order_search base modulus (start + 1) (S fuel))
           mod modulus = 1).
      split; [rewrite Nat2Z.inj_succ; lia | exact Hsound].
Qed.

Lemma ord_search_exact x modulus phi :
  OrderInput x modulus phi ->
  1 <= Ord x modulus <= phi /\
  Z.pow x (Ord x modulus) mod modulus = 1 /\
  (forall candidate,
      1 <= candidate < Ord x modulus ->
      Z.pow x candidate mod modulus <> 1).
Proof.
  intros Hinput.
  unfold OrderInput in Hinput.
  destruct Hinput as
      (Hmodulus & Hphi & Hgcd & Hphibounds & Hordpos & Hordphi & Hphipow).
  unfold Ord.
  assert (Hmodulus_neq : Z.eqb modulus 1 = false).
  { apply Z.eqb_neq; lia. }
  rewrite Hmodulus_neq.
  rewrite <- Hphi.
  remember (Z.to_nat phi) as count eqn:Hcount.
  assert (Hcount_value : Z.of_nat count = phi).
  { rewrite Hcount; apply Z2Nat.id; lia. }
  destruct count as [|fuel].
  - cbn in Hcount_value; lia.
  - assert (Hterminal_exponent : 1 + Z.of_nat fuel = phi).
    { rewrite Nat2Z.inj_succ in Hcount_value; lia. }
    assert (Hterminal :
      Z.pow (x mod modulus) (1 + Z.of_nat fuel) mod modulus = 1).
    { rewrite Hterminal_exponent.
      rewrite pow_mod_base by lia.
      exact Hphipow. }
    destruct (order_search_terminal_spec
                (x mod modulus) modulus 1 fuel ltac:(lia) Hterminal)
      as [Hbounds Hsound].
    split.
    + rewrite Hterminal_exponent in Hbounds; exact Hbounds.
    + split.
      * rewrite <- (pow_mod_base x modulus
                      (order_search (x mod modulus) modulus 1 (S fuel)))
          by lia.
        exact Hsound.
      * intros candidate Hcandidate Hcandidatepow.
        eapply (order_search_minimal
                  (x mod modulus) modulus 1 (S fuel) candidate);
          try eassumption; try lia.
        rewrite pow_mod_base by lia.
        exact Hcandidatepow.
Qed.

Lemma minimal_success_divides
    x modulus period exponent :
  1 < modulus ->
  0 < period ->
  Z.pow x period mod modulus = 1 ->
  (forall candidate,
      1 <= candidate < period ->
      Z.pow x candidate mod modulus <> 1) ->
  0 <= exponent ->
  Z.pow x exponent mod modulus = 1 ->
  (period | exponent).
Proof.
  intros Hmodulus Hperiod Hperiodpow Hminimal Hexponent Hexponentpow.
  pose proof (Z.mod_pos_bound exponent period Hperiod) as Hremainder.
  assert (Hremainderpow :
    Z.pow x (exponent mod period) mod modulus = 1).
  { rewrite <- (pow_divmod_remainder
                  x modulus period exponent
                  Hmodulus Hperiod Hexponent Hperiodpow).
    exact Hexponentpow. }
  destruct (Z.eq_dec (exponent mod period) 0) as [Hzero | Hnonzero].
  - apply (proj1 (Z.mod_divide exponent period ltac:(lia))); exact Hzero.
  - exfalso.
    eapply (Hminimal (exponent mod period)); [lia | exact Hremainderpow].
Qed.

Lemma success_of_period_divides
    x modulus period exponent :
  1 < modulus ->
  0 < period ->
  Z.pow x period mod modulus = 1 ->
  0 <= exponent ->
  (period | exponent) ->
  Z.pow x exponent mod modulus = 1.
Proof.
  intros Hmodulus Hperiod Hperiodpow Hexponent [multiplier Heq].
  assert (Hmultiplier : 0 <= multiplier) by nia.
  rewrite Heq.
  rewrite Z.mul_comm.
  apply pow_multiple_mod_one; try lia; assumption.
Qed.

Theorem order_input_implies_order_power_law :
  forall x modulus phi,
    OrderInput x modulus phi ->
    OrderPowerLaw x modulus.
Proof.
  intros x modulus phi Hinput.
  pose proof Hinput as Hinput_bounds.
  unfold OrderInput in Hinput_bounds.
  destruct Hinput_bounds as
      (Hmodulus & Hphi & Hgcd & Hphibounds & Hordpos & Hordphi & Hphipow).
  destruct (ord_search_exact x modulus phi Hinput)
    as [Hordbounds [Hordpow Hminimal]].
  unfold OrderPowerLaw.
  intros exponent Hexponent.
  split.
  - intros Hexponentpow.
    eapply minimal_success_divides; eauto; lia.
  - intros Hdivides.
    eapply success_of_period_divides; eauto; lia.
Qed.

End P090_OrderExact.
End P090_OrderExact.
Export P090_OrderExact.

Module P090_FactorTable.

Import ListNotations.
Local Open Scope Z_scope.

(** The on-disk [FactorPrefix] records that every stored prime is below the
    current candidate, but it does not record the relative order of the stored
    entries.  This additional conjunct is the missing construction history
    needed by [ValidFactorTable]. *)
Definition StrictPrimePrefix (pr : list Z) : Prop :=
  forall j k,
    0 <= j /\ j < k /\ k < Zlength pr ->
    Znth j pr 0 < Znth k pr 0.

Definition StrictFactorPrefix
    (m candidate remainder : Z) (pr pe : list Z) : Prop :=
  FactorPrefix m candidate remainder pr pe /\ StrictPrimePrefix pr.

Lemma strict_factor_prefix_base m :
  0 < m -> StrictFactorPrefix m 2 m [] [].
Proof.
  intros Hm.
  split.
  - unfold FactorPrefix.
    split; [reflexivity|].
    split; [rewrite Zlength_nil; lia|].
    split; [lia|].
    split; [lia|].
    split; [simpl; destruct m; reflexivity|].
    split.
    + intros k Hk; rewrite Zlength_nil in Hk; lia.
    + intros prime [Hprime _] Hlt; lia.
  - unfold StrictPrimePrefix.
    intros j k Hjk; rewrite Zlength_nil in Hjk; lia.
Qed.

Lemma strict_factor_prefix_forgets_order m candidate remainder pr pe :
  StrictFactorPrefix m candidate remainder pr pe ->
  FactorPrefix m candidate remainder pr pe.
Proof. intros [H _]; exact H. Qed.

Lemma strict_factor_prefix_has_order m candidate remainder pr pe :
  StrictFactorPrefix m candidate remainder pr pe -> StrictPrimePrefix pr.
Proof. intros [_ H]; exact H. Qed.

Lemma strict_prime_prefix_lt pr j k :
  StrictPrimePrefix pr ->
  0 <= j -> j < k -> k < Zlength pr ->
  Znth j pr 0 < Znth k pr 0.
Proof.
  intros Horder Hj Hjk Hk.
  apply Horder; lia.
Qed.

Lemma strict_prime_prefix_distinct_indices pr j k :
  StrictPrimePrefix pr ->
  0 <= j < Zlength pr ->
  0 <= k < Zlength pr ->
  j <> k ->
  Znth j pr 0 <> Znth k pr 0.
Proof.
  intros Horder Hj Hk Hne Heq.
  destruct (Z_lt_ge_dec j k) as [Hjk | Hkj].
  - specialize (Horder j k ltac:(lia)); lia.
  - specialize (Horder k j ltac:(lia)); lia.
Qed.

Lemma strict_prime_prefix_snoc pr p :
  StrictPrimePrefix pr ->
  (forall k, 0 <= k < Zlength pr -> Znth k pr 0 < p) ->
  StrictPrimePrefix (pr ++ [p]).
Proof.
  intros Horder Hbelow j k (Hj & Hjk & Hk).
  rewrite Zlength_app_cons in Hk.
  destruct (Z_lt_ge_dec k (Zlength pr)) as [Hkin | Hklast].
  - rewrite (app_Znth1 0 pr [p] j) by lia.
    rewrite (app_Znth1 0 pr [p] k) by lia.
    apply Horder; lia.
  - assert (k = Zlength pr) by lia; subst k.
    rewrite (app_Znth1 0 pr [p] j) by lia.
    rewrite (app_Znth2 0 pr [p] (Zlength pr)) by lia.
    rewrite Z.sub_diag; simpl.
    apply Hbelow; lia.
Qed.

Lemma factor_product_snoc pr pe p e :
  Zlength pr = Zlength pe ->
  factor_product (pr ++ [p]) (pe ++ [e]) =
  factor_product pr pe * Z.pow p e.
Proof.
  revert pe.
  induction pr as [| q pr IH]; intros pe Hlen.
  - destruct pe as [| f pe].
    + simpl.
      rewrite Z.mul_1_r; destruct (Z.pow p e); reflexivity.
    + pose proof (Zlength_nonneg pe).
      rewrite Zlength_nil, Zlength_cons in Hlen; lia.
  - destruct pe as [| f pe].
    + pose proof (Zlength_nonneg pr).
      rewrite Zlength_nil, Zlength_cons in Hlen; lia.
    + simpl.
      rewrite IH.
      * rewrite Z.mul_assoc; reflexivity.
      * rewrite !Zlength_cons in Hlen; lia.
Qed.

Lemma strict_factor_prefix_length_bounds m candidate remainder pr pe :
  StrictFactorPrefix m candidate remainder pr pe ->
  0 <= Zlength pr <= 64.
Proof.
  intros [(_ & Hlen & _) _].
  exact Hlen.
Qed.

Lemma strict_factor_prefix_snoc_capacity m candidate remainder pr pe p :
  StrictFactorPrefix m candidate remainder pr pe ->
  Zlength pr < 64 ->
  0 <= Zlength (pr ++ [p]) <= 64.
Proof.
  intros Hprefix Hroom.
  pose proof (strict_factor_prefix_length_bounds _ _ _ _ _ Hprefix).
  rewrite Zlength_app_cons; lia.
Qed.

Lemma factor_prefix_smaller_prime_survives_division
    m candidate original remainder pr pe p exponent :
  FactorPrefix m candidate original pr pe ->
  original = Z.pow p exponent * remainder ->
  forall q, IsPrime q -> q < candidate -> remainder mod q <> 0.
Proof.
  intros Hprefix Hdecomp q Hprime Hq Hmod.
  destruct Hprefix as (_ & _ & _ & _ & _ & _ & Hexclude).
  specialize (Hexclude q Hprime Hq).
  destruct Hprime as [Hqprime _].
  assert (Hq0 : q <> 0) by lia.
  apply Hexclude.
  apply Z.mod_divide in Hmod; [| exact Hq0].
  destruct Hmod as [c Hc].
  apply Z.mod_divide; [exact Hq0|].
  exists (Z.pow p exponent * c).
  rewrite Hdecomp, Hc.
  ring.
Qed.

(** A completed division by the current prime may be appended.  All premises
    are primitive facts produced by the factor loop: exact division history,
    positive exponent/remainder, the failed next divisibility test, and one
    free table slot. *)
Lemma strict_factor_prefix_append_completed_prime
    m candidate original remainder exponent pr pe :
  StrictFactorPrefix m candidate original pr pe ->
  IsPrime candidate ->
  1 <= exponent ->
  original = Z.pow candidate exponent * remainder ->
  0 < remainder ->
  remainder mod candidate <> 0 ->
  Zlength pr < 64 ->
  StrictFactorPrefix m (candidate + 1) remainder
    (pr ++ [candidate]) (pe ++ [exponent]).
Proof.
  intros [Hprefix Horder] Hprime Hexp Hdecomp Hrem Hnotdiv Hroom.
  pose proof Hprefix as Hprefix_before_append.
  destruct Hprefix as
      (Hlens & Hcap & Hcandidate & Horiginal & Hproduct & Hentries & Hexclude).
  split.
  - unfold FactorPrefix.
    split.
    + rewrite !Zlength_app_cons; lia.
    + split.
      * rewrite Zlength_app_cons; lia.
      * split; [lia|].
        split.
        -- split; [exact Hrem|].
           destruct Horiginal; nia.
        -- split.
           ++ rewrite factor_product_snoc by exact Hlens.
              rewrite Hproduct, Hdecomp.
              ring.
           ++ split.
              ** intros k Hk.
                 rewrite Zlength_app_cons in Hk.
                 destruct (Z_lt_ge_dec k (Zlength pr)) as [Hkin | Hklast].
                 { rewrite (app_Znth1 0 pr [candidate] k) by lia.
                   rewrite (app_Znth1 0 pe [exponent] k) by lia.
                   specialize (Hentries k ltac:(lia)).
                   destruct Hentries as (Hpk & Hek & Hpklt).
                   split; [exact Hpk|].
                   split; [exact Hek|lia]. }
                 { assert (k = Zlength pr) by lia; subst k.
                   rewrite (app_Znth2 0 pr [candidate] (Zlength pr)) by lia.
                   rewrite (app_Znth2 0 pe [exponent] (Zlength pr)) by lia.
                   rewrite Hlens, !Z.sub_diag; simpl.
                   change (IsPrime candidate /\
                           1 <= exponent /\ candidate < candidate + 1).
                   split; [exact Hprime|].
                   split; [exact Hexp|lia]. }
              ** intros q Hqprime Hqbelow.
                 destruct (Z_lt_ge_dec q candidate) as [Hsmall | Hsame].
                 { eapply factor_prefix_smaller_prime_survives_division.
                   - exact Hprefix_before_append.
                   - exact Hdecomp.
                   - exact Hqprime.
                   - exact Hsmall. }
                 { assert (q = candidate) by lia; subst q; exact Hnotdiv. }
  - apply strict_prime_prefix_snoc; [exact Horder|].
    intros k Hk.
    specialize (Hentries k Hk).
    tauto.
Qed.

Lemma strict_factor_prefix_residual_ge_candidate
    m candidate remainder pr pe :
  StrictFactorPrefix m candidate remainder pr pe ->
  IsPrime remainder ->
  candidate <= remainder.
Proof.
  intros [[_ Hrest] _] Hprime.
  destruct Hrest as (_ & _ & _ & _ & _ & Hexclude).
  destruct (Z_lt_ge_dec remainder candidate); [|lia].
  specialize (Hexclude remainder Hprime l).
  rewrite Z.mod_same in Hexclude by (destruct Hprime; lia).
  contradiction.
Qed.

Lemma strict_factor_prefix_finalize_one m candidate pr pe :
  StrictFactorPrefix m candidate 1 pr pe ->
  ValidFactorTable m pr pe.
Proof.
  intros [Hprefix Horder].
  destruct Hprefix as
      (Hlens & Hcap & Hcandidate & Hrem & Hproduct & Hentries & Hexclude).
  unfold ValidFactorTable.
  split; [exact Hlens|].
  split; [exact Hcap|].
  split.
  - rewrite Z.mul_1_r in Hproduct; exact Hproduct.
  - split.
    + intros k Hk.
    specialize (Hentries k Hk).
    tauto.
    + exact Horder.
Qed.

(** If the trial loop exits with a prime residual, the prefix exclusion fact
    itself proves that the residual cannot be smaller than the candidate. *)
Lemma strict_factor_prefix_finalize_prime_residual
    m candidate remainder pr pe :
  StrictFactorPrefix m candidate remainder pr pe ->
  IsPrime remainder ->
  Zlength pr < 64 ->
  ValidFactorTable m (pr ++ [remainder]) (pe ++ [1]).
Proof.
  intros Hstrict Hprime Hroom.
  pose proof Hstrict as [[Hlens Hrest] Horder].
  destruct Hrest as (Hcap & Hcandidate & Hrem & Hproduct & Hentries & Hexclude).
  pose proof (strict_factor_prefix_residual_ge_candidate
                _ _ _ _ _ Hstrict Hprime) as Hge.
  unfold ValidFactorTable.
  split.
  - rewrite !Zlength_app_cons; lia.
  - split.
    + rewrite Zlength_app_cons; lia.
    + split.
      * rewrite factor_product_snoc by exact Hlens.
        rewrite Z.pow_1_r.
        exact Hproduct.
      * split.
        -- intros k Hk.
           rewrite Zlength_app_cons in Hk.
           destruct (Z_lt_ge_dec k (Zlength pr)) as [Hkin | Hklast].
           { rewrite (app_Znth1 0 pr [remainder] k) by lia.
             rewrite (app_Znth1 0 pe [1] k) by lia.
             specialize (Hentries k ltac:(lia)).
             tauto. }
           { assert (k = Zlength pr) by lia; subst k.
             rewrite (app_Znth2 0 pr [remainder] (Zlength pr)) by lia.
             rewrite (app_Znth2 0 pe [1] (Zlength pr)) by lia.
             rewrite Hlens, !Z.sub_diag; simpl.
             change (IsPrime remainder /\ 1 <= 1).
             split; [exact Hprime|lia]. }
        -- apply strict_prime_prefix_snoc; [exact Horder|].
           intros k Hk.
           specialize (Hentries k Hk).
           destruct Hentries as (_ & _ & Hbelow).
           lia.
Qed.

Lemma duplicated_prefix_is_rejected :
  ~ StrictFactorPrefix 60 4 5 [2; 2; 3] [1; 1; 1].
Proof.
  intros [_ Horder].
  specialize (Horder 0 1 ltac:(
    repeat rewrite Zlength_cons; rewrite Zlength_nil; lia)).
  rewrite Znth0_cons in Horder.
  rewrite Znth_cons in Horder by lia.
  replace (1 - 1) with 0 in Horder by lia.
  rewrite Znth0_cons in Horder; lia.
Qed.

Lemma duplicated_complete_prefix_is_rejected :
  ~ StrictFactorPrefix 12 4 1 [2; 2; 3] [1; 1; 1].
Proof.
  intros [_ Horder].
  specialize (Horder 0 1 ltac:(
    repeat rewrite Zlength_cons; rewrite Zlength_nil; lia)).
  rewrite Znth0_cons in Horder.
  rewrite Znth_cons in Horder by lia.
  replace (1 - 1) with 0 in Horder by lia.
  rewrite Znth0_cons in Horder; lia.
Qed.
End P090_FactorTable.
Export P090_FactorTable.

Module P090_FactorFoundations.

Import ListNotations.
Local Open Scope Z_scope.

(** A list-level form of the facts supplied by [FactorPrefix]. *)
Definition FactorEntriesAtLeastTwo (pr pe : list Z) : Prop :=
  forall k, 0 <= k < Zlength pr ->
    2 <= Znth k pr 0 /\ 1 <= Znth k pe 0.

Lemma factor_entries_of_strict_prefix m candidate remainder pr pe :
  StrictFactorPrefix m candidate remainder pr pe ->
  FactorEntriesAtLeastTwo pr pe.
Proof.
  intros [Hprefix _] k Hk.
  destruct Hprefix as (_ & _ & _ & _ & _ & Hentries & _).
  specialize (Hentries k Hk).
  destruct Hentries as [Hprime [He _]].
  destruct Hprime as [Hp _].
  split; lia.
Qed.

Lemma factor_product_lower_bound pr pe :
  Zlength pr = Zlength pe ->
  FactorEntriesAtLeastTwo pr pe ->
  Z.pow 2 (Zlength pr) <= factor_product pr pe.
Proof.
  revert pe.
  induction pr as [| p pr IH]; intros pe Hlen Hentries.
  - destruct pe as [| e pe].
    + rewrite Zlength_nil, Z.pow_0_r; reflexivity.
    + pose proof (Zlength_nonneg pe).
      rewrite Zlength_nil, Zlength_cons in Hlen; lia.
  - destruct pe as [| e pe].
    + pose proof (Zlength_nonneg pr).
      rewrite Zlength_nil, Zlength_cons in Hlen; lia.
    + assert (Hhead : 2 <= p /\ 1 <= e).
      { apply (Hentries 0).
        rewrite Zlength_cons.
        pose proof (Zlength_nonneg pr); lia. }
      assert (Htail : FactorEntriesAtLeastTwo pr pe).
      { intros k Hk.
        specialize (Hentries (k + 1) ltac:(
          rewrite Zlength_cons; lia)).
        rewrite !Znth_cons in Hentries by lia.
        replace (k + 1 - 1) with k in Hentries by lia.
        exact Hentries. }
      assert (Htail_len : Zlength pr = Zlength pe).
      { rewrite !Zlength_cons in Hlen; lia. }
      specialize (IH pe Htail_len Htail).
      assert (Hpow_head : 2 <= Z.pow p e).
      { pose proof (Z.pow_le_mono_r p 1 e ltac:(lia) ltac:(lia)).
        rewrite Z.pow_1_r in H; lia. }
      assert (Hpow_tail : 0 < Z.pow 2 (Zlength pr)).
      { apply Z.pow_pos_nonneg; [lia|apply Zlength_nonneg]. }
      rewrite Zlength_cons, Z.pow_succ_r by apply Zlength_nonneg.
      simpl factor_product.
      nia.
Qed.

Lemma strict_factor_prefix_product_lower_bound
    m candidate remainder pr pe :
  StrictFactorPrefix m candidate remainder pr pe ->
  Z.pow 2 (Zlength pr) <= factor_product pr pe.
Proof.
  intros Hstrict.
  apply factor_product_lower_bound.
  - destruct Hstrict as [[Hlen _] _]; exact Hlen.
  - now apply factor_entries_of_strict_prefix with m candidate remainder.
Qed.

Lemma strict_factor_prefix_power_bounded_by_m
    m candidate remainder pr pe :
  StrictFactorPrefix m candidate remainder pr pe ->
  Z.pow 2 (Zlength pr) <= m.
Proof.
  intros Hstrict.
  pose proof (strict_factor_prefix_product_lower_bound
                _ _ _ _ _ Hstrict) as Hlower.
  destruct Hstrict as [Hprefix _].
  destruct Hprefix as (_ & _ & _ & Hrem & Hproduct & _ & _).
  assert (Hpowpos : 0 < Z.pow 2 (Zlength pr)).
  { apply Z.pow_pos_nonneg; [lia|apply Zlength_nonneg]. }
  nia.
Qed.

Lemma strict_factor_prefix_length_lt_47
    m candidate remainder pr pe :
  StrictFactorPrefix m candidate remainder pr pe ->
  m <= 100000000000000 ->
  Zlength pr < 47.
Proof.
  intros Hstrict Hm.
  pose proof (strict_factor_prefix_power_bounded_by_m
                _ _ _ _ _ Hstrict) as Hbound.
  destruct (Z_lt_ge_dec (Zlength pr) 47); [assumption|].
  assert (Hmono : Z.pow 2 47 <= Z.pow 2 (Zlength pr)).
  { apply Z.pow_le_mono_r; lia. }
  assert (Hnumeric : 100000000000000 < Z.pow 2 47) by (vm_compute; lia).
  lia.
Qed.

Corollary strict_factor_prefix_has_free_slot
    m candidate remainder pr pe :
  StrictFactorPrefix m candidate remainder pr pe ->
  m <= 100000000000000 ->
  Zlength pr < 64.
Proof.
  intros Hstrict Hm.
  pose proof (strict_factor_prefix_length_lt_47
                _ _ _ _ _ Hstrict Hm).
  lia.
Qed.

(** Bridge between Coq's standard primality and the case's trial-division
    definition. *)
Lemma standard_prime_is_case_prime p :
  prime p -> IsPrime p.
Proof.
  intros Hp.
  pose proof (prime_ge_2 p Hp) as Hp2.
  split; [lia|].
  intros d Hd Hmod.
  assert (Hd0 : d <> 0) by lia.
  apply Z.mod_divide in Hmod; [|exact Hd0].
  destruct (prime_divisors p Hp d Hmod)
    as [-> | [-> | [-> | ->]]]; lia.
Qed.

Lemma standard_prime_divisor_exists n :
  1 < n -> exists p, prime p /\ Z.divide p n.
Proof.
  intros Hn.
  assert (Hnonneg : 0 <= n) by lia.
  revert Hn.
  pattern n.
  apply Z_lt_induction.
  - intros k IH Hk.
    destruct (prime_dec k) as [Hprime | Hcomposite].
    + exists k; split; [exact Hprime|].
      exists 1; nia.
    + destruct (not_prime_divide k Hk Hcomposite)
        as [d [[Hd1 Hdk] Hddiv]].
      destruct (IH d ltac:(lia) Hd1) as [p [Hp Hpd]].
      exists p; split; [exact Hp|].
      eapply Z.divide_trans; eauto.
  - exact Hnonneg.
Qed.

Lemma case_prime_divisor_exists n :
  1 < n -> exists p, IsPrime p /\ Z.divide p n.
Proof.
  intros Hn.
  destruct (standard_prime_divisor_exists n Hn) as [p [Hp Hdiv]].
  exists p; split; [now apply standard_prime_is_case_prime|exact Hdiv].
Qed.

Lemma no_small_prime_divisor_implies_prime
    frontier remainder :
  2 <= frontier ->
  1 < remainder ->
  remainder < frontier * frontier ->
  (forall p, IsPrime p -> p < frontier -> remainder mod p <> 0) ->
  IsPrime remainder.
Proof.
  intros Hfrontier Hremainder Hsquare Hexclude.
  split; [exact Hremainder|].
  intros d Hd Hmod.
  assert (Hd0 : d <> 0) by lia.
  apply Z.mod_divide in Hmod; [|exact Hd0].
  destruct Hmod as [cofactor Hfactor].
  assert (Hcofactor : 1 < cofactor) by nia.
  assert (Hsmall : d < frontier \/ cofactor < frontier) by nia.
  destruct Hsmall as [Hdsmall | Hcosmall].
  - destruct (case_prime_divisor_exists d ltac:(lia))
      as [p [Hp Hpd]].
    assert (Hp2 : 2 <= p) by (destruct Hp; lia).
    assert (Hple : p <= d).
    { destruct Hpd as [a Ha].
      assert (1 <= a) by nia.
      nia. }
    specialize (Hexclude p Hp ltac:(lia)).
    apply Hexclude.
    apply Z.mod_divide; [lia|].
    eapply Z.divide_trans; eauto.
    exists cofactor; exact Hfactor.
  - destruct (case_prime_divisor_exists cofactor Hcofactor)
      as [p [Hp Hpc]].
    assert (Hp2 : 2 <= p) by (destruct Hp; lia).
    assert (Hple : p <= cofactor).
    { destruct Hpc as [a Ha].
      assert (1 <= a) by nia.
      nia. }
    specialize (Hexclude p Hp ltac:(lia)).
    apply Hexclude.
    apply Z.mod_divide; [lia|].
    eapply Z.divide_trans; [exact Hpc|].
    exists d; nia.
Qed.

Lemma strict_factor_prefix_residual_prime
    m candidate remainder pr pe :
  StrictFactorPrefix m candidate remainder pr pe ->
  1 < remainder ->
  candidate * candidate > remainder ->
  IsPrime remainder.
Proof.
  intros [Hprefix _] Hrem Hsquare.
  destruct Hprefix as (_ & _ & Hcandidate & _ & _ & _ & Hexclude).
  eapply no_small_prime_divisor_implies_prime.
  - exact Hcandidate.
  - exact Hrem.
  - lia.
  - exact Hexclude.
Qed.

(** The complete factor-loop exit: either no residual remains, or the square
    guard makes the residual prime and it is appended into a provably free
    slot. *)
Theorem strict_factor_prefix_finalize_after_square_exit
    m candidate remainder pr pe :
  StrictFactorPrefix m candidate remainder pr pe ->
  m <= 100000000000000 ->
  candidate * candidate > remainder ->
  exists final_pr final_pe,
    ValidFactorTable m final_pr final_pe /\
    ((remainder = 1 /\ final_pr = pr /\ final_pe = pe) \/
     (1 < remainder /\
      final_pr = pr ++ [remainder] /\ final_pe = pe ++ [1])).
Proof.
  intros Hstrict Hm Hsquare.
  pose proof Hstrict as [Hprefix _].
  destruct Hprefix as (_ & _ & _ & Hrem & _ & _ & _).
  destruct (Z.eq_dec remainder 1) as [-> | Hnotone].
  - exists pr, pe.
    split.
    + now apply strict_factor_prefix_finalize_one with candidate.
    + left; tauto.
  - assert (Hgtone : 1 < remainder) by lia.
    pose proof (strict_factor_prefix_residual_prime
                  _ _ _ _ _ Hstrict Hgtone Hsquare) as Hprime.
    pose proof (strict_factor_prefix_has_free_slot
                  _ _ _ _ _ Hstrict Hm) as Hroom.
    exists (pr ++ [remainder]), (pe ++ [1]).
    split.
    + now apply strict_factor_prefix_finalize_prime_residual
        with candidate.
    + right; tauto.
Qed.
End P090_FactorFoundations.
Export P090_FactorFoundations.

Module P090_WalkFoundations.

Import ListNotations.
Local Open Scope Z_scope.

Module ETI := euler_theorem_inverse_lib.

(** The case's tail-recursive count is exactly the already-verified canonical
    finite residue count used by the Euler-theorem development. *)

Lemma coprime_count_filter (n : Z) (fuel : nat) :
  coprime_count n fuel =
  Z.of_nat
    (length
       (filter
          (fun k : nat => Z.eqb (Z.gcd (Z.of_nat k) n) 1)
          (seq 1 fuel))).
Proof.
  induction fuel as [| fuel IH].
  - reflexivity.
  - change
      (coprime_count n fuel +
         (if Z.eqb (Z.gcd (Z.of_nat (S fuel)) n) 1 then 1 else 0) =
       Z.of_nat
         (length
            (filter
               (fun k : nat => Z.eqb (Z.gcd (Z.of_nat k) n) 1)
               (seq 1 (S fuel))))).
    rewrite seq_S.
    replace (1 + fuel)%nat with (S fuel) by lia.
    rewrite filter_app, length_app, Nat2Z.inj_add, <- IH.
    destruct (Z.eqb (Z.gcd (Z.of_nat (S fuel)) n) 1) eqn:Htest.
    + replace
        (filter
           (fun k : nat => Z.eqb (Z.gcd (Z.of_nat k) n) 1)
           [S fuel]) with [S fuel].
      * reflexivity.
      * cbn [filter].
        rewrite Htest. reflexivity.
    + replace
        (filter
           (fun k : nat => Z.eqb (Z.gcd (Z.of_nat k) n) 1)
           [S fuel]) with (@nil nat).
      * reflexivity.
      * cbn [filter].
        rewrite Htest. reflexivity.
Qed.

Lemma euler_phi_bridge (n : Z) :
  EulerPhi n = ETI.EulerTotientValue n.
Proof.
  rewrite ETI.EulerTotientValue_compat.
  unfold EulerPhi, ETI.EulerTotientCountLegacy.
  apply coprime_count_filter.
Qed.

Lemma coprime_count_nonnegative (n : Z) (fuel : nat) :
  0 <= coprime_count n fuel.
Proof.
  rewrite coprime_count_filter.
  apply Nat2Z.is_nonneg.
Qed.

Lemma euler_phi_nonnegative (n : Z) :
  0 <= EulerPhi n.
Proof.
  unfold EulerPhi.
  apply coprime_count_nonnegative.
Qed.

Lemma euler_phi_positive_bounded (n : Z) :
  1 <= n ->
  1 <= EulerPhi n <= n.
Proof.
  intros Hn.
  rewrite euler_phi_bridge.
  rewrite ETI.EulerTotientValue_compat.
  unfold ETI.EulerTotientCountLegacy.
  set (residues :=
    filter
      (fun k : nat => Z.eqb (Z.gcd (Z.of_nat k) n) 1)
      (seq 1 (Z.to_nat n))).
  assert (Hone : In 1%nat residues).
  {
    unfold residues.
    apply filter_In.
    split.
    - apply in_seq. split; [lia |].
      assert (1 <= Z.to_nat n)%nat.
      {
        apply (proj1 (Z2Nat.inj_le 1 n ltac:(lia) ltac:(lia))).
        lia.
      }
      lia.
    - rewrite Z.gcd_1_l. reflexivity.
  }
  assert (Hlower : (1 <= length residues)%nat).
  {
    destruct residues as [| a residues].
    - contradiction.
    - simpl; lia.
  }
  assert (Hupper : (length residues <= Z.to_nat n)%nat).
  {
    unfold residues.
    eapply Nat.le_trans.
    - apply filter_length_le.
    - rewrite length_seq. lia.
  }
  split.
  - change (Z.of_nat 1 <= Z.of_nat (length residues)).
    apply Nat2Z.inj_le. exact Hlower.
  - rewrite <- (Z2Nat.id n) by lia.
    apply Nat2Z.inj_le. exact Hupper.
Qed.

(** Strict positivity needs a positive modulus.  The concrete zero case is a
    compiled counterexample to any unconditional positivity claim. *)

Example euler_phi_zero_counterexample : EulerPhi 0 = 0.
Proof. reflexivity. Qed.

Lemma is_prime_to_coq_prime (p : Z) :
  IsPrime p -> prime p.
Proof.
  intros [Hp Htrial].
  apply (proj1 (prime_alt p)).
  split; [exact Hp |].
  intros q Hq Hdivide.
  apply (Htrial q Hq).
  apply Zdivide_mod.
  exact Hdivide.
Qed.

Lemma euler_phi_prime_power
    (p exponent : Z) :
  IsPrime p ->
  1 <= exponent ->
  EulerPhi (p ^ exponent) =
    p ^ (exponent - 1) * (p - 1).
Proof.
  intros Hp He.
  rewrite euler_phi_bridge.
  apply ETI.euler_totient_prime_power__euler_phi_setup_removal.
  - apply is_prime_to_coq_prime. exact Hp.
  - exact He.
Qed.

Lemma euler_phi_coprime_multiplicative
    (a b : Z) :
  2 <= a ->
  2 <= b ->
  Z.gcd a b = 1 ->
  EulerPhi (a * b) = EulerPhi a * EulerPhi b.
Proof.
  intros Ha Hb Hgcd.
  rewrite !euler_phi_bridge.
  apply ETI.euler_totient_multiplicative__euler_phi_setup_removal;
    try assumption.
  apply Zgcd_1_rel_prime.
  exact Hgcd.
Qed.

Lemma euler_phi_coprime_prime_power
    (d p exponent : Z) :
  1 <= d ->
  IsPrime p ->
  1 <= exponent ->
  d mod p <> 0 ->
  EulerPhi (d * p ^ exponent) =
    EulerPhi d * (p ^ (exponent - 1) * (p - 1)).
Proof.
  intros Hd Hp He Hmod.
  rewrite !euler_phi_bridge.
  apply ETI.euler_totient_coprime_prime_power__euler_phi_setup_removal;
    try assumption.
  - apply is_prime_to_coq_prime. exact Hp.
  - intro Hdivide.
    apply Hmod.
    apply Zdivide_mod. exact Hdivide.
Qed.

(** The arithmetic and CRT portions of the order transition. *)

Lemma gcd_prime_power_one
    (d p exponent : Z) :
  0 <= exponent ->
  Z.gcd d p = 1 ->
  Z.gcd d (p ^ exponent) = 1.
Proof.
  intros He Hgcd.
  apply Zgcd_1_rel_prime.
  apply rel_prime_Zpower_r; [exact He |].
  apply Zgcd_1_rel_prime. exact Hgcd.
Qed.

Lemma pow_mod_coprime_product_one_iff
    (a b x exponent : Z) :
  2 <= a ->
  2 <= b ->
  Z.gcd a b = 1 ->
  (x ^ exponent) mod (a * b) = 1 <->
  (x ^ exponent) mod a = 1 /\ (x ^ exponent) mod b = 1.
Proof.
  intros Ha Hb Hgcd.
  assert (Hab : rel_prime a b).
  { apply Zgcd_1_rel_prime. exact Hgcd. }
  split.
  - intro Hproduct.
    assert (Hdivide_product : (a * b | x ^ exponent - 1)).
    { apply Zmod_divide_minus; nia. }
    split.
    + apply Zdivide_mod_minus; [lia |].
      eapply Z.divide_trans; [| exact Hdivide_product].
      exists b. ring.
    + apply Zdivide_mod_minus; [lia |].
      eapply Z.divide_trans; [| exact Hdivide_product].
      exists a. ring.
  - intros [Ha_one Hb_one].
    apply Zdivide_mod_minus; [nia |].
    apply ETI.euler_relprime_product_divide__euler_phi_setup_removal;
      [exact Hab | |].
    + apply Zmod_divide_minus; [lia | exact Ha_one].
    + apply Zmod_divide_minus; [lia | exact Hb_one].
Qed.

Definition ExactOrderCriterion (x modulus candidate : Z) : Prop :=
  0 < candidate /\
  forall exponent,
    0 <= exponent ->
    ((x ^ exponent) mod modulus = 1 <-> (candidate | exponent)).

Lemma lcm_as_gcd_quotient_product (a b : Z) :
  0 < a ->
  0 < b ->
  Z.lcm a b = a / Z.gcd a b * b.
Proof.
  intros Ha Hb.
  assert (Hgcd_nonzero : Z.gcd a b <> 0).
  {
    intro Hz.
    apply Z.gcd_eq_0 in Hz.
    lia.
  }
  assert (Hgcd_pos : 0 < Z.gcd a b) by
    (pose proof (Z.gcd_nonneg a b); lia).
  assert (Hquot_pos : 0 < b / Z.gcd a b).
  {
    apply Z.div_str_pos.
    split; [exact Hgcd_pos |].
    apply Z.divide_pos_le; [exact Hb | apply Z.gcd_divide_r].
  }
  unfold Z.lcm.
  rewrite Z.abs_eq by nia.
  rewrite Z.lcm_equiv1 by exact Hgcd_nonzero.
  symmetry.
  apply Z.lcm_equiv2.
  exact Hgcd_nonzero.
Qed.

Lemma exact_order_coprime_product_lcm
    (a b x order_a order_b : Z) :
  2 <= a ->
  2 <= b ->
  Z.gcd a b = 1 ->
  ExactOrderCriterion x a order_a ->
  ExactOrderCriterion x b order_b ->
  ExactOrderCriterion x (a * b) (Z.lcm order_a order_b).
Proof.
  intros Ha Hb Hgcd [Hord_a_pos Hord_a] [Hord_b_pos Hord_b].
  split.
  - rewrite lcm_as_gcd_quotient_product by assumption.
    assert (Hgcd_pos : 0 < Z.gcd order_a order_b).
    {
      pose proof (Z.gcd_nonneg order_a order_b).
      assert (Z.gcd order_a order_b <> 0).
      { intro Hz. apply Z.gcd_eq_0 in Hz. lia. }
      lia.
    }
    assert (Hquot_pos : 0 < order_a / Z.gcd order_a order_b).
    {
      apply Z.div_str_pos.
      split; [exact Hgcd_pos |].
      apply Z.divide_pos_le;
        [exact Hord_a_pos | apply Z.gcd_divide_l].
    }
    nia.
  - intros exponent Hexp.
    rewrite pow_mod_coprime_product_one_iff by assumption.
    rewrite Hord_a by exact Hexp.
    rewrite Hord_b by exact Hexp.
    symmetry.
    apply Z.lcm_divide_iff.
Qed.

Lemma order_lcm_runtime_formula
    (order_a order_b g : Z) :
  0 < order_a ->
  0 < order_b ->
  g = Z.gcd order_a order_b ->
  order_a / g * order_b = Z.lcm order_a order_b /\
  0 < order_a / g * order_b.
Proof.
  intros Ha Hb ->.
  split.
  - symmetry. apply lcm_as_gcd_quotient_product; assumption.
  -
  assert (Hgcd_pos : 0 < Z.gcd order_a order_b).
  {
    pose proof (Z.gcd_nonneg order_a order_b).
    assert (Z.gcd order_a order_b <> 0).
    { intro Hz. apply Z.gcd_eq_0 in Hz. lia. }
    lia.
  }
  assert (Hquot_pos : 0 < order_a / Z.gcd order_a order_b).
  {
    apply Z.div_str_pos.
    split; [exact Hgcd_pos |].
    apply Z.divide_pos_le; [exact Ha | apply Z.gcd_divide_l].
  }
    apply Z.mul_pos_pos; assumption.
Qed.

(** [Ord] is only a genuine multiplicative order under coprimality and an
    Euler bound.  Its fallback value is observably not an order otherwise. *)

Lemma order_search_positive (x n k : Z) (fuel : nat) :
  1 <= k ->
  1 <= order_search x n k fuel.
Proof.
  revert k.
  induction fuel as [| fuel IH]; intros k Hk; simpl.
  - lia.
  - destruct (Z.eqb (x ^ k mod n) 1); [exact Hk |].
    apply IH. lia.
Qed.

Lemma ord_positive (x n : Z) :
  1 <= Ord x n.
Proof.
  unfold Ord.
  destruct (Z.eqb n 1); [lia |].
  apply order_search_positive. lia.
Qed.

Example ord_non_coprime_counterexample :
  Ord 2 4 = 1 /\
  2 ^ Ord 2 4 mod 4 <> 1.
Proof. split; vm_compute; congruence. Qed.

(** Nonnegativity and the exact structural decomposition of the walk. *)

Lemma cycle_term_nonnegative (x d : Z) :
  0 <= CycleTerm x d.
Proof.
  unfold CycleTerm.
  destruct (Z.eqb d 1); [lia |].
  apply Z.div_pos.
  - apply euler_phi_nonnegative.
  - pose proof (ord_positive (x mod d) d). lia.
Qed.

Lemma sum_nat_range_nonnegative_local
    (first count : nat) (f : nat -> Z) :
  (forall k, 0 <= f k) ->
  0 <= sum_nat_range first count f.
Proof.
  revert first.
  induction count as [| count IH]; intros first Hf; simpl.
  - lia.
  - pose proof (Hf first).
    pose proof (IH (S first) Hf).
    lia.
Qed.

Lemma walk_suffix_lists_nonnegative
    (pr pe : list Z) (x d : Z) :
  0 <= walk_suffix_lists pr pe x d.
Proof.
  revert pe d.
  induction pr as [| p pr IH]; intros pe d;
    destruct pe as [| exponent pe].
  - change (0 <= CycleTerm x d).
    apply cycle_term_nonnegative.
  - change (0 <= CycleTerm x d).
    apply cycle_term_nonnegative.
  - change (0 <= CycleTerm x d).
    apply cycle_term_nonnegative.
  - change
      (0 <= sum_nat_range 0 (S (Z.to_nat exponent))
        (fun e =>
           walk_suffix_lists pr pe x (d * p ^ Z.of_nat e))).
    apply sum_nat_range_nonnegative_local.
    intros e. apply IH.
Qed.

Lemma walk_suffix_nonnegative
    (pr pe : list Z) (x i d : Z) :
  0 <= WalkSuffix pr pe x i d.
Proof.
  unfold WalkSuffix.
  apply walk_suffix_lists_nonnegative.
Qed.

Lemma walk_suffix_lists_cons
    (p exponent : Z) (pr pe : list Z) (x d : Z) :
  walk_suffix_lists (p :: pr) (exponent :: pe) x d =
  sum_nat_range 0 (S (Z.to_nat exponent))
    (fun e =>
       walk_suffix_lists pr pe x
         (d * p ^ Z.of_nat e)).
Proof. reflexivity. Qed.

Lemma walk_suffix_zero_index
    (pr pe : list Z) (x d : Z) :
  WalkSuffix pr pe x 0 d =
  walk_suffix_lists pr pe x d.
Proof. reflexivity. Qed.

Lemma walk_suffix_mismatched_left
    (pe : list Z) (x d : Z) :
  walk_suffix_lists [] pe x d = CycleTerm x d.
Proof. destruct pe; reflexivity. Qed.

Lemma walk_suffix_mismatched_right
    (pr : list Z) (x d : Z) :
  walk_suffix_lists pr [] x d = CycleTerm x d.
Proof. destruct pr; reflexivity. Qed.

(** Multiplication by a unit preserves every gcd stratum.  This is the first
    orbit fact needed by the final catching-set argument. *)

Lemma gcd_stratum_preserved
    (m x start exponent : Z) :
  0 < m ->
  0 <= exponent ->
  Z.gcd x m = 1 ->
  Z.gcd ((start * x ^ exponent) mod m) m = Z.gcd start m.
Proof.
  intros Hm Hexp Hunit.
  rewrite Z.gcd_mod by lia.
  apply Z.divide_antisym_nonneg; [apply Z.gcd_nonneg | apply Z.gcd_nonneg | |].
  - apply Z.gcd_greatest.
    + assert (Hrel_m_power : rel_prime m (x ^ exponent)).
      {
        apply rel_prime_Zpower_r; [exact Hexp |].
        apply rel_prime_sym.
        apply Zgcd_1_rel_prime. exact Hunit.
      }
      assert
        (Hrel_gcd_power : rel_prime (Z.gcd m (start * x ^ exponent))
                                      (x ^ exponent)).
      {
        apply rel_prime_div with m.
        - exact Hrel_m_power.
        - apply Z.gcd_divide_l.
      }
      apply Gauss with (x ^ exponent).
      * rewrite Z.mul_comm. apply Z.gcd_divide_r.
      * exact Hrel_gcd_power.
    + apply Z.gcd_divide_l.
  - apply Z.gcd_greatest.
    + apply Z.gcd_divide_r.
    + eapply Z.divide_trans.
      * apply Z.gcd_divide_l.
      * exists (x ^ exponent). ring.
Qed.

Lemma catches_all_contains_zero
    (m x : Z) (traps : list Z) :
  0 < m ->
  CatchesAll m x traps ->
  In 0 traps.
Proof.
  intros Hm (_ & _ & Hcatches).
  destruct (Hcatches 0 ltac:(lia)) as
      [time [room [Htime [Hroom Hin]]]].
  subst room.
  replace (0 * x ^ time) with 0 in Hin by ring.
  rewrite Z.mod_0_l in Hin by lia.
  exact Hin.
Qed.

Lemma catches_all_hits_same_gcd_stratum
    (m x : Z) (traps : list Z) :
  0 < m ->
  Z.gcd x m = 1 ->
  CatchesAll m x traps ->
  forall start,
    0 <= start < m ->
    exists room,
      In room traps /\
      Z.gcd room m = Z.gcd start m.
Proof.
  intros Hm Hunit (_ & _ & Hcatches) start Hstart.
  destruct (Hcatches start Hstart) as
      [time [room [Htime [Hroom Hin]]]].
  exists room. split; [exact Hin |].
  subst room.
  apply gcd_stratum_preserved;
    [exact Hm | lia | exact Hunit].
Qed.

(** Unresolved foundations, deliberately not represented by assumptions:

    - prove that the bounded [order_search] defining [Ord] satisfies
      [ExactOrderCriterion] when the base is coprime to a positive modulus;
    - prove that [ValidFactorTable] and [PrefixSelected] enumerate every
      positive divisor exactly once (unique prime factorization is the missing
      ingredient connecting the list representation to divisibility);
    - use that bijection to identify [WalkSuffix pr pe x 0 1] with the sum of
      [EulerPhi d / Ord (x mod d) d] over non-unit divisors [d] of [m];
    - prove the divisor identity [sum_(d|m) EulerPhi d = m], yielding the
      cumulative walk budget after order positivity and divisibility;
    - strengthen [gcd_stratum_preserved] to the orbit theorem: each nonzero
      gcd stratum is isomorphic to the units modulo its associated divisor,
      multiplication by [x] has orbit length [Ord], and any catching set must
      meet every such orbit.  That supplies both the catching-set construction
      and its matching lower bound.

    The two counterexamples above explain why positivity needs [n >= 1] and
    why the exact-order theorem must retain the coprimality/Euler hypotheses. *)
End P090_WalkFoundations.
Export P090_WalkFoundations.

Module P090_OrbitOptimality.

Import ListNotations.
Local Open Scope Z_scope.


(** Generic finite-sum infrastructure used by the divisor budget. *)

Lemma sum_nat_range_ext
    (first count : nat) (f g : nat -> Z) :
  (forall k, (first <= k < first + count)%nat -> f k = g k) ->
  sum_nat_range first count f = sum_nat_range first count g.
Proof.
  revert first.
  induction count as [| count IH]; intros first Heq; simpl.
  - reflexivity.
  - rewrite Heq by lia.
    f_equal.
    apply IH. intros k Hk. apply Heq. lia.
Qed.

Lemma sum_nat_range_mono
    (first count : nat) (f g : nat -> Z) :
  (forall k, (first <= k < first + count)%nat -> f k <= g k) ->
  sum_nat_range first count f <= sum_nat_range first count g.
Proof.
  revert first.
  induction count as [| count IH]; intros first Hle; simpl.
  - lia.
  - pose proof (Hle first ltac:(lia)) as Hhead.
    pose proof
      (IH (S first) (fun k Hk => Hle k ltac:(lia))) as Htail.
    lia.
Qed.

Lemma sum_nat_range_app
    (first left right : nat) (f : nat -> Z) :
  sum_nat_range first (left + right) f =
  sum_nat_range first left f +
  sum_nat_range (first + left) right f.
Proof.
  revert first.
  induction left as [| left IH]; intros first; simpl.
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite IH.
    replace (S first + left)%nat with (first + S left)%nat by lia.
    lia.
Qed.

(** The complete divisor-totient identity for a prime power.  This is the
    atomic case of [sum_(d|m) phi(d) = m], proved against the case's actual
    [EulerPhi] definition via the verified bridge in [P090_WalkFoundations]. *)

Lemma euler_phi_prime_power_sum_nat
    (p : Z) (n : nat) :
  IsPrime p ->
  sum_nat_range 0 (S n)
    (fun k => EulerPhi (p ^ Z.of_nat k)) =
  p ^ Z.of_nat n.
Proof.
  intros Hp.
  induction n as [| n IH].
  - simpl. reflexivity.
  - replace (S (S n)) with (S n + 1)%nat by lia.
    rewrite sum_nat_range_app.
    replace (0 + S n)%nat with (S n) by lia.
    rewrite IH.
    change
      (p ^ Z.of_nat n +
         (EulerPhi (p ^ Z.of_nat (S n)) + 0) =
       p ^ Z.of_nat (S n)).
    rewrite euler_phi_prime_power by
      (try exact Hp; rewrite Nat2Z.inj_succ; lia).
    rewrite !Nat2Z.inj_succ.
    replace (Z.of_nat n + 1 - 1) with (Z.of_nat n) by lia.
    rewrite Z.pow_succ_r by apply Nat2Z.is_nonneg.
    replace (Z.succ (Z.of_nat n) - 1) with (Z.of_nat n) by lia.
    ring.
Qed.

Lemma euler_phi_prime_power_sum
    (p exponent : Z) :
  IsPrime p ->
  0 <= exponent ->
  sum_nat_range 0 (S (Z.to_nat exponent))
    (fun k => EulerPhi (p ^ Z.of_nat k)) =
  p ^ exponent.
Proof.
  intros Hp He.
  rewrite <- (Z2Nat.id exponent) at 2 by exact He.
  apply euler_phi_prime_power_sum_nat.
  exact Hp.
Qed.

Lemma cycle_term_le_euler_phi (x d : Z) :
  CycleTerm x d <= EulerPhi d.
Proof.
  unfold CycleTerm.
  destruct (Z.eqb d 1) eqn:Hd.
  - pose proof (euler_phi_nonnegative d). lia.
  - apply Z.div_le_upper_bound.
    + pose proof (ord_positive (x mod d) d). lia.
    + pose proof (euler_phi_nonnegative d).
      pose proof (ord_positive (x mod d) d).
      nia.
Qed.

(** For a one-prime factor table, the walk's cumulative work is bounded by
    the exact prime-power divisor-totient sum.  No statement about [Spec] or
    orbit optimality is used. *)

Lemma walk_prime_power_budget
    (p exponent x : Z) :
  IsPrime p ->
  0 <= exponent ->
  0 <= walk_suffix_lists [p] [exponent] x 1 <= p ^ exponent.
Proof.
  intros Hp He.
  split.
  - apply walk_suffix_lists_nonnegative.
  - change
      (sum_nat_range 0 (S (Z.to_nat exponent))
         (fun k => CycleTerm x (1 * p ^ Z.of_nat k)) <=
       p ^ exponent).
    rewrite <- (euler_phi_prime_power_sum p exponent Hp He).
    apply sum_nat_range_mono.
    intros k Hk.
    replace (1 * p ^ Z.of_nat k) with (p ^ Z.of_nat k) by ring.
    apply cycle_term_le_euler_phi.
Qed.

(** Modular cancellation by a unit gives the exact return-time theorem for a
    unit orbit.  This is the core lower-bound fact: a unit orbit cannot return
    before its exact multiplicative order. *)

Lemma unit_orbit_return_iff
    (m x unit order exponent : Z) :
  2 <= m ->
  0 <= unit < m ->
  Z.gcd unit m = 1 ->
  0 <= exponent ->
  ExactOrderCriterion x m order ->
  ((unit * x ^ exponent) mod m = unit <-> (order | exponent)).
Proof.
  intros Hm Hunit_bounds Hunit_gcd Hexp [_ Horder].
  rewrite <- Horder by exact Hexp.
  split.
  - intro Hreturn.
    assert (Hdivide_product : (m | unit * (x ^ exponent - 1))).
    {
      replace (unit * (x ^ exponent - 1))
        with (unit * x ^ exponent - unit) by ring.
      apply Zmod_divide_minus; [lia | exact Hreturn].
    }
    assert (Hrel : rel_prime m unit).
    {
      apply rel_prime_sym.
      apply Zgcd_1_rel_prime. exact Hunit_gcd.
    }
    assert (Hdivide : (m | x ^ exponent - 1)).
    { apply Gauss with unit; assumption. }
    apply Zdivide_mod_minus; [lia | exact Hdivide].
  - intro Hpower.
    assert (Hdivide : (m | x ^ exponent - 1)).
    { apply Zmod_divide_minus; [lia | exact Hpower]. }
    apply Zdivide_mod_minus; [exact Hunit_bounds |].
    replace (unit * x ^ exponent - unit)
      with (unit * (x ^ exponent - 1)) by ring.
    destruct Hdivide as [q Hq].
    exists (unit * q).
    rewrite Hq. ring.
Qed.

Lemma unit_orbit_period
    (m x unit order time : Z) :
  2 <= m ->
  0 <= unit < m ->
  Z.gcd unit m = 1 ->
  0 <= time ->
  ExactOrderCriterion x m order ->
  (unit * x ^ (time + order)) mod m =
  (unit * x ^ time) mod m.
Proof.
  intros Hm Hunit_bounds Hunit_gcd Htime [Horder_pos Horder].
  assert (Horder_power : x ^ order mod m = 1).
  { apply Horder; [lia | exists 1; ring]. }
  rewrite Z.pow_add_r by lia.
  rewrite Z.mul_assoc.
  rewrite <- Z.mul_mod_idemp_r by lia.
  rewrite Horder_power.
  rewrite Z.mul_1_r.
  reflexivity.
Qed.

Lemma unit_orbit_no_early_return
    (m x unit order exponent : Z) :
  2 <= m ->
  0 <= unit < m ->
  Z.gcd unit m = 1 ->
  0 < exponent < order ->
  ExactOrderCriterion x m order ->
  (unit * x ^ exponent) mod m <> unit.
Proof.
  intros Hm Hunit_bounds Hunit_gcd Hexp Hcriterion Hreturn.
  pose proof
    (proj1
       (unit_orbit_return_iff
          m x unit order exponent Hm Hunit_bounds Hunit_gcd
          ltac:(lia) Hcriterion)
       Hreturn) as Hdivide.
  destruct Hdivide as [q Hq].
  destruct Hcriterion as [Horder_pos _].
  assert (0 < q) by nia.
  nia.
Qed.

(** A catching set really intersects the forward orbit of every unit start;
    combined with [unit_orbit_no_early_return], distinct orbit classes require
    distinct traps.  Constructing and counting a complete representative list
    remains the finite-quotient step documented below. *)

Lemma catches_all_hits_unit_orbit
    (m x : Z) (traps : list Z) (start : Z) :
  2 <= m ->
  Z.gcd x m = 1 ->
  CatchesAll m x traps ->
  0 <= start < m ->
  Z.gcd start m = 1 ->
  exists time room,
    0 <= time /\
    room = (start * x ^ time) mod m /\
    In room traps /\
    Z.gcd room m = 1.
Proof.
  intros Hm Hx_unit (_ & _ & Hcatches) Hstart Hstart_unit.
  destruct (Hcatches start Hstart) as
      [time [room [Htime [Hroom Hin]]]].
  exists time, room.
  split; [lia |].
  split; [exact Hroom |].
  split; [exact Hin |].
  subst room.
  rewrite <- Hstart_unit.
  apply gcd_stratum_preserved; [lia | lia |].
  exact Hx_unit.
Qed.

(** Exact unresolved boundary.

    The prime-power identity and budget above are complete.  Extending them to
    arbitrary [ValidFactorTable] requires the still-unproved conversion from
    its [Znth]-based sortedness clauses to an inductive pairwise-coprime table;
    the mathematical induction then multiplies the prime-power sums using
    [euler_phi_coprime_multiplicative].

    The orbit-return theorem is also complete, but the current library has no
    finite quotient construction for the equivalence relation generated by
    unit multiplication.  A full [Spec] theorem still needs, without choice
    axioms: (1) a concrete list containing exactly one representative of each
    unit orbit; (2) its length [EulerPhi d / Ord (x mod d) d]; (3) transport
    between the gcd-[m/d] stratum modulo [m] and units modulo [d]; and (4) the
    disjoint-orbit pigeonhole argument showing every [CatchesAll] list has at
    least one member per representative.  Those results also depend on proving
    [ExactOrderCriterion] for the bounded-search definition [Ord] under
    coprimality.  None of these conclusions is assumed or hidden in a
    predicate in this module. *)
End P090_OrbitOptimality.
Export P090_OrbitOptimality.

Module P090_WalkBridge.

Import ListNotations.
Local Open Scope Z_scope.

(** Finite-range sums.  These lemmas expose exactly the recursion used by
    [WalkExpSuffix], without assuming anything about the summands. *)

Lemma sum_nat_range_head (first count : nat) (f : nat -> Z) :
  sum_nat_range first (S count) f =
  f first + sum_nat_range (S first) count f.
Proof. reflexivity. Qed.

Lemma sum_nat_range_app (first left right : nat) (f : nat -> Z) :
  sum_nat_range first (left + right) f =
  sum_nat_range first left f +
  sum_nat_range (first + left) right f.
Proof.
  revert first.
  induction left as [| left IH]; intros first; simpl.
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite IH.
    replace (S first + left)%nat with (first + S left)%nat by lia.
    lia.
Qed.

Lemma sum_nat_range_nonnegative
    (first count : nat) (f : nat -> Z) :
  (forall k : nat, (first <= k < first + count)%nat -> 0 <= f k) ->
  0 <= sum_nat_range first count f.
Proof.
  revert first.
  induction count as [| count IH]; intros first Hf; simpl.
  - lia.
  - assert (Hhead : 0 <= f first).
    { apply Hf; lia. }
    assert (Htail : 0 <= sum_nat_range (S first) count f).
    { apply IH. intros k Hk. apply Hf. lia. }
    lia.
Qed.

Lemma sum_nat_range_nonnegative_pointwise
    (first count : nat) (f : nat -> Z) :
  (forall k : nat, 0 <= f k) ->
  0 <= sum_nat_range first count f.
Proof.
  intros Hf. apply sum_nat_range_nonnegative.
  intros k _. apply Hf.
Qed.

(** The exponent suffix consists of the current recursive call followed by
    the suffix beginning at the next exponent.  Both bounds are necessary:
    nonnegativity makes [Z.to_nat] preserve [next_e], and [next_e <= exponent]
    says that a head actually remains. *)

Lemma walk_exp_suffix_head_tail
    (pr pe : list Z) (x i next_e d : Z) :
  0 <= next_e <= Znth i pe 0 ->
  WalkExpSuffix pr pe x i next_e d =
    WalkSuffix pr pe x (i + 1)
      (d * Z.pow (Znth i pr 0) next_e) +
    WalkExpSuffix pr pe x i (next_e + 1) d.
Proof.
  intros Hbounds.
  unfold WalkExpSuffix.
  replace (Z.to_nat (Znth i pe 0 - next_e + 1))
    with (S (Z.to_nat (Znth i pe 0 - next_e))) by lia.
  simpl.
  rewrite (Z2Nat.id next_e) by lia.
  replace (S (Z.to_nat next_e)) with (Z.to_nat (next_e + 1)) by lia.
  replace (Znth i pe 0 - (next_e + 1) + 1)
    with (Znth i pe 0 - next_e) by lia.
  reflexivity.
Qed.

Lemma walk_exp_suffix_exact_exhaustion
    (pr pe : list Z) (x i d : Z) :
  WalkExpSuffix pr pe x i (Znth i pe 0 + 1) d = 0.
Proof.
  unfold WalkExpSuffix.
  replace (Znth i pe 0 - (Znth i pe 0 + 1) + 1) with 0 by lia.
  reflexivity.
Qed.

Lemma walk_exp_suffix_past_exhaustion
    (pr pe : list Z) (x i next_e d : Z) :
  Znth i pe 0 + 1 <= next_e ->
  WalkExpSuffix pr pe x i next_e d = 0.
Proof.
  intros Hpast.
  apply walk_exp_suffix_exhausted.
  lia.
Qed.

Lemma walk_exp_suffix_nonnegative
    (pr pe : list Z) (x i next_e d : Z) :
  (forall e : nat,
      0 <= WalkSuffix pr pe x (i + 1)
        (d * Z.pow (Znth i pr 0) (Z.of_nat e))) ->
  0 <= WalkExpSuffix pr pe x i next_e d.
Proof.
  intros Hsuffix.
  unfold WalkExpSuffix.
  apply sum_nat_range_nonnegative_pointwise.
  exact Hsuffix.
Qed.

(** Structural facts about a selected prefix.  Positivity is conditional on
    positivity of the selected bases, because [PrefixSelected] itself does not
    state that the table is valid. *)

Lemma prefix_selected_at_zero
    (pr pe : list Z) (d : Z) :
  PrefixSelected pr pe 0 d -> d = 1.
Proof.
  intros Hselected.
  inversion Hselected; subst; auto; lia.
Qed.

Lemma prefix_selected_successor_product
    (pr pe : list Z) (i d : Z) :
  0 < i ->
  PrefixSelected pr pe i d ->
  exists previous exponent,
    PrefixSelected pr pe (i - 1) previous /\
    0 <= i - 1 < Zlength pr /\
    0 <= exponent <= Znth (i - 1) pe 0 /\
    d = previous * Z.pow (Znth (i - 1) pr 0) exponent.
Proof.
  intros Hi Hselected.
  inversion Hselected as [| i0 previous exponent Hprefix Hindex Hexp];
    subst.
  - lia.
  - exists previous, exponent.
    replace (i0 + 1 - 1) with i0 by lia.
    split; [exact Hprefix |].
    split; [exact Hindex |].
    split; [exact Hexp |].
    reflexivity.
Qed.

Lemma prefix_selected_positive
    (pr pe : list Z) (i d : Z) :
  PrefixSelected pr pe i d ->
  (forall k, 0 <= k < i -> 0 < Znth k pr 0) ->
  0 < d.
Proof.
  intros Hselected.
  induction Hselected as
      [| i0 previous exponent Hprefix IH Hindex Hexp]; intros Hbases.
  - lia.
  - assert (Hprevious : 0 < previous).
    { apply IH. intros k Hk. apply Hbases. lia. }
    assert (Hbase : 0 < Znth i0 pr 0).
    { apply Hbases. lia. }
    assert (Hpow : 0 < Z.pow (Znth i0 pr 0) exponent).
    { apply Z.pow_pos_nonneg; lia. }
    nia.
Qed.

Lemma prefix_selected_index_bounds
    (pr pe : list Z) (i d : Z) :
  PrefixSelected pr pe i d ->
  0 <= i <= Zlength pr.
Proof.
  intros Hselected.
  induction Hselected as
      [| i0 previous exponent Hprefix IH Hindex Hexp].
  - pose proof (Zlength_nonneg pr). lia.
  - lia.
Qed.

Lemma prefix_selected_positive_from_valid_table
    (m : Z) (pr pe : list Z) (i d : Z) :
  ValidFactorTable m pr pe ->
  PrefixSelected pr pe i d ->
  0 < d.
Proof.
  intros Hvalid Hselected.
  destruct Hvalid as (_ & _ & _ & Hentries & _).
  pose proof (prefix_selected_index_bounds pr pe i d Hselected) as Hbounds.
  apply (prefix_selected_positive pr pe i d Hselected).
  intros k Hk.
  specialize (Hentries k ltac:(lia)).
  destruct Hentries as [[Hprime _] _].
  lia.
Qed.

Lemma prefix_selected_step_product
    (pr pe : list Z) (i d exponent : Z) :
  PrefixSelected pr pe i d ->
  0 <= i < Zlength pr ->
  0 <= exponent <= Znth i pe 0 ->
  PrefixSelected pr pe (i + 1)
    (d * Z.pow (Znth i pr 0) exponent).
Proof.
  exact (prefix_selected_step pr pe i d exponent).
Qed.

(** A constructor-facing version of [PrimePowerTransition].  The hard CRT,
    Euler-phi, and multiplicative-order facts are explicit premises rather
    than conclusions extracted from an already-built transition predicate. *)

Lemma prime_power_transition_build
    (x d phi ord p e pk ph o g next_d next_phi next_ord : Z) :
  0 < d ->
  1 < p ->
  1 <= e ->
  pk = Z.pow p e ->
  ph = EulerPhi pk ->
  o = Ord (x mod pk) pk ->
  g = Z.gcd ord o ->
  next_d = d * pk ->
  next_phi = phi * ph ->
  next_ord = ord / g * o ->
  Z.gcd d pk = 1 ->
  EulerPhi next_d = EulerPhi d * EulerPhi pk ->
  Ord x next_d = next_ord ->
  0 < next_d ->
  0 < next_phi ->
  0 < next_ord ->
  PrimePowerTransition
    x d phi ord p e pk ph o g next_d next_phi next_ord.
Proof.
  unfold PrimePowerTransition.
  tauto.
Qed.

(** Honest final boundary.  Completion of the C walk is kept separate from
    the mathematical orbit theorem.  The bridge asks for an actual catching
    set of the computed size and a lower bound for every catching set; it does
    not hide [Spec] in a loop invariant. *)

Definition WalkCompleted
    (pr pe : list Z) (x total : Z) : Prop :=
  total = WalkSuffix pr pe x 0 1.

Definition OrbitCoverUpperBound
    (m x cycle_count : Z) : Prop :=
  exists traps,
    CatchesAll m x traps /\
    Zlength traps = cycle_count + 1.

Definition OrbitCoverLowerBound
    (m x cycle_count : Z) : Prop :=
  forall traps,
    CatchesAll m x traps ->
    cycle_count + 1 <= Zlength traps.

Lemma walk_completed_from_exhausted_loop
    (pr pe : list Z) (x total next_e : Z) :
  WalkLoopState pr pe x 0 1 0 total next_e ->
  Znth 0 pe 0 < next_e ->
  WalkCompleted pr pe x total.
Proof.
  intros Hloop Hexhausted.
  unfold WalkCompleted, WalkLoopState in *.
  rewrite (walk_exp_suffix_exhausted pr pe x 0 1 next_e Hexhausted)
    in Hloop.
  lia.
Qed.

Lemma orbit_cover_bounds_imply_spec
    (m x cycle_count : Z) :
  OrbitCoverUpperBound m x cycle_count ->
  OrbitCoverLowerBound m x cycle_count ->
  Spec m x (cycle_count + 1).
Proof.
  intros [traps [Hcatches Hlength]] Hlower.
  unfold Spec, min_value_of_subset, min_object_of_subset.
  exists (cycle_count + 1).
  split.
  - split.
    + exists traps. split; [exact Hcatches | symmetry; exact Hlength].
    + intros candidate [candidate_traps [Hcandidate Hcandidate_length]].
      simpl.
      subst candidate.
      apply Hlower; exact Hcandidate.
  - reflexivity.
Qed.

Lemma walk_completed_and_orbit_bounds_imply_spec
    (pr pe : list Z) (m x total : Z) :
  WalkCompleted pr pe x total ->
  OrbitCoverUpperBound m x (WalkSuffix pr pe x 0 1) ->
  OrbitCoverLowerBound m x (WalkSuffix pr pe x 0 1) ->
  Spec m x (total + 1).
Proof.
  intros Hcompleted Hupper Hlower.
  unfold WalkCompleted in Hcompleted.
  subst total.
  apply orbit_cover_bounds_imply_spec; assumption.
Qed.
End P090_WalkBridge.
Export P090_WalkBridge.

Module P090_TableBudget.

Import ListNotations.
Local Open Scope Z_scope.


(** A list-native view of [ValidFactorTable].  Keeping the ordering premise on
    every tail element makes the induction follow the actual nested walk. *)
Inductive OrderedPrimeTable : list Z -> list Z -> Prop :=
| ordered_prime_table_nil : OrderedPrimeTable [] []
| ordered_prime_table_cons : forall p exponent pr pe,
    IsPrime p ->
    1 <= exponent ->
    Forall (fun q => p < q) pr ->
    OrderedPrimeTable pr pe ->
    OrderedPrimeTable (p :: pr) (exponent :: pe).

Lemma valid_factor_table_ordered_aux
    (pr pe : list Z) :
  Zlength pr = Zlength pe ->
  (forall k, 0 <= k < Zlength pr ->
     IsPrime (Znth k pr 0) /\ 1 <= Znth k pe 0) ->
  (forall j k,
     0 <= j /\ j < k /\ k < Zlength pr ->
     Znth j pr 0 < Znth k pr 0) ->
  OrderedPrimeTable pr pe.
Proof.
  revert pe.
  induction pr as [| p pr IH]; intros pe Hlen Hentry Horder.
  - destruct pe; [constructor |].
    rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
  - destruct pe as [| exponent pe].
    + rewrite !Zlength_correct in Hlen. simpl in Hlen. lia.
    + pose proof (Zlength_nonneg pr) as Hprlen.
      constructor.
      * pose proof
          (Hentry 0 ltac:(rewrite Zlength_cons; lia)) as Hhead.
        rewrite !Znth0_cons in Hhead.
        exact (proj1 Hhead).
      * pose proof
          (Hentry 0 ltac:(rewrite Zlength_cons; lia)) as Hhead.
        rewrite !Znth0_cons in Hhead.
        exact (proj2 Hhead).
      * apply Forall_forall.
        intros q Hq.
        apply In_nth_error in Hq.
        destruct Hq as [n Hnth].
        assert (Hnlt : (n < length pr)%nat).
        { apply nth_error_Some. rewrite Hnth. discriminate. }
        assert (Hznth : Znth (Z.of_nat n) pr 0 = q).
        {
          unfold Znth. rewrite Nat2Z.id.
          eapply nth_error_nth. exact Hnth.
        }
        specialize (Horder 0 (Z.of_nat n + 1)).
        rewrite Znth0_cons in Horder.
        rewrite Znth_cons in Horder by lia.
        replace (Z.of_nat n + 1 - 1) with (Z.of_nat n) in Horder by lia.
        rewrite Hznth in Horder.
        apply Horder.
        rewrite Zlength_cons, Zlength_correct.
        split; [lia |].
        apply Nat2Z.inj_lt in Hnlt. lia.
      * apply IH.
        -- rewrite !Zlength_cons in Hlen. lia.
        -- intros k Hk.
           specialize (Hentry (k + 1) ltac:(rewrite Zlength_cons; lia)).
           rewrite !Znth_cons in Hentry by lia.
           replace (k + 1 - 1) with k in Hentry by lia.
           exact Hentry.
        -- intros j k Hjk.
           specialize (Horder (j + 1) (k + 1)
             ltac:(rewrite Zlength_cons; lia)).
           rewrite !Znth_cons in Horder by lia.
           replace (j + 1 - 1) with j in Horder by lia.
           replace (k + 1 - 1) with k in Horder by lia.
           exact Horder.
Qed.

Lemma valid_factor_table_ordered
    (m : Z) (pr pe : list Z) :
  ValidFactorTable m pr pe -> OrderedPrimeTable pr pe.
Proof.
  intros (Hlen & _ & _ & Hentry & Horder).
  eapply valid_factor_table_ordered_aux; eauto.
Qed.

(** The same recursion as [walk_suffix_lists], with the leaf contribution
    replaced by the full totient of the selected product. *)
Fixpoint enumerated_phi_sum (pr pe : list Z) (d : Z) : Z :=
  match pr, pe with
  | p :: pr', exponent :: pe' =>
      sum_nat_range 0 (S (Z.to_nat exponent))
        (fun k => enumerated_phi_sum pr' pe'
          (d * p ^ Z.of_nat k))
  | _, _ => EulerPhi d
  end.

Lemma sum_nat_range_mul_l
    (first count : nat) (c : Z) (f : nat -> Z) :
  sum_nat_range first count (fun k => c * f k) =
  c * sum_nat_range first count f.
Proof.
  revert first.
  induction count as [| count IH]; intros first; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

Lemma sum_nat_range_mul_r
    (first count : nat) (c : Z) (f : nat -> Z) :
  sum_nat_range first count (fun k => f k * c) =
  sum_nat_range first count f * c.
Proof.
  revert first.
  induction count as [| count IH]; intros first; simpl.
  - ring.
  - rewrite IH. ring.
Qed.

Lemma euler_phi_one : EulerPhi 1 = 1.
Proof. reflexivity. Qed.

Lemma euler_phi_coprime_prime_power_all
    (d p exponent : Z) :
  1 <= d ->
  IsPrime p ->
  0 <= exponent ->
  Z.gcd d p = 1 ->
  EulerPhi (d * p ^ exponent) =
    EulerPhi d * EulerPhi (p ^ exponent).
Proof.
  intros Hd Hp He Hgcd.
  destruct (Z.eq_dec exponent 0) as [-> | Hne].
  - simpl. rewrite euler_phi_one, !Z.mul_1_r. reflexivity.
  - assert (Hexponent : 1 <= exponent) by lia.
    assert (Hmod : d mod p <> 0).
    {
      apply Zrel_prime_neq_mod_0.
      - exact (proj1 Hp).
      - apply Zgcd_1_rel_prime. exact Hgcd.
    }
    rewrite (euler_phi_coprime_prime_power d p exponent
      Hd Hp Hexponent Hmod).
    rewrite (euler_phi_prime_power p exponent Hp Hexponent).
    reflexivity.
Qed.

Lemma euler_phi_coprime_prime_power_sum
    (d p exponent : Z) :
  1 <= d ->
  IsPrime p ->
  0 <= exponent ->
  Z.gcd d p = 1 ->
  sum_nat_range 0 (S (Z.to_nat exponent))
    (fun k => EulerPhi (d * p ^ Z.of_nat k)) =
  EulerPhi d * p ^ exponent.
Proof.
  intros Hd Hp He Hgcd.
  transitivity
    (sum_nat_range 0 (S (Z.to_nat exponent))
       (fun k => EulerPhi d * EulerPhi (p ^ Z.of_nat k))).
  - apply sum_nat_range_ext. intros k Hk.
    apply euler_phi_coprime_prime_power_all; try assumption.
    apply Nat2Z.is_nonneg.
  - rewrite sum_nat_range_mul_l.
    rewrite euler_phi_prime_power_sum by assumption.
    reflexivity.
Qed.

Definition CoprimeToTable (d : Z) (pr : list Z) : Prop :=
  Forall (fun p => Z.gcd d p = 1) pr.

Lemma smaller_distinct_primes_coprime
    (p q : Z) :
  IsPrime p -> IsPrime q -> p < q -> Z.gcd p q = 1.
Proof.
  intros Hp Hq Hlt.
  apply Zgcd_1_rel_prime.
  apply rel_prime_sym.
  apply prime_rel_prime.
  - apply is_prime_to_coq_prime. exact Hq.
  - intro Hdivide.
    pose proof (proj1 Hp) as Hpgt.
    pose proof (Z.divide_pos_le q p ltac:(lia) Hdivide).
    lia.
Qed.

Lemma coprime_to_table_extend
    (d p : Z) (pr : list Z) (k : nat) :
  CoprimeToTable d pr ->
  IsPrime p ->
  Forall IsPrime pr ->
  Forall (fun q => p < q) pr ->
  CoprimeToTable (d * p ^ Z.of_nat k) pr.
Proof.
  intros Hd Hp Hprimes Hlt.
  unfold CoprimeToTable in *.
  induction pr as [| q pr IH].
  - constructor.
  - inversion Hd as [| ? ? Hdq Hdrest]; subst.
    inversion Hprimes as [| ? ? Hq Hqrest]; subst.
    inversion Hlt as [| ? ? Hpq Hpqrest]; subst.
    constructor.
    + apply Zgcd_1_rel_prime.
      apply rel_prime_sym.
      apply rel_prime_mult.
      * apply rel_prime_sym. apply Zgcd_1_rel_prime. exact Hdq.
      * apply rel_prime_Zpower_r.
        -- apply Nat2Z.is_nonneg.
        -- apply rel_prime_sym. apply Zgcd_1_rel_prime.
           apply smaller_distinct_primes_coprime; assumption.
    + apply IH; assumption.
Qed.

Lemma ordered_prime_table_all_primes
    (pr pe : list Z) :
  OrderedPrimeTable pr pe -> Forall IsPrime pr.
Proof.
  intros Htable. induction Htable; constructor; assumption.
Qed.

Lemma enumerated_phi_sum_factor_product
    (pr pe : list Z) (d : Z) :
  OrderedPrimeTable pr pe ->
  1 <= d ->
  CoprimeToTable d pr ->
  enumerated_phi_sum pr pe d =
    EulerPhi d * factor_product pr pe.
Proof.
  intros Htable.
  revert d.
  induction Htable as
      [| p exponent pr pe Hp He Hlt Htail IH];
    intros d Hd Hcoprime.
  - simpl. ring.
  - change
      (sum_nat_range 0 (S (Z.to_nat exponent))
         (fun k => enumerated_phi_sum pr pe
           (d * p ^ Z.of_nat k)) =
       EulerPhi d *
         (p ^ exponent * factor_product pr pe)).
    inversion Hcoprime as [| ? ? Hgcd Hcoprime_tail]; subst.
    transitivity
      (sum_nat_range 0 (S (Z.to_nat exponent))
         (fun k =>
            EulerPhi (d * p ^ Z.of_nat k) *
            factor_product pr pe)).
    + apply sum_nat_range_ext. intros k Hk.
      apply IH.
      * pose proof (proj1 Hp) as Hpgt.
        pose proof (Z.pow_pos_nonneg p (Z.of_nat k) ltac:(lia) ltac:(lia)).
        nia.
      * apply coprime_to_table_extend; try assumption.
        apply ordered_prime_table_all_primes with pe. exact Htail.
    + rewrite sum_nat_range_mul_r.
      rewrite (euler_phi_coprime_prime_power_sum d p exponent
        Hd Hp ltac:(lia) Hgcd).
      ring.
Qed.

Lemma coprime_one_table (pr : list Z) : CoprimeToTable 1 pr.
Proof.
  unfold CoprimeToTable.
  induction pr; constructor; [apply Z.gcd_1_l | assumption].
Qed.

Lemma valid_factor_table_enumerated_phi_exact
    (m : Z) (pr pe : list Z) :
  ValidFactorTable m pr pe ->
  enumerated_phi_sum pr pe 1 = m.
Proof.
  intros Hvalid.
  destruct Hvalid as (Hlen & Hbound & Hproduct & Hentry & Horder).
  assert (Htable : OrderedPrimeTable pr pe).
  { eapply valid_factor_table_ordered_aux; eauto. }
  rewrite enumerated_phi_sum_factor_product by
    (try exact Htable; try lia; apply coprime_one_table).
  rewrite euler_phi_one, Z.mul_1_l.
  symmetry. exact Hproduct.
Qed.

Lemma walk_suffix_lists_le_enumerated_phi
    (pr pe : list Z) (x d : Z) :
  walk_suffix_lists pr pe x d <= enumerated_phi_sum pr pe d.
Proof.
  revert pe d.
  induction pr as [| p pr IH]; intros pe d;
    destruct pe as [| exponent pe].
  - change (CycleTerm x d <= EulerPhi d).
    apply cycle_term_le_euler_phi.
  - change (CycleTerm x d <= EulerPhi d).
    apply cycle_term_le_euler_phi.
  - change (CycleTerm x d <= EulerPhi d).
    apply cycle_term_le_euler_phi.
  - change
      (sum_nat_range 0 (S (Z.to_nat exponent))
         (fun k => walk_suffix_lists pr pe x
           (d * p ^ Z.of_nat k)) <=
       sum_nat_range 0 (S (Z.to_nat exponent))
         (fun k => enumerated_phi_sum pr pe
           (d * p ^ Z.of_nat k))).
    apply sum_nat_range_mono.
    intros k Hk. apply IH.
Qed.

Lemma nonunit_cycle_term_exact_bounds
    (x d : Z) :
  d <> 1 ->
  CycleTerm x d =
    EulerPhi d / Ord (x mod d) d /\
  0 <= CycleTerm x d <= EulerPhi d.
Proof.
  intros Hd.
  split.
  - unfold CycleTerm.
    destruct (Z.eqb_spec d 1); [contradiction | reflexivity].
  - split.
    + apply cycle_term_nonnegative.
    + apply cycle_term_le_euler_phi.
Qed.

Lemma ordered_table_walk_bounds
    (pr pe : list Z) (x d : Z) :
  OrderedPrimeTable pr pe ->
  1 <= d ->
  CoprimeToTable d pr ->
  0 <= walk_suffix_lists pr pe x d <=
    EulerPhi d * factor_product pr pe.
Proof.
  intros Htable Hd Hcoprime.
  split.
  - apply walk_suffix_lists_nonnegative.
  - eapply Z.le_trans.
    + apply walk_suffix_lists_le_enumerated_phi.
    + rewrite (enumerated_phi_sum_factor_product pr pe d
        Htable Hd Hcoprime).
      lia.
Qed.

Lemma walk_suffix_recursive_budget
    (m before : Z) (pr pe : list Z) (x i d : Z) :
  OrderedPrimeTable
    (skipn (Z.to_nat i) pr) (skipn (Z.to_nat i) pe) ->
  1 <= d ->
  CoprimeToTable d (skipn (Z.to_nat i) pr) ->
  0 <= before ->
  before +
    EulerPhi d *
      factor_product
        (skipn (Z.to_nat i) pr) (skipn (Z.to_nat i) pe) <= m ->
  WalkBudget m before (WalkSuffix pr pe x i d).
Proof.
  intros Htable Hd Hcoprime Hbefore Hcapacity.
  unfold WalkSuffix.
  unfold WalkBudget.
  pose proof
    (ordered_table_walk_bounds
       (skipn (Z.to_nat i) pr) (skipn (Z.to_nat i) pe)
       x d Htable Hd Hcoprime) as Hwalk.
  lia.
Qed.

Lemma valid_factor_table_walk_bounds
    (m x : Z) (pr pe : list Z) :
  ValidFactorTable m pr pe ->
  0 <= WalkSuffix pr pe x 0 1 <= m.
Proof.
  intros Hvalid. split.
  - apply walk_suffix_nonnegative.
  - rewrite walk_suffix_zero_index.
    eapply Z.le_trans.
    + apply walk_suffix_lists_le_enumerated_phi.
    + rewrite (valid_factor_table_enumerated_phi_exact m pr pe Hvalid).
      lia.
Qed.

Lemma valid_factor_table_initial_walk_budget
    (m x : Z) (pr pe : list Z) :
  ValidFactorTable m pr pe ->
  WalkBudget m 0 (WalkSuffix pr pe x 0 1).
Proof.
  intros Hvalid.
  unfold WalkBudget.
  pose proof (valid_factor_table_walk_bounds m x pr pe Hvalid).
  lia.
Qed.

Lemma walk_budget_from_cumulative_bound
    (m before work : Z) :
  0 <= before ->
  0 <= work ->
  before + work <= m ->
  WalkBudget m before work.
Proof. unfold WalkBudget; tauto. Qed.

Lemma walk_suffix_cumulative_budget
    (m before : Z) (pr pe : list Z) (x i d : Z) :
  0 <= before ->
  before + WalkSuffix pr pe x i d <= m ->
  WalkBudget m before (WalkSuffix pr pe x i d).
Proof.
  intros Hbefore Hbound.
  apply walk_budget_from_cumulative_bound; try assumption.
  apply walk_suffix_nonnegative.
Qed.

(** This module deliberately proves the table budget without proving that the
    enumerated products are all divisors.  The sole remaining bridge to the
    final optimality theorem is therefore orbit/divisor surjectivity, not a
    missing arithmetic fact about the C walk's cumulative bound. *)
End P090_TableBudget.
Export P090_TableBudget.

Module P090_DivisorEnumeration.

Import ListNotations.
Local Open Scope Z_scope.

(** Explicit exponent vectors and their products.  This relation follows the
    same head-first recursion as [walk_suffix_lists]. *)
Inductive ExponentTrace : list Z -> list Z -> list Z -> Z -> Prop :=
| exponent_trace_nil :
    ExponentTrace [] [] [] 1
| exponent_trace_cons : forall p pr maximum pe exponent exponents product,
    0 <= exponent <= maximum ->
    ExponentTrace pr pe exponents product ->
    ExponentTrace (p :: pr) (maximum :: pe) (exponent :: exponents)
      (Z.pow p exponent * product).

Fixpoint enumerated_products (pr pe : list Z) : list Z :=
  match pr, pe with
  | p :: pr', maximum :: pe' =>
      concat
        (map
           (fun n =>
              map (fun product => Z.pow p (Z.of_nat n) * product)
                (enumerated_products pr' pe'))
           (seq 0 (S (Z.to_nat maximum))))
  | _, _ => [1]
  end.

Fixpoint enumerated_walk_terms
    (pr pe : list Z) (x d : Z) : list Z :=
  match pr, pe with
  | p :: pr', maximum :: pe' =>
      concat
        (map
           (fun n =>
              enumerated_walk_terms pr' pe' x
                (d * Z.pow p (Z.of_nat n)))
           (seq 0 (S (Z.to_nat maximum))))
  | _, _ => [CycleTerm x d]
  end.

Definition NonUnitDivisorCycleSum
    (pr pe : list Z) (x : Z) : Z :=
  fold_right Z.add 0
    (map (CycleTerm x)
      (filter (fun d => negb (Z.eqb d 1))
        (enumerated_products pr pe))).

Lemma exponent_trace_lengths pr pe exponents product :
  ExponentTrace pr pe exponents product ->
  length pr = length pe /\ length exponents = length pr.
Proof.
  intros Htrace; induction Htrace; simpl; lia.
Qed.

Lemma exponent_trace_product_functional pr pe exponents a b :
  ExponentTrace pr pe exponents a ->
  ExponentTrace pr pe exponents b ->
  a = b.
Proof.
  intros Ha; revert b.
  induction Ha; intros b Hb; inversion Hb; subst; auto.
  f_equal; eauto.
Qed.

Lemma enumerated_products_trace pr pe product :
  Zlength pr = Zlength pe ->
  Forall (fun exponent => 0 <= exponent) pe ->
  In product (enumerated_products pr pe) <->
  exists exponents, ExponentTrace pr pe exponents product.
Proof.
  revert pe product.
  induction pr as [| p pr IH]; intros pe product Hlen Hnonnegative.
  - destruct pe as [| maximum pe].
    + simpl.
      split.
      * intros [Hproduct | []].
        subst product; exists []; constructor.
      * intros [exponents Htrace].
        inversion Htrace; subst; simpl; auto.
    + pose proof (Zlength_nonneg pe).
      rewrite Zlength_nil, Zlength_cons in Hlen; lia.
  - destruct pe as [| maximum pe].
    + pose proof (Zlength_nonneg pr).
      rewrite Zlength_nil, Zlength_cons in Hlen; lia.
    + assert (Htail_len : Zlength pr = Zlength pe).
      { rewrite !Zlength_cons in Hlen; lia. }
      inversion Hnonnegative as [| maximum0 pe0 Hmaximum Htail_nonnegative];
        subst.
      unfold enumerated_products; fold enumerated_products.
      rewrite in_concat.
      split.
      * intros [block [Hblock Hin]].
        apply in_map_iff in Hblock.
        destruct Hblock as [n [Hblock Hn]].
        subst block.
        apply in_map_iff in Hin.
        destruct Hin as [tail [Hproduct Htail]].
        subst product.
        apply IH in Htail; [|exact Htail_len|exact Htail_nonnegative].
        destruct Htail as [exponents Htrace].
        exists (Z.of_nat n :: exponents).
        constructor.
        -- apply in_seq in Hn.
           destruct Hn as [_ Hn].
           split; [lia|].
           assert (Z.of_nat n < Z.of_nat (S (Z.to_nat maximum)))
             by (apply Nat2Z.inj_lt; exact Hn).
           rewrite Nat2Z.inj_succ, Z2Nat.id in H by lia.
           lia.
        -- exact Htrace.
      * intros [exponents Htrace].
        inversion Htrace as
            [| p0 pr0 maximum0 pe0 exponent exponents0 tail Hexp Htail];
          subst.
        exists
          (map
             (fun tail0 => Z.pow p (Z.of_nat (Z.to_nat exponent)) * tail0)
             (enumerated_products pr pe)).
        split.
        -- apply in_map_iff.
           exists (Z.to_nat exponent); split; [reflexivity|].
           apply in_seq.
           split; [lia|].
           apply Nat2Z.inj_lt.
           rewrite !Z2Nat.id by lia.
           lia.
        -- apply in_map_iff.
           exists tail; split.
           ++ rewrite Z2Nat.id by lia; reflexivity.
           ++ apply IH; [exact Htail_len|exact Htail_nonnegative|].
              exists exponents0; exact Htail.
Qed.

Lemma valid_factor_table_exponents_nonnegative m pr pe :
  ValidFactorTable m pr pe ->
  Forall (fun exponent => 0 <= exponent) pe.
Proof.
  intros (Hlen & _ & _ & Hentries & _).
  revert pr Hlen Hentries.
  induction pe as [| exponent pe IH]; intros pr Hlen Hentries.
  - constructor.
  - destruct pr as [| p pr].
    + pose proof (Zlength_nonneg pe).
      rewrite Zlength_nil, Zlength_cons in Hlen; lia.
    + constructor.
      * specialize (Hentries 0 ltac:(
          rewrite Zlength_cons; pose proof (Zlength_nonneg pr); lia)).
        rewrite !Znth0_cons in Hentries.
        destruct Hentries as [_ Hexp]; lia.
      * apply IH with pr.
        -- rewrite !Zlength_cons in Hlen; lia.
        -- intros k Hk.
           specialize (Hentries (k + 1) ltac:(
             rewrite Zlength_cons; lia)).
           rewrite !Znth_cons in Hentries by lia.
           replace (k + 1 - 1) with k in Hentries by lia.
           exact Hentries.
Qed.

Theorem valid_factor_table_exact_trace_enumeration
    m pr pe product :
  ValidFactorTable m pr pe ->
  In product (enumerated_products pr pe) <->
  exists exponents,
    ExponentTrace pr pe exponents product /\
    Zlength exponents = Zlength pr.
Proof.
  intros Hvalid.
  pose proof Hvalid as (Hlen & _).
  pose proof (valid_factor_table_exponents_nonnegative _ _ _ Hvalid)
    as Hnonnegative.
  rewrite enumerated_products_trace by (assumption || exact Hnonnegative).
  split.
  - intros [exponents Htrace].
    exists exponents; split; [exact Htrace|].
    destruct (exponent_trace_lengths _ _ _ _ Htrace) as [_ Hlength].
    rewrite !Zlength_correct; lia.
  - intros [exponents [Htrace _]].
    exists exponents; exact Htrace.
Qed.

Lemma sum_nat_range_as_seq first count f :
  sum_nat_range first count f =
  fold_right Z.add 0 (map f (seq first count)).
Proof.
  revert first.
  induction count as [| count IH]; intros first; simpl.
  - reflexivity.
  - rewrite IH; reflexivity.
Qed.

Lemma fold_right_add_acc values accumulator :
  fold_right Z.add accumulator values =
  fold_right Z.add 0 values + accumulator.
Proof.
  induction values as [| value values IH]; simpl; [ring|].
  rewrite IH; ring.
Qed.

Lemma fold_right_concat_map {A : Type}
    (blocks : list A) (f : A -> list Z) :
  fold_right Z.add 0 (concat (map f blocks)) =
  fold_right Z.add 0
    (map (fun a => fold_right Z.add 0 (f a)) blocks).
Proof.
  induction blocks as [| a blocks IH]; simpl; [reflexivity|].
  rewrite fold_right_app, IH, fold_right_add_acc; reflexivity.
Qed.

Lemma walk_suffix_lists_exact_terms pr pe x d :
  walk_suffix_lists pr pe x d =
  fold_right Z.add 0 (enumerated_walk_terms pr pe x d).
Proof.
  revert pe d.
  induction pr as [| p pr IH]; intros pe d.
  - destruct pe; simpl; ring.
  - destruct pe as [| maximum pe].
    + simpl; ring.
    + unfold walk_suffix_lists; fold walk_suffix_lists.
      rewrite sum_nat_range_as_seq.
      unfold enumerated_walk_terms; fold enumerated_walk_terms.
      rewrite fold_right_concat_map.
      apply f_equal.
      apply map_ext_in.
      intros n Hn.
      apply IH.
Qed.

Lemma enumerated_walk_terms_as_products pr pe x d :
  enumerated_walk_terms pr pe x d =
  map (fun product => CycleTerm x (d * product))
    (enumerated_products pr pe).
Proof.
  revert pe d.
  induction pr as [| p pr IH]; intros pe d.
  - destruct pe; simpl.
    + replace (d * 1) with d by ring; reflexivity.
    + replace (d * 1) with d by ring; reflexivity.
  - destruct pe as [| maximum pe].
    + simpl; replace (d * 1) with d by ring; reflexivity.
    + unfold enumerated_walk_terms, enumerated_products.
      fold enumerated_walk_terms enumerated_products.
      rewrite concat_map, !map_map.
      apply f_equal.
      apply map_ext_in.
      intros n Hn.
      rewrite IH, map_map.
      apply map_ext.
      intros product.
      f_equal; ring.
Qed.

Theorem walk_suffix_exact_divisor_cycle_sum pr pe x i d :
  WalkSuffix pr pe x i d =
  fold_right Z.add 0
    (map (fun product => CycleTerm x (d * product))
      (enumerated_products
        (skipn (Z.to_nat i) pr) (skipn (Z.to_nat i) pe))).
Proof.
  unfold WalkSuffix.
  rewrite walk_suffix_lists_exact_terms.
  rewrite enumerated_walk_terms_as_products.
  reflexivity.
Qed.

Lemma cycle_term_one x : CycleTerm x 1 = 0.
Proof. unfold CycleTerm; now rewrite Z.eqb_refl. Qed.

Lemma fold_filter_cycle_term_one x products :
  fold_right Z.add 0 (map (CycleTerm x) products) =
  fold_right Z.add 0
    (map (CycleTerm x)
      (filter (fun d => negb (Z.eqb d 1)) products)).
Proof.
  induction products as [| d products IH]; simpl; [reflexivity|].
  destruct (Z.eqb d 1) eqn:Hd.
  - apply Z.eqb_eq in Hd; subst d.
    rewrite cycle_term_one, IH; reflexivity.
  - simpl; rewrite IH; reflexivity.
Qed.

Theorem walk_suffix_zero_is_nonunit_cycle_sum pr pe x :
  WalkSuffix pr pe x 0 1 = NonUnitDivisorCycleSum pr pe x.
Proof.
  rewrite walk_suffix_exact_divisor_cycle_sum.
  unfold NonUnitDivisorCycleSum.
  change
    (fold_right Z.add 0
       (map (fun product => CycleTerm x (1 * product))
         (enumerated_products pr pe)) =
     fold_right Z.add 0
       (map (CycleTerm x)
         (filter (fun d => negb (Z.eqb d 1))
           (enumerated_products pr pe)))).
  replace
    (map (fun product => CycleTerm x (1 * product))
      (enumerated_products pr pe))
    with (map (CycleTerm x) (enumerated_products pr pe)).
  2: { apply map_ext; intros product; f_equal; ring. }
  apply fold_filter_cycle_term_one.
Qed.

Corollary walk_budget_nonunit_cycle_interface m pr pe x :
  WalkBudget m 0 (WalkSuffix pr pe x 0 1) <->
  0 <= NonUnitDivisorCycleSum pr pe x /\
  NonUnitDivisorCycleSum pr pe x <= m.
Proof.
  rewrite walk_suffix_zero_is_nonunit_cycle_sum.
  unfold WalkBudget; lia.
Qed.

(** A durable choice history for the existing forward [PrefixSelected]
    relation. *)
Inductive PrefixSelectedTrace (pr pe : list Z) :
    Z -> list Z -> Z -> Prop :=
| prefix_selected_trace_zero :
    PrefixSelectedTrace pr pe 0 [] 1
| prefix_selected_trace_step : forall i exponents d exponent,
    PrefixSelectedTrace pr pe i exponents d ->
    0 <= i < Zlength pr ->
    0 <= exponent <= Znth i pe 0 ->
    PrefixSelectedTrace pr pe (i + 1) (exponents ++ [exponent])
      (d * Z.pow (Znth i pr 0) exponent).

Lemma prefix_selected_trace_forget pr pe i exponents d :
  PrefixSelectedTrace pr pe i exponents d ->
  PrefixSelected pr pe i d.
Proof.
  intros Htrace; induction Htrace.
  - constructor.
  - econstructor; eauto.
Qed.

Lemma prefix_selected_has_trace pr pe i d :
  PrefixSelected pr pe i d ->
  exists exponents, PrefixSelectedTrace pr pe i exponents d.
Proof.
  intros Hselected; induction Hselected.
  - exists []; constructor.
  - destruct IHHselected as [exponents Htrace].
    exists (exponents ++ [e]).
    econstructor; eauto.
Qed.

Lemma prefix_selected_trace_length pr pe i exponents d :
  PrefixSelectedTrace pr pe i exponents d ->
  Zlength exponents = i.
Proof.
  intros Htrace; induction Htrace.
  - rewrite Zlength_nil; reflexivity.
  - rewrite Zlength_app_cons, IHHtrace; reflexivity.
Qed.

Theorem prefix_selected_exact_trace_interface pr pe i d :
  PrefixSelected pr pe i d <->
  exists exponents,
    PrefixSelectedTrace pr pe i exponents d /\ Zlength exponents = i.
Proof.
  split.
  - intros Hselected.
    destruct (prefix_selected_has_trace _ _ _ _ Hselected)
      as [exponents Htrace].
    exists exponents; split; [exact Htrace|].
    now apply prefix_selected_trace_length with pr pe d.
  - intros [exponents [Htrace _]].
    now apply prefix_selected_trace_forget with exponents.
Qed.
End P090_DivisorEnumeration.
Export P090_DivisorEnumeration.

Module P090_DivisorCompleteness.

Import ListNotations.
Local Open Scope Z_scope.
Import P090_OrderFoundations.P090_OrderFoundations.

(** A recursive form of the prime-power table facts needed by unique
    factorization.  The last conjunct is precisely the coprimality boundary
    between the head prime and the remaining table product. *)
Inductive CanonicalFactorTable : list Z -> list Z -> Prop :=
| canonical_factor_table_nil :
    CanonicalFactorTable [] []
| canonical_factor_table_cons : forall p pr exponent pe,
    prime p ->
    1 <= exponent ->
    CanonicalFactorTable pr pe ->
    ~ (p | factor_product pr pe) ->
    CanonicalFactorTable (p :: pr) (exponent :: pe).

Lemma smaller_prime_not_divide_factor_product p pr pe :
  prime p ->
  Zlength pr = Zlength pe ->
  (forall k, 0 <= k < Zlength pr ->
     prime (Znth k pr 0) /\
     1 <= Znth k pe 0 /\
     p < Znth k pr 0) ->
  ~ (p | factor_product pr pe).
Proof.
  intros Hp.
  revert pe.
  induction pr as [| q pr IH]; intros pe Hlen Hentries Hdivide.
  - destruct pe; simpl in Hdivide.
    + pose proof (prime_ge_2 p Hp).
      assert (p <= 1) by (eapply Z.divide_pos_le; eauto; lia).
      lia.
    + pose proof (Zlength_nonneg pe).
      rewrite Zlength_nil, Zlength_cons in Hlen; lia.
  - destruct pe as [| exponent pe].
    + pose proof (Zlength_nonneg pr).
      rewrite Zlength_nil, Zlength_cons in Hlen; lia.
    + simpl factor_product in Hdivide.
      destruct (prime_mult p Hp _ _ Hdivide) as [Hhead | Htail].
      * specialize (Hentries 0 ltac:(
          rewrite Zlength_cons; pose proof (Zlength_nonneg pr); lia)).
        rewrite !Znth0_cons in Hentries.
        destruct Hentries as [Hqprime [Hexponent Hpq]].
        pose proof (prime_power_prime p q exponent ltac:(lia)
                      Hp Hqprime Hhead).
        lia.
      * apply (IH pe).
        -- rewrite !Zlength_cons in Hlen; lia.
        -- intros k Hk.
           specialize (Hentries (k + 1) ltac:(
             rewrite Zlength_cons; lia)).
           rewrite !Znth_cons in Hentries by lia.
           replace (k + 1 - 1) with k in Hentries by lia.
           exact Hentries.
        -- exact Htail.
Qed.

Lemma valid_factor_table_canonical m pr pe :
  ValidFactorTable m pr pe -> CanonicalFactorTable pr pe.
Proof.
  intros (Hlen & _ & _ & Hentries & Horder).
  revert pe Hlen Hentries Horder.
  induction pr as [| p pr IH]; intros pe Hlen Hentries Horder.
  - destruct pe.
    + constructor.
    + pose proof (Zlength_nonneg pe).
      rewrite Zlength_nil, Zlength_cons in Hlen; lia.
  - destruct pe as [| exponent pe].
    + pose proof (Zlength_nonneg pr).
      rewrite Zlength_nil, Zlength_cons in Hlen; lia.
    + assert (Hhead : IsPrime p /\ 1 <= exponent).
      { specialize (Hentries 0 ltac:(
          rewrite Zlength_cons; pose proof (Zlength_nonneg pr); lia)).
        rewrite !Znth0_cons in Hentries; exact Hentries. }
      destruct Hhead as [Hp Hexp].
      constructor.
      * apply is_prime_iff_std; exact Hp.
      * exact Hexp.
      * apply IH.
        -- rewrite !Zlength_cons in Hlen; lia.
        -- intros k Hk.
           specialize (Hentries (k + 1) ltac:(
             rewrite Zlength_cons; lia)).
           rewrite !Znth_cons in Hentries by lia.
           replace (k + 1 - 1) with k in Hentries by lia.
           exact Hentries.
        -- intros j k Hj.
           specialize (Horder (j + 1) (k + 1) ltac:(
             rewrite Zlength_cons; lia)).
           rewrite !Znth_cons in Horder by lia.
           replace (j + 1 - 1) with j in Horder by lia.
           replace (k + 1 - 1) with k in Horder by lia.
           exact Horder.
      * apply smaller_prime_not_divide_factor_product.
        -- apply is_prime_iff_std; exact Hp.
        -- rewrite !Zlength_cons in Hlen; lia.
        -- intros k Hk.
           specialize (Hentries (k + 1) ltac:(
             rewrite Zlength_cons; lia)).
           specialize (Horder 0 (k + 1) ltac:(
             rewrite Zlength_cons; lia)).
           rewrite Znth0_cons in Horder.
           rewrite !Znth_cons in Hentries by lia.
           rewrite Znth_cons in Horder by lia.
           replace (k + 1 - 1) with k in Hentries by lia.
           replace (k + 1 - 1) with k in Horder by lia.
           destruct Hentries as [Hq He].
           split; [apply is_prime_iff_std; exact Hq|].
           split; assumption.
Qed.

(** Strip from a divisor exactly the power of [p] available in the ambient
    factor [p^maximum * rest]. *)
Lemma extract_prime_power_from_divisor p maximum rest divisor :
  prime p ->
  0 <= maximum ->
  0 < rest ->
  ~ (p | rest) ->
  0 < divisor ->
  (divisor | Z.pow p maximum * rest) ->
  exists exponent residual,
    0 <= exponent <= maximum /\
    0 < residual /\
    ~ (p | residual) /\
    (residual | rest) /\
    divisor = Z.pow p exponent * residual.
Proof.
  intros Hp Hmaximum.
  revert divisor.
  pattern maximum.
  apply natlike_ind.
  - intros divisor Hrest Hprest Hdivisor Hdivide.
    rewrite Z.pow_0_r, Z.mul_1_l in Hdivide.
    exists 0, divisor.
    repeat split; try lia; try assumption.
    + intro Hpdivisor.
      apply Hprest.
      eapply Z.divide_trans; eauto.
  - intros n Hn IH divisor Hrest Hprest Hdivisor Hdivide.
    rewrite Z.pow_succ_r in Hdivide by exact Hn.
    replace (p * Z.pow p n * rest) with
      (p * (Z.pow p n * rest)) in Hdivide by ring.
    destruct (Zdivide_dec p divisor) as [Hpdivisor | Hnotdivide].
    + destruct Hpdivisor as [quotient Hquotient].
      assert (Hquotient_pos : 0 < quotient) by
        (pose proof (prime_ge_2 p Hp); nia).
      assert (Hquotient_divides :
        (quotient | Z.pow p n * rest)).
      { destruct Hdivide as [multiplier Hproduct].
        exists multiplier.
        apply (proj1 (Z.mul_cancel_l _ _ p ltac:(
          pose proof (prime_ge_2 p Hp); lia))).
        rewrite Hproduct, Hquotient; ring. }
      destruct (IH quotient Hrest Hprest Hquotient_pos Hquotient_divides)
        as [exponent [residual
          [Hexponent [Hresidual [Hpresidual [Hresdiv Hfactor]]]]]].
      exists (exponent + 1), residual.
      repeat split; try lia; try assumption.
      rewrite Hquotient, Hfactor, Z.pow_add_r by lia.
      rewrite Z.pow_1_r; ring.
    + assert (Hcoprime : rel_prime divisor p).
      { apply rel_prime_sym, prime_rel_prime; assumption. }
      assert (Hlower_divide : (divisor | Z.pow p n * rest)).
      { eapply Gauss; eauto. }
      destruct (IH divisor Hrest Hprest Hdivisor Hlower_divide)
        as [exponent [residual
          [Hexponent [Hresidual [Hpresidual [Hresdiv Hfactor]]]]]].
      exists exponent, residual.
      repeat split; try lia; assumption.
  - exact Hmaximum.
Qed.

Lemma canonical_factor_product_positive pr pe :
  CanonicalFactorTable pr pe -> 0 < factor_product pr pe.
Proof.
  intros Htable; induction Htable; simpl.
  - lia.
  - pose proof (prime_ge_2 p H).
    pose proof (Z.pow_pos_nonneg p exponent ltac:(lia) ltac:(lia)).
    nia.
Qed.

Lemma canonical_divisor_complete pr pe divisor :
  CanonicalFactorTable pr pe ->
  0 < divisor ->
  (divisor | factor_product pr pe) ->
  exists exponents, ExponentTrace pr pe exponents divisor.
Proof.
  intros Htable; revert divisor.
  induction Htable as
      [| p pr exponent pe Hp Hexp Htable IH Hnotdivide];
    intros divisor Hdivisor Hdivide.
  - simpl in Hdivide.
    assert (divisor <= 1) by (eapply Z.divide_pos_le; eauto; lia).
    assert (divisor = 1) by lia; subst.
    exists []; constructor.
  - simpl factor_product in Hdivide.
    pose proof (canonical_factor_product_positive _ _ Htable) as Hrest.
    destruct (extract_prime_power_from_divisor
                p exponent (factor_product pr pe) divisor
                Hp ltac:(lia) Hrest Hnotdivide Hdivisor Hdivide)
      as [chosen [residual
        [Hchosen [Hresidual [Hpresidual [Hresdiv Hfactor]]]]]].
    destruct (IH residual Hresidual Hresdiv)
      as [tail_exponents Htail].
    exists (chosen :: tail_exponents).
    rewrite Hfactor.
    constructor; assumption.
Qed.

Theorem valid_factor_table_divisor_complete m pr pe divisor :
  ValidFactorTable m pr pe ->
  0 < divisor ->
  (divisor | m) ->
  exists exponents, ExponentTrace pr pe exponents divisor.
Proof.
  intros Hvalid Hdivisor Hdivide.
  pose proof Hvalid as Hvalid_canonical.
  destruct Hvalid as (_ & _ & Hproduct & Hrest).
  apply canonical_divisor_complete.
  - exact (valid_factor_table_canonical m pr pe Hvalid_canonical).
  - exact Hdivisor.
  - rewrite <- Hproduct; exact Hdivide.
Qed.

Lemma prime_power_residual_unique p e f a b :
  prime p ->
  0 <= e -> 0 <= f ->
  0 < a -> 0 < b ->
  ~ (p | a) -> ~ (p | b) ->
  Z.pow p e * a = Z.pow p f * b ->
  e = f /\ a = b.
Proof.
  intros Hp He Hf Ha Hb Hpa Hpb Heq.
  pose proof (prime_ge_2 p Hp) as Hp2.
  destruct (Z.lt_trichotomy e f) as [Hef | [-> | Hfe]].
  - exfalso; apply Hpa.
    assert (Hdiff : 0 < f - e) by lia.
    replace f with (e + (f - e)) in Heq by lia.
    rewrite (Z.pow_add_r p e (f - e)) in Heq by lia.
    replace (Z.pow p e * Z.pow p (f - e) * b) with
      (Z.pow p e * (Z.pow p (f - e) * b)) in Heq by ring.
    apply (proj1 (Z.mul_cancel_l _ _ (Z.pow p e) ltac:(
      pose proof (Z.pow_pos_nonneg p e ltac:(lia) He); lia))) in Heq.
    rewrite Heq.
    apply Z.divide_mul_l.
    apply Zpower_divide; exact Hdiff.
  - split; [reflexivity|].
    apply (proj1 (Z.mul_cancel_l _ _ (Z.pow p f) ltac:(
      pose proof (Z.pow_pos_nonneg p f ltac:(lia) Hf); lia))).
    exact Heq.
  - exfalso; apply Hpb.
    assert (Hdiff : 0 < e - f) by lia.
    replace e with (f + (e - f)) in Heq by lia.
    rewrite (Z.pow_add_r p f (e - f)) in Heq by lia.
    replace (Z.pow p f * Z.pow p (e - f) * a) with
      (Z.pow p f * (Z.pow p (e - f) * a)) in Heq by ring.
    apply (proj1 (Z.mul_cancel_l _ _ (Z.pow p f) ltac:(
      pose proof (Z.pow_pos_nonneg p f ltac:(lia) Hf); lia))) in Heq.
    rewrite <- Heq.
    apply Z.divide_mul_l.
    apply Zpower_divide; exact Hdiff.
Qed.

Lemma exponent_trace_positive pr pe exponents product :
  CanonicalFactorTable pr pe ->
  ExponentTrace pr pe exponents product ->
  0 < product.
Proof.
  intros Htable Htrace.
  induction Htrace; inversion Htable; subst; simpl.
  - lia.
  - pose proof (prime_ge_2 p H4).
    pose proof (Z.pow_pos_nonneg p exponent ltac:(lia) ltac:(lia)).
    specialize (IHHtrace H6); nia.
Qed.

Lemma exponent_trace_divides_factor_product pr pe exponents product :
  CanonicalFactorTable pr pe ->
  ExponentTrace pr pe exponents product ->
  (product | factor_product pr pe).
Proof.
  intros Htable Htrace.
  induction Htrace; inversion Htable; subst; simpl.
  - apply Z.divide_refl.
  - specialize (IHHtrace H6).
    destruct IHHtrace as [tail_multiplier Htail].
    exists (Z.pow p (maximum - exponent) * tail_multiplier).
    assert (Hpow : Z.pow p maximum =
                   Z.pow p exponent * Z.pow p (maximum - exponent)).
    { rewrite <- Z.pow_add_r by lia.
      f_equal; lia. }
    rewrite Htail, Hpow.
    ring.
Qed.

Lemma exponent_trace_cons_inv p pr maximum pe exponents product :
  ExponentTrace (p :: pr) (maximum :: pe) exponents product ->
  exists exponent tail_exponents tail_product,
    exponents = exponent :: tail_exponents /\
    product = Z.pow p exponent * tail_product /\
    0 <= exponent <= maximum /\
    ExponentTrace pr pe tail_exponents tail_product.
Proof.
  intros Htrace.
  inversion Htrace as
      [| p0 pr0 maximum0 pe0 exponent tail_exponents tail_product
          Hbound Htail]; subst.
  exists exponent, tail_exponents, tail_product.
  split; [reflexivity|].
  split; [reflexivity|].
  split; assumption.
Qed.

Lemma canonical_exponent_trace_unique pr pe exponents1 exponents2 product :
  CanonicalFactorTable pr pe ->
  ExponentTrace pr pe exponents1 product ->
  ExponentTrace pr pe exponents2 product ->
  exponents1 = exponents2.
Proof.
  intros Htable; revert exponents1 exponents2 product.
  induction Htable as
      [| p pr maximum pe Hp Hmaximum Htail IH Hp_rest];
    intros exponents1 exponents2 product Htrace1 Htrace2.
  - inversion Htrace1; inversion Htrace2; reflexivity.
  - destruct (exponent_trace_cons_inv _ _ _ _ _ _ Htrace1)
      as [exponent1 [tail_exponents1 [tail_product1
        [Hexponents1 [Hproduct1 [Hbound1 Htail1]]]]]].
    destruct (exponent_trace_cons_inv _ _ _ _ _ _ Htrace2)
      as [exponent2 [tail_exponents2 [tail_product2
        [Hexponents2 [Hproduct2 [Hbound2 Htail2]]]]]].
    subst exponents1 exponents2.
    assert (Htail1_pos : 0 < tail_product1).
    { eapply exponent_trace_positive; eauto. }
    assert (Htail2_pos : 0 < tail_product2).
    { eapply exponent_trace_positive; eauto. }
    assert (Hp_tail1 : ~ (p | tail_product1)).
    { intro Hdivide.
      apply Hp_rest.
      eapply Z.divide_trans; [exact Hdivide|].
      eapply exponent_trace_divides_factor_product; eauto. }
    assert (Hp_tail2 : ~ (p | tail_product2)).
    { intro Hdivide.
      apply Hp_rest.
      eapply Z.divide_trans; [exact Hdivide|].
      eapply exponent_trace_divides_factor_product; eauto. }
    assert (Hproducts :
      Z.pow p exponent1 * tail_product1 =
      Z.pow p exponent2 * tail_product2) by
      (rewrite <- Hproduct1, <- Hproduct2; reflexivity).
    destruct (prime_power_residual_unique
                p exponent1 exponent2 tail_product1 tail_product2
                Hp ltac:(lia) ltac:(lia)
                Htail1_pos Htail2_pos Hp_tail1 Hp_tail2 Hproducts)
      as [Hexponent Hproduct].
    subst exponent2 tail_product2.
    f_equal.
    eapply IH; eauto.
Qed.

Theorem valid_factor_table_exponent_vector_unique
    m pr pe exponents1 exponents2 product :
  ValidFactorTable m pr pe ->
  ExponentTrace pr pe exponents1 product ->
  ExponentTrace pr pe exponents2 product ->
  exponents1 = exponents2.
Proof.
  intros Hvalid.
  apply canonical_exponent_trace_unique.
  now apply valid_factor_table_canonical with m.
Qed.

Fixpoint enumerated_exponent_vectors (pe : list Z) : list (list Z) :=
  match pe with
  | [] => [[]]
  | maximum :: pe' =>
      concat
        (map
          (fun n => map (cons (Z.of_nat n))
            (enumerated_exponent_vectors pe'))
          (seq 0 (S (Z.to_nat maximum))))
  end.

Fixpoint exponent_vector_product (pr exponents : list Z) : Z :=
  match pr, exponents with
  | p :: pr', exponent :: exponents' =>
      Z.pow p exponent * exponent_vector_product pr' exponents'
  | _, _ => 1
  end.

Lemma map_injective_nodup {A B : Type} (f : A -> B) xs :
  (forall x y, In x xs -> In y xs -> f x = f y -> x = y) ->
  NoDup xs -> NoDup (map f xs).
Proof.
  intros Hinjective Hnodup; induction Hnodup; simpl; constructor.
  - intros Hin.
    apply in_map_iff in Hin.
    destruct Hin as [y [Heq Hin]].
    assert (y = x) by
      (apply Hinjective; [right; exact Hin|left; reflexivity|exact Heq]).
    subst y; contradiction.
  - apply IHHnodup.
    intros x0 y Hx0 Hy Heq.
    apply Hinjective; [right|right|]; assumption.
Qed.

Lemma tagged_vectors_nodup tags tails :
  NoDup tags -> NoDup tails ->
  NoDup
    (concat (map
      (fun tag => map (cons (Z.of_nat tag)) tails) tags)).
Proof.
  intros Htags Htails; induction Htags; simpl; [constructor|].
  apply NoDup_app.
  - apply map_injective_nodup;
      [intros tail1 tail2 _ _ Heq; inversion Heq; reflexivity|].
    exact Htails.
  - apply IHHtags.
  - intros vector Hin_head Hin_tail.
    apply in_map_iff in Hin_head.
    destruct Hin_head as [tail [Hvector _]].
    subst vector.
    apply in_concat in Hin_tail.
    destruct Hin_tail as [block [Hblock Hinblock]].
    apply in_map_iff in Hblock.
    destruct Hblock as [tag [Hblock Htag]].
    subst block.
    apply in_map_iff in Hinblock.
    destruct Hinblock as [tail' [Heq _]].
    inversion Heq; subst.
    assert (tag = x) by (apply Nat2Z.inj; assumption).
    subst tag; contradiction.
Qed.

Lemma enumerated_exponent_vectors_nodup pe :
  NoDup (enumerated_exponent_vectors pe).
Proof.
  induction pe as [| maximum pe IH].
  - simpl; constructor; [simpl; tauto|constructor].
  - unfold enumerated_exponent_vectors; fold enumerated_exponent_vectors.
    apply tagged_vectors_nodup; [apply seq_NoDup|exact IH].
Qed.

Lemma enumerated_products_as_vector_map pr pe :
  Zlength pr = Zlength pe ->
  enumerated_products pr pe =
  map (exponent_vector_product pr) (enumerated_exponent_vectors pe).
Proof.
  revert pe.
  induction pr as [| p pr IH]; intros pe Hlen.
  - destruct pe; simpl; [reflexivity|].
    pose proof (Zlength_nonneg pe).
    rewrite Zlength_nil, Zlength_cons in Hlen; lia.
  - destruct pe as [| maximum pe].
    + pose proof (Zlength_nonneg pr).
      rewrite Zlength_nil, Zlength_cons in Hlen; lia.
    + assert (Htail_len : Zlength pr = Zlength pe).
      { rewrite !Zlength_cons in Hlen; lia. }
      unfold enumerated_products, enumerated_exponent_vectors.
      fold enumerated_products enumerated_exponent_vectors.
      rewrite concat_map, !map_map.
      apply f_equal.
      apply map_ext_in; intros n Hn.
      rewrite IH by exact Htail_len.
      rewrite !map_map.
      apply map_ext; intros tail; reflexivity.
Qed.

Lemma enumerated_vector_has_trace pr pe exponents :
  Zlength pr = Zlength pe ->
  Forall (fun maximum => 0 <= maximum) pe ->
  In exponents (enumerated_exponent_vectors pe) ->
  ExponentTrace pr pe exponents (exponent_vector_product pr exponents).
Proof.
  revert pe exponents.
  induction pr as [| p pr IH]; intros pe exponents Hlen Hnonnegative Hin.
  - destruct pe.
    + simpl in Hin.
      destruct Hin as [Hexponents | []].
      subst exponents; simpl; constructor.
    + pose proof (Zlength_nonneg pe).
      rewrite Zlength_nil, Zlength_cons in Hlen; lia.
  - destruct pe as [| maximum pe].
    + pose proof (Zlength_nonneg pr).
      rewrite Zlength_nil, Zlength_cons in Hlen; lia.
    + inversion Hnonnegative as [| maximum0 pe0 Hmaximum Htail]; subst.
      unfold enumerated_exponent_vectors in Hin;
        fold enumerated_exponent_vectors in Hin.
      apply in_concat in Hin.
      destruct Hin as [block [Hblock Hin]].
      apply in_map_iff in Hblock.
      destruct Hblock as [n [Hblock Hn]]; subst block.
      apply in_map_iff in Hin.
      destruct Hin as [tail [Hexponents Htailin]]; subst exponents.
      simpl exponent_vector_product.
      constructor.
      * apply in_seq in Hn; destruct Hn as [_ Hn].
        split; [lia|].
        assert (Z.of_nat n < Z.of_nat (S (Z.to_nat maximum)))
          by (apply Nat2Z.inj_lt; exact Hn).
        rewrite Nat2Z.inj_succ, Z2Nat.id in H by lia.
        lia.
      * apply (IH pe tail).
        -- rewrite !Zlength_cons in Hlen; lia.
        -- exact Htail.
        -- exact Htailin.
Qed.

Theorem valid_factor_table_enumerated_products_nodup m pr pe :
  ValidFactorTable m pr pe -> NoDup (enumerated_products pr pe).
Proof.
  intros Hvalid.
  destruct Hvalid as (Hlen & Hrest).
  rewrite enumerated_products_as_vector_map by exact Hlen.
  apply map_injective_nodup.
  - intros exponents1 exponents2 Hin1 Hin2 Heq.
    eapply valid_factor_table_exponent_vector_unique.
    + split; [exact Hlen|exact Hrest].
    + apply enumerated_vector_has_trace.
      * exact Hlen.
      * apply valid_factor_table_exponents_nonnegative with m pr.
        split; [exact Hlen|exact Hrest].
      * exact Hin1.
    + rewrite Heq.
      apply enumerated_vector_has_trace.
      * exact Hlen.
      * apply valid_factor_table_exponents_nonnegative with m pr.
        split; [exact Hlen|exact Hrest].
      * exact Hin2.
  - apply enumerated_exponent_vectors_nodup.
Qed.

Theorem valid_factor_table_exact_positive_divisor_bijection
    m pr pe divisor :
  ValidFactorTable m pr pe ->
  (In divisor (enumerated_products pr pe) <->
   0 < divisor /\ (divisor | m)).
Proof.
  intros Hvalid; split.
  - intros Hin.
    pose proof Hvalid as Hcanonical.
    apply (proj1
      (valid_factor_table_exact_trace_enumeration
        m pr pe divisor Hvalid)) in Hin.
    destruct Hin as [exponents [Htrace _]].
    split.
    + eapply exponent_trace_positive.
      * exact (valid_factor_table_canonical m pr pe Hcanonical).
      * exact Htrace.
    + destruct Hvalid as (_ & _ & Hproduct & Hrest).
      rewrite Hproduct.
      eapply exponent_trace_divides_factor_product.
      * exact (valid_factor_table_canonical m pr pe Hcanonical).
      * exact Htrace.
  - intros [Hpositive Hdivide].
    apply (proj2
      (valid_factor_table_exact_trace_enumeration
        m pr pe divisor Hvalid)).
    destruct (valid_factor_table_divisor_complete
                m pr pe divisor Hvalid Hpositive Hdivide)
      as [exponents Htrace].
    exists exponents; split; [exact Htrace|].
    destruct (exponent_trace_lengths _ _ _ _ Htrace) as [_ Hlength].
    rewrite !Zlength_correct; lia.
Qed.
End P090_DivisorCompleteness.
Export P090_DivisorCompleteness.

Module P090_OrderInputBridge.

Local Open Scope Z_scope.

Module ETI := euler_theorem_inverse_lib.

Import P090_OrderExcess.P090_OrderExcess.
Import P090_OrderExact.P090_OrderExact.

(** The search proof does not need an already-established [OrderInput].
    A positive terminal exponent whose power is one is enough.  Keeping this
    constructor separate avoids assuming [Ord | EulerPhi] in order to prove
    that very fact. *)
Lemma ord_search_exact_from_terminal
    (x modulus phi : Z) :
  1 < modulus ->
  phi = EulerPhi modulus ->
  0 < phi ->
  Z.pow x phi mod modulus = 1 ->
  1 <= Ord x modulus <= phi /\
  Z.pow x (Ord x modulus) mod modulus = 1 /\
  (forall candidate,
      1 <= candidate < Ord x modulus ->
      Z.pow x candidate mod modulus <> 1).
Proof.
  intros Hmodulus Hphi Hphi_positive Hterminal.
  unfold Ord.
  assert (Hmodulus_neq : Z.eqb modulus 1 = false).
  { apply Z.eqb_neq; lia. }
  rewrite Hmodulus_neq.
  rewrite <- Hphi.
  remember (Z.to_nat phi) as count eqn:Hcount.
  assert (Hcount_value : Z.of_nat count = phi).
  { rewrite Hcount; apply Z2Nat.id; lia. }
  destruct count as [| fuel].
  - cbn in Hcount_value; lia.
  - assert (Hterminal_exponent : 1 + Z.of_nat fuel = phi).
    { rewrite Nat2Z.inj_succ in Hcount_value; lia. }
    assert (Hterminal_reduced :
      Z.pow (x mod modulus) (1 + Z.of_nat fuel) mod modulus = 1).
    {
      rewrite Hterminal_exponent.
      rewrite pow_mod_base by lia.
      exact Hterminal.
    }
    destruct
      (order_search_terminal_spec
         (x mod modulus) modulus 1 fuel ltac:(lia) Hterminal_reduced)
      as [Hbounds Hsound].
    split.
    + rewrite Hterminal_exponent in Hbounds; exact Hbounds.
    + split.
      * rewrite <-
          (pow_mod_base x modulus
             (order_search (x mod modulus) modulus 1 (S fuel)))
          by lia.
        exact Hsound.
      * intros candidate Hcandidate Hcandidate_power.
        eapply
          (order_search_minimal
             (x mod modulus) modulus 1 (S fuel) candidate);
          try eassumption; try lia.
        rewrite pow_mod_base by lia.
        exact Hcandidate_power.
Qed.

Lemma reduced_base_coprime
    (x modulus : Z) :
  modulus <> 0 ->
  Z.gcd x modulus = 1 ->
  Z.gcd (x mod modulus) modulus = 1.
Proof.
  intros Hmodulus Hgcd.
  rewrite Z.gcd_mod by exact Hmodulus.
  rewrite Z.gcd_comm.
  exact Hgcd.
Qed.

Lemma reduced_base_positive
    (x modulus : Z) :
  1 < modulus ->
  Z.gcd x modulus = 1 ->
  0 < x mod modulus < modulus.
Proof.
  intros Hmodulus Hgcd.
  pose proof (Z.mod_pos_bound x modulus ltac:(lia)) as Hbounds.
  assert (Hreduced_gcd : Z.gcd (x mod modulus) modulus = 1).
  { apply reduced_base_coprime; lia. }
  split; [| lia].
  destruct (Z.eq_dec (x mod modulus) 0) as [Hzero | Hnonzero]; [| lia].
  rewrite Hzero, Z.gcd_0_l, Z.abs_eq in Hreduced_gcd by lia.
  lia.
Qed.

Lemma euler_power_for_case_phi
    (x modulus : Z) :
  1 < modulus ->
  Z.gcd x modulus = 1 ->
  Z.pow x (EulerPhi modulus) mod modulus = 1.
Proof.
  intros Hmodulus Hgcd.
  pose proof (reduced_base_positive x modulus Hmodulus Hgcd)
    as Hreduced_bounds.
  pose proof (reduced_base_coprime x modulus ltac:(lia) Hgcd)
    as Hreduced_gcd.
  pose proof
    (ETI.euler_power_totient_mod__inverse_final_result
       (x mod modulus) modulus
       (proj1 Hreduced_bounds) (proj2 Hreduced_bounds)
       ltac:(lia) Hreduced_gcd) as Heuler.
  pose proof (euler_phi_nonnegative modulus) as Hphi_nonnegative.
  rewrite <- euler_phi_bridge in Heuler.
  rewrite pow_mod_base in Heuler by lia.
  exact Heuler.
Qed.

(** This is the non-circular producer contract needed by every caller of the
    C [order] helper. *)
Theorem coprime_implies_order_input
    (x modulus : Z) :
  1 < modulus ->
  Z.gcd x modulus = 1 ->
  OrderInput x modulus (EulerPhi modulus).
Proof.
  intros Hmodulus Hgcd.
  pose proof (euler_phi_positive_bounded modulus ltac:(lia))
    as Hphi_bounds.
  pose proof (euler_power_for_case_phi x modulus Hmodulus Hgcd)
    as Heuler.
  destruct
    (ord_search_exact_from_terminal
       x modulus (EulerPhi modulus)
       Hmodulus eq_refl ltac:(lia) Heuler)
    as [Hord_bounds [Hord_power Hminimal]].
  assert (Hord_divides :
      (Ord x modulus | EulerPhi modulus)).
  {
    eapply minimal_success_divides;
      try exact Hmodulus;
      try exact (proj1 Hord_bounds);
      try exact Hord_power;
      try exact Hminimal;
      try exact Heuler;
      lia.
  }
  unfold OrderInput.
  repeat split; try assumption; try reflexivity; lia.
Qed.

Lemma ord_reduced_base
    (x modulus : Z) :
  modulus <> 0 ->
  Ord (x mod modulus) modulus = Ord x modulus.
Proof.
  intros Hmodulus.
  unfold Ord.
  destruct (Z.eqb modulus 1); [reflexivity |].
  rewrite Z.mod_mod by exact Hmodulus.
  reflexivity.
Qed.

Corollary coprime_implies_reduced_order_input
    (x modulus : Z) :
  1 < modulus ->
  Z.gcd x modulus = 1 ->
  OrderInput (x mod modulus) modulus (EulerPhi modulus).
Proof.
  intros Hmodulus Hgcd.
  apply coprime_implies_order_input; [exact Hmodulus |].
  apply reduced_base_coprime; lia.
Qed.

Theorem coprime_implies_exact_order_criterion
    (x modulus : Z) :
  1 < modulus ->
  Z.gcd x modulus = 1 ->
  ExactOrderCriterion x modulus (Ord x modulus).
Proof.
  intros Hmodulus Hgcd.
  pose proof (coprime_implies_order_input x modulus Hmodulus Hgcd)
    as Hinput.
  pose proof
    (order_input_implies_order_power_law
       x modulus (EulerPhi modulus) Hinput) as Hlaw.
  split.
  - unfold OrderInput in Hinput; tauto.
  - intros exponent Hnonnegative.
    apply Hlaw; exact Hnonnegative.
Qed.

Corollary coprime_implies_reduced_exact_order_criterion
    (x modulus : Z) :
  1 < modulus ->
  Z.gcd x modulus = 1 ->
  ExactOrderCriterion
    (x mod modulus) modulus (Ord (x mod modulus) modulus).
Proof.
  intros Hmodulus Hgcd.
  apply coprime_implies_exact_order_criterion; [exact Hmodulus |].
  apply reduced_base_coprime; lia.
Qed.

Lemma exact_order_criterion_unique
    (x modulus first second : Z) :
  ExactOrderCriterion x modulus first ->
  ExactOrderCriterion x modulus second ->
  first = second.
Proof.
  intros [Hfirst_positive Hfirst] [Hsecond_positive Hsecond].
  assert (Hfirst_divides_second : (first | second)).
  {
    apply (proj1 (Hfirst second ltac:(lia))).
    apply (proj2 (Hsecond second ltac:(lia))).
    exists 1; ring.
  }
  assert (Hsecond_divides_first : (second | first)).
  {
    apply (proj1 (Hsecond first ltac:(lia))).
    apply (proj2 (Hfirst first ltac:(lia))).
    exists 1; ring.
  }
  pose proof
    (Z.divide_pos_le first second Hsecond_positive Hfirst_divides_second)
    as Hfirst_le_second.
  pose proof
    (Z.divide_pos_le second first Hfirst_positive Hsecond_divides_first)
    as Hsecond_le_first.
  lia.
Qed.

Corollary exact_order_criterion_is_ord
    (x modulus candidate : Z) :
  1 < modulus ->
  Z.gcd x modulus = 1 ->
  ExactOrderCriterion x modulus candidate ->
  candidate = Ord x modulus.
Proof.
  intros Hmodulus Hgcd Hcandidate.
  eapply exact_order_criterion_unique; [exact Hcandidate |].
  apply coprime_implies_exact_order_criterion; assumption.
Qed.

Corollary coprime_implies_order_result
    (x modulus : Z) :
  1 < modulus ->
  Z.gcd x modulus = 1 ->
  OrderResult x modulus (Ord x modulus).
Proof.
  intros Hmodulus Hgcd.
  pose proof (coprime_implies_order_input x modulus Hmodulus Hgcd)
    as Hinput.
  pose proof (euler_phi_positive_bounded modulus ltac:(lia))
    as Hphi_bounds.
  pose proof
    (ord_search_exact_from_terminal
       x modulus (EulerPhi modulus)
       Hmodulus eq_refl
       ltac:(lia)
       (euler_power_for_case_phi x modulus Hmodulus Hgcd))
    as [Hbounds [Hpower _]].
  unfold OrderInput in Hinput.
  destruct Hinput as (_ & _ & _ & _ & _ & Hdivides & _).
  unfold OrderResult.
  repeat split; try reflexivity; try assumption; lia.
Qed.
End P090_OrderInputBridge.
Export P090_OrderInputBridge.

Module P090_FactorConsumer.

Local Open Scope Z_scope.
Import ListNotations.

Import P090_OrderExcess.P090_OrderExcess.
Import P090_OrderFoundations.P090_OrderFoundations.

(** The active division loop must retain the ordering history of the prefix.
    The old [FactorAtPrime] contained only [FactorPrefix], which is insufficient
    to reconstruct the strict, duplicate-free table at loop exit. *)
Definition StrictTrialState
    (m candidate remainder : Z) (pr pe : list Z) : Prop :=
  StrictFactorPrefix m candidate remainder pr pe.

Definition StrictFactorAtPrime
    (m candidate original_remainder remainder exponent : Z)
    (pr pe : list Z) : Prop :=
  StrictFactorPrefix m candidate original_remainder pr pe /\
  IsPrime candidate /\
  original_remainder mod candidate = 0 /\
  0 <= exponent /\
  original_remainder = Z.pow candidate exponent * remainder /\
  0 < remainder <= original_remainder.

Lemma strict_trial_init m :
  0 < m -> StrictTrialState m 2 m [] [].
Proof.
  unfold StrictTrialState.
  apply strict_factor_prefix_base.
Qed.

Lemma strict_trial_skip
    m candidate remainder pr pe :
  StrictTrialState m candidate remainder pr pe ->
  remainder mod candidate <> 0 ->
  StrictTrialState m (candidate + 1) remainder pr pe.
Proof.
  intros [Hprefix Horder] Hcandidate_mod.
  destruct Hprefix as
      (Hlength & Hcapacity & Hcandidate & Hremainder & Hproduct &
       Hentries & Hnone).
  split; [| exact Horder].
  unfold FactorPrefix.
  split; [exact Hlength |].
  split; [exact Hcapacity |].
  split; [lia |].
  split; [exact Hremainder |].
  split; [exact Hproduct |].
  split.
  - intros k Hk.
    specialize (Hentries k Hk).
    destruct Hentries as (Hprime & Hexponent & Hbelow).
    split; [exact Hprime |].
    split; [exact Hexponent | lia].
  - intros p Hp Hbelow.
    destruct (Z_lt_ge_dec p candidate) as [Hsmall | Hsame].
    + apply Hnone; assumption.
    + assert (p = candidate) by lia.
      subst p; exact Hcandidate_mod.
Qed.

Lemma strict_trial_enter_factor
    m candidate remainder pr pe :
  2 <= candidate ->
  StrictTrialState m candidate remainder pr pe ->
  remainder mod candidate = 0 ->
  StrictFactorAtPrime
    m candidate remainder remainder 0 pr pe.
Proof.
  intros Hcandidate Htrial Hdivides.
  pose proof Htrial as [Hprefix _].
  destruct Hprefix as
      (_ & _ & _ & Hremainder & _ & _ & Hnone).
  assert (Hprime : IsPrime candidate).
  {
    eapply smallest_remaining_divisor_prime_law;
      try exact Hcandidate;
      try exact (proj1 Hremainder);
      try exact Hnone;
      exact Hdivides.
  }
  unfold StrictFactorAtPrime.
  split; [exact Htrial |].
  split; [exact Hprime |].
  split; [exact Hdivides |].
  split; [lia |].
  split.
  - rewrite Z.pow_0_r, Z.mul_1_l; reflexivity.
  - lia.
Qed.

Lemma strict_factor_at_prime_forgets_order
    m candidate original remainder exponent pr pe :
  StrictFactorAtPrime
    m candidate original remainder exponent pr pe ->
  FactorAtPrime m candidate original remainder exponent pr pe.
Proof.
  intros (Hstrict & Hprime & Hentry & Hexponent & Hproduct & Hbounds).
  unfold FactorAtPrime.
  split.
  - now apply strict_factor_prefix_forgets_order in Hstrict.
  - split; [exact Hprime |].
    split; [exact Hentry |].
    split; [exact Hexponent |].
    split; assumption.
Qed.

Lemma strict_factor_divide_step
    m candidate original remainder remainder' exponent pr pe :
  StrictFactorAtPrime
    m candidate original remainder exponent pr pe ->
  remainder = candidate * remainder' ->
  StrictFactorAtPrime
    m candidate original remainder' (exponent + 1) pr pe.
Proof.
  intros
    (Hstrict & Hprime & Hentry & Hexponent & Hproduct & Hbounds)
    Hdivision.
  pose proof (proj1 Hprime) as Hcandidate.
  assert (Hremainder'_positive : 0 < remainder') by nia.
  unfold StrictFactorAtPrime.
  split; [exact Hstrict |].
  split; [exact Hprime |].
  split; [exact Hentry |].
  split; [lia |].
  split.
  - rewrite Hproduct, Hdivision.
    rewrite Z.pow_add_r by lia.
    rewrite Z.pow_1_r.
    ring.
  - nia.
Qed.

Lemma strict_factor_positive_exponent_at_exit
    m candidate original remainder exponent pr pe :
  StrictFactorAtPrime
    m candidate original remainder exponent pr pe ->
  remainder mod candidate <> 0 ->
  1 <= exponent.
Proof.
  intros
    (_ & Hprime & Hentry & Hexponent & Hproduct & _) Hexit.
  destruct (Z.eq_dec exponent 0) as [Hzero | Hnonzero]; [| lia].
  subst exponent.
  rewrite Z.pow_0_r, Z.mul_1_l in Hproduct.
  rewrite Hproduct in Hentry.
  contradiction.
Qed.

Lemma strict_factor_finish_prime
    m candidate original remainder exponent pr pe :
  StrictFactorAtPrime
    m candidate original remainder exponent pr pe ->
  remainder mod candidate <> 0 ->
  Zlength pr < 64 ->
  StrictTrialState m (candidate + 1) remainder
    (pr ++ [candidate]) (pe ++ [exponent]).
Proof.
  intros Hstate Hexit Hroom.
  pose proof Hstate as
    (Hstrict & Hprime & Hentry & Hexponent & Hproduct & Hbounds).
  pose proof
    (strict_factor_positive_exponent_at_exit
       m candidate original remainder exponent pr pe Hstate Hexit)
    as Hexponent_positive.
  unfold StrictTrialState.
  eapply strict_factor_prefix_append_completed_prime;
    try exact Hstrict;
    try exact Hprime;
    try exact Hexponent_positive;
    try exact Hproduct;
    try exact (proj1 Hbounds);
    try exact Hexit;
    exact Hroom.
Qed.

Lemma strict_trial_finalize_after_square_exit
    m candidate remainder pr pe :
  StrictTrialState m candidate remainder pr pe ->
  m <= 100000000000000 ->
  candidate * candidate > remainder ->
  exists final_pr final_pe,
    ValidFactorTable m final_pr final_pe /\
    ((remainder = 1 /\ final_pr = pr /\ final_pe = pe) \/
     (1 < remainder /\
      final_pr = pr ++ [remainder] /\ final_pe = pe ++ [1])).
Proof.
  unfold StrictTrialState.
  apply strict_factor_prefix_finalize_after_square_exit.
Qed.

(** The exact loop-control formulation: a failed square guard produces the
    complete table, with the residual appended precisely when it is nonunit. *)
Corollary strict_trial_finalize_from_failed_guard
    m candidate remainder pr pe :
  StrictTrialState m candidate remainder pr pe ->
  m <= 100000000000000 ->
  ~ (candidate * candidate <= remainder) ->
  exists final_pr final_pe,
    ValidFactorTable m final_pr final_pe.
Proof.
  intros Htrial Hm Hguard.
  destruct
    (strict_trial_finalize_after_square_exit
       m candidate remainder pr pe Htrial Hm ltac:(lia))
    as [final_pr [final_pe [Hvalid _]]].
  exists final_pr, final_pe; exact Hvalid.
Qed.
End P090_FactorConsumer.
Export P090_FactorConsumer.

Module P090_FactorMachineBounds.

Import ListNotations.
Local Open Scope Z_scope.

Definition FactorInputLimit : Z := 100000000000000.
Definition FactorCandidateGuardLimit : Z := 10000000.
Definition FactorCandidateStateLimit : Z := 10000001.
Definition Signed64Max : Z := 9223372036854775807.

(** [StrictTrialState] alone intentionally permits arbitrary candidates once
    the residual is one.  The executable loop does not: every advance occurs
    only after a successful square guard.  This staging predicate records the
    resulting consumer-visible frontier bound. *)
Definition FactorMachineTrialState
    (m candidate remainder : Z) (pr pe : list Z) : Prop :=
  StrictTrialState m candidate remainder pr pe /\
  m <= FactorInputLimit /\
  candidate <= FactorCandidateStateLimit.

Definition FactorMachineAtPrime
    (m candidate original remainder exponent : Z)
    (pr pe : list Z) : Prop :=
  StrictFactorAtPrime
    m candidate original remainder exponent pr pe /\
  m <= FactorInputLimit /\
  candidate <= FactorCandidateGuardLimit.

Lemma strict_trial_numeric_components
    m candidate remainder pr pe :
  StrictTrialState m candidate remainder pr pe ->
  2 <= candidate /\ 0 < remainder <= m.
Proof.
  intros [[Hlength [Hcapacity [Hcandidate [Hremainder Hrest]]]] Horder].
  split; assumption.
Qed.

Lemma strict_trial_candidate_bound_under_guard
    m candidate remainder pr pe :
  StrictTrialState m candidate remainder pr pe ->
  m <= FactorInputLimit ->
  candidate * candidate <= remainder ->
  candidate <= FactorCandidateGuardLimit.
Proof.
  intros Htrial Hm Hguard.
  destruct (strict_trial_numeric_components
    m candidate remainder pr pe Htrial) as [Hcandidate Hremainder].
  unfold FactorInputLimit, FactorCandidateGuardLimit in *.
  nia.
Qed.

Lemma strict_trial_guard_square_range
    m candidate remainder pr pe :
  StrictTrialState m candidate remainder pr pe ->
  m <= FactorInputLimit ->
  candidate * candidate <= remainder ->
  0 <= candidate * candidate <= FactorInputLimit.
Proof.
  intros Htrial Hm Hguard.
  destruct (strict_trial_numeric_components
    m candidate remainder pr pe Htrial) as [Hcandidate Hremainder].
  split; nia.
Qed.

Lemma strict_factor_exponent_cap
    m candidate original remainder exponent pr pe :
  StrictFactorAtPrime
    m candidate original remainder exponent pr pe ->
  m <= FactorInputLimit ->
  exponent < 47.
Proof.
  intros Hstate Hm.
  destruct Hstate as
      (Hprefix & Hprime & Hentry & Hexponent & Hdecomposition & Hbounds).
  destruct Hprefix as [Hfactor_prefix Horder].
  destruct Hfactor_prefix as
      (Hlength & Hcapacity & Hcandidate & Horiginal & Hproduct &
       Hentries & Hexclude).
  assert (Hcandidate_power_nonnegative :
      0 <= Z.pow candidate exponent).
  { apply Z.pow_nonneg; lia. }
  assert (Hcandidate_power_bounded : Z.pow candidate exponent <= original).
  { rewrite Hdecomposition. nia. }
  assert (Htwo_power_bounded :
      Z.pow 2 exponent <= Z.pow candidate exponent).
  { apply Z.pow_le_mono_l; lia. }
  destruct (Z_lt_ge_dec exponent 47) as [Hcap | Hlarge];
    [exact Hcap |].
  assert (Hmonotone : Z.pow 2 47 <= Z.pow 2 exponent).
  { apply Z.pow_le_mono_r; lia. }
  assert (Hpow47 : Z.pow 2 47 = 140737488355328) by reflexivity.
  assert (Hnumeric : 100000000000000 < Z.pow 2 47).
  { rewrite Hpow47. lia. }
  unfold FactorInputLimit in Hm.
  lia.
Qed.

Corollary strict_factor_exponent_nonnegative_bounded
    m candidate original remainder exponent pr pe :
  StrictFactorAtPrime
    m candidate original remainder exponent pr pe ->
  m <= FactorInputLimit ->
  0 <= exponent <= 46.
Proof.
  intros Hstate Hm.
  split.
  - unfold StrictFactorAtPrime in Hstate. tauto.
  - pose proof
      (strict_factor_exponent_cap
         m candidate original remainder exponent pr pe Hstate Hm).
    lia.
Qed.

Lemma factor_machine_trial_init m :
  0 < m ->
  m <= FactorInputLimit ->
  FactorMachineTrialState m 2 m [] [].
Proof.
  intros Hm Hlimit.
  unfold FactorMachineTrialState.
  split; [apply strict_trial_init; exact Hm |].
  split; [exact Hlimit |].
  unfold FactorCandidateStateLimit. lia.
Qed.

Lemma factor_machine_trial_skip
    m candidate remainder pr pe :
  FactorMachineTrialState m candidate remainder pr pe ->
  candidate * candidate <= remainder ->
  remainder mod candidate <> 0 ->
  FactorMachineTrialState m (candidate + 1) remainder pr pe.
Proof.
  intros (Htrial & Hm & Hcandidate_state) Hguard Hnotdivides.
  assert (Hguard_bound : candidate <= FactorCandidateGuardLimit).
  { eapply strict_trial_candidate_bound_under_guard; eauto. }
  unfold FactorMachineTrialState.
  split.
  - apply strict_trial_skip; assumption.
  - split; [exact Hm |].
    unfold FactorCandidateGuardLimit, FactorCandidateStateLimit in *.
    lia.
Qed.

Lemma factor_machine_enter_prime
    m candidate remainder pr pe :
  FactorMachineTrialState m candidate remainder pr pe ->
  candidate * candidate <= remainder ->
  remainder mod candidate = 0 ->
  FactorMachineAtPrime
    m candidate remainder remainder 0 pr pe.
Proof.
  intros (Htrial & Hm & Hcandidate_state) Hguard Hdivides.
  assert (Hcandidate : 2 <= candidate).
  { apply (proj1
      (strict_trial_numeric_components
        m candidate remainder pr pe Htrial)). }
  assert (Hguard_bound : candidate <= FactorCandidateGuardLimit).
  { eapply strict_trial_candidate_bound_under_guard; eauto. }
  unfold FactorMachineAtPrime.
  split.
  - apply strict_trial_enter_factor; assumption.
  - split; assumption.
Qed.

Lemma factor_machine_divide_step
    m candidate original remainder remainder' exponent pr pe :
  FactorMachineAtPrime
    m candidate original remainder exponent pr pe ->
  remainder = candidate * remainder' ->
  FactorMachineAtPrime
    m candidate original remainder' (exponent + 1) pr pe.
Proof.
  intros (Hfactor & Hm & Hcandidate) Hdivision.
  unfold FactorMachineAtPrime.
  split.
  - eapply strict_factor_divide_step; eauto.
  - split; assumption.
Qed.

Lemma factor_machine_active_exponent_bounds
    m candidate original remainder exponent pr pe :
  FactorMachineAtPrime
    m candidate original remainder exponent pr pe ->
  0 <= exponent <= 46.
Proof.
  intros (Hfactor & Hm & Hcandidate).
  eapply strict_factor_exponent_nonnegative_bounded; eauto.
Qed.

Lemma factor_machine_finish_prime
    m candidate original remainder exponent pr pe :
  FactorMachineAtPrime
    m candidate original remainder exponent pr pe ->
  remainder mod candidate <> 0 ->
  Zlength pr < 64 ->
  FactorMachineTrialState m (candidate + 1) remainder
    (pr ++ [candidate]) (pe ++ [exponent]).
Proof.
  intros (Hfactor & Hm & Hcandidate) Hexit Hroom.
  unfold FactorMachineTrialState.
  split.
  - eapply strict_factor_finish_prime; eauto.
  - split; [exact Hm |].
    unfold FactorCandidateGuardLimit, FactorCandidateStateLimit in *.
    lia.
Qed.

Lemma factor_machine_candidate_square_signed64
    m candidate remainder pr pe :
  FactorMachineTrialState m candidate remainder pr pe ->
  0 <= candidate * candidate <= Signed64Max.
Proof.
  intros (Htrial & Hm & Hcandidate_upper).
  destruct (strict_trial_numeric_components
    m candidate remainder pr pe Htrial) as [Hcandidate_lower Hremainder].
  unfold FactorCandidateStateLimit, Signed64Max in *.
  nia.
Qed.

Lemma factor_machine_candidate_increment_signed64
    m candidate remainder pr pe :
  FactorMachineTrialState m candidate remainder pr pe ->
  0 <= candidate + 1 <= Signed64Max.
Proof.
  intros (Htrial & Hm & Hcandidate_upper).
  destruct (strict_trial_numeric_components
    m candidate remainder pr pe Htrial) as [Hcandidate_lower Hremainder].
  unfold FactorCandidateStateLimit, Signed64Max in *.
  lia.
Qed.

Lemma factor_machine_square_guard_no_wrap
    m candidate remainder pr pe square :
  FactorMachineTrialState m candidate remainder pr pe ->
  square = candidate * candidate ->
  0 <= square <= Signed64Max /\
  (square <= remainder <-> candidate * candidate <= remainder).
Proof.
  intros Hstate ->.
  split.
  - apply factor_machine_candidate_square_signed64 with m remainder pr pe.
    exact Hstate.
  - reflexivity.
Qed.

Theorem factor_machine_finalize_from_failed_square_guard
    m candidate remainder pr pe square :
  FactorMachineTrialState m candidate remainder pr pe ->
  square = candidate * candidate ->
  ~ (square <= remainder) ->
  0 <= square <= Signed64Max /\
  square > remainder /\
  exists final_pr final_pe,
    ValidFactorTable m final_pr final_pe.
Proof.
  intros (Htrial & Hm & Hcandidate) Hsquare Hfailed.
  subst square.
  split.
  - apply factor_machine_candidate_square_signed64 with m remainder pr pe.
    unfold FactorMachineTrialState. tauto.
  - split; [lia |].
    apply strict_trial_finalize_from_failed_guard with candidate remainder pr pe;
      assumption.
Qed.

(** The strengthened state is mapped at every C transition that changes the
    factor frontier: base, guarded skip, guarded factor entry, division step,
    completed-prime return, and failed-square finalisation.  No unrestricted
    [StrictTrialState -> candidate bound] lemma is stated because it is false
    once the residual is one. *)
End P090_FactorMachineBounds.
Export P090_FactorMachineBounds.

Module P090_OrderConsumer.

Local Open Scope Z_scope.

Import P090_OrderExcess.P090_OrderExcess.
Import P090_OrderFoundations.P090_OrderFoundations.
Import P090_OrderExact.P090_OrderExact.

(** Consumer-facing wrappers discharge every abstract mathematical-law
    argument of the order-state transition library.  Consequently the C
    annotation needs only the current state and the facts produced by the
    tested branch. *)

Lemma order_trial_init_from_coprime x modulus :
  1 < modulus ->
  Z.gcd x modulus = 1 ->
  OrderTrialStateEx
    x modulus (EulerPhi modulus) 2 (EulerPhi modulus) (EulerPhi modulus).
Proof.
  intros Hmodulus Hgcd.
  apply order_trial_init.
  apply coprime_implies_order_input; assumption.
Qed.

Lemma order_power_law_from_trial
    x modulus phi candidate remainder ord :
  OrderTrialStateEx x modulus phi candidate remainder ord ->
  OrderPowerLaw x modulus.
Proof.
  intros (Hinput & _).
  now apply order_input_implies_order_power_law with phi.
Qed.

Lemma order_power_law_from_factor
    x modulus phi active remainder ord :
  OrderFactorStateEx x modulus phi active remainder ord ->
  OrderPowerLaw x modulus.
Proof.
  intros (Hinput & _).
  now apply order_input_implies_order_power_law with phi.
Qed.

Lemma order_power_law_from_strip
    x modulus phi active remainder ord :
  OrderStripStateEx x modulus phi active remainder ord ->
  OrderPowerLaw x modulus.
Proof.
  intros [(Hinput & _) _].
  now apply order_input_implies_order_power_law with phi.
Qed.

Lemma order_power_law_from_final
    x modulus phi active ord :
  OrderFinalStateEx x modulus phi active ord ->
  OrderPowerLaw x modulus.
Proof.
  intros (Hinput & _).
  now apply order_input_implies_order_power_law with phi.
Qed.

Lemma order_trial_enter_factor_closed
    x modulus phi candidate remainder ord :
  2 <= candidate ->
  OrderTrialStateEx x modulus phi candidate remainder ord ->
  remainder mod candidate = 0 ->
  OrderFactorStateEx x modulus phi candidate remainder ord.
Proof.
  intros Hcandidate Hstate Hdivides.
  eapply order_trial_enter_factor; eauto.
  exact smallest_remaining_divisor_prime_law.
Qed.

Lemma order_factor_step_closed
    x modulus phi active remainder remainder' ord :
  OrderFactorStateEx x modulus phi active remainder ord ->
  remainder = active * remainder' ->
  OrderFactorStateEx x modulus phi active remainder' ord.
Proof.
  intros Hstate Hdivision.
  eapply order_factor_step; eauto.
  - exact prime_divisor_product_law.
  - exact prime_divisor_of_prime_law.
Qed.

Lemma order_strip_step_closed
    x modulus phi active remainder ord ord' :
  OrderStripStateEx x modulus phi active remainder ord ->
  ord = active * ord' ->
  Z.pow x ord' mod modulus = 1 ->
  OrderStripStateEx x modulus phi active remainder ord'.
Proof.
  intros Hstate Hdivision Hpower.
  eapply order_strip_step; eauto.
  now apply order_power_law_from_strip with phi active remainder ord.
Qed.

Lemma order_strip_exit_pow_failure_closed
    x modulus phi active remainder ord quotient :
  OrderStripStateEx x modulus phi active remainder ord ->
  ord = active * quotient ->
  Z.pow x quotient mod modulus <> 1 ->
  OrderTrialStateEx x modulus phi (active + 1) remainder ord.
Proof.
  intros Hstate Hdivision Hfailure.
  eapply order_strip_exit_pow_failure; eauto.
  now apply order_power_law_from_strip with phi active remainder ord.
Qed.

Lemma order_trial_exit_exhausted_closed
    x modulus phi candidate ord :
  OrderTrialStateEx x modulus phi candidate 1 ord ->
  OrderResult x modulus ord.
Proof.
  apply order_trial_exit_exhausted.
  exact prime_factor_exists_law.
Qed.

Lemma order_trial_enter_final_closed
    x modulus phi candidate remainder ord :
  2 <= candidate ->
  1 < remainder ->
  candidate * candidate > remainder ->
  OrderTrialStateEx x modulus phi candidate remainder ord ->
  OrderFinalStateEx x modulus phi remainder ord.
Proof.
  intros Hcandidate Hremainder Hguard Hstate.
  eapply order_trial_enter_final; eauto.
  - exact residual_remainder_prime_law.
  - exact prime_divisor_of_prime_law.
Qed.

Lemma order_final_step_closed
    x modulus phi active ord ord' :
  OrderFinalStateEx x modulus phi active ord ->
  ord = active * ord' ->
  Z.pow x ord' mod modulus = 1 ->
  OrderFinalStateEx x modulus phi active ord'.
Proof.
  intros Hstate Hdivision Hpower.
  eapply order_final_step; eauto.
  now apply order_power_law_from_final with phi active ord.
Qed.

Lemma order_final_exit_nodiv_closed
    x modulus phi active ord :
  OrderFinalStateEx x modulus phi active ord ->
  ~ (active | ord) ->
  OrderResult x modulus ord.
Proof.
  intros Hstate Hnotdivides.
  eapply order_final_exit_nodiv; eauto.
  exact prime_factor_exists_law.
Qed.

Lemma order_final_exit_pow_failure_closed
    x modulus phi active ord quotient :
  OrderFinalStateEx x modulus phi active ord ->
  ord = active * quotient ->
  Z.pow x quotient mod modulus <> 1 ->
  OrderResult x modulus ord.
Proof.
  intros Hstate Hdivision Hfailure.
  eapply order_final_exit_pow_failure; eauto.
  - exact prime_factor_exists_law.
  - now apply order_power_law_from_final with phi active ord.
Qed.

End P090_OrderConsumer.
Export P090_OrderConsumer.

Module P090_WalkConsumer.

Import ListNotations.
Local Open Scope Z_scope.


Lemma valid_table_exponent_positive
    (m : Z) (pr pe : list Z) (i : Z) :
  ValidFactorTable m pr pe ->
  0 <= i < Zlength pr ->
  1 <= Znth i pe 0.
Proof.
  intros (_ & _ & _ & Hentries & _) Hi.
  exact (proj2 (Hentries i Hi)).
Qed.

Lemma valid_table_initial_prefix_choice
    (m x : Z) (pr pe : list Z) :
  ValidFactorTable m pr pe ->
  PrefixChoice pr pe x 0 1 1 1.
Proof.
  intros Hvalid.
  pose proof Hvalid as (Hlength & _).
  unfold PrefixChoice.
  split; [exact Hlength |].
  split.
  - pose proof (Zlength_nonneg pr); lia.
  - split; [constructor |].
    split; [lia |].
    split; [lia |].
    split; [lia |].
    split.
    + unfold EulerPhi, coprime_count; reflexivity.
    + split.
      * unfold Ord; now rewrite Z.eqb_refl.
      * apply Z.gcd_1_r.
Qed.

Lemma prefix_choice_zero_extend
    (m : Z) (pr pe : list Z) (x i d phi ord : Z) :
  ValidFactorTable m pr pe ->
  PrefixChoice pr pe x i d phi ord ->
  i < Zlength pr ->
  PrefixChoice pr pe x (i + 1) d phi ord.
Proof.
  intros Hvalid
    (Hlength & Hindex & Hselected & Hd & Hphi & Hord &
     Hphi_value & Hord_value & Hgcd) Hi.
  assert (Hexponent : 0 <= 0 <= Znth i pe 0).
  {
    pose proof (valid_table_exponent_positive m pr pe i Hvalid)
      as Hpositive.
    lia.
  }
  assert (Hselected_next : PrefixSelected pr pe (i + 1) d).
  {
    pose proof
      (prefix_selected_step pr pe i d 0
         Hselected ltac:(lia) Hexponent) as Hstep.
    replace (d * Z.pow (Znth i pr 0) 0) with d in Hstep by
      (rewrite Z.pow_0_r; ring).
    exact Hstep.
  }
  unfold PrefixChoice.
  repeat split; try assumption; lia.
Qed.

Lemma walk_suffix_at_terminal
    (pr pe : list Z) (x i d : Z) :
  Zlength pr = Zlength pe ->
  i = Zlength pr ->
  WalkSuffix pr pe x i d = CycleTerm x d.
Proof.
  intros Hlength ->.
  assert (Hlength_nat : length pr = length pe).
  {
    rewrite !Zlength_correct in Hlength.
    now apply Nat2Z.inj in Hlength.
  }
  unfold WalkSuffix.
  rewrite Zlength_correct.
  rewrite Nat2Z.id.
  rewrite skipn_all.
  rewrite Hlength_nat, skipn_all.
  reflexivity.
Qed.

Lemma prefix_choice_leaf_cycle_term
    (pr pe : list Z) (x i d phi ord : Z) :
  PrefixChoice pr pe x i d phi ord ->
  d <> 1 ->
  CycleTerm x d = phi / ord.
Proof.
  intros
    (_ & _ & _ & Hd & Hphi & Hord & Hphi_value & Hord_value & _)
    Hnotone.
  unfold CycleTerm.
  destruct (Z.eqb_spec d 1); [contradiction |].
  rewrite (ord_reduced_base x d ltac:(lia)).
  now rewrite Hphi_value, Hord_value.
Qed.

Lemma prefix_choice_terminal_walk_value
    (pr pe : list Z) (x i d phi ord : Z) :
  PrefixChoice pr pe x i d phi ord ->
  i = Zlength pr ->
  d <> 1 ->
  WalkSuffix pr pe x i d = phi / ord.
Proof.
  intros Hchoice Hi Hd.
  rewrite walk_suffix_at_terminal
    by (unfold PrefixChoice in Hchoice; tauto).
  now apply prefix_choice_leaf_cycle_term with pr pe i.
Qed.

Lemma skipn_nth_cons_nat {A : Type}
    (values : list A) (index : nat) (default : A) :
  (index < length values)%nat ->
  skipn index values =
    nth index values default :: skipn (S index) values.
Proof.
  revert values.
  induction index as [| index IH]; intros values Hindex;
    destruct values as [| value values]; simpl in *; try lia.
  - reflexivity.
  - apply IH; lia.
Qed.

Lemma skipn_Znth_cons {A : Type}
    (values : list A) (index : Z) (default : A) :
  0 <= index < Zlength values ->
  skipn (Z.to_nat index) values =
    Znth index values default :: skipn (Z.to_nat (index + 1)) values.
Proof.
  intros Hindex.
  unfold Znth.
  pose proof
    (skipn_nth_cons_nat values (Z.to_nat index) default ltac:(
       rewrite Zlength_correct in Hindex;
       apply Nat2Z.inj_lt;
       rewrite Z2Nat.id by lia;
       exact (proj2 Hindex))) as Hskip.
  replace (S (Z.to_nat index)) with (Z.to_nat (index + 1)) in Hskip
    by lia.
  exact Hskip.
Qed.

Lemma walk_suffix_as_exp_suffix_zero
    (m : Z) (pr pe : list Z) (x i d : Z) :
  ValidFactorTable m pr pe ->
  0 <= i < Zlength pr ->
  WalkSuffix pr pe x i d =
  WalkExpSuffix pr pe x i 0 d.
Proof.
  intros Hvalid Hi.
  pose proof Hvalid as (Hlength & _).
  assert (Hi_pe : 0 <= i < Zlength pe) by lia.
  pose proof (valid_table_exponent_positive m pr pe i Hvalid Hi)
    as Hpositive.
  unfold WalkSuffix, WalkExpSuffix.
  rewrite (skipn_Znth_cons pr i 0 Hi).
  rewrite (skipn_Znth_cons pe i 0 Hi_pe).
  simpl walk_suffix_lists.
  replace (Z.to_nat (Znth i pe 0 - 0 + 1))
    with (S (Z.to_nat (Znth i pe 0))) by lia.
  reflexivity.
Qed.

Lemma walk_suffix_head_zero
    (m : Z) (pr pe : list Z) (x i d : Z) :
  ValidFactorTable m pr pe ->
  0 <= i < Zlength pr ->
  WalkSuffix pr pe x i d =
    WalkSuffix pr pe x (i + 1) d +
    WalkExpSuffix pr pe x i 1 d.
Proof.
  intros Hvalid Hi.
  pose proof (valid_table_exponent_positive m pr pe i Hvalid Hi)
    as Hpositive.
  pose proof
    (walk_exp_suffix_head_tail pr pe x i 0 d ltac:(lia))
    as Hsplit.
  rewrite Z.pow_0_r, Z.mul_1_r in Hsplit.
  rewrite
    (walk_suffix_as_exp_suffix_zero m pr pe x i d Hvalid Hi).
  exact Hsplit.
Qed.

Lemma walk_pending_after_zero
    (m : Z) (pr pe : list Z)
    (x i d before current : Z) :
  ValidFactorTable m pr pe ->
  0 <= i < Zlength pr ->
  WalkBudget m before (WalkSuffix pr pe x i d) ->
  current = before + WalkSuffix pr pe x (i + 1) d ->
  WalkPendingState pr pe m x i d before current 1.
Proof.
  intros Hvalid Hi Hbudget Hcurrent.
  pose proof (walk_suffix_head_zero m pr pe x i d Hvalid Hi)
    as Hsplit.
  pose proof (walk_suffix_nonnegative pr pe x (i + 1) d)
    as Hhead_nonnegative.
  pose proof
    (walk_exp_suffix_nonnegative pr pe x i 1 d
       (fun e => walk_suffix_nonnegative
         pr pe x (i + 1)
         (d * Z.pow (Znth i pr 0) (Z.of_nat e))))
    as Htail_nonnegative.
  unfold WalkBudget in Hbudget.
  unfold WalkPendingState, WalkLoopState, WalkBudget.
  split.
  - lia.
  - repeat split; lia.
Qed.

Lemma walk_pending_consume_head
    (pr pe : list Z) (m x i d before current next_e current' : Z) :
  0 <= next_e <= Znth i pe 0 ->
  WalkPendingState
    pr pe m x i d before current next_e ->
  current' = current +
    WalkSuffix pr pe x (i + 1)
      (d * Z.pow (Znth i pr 0) next_e) ->
  WalkPendingState
    pr pe m x i d before current' (next_e + 1).
Proof.
  intros Hbounds [Hloop Hbudget] Hcurrent'.
  pose proof
    (walk_exp_suffix_head_tail pr pe x i next_e d Hbounds)
    as Hsplit.
  pose proof (walk_suffix_nonnegative
    pr pe x (i + 1) (d * Z.pow (Znth i pr 0) next_e))
    as Hhead_nonnegative.
  pose proof
    (walk_exp_suffix_nonnegative pr pe x i (next_e + 1) d
       (fun e => walk_suffix_nonnegative
          pr pe x (i + 1)
          (d * Z.pow (Znth i pr 0) (Z.of_nat e))))
    as Htail_nonnegative.
  unfold WalkLoopState in Hloop.
  unfold WalkBudget in Hbudget.
  unfold WalkPendingState, WalkLoopState, WalkBudget.
  split.
  - lia.
  - repeat split; lia.
Qed.

Lemma walk_pending_finish
    (pr pe : list Z) (m x i d before current : Z) :
  WalkPendingState
    pr pe m x i d before current (Znth i pe 0 + 1) ->
  current = before + WalkSuffix pr pe x i d /\
  0 <= current <= m.
Proof.
  intros [Hloop Hbudget].
  unfold WalkLoopState in Hloop.
  unfold WalkBudget in Hbudget.
  rewrite walk_exp_suffix_exact_exhaustion in Hloop, Hbudget.
  lia.
Qed.

(** A returned recursive call consumes exactly the current head term and
    therefore advances the durable pending-state index by one. *)
Corollary walk_recursive_return_continuation
    (pr pe : list Z) (m x i d before current exponent returned : Z) :
  0 <= exponent <= Znth i pe 0 ->
  WalkPendingState
    pr pe m x i d before current exponent ->
  returned = current +
    WalkSuffix pr pe x (i + 1)
      (d * Z.pow (Znth i pr 0) exponent) ->
  WalkPendingState
    pr pe m x i d before returned (exponent + 1).
Proof.
  exact (walk_pending_consume_head pr pe m x i d before current exponent returned).
Qed.
End P090_WalkConsumer.
Export P090_WalkConsumer.

Module P090_WalkCallBudget.

Import ListNotations.
Local Open Scope Z_scope.


(** A cumulative budget for [head + tail] supplies both the recursive-call
    budget for [head] and, after that exact call returns, the continuation
    budget for [tail]. *)
Lemma walk_budget_split_head_tail
    (m current head tail : Z) :
  0 <= head ->
  0 <= tail ->
  WalkBudget m current (head + tail) ->
  WalkBudget m current head /\
  WalkBudget m (current + head) tail.
Proof.
  intros Hhead Htail Hbudget.
  unfold WalkBudget in *.
  split; repeat split; lia.
Qed.

(** At entry to a nonterminal [walk] frame, exponent zero is the first C
    recursive call.  The unconsumed work is exactly the exponent suffix
    beginning at one. *)
Lemma incoming_walk_suffix_zero_head_tail_budget
    (m : Z) (pr pe : list Z) (x i d before : Z) :
  ValidFactorTable m pr pe ->
  0 <= i < Zlength pr ->
  WalkBudget m before (WalkSuffix pr pe x i d) ->
  WalkSuffix pr pe x i d =
    WalkSuffix pr pe x (i + 1) d +
    WalkExpSuffix pr pe x i 1 d /\
  WalkBudget m before
    (WalkSuffix pr pe x (i + 1) d) /\
  WalkBudget m
    (before + WalkSuffix pr pe x (i + 1) d)
    (WalkExpSuffix pr pe x i 1 d).
Proof.
  intros Hvalid Hi Hwhole.
  pose proof (walk_suffix_head_zero m pr pe x i d Hvalid Hi)
    as Hsplit.
  pose proof
    (P090_WalkFoundations.walk_suffix_nonnegative
      pr pe x (i + 1) d) as Hhead.
  pose proof
    (walk_exp_suffix_nonnegative pr pe x i 1 d
      (fun exponent =>
        P090_WalkFoundations.walk_suffix_nonnegative
          pr pe x (i + 1)
          (d * Z.pow (Znth i pr 0) (Z.of_nat exponent))))
    as Htail.
  split; [exact Hsplit |].
  apply walk_budget_split_head_tail; try assumption.
  rewrite <- Hsplit. exact Hwhole.
Qed.

Corollary incoming_walk_suffix_zero_call_budget
    (m : Z) (pr pe : list Z) (x i d before : Z) :
  ValidFactorTable m pr pe ->
  0 <= i < Zlength pr ->
  WalkBudget m before (WalkSuffix pr pe x i d) ->
  WalkBudget m before
    (WalkSuffix pr pe x (i + 1) d).
Proof.
  intros Hvalid Hi Hwhole.
  exact
    (proj1 (proj2
      (incoming_walk_suffix_zero_head_tail_budget
        m pr pe x i d before Hvalid Hi Hwhole))).
Qed.

Lemma incoming_walk_suffix_zero_return_continuation
    (m : Z) (pr pe : list Z)
    (x i d before returned : Z) :
  ValidFactorTable m pr pe ->
  0 <= i < Zlength pr ->
  WalkBudget m before (WalkSuffix pr pe x i d) ->
  returned = before + WalkSuffix pr pe x (i + 1) d ->
  WalkPendingState
    pr pe m x i d before returned 1.
Proof.
  intros Hvalid Hi Hwhole Hreturned.
  exact
    (walk_pending_after_zero
      m pr pe x i d before returned
      Hvalid Hi Hwhole Hreturned).
Qed.

Theorem incoming_walk_suffix_zero_call_and_continuation
    (m : Z) (pr pe : list Z) (x i d before : Z) :
  ValidFactorTable m pr pe ->
  0 <= i < Zlength pr ->
  WalkBudget m before (WalkSuffix pr pe x i d) ->
  WalkBudget m before
    (WalkSuffix pr pe x (i + 1) d) /\
  forall returned,
    returned = before + WalkSuffix pr pe x (i + 1) d ->
    WalkPendingState
      pr pe m x i d before returned 1.
Proof.
  intros Hvalid Hi Hwhole.
  split.
  - eapply incoming_walk_suffix_zero_call_budget; eauto.
  - intros returned Hreturned.
    eapply incoming_walk_suffix_zero_return_continuation; eauto.
Qed.

(** Each exponent-loop iteration exposes exactly one recursive call.  The
    current accumulator funds that head call, and the returned accumulator
    funds the remaining exponent suffix. *)
Lemma walk_pending_head_tail_budget
    (pr pe : list Z) (m x i d before current exponent : Z) :
  0 <= exponent <= Znth i pe 0 ->
  WalkPendingState
    pr pe m x i d before current exponent ->
  WalkExpSuffix pr pe x i exponent d =
    WalkSuffix pr pe x (i + 1)
      (d * Z.pow (Znth i pr 0) exponent) +
    WalkExpSuffix pr pe x i (exponent + 1) d /\
  WalkBudget m current
    (WalkSuffix pr pe x (i + 1)
      (d * Z.pow (Znth i pr 0) exponent)) /\
  WalkBudget m
    (current + WalkSuffix pr pe x (i + 1)
      (d * Z.pow (Znth i pr 0) exponent))
    (WalkExpSuffix pr pe x i (exponent + 1) d).
Proof.
  intros Hbounds [_ Hpending_budget].
  pose proof
    (walk_exp_suffix_head_tail pr pe x i exponent d Hbounds)
    as Hsplit.
  pose proof
    (P090_WalkFoundations.walk_suffix_nonnegative
      pr pe x (i + 1)
      (d * Z.pow (Znth i pr 0) exponent)) as Hhead.
  pose proof
    (walk_exp_suffix_nonnegative pr pe x i (exponent + 1) d
      (fun next =>
        P090_WalkFoundations.walk_suffix_nonnegative
          pr pe x (i + 1)
          (d * Z.pow (Znth i pr 0) (Z.of_nat next))))
    as Htail.
  split; [exact Hsplit |].
  apply walk_budget_split_head_tail; try assumption.
  rewrite <- Hsplit. exact Hpending_budget.
Qed.

Corollary walk_pending_recursive_call_budget
    (pr pe : list Z) (m x i d before current exponent : Z) :
  0 <= exponent <= Znth i pe 0 ->
  WalkPendingState
    pr pe m x i d before current exponent ->
  WalkBudget m current
    (WalkSuffix pr pe x (i + 1)
      (d * Z.pow (Znth i pr 0) exponent)).
Proof.
  intros Hbounds Hpending.
  exact
    (proj1 (proj2
      (walk_pending_head_tail_budget
        pr pe m x i d before current exponent
        Hbounds Hpending))).
Qed.

Corollary walk_pending_post_return_tail_budget
    (pr pe : list Z)
    (m x i d before current exponent returned : Z) :
  0 <= exponent <= Znth i pe 0 ->
  WalkPendingState
    pr pe m x i d before current exponent ->
  returned = current +
    WalkSuffix pr pe x (i + 1)
      (d * Z.pow (Znth i pr 0) exponent) ->
  WalkBudget m returned
    (WalkExpSuffix pr pe x i (exponent + 1) d).
Proof.
  intros Hbounds Hpending Hreturned.
  subst returned.
  exact
    (proj2 (proj2
      (walk_pending_head_tail_budget
        pr pe m x i d before current exponent
        Hbounds Hpending))).
Qed.

Theorem walk_pending_recursive_call_and_return
    (pr pe : list Z) (m x i d before current exponent : Z) :
  0 <= exponent <= Znth i pe 0 ->
  WalkPendingState
    pr pe m x i d before current exponent ->
  WalkBudget m current
    (WalkSuffix pr pe x (i + 1)
      (d * Z.pow (Znth i pr 0) exponent)) /\
  forall returned,
    returned = current +
      WalkSuffix pr pe x (i + 1)
        (d * Z.pow (Znth i pr 0) exponent) ->
    WalkPendingState
      pr pe m x i d before returned (exponent + 1).
Proof.
  intros Hbounds Hpending.
  split.
  - eapply walk_pending_recursive_call_budget; eauto.
  - intros returned Hreturned.
    eapply walk_recursive_return_continuation; eauto.
Qed.

(** The current predicates already expose exactly the cumulative facts used
    above: [WalkPendingState] retains both the whole-frame conservation
    equation and the budget for every unconsumed exponent.  No strengthening
    of the annotation predicate is required for recursive-call extraction. *)
End P090_WalkCallBudget.
Export P090_WalkCallBudget.

Module P090_PrimePowerConsumer.

Import ListNotations.
Local Open Scope Z_scope.


Lemma valid_factor_table_entry
    (m : Z) (pr pe : list Z) (i : Z) :
  ValidFactorTable m pr pe ->
  0 <= i < Zlength pr ->
  IsPrime (Znth i pr 0) /\ 1 <= Znth i pe 0.
Proof. intros (_ & _ & _ & Hentry & _) Hi; apply Hentry; exact Hi. Qed.

Lemma table_power_at_divides_factor_product
    (pr pe : list Z) (i chosen : Z) :
  OrderedPrimeTable pr pe ->
  0 <= i < Zlength pr ->
  0 <= chosen <= Znth i pe 0 ->
  (Z.pow (Znth i pr 0) chosen | factor_product pr pe).
Proof.
  intros Htable.
  revert i chosen.
  induction Htable as
      [| p maximum pr pe Hp Hmaximum Hlt Htail IH];
    intros i chosen Hi Hchosen.
  - rewrite Zlength_nil in Hi; lia.
  - rewrite Zlength_cons in Hi.
    destruct (Z.eq_dec i 0) as [-> | Hine].
    + rewrite !Znth0_cons in Hchosen.
      simpl.
      exists (Z.pow p (maximum - chosen) * factor_product pr pe).
      assert (Hpow : Z.pow p maximum =
          Z.pow p chosen * Z.pow p (maximum - chosen)).
      {
        rewrite <- Z.pow_add_r by lia.
        f_equal; lia.
      }
      rewrite Hpow, Znth0_cons. ring.
    + assert (Hi_pos : 0 < i) by lia.
      rewrite !Znth_cons in Hchosen by lia.
      rewrite Znth_cons by lia.
      specialize (IH (i - 1) chosen ltac:(lia) Hchosen).
      destruct IH as [multiplier Hfactor].
      simpl.
      exists (Z.pow p maximum * multiplier).
      rewrite Hfactor. ring.
Qed.

Lemma valid_table_power_at_divides_m
    (m : Z) (pr pe : list Z) (i chosen : Z) :
  ValidFactorTable m pr pe ->
  0 <= i < Zlength pr ->
  0 <= chosen <= Znth i pe 0 ->
  (Z.pow (Znth i pr 0) chosen | m).
Proof.
  intros Hvalid Hi Hchosen.
  destruct Hvalid as (Hlen & Hbounds & Hproduct & Hentry & Horder).
  rewrite Hproduct.
  apply table_power_at_divides_factor_product; try assumption.
  eapply valid_factor_table_ordered_aux; eauto.
Qed.

Lemma prefix_selected_coprime_later_prime
    (m : Z) (pr pe : list Z) (i d k : Z) :
  ValidFactorTable m pr pe ->
  PrefixSelected pr pe i d ->
  i <= k < Zlength pr ->
  Z.gcd d (Znth k pr 0) = 1.
Proof.
  intros Hvalid Hselected.
  destruct Hvalid as (Hlen & Hbounds & Hproduct & Hentry & Horder).
  induction Hselected as
      [| j previous exponent Hprefix IH Hj Hexp]; intros Hk.
  - apply Z.gcd_1_l.
  - assert (Hjk : j < k) by lia.
    assert (Hprevious : Z.gcd previous (Znth k pr 0) = 1).
    { apply IH. lia. }
    destruct (Hentry j ltac:(lia)) as [Hprime_j Hmax_j].
    destruct (Hentry k ltac:(lia)) as [Hprime_k Hmax_k].
    assert (Hless : Znth j pr 0 < Znth k pr 0).
    { apply Horder; lia. }
    assert (Hprime_gcd :
        Z.gcd (Znth j pr 0) (Znth k pr 0) = 1).
    { apply smaller_distinct_primes_coprime; assumption. }
    apply Zgcd_1_rel_prime.
    apply rel_prime_sym.
    apply rel_prime_mult.
    + apply rel_prime_sym, Zgcd_1_rel_prime. exact Hprevious.
    + apply rel_prime_Zpower_r; [lia |].
      apply rel_prime_sym, Zgcd_1_rel_prime. exact Hprime_gcd.
Qed.

Lemma coprime_divisors_product_divides
    (a b whole : Z) :
  (a | whole) ->
  (b | whole) ->
  Z.gcd a b = 1 ->
  (a * b | whole).
Proof.
  intros [a_multiplier Ha] Hb Hgcd.
  subst whole.
  assert (Hrel : rel_prime b a).
  { apply rel_prime_sym, Zgcd_1_rel_prime. exact Hgcd. }
  assert (Hb_multiplier : (b | a_multiplier)).
  {
    eapply Gauss.
    - replace (a * a_multiplier) with (a_multiplier * a) by ring.
      exact Hb.
    - exact Hrel.
  }
  destruct Hb_multiplier as [multiplier Hmultiplier].
  exists multiplier. rewrite Hmultiplier. ring.
Qed.

Lemma prefix_selected_divides_m
    (m : Z) (pr pe : list Z) (i d : Z) :
  ValidFactorTable m pr pe ->
  PrefixSelected pr pe i d ->
  (d | m).
Proof.
  intros Hvalid Hselected.
  induction Hselected as
      [| j previous exponent Hprefix IH Hj Hexp].
  - apply Z.divide_1_l.
  - apply coprime_divisors_product_divides.
    + exact IH.
    + apply (valid_table_power_at_divides_m m pr pe j exponent);
        try assumption; lia.
    + apply gcd_prime_power_one; [lia |].
      apply (prefix_selected_coprime_later_prime
        m pr pe j previous j); try assumption; lia.
Qed.

Lemma gcd_with_divisor_of_coprime_modulus
    (x divisor modulus : Z) :
  Z.gcd x modulus = 1 ->
  (divisor | modulus) ->
  Z.gcd x divisor = 1.
Proof.
  intros Hgcd Hdivide.
  apply Zgcd_1_rel_prime.
  apply rel_prime_sym.
  eapply rel_prime_div.
  - apply rel_prime_sym, Zgcd_1_rel_prime. exact Hgcd.
  - exact Hdivide.
Qed.

Lemma gcd_coprime_product
    (x a b : Z) :
  Z.gcd x a = 1 ->
  Z.gcd x b = 1 ->
  Z.gcd x (a * b) = 1.
Proof.
  intros Ha Hb.
  apply Zgcd_1_rel_prime, rel_prime_mult;
    apply Zgcd_1_rel_prime; assumption.
Qed.

Lemma prime_power_consumer_basic
    (m x p exponent pk d : Z) (pr pe : list Z) (i : Z) :
  ValidFactorTable m pr pe ->
  PrefixSelected pr pe i d ->
  0 <= i < Zlength pr ->
  p = Znth i pr 0 ->
  1 <= exponent <= Znth i pe 0 ->
  WalkGlobalBounds m x ->
  pk = Z.pow p exponent ->
  2 <= pk <= m /\
  (pk | m) /\
  Z.gcd d p = 1 /\
  Z.gcd d pk = 1 /\
  Z.gcd x pk = 1.
Proof.
  intros Hvalid Hselected Hi -> Hexponent Hglobal ->.
  destruct Hglobal as ((Hm_lower & Hm_upper) & Hx & Hxm).
  destruct (valid_factor_table_entry m pr pe i Hvalid Hi)
    as [Hp Hmaximum].
  assert (Hdivide : (Z.pow (Znth i pr 0) exponent | m)).
  {
    apply (valid_table_power_at_divides_m m pr pe i exponent);
      try assumption; lia.
  }
  assert (Hpow_positive : 0 < Z.pow (Znth i pr 0) exponent).
  {
    apply Z.pow_pos_nonneg; [destruct Hp; lia | lia].
  }
  assert (Hgcd_dp : Z.gcd d (Znth i pr 0) = 1).
  {
    apply (prefix_selected_coprime_later_prime m pr pe i d i);
      try assumption; lia.
  }
  assert (Hgcd_dpk :
      Z.gcd d (Z.pow (Znth i pr 0) exponent) = 1).
  { apply gcd_prime_power_one; [lia | exact Hgcd_dp]. }
  assert (Hgcd_xpk :
      Z.gcd x (Z.pow (Znth i pr 0) exponent) = 1).
  { eapply gcd_with_divisor_of_coprime_modulus; eauto. }
  repeat split; try assumption.
  - assert (Hprime_lower : 1 < Znth i pr 0) by exact (proj1 Hp).
    assert (Hpower_lower : 2 <= Z.pow (Znth i pr 0) exponent).
    {
      replace exponent with (1 + (exponent - 1)) by lia.
      rewrite Z.pow_add_r by lia.
      rewrite Z.pow_1_r.
      pose proof
        (Z.pow_pos_nonneg (Znth i pr 0) (exponent - 1)
          ltac:(lia) ltac:(lia)).
      nia.
    }
    exact Hpower_lower.
  - eapply Z.divide_pos_le; [lia | exact Hdivide].
Qed.

Lemma prime_power_consumer_order_input
    (m x p exponent pk ph d : Z) (pr pe : list Z) (i : Z) :
  ValidFactorTable m pr pe ->
  PrefixSelected pr pe i d ->
  0 <= i < Zlength pr ->
  p = Znth i pr 0 ->
  1 <= exponent <= Znth i pe 0 ->
  WalkGlobalBounds m x ->
  pk = Z.pow p exponent ->
  ph = EulerPhi pk ->
  OrderInput (x mod pk) pk ph.
Proof.
  intros Hvalid Hselected Hi Hp Hexponent Hglobal Hpk Hph.
  destruct
    (prime_power_consumer_basic
       m x p exponent pk d pr pe i
       Hvalid Hselected Hi Hp Hexponent Hglobal Hpk)
    as [Hpk_bounds [_ [_ [_ Hgcd_xpk]]]].
  subst ph.
  apply coprime_implies_reduced_order_input; lia.
Qed.

Lemma prime_power_consumer_euler
    (m p exponent pk d : Z) (pr pe : list Z) (i : Z) :
  ValidFactorTable m pr pe ->
  PrefixSelected pr pe i d ->
  0 <= i < Zlength pr ->
  p = Znth i pr 0 ->
  1 <= exponent <= Znth i pe 0 ->
  pk = Z.pow p exponent ->
  EulerPhi (d * pk) = EulerPhi d * EulerPhi pk.
Proof.
  intros Hvalid Hselected Hi -> Hexponent ->.
  destruct (valid_factor_table_entry m pr pe i Hvalid Hi)
    as [Hp Hmaximum].
  assert (Hd : 1 <= d).
  { pose proof (prefix_selected_positive_from_valid_table
      m pr pe i d Hvalid Hselected); lia. }
  apply euler_phi_coprime_prime_power_all; try assumption; try lia.
  apply (prefix_selected_coprime_later_prime m pr pe i d i);
    try assumption; lia.
Qed.

Lemma prime_power_consumer_order_product
    (m x p exponent pk d phi ord o g : Z)
    (pr pe : list Z) (i : Z) :
  ValidFactorTable m pr pe ->
  PrefixChoice pr pe x i d phi ord ->
  0 <= i < Zlength pr ->
  p = Znth i pr 0 ->
  1 <= exponent <= Znth i pe 0 ->
  WalkGlobalBounds m x ->
  pk = Z.pow p exponent ->
  o = Ord (x mod pk) pk ->
  g = Z.gcd ord o ->
  Ord x (d * pk) = ord / g * o /\
  0 < ord / g * o.
Proof.
  intros Hvalid Hchoice Hi Hp Hexponent Hglobal Hpk Ho Hg.
  destruct Hchoice as
      (Hlen & Hchoice_i & Hselected & Hd & Hphi & Hord &
       Hphi_eq & Hord_eq & Hgcd_xd).
  destruct
    (prime_power_consumer_basic
       m x p exponent pk d pr pe i
       Hvalid Hselected Hi Hp Hexponent Hglobal Hpk)
    as [Hpk_bounds [Hpk_divides [Hgcd_dp [Hgcd_dpk Hgcd_xpk]]]].
  assert (Ho_positive : 0 < o).
  { rewrite Ho. pose proof (ord_positive (x mod pk) pk); lia. }
  destruct (order_lcm_runtime_formula ord o g Hord Ho_positive Hg)
    as [Hruntime Hruntime_positive].
  split; [| exact Hruntime_positive].
  destruct (Z.eq_dec d 1) as [Hd_one | Hd_not_one].
  - subst d.
    assert (Hord_one : ord = 1).
    { rewrite Hord_eq. reflexivity. }
    assert (Ho_unreduced : o = Ord x pk).
    {
      rewrite Ho.
      apply ord_reduced_base. lia.
    }
    subst ord.
    rewrite Z.gcd_1_l in Hg. subst g.
    rewrite Hord_one.
    rewrite Z.mul_1_l.
    replace (1 / 1) with 1 by reflexivity.
    rewrite Z.mul_1_l.
    symmetry. exact Ho_unreduced.
  - assert (Hd_two : 2 <= d) by lia.
    assert (Hcriterion_d : ExactOrderCriterion x d ord).
    {
      rewrite Hord_eq.
      apply coprime_implies_exact_order_criterion;
        [lia | exact Hgcd_xd].
    }
    assert (Hcriterion_pk : ExactOrderCriterion x pk o).
    {
      assert (Ho_unreduced : o = Ord x pk).
      { rewrite Ho. apply ord_reduced_base. lia. }
      rewrite Ho_unreduced.
      apply coprime_implies_exact_order_criterion; lia.
    }
    assert (Hcriterion_product :
        ExactOrderCriterion x (d * pk) (Z.lcm ord o)).
    {
      apply exact_order_coprime_product_lcm; try assumption; lia.
    }
    assert (Hgcd_product : Z.gcd x (d * pk) = 1).
    { apply gcd_coprime_product; assumption. }
    rewrite Hruntime.
    symmetry.
    apply exact_order_criterion_is_ord; try assumption; nia.
Qed.

Theorem prime_power_consumer_transition
    (m x p exponent pk ph o g d phi ord : Z)
    (pr pe : list Z) (i : Z) :
  ValidFactorTable m pr pe ->
  PrefixChoice pr pe x i d phi ord ->
  0 <= i < Zlength pr ->
  p = Znth i pr 0 ->
  1 <= exponent <= Znth i pe 0 ->
  WalkGlobalBounds m x ->
  pk = Z.pow p exponent ->
  ph = EulerPhi pk ->
  o = Ord (x mod pk) pk ->
  g = Z.gcd ord o ->
  OrderInput (x mod pk) pk ph /\
  PrimePowerTransition
    x d phi ord p exponent pk ph o g
    (d * pk) (phi * ph) (ord / g * o) /\
  PrefixChoice pr pe x (i + 1)
    (d * pk) (phi * ph) (ord / g * o) /\
  WalkMachineBounds m (d * pk) (phi * ph) (ord / g * o).
Proof.
  intros Hvalid Hchoice Hi Hp Hexponent Hglobal Hpk Hph Ho Hg.
  pose proof Hchoice as Hchoice_copy.
  destruct Hchoice as
      (Hlen & Hchoice_i & Hselected & Hd & Hphi & Hord &
       Hphi_eq & Hord_eq & Hgcd_xd).
  destruct
    (prime_power_consumer_basic
       m x p exponent pk d pr pe i
       Hvalid Hselected Hi Hp Hexponent Hglobal Hpk)
    as [Hpk_bounds [Hpk_divides [Hgcd_dp [Hgcd_dpk Hgcd_xpk]]]].
  assert (Hinput : OrderInput (x mod pk) pk ph).
  {
    eapply prime_power_consumer_order_input; eauto.
  }
  assert (Heuler :
      EulerPhi (d * pk) =
      EulerPhi d * EulerPhi pk).
  { eapply prime_power_consumer_euler; eauto. }
  destruct
    (prime_power_consumer_order_product
       m x p exponent pk d phi ord o g pr pe i
       Hvalid Hchoice_copy Hi Hp Hexponent Hglobal Hpk Ho Hg)
    as [Horder Hnext_ord_positive].
  assert (Hnext_d_positive : 0 < d * pk) by nia.
  assert (Hnext_phi_positive : 0 < phi * ph).
  {
    rewrite Hph.
    pose proof (euler_phi_positive_bounded pk ltac:(lia)).
    nia.
  }
  assert (Hgcd_product : Z.gcd x (d * pk) = 1).
  { apply gcd_coprime_product; assumption. }
  assert (Hnext_selected :
      PrefixSelected pr pe (i + 1) (d * pk)).
  {
    rewrite Hpk, Hp.
    apply prefix_selected_step_product; try assumption; lia.
  }
  assert (Hnext_choice :
      PrefixChoice pr pe x (i + 1)
        (d * pk) (phi * ph) (ord / g * o)).
  {
    unfold PrefixChoice.
    repeat split; try assumption; try lia.
  }
  assert (Htransition :
      PrimePowerTransition
        x d phi ord p exponent pk ph o g
        (d * pk) (phi * ph) (ord / g * o)).
  {
    apply prime_power_transition_build;
      try assumption; try reflexivity; try lia.
    - destruct (valid_factor_table_entry m pr pe i Hvalid Hi) as [Hprime _].
      rewrite <- Hp in Hprime; exact (proj1 Hprime).
  }
  assert (Hnext_divides : (d * pk | m)).
  { eapply prefix_selected_divides_m; eauto. }
  assert (Hnext_d_bounds : 0 < d * pk <= m).
  { split; [exact Hnext_d_positive |].
    eapply Z.divide_pos_le; [destruct Hglobal as ((Hm & _) & _); lia |].
    exact Hnext_divides. }
  assert (Hnext_phi_bounds : 0 < phi * ph <= m).
  {
    rewrite Hphi_eq, Hph, <- Heuler.
    pose proof (euler_phi_positive_bounded (d * pk) ltac:(lia)).
    lia.
  }
  assert (Hnext_ord_bounds : 0 < ord / g * o <= m).
  {
    assert (Hproduct_input :
        OrderInput x (d * pk) (EulerPhi (d * pk))).
    { apply coprime_implies_order_input; try assumption; nia. }
    destruct Hproduct_input as
        (_ & _ & _ & Hphi_product_bounds & Hord_product_positive &
         Hord_divides & _).
    rewrite Horder in Hord_product_positive, Hord_divides.
    split; [exact Hord_product_positive |].
    eapply Z.le_trans.
    - eapply Z.divide_pos_le; [exact (proj1 Hphi_product_bounds) |].
      exact Hord_divides.
    - eapply Z.le_trans.
      + exact (proj2 Hphi_product_bounds).
      + exact (proj2 Hnext_d_bounds).
  }
  split; [exact Hinput |].
  split; [exact Htransition |].
  split; [exact Hnext_choice |].
  unfold WalkMachineBounds.
  split; [exact Hnext_d_bounds |].
  split; [exact Hnext_phi_bounds | exact Hnext_ord_bounds].
Qed.

(** The theorem above closes the consumer-facing transition without assuming
    a final [Spec] fact.  Its only table-specific ingredients are the exact
    indexed prime power, the selected-prefix coprimality boundary, and the
    factor-product divisibility proved in this module. *)
End P090_PrimePowerConsumer.
Export P090_PrimePowerConsumer.

Module P090_WalkExponentConsumer.

Local Open Scope Z_scope.


(** The C exponent loop starts immediately after the exponent-zero recursive
    call.  The table entry supplies both primality and the positive maximum
    exponent; exact divisibility supplies the machine bound on [p]. *)
Lemma walk_exponent_init_from_table
    (m p : Z) (pr pe : list Z) (i : Z) :
  2 <= m ->
  ValidFactorTable m pr pe ->
  0 <= i < Zlength pr ->
  p = Znth i pr 0 ->
  WalkExponentState m p 1 (Znth i pe 0) 1 1.
Proof.
  intros Hm Hvalid Hi Hp.
  destruct (valid_factor_table_entry m pr pe i Hvalid Hi)
    as [Hprime Hmaximum].
  assert (Hpdivide : (p | m)).
  {
    pose proof
      (valid_table_power_at_divides_m m pr pe i 1 Hvalid Hi
         ltac:(lia)) as Hdivide.
    rewrite <- Hp, Z.pow_1_r in Hdivide.
    exact Hdivide.
  }
  assert (Hp_bounds : 2 <= p <= m).
  {
    split.
    - rewrite Hp. pose proof (proj1 Hprime); lia.
    - eapply Z.divide_pos_le; [lia | exact Hpdivide].
  }
  unfold WalkExponentState.
  repeat split; try lia.
Qed.

(** Multiplying the running prime power is exact at every taken iteration. *)
Lemma walk_exponent_pk_step
    (p exponent pk : Z) :
  1 <= exponent ->
  pk = Z.pow p (exponent - 1) ->
  pk * p = Z.pow p exponent.
Proof.
  intros Hexponent ->.
  pose proof
    (Z.pow_add_r p (exponent - 1) 1 ltac:(lia) ltac:(lia))
    as Hpower.
  rewrite Z.pow_1_r in Hpower.
  replace (exponent - 1 + 1) with exponent in Hpower by lia.
  symmetry; exact Hpower.
Qed.

(** This is the exact branch expression used by the C assignment to [ph]. *)
Definition WalkExponentPhiUpdate
    (p exponent ph : Z) : Z :=
  if Z.eqb exponent 1 then p - 1 else ph * p.

Lemma walk_exponent_phi_step
    (p exponent pk ph : Z) :
  IsPrime p ->
  1 <= exponent ->
  pk = Z.pow p (exponent - 1) ->
  ph = EulerPhi pk ->
  WalkExponentPhiUpdate p exponent ph =
    EulerPhi (pk * p).
Proof.
  intros Hprime Hexponent Hpk Hph.
  unfold WalkExponentPhiUpdate.
  destruct (Z.eqb exponent 1) eqn:Hequal.
  - apply Z.eqb_eq in Hequal; subst exponent.
    rewrite Hpk, Z.sub_diag, Z.pow_0_r, Z.mul_1_l.
    pose proof (euler_phi_prime_power p 1 Hprime ltac:(lia)) as Heuler.
    rewrite Z.pow_1_r, Z.pow_0_r, Z.mul_1_l in Heuler.
    symmetry; exact Heuler.
  - apply Z.eqb_neq in Hequal.
    assert (Hexponent_two : 2 <= exponent) by lia.
    assert (Hpk_step : pk * p = Z.pow p exponent).
    { eapply walk_exponent_pk_step; eauto. }
    rewrite Hph, Hpk_step, Hpk.
    rewrite (euler_phi_prime_power p (exponent - 1) Hprime ltac:(lia)).
    rewrite (euler_phi_prime_power p exponent Hprime Hexponent).
    pose proof
      (Z.pow_add_r p (exponent - 2) 1 ltac:(lia) ltac:(lia))
      as Hpower.
    rewrite Z.pow_1_r in Hpower.
    replace (exponent - 2 + 1) with (exponent - 1) in Hpower by lia.
    rewrite Hpower.
    replace (exponent - 1 - 1) with (exponent - 2) by lia.
    ring.
Qed.

(** A positive divisor of [m] is at most [m].  Stating this separately keeps
    the no-overflow premise visible rather than hiding it in the loop state. *)
Lemma positive_prime_power_divisor_bound
    (m p exponent : Z) :
  0 < m ->
  1 < p ->
  0 <= exponent ->
  (Z.pow p exponent | m) ->
  1 <= Z.pow p exponent <= m.
Proof.
  intros Hm Hp Hexponent Hdivide.
  assert (Hpositive : 0 < Z.pow p exponent).
  { apply Z.pow_pos_nonneg; lia. }
  split; [lia |].
  eapply Z.divide_pos_le; assumption.
Qed.

(** Consumer-driven preservation theorem for one taken C-loop iteration.
    The indexed table supplies the exact divisibility that makes both
    multiplications mathematical (hence non-wrapping), while primality gives
    the Euler-phi update. *)
Theorem walk_exponent_step_from_table
    (m p exponent maximum pk ph : Z)
    (pr pe : list Z) (i : Z) :
  m <= 100000000000000 ->
  ValidFactorTable m pr pe ->
  0 <= i < Zlength pr ->
  p = Znth i pr 0 ->
  maximum = Znth i pe 0 ->
  exponent <= maximum ->
  WalkExponentState m p exponent maximum pk ph ->
  WalkExponentState m p (exponent + 1) maximum
    (pk * p) (WalkExponentPhiUpdate p exponent ph) /\
  pk * p = Z.pow p exponent /\
  WalkExponentPhiUpdate p exponent ph = EulerPhi (pk * p) /\
  0 <= pk * p <= 18446744073709551615 /\
  0 <= WalkExponentPhiUpdate p exponent ph <= 18446744073709551615.
Proof.
  intros Hm_cap Hvalid Hi Hp Hmaximum Hguard Hstate.
  pose proof Hstate as
    (Hp_bounds & Hexponent_bounds & Hpk_bounds & Hph_bounds & Hpk & Hph).
  destruct (valid_factor_table_entry m pr pe i Hvalid Hi)
    as [Hprime Htable_maximum].
  assert (Hexponent : 1 <= exponent <= Znth i pe 0) by lia.
  assert (Hpower_divides : (Z.pow p exponent | m)).
  {
    rewrite Hp.
    apply (valid_table_power_at_divides_m m pr pe i exponent);
      try assumption; lia.
  }
  assert (Hpower_bounds : 1 <= Z.pow p exponent <= m).
  {
    eapply positive_prime_power_divisor_bound; try eassumption; try lia.
  }
  assert (Hprime_p : IsPrime p).
  { rewrite Hp. exact Hprime. }
  assert (Hpk_step : pk * p = Z.pow p exponent).
  { eapply walk_exponent_pk_step; [lia | exact Hpk]. }
  assert (Hphi_step :
      WalkExponentPhiUpdate p exponent ph = EulerPhi (pk * p)).
  {
    eapply walk_exponent_phi_step;
      [exact Hprime_p | lia | exact Hpk | exact Hph].
  }
  assert (Hnext_positive : 0 < pk * p) by nia.
  pose proof
    (euler_phi_positive_bounded (pk * p) ltac:(lia))
    as Hphi_bounds.
  split.
  - unfold WalkExponentState.
    repeat split; try assumption; try lia.
    + rewrite Hpk_step.
      replace (exponent + 1 - 1) with exponent by lia.
      reflexivity.
  - split; [exact Hpk_step |].
    split; [exact Hphi_step |].
    split.
    + rewrite Hpk_step. lia.
    + rewrite Hphi_step. lia.
Qed.

(** The two branch-specialized forms match the C conditional assignment
    without leaving an [if] for symbolic execution to normalize. *)
Corollary walk_exponent_step_first_from_table
    (m p maximum pk ph : Z) (pr pe : list Z) (i : Z) :
  m <= 100000000000000 ->
  ValidFactorTable m pr pe ->
  0 <= i < Zlength pr ->
  p = Znth i pr 0 ->
  maximum = Znth i pe 0 ->
  WalkExponentState m p 1 maximum pk ph ->
  WalkExponentState m p 2 maximum (pk * p) (p - 1) /\
  pk * p = Z.pow p 1 /\
  p - 1 = EulerPhi (pk * p) /\
  0 <= pk * p <= 18446744073709551615 /\
  0 <= p - 1 <= 18446744073709551615.
Proof.
  intros Hm Hvalid Hi Hp Hmaximum Hstate.
  destruct (valid_factor_table_entry m pr pe i Hvalid Hi)
    as [_ Hpositive].
  pose proof
    (walk_exponent_step_from_table
       m p 1 maximum pk ph pr pe i
       Hm Hvalid Hi Hp Hmaximum ltac:(lia) Hstate)
    as Hstep.
  unfold WalkExponentPhiUpdate in Hstep.
  rewrite Z.eqb_refl in Hstep.
  exact Hstep.
Qed.

Corollary walk_exponent_step_later_from_table
    (m p exponent maximum pk ph : Z)
    (pr pe : list Z) (i : Z) :
  m <= 100000000000000 ->
  ValidFactorTable m pr pe ->
  0 <= i < Zlength pr ->
  p = Znth i pr 0 ->
  maximum = Znth i pe 0 ->
  1 < exponent ->
  exponent <= maximum ->
  WalkExponentState m p exponent maximum pk ph ->
  WalkExponentState m p (exponent + 1) maximum
    (pk * p) (ph * p) /\
  pk * p = Z.pow p exponent /\
  ph * p = EulerPhi (pk * p) /\
  0 <= pk * p <= 18446744073709551615 /\
  0 <= ph * p <= 18446744073709551615.
Proof.
  intros Hm Hvalid Hi Hp Hmaximum Hexponent Hguard Hstate.
  pose proof
    (walk_exponent_step_from_table
       m p exponent maximum pk ph pr pe i
       Hm Hvalid Hi Hp Hmaximum Hguard Hstate)
    as Hstep.
  unfold WalkExponentPhiUpdate in Hstep.
  assert (Hequal : Z.eqb exponent 1 = false).
  { apply Z.eqb_neq; lia. }
  rewrite Hequal in Hstep.
  exact Hstep.
Qed.

(** Projections after the body, in exactly the form expected by
    [prime_power_consumer_transition]. *)
Lemma walk_exponent_ready_for_transition
    (m p exponent maximum pk ph : Z) :
  1 <= exponent <= maximum ->
  WalkExponentState m p (exponent + 1) maximum pk ph ->
  pk = Z.pow p exponent /\
  ph = EulerPhi pk /\
  1 <= pk <= m /\
  1 <= ph <= m.
Proof.
  intros Hexponent
    (_ & _ & Hpk_bounds & Hph_bounds & Hpk & Hph).
  replace (exponent + 1 - 1) with exponent in Hpk by lia.
  repeat split; try assumption; lia.
Qed.

(** Complete handoff from the exponent-state invariant to the packaged
    divisor/order transition used immediately before the recursive call. *)
Theorem walk_exponent_state_consumer_transition
    (m x p exponent pk ph o g d phi ord : Z)
    (pr pe : list Z) (i : Z) :
  ValidFactorTable m pr pe ->
  PrefixChoice pr pe x i d phi ord ->
  0 <= i < Zlength pr ->
  p = Znth i pr 0 ->
  1 <= exponent <= Znth i pe 0 ->
  WalkGlobalBounds m x ->
  WalkExponentState m p (exponent + 1) (Znth i pe 0) pk ph ->
  o = Ord (x mod pk) pk ->
  g = Z.gcd ord o ->
  OrderInput (x mod pk) pk ph /\
  PrimePowerTransition
    x d phi ord p exponent pk ph o g
    (d * pk) (phi * ph) (ord / g * o) /\
  PrefixChoice pr pe x (i + 1)
    (d * pk) (phi * ph) (ord / g * o) /\
  WalkMachineBounds m (d * pk) (phi * ph) (ord / g * o).
Proof.
  intros Hvalid Hchoice Hi Hp Hexponent Hglobal Hstate Ho Hg.
  destruct
    (walk_exponent_ready_for_transition
       m p exponent (Znth i pe 0) pk ph Hexponent Hstate)
    as [Hpk [Hph _]].
  eapply prime_power_consumer_transition; eauto.
Qed.

(** On a failed loop guard, the state index is exactly one past the table
    exponent.  Its [pk]/[ph] values therefore describe the complete table
    prime power and remain machine-bounded. *)
Lemma walk_exponent_exit
    (m p exponent maximum pk ph : Z) :
  WalkExponentState m p exponent maximum pk ph ->
  maximum < exponent ->
  exponent = maximum + 1 /\
  pk = Z.pow p maximum /\
  ph = EulerPhi pk /\
  1 <= pk <= m /\
  1 <= ph <= m.
Proof.
  intros
    (_ & Hexponent & Hpk_bounds & Hph_bounds & Hpk & Hph) Hguard.
  assert (Hexit : exponent = maximum + 1) by lia.
  subst exponent.
  replace (maximum + 1 - 1) with maximum in Hpk by lia.
  repeat split; try assumption; lia.
Qed.

(** Composition with the cumulative walk invariant at the same failed guard. *)
Lemma walk_exponent_pending_exit
    (pr pe : list Z) (m x i d before current p exponent pk ph : Z) :
  WalkExponentState m p exponent (Znth i pe 0) pk ph ->
  Znth i pe 0 < exponent ->
  WalkPendingState pr pe m x i d before current exponent ->
  current = before + WalkSuffix pr pe x i d /\
  0 <= current <= m.
Proof.
  intros Hstate Hguard Hpending.
  destruct (walk_exponent_exit
    m p exponent (Znth i pe 0) pk ph Hstate Hguard)
    as [-> _].
  exact (walk_pending_finish pr pe m x i d before current Hpending).
Qed.
End P090_WalkExponentConsumer.
Export P090_WalkExponentConsumer.

Module P090_OrbitQuotient.

Import ListNotations.
Local Open Scope Z_scope.

Module OrderExact := P090_OrderExact.P090_OrderExact.

(** A forward-orbit hit is deliberately kept separate from any quotient
    representation.  This is exactly the witness exposed by [CatchesAll]. *)

Definition OrbitHit (m x start room : Z) : Prop :=
  exists time, 0 <= time /\
    room = (start * x ^ time) mod m.

Lemma orbit_hit_zero (m x start : Z) :
  0 < m ->
  0 <= start < m ->
  OrbitHit m x start start.
Proof.
  intros Hm Hstart.
  exists 0. split; [lia |].
  simpl. rewrite Z.mul_1_r.
  symmetry. apply Z.mod_small. exact Hstart.
Qed.

Lemma catches_all_gives_orbit_hit
    (m x : Z) (traps : list Z) (start : Z) :
  CatchesAll m x traps ->
  0 <= start < m ->
  exists room, In room traps /\ OrbitHit m x start room.
Proof.
  intros (_ & _ & Hcatch) Hstart.
  destruct (Hcatch start Hstart) as
      [time [room [Htime [Hroom Hin]]]].
  exists room. split; [exact Hin |].
  exists time. split; [lia | exact Hroom].
Qed.

(** [OrbitSeparated] is the consumer-facing uniqueness condition.  It says
    that two listed representatives cannot reach a common room.  Unlike a
    bare pairwise inequality, this is precisely what is needed to inject the
    representatives into an arbitrary catching list. *)

Definition OrbitSeparated
    (m x : Z) (representatives : list Z) : Prop :=
  forall left right room,
    In left representatives ->
    In right representatives ->
    OrbitHit m x left room ->
    OrbitHit m x right room ->
    left = right.

Definition OrbitCoversRange
    (m x : Z) (representatives : list Z) : Prop :=
  forall start,
    0 <= start < m ->
    exists representative,
      In representative representatives /\
      OrbitHit m x start representative.

Definition OrbitRepresentativeSystem
    (m x : Z) (representatives : list Z) : Prop :=
  NoDup representatives /\
  Forall (fun room => 0 <= room < m) representatives /\
  OrbitCoversRange m x representatives /\
  OrbitSeparated m x representatives.

Lemma representative_system_catches_all
    (m x : Z) (representatives : list Z) :
  OrbitRepresentativeSystem m x representatives ->
  CatchesAll m x representatives.
Proof.
  intros (Hnodup & Hrange & Hcover & _).
  split; [exact Hnodup |].
  split; [exact Hrange |].
  intros start Hstart.
  destruct (Hcover start Hstart) as
      [representative [Hin [time [Htime Hroom]]]].
  exists time, representative.
  split; [lia |]. split; [exact Hroom | exact Hin].
Qed.

(** A constructive finite pigeonhole lemma.  No choice function is used:
    at the induction step one concrete witness is removed from [targets]. *)

Lemma separated_witnesses_length
    (sources targets : list Z) (relation : Z -> Z -> Prop) :
  NoDup sources ->
  (forall source,
      In source sources ->
      exists target, In target targets /\ relation source target) ->
  (forall left right target,
      In left sources ->
      In right sources ->
      relation left target ->
      relation right target ->
      left = right) ->
  (length sources <= length targets)%nat.
Proof.
  intros Hnodup.
  revert targets.
  induction sources as [|source sources IH]; intros targets Hhits Hseparated.
  - simpl. lia.
  - inversion Hnodup as [| ? ? Hnotin Htailnodup]; subst.
    destruct (Hhits source ltac:(left; reflexivity)) as
        [target [Htarget_in Hsource_target]].
    assert (Htail_hits :
      forall other,
        In other sources ->
        exists other_target,
          In other_target (remove Z.eq_dec target targets) /\
          relation other other_target).
    {
      intros other Hother_in.
      destruct (Hhits other ltac:(right; exact Hother_in)) as
          [other_target [Hother_target_in Hother_target]].
      exists other_target. split; [| exact Hother_target].
      apply in_in_remove; [| exact Hother_target_in].
      intro Heq. subst other_target.
      assert (other = source).
      {
        apply (Hseparated other source target);
          try (right; exact Hother_in);
          try (left; reflexivity);
          assumption.
      }
      subst other. contradiction.
    }
    assert (Htail_separated :
      forall left right common,
        In left sources ->
        In right sources ->
        relation left common ->
        relation right common ->
        left = right).
    {
      intros left right common Hleft Hright.
      apply (Hseparated left right common);
        try (right; assumption).
    }
    pose proof
      (IH Htailnodup (remove Z.eq_dec target targets)
          Htail_hits Htail_separated) as Hlength_tail.
    pose proof
      (remove_length_lt Z.eq_dec targets target Htarget_in) as Hremove.
    simpl. lia.
Qed.

Lemma representative_system_lower_bound
    (m x : Z) (representatives traps : list Z) :
  OrbitRepresentativeSystem m x representatives ->
  CatchesAll m x traps ->
  (length representatives <= length traps)%nat.
Proof.
  intros (Hnodup & Hrange & _ & Hseparated) Hcatches.
  apply (separated_witnesses_length
           representatives traps (OrbitHit m x)); [exact Hnodup | |].
  - intros representative Hin.
    apply catches_all_gives_orbit_hit; [exact Hcatches |].
    rewrite Forall_forall in Hrange.
    apply Hrange. exact Hin.
  - exact Hseparated.
Qed.

Lemma representative_system_zlength_lower_bound
    (m x : Z) (representatives traps : list Z) :
  OrbitRepresentativeSystem m x representatives ->
  CatchesAll m x traps ->
  Zlength representatives <= Zlength traps.
Proof.
  intros Hsystem Hcatches.
  rewrite !Zlength_correct.
  apply Nat2Z.inj_le.
  eapply representative_system_lower_bound; eauto.
Qed.

(** Thus a concrete representative system of the divisor-cycle size closes
    both halves of the minimisation specification. *)

Lemma representative_system_implies_orbit_bounds
    (m x cycle_count : Z) (representatives : list Z) :
  OrbitRepresentativeSystem m x representatives ->
  Zlength representatives = cycle_count + 1 ->
  P090_WalkBridge.OrbitCoverUpperBound m x cycle_count /\
  P090_WalkBridge.OrbitCoverLowerBound m x cycle_count.
Proof.
  intros Hsystem Hlength.
  split.
  - exists representatives. split.
    + apply representative_system_catches_all. exact Hsystem.
    + exact Hlength.
  - intros traps Htraps.
    rewrite <- Hlength.
    exact
      (representative_system_zlength_lower_bound
         m x representatives traps Hsystem Htraps).
Qed.

Lemma representative_system_implies_spec
    (m x cycle_count : Z) (representatives : list Z) :
  OrbitRepresentativeSystem m x representatives ->
  Zlength representatives = cycle_count + 1 ->
  Spec m x (cycle_count + 1).
Proof.
  intros Hsystem Hlength.
  destruct
    (representative_system_implies_orbit_bounds
       m x cycle_count representatives Hsystem Hlength)
    as [Hupper Hlower].
  apply P090_WalkBridge.orbit_cover_bounds_imply_spec; assumption.
Qed.

(** The exact bounded-search result now discharges the order premise used by
    the earlier orbit lemmas. *)

Lemma order_input_exact_order_criterion
    (x modulus phi : Z) :
  OrderInput x modulus phi ->
  P090_WalkFoundations.ExactOrderCriterion
    x modulus (Ord x modulus).
Proof.
  intros Hinput.
  split.
  - pose proof (P090_WalkFoundations.ord_positive x modulus). lia.
  - apply OrderExact.order_input_implies_order_power_law with phi.
    exact Hinput.
Qed.

(** Quotients are formed separately inside a gcd stratum.  This prevents the
    false conclusion that every residue has the global unit-orbit length. *)

Definition StratumCovers
    (m x gcd_value : Z) (representatives : list Z) : Prop :=
  forall start,
    0 <= start < m ->
    Z.gcd start m = gcd_value ->
    exists representative,
      In representative representatives /\
      OrbitHit m x start representative.

Definition StratumRepresentativeSystem
    (m x gcd_value : Z) (representatives : list Z) : Prop :=
  NoDup representatives /\
  Forall
    (fun room => 0 <= room < m /\ Z.gcd room m = gcd_value)
    representatives /\
  StratumCovers m x gcd_value representatives /\
  OrbitSeparated m x representatives.

Lemma stratum_representatives_lower_bound
    (m x gcd_value : Z) (representatives traps : list Z) :
  StratumRepresentativeSystem m x gcd_value representatives ->
  CatchesAll m x traps ->
  (length representatives <= length traps)%nat.
Proof.
  intros (Hnodup & Hrange & _ & Hseparated) Hcatches.
  apply (separated_witnesses_length
           representatives traps (OrbitHit m x)); [exact Hnodup | |].
  - intros representative Hin.
    apply catches_all_gives_orbit_hit; [exact Hcatches |].
    rewrite Forall_forall in Hrange.
    exact (proj1 (Hrange representative Hin)).
  - exact Hseparated.
Qed.

(** The zero stratum is the exceptional one-point orbit, explaining the
    [+1] convention in [CycleAnswer]. *)

Lemma zero_singleton_stratum_system
    (m x : Z) :
  0 < m ->
  StratumRepresentativeSystem m x m [0].
Proof.
  intros Hm.
  split; [constructor; [simpl; tauto | constructor] |].
  split.
  - constructor.
    + split; [lia |]. rewrite Z.gcd_0_l. lia.
    + constructor.
  - split.
    + intros start Hstart Hgcd.
      assert (start = 0).
      {
        pose proof (Z.gcd_divide_l start m) as Hdivides.
        rewrite Hgcd in Hdivides.
        pose proof
          (proj2 (Z.mod_divide start m ltac:(lia)) Hdivides)
          as Hmodzero.
        rewrite Z.mod_small in Hmodzero by exact Hstart.
        exact Hmodzero.
      }
      subst start.
      exists 0. split; [simpl; auto |].
      apply orbit_hit_zero; lia.
    + intros left right room Hleft Hright _ _.
      simpl in Hleft, Hright. intuition congruence.
Qed.

(** A single nonzero quotient block is completely explicit.  Its indices are
    the half-open interval [0, Ord), so the list can be counted without any
    quotient choice. *)

Definition UnitOrbitList
    (modulus x unit : Z) : list Z :=
  map
    (fun index : nat =>
       (unit * x ^ Z.of_nat index) mod modulus)
    (seq 0 (Z.to_nat (Ord x modulus))).

Lemma unit_orbit_list_length
    (modulus x unit : Z) :
  length (UnitOrbitList modulus x unit) =
  Z.to_nat (Ord x modulus).
Proof.
  unfold UnitOrbitList.
  rewrite length_map, length_seq. reflexivity.
Qed.

Lemma unit_orbit_list_zlength
    (modulus x unit phi : Z) :
  OrderInput x modulus phi ->
  Zlength (UnitOrbitList modulus x unit) = Ord x modulus.
Proof.
  intros Hinput.
  rewrite Zlength_correct, unit_orbit_list_length.
  rewrite Z2Nat.id; [reflexivity |].
  pose proof (P090_WalkFoundations.ord_positive x modulus). lia.
Qed.

Lemma nodup_map_on
    {A B : Type} (f : A -> B) (items : list A) :
  NoDup items ->
  (forall left right,
      In left items ->
      In right items ->
      f left = f right ->
      left = right) ->
  NoDup (map f items).
Proof.
  intros Hnodup Hinjective.
  induction items as [|item items IH].
  - constructor.
  - inversion Hnodup as [| ? ? Hnotin Htail]; subst.
    constructor.
    + intros Hmapped.
      apply in_map_iff in Hmapped.
      destruct Hmapped as [other [Hequal Hother]].
      apply Hnotin.
      assert (item = other).
      {
        apply (Hinjective item other);
          try (simpl; auto).
      }
      subst other. exact Hother.
    + apply IH; [exact Htail |].
      intros left right Hleft Hright.
      apply Hinjective; simpl; auto.
Qed.

(** A no-choice finite quotient constructor.  The representative of an item
    is the first related element of the fixed universe, and [nodup] keeps one
    copy of each such canonical key. *)

Definition EquivalenceLaws (relation : Z -> Z -> Prop) : Prop :=
  (forall item, relation item item) /\
  (forall left right, relation left right -> relation right left) /\
  (forall left middle right,
      relation left middle -> relation middle right -> relation left right).

Definition CanonicalKey
    (relatedb : Z -> Z -> bool) (universe : list Z) (item : Z) : Z :=
  match find (relatedb item) universe with
  | Some representative => representative
  | None => 0
  end.

Definition FiniteQuotient
    (relatedb : Z -> Z -> bool) (universe : list Z) : list Z :=
  nodup Z.eq_dec (map (CanonicalKey relatedb universe) universe).

Lemma find_extensional_bool
    (test_left test_right : Z -> bool) (items : list Z) :
  (forall item, test_left item = test_right item) ->
  find test_left items = find test_right items.
Proof.
  intros Hequal.
  induction items as [|item items IH]; [reflexivity |].
  simpl. rewrite Hequal. destruct (test_right item); auto.
Qed.

Lemma canonical_key_in_and_related
    (relatedb : Z -> Z -> bool)
    (relation : Z -> Z -> Prop)
    (universe : list Z) (item : Z) :
  (forall left right,
      relatedb left right = true <-> relation left right) ->
  (forall value, relation value value) ->
  In item universe ->
  In (CanonicalKey relatedb universe item) universe /\
  relation item (CanonicalKey relatedb universe item).
Proof.
  intros Hreflect Hreflexive Hitem.
  unfold CanonicalKey.
  destruct (find (relatedb item) universe) as [key |] eqn:Hfind.
  - apply find_some in Hfind.
    destruct Hfind as [Hkey Htest].
    split; [exact Hkey |].
    apply Hreflect. exact Htest.
  - pose proof
      (find_none (relatedb item) universe Hfind item Hitem)
      as Hfalse.
    assert (relatedb item item = true).
    { apply Hreflect. apply Hreflexive. }
    congruence.
Qed.

Lemma canonical_key_equal_on_class
    (relatedb : Z -> Z -> bool)
    (relation : Z -> Z -> Prop)
    (universe : list Z) (left right : Z) :
  (forall a b,
      relatedb a b = true <-> relation a b) ->
  EquivalenceLaws relation ->
  relation left right ->
  CanonicalKey relatedb universe left =
  CanonicalKey relatedb universe right.
Proof.
  intros Hreflect (Hreflexive & Hsymmetric & Htransitive) Hrelated.
  unfold CanonicalKey.
  assert (Htests :
    forall candidate,
      relatedb left candidate = relatedb right candidate).
  {
    intros candidate.
    destruct (relatedb left candidate) eqn:Hleft,
             (relatedb right candidate) eqn:Hright;
      try reflexivity.
    - exfalso.
      apply Hreflect in Hleft.
      assert (Hright_related : relation right candidate).
      { eapply Htransitive; [apply Hsymmetric; exact Hrelated | exact Hleft]. }
      apply Hreflect in Hright_related. congruence.
    - exfalso.
      apply Hreflect in Hright.
      assert (Hleft_related : relation left candidate).
      { eapply Htransitive; [exact Hrelated | exact Hright]. }
      apply Hreflect in Hleft_related. congruence.
  }
  rewrite (find_extensional_bool
             (relatedb left) (relatedb right) universe Htests).
  reflexivity.
Qed.

Lemma canonical_key_idempotent
    (relatedb : Z -> Z -> bool)
    (relation : Z -> Z -> Prop)
    (universe : list Z) (item : Z) :
  (forall a b,
      relatedb a b = true <-> relation a b) ->
  EquivalenceLaws relation ->
  In item universe ->
  CanonicalKey relatedb universe
    (CanonicalKey relatedb universe item) =
  CanonicalKey relatedb universe item.
Proof.
  intros Hreflect Hlaws Hitem.
  symmetry.
  apply canonical_key_equal_on_class with relation.
  - exact Hreflect.
  - exact Hlaws.
  - destruct Hlaws as [Hreflexive _].
    exact
      (proj2
        (canonical_key_in_and_related
          relatedb relation universe item Hreflect Hreflexive Hitem)).
Qed.

Lemma finite_quotient_nodup
    (relatedb : Z -> Z -> bool) (universe : list Z) :
  NoDup (FiniteQuotient relatedb universe).
Proof. unfold FiniteQuotient. apply NoDup_nodup. Qed.

Lemma finite_quotient_key_in
    (relatedb : Z -> Z -> bool) (universe : list Z) (item : Z) :
  In item universe ->
  In (CanonicalKey relatedb universe item)
     (FiniteQuotient relatedb universe).
Proof.
  intros Hitem.
  unfold FiniteQuotient.
  apply (proj2 (nodup_In Z.eq_dec _ _)).
  apply in_map. exact Hitem.
Qed.

Lemma finite_quotient_forall_universe
    (relatedb : Z -> Z -> bool)
    (relation : Z -> Z -> Prop)
    (universe : list Z) :
  (forall left right,
      relatedb left right = true <-> relation left right) ->
  (forall value, relation value value) ->
  Forall (fun representative => In representative universe)
    (FiniteQuotient relatedb universe).
Proof.
  intros Hreflect Hreflexive.
  rewrite Forall_forall.
  intros representative Hin.
  unfold FiniteQuotient in Hin.
  apply (proj1 (nodup_In Z.eq_dec _ _)) in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [item [<- Hitem]].
  exact
    (proj1
      (canonical_key_in_and_related
        relatedb relation universe item Hreflect Hreflexive Hitem)).
Qed.

Lemma finite_quotient_covers
    (relatedb : Z -> Z -> bool)
    (relation : Z -> Z -> Prop)
    (universe : list Z) :
  (forall left right,
      relatedb left right = true <-> relation left right) ->
  (forall value, relation value value) ->
  forall item,
    In item universe ->
    exists representative,
      In representative (FiniteQuotient relatedb universe) /\
      relation item representative.
Proof.
  intros Hreflect Hreflexive item Hitem.
  exists (CanonicalKey relatedb universe item).
  split.
  - apply finite_quotient_key_in. exact Hitem.
  - exact
      (proj2
        (canonical_key_in_and_related
          relatedb relation universe item Hreflect Hreflexive Hitem)).
Qed.

Lemma finite_quotient_separated
    (relatedb : Z -> Z -> bool)
    (relation : Z -> Z -> Prop)
    (universe : list Z) :
  (forall left right,
      relatedb left right = true <-> relation left right) ->
  EquivalenceLaws relation ->
  forall left right,
    In left (FiniteQuotient relatedb universe) ->
    In right (FiniteQuotient relatedb universe) ->
    relation left right ->
    left = right.
Proof.
  intros Hreflect Hlaws left right Hleft Hright Hrelated.
  unfold FiniteQuotient in Hleft, Hright.
  apply (proj1 (nodup_In Z.eq_dec _ _)) in Hleft.
  apply (proj1 (nodup_In Z.eq_dec _ _)) in Hright.
  apply in_map_iff in Hleft.
  apply in_map_iff in Hright.
  destruct Hleft as [left_source [Hleft_key Hleft_source]].
  destruct Hright as [right_source [Hright_key Hright_source]].
  assert (Hleft_fixed :
    CanonicalKey relatedb universe left = left).
  {
    rewrite <- Hleft_key.
    apply canonical_key_idempotent with relation;
      assumption.
  }
  assert (Hright_fixed :
    CanonicalKey relatedb universe right = right).
  {
    rewrite <- Hright_key.
    apply canonical_key_idempotent with relation;
      assumption.
  }
  rewrite <- Hleft_fixed, <- Hright_fixed.
  apply canonical_key_equal_on_class with relation;
    assumption.
Qed.

Lemma orbit_advance
    (modulus x start first extra : Z) :
  modulus <> 0 ->
  0 <= first ->
  0 <= extra ->
  (((start * x ^ first) mod modulus) * x ^ extra) mod modulus =
  (start * x ^ (first + extra)) mod modulus.
Proof.
  intros Hmodulus Hfirst Hextra.
  rewrite Z.mul_mod_idemp_l by exact Hmodulus.
  rewrite <- Z.mul_assoc.
  rewrite <- Z.pow_add_r by assumption.
  reflexivity.
Qed.

Lemma unit_orbit_list_forall_range
    (modulus x unit phi : Z) :
  OrderInput x modulus phi ->
  Forall
    (fun room => 0 <= room < modulus)
    (UnitOrbitList modulus x unit).
Proof.
  intros Hinput.
  unfold UnitOrbitList.
  apply Forall_map. rewrite Forall_forall.
  intros index _.
  apply Z.mod_pos_bound.
  unfold OrderInput in Hinput. lia.
Qed.

Lemma unit_orbit_list_forall_unit
    (modulus x unit phi : Z) :
  OrderInput x modulus phi ->
  0 <= unit < modulus ->
  Z.gcd unit modulus = 1 ->
  Forall
    (fun room => Z.gcd room modulus = 1)
    (UnitOrbitList modulus x unit).
Proof.
  intros Hinput Hunit_range Hunit.
  unfold UnitOrbitList.
  apply Forall_map. rewrite Forall_forall.
  intros index _.
  rewrite <- Hunit.
  apply P090_WalkFoundations.gcd_stratum_preserved.
  - unfold OrderInput in Hinput. lia.
  - apply Nat2Z.is_nonneg.
  - unfold OrderInput in Hinput. tauto.
Qed.

Lemma unit_orbit_list_member_is_hit
    (modulus x unit phi room : Z) :
  OrderInput x modulus phi ->
  In room (UnitOrbitList modulus x unit) ->
  OrbitHit modulus x unit room.
Proof.
  intros _ Hin.
  unfold UnitOrbitList in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [index [Hroom _]].
  exists (Z.of_nat index).
  split; [apply Nat2Z.is_nonneg |].
  symmetry. exact Hroom.
Qed.

Lemma unit_orbit_list_nodup
    (modulus x unit phi : Z) :
  OrderInput x modulus phi ->
  0 <= unit < modulus ->
  Z.gcd unit modulus = 1 ->
  NoDup (UnitOrbitList modulus x unit).
Proof.
  intros Hinput Hunit_range Hunit.
  pose proof
    (order_input_exact_order_criterion x modulus phi Hinput)
    as Hcriterion.
  destruct Hcriterion as [Horder_pos Hpowerlaw].
  unfold UnitOrbitList.
  apply nodup_map_on.
  - apply seq_NoDup.
  - intros left right Hleft Hright Hequal.
    apply in_seq in Hleft.
    apply in_seq in Hright.
    simpl in Hleft, Hright.
    assert (Horder_nat :
      Z.of_nat (Z.to_nat (Ord x modulus)) =
      Ord x modulus).
    { apply Z2Nat.id. lia. }
    assert (Hleft_bound :
      0 <= Z.of_nat left < Ord x modulus).
    {
      split; [apply Nat2Z.is_nonneg |].
      rewrite <- Horder_nat.
      apply Nat2Z.inj_lt. lia.
    }
    assert (Hright_bound :
      0 <= Z.of_nat right < Ord x modulus).
    {
      split; [apply Nat2Z.is_nonneg |].
      rewrite <- Horder_nat.
      apply Nat2Z.inj_lt. lia.
    }
    destruct (Nat.lt_trichotomy left right) as
        [Hlt | [Heq | Hgt]]; [| exact Heq |].
    + set (advanced :=
        (unit * x ^ Z.of_nat left) mod modulus).
      assert (Hadvanced_range : 0 <= advanced < modulus).
      {
        unfold advanced.
        apply Z.mod_pos_bound.
        unfold OrderInput in Hinput. lia.
      }
      assert (Hadvanced_unit : Z.gcd advanced modulus = 1).
      {
        unfold advanced.
        rewrite <- Hunit.
        apply P090_WalkFoundations.gcd_stratum_preserved.
        - unfold OrderInput in Hinput. lia.
        - apply Nat2Z.is_nonneg.
        - unfold OrderInput in Hinput. tauto.
      }
      assert (Hreturn :
        (advanced * x ^ (Z.of_nat right - Z.of_nat left)) mod modulus =
        advanced).
      {
        unfold advanced.
        rewrite orbit_advance by
          (try (unfold OrderInput in Hinput; lia);
           try apply Nat2Z.is_nonneg;
           try lia).
        replace
          (Z.of_nat left + (Z.of_nat right - Z.of_nat left))
          with (Z.of_nat right) by lia.
        symmetry. exact Hequal.
      }
      pose proof
        (proj1
          (P090_OrbitOptimality.unit_orbit_return_iff
            modulus x advanced (Ord x modulus)
            (Z.of_nat right - Z.of_nat left)
            ltac:(unfold OrderInput in Hinput; lia)
            Hadvanced_range Hadvanced_unit ltac:(lia)
            (conj Horder_pos Hpowerlaw))
          Hreturn) as Hdivides.
      pose proof
        (Z.divide_pos_le
          (Ord x modulus)
          (Z.of_nat right - Z.of_nat left)
          ltac:(lia) Hdivides) as Htoo_large.
      lia.
    + exfalso.
      set (advanced :=
        (unit * x ^ Z.of_nat right) mod modulus).
      assert (Hadvanced_range : 0 <= advanced < modulus).
      {
        unfold advanced.
        apply Z.mod_pos_bound.
        unfold OrderInput in Hinput. lia.
      }
      assert (Hadvanced_unit : Z.gcd advanced modulus = 1).
      {
        unfold advanced.
        rewrite <- Hunit.
        apply P090_WalkFoundations.gcd_stratum_preserved.
        - unfold OrderInput in Hinput. lia.
        - apply Nat2Z.is_nonneg.
        - unfold OrderInput in Hinput. tauto.
      }
      assert (Hreturn :
        (advanced * x ^ (Z.of_nat left - Z.of_nat right)) mod modulus =
        advanced).
      {
        unfold advanced.
        rewrite orbit_advance by
          (try (unfold OrderInput in Hinput; lia);
           try apply Nat2Z.is_nonneg;
           try lia).
        replace
          (Z.of_nat right + (Z.of_nat left - Z.of_nat right))
          with (Z.of_nat left) by lia.
        exact Hequal.
      }
      pose proof
        (proj1
          (P090_OrbitOptimality.unit_orbit_return_iff
            modulus x advanced (Ord x modulus)
            (Z.of_nat left - Z.of_nat right)
            ltac:(unfold OrderInput in Hinput; lia)
            Hadvanced_range Hadvanced_unit ltac:(lia)
            (conj Horder_pos Hpowerlaw))
          Hreturn) as Hdivides.
      pose proof
        (Z.divide_pos_le
          (Ord x modulus)
          (Z.of_nat left - Z.of_nat right)
          ltac:(lia) Hdivides) as Htoo_large.
      lia.
Qed.

(** Every forward hit from a unit is represented by the bounded list: reduce
    its time modulo the exact order, then use the explicit index. *)

Lemma unit_orbit_hit_in_list
    (modulus x unit phi room : Z) :
  OrderInput x modulus phi ->
  0 <= unit < modulus ->
  Z.gcd unit modulus = 1 ->
  OrbitHit modulus x unit room ->
  In room (UnitOrbitList modulus x unit).
Proof.
  intros Hinput _ _ [time [Htime Hroom]].
  pose proof
    (order_input_exact_order_criterion x modulus phi Hinput)
    as [Horder_pos Hpowerlaw].
  assert (Horder_power :
    x ^ Ord x modulus mod modulus = 1).
  {
    apply Hpowerlaw; [lia |].
    exists 1. ring.
  }
  pose proof
    (Z.mod_pos_bound time (Ord x modulus) Horder_pos)
    as Hremainder.
  assert (Hmodulus_nonzero : modulus <> 0).
  { unfold OrderInput in Hinput. lia. }
  set (index := Z.to_nat (time mod Ord x modulus)).
  unfold UnitOrbitList.
  apply in_map_iff.
  exists index. split.
  - unfold index.
    rewrite Z2Nat.id by lia.
    rewrite Hroom.
    rewrite <- (Z.mul_mod_idemp_r
      unit (x ^ (time mod Ord x modulus))
      modulus Hmodulus_nonzero).
    rewrite <- (Z.mul_mod_idemp_r
      unit (x ^ time) modulus Hmodulus_nonzero).
    f_equal.
    f_equal.
    symmetry.
    apply OrderExact.pow_divmod_remainder;
      try (unfold OrderInput in Hinput; lia);
      assumption.
  - apply in_seq. simpl.
    split; [lia |].
    unfold index.
    apply (proj1 (Z2Nat.inj_lt
                    (time mod Ord x modulus)
                    (Ord x modulus)
                    ltac:(lia) ltac:(lia))).
    lia.
Qed.

(** Consequently the explicit block contains exactly the forward orbit and
    has cardinality [Ord]. *)

Lemma unit_orbit_list_exact
    (modulus x unit phi : Z) :
  OrderInput x modulus phi ->
  0 <= unit < modulus ->
  Z.gcd unit modulus = 1 ->
  NoDup (UnitOrbitList modulus x unit) /\
  Zlength (UnitOrbitList modulus x unit) = Ord x modulus /\
  (forall room,
      In room (UnitOrbitList modulus x unit) <->
      OrbitHit modulus x unit room).
Proof.
  intros Hinput Hrange Hunit.
  split.
  - apply unit_orbit_list_nodup with phi; assumption.
  - split.
    + apply unit_orbit_list_zlength with phi. exact Hinput.
    + intros room. split.
      * apply unit_orbit_list_member_is_hit with phi. exact Hinput.
      * apply unit_orbit_hit_in_list with phi; assumption.
Qed.

Lemma orbit_hit_transitive
    (modulus x start middle room : Z) :
  modulus <> 0 ->
  OrbitHit modulus x start middle ->
  OrbitHit modulus x middle room ->
  OrbitHit modulus x start room.
Proof.
  intros Hmodulus
    [first [Hfirst Hmiddle]] [second [Hsecond Hroom]].
  exists (first + second). split; [lia |].
  rewrite Hroom, Hmiddle.
  apply orbit_advance; lia.
Qed.

Lemma unit_orbit_hit_symmetric
    (modulus x unit phi room : Z) :
  OrderInput x modulus phi ->
  0 <= unit < modulus ->
  Z.gcd unit modulus = 1 ->
  OrbitHit modulus x unit room ->
  OrbitHit modulus x room unit.
Proof.
  intros Hinput Hunit_range Hunit Hhit.
  pose proof
    (unit_orbit_hit_in_list
       modulus x unit phi room Hinput Hunit_range Hunit Hhit)
    as Hin.
  unfold UnitOrbitList in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [index [Hindexed Hindex]].
  apply in_seq in Hindex. simpl in Hindex.
  pose proof
    (order_input_exact_order_criterion x modulus phi Hinput)
    as [Horder_pos Hpowerlaw].
  assert (Horder_nat :
    Z.of_nat (Z.to_nat (Ord x modulus)) =
    Ord x modulus).
  { apply Z2Nat.id. lia. }
  assert (Hindex_bounds :
    0 <= Z.of_nat index < Ord x modulus).
  {
    split; [apply Nat2Z.is_nonneg |].
    rewrite <- Horder_nat.
    apply Nat2Z.inj_lt. lia.
  }
  assert (Horder_power :
    x ^ Ord x modulus mod modulus = 1).
  {
    apply Hpowerlaw; [lia |]. exists 1. ring.
  }
  destruct (Z.eq_dec (Z.of_nat index) 0) as [Hindex_zero | Hindex_nonzero].
  - assert (Hroom_unit : room = unit).
    {
      rewrite <- Hindexed, Hindex_zero.
      simpl. rewrite Z.mul_1_r.
      apply Z.mod_small. exact Hunit_range.
    }
    rewrite Hroom_unit.
    apply orbit_hit_zero.
    + unfold OrderInput in Hinput. lia.
    + exact Hunit_range.
  - exists (Ord x modulus - Z.of_nat index).
    split; [lia |].
    rewrite <- Hindexed.
    rewrite orbit_advance by
      (try (unfold OrderInput in Hinput; lia);
       try apply Nat2Z.is_nonneg;
       try lia).
    replace
      (Z.of_nat index +
         (Ord x modulus - Z.of_nat index))
      with (Ord x modulus) by lia.
    rewrite <- (Z.mul_mod_idemp_r
      unit (x ^ Ord x modulus) modulus)
      by (unfold OrderInput in Hinput; lia).
    rewrite Horder_power, Z.mul_1_r.
    symmetry. apply Z.mod_small. exact Hunit_range.
Qed.

Definition UnitOrbitRelatedb
    (modulus x left right : Z) : bool :=
  existsb (Z.eqb right) (UnitOrbitList modulus x left).

Lemma unit_orbit_relatedb_true_iff
    (modulus x left phi right : Z) :
  OrderInput x modulus phi ->
  0 <= left < modulus ->
  Z.gcd left modulus = 1 ->
  (UnitOrbitRelatedb modulus x left right = true <->
   OrbitHit modulus x left right).
Proof.
  intros Hinput Hrange Hunit.
  unfold UnitOrbitRelatedb.
  rewrite existsb_exists.
  split.
  - intros [member [Hin Hequal]].
    apply Z.eqb_eq in Hequal. subst member.
    apply unit_orbit_list_member_is_hit with phi;
      assumption.
  - intros Hhit.
    exists right. split.
    + apply unit_orbit_hit_in_list with phi; assumption.
    + apply Z.eqb_refl.
Qed.

Lemma unit_orbit_equivalence_on_units
    (modulus x phi : Z) :
  OrderInput x modulus phi ->
  (forall unit,
      0 <= unit < modulus ->
      Z.gcd unit modulus = 1 ->
      OrbitHit modulus x unit unit) /\
  (forall left right,
      0 <= left < modulus ->
      Z.gcd left modulus = 1 ->
      OrbitHit modulus x left right ->
      OrbitHit modulus x right left) /\
  (forall left middle right,
      OrbitHit modulus x left middle ->
      OrbitHit modulus x middle right ->
      OrbitHit modulus x left right).
Proof.
  intros Hinput.
  split.
  - intros unit Hrange _. apply orbit_hit_zero.
    + unfold OrderInput in Hinput. lia.
    + exact Hrange.
  - split.
    + intros left right Hrange Hunit.
      apply unit_orbit_hit_symmetric with phi;
        assumption.
    + intros left middle right.
      apply orbit_hit_transitive.
      unfold OrderInput in Hinput. lia.
Qed.

(** Exact remaining quotient boundary.

    The lemmas above finish the constructive pigeonhole argument and the
    final [Spec] bridge once a representative list is available.  What is
    still missing is the following *theorem*, which is intentionally not
    declared as an axiom or predicate field:

      For every divisor [d >= 2] of [m], under [OrderInput (x mod d) d
      (EulerPhi d)], construct a list of representatives for the gcd-[m/d]
      stratum modulo [m], prove [OrbitSeparated], and prove its length is
      [EulerPhi d / Ord (x mod d) d].

    The no-choice enumeration mechanism itself is now complete:
    [FiniteQuotient] takes the first related item as a canonical key and its
    coverage and separation are proved above.  The concrete unit-orbit
    decision procedure [UnitOrbitRelatedb] is also proved correct, forward
    hits are symmetric/transitive on units, and [UnitOrbitList] proves that
    every class is duplicate-free with exact length [Ord].

    The minimal missing cardinality theorem is therefore the finite partition
    statement obtained after restricting [FiniteQuotient] to the explicit
    list of unit residues:

      [Zlength unit_representatives * Ord (x mod d) d = EulerPhi d],

    proved by showing that
    [concat (map (UnitOrbitList d (x mod d)) unit_representatives)] is a
    permutation of that unit list.  This needs only the remaining bookkeeping
    that packages the equivalence laws on the unit-residue universe; neither
    class size nor representative selection is still a number-theory gap.
    Dividing the equality gives the requested quotient length.  After the
    elementary transport [u |-> (m/d)*u], concatenating all divisor strata
    with [zero_singleton_stratum_system] gives the full representative system,
    and [representative_system_implies_spec] closes solver optimality.  No
    statement above assumes this cardinality or transport result. *)
End P090_OrbitQuotient.
Export P090_OrbitQuotient.

Module P090_UnitOrbitPartition.

Import ListNotations.
Local Open Scope Z_scope.

Module ETI := euler_theorem_inverse_lib.

(** The finite domain used by Euler phi, converted from natural residues to
    integers.  For moduli at least two the last candidate [modulus] is
    filtered out, so this is exactly the half-open unit range. *)

Definition UnitResidue (modulus unit : Z) : Prop :=
  0 <= unit < modulus /\ Z.gcd unit modulus = 1.

Definition UnitResidueb (modulus unit : Z) : bool :=
  (0 <=? unit) && (unit <? modulus) &&
  Z.eqb (Z.gcd unit modulus) 1.

Definition UnitResidues (modulus : Z) : list Z :=
  map Z.of_nat
    (filter
      (fun k : nat => Z.eqb (Z.gcd (Z.of_nat k) modulus) 1)
      (seq 1 (Z.to_nat modulus))).

Lemma unit_residueb_true_iff (modulus unit : Z) :
  UnitResidueb modulus unit = true <-> UnitResidue modulus unit.
Proof.
  unfold UnitResidueb, UnitResidue.
  rewrite !andb_true_iff, Z.leb_le, Z.ltb_lt, Z.eqb_eq.
  tauto.
Qed.

Lemma unit_residues_member_iff
    (modulus unit : Z) :
  2 <= modulus ->
  (In unit (UnitResidues modulus) <-> UnitResidue modulus unit).
Proof.
  intros Hmodulus.
  unfold UnitResidues, UnitResidue.
  rewrite in_map_iff.
  split.
  - intros [index [Hunit Hindex]].
    apply filter_In in Hindex.
    destruct Hindex as [Hindex Hcoprime].
    apply in_seq in Hindex.
    apply Z.eqb_eq in Hcoprime.
    subst unit.
    assert (Hindex_upper : Z.of_nat index <= modulus).
    {
      rewrite <- (Z2Nat.id modulus) by lia.
      apply Nat2Z.inj_le. lia.
    }
    assert (Hindex_strict : Z.of_nat index < modulus).
    {
      destruct (Z.eq_dec (Z.of_nat index) modulus) as [Hequal | Hneq];
        [| lia].
      rewrite Hequal, Z.gcd_diag, Z.abs_eq in Hcoprime by lia.
      lia.
    }
    split.
    + split; [apply Nat2Z.is_nonneg | exact Hindex_strict].
    + exact Hcoprime.
  - intros [[Hunit_nonnegative Hunit_upper] Hcoprime].
    exists (Z.to_nat unit).
    split.
    + apply Z2Nat.id. exact Hunit_nonnegative.
    + apply filter_In. split.
      * apply in_seq. split.
        -- assert (unit <> 0).
           {
             intro Hzero. subst unit.
             rewrite Z.gcd_0_l, Z.abs_eq in Hcoprime by lia.
             lia.
           }
           apply (proj1
             (Z2Nat.inj_le 1 unit ltac:(lia) Hunit_nonnegative)).
           lia.
        -- assert
             (Z.to_nat unit < Z.to_nat modulus)%nat.
           {
             apply (proj1
               (Z2Nat.inj_lt unit modulus
                 Hunit_nonnegative ltac:(lia))).
             exact Hunit_upper.
           }
           lia.
      * rewrite Z2Nat.id by exact Hunit_nonnegative.
        apply Z.eqb_eq. exact Hcoprime.
Qed.

Lemma unit_residues_nodup (modulus : Z) :
  NoDup (UnitResidues modulus).
Proof.
  unfold UnitResidues.
  apply nodup_map_on.
  - apply NoDup_filter. apply seq_NoDup.
  - intros left right _ _ Hequal.
    apply Nat2Z.inj. exact Hequal.
Qed.

Lemma unit_residues_zlength (modulus : Z) :
  Zlength (UnitResidues modulus) = EulerPhi modulus.
Proof.
  unfold UnitResidues.
  rewrite Zlength_correct, length_map.
  unfold EulerPhi.
  rewrite P090_WalkFoundations.coprime_count_filter.
  reflexivity.
Qed.

(** Guard the orbit relation outside the unit domain so that it is a genuine
    equivalence on all integers.  Inside the domain it is exactly forward
    reachability; outside it degenerates to equality. *)

Definition UnitOrbitEquiv
    (modulus x left right : Z) : Prop :=
  if UnitResidueb modulus left
  then UnitResidue modulus right /\ OrbitHit modulus x left right
  else left = right.

Definition UnitOrbitEquivb
    (modulus x left right : Z) : bool :=
  if UnitResidueb modulus left
  then UnitResidueb modulus right && UnitOrbitRelatedb modulus x left right
  else Z.eqb left right.

Lemma unit_orbit_equivb_true_iff
    (modulus x phi left right : Z) :
  OrderInput x modulus phi ->
  (UnitOrbitEquivb modulus x left right = true <->
   UnitOrbitEquiv modulus x left right).
Proof.
  intros Hinput.
  unfold UnitOrbitEquivb, UnitOrbitEquiv.
  destruct (UnitResidueb modulus left) eqn:Hleft.
  - apply unit_residueb_true_iff in Hleft.
    rewrite andb_true_iff.
    rewrite unit_residueb_true_iff.
    rewrite (unit_orbit_relatedb_true_iff
      modulus x left phi right Hinput
      (proj1 Hleft) (proj2 Hleft)).
    tauto.
  - rewrite Z.eqb_eq. tauto.
Qed.

Lemma unit_orbit_equiv_laws
    (modulus x phi : Z) :
  OrderInput x modulus phi ->
  EquivalenceLaws (UnitOrbitEquiv modulus x).
Proof.
  intros Hinput.
  unfold EquivalenceLaws.
  split.
  - intros item.
    unfold UnitOrbitEquiv.
    destruct (UnitResidueb modulus item) eqn:Hitem.
    + apply unit_residueb_true_iff in Hitem.
      split; [exact Hitem |].
      apply orbit_hit_zero.
      * unfold OrderInput in Hinput. lia.
      * exact (proj1 Hitem).
    + reflexivity.
  - split.
    + intros left right Hrelated.
      unfold UnitOrbitEquiv in *.
      destruct (UnitResidueb modulus left) eqn:Hleft.
      * apply unit_residueb_true_iff in Hleft.
        destruct Hrelated as [Hright Hhit].
        assert (Hrightb : UnitResidueb modulus right = true).
        { apply unit_residueb_true_iff. exact Hright. }
        rewrite Hrightb.
        split; [exact Hleft |].
        apply unit_orbit_hit_symmetric with phi.
        -- exact Hinput.
        -- exact (proj1 Hleft).
        -- exact (proj2 Hleft).
        -- exact Hhit.
      * subst right. rewrite Hleft. reflexivity.
    + intros left middle right Hleft_middle Hmiddle_right.
      unfold UnitOrbitEquiv in *.
      destruct (UnitResidueb modulus left) eqn:Hleft.
      * apply unit_residueb_true_iff in Hleft.
        destruct Hleft_middle as [Hmiddle Hhit_left].
        assert (Hmiddleb : UnitResidueb modulus middle = true).
        { apply unit_residueb_true_iff. exact Hmiddle. }
        rewrite Hmiddleb in Hmiddle_right.
        destruct Hmiddle_right as [Hright Hhit_right].
        split; [exact Hright |].
        apply orbit_hit_transitive with middle.
        -- unfold OrderInput in Hinput. lia.
        -- exact Hhit_left.
        -- exact Hhit_right.
      * subst middle.
        rewrite Hleft in Hmiddle_right.
        exact Hmiddle_right.
Qed.

Definition UnitRepresentatives (modulus x : Z) : list Z :=
  FiniteQuotient
    (UnitOrbitEquivb modulus x)
    (UnitResidues modulus).

Lemma unit_representatives_nodup (modulus x : Z) :
  NoDup (UnitRepresentatives modulus x).
Proof. unfold UnitRepresentatives. apply finite_quotient_nodup. Qed.

Lemma unit_representatives_forall_unit
    (modulus x phi : Z) :
  2 <= modulus ->
  OrderInput x modulus phi ->
  Forall (UnitResidue modulus) (UnitRepresentatives modulus x).
Proof.
  intros Hmodulus Hinput.
  unfold UnitRepresentatives.
  pose proof
    (finite_quotient_forall_universe
      (UnitOrbitEquivb modulus x)
      (UnitOrbitEquiv modulus x)
      (UnitResidues modulus)
      (fun left right =>
         unit_orbit_equivb_true_iff
           modulus x phi left right Hinput)
      (proj1 (unit_orbit_equiv_laws modulus x phi Hinput)))
    as Hforall.
  rewrite Forall_forall in *.
  intros representative Hin.
  apply unit_residues_member_iff; [exact Hmodulus |].
  apply Hforall. exact Hin.
Qed.

Lemma unit_representatives_cover
    (modulus x phi start : Z) :
  2 <= modulus ->
  OrderInput x modulus phi ->
  UnitResidue modulus start ->
  exists representative,
    In representative (UnitRepresentatives modulus x) /\
    OrbitHit modulus x start representative.
Proof.
  intros Hmodulus Hinput Hstart.
  assert (Hstart_in : In start (UnitResidues modulus)).
  { apply unit_residues_member_iff; assumption. }
  destruct
    (finite_quotient_covers
      (UnitOrbitEquivb modulus x)
      (UnitOrbitEquiv modulus x)
      (UnitResidues modulus)
      (fun left right =>
         unit_orbit_equivb_true_iff
           modulus x phi left right Hinput)
      (proj1 (unit_orbit_equiv_laws modulus x phi Hinput))
      start Hstart_in)
    as [representative [Hin Hrelated]].
  exists representative. split; [exact Hin |].
  unfold UnitOrbitEquiv in Hrelated.
  assert (Hstartb : UnitResidueb modulus start = true).
  { apply unit_residueb_true_iff. exact Hstart. }
  rewrite Hstartb in Hrelated.
  exact (proj2 Hrelated).
Qed.

Lemma unit_representatives_separated
    (modulus x phi : Z) :
  2 <= modulus ->
  OrderInput x modulus phi ->
  OrbitSeparated modulus x (UnitRepresentatives modulus x).
Proof.
  intros Hmodulus Hinput left right room Hleft Hright
    Hleft_hit Hright_hit.
  pose proof
    (unit_representatives_forall_unit
      modulus x phi Hmodulus Hinput) as Hunits.
  rewrite Forall_forall in Hunits.
  pose proof (Hunits left Hleft) as Hleft_unit.
  pose proof (Hunits right Hright) as Hright_unit.
  assert (Hright_left : OrbitHit modulus x right left).
  {
    apply orbit_hit_transitive with room.
    - unfold OrderInput in Hinput. lia.
    - exact Hright_hit.
    - apply unit_orbit_hit_symmetric with phi;
        try exact Hinput;
        try exact (proj1 Hleft_unit);
        try exact (proj2 Hleft_unit);
        exact Hleft_hit.
  }
  assert (Hrelated : UnitOrbitEquiv modulus x right left).
  {
    unfold UnitOrbitEquiv.
    assert (Hrightb : UnitResidueb modulus right = true).
    { apply unit_residueb_true_iff. exact Hright_unit. }
    rewrite Hrightb. auto.
  }
  symmetry.
  apply
    (finite_quotient_separated
      (UnitOrbitEquivb modulus x)
      (UnitOrbitEquiv modulus x)
      (UnitResidues modulus)
      (fun first second =>
         unit_orbit_equivb_true_iff
           modulus x phi first second Hinput)
      (unit_orbit_equiv_laws modulus x phi Hinput)
      right left);
    assumption.
Qed.

Theorem unit_representatives_stratum_system
    (modulus x phi : Z) :
  2 <= modulus ->
  OrderInput x modulus phi ->
  StratumRepresentativeSystem
    modulus x 1 (UnitRepresentatives modulus x).
Proof.
  intros Hmodulus Hinput.
  split; [apply unit_representatives_nodup |].
  split.
  - pose proof
      (unit_representatives_forall_unit
        modulus x phi Hmodulus Hinput) as Hforall.
    rewrite Forall_forall in *.
    intros representative Hin.
    exact (Hforall representative Hin).
  - split.
    + intros start Hrange Hunit.
      apply unit_representatives_cover with phi;
        [exact Hmodulus | exact Hinput |].
      split; assumption.
    + apply unit_representatives_separated with phi;
        assumption.
Qed.

(** The orbit blocks of distinct canonical representatives are disjoint. *)

Lemma nodup_concat_map_disjoint
    (items : list Z) (block : Z -> list Z) :
  NoDup items ->
  (forall item, In item items -> NoDup (block item)) ->
  (forall left right common,
      In left items ->
      In right items ->
      In common (block left) ->
      In common (block right) ->
      left = right) ->
  NoDup (concat (map block items)).
Proof.
  intros Hnodup Hblock Hdisjoint.
  induction items as [|item items IH].
  - constructor.
  - inversion Hnodup as [| ? ? Hnotin Htail]; subst.
    simpl.
    apply NoDup_app.
    + apply Hblock. simpl; auto.
    + apply IH.
      * exact Htail.
      * intros other Hother. apply Hblock. simpl; auto.
      * intros left right common Hleft Hright.
        apply Hdisjoint; simpl; auto.
    + intros common Hcommon_head Hcommon_tail.
      apply in_concat in Hcommon_tail.
      destruct Hcommon_tail as [other_block [Hother_block Hcommon_other]].
      apply in_map_iff in Hother_block.
      destruct Hother_block as [other [Hblock_equal Hother]].
      subst other_block.
      assert (item = other).
      {
        apply (Hdisjoint item other common);
          simpl; auto.
      }
      subst other. contradiction.
Qed.

Definition UnitOrbitBlocks (modulus x : Z) : list Z :=
  concat
    (map (UnitOrbitList modulus x)
      (UnitRepresentatives modulus x)).

Lemma unit_orbit_blocks_nodup
    (modulus x phi : Z) :
  2 <= modulus ->
  OrderInput x modulus phi ->
  NoDup (UnitOrbitBlocks modulus x).
Proof.
  intros Hmodulus Hinput.
  unfold UnitOrbitBlocks.
  apply nodup_concat_map_disjoint.
  - apply unit_representatives_nodup.
  - intros representative Hin.
    pose proof
      (unit_representatives_forall_unit
        modulus x phi Hmodulus Hinput) as Hunits.
    rewrite Forall_forall in Hunits.
    pose proof (Hunits representative Hin) as Hunit.
    apply unit_orbit_list_nodup with phi;
      [exact Hinput | exact (proj1 Hunit) | exact (proj2 Hunit)].
  - intros left right common Hleft Hright Hcommon_left Hcommon_right.
    apply
      (unit_representatives_separated
        modulus x phi Hmodulus Hinput left right common);
      try assumption.
    + apply unit_orbit_list_member_is_hit with phi;
        assumption.
    + apply unit_orbit_list_member_is_hit with phi;
        assumption.
Qed.

Lemma unit_orbit_blocks_member_iff
    (modulus x phi room : Z) :
  2 <= modulus ->
  OrderInput x modulus phi ->
  (In room (UnitOrbitBlocks modulus x) <->
   In room (UnitResidues modulus)).
Proof.
  intros Hmodulus Hinput.
  split.
  - intros Hin.
    unfold UnitOrbitBlocks in Hin.
    apply in_concat in Hin.
    destruct Hin as [block [Hblock Hroom]].
    apply in_map_iff in Hblock.
    destruct Hblock as [representative [Hblock Hrepresentative]].
    subst block.
    pose proof
      (unit_representatives_forall_unit
        modulus x phi Hmodulus Hinput) as Hunits.
    rewrite Forall_forall in Hunits.
    pose proof (Hunits representative Hrepresentative) as Hunit.
    pose proof
      (unit_orbit_list_forall_unit
        modulus x representative phi
        Hinput (proj1 Hunit) (proj2 Hunit)) as Hblock_units.
    pose proof
      (unit_orbit_list_forall_range
        modulus x representative phi Hinput) as Hblock_range.
    rewrite Forall_forall in Hblock_units, Hblock_range.
    apply unit_residues_member_iff; [exact Hmodulus |].
    split.
    + apply Hblock_range. exact Hroom.
    + apply Hblock_units. exact Hroom.
  - intros Hroom.
    apply unit_residues_member_iff in Hroom; [| exact Hmodulus].
    destruct
      (unit_representatives_cover
        modulus x phi room Hmodulus Hinput Hroom)
      as [representative [Hrepresentative Hhit]].
    assert (Hreverse : OrbitHit modulus x representative room).
    {
      apply unit_orbit_hit_symmetric with phi;
        [exact Hinput | exact (proj1 Hroom) |
         exact (proj2 Hroom) | exact Hhit].
    }
    assert (Hrepresentative_unit : UnitResidue modulus representative).
    {
      pose proof
        (unit_representatives_forall_unit
          modulus x phi Hmodulus Hinput) as Hunits.
      rewrite Forall_forall in Hunits.
      apply Hunits. exact Hrepresentative.
    }
    unfold UnitOrbitBlocks.
    apply in_concat.
    exists (UnitOrbitList modulus x representative).
    split.
    + apply in_map. exact Hrepresentative.
    + apply unit_orbit_hit_in_list with phi;
        [exact Hinput | exact (proj1 Hrepresentative_unit) |
         exact (proj2 Hrepresentative_unit) | exact Hreverse].
Qed.

Theorem unit_orbit_blocks_permutation
    (modulus x phi : Z) :
  2 <= modulus ->
  OrderInput x modulus phi ->
  Permutation
    (UnitOrbitBlocks modulus x)
    (UnitResidues modulus).
Proof.
  intros Hmodulus Hinput.
  apply NoDup_Permutation.
  - apply unit_orbit_blocks_nodup with phi; assumption.
  - apply unit_residues_nodup.
  - intros room.
    apply unit_orbit_blocks_member_iff with phi;
      assumption.
Qed.

Lemma concat_map_constant_length
    (items : list Z) (block : Z -> list Z) (size : nat) :
  (forall item, In item items -> length (block item) = size) ->
  length (concat (map block items)) = (length items * size)%nat.
Proof.
  intros Hsize.
  induction items as [|item items IH]; simpl.
  - reflexivity.
  - rewrite length_app, Hsize by (simpl; auto).
    rewrite IH by (intros other Hother; apply Hsize; simpl; auto).
    lia.
Qed.

Theorem unit_representatives_product_count
    (modulus x phi : Z) :
  2 <= modulus ->
  OrderInput x modulus phi ->
  Zlength (UnitRepresentatives modulus x) * Ord x modulus =
  EulerPhi modulus.
Proof.
  intros Hmodulus Hinput.
  pose proof
    (Permutation_length
      (unit_orbit_blocks_permutation
        modulus x phi Hmodulus Hinput)) as Hlength.
  unfold UnitOrbitBlocks in Hlength.
  rewrite
    (concat_map_constant_length
      (UnitRepresentatives modulus x)
      (UnitOrbitList modulus x)
      (Z.to_nat (Ord x modulus))) in Hlength.
  2: { intros item _. apply unit_orbit_list_length. }
  rewrite <- unit_residues_zlength.
  rewrite !Zlength_correct.
  replace (Ord x modulus)
    with (Z.of_nat (Z.to_nat (Ord x modulus))).
  2: {
    apply Z2Nat.id.
    pose proof (P090_WalkFoundations.ord_positive x modulus). lia.
  }
  rewrite <- Nat2Z.inj_mul.
  apply f_equal. exact Hlength.
Qed.

Corollary unit_representatives_order_divides_phi
    (modulus x phi : Z) :
  2 <= modulus ->
  OrderInput x modulus phi ->
  (Ord x modulus | EulerPhi modulus).
Proof.
  intros Hmodulus Hinput.
  exists (Zlength (UnitRepresentatives modulus x)).
  symmetry.
  apply unit_representatives_product_count with phi;
    assumption.
Qed.

Theorem unit_representatives_quotient_count
    (modulus x phi : Z) :
  2 <= modulus ->
  OrderInput x modulus phi ->
  Zlength (UnitRepresentatives modulus x) =
  EulerPhi modulus / Ord x modulus.
Proof.
  intros Hmodulus Hinput.
  pose proof
    (unit_representatives_product_count
      modulus x phi Hmodulus Hinput) as Hproduct.
  rewrite <- Hproduct.
  symmetry. apply Z.div_mul.
  pose proof (P090_WalkFoundations.ord_positive x modulus). lia.
Qed.

Definition UnitOrbitRepresentativeSystem
    (modulus x : Z) (representatives : list Z) : Prop :=
  StratumRepresentativeSystem modulus x 1 representatives.

Theorem unit_representatives_exact_package
    (modulus x phi : Z) :
  2 <= modulus ->
  OrderInput x modulus phi ->
  UnitOrbitRepresentativeSystem
    modulus x (UnitRepresentatives modulus x) /\
  Zlength (UnitRepresentatives modulus x) =
    EulerPhi modulus / Ord x modulus /\
  Permutation
    (UnitOrbitBlocks modulus x)
    (UnitResidues modulus).
Proof.
  intros Hmodulus Hinput.
  split.
  - apply unit_representatives_stratum_system with phi;
      assumption.
  - split.
    + apply unit_representatives_quotient_count with phi;
        assumption.
    + apply unit_orbit_blocks_permutation with phi;
        assumption.
Qed.

(** Consumer-facing reduced-base package used by each nonzero divisor
    stratum of the solver. *)

Theorem reduced_unit_representatives_exact
    (x modulus : Z) :
  2 <= modulus ->
  Z.gcd x modulus = 1 ->
  StratumRepresentativeSystem
    modulus (x mod modulus) 1
    (UnitRepresentatives modulus (x mod modulus)) /\
  Zlength (UnitRepresentatives modulus (x mod modulus)) =
    EulerPhi modulus /
      Ord (x mod modulus) modulus /\
  Permutation
    (UnitOrbitBlocks modulus (x mod modulus))
    (UnitResidues modulus).
Proof.
  intros Hmodulus Hcoprime.
  pose proof
    (coprime_implies_reduced_order_input
      x modulus ltac:(lia) Hcoprime) as Hinput.
  split.
  - apply unit_representatives_stratum_system
      with (EulerPhi modulus);
      assumption.
  - split.
    + apply unit_representatives_quotient_count
        with (EulerPhi modulus);
        assumption.
    + apply unit_orbit_blocks_permutation
        with (EulerPhi modulus);
        assumption.
Qed.
End P090_UnitOrbitPartition.
Export P090_UnitOrbitPartition.

Module P090_GcdStratumTransport.

Import ListNotations.
Local Open Scope Z_scope.

Module OQ := P090_OrbitQuotient.
Module OE := P090_OrderExact.P090_OrderExact.

Definition StratumLift (m d unit : Z) : Z :=
  (m / d) * unit.

Definition StratumProject (m d room : Z) : Z :=
  room / (m / d).

Definition LiftedRepresentatives
    (m d : Z) (representatives : list Z) : list Z :=
  map (StratumLift m d) representatives.

Lemma divisor_quotient_factorization (m d : Z) :
  0 < d ->
  (d | m) ->
  m = (m / d) * d.
Proof.
  intros Hd Hdiv.
  rewrite Z.mul_comm.
  apply Zdivide_Zdiv_eq; assumption.
Qed.

Lemma positive_divisor_quotient_positive (m d : Z) :
  0 < m ->
  0 < d ->
  (d | m) ->
  0 < m / d.
Proof.
  intros Hm Hd Hdiv.
  apply Z.div_str_pos.
  split; [exact Hd |].
  apply Z.divide_pos_le; assumption.
Qed.

Lemma coprime_mod_positive_divisor (m d x : Z) :
  0 < d ->
  (d | m) ->
  Z.gcd x m = 1 ->
  Z.gcd (x mod d) d = 1.
Proof.
  intros Hd Hdiv Hcoprime.
  rewrite Z.gcd_mod by lia.
  apply (proj2 (Zgcd_1_rel_prime d x)).
  apply rel_prime_div with m.
  - apply (proj1 (Zgcd_1_rel_prime m x)).
    rewrite Z.gcd_comm. exact Hcoprime.
  - exact Hdiv.
Qed.

Lemma stratum_lift_range_and_gcd
    (m d unit : Z) :
  0 < m ->
  0 < d ->
  (d | m) ->
  0 <= unit < d ->
  Z.gcd unit d = 1 ->
  0 <= StratumLift m d unit < m /\
  Z.gcd (StratumLift m d unit) m = m / d.
Proof.
  intros Hm Hd Hdiv Hrange Hunit.
  pose proof
    (positive_divisor_quotient_positive m d Hm Hd Hdiv) as Hq.
  pose proof
    (divisor_quotient_factorization m d Hd Hdiv) as Hfactor.
  set (q := m / d).
  change
    (0 <= q * unit < m /\ Z.gcd (q * unit) m = q).
  split.
  - split; nia.
  - rewrite Hfactor.
    change (Z.gcd (q * unit) (q * d) = q).
    rewrite Z.gcd_mul_mono_l.
    rewrite Z.abs_eq by lia.
    rewrite Hunit. ring.
Qed.

Lemma stratum_extract_unit
    (m d room : Z) :
  0 < m ->
  0 < d ->
  (d | m) ->
  0 <= room < m ->
  Z.gcd room m = m / d ->
  room = StratumLift m d (StratumProject m d room) /\
  0 <= StratumProject m d room < d /\
  Z.gcd (StratumProject m d room) d = 1.
Proof.
  intros Hm Hd Hdiv Hrange Hgcd.
  pose proof
    (positive_divisor_quotient_positive m d Hm Hd Hdiv) as Hq.
  pose proof
    (divisor_quotient_factorization m d Hd Hdiv) as Hfactor.
  set (q := m / d).
  set (unit := room / q).
  assert (Hqdiv : (q | room)).
  {
    pose proof (Z.gcd_divide_l room m) as Hgd.
    rewrite Hgcd in Hgd. exact Hgd.
  }
  assert (Hroom : room = q * unit).
  {
    unfold unit.
    apply Zdivide_Zdiv_eq; assumption.
  }
  assert (Hunit_range : 0 <= unit < d).
  {
    split.
    - unfold unit. apply Z.div_pos; lia.
    - rewrite Hroom in Hrange.
      rewrite Hfactor in Hrange.
      nia.
  }
  assert (Hunit : Z.gcd unit d = 1).
  {
    change (Z.gcd room m = q) in Hgcd.
    rewrite Hroom in Hgcd.
    replace m with (q * d) in Hgcd by
      (unfold q; symmetry; exact Hfactor).
    rewrite Z.gcd_mul_mono_l in Hgcd.
    rewrite Z.abs_eq in Hgcd by lia.
    apply (Z.mul_reg_l (Z.gcd unit d) 1 q); [lia |].
    rewrite Z.mul_1_r. exact Hgcd.
  }
  change
    (room = q * unit /\ 0 <= unit < d /\ Z.gcd unit d = 1).
  auto.
Qed.

Lemma stratum_project_lift
    (m d unit : Z) :
  0 < m ->
  0 < d ->
  (d | m) ->
  StratumProject m d (StratumLift m d unit) = unit.
Proof.
  intros Hm Hd Hdiv.
  pose proof
    (positive_divisor_quotient_positive m d Hm Hd Hdiv) as Hq.
  unfold StratumProject, StratumLift.
  rewrite Z.mul_comm.
  apply Z.div_mul. lia.
Qed.

Lemma stratum_lift_injective
    (m d left right : Z) :
  0 < m ->
  0 < d ->
  (d | m) ->
  StratumLift m d left = StratumLift m d right ->
  left = right.
Proof.
  intros Hm Hd Hdiv Hequal.
  unfold StratumLift in Hequal.
  apply (Z.mul_reg_l left right (m / d)); [| exact Hequal].
  pose proof
    (positive_divisor_quotient_positive m d Hm Hd Hdiv).
  lia.
Qed.

Lemma stratum_lift_mul_mod
    (m d unit x time : Z) :
  0 < m ->
  0 < d ->
  (d | m) ->
  0 <= time ->
  (StratumLift m d unit * x ^ time) mod m =
  StratumLift m d
    ((unit * (x mod d) ^ time) mod d).
Proof.
  intros Hm Hd Hdiv Htime.
  pose proof
    (positive_divisor_quotient_positive m d Hm Hd Hdiv) as Hq.
  pose proof
    (divisor_quotient_factorization m d Hd Hdiv) as Hfactor.
  set (q := m / d).
  change
    (((q * unit) * x ^ time) mod m =
     q * ((unit * (x mod d) ^ time) mod d)).
  replace m with (q * d) by
    (unfold q; symmetry; exact Hfactor).
  replace ((q * unit) * x ^ time)
    with (q * (unit * x ^ time)) by ring.
  rewrite Z.mul_mod_distr_l by lia.
  f_equal.
  rewrite <- (Z.mul_mod_idemp_r unit (x ^ time) d) by lia.
  rewrite <- (Z.mul_mod_idemp_r unit ((x mod d) ^ time) d) by lia.
  rewrite OE.pow_mod_base by lia.
  reflexivity.
Qed.

Lemma stratum_lift_orbit_hit
    (m d x unit representative : Z) :
  0 < m ->
  0 < d ->
  (d | m) ->
  OQ.OrbitHit d (x mod d) unit representative ->
  OQ.OrbitHit m x
    (StratumLift m d unit)
    (StratumLift m d representative).
Proof.
  intros Hm Hd Hdiv [time [Htime Hrepresentative]].
  exists time. split; [exact Htime |].
  rewrite stratum_lift_mul_mod by assumption.
  now rewrite Hrepresentative.
Qed.

Lemma stratum_lift_orbit_hit_inverse
    (m d x unit room : Z) :
  0 < m ->
  0 < d ->
  (d | m) ->
  OQ.OrbitHit m x (StratumLift m d unit) room ->
  exists quotient_room,
    room = StratumLift m d quotient_room /\
    OQ.OrbitHit d (x mod d) unit quotient_room.
Proof.
  intros Hm Hd Hdiv [time [Htime Hroom]].
  exists ((unit * (x mod d) ^ time) mod d).
  split.
  - rewrite Hroom.
    apply stratum_lift_mul_mod; assumption.
  - exists time. split; [exact Htime | reflexivity].
Qed.

Theorem coprime_stratum_orbit_compatibility
    (m d x unit representative : Z) :
  0 < m ->
  0 < d ->
  (d | m) ->
  Z.gcd x m = 1 ->
  OQ.OrbitHit d (x mod d) unit representative ->
  OQ.OrbitHit m x
    (StratumLift m d unit)
    (StratumLift m d representative).
Proof.
  intros Hm Hd Hdiv Hcoprime Hhit.
  pose proof
    (coprime_mod_positive_divisor m d x Hd Hdiv Hcoprime).
  apply stratum_lift_orbit_hit; assumption.
Qed.

Lemma lifted_representatives_length
    (m d : Z) (representatives : list Z) :
  length (LiftedRepresentatives m d representatives) =
  length representatives.
Proof. unfold LiftedRepresentatives. apply length_map. Qed.

Lemma lifted_representatives_zlength
    (m d : Z) (representatives : list Z) :
  Zlength (LiftedRepresentatives m d representatives) =
  Zlength representatives.
Proof.
  rewrite !Zlength_correct, lifted_representatives_length.
  reflexivity.
Qed.

(** A unit representative system is exactly the gcd-one stratum system in
    the quotient modulus.  Transporting it produces the gcd-[m/d] stratum
    system in the original modulus, preserving its cardinality. *)
Theorem transport_unit_stratum_system
    (m d x : Z) (unit_representatives : list Z) :
  0 < m ->
  1 < d ->
  (d | m) ->
  Z.gcd x m = 1 ->
  OQ.StratumRepresentativeSystem
    d (x mod d) 1 unit_representatives ->
  OQ.StratumRepresentativeSystem
    m x (m / d)
      (LiftedRepresentatives m d unit_representatives) /\
  Zlength (LiftedRepresentatives m d unit_representatives) =
    Zlength unit_representatives.
Proof.
  intros Hm Hd Hdiv Hcoprime Hsystem.
  pose proof
    (positive_divisor_quotient_positive m d Hm ltac:(lia) Hdiv) as Hq.
  pose proof
    (coprime_mod_positive_divisor m d x ltac:(lia) Hdiv Hcoprime)
    as Hxd.
  destruct Hsystem as (Hnodup & Hforall & Hcovers & Hseparated).
  split.
  - split.
    + unfold LiftedRepresentatives.
      apply OQ.nodup_map_on; [exact Hnodup |].
      intros left right _ _.
      apply stratum_lift_injective; try lia; assumption.
    + split.
      * unfold LiftedRepresentatives.
        apply Forall_map.
        rewrite Forall_forall in Hforall |- *.
        intros unit Hunit_in.
        destruct (Hforall unit Hunit_in) as [Hrange Hunit].
        apply stratum_lift_range_and_gcd; try lia; assumption.
      * split.
        -- intros start Hstart Hgcd.
           destruct
             (stratum_extract_unit m d start Hm ltac:(lia)
                Hdiv Hstart Hgcd)
             as [Hstart_lift [Hunit_range Hunit]].
           destruct (Hcovers (StratumProject m d start)
             Hunit_range Hunit)
             as [representative [Hrepresentative_in Hhit]].
           exists (StratumLift m d representative).
           split.
           ++ unfold LiftedRepresentatives.
              apply in_map. exact Hrepresentative_in.
           ++ rewrite Hstart_lift.
              apply stratum_lift_orbit_hit; try lia; assumption.
        -- intros left right room Hleft Hright Hleft_hit Hright_hit.
           unfold LiftedRepresentatives in Hleft, Hright.
           apply in_map_iff in Hleft.
           apply in_map_iff in Hright.
           destruct Hleft as [left_unit [Hleft Hleft_in]].
           destruct Hright as [right_unit [Hright Hright_in]].
           subst left right.
           destruct
             (stratum_lift_orbit_hit_inverse
               m d x left_unit room Hm ltac:(lia) Hdiv Hleft_hit)
             as [left_room [Hleft_room Hleft_unit_hit]].
           destruct
             (stratum_lift_orbit_hit_inverse
               m d x right_unit room Hm ltac:(lia) Hdiv Hright_hit)
             as [right_room [Hright_room Hright_unit_hit]].
           assert (left_room = right_room).
           {
             apply stratum_lift_injective with m d.
             - exact Hm.
             - lia.
             - exact Hdiv.
             - rewrite <- Hleft_room, <- Hright_room. reflexivity.
           }
           subst right_room.
           assert (left_unit = right_unit).
           {
             apply (Hseparated left_unit right_unit left_room);
               assumption.
           }
           subst right_unit. reflexivity.
  - apply lifted_representatives_zlength.
Qed.

(** Divisor one is the zero stratum: its sole unit residue is zero, and its
    lift is the unique room whose gcd with [m] is [m]. *)
Lemma divisor_one_lift_zero (m : Z) :
  StratumLift m 1 0 = 0.
Proof. unfold StratumLift. ring. Qed.

Theorem divisor_one_zero_stratum_transport
    (m x : Z) :
  0 < m ->
  OQ.StratumRepresentativeSystem
    m x (m / 1) (LiftedRepresentatives m 1 [0]) /\
  Zlength (LiftedRepresentatives m 1 [0]) = 1.
Proof.
  intros Hm.
  replace (m / 1) with m by (symmetry; apply Z.div_1_r).
  unfold LiftedRepresentatives, StratumLift.
  simpl. rewrite Z.mul_0_r.
  change
    (OQ.StratumRepresentativeSystem m x m [0] /\ Zlength [0] = 1).
  split.
  - apply OQ.zero_singleton_stratum_system. exact Hm.
  - reflexivity.
Qed.
End P090_GcdStratumTransport.
Export P090_GcdStratumTransport.

Module P090_DivisorCycleBridge.

Import ListNotations.
Local Open Scope Z_scope.


(** A concrete finite list of the positive divisors of [m].  The enumeration
    starts at one and ends at [m], so zero never reaches the remainder test. *)
Definition positive_divisor_list (m : Z) : list Z :=
  filter
    (fun d => Z.eqb (m mod d) 0)
    (map Z.of_nat (seq 1 (Z.to_nat m))).

Definition ConcreteNonUnitDivisorCycleSum (m x : Z) : Z :=
  fold_right Z.add 0
    (map (CycleTerm x)
      (filter (fun d => negb (Z.eqb d 1))
        (positive_divisor_list m))).

Definition RoomZeroCycleTotal (m x : Z) : Z :=
  1 + ConcreteNonUnitDivisorCycleSum m x.

Lemma positive_divisor_list_spec (m d : Z) :
  0 < m ->
  (In d (positive_divisor_list m) <->
   0 < d /\ d <= m /\ (d | m)).
Proof.
  intros Hm.
  unfold positive_divisor_list.
  rewrite filter_In.
  split.
  - intros [Hin Hmod].
    apply Z.eqb_eq in Hmod.
    apply in_map_iff in Hin.
    destruct Hin as [n [Hd Hn]].
    subst d.
    apply in_seq in Hn.
    assert (Hnpos : (0 < n)%nat) by lia.
    assert (Hnle : Z.of_nat n <= m).
    { replace m with (Z.of_nat (Z.to_nat m)) by
        (apply Z2Nat.id; lia).
      apply Nat2Z.inj_le. lia. }
    split; [lia |].
    split; [exact Hnle |].
    apply Z.mod_divide; [lia | exact Hmod].
  - intros [Hd [Hdm Hdiv]].
    split.
    + apply in_map_iff.
      exists (Z.to_nat d).
      split.
      * rewrite Z2Nat.id by lia. reflexivity.
      * apply in_seq.
        split.
        -- apply Nat2Z.inj_le. simpl.
           rewrite Z2Nat.id by lia. lia.
        -- assert (Hdz : Z.of_nat (Z.to_nat d) = d) by
             (apply Z2Nat.id; lia).
           assert (Hmz : Z.of_nat (Z.to_nat m) = m) by
             (apply Z2Nat.id; lia).
           apply (proj2 (Nat2Z.inj_lt _ _)).
           rewrite Nat2Z.inj_add.
           change (Z.of_nat (Z.to_nat d) <
             1 + Z.of_nat (Z.to_nat m)).
           rewrite Hdz, Hmz, Z.add_1_l.
           apply (proj2 (Z.lt_succ_r d m)). exact Hdm.
    + apply Z.eqb_eq.
      apply Z.mod_divide; [lia | exact Hdiv].
Qed.

Lemma positive_divisor_list_nodup (m : Z) :
  NoDup (positive_divisor_list m).
Proof.
  unfold positive_divisor_list.
  apply NoDup_filter.
  apply FinFun.Injective_map_NoDup.
  - intros a b Hab. apply Nat2Z.inj. exact Hab.
  - apply seq_NoDup.
Qed.

Lemma valid_factor_table_m_positive (m : Z) (pr pe : list Z) :
  ValidFactorTable m pr pe -> 0 < m.
Proof.
  intros Hvalid.
  pose proof (valid_factor_table_canonical m pr pe Hvalid) as Hcanonical.
  destruct Hvalid as (_ & _ & Hproduct & _ & _).
  rewrite Hproduct.
  apply canonical_factor_product_positive.
  exact Hcanonical.
Qed.

Theorem valid_factor_table_divisor_permutation
    (m : Z) (pr pe : list Z) :
  ValidFactorTable m pr pe ->
  Permutation (enumerated_products pr pe) (positive_divisor_list m).
Proof.
  intros Hvalid.
  apply NoDup_Permutation.
  - apply valid_factor_table_enumerated_products_nodup with m.
    exact Hvalid.
  - apply positive_divisor_list_nodup.
  - intros d.
    rewrite (valid_factor_table_exact_positive_divisor_bijection
      m pr pe d Hvalid).
    rewrite positive_divisor_list_spec by
      (eapply valid_factor_table_m_positive; eauto).
    split.
    + intros [Hd Hdiv].
      split; [exact Hd |].
      split; [| exact Hdiv].
      eapply Z.divide_pos_le.
      * eapply valid_factor_table_m_positive; eauto.
      * exact Hdiv.
    + intros [Hd [_ Hdiv]]. exact (conj Hd Hdiv).
Qed.

Lemma permutation_fold_right_add (xs ys : list Z) :
  Permutation xs ys ->
  fold_right Z.add 0 xs = fold_right Z.add 0 ys.
Proof.
  intros Hperm.
  induction Hperm; simpl; lia.
Qed.

Lemma permutation_filter_bool
    {A : Type} (keep : A -> bool) (xs ys : list A) :
  Permutation xs ys ->
  Permutation (filter keep xs) (filter keep ys).
Proof.
  intros Hperm.
  induction Hperm; simpl.
  - apply Permutation_refl.
  - destruct (keep x); simpl.
    + apply perm_skip. exact IHHperm.
    + exact IHHperm.
  - destruct (keep x), (keep y); simpl;
      try apply perm_swap; apply Permutation_refl.
  - eapply Permutation_trans; eauto.
Qed.

Lemma divisor_permutation_nonunit_cycle_sum
    (m x : Z) (pr pe : list Z) :
  ValidFactorTable m pr pe ->
  NonUnitDivisorCycleSum pr pe x =
  ConcreteNonUnitDivisorCycleSum m x.
Proof.
  intros Hvalid.
  unfold NonUnitDivisorCycleSum, ConcreteNonUnitDivisorCycleSum.
  apply permutation_fold_right_add.
  apply Permutation_map.
  apply permutation_filter_bool.
  apply valid_factor_table_divisor_permutation.
  exact Hvalid.
Qed.

Theorem walk_suffix_is_concrete_nonunit_divisor_cycle_sum
    (m x : Z) (pr pe : list Z) :
  ValidFactorTable m pr pe ->
  WalkSuffix pr pe x 0 1 =
  ConcreteNonUnitDivisorCycleSum m x.
Proof.
  intros Hvalid.
  rewrite walk_suffix_zero_is_nonunit_cycle_sum.
  apply divisor_permutation_nonunit_cycle_sum.
  exact Hvalid.
Qed.

Theorem concrete_nonunit_divisor_cycle_budget
    (m x : Z) (pr pe : list Z) :
  ValidFactorTable m pr pe ->
  WalkBudget m 0 (ConcreteNonUnitDivisorCycleSum m x).
Proof.
  intros Hvalid.
  rewrite <- (walk_suffix_is_concrete_nonunit_divisor_cycle_sum
    m x pr pe Hvalid).
  apply valid_factor_table_initial_walk_budget.
  exact Hvalid.
Qed.

Theorem room_zero_final_decomposition
    (m x : Z) (pr pe : list Z) :
  ValidFactorTable m pr pe ->
  1 + WalkSuffix pr pe x 0 1 = RoomZeroCycleTotal m x.
Proof.
  intros Hvalid.
  unfold RoomZeroCycleTotal.
  now rewrite (walk_suffix_is_concrete_nonunit_divisor_cycle_sum
    m x pr pe Hvalid).
Qed.

(** The concrete list contains divisor one, but [CycleTerm] assigns it zero.
    This is the exact full-divisor formulation of the same walk sum. *)
Theorem walk_suffix_is_concrete_full_divisor_cycle_sum
    (m x : Z) (pr pe : list Z) :
  ValidFactorTable m pr pe ->
  WalkSuffix pr pe x 0 1 =
  fold_right Z.add 0
    (map (CycleTerm x) (positive_divisor_list m)).
Proof.
  intros Hvalid.
  rewrite (walk_suffix_is_concrete_nonunit_divisor_cycle_sum
    m x pr pe Hvalid).
  unfold ConcreteNonUnitDivisorCycleSum.
  symmetry.
  apply fold_filter_cycle_term_one.
Qed.

Corollary room_zero_full_divisor_decomposition
    (m x : Z) (pr pe : list Z) :
  ValidFactorTable m pr pe ->
  1 + WalkSuffix pr pe x 0 1 =
  1 + fold_right Z.add 0
    (map (CycleTerm x) (positive_divisor_list m)).
Proof.
  intros Hvalid.
  now rewrite (walk_suffix_is_concrete_full_divisor_cycle_sum
    m x pr pe Hvalid).
Qed.
End P090_DivisorCycleBridge.
Export P090_DivisorCycleBridge.

Module P090_GlobalOrbitBridge.

Import ListNotations.
Local Open Scope Z_scope.


(** This alignment predicate is the reusable consumer interface for later
    stratum constructors.  It asks only for a proved representative system
    at each gcd value; it does not prescribe how that system was built. *)
Definition AlignedStratumSystems
    (m x : Z) (gcd_values : list Z) (blocks : list (list Z)) : Prop :=
  Forall2
    (fun gcd_value representatives =>
       StratumRepresentativeSystem m x gcd_value representatives)
    gcd_values blocks.

Definition ExactNonUnitDivisorSystems
    (m x : Z) (divisors : list Z) (blocks : list (list Z)) : Prop :=
  Forall2
    (fun divisor representatives =>
       1 < divisor /\
       (divisor | m) /\
       StratumRepresentativeSystem
         m x (m / divisor) representatives /\
       Zlength representatives = CycleTerm x divisor)
    divisors blocks.

Definition ExactZeroStratumSystem
    (m x : Z) (zero_block : list Z) : Prop :=
  StratumRepresentativeSystem m x m zero_block /\
  Zlength zero_block = 1.

(** Every room is classified either into the zero gcd stratum [m], or into
    one of the explicitly supplied nonunit divisor strata. *)
Definition DivisorStrataClassify
    (m : Z) (divisors : list Z) : Prop :=
  forall start,
    0 <= start < m ->
    Z.gcd start m = m \/
    exists divisor,
      In divisor divisors /\
      Z.gcd start m = m / divisor.

Definition DistinctGlobalStratumKeys
    (m : Z) (divisors : list Z) : Prop :=
  NoDup (m :: map (fun divisor => m / divisor) divisors).

Lemma exact_nonunit_systems_aligned
    (m x : Z) (divisors : list Z) (blocks : list (list Z)) :
  ExactNonUnitDivisorSystems m x divisors blocks ->
  AlignedStratumSystems
    m x (map (fun divisor => m / divisor) divisors) blocks.
Proof.
  intros Hsystems.
  induction Hsystems as
      [| divisor representatives divisors blocks Hhead Htail IH].
  - constructor.
  - constructor; [exact (proj1 (proj2 (proj2 Hhead))) | exact IH].
Qed.

Lemma exact_nonunit_blocks_length
    (m x : Z) (divisors : list Z) (blocks : list (list Z)) :
  ExactNonUnitDivisorSystems m x divisors blocks ->
  Zlength (concat blocks) =
  fold_right Z.add 0 (map (CycleTerm x) divisors).
Proof.
  intros Hsystems.
  induction Hsystems as
      [| divisor representatives divisors blocks Hhead Htail IH].
  - reflexivity.
  - simpl.
    rewrite Zlength_app, IH.
    rewrite (proj2 (proj2 (proj2 Hhead))).
    reflexivity.
Qed.

Lemma aligned_system_member_has_key
    (m x room : Z) (keys : list Z) (blocks : list (list Z)) :
  AlignedStratumSystems m x keys blocks ->
  In room (concat blocks) ->
  exists key,
    In key keys /\ Z.gcd room m = key.
Proof.
  intros Hsystems.
  induction Hsystems as
      [| key representatives keys blocks Hsystem Htail IH];
    intros Hroom.
  - contradiction.
  - simpl in Hroom.
    apply in_app_or in Hroom.
    destruct Hroom as [Hhead | Htail_room].
    + exists key. split; [simpl; auto |].
      destruct Hsystem as (_ & Hrange & _).
      rewrite Forall_forall in Hrange.
      exact (proj2 (Hrange room Hhead)).
    + destruct (IH Htail_room) as [tail_key [Hin Hgcd]].
      exists tail_key. split; [simpl; auto | exact Hgcd].
Qed.

Lemma aligned_systems_concat_forall_range
    (m x : Z) (keys : list Z) (blocks : list (list Z)) :
  AlignedStratumSystems m x keys blocks ->
  Forall (fun room => 0 <= room < m) (concat blocks).
Proof.
  intros Hsystems.
  induction Hsystems as
      [| key representatives keys blocks Hsystem Htail IH].
  - constructor.
  - simpl. apply Forall_app. split.
    + destruct Hsystem as (_ & Hrange & _).
      eapply Forall_impl; [| exact Hrange].
      intros room Hroom. exact (proj1 Hroom).
    + exact IH.
Qed.

Lemma aligned_systems_concat_nodup
    (m x : Z) (keys : list Z) (blocks : list (list Z)) :
  NoDup keys ->
  AlignedStratumSystems m x keys blocks ->
  NoDup (concat blocks).
Proof.
  intros Hkeys Hsystems.
  revert Hkeys.
  induction Hsystems as
      [| key representatives keys blocks Hsystem Htail IH];
    intros Hkeys.
  - constructor.
  - inversion Hkeys as [| ? ? Hkey_notin Hkeys_tail]; subst.
    simpl. apply NoDup_app.
    + exact (proj1 Hsystem).
    + apply IH. exact Hkeys_tail.
    + intros room Hhead Htail_room.
      destruct Hsystem as (_ & Hrange & _).
      rewrite Forall_forall in Hrange.
      pose proof (proj2 (Hrange room Hhead)) as Hroom_key.
      destruct
        (aligned_system_member_has_key
           m x room keys blocks Htail Htail_room)
        as [tail_key [Htail_key Hroom_tail_key]].
      apply Hkey_notin. rewrite <- Hroom_key, Hroom_tail_key.
      exact Htail_key.
Qed.

Lemma orbit_hit_preserves_gcd_key
    (m x start room key : Z) :
  0 < m ->
  Z.gcd x m = 1 ->
  Z.gcd start m = key ->
  OrbitHit m x start room ->
  Z.gcd room m = key.
Proof.
  intros Hm Hxm Hstart [time [Htime Hroom]].
  subst room.
  rewrite P090_WalkFoundations.gcd_stratum_preserved by assumption.
  exact Hstart.
Qed.

Lemma aligned_systems_concat_separated
    (m x : Z) (keys : list Z) (blocks : list (list Z)) :
  0 < m ->
  Z.gcd x m = 1 ->
  NoDup keys ->
  AlignedStratumSystems m x keys blocks ->
  OrbitSeparated m x (concat blocks).
Proof.
  intros Hm Hxm Hkeys Hsystems.
  revert Hkeys.
  induction Hsystems as
      [| key representatives keys blocks Hsystem Htail IH];
    intros Hkeys left right room Hleft Hright Hleft_hit Hright_hit.
  - contradiction.
  - inversion Hkeys as [| ? ? Hkey_notin Hkeys_tail]; subst.
    simpl in Hleft, Hright.
    apply in_app_or in Hleft.
    apply in_app_or in Hright.
    destruct Hleft as [Hleft_head | Hleft_tail];
      destruct Hright as [Hright_head | Hright_tail].
    + destruct Hsystem as (_ & _ & _ & Hseparated).
      eapply Hseparated; eauto.
    + destruct Hsystem as (_ & Hhead_range & _).
      rewrite Forall_forall in Hhead_range.
      pose proof (proj2 (Hhead_range left Hleft_head)) as Hleft_key.
      destruct
        (aligned_system_member_has_key
           m x right keys blocks Htail Hright_tail)
        as [right_key [Hright_key_in Hright_key]].
      assert (Hroom_left : Z.gcd room m = key).
      { eapply orbit_hit_preserves_gcd_key; eauto. }
      assert (Hroom_right : Z.gcd room m = right_key).
      { eapply orbit_hit_preserves_gcd_key; eauto. }
      exfalso. apply Hkey_notin.
      rewrite <- Hroom_left, Hroom_right. exact Hright_key_in.
    + destruct Hsystem as (_ & Hhead_range & _).
      rewrite Forall_forall in Hhead_range.
      pose proof (proj2 (Hhead_range right Hright_head)) as Hright_key.
      destruct
        (aligned_system_member_has_key
           m x left keys blocks Htail Hleft_tail)
        as [left_key [Hleft_key_in Hleft_key]].
      assert (Hroom_left : Z.gcd room m = left_key).
      { eapply orbit_hit_preserves_gcd_key; eauto. }
      assert (Hroom_right : Z.gcd room m = key).
      { eapply orbit_hit_preserves_gcd_key; eauto. }
      exfalso. apply Hkey_notin.
      rewrite <- Hroom_right, Hroom_left. exact Hleft_key_in.
    + eapply IH; eauto.
Qed.

Lemma aligned_system_for_key
    (m x key : Z) (keys : list Z) (blocks : list (list Z)) :
  NoDup keys ->
  AlignedStratumSystems m x keys blocks ->
  In key keys ->
  exists representatives,
    In representatives blocks /\
    StratumRepresentativeSystem m x key representatives.
Proof.
  intros Hnodup Hsystems.
  induction Hsystems as
      [| head representatives keys blocks Hhead Htail IH];
    intros Hkey.
  - contradiction.
  - inversion Hnodup as [| ? ? Hnotin Hnodup_tail]; subst.
    simpl in Hkey.
    destruct Hkey as [-> | Hkey_tail].
    + exists representatives. split; [simpl; auto | exact Hhead].
    + destruct (IH Hnodup_tail Hkey_tail) as [block [Hin Hsystem]].
      exists block. split; [simpl; auto | exact Hsystem].
Qed.

Lemma global_cover_from_strata
    (m x : Z) (keys : list Z) (blocks : list (list Z)) :
  NoDup keys ->
  AlignedStratumSystems m x keys blocks ->
  (forall start, 0 <= start < m -> In (Z.gcd start m) keys) ->
  OrbitCoversRange m x (concat blocks).
Proof.
  intros Hkeys Hsystems Hclassify start Hstart.
  destruct
    (aligned_system_for_key
       m x (Z.gcd start m) keys blocks
       Hkeys Hsystems (Hclassify start Hstart))
    as [representatives [Hblock Hsystem]].
  destruct Hsystem as (_ & _ & Hcover & _).
  destruct (Hcover start Hstart eq_refl)
    as [representative [Hin Hhit]].
  exists representative. split; [| exact Hhit].
  apply in_concat. exists representatives. split; assumption.
Qed.

Theorem aligned_strata_form_global_representative_system
    (m x : Z) (keys : list Z) (blocks : list (list Z)) :
  0 < m ->
  Z.gcd x m = 1 ->
  NoDup keys ->
  AlignedStratumSystems m x keys blocks ->
  (forall start, 0 <= start < m -> In (Z.gcd start m) keys) ->
  OrbitRepresentativeSystem m x (concat blocks).
Proof.
  intros Hm Hxm Hkeys Hsystems Hclassify.
  split.
  - eapply aligned_systems_concat_nodup; eauto.
  - split.
    + exact
        (aligned_systems_concat_forall_range
           m x keys blocks Hsystems).
    + split.
      * eapply global_cover_from_strata; eauto.
      * eapply aligned_systems_concat_separated; eauto.
Qed.

Lemma divisor_classification_gives_key_membership
    (m : Z) (divisors : list Z) :
  DivisorStrataClassify m divisors ->
  forall start,
    0 <= start < m ->
    In (Z.gcd start m)
      (m :: map (fun divisor => m / divisor) divisors).
Proof.
  intros Hclassify start Hstart.
  destruct (Hclassify start Hstart) as [Hzero | Hnonunit].
  - simpl; auto.
  - destruct Hnonunit as [divisor [Hin Hgcd]].
    right. apply in_map_iff.
    exists divisor. split; [symmetry; exact Hgcd | exact Hin].
Qed.

Theorem exact_divisor_strata_global_system
    (m x : Z) (divisors : list Z)
    (zero_block : list Z) (nonunit_blocks : list (list Z)) :
  0 < m ->
  Z.gcd x m = 1 ->
  ExactZeroStratumSystem m x zero_block ->
  ExactNonUnitDivisorSystems m x divisors nonunit_blocks ->
  DistinctGlobalStratumKeys m divisors ->
  DivisorStrataClassify m divisors ->
  OrbitRepresentativeSystem
    m x (zero_block ++ concat nonunit_blocks) /\
  Zlength (zero_block ++ concat nonunit_blocks) =
    1 + fold_right Z.add 0
      (map (CycleTerm x) divisors).
Proof.
  intros Hm Hxm [Hzero Hzero_length] Hnonunit Hkeys Hclassify.
  assert (Haligned_nonunit :
      AlignedStratumSystems
        m x (map (fun divisor => m / divisor) divisors)
        nonunit_blocks).
  { apply exact_nonunit_systems_aligned. exact Hnonunit. }
  assert (Haligned_global :
      AlignedStratumSystems
        m x (m :: map (fun divisor => m / divisor) divisors)
        (zero_block :: nonunit_blocks)).
  { constructor; assumption. }
  split.
  - change
      (OrbitRepresentativeSystem
         m x (concat (zero_block :: nonunit_blocks))).
    apply aligned_strata_form_global_representative_system with
      (keys := m :: map (fun divisor => m / divisor) divisors);
      try assumption.
    apply divisor_classification_gives_key_membership.
    exact Hclassify.
  - rewrite Zlength_app, Hzero_length.
    rewrite (exact_nonunit_blocks_length
      m x divisors nonunit_blocks Hnonunit).
    reflexivity.
Qed.

Theorem exact_divisor_strata_imply_spec
    (m x : Z) (divisors : list Z)
    (zero_block : list Z) (nonunit_blocks : list (list Z)) :
  0 < m ->
  Z.gcd x m = 1 ->
  ExactZeroStratumSystem m x zero_block ->
  ExactNonUnitDivisorSystems m x divisors nonunit_blocks ->
  DistinctGlobalStratumKeys m divisors ->
  DivisorStrataClassify m divisors ->
  Spec m x
    (1 + fold_right Z.add 0
      (map (CycleTerm x) divisors)).
Proof.
  intros Hm Hxm Hzero Hnonunit Hkeys Hclassify.
  destruct
    (exact_divisor_strata_global_system
       m x divisors zero_block nonunit_blocks
       Hm Hxm Hzero Hnonunit Hkeys Hclassify)
    as [Hsystem Hlength].
  set (cycle_count :=
    fold_right Z.add 0 (map (CycleTerm x) divisors)).
  replace (1 + cycle_count) with (cycle_count + 1) by ring.
  apply representative_system_implies_spec with
    (representatives := zero_block ++ concat nonunit_blocks).
  - exact Hsystem.
  - lia.
Qed.

Theorem exact_divisor_strata_global_bounds
    (m x : Z) (divisors : list Z)
    (zero_block : list Z) (nonunit_blocks : list (list Z)) :
  0 < m ->
  Z.gcd x m = 1 ->
  ExactZeroStratumSystem m x zero_block ->
  ExactNonUnitDivisorSystems m x divisors nonunit_blocks ->
  DistinctGlobalStratumKeys m divisors ->
  DivisorStrataClassify m divisors ->
  let traps := zero_block ++ concat nonunit_blocks in
  NoDup traps /\
  CatchesAll m x traps /\
  Zlength traps =
    1 + fold_right Z.add 0
      (map (CycleTerm x) divisors) /\
  (forall other,
      CatchesAll m x other ->
      Zlength traps <= Zlength other).
Proof.
  intros Hm Hxm Hzero Hnonunit Hkeys Hclassify traps.
  destruct
    (exact_divisor_strata_global_system
       m x divisors zero_block nonunit_blocks
       Hm Hxm Hzero Hnonunit Hkeys Hclassify)
    as [Hsystem Hlength].
  split.
  - exact (proj1 Hsystem).
  - split.
    + apply representative_system_catches_all. exact Hsystem.
    + split; [exact Hlength |].
      intros other Hother.
      eapply representative_system_zlength_lower_bound; eauto.
Qed.

(** Specialisation to the exact divisor list used by the executable walk.
    The later transport/partition modules need only instantiate the four
    explicit interfaces above; all concatenation, disjointness, counting,
    catching, and universal lower-bound work is complete here. *)
Corollary concrete_divisor_strata_imply_spec
    (m x : Z) (zero_block : list Z)
    (nonunit_blocks : list (list Z)) :
  let divisors :=
    filter (fun d => negb (Z.eqb d 1)) (positive_divisor_list m) in
  0 < m ->
  Z.gcd x m = 1 ->
  ExactZeroStratumSystem m x zero_block ->
  ExactNonUnitDivisorSystems m x divisors nonunit_blocks ->
  DistinctGlobalStratumKeys m divisors ->
  DivisorStrataClassify m divisors ->
  Spec m x (RoomZeroCycleTotal m x).
Proof.
  intros divisors Hm Hxm Hzero Hnonunit Hkeys Hclassify.
  unfold RoomZeroCycleTotal, ConcreteNonUnitDivisorCycleSum.
  apply exact_divisor_strata_imply_spec with zero_block nonunit_blocks;
    assumption.
Qed.
End P090_GlobalOrbitBridge.
Export P090_GlobalOrbitBridge.

Module P090_DivisorStrataKeys.

Import ListNotations.
Local Open Scope Z_scope.


Definition concrete_nonunit_divisors (m : Z) : list Z :=
  filter (fun divisor => negb (Z.eqb divisor 1))
    (positive_divisor_list m).

Lemma concrete_nonunit_divisor_spec
    (m divisor : Z) :
  0 < m ->
  (In divisor (concrete_nonunit_divisors m) <->
   1 < divisor /\ divisor <= m /\ (divisor | m)).
Proof.
  intros Hm.
  unfold concrete_nonunit_divisors.
  rewrite filter_In, positive_divisor_list_spec by exact Hm.
  split.
  - intros [[Hpositive [Hle Hdivide]] Hnotone].
    apply Bool.negb_true_iff in Hnotone.
    apply Z.eqb_neq in Hnotone.
    split; [lia |]. split; assumption.
  - intros [Htwo [Hle Hdivide]].
    split.
    + split; [lia |]. split; assumption.
    + apply Bool.negb_true_iff, Z.eqb_neq. lia.
Qed.

Lemma concrete_nonunit_divisors_nodup (m : Z) :
  NoDup (concrete_nonunit_divisors m).
Proof.
  unfold concrete_nonunit_divisors.
  apply NoDup_filter, positive_divisor_list_nodup.
Qed.

Lemma positive_divisor_exact_product
    (m divisor : Z) :
  0 < divisor ->
  (divisor | m) ->
  m = divisor * (m / divisor).
Proof.
  intros Hdivisor Hdivide.
  apply Z.div_exact; [lia |].
  apply Z.mod_divide; [lia | exact Hdivide].
Qed.

Lemma positive_divisor_quotient_positive
    (m divisor : Z) :
  0 < m ->
  0 < divisor ->
  (divisor | m) ->
  0 < m / divisor.
Proof.
  intros Hm Hdivisor Hdivide.
  apply Z.div_str_pos.
  split; [exact Hdivisor |].
  eapply Z.divide_pos_le; eauto.
Qed.

Lemma positive_divisor_quotient_injective
    (m left right : Z) :
  0 < m ->
  0 < left ->
  0 < right ->
  (left | m) ->
  (right | m) ->
  m / left = m / right ->
  left = right.
Proof.
  intros Hm Hleft Hright Hleft_div Hright_div Hquotient.
  pose proof
    (positive_divisor_exact_product m left Hleft Hleft_div)
    as Hleft_product.
  pose proof
    (positive_divisor_exact_product m right Hright Hright_div)
    as Hright_product.
  assert (Hquotient_positive : 0 < m / left).
  { eapply positive_divisor_quotient_positive; eauto. }
  rewrite Hquotient in Hleft_product.
  nia.
Qed.

Lemma concrete_nonunit_key_positive
    (m divisor : Z) :
  0 < m ->
  In divisor (concrete_nonunit_divisors m) ->
  0 < m / divisor.
Proof.
  intros Hm Hin.
  apply concrete_nonunit_divisor_spec in Hin; [| exact Hm].
  destruct Hin as [Hdivisor [_ Hdivide]].
  eapply positive_divisor_quotient_positive; eauto; lia.
Qed.

Lemma concrete_nonunit_key_nonzero
    (m divisor : Z) :
  0 < m ->
  In divisor (concrete_nonunit_divisors m) ->
  m / divisor <> 0.
Proof.
  intros Hm Hin.
  pose proof (concrete_nonunit_key_positive m divisor Hm Hin).
  lia.
Qed.

Lemma concrete_nonunit_keys_pairwise_distinct
    (m left right : Z) :
  0 < m ->
  In left (concrete_nonunit_divisors m) ->
  In right (concrete_nonunit_divisors m) ->
  m / left = m / right ->
  left = right.
Proof.
  intros Hm Hleft Hright Hkeys.
  apply concrete_nonunit_divisor_spec in Hleft; [| exact Hm].
  apply concrete_nonunit_divisor_spec in Hright; [| exact Hm].
  destruct Hleft as [Hleft_pos [_ Hleft_div]].
  destruct Hright as [Hright_pos [_ Hright_div]].
  eapply positive_divisor_quotient_injective; eauto; lia.
Qed.

Lemma concrete_nonunit_key_distinct_from_zero_key
    (m divisor : Z) :
  0 < m ->
  In divisor (concrete_nonunit_divisors m) ->
  m / divisor <> m.
Proof.
  intros Hm Hin Hequal.
  apply concrete_nonunit_divisor_spec in Hin; [| exact Hm].
  destruct Hin as [Hdivisor [_ Hdivide]].
  pose proof
    (positive_divisor_exact_product m divisor ltac:(lia) Hdivide)
    as Hproduct.
  rewrite Hequal in Hproduct.
  nia.
Qed.

Theorem concrete_distinct_global_stratum_keys
    (m : Z) :
  0 < m ->
  DistinctGlobalStratumKeys m (concrete_nonunit_divisors m).
Proof.
  intros Hm.
  unfold DistinctGlobalStratumKeys.
  constructor.
  - intros Hin.
    apply in_map_iff in Hin.
    destruct Hin as [divisor [Hkey Hin]].
    eapply concrete_nonunit_key_distinct_from_zero_key;
      [exact Hm | exact Hin |].
    exact Hkey.
  - apply nodup_map_on.
    + apply concrete_nonunit_divisors_nodup.
    + intros left right Hleft Hright Hkeys.
      eapply concrete_nonunit_keys_pairwise_distinct; eauto.
Qed.

Lemma gcd_positive_with_positive_modulus
    (room m : Z) :
  0 < m ->
  0 < Z.gcd room m.
Proof.
  intros Hm.
  pose proof (Z.gcd_nonneg room m) as Hnonnegative.
  destruct (Z.eq_dec (Z.gcd room m) 0) as [Hzero | Hnonzero]; [| lia].
  apply Z.gcd_eq_0 in Hzero. lia.
Qed.

Lemma gcd_quotient_is_positive_divisor
    (room m : Z) :
  0 < m ->
  let gcd_value := Z.gcd room m in
  let divisor := m / gcd_value in
  0 < divisor /\ divisor <= m /\ (divisor | m) /\
  m / divisor = gcd_value.
Proof.
  intros Hm gcd_value divisor.
  assert (Hgcd_positive : 0 < gcd_value).
  { unfold gcd_value. apply gcd_positive_with_positive_modulus. exact Hm. }
  assert (Hgcd_divides : (gcd_value | m)).
  { unfold gcd_value. apply Z.gcd_divide_r. }
  assert (Hgcd_le : gcd_value <= m).
  { eapply Z.divide_pos_le; eauto. }
  assert (Hdivisor_positive : 0 < divisor).
  { unfold divisor. apply Z.div_str_pos. lia. }
  assert (Hm_product : m = gcd_value * divisor).
  {
    unfold divisor.
    apply positive_divisor_exact_product; assumption.
  }
  repeat split; try assumption.
  - eapply Z.divide_pos_le.
    + exact Hm.
    + exists gcd_value. rewrite Hm_product. ring.
  - exists gcd_value. rewrite Hm_product. ring.
  - rewrite Hm_product.
    rewrite Z.div_mul by lia.
    reflexivity.
Qed.

Lemma gcd_equal_modulus_room_zero
    (room m : Z) :
  0 < m ->
  0 <= room < m ->
  Z.gcd room m = m ->
  room = 0.
Proof.
  intros Hm Hroom Hgcd.
  pose proof (Z.gcd_divide_l room m) as Hdivide.
  rewrite Hgcd in Hdivide.
  pose proof (proj2 (Z.mod_divide room m ltac:(lia)) Hdivide)
    as Hmod.
  rewrite Z.mod_small in Hmod by exact Hroom.
  exact Hmod.
Qed.

Lemma gcd_quotient_nonunit_when_not_zero_stratum
    (room m : Z) :
  0 < m ->
  Z.gcd room m <> m ->
  1 < m / Z.gcd room m.
Proof.
  intros Hm Hnotzero.
  destruct (gcd_quotient_is_positive_divisor room m Hm)
    as [Hpositive [_ [_ Hquotient]]].
  assert (m / Z.gcd room m <> 1).
  {
    intro Hone.
    assert (Hm_product :
        m = Z.gcd room m * (m / Z.gcd room m)).
    {
      apply positive_divisor_exact_product.
      - apply gcd_positive_with_positive_modulus; exact Hm.
      - apply Z.gcd_divide_r.
    }
    rewrite Hone, Z.mul_1_r in Hm_product.
    apply Hnotzero. symmetry. exact Hm_product.
  }
  lia.
Qed.

Theorem concrete_divisor_strata_classify
    (m : Z) :
  0 < m ->
  DivisorStrataClassify m (concrete_nonunit_divisors m).
Proof.
  intros Hm room Hroom.
  destruct (Z.eq_dec (Z.gcd room m) m) as [Hzero | Hnonzero].
  - left. exact Hzero.
  - right.
    set (divisor := m / Z.gcd room m).
    exists divisor. split.
    + apply concrete_nonunit_divisor_spec; [exact Hm |].
      destruct (gcd_quotient_is_positive_divisor room m Hm)
        as [Hpositive [Hle [Hdivide Hkey]]].
      split.
      * unfold divisor.
        apply gcd_quotient_nonunit_when_not_zero_stratum; assumption.
      * split; assumption.
    + unfold divisor.
      destruct (gcd_quotient_is_positive_divisor room m Hm)
        as [_ [_ [_ Hkey]]].
      symmetry. exact Hkey.
Qed.

Lemma concrete_nonunit_stratum_divisor_unique
    (m room left right : Z) :
  0 < m ->
  In left (concrete_nonunit_divisors m) ->
  In right (concrete_nonunit_divisors m) ->
  Z.gcd room m = m / left ->
  Z.gcd room m = m / right ->
  left = right.
Proof.
  intros Hm Hleft Hright Hleft_key Hright_key.
  eapply concrete_nonunit_keys_pairwise_distinct; eauto.
  rewrite <- Hleft_key, <- Hright_key. reflexivity.
Qed.

(** These are exactly the two concrete, purely arithmetic premises consumed
    by [concrete_divisor_strata_imply_spec].  Later orbit modules therefore
    need only supply the exact per-stratum representative systems. *)
Theorem concrete_divisor_strata_key_premises
    (m : Z) :
  0 < m ->
  let divisors :=
    filter (fun d => negb (Z.eqb d 1)) (positive_divisor_list m) in
  DistinctGlobalStratumKeys m divisors /\
  DivisorStrataClassify m divisors.
Proof.
  intros Hm divisors.
  change
    (DistinctGlobalStratumKeys m (concrete_nonunit_divisors m) /\
     DivisorStrataClassify m (concrete_nonunit_divisors m)).
  split.
  - apply concrete_distinct_global_stratum_keys. exact Hm.
  - apply concrete_divisor_strata_classify. exact Hm.
Qed.
End P090_DivisorStrataKeys.
Export P090_DivisorStrataKeys.

Module P090_FinalOrbitInstantiation.

Import ListNotations.
Local Open Scope Z_scope.


Definition ConcreteZeroBlock (m : Z) : list Z :=
  LiftedRepresentatives m 1 [0].

Definition ConcreteNonUnitBlock
    (m x divisor : Z) : list Z :=
  LiftedRepresentatives m divisor
    (UnitRepresentatives divisor (x mod divisor)).

Definition ConcreteNonUnitBlocks
    (m x : Z) : list (list Z) :=
  map (ConcreteNonUnitBlock m x)
    (concrete_nonunit_divisors m).

Lemma coprime_with_positive_divisor
    (m x divisor : Z) :
  Z.gcd x m = 1 ->
  (divisor | m) ->
  Z.gcd x divisor = 1.
Proof.
  intros Hxm Hdivide.
  apply Zgcd_1_rel_prime.
  apply rel_prime_sym.
  eapply rel_prime_div.
  - apply rel_prime_sym, Zgcd_1_rel_prime. exact Hxm.
  - exact Hdivide.
Qed.

Lemma concrete_zero_block_exact
    (m x : Z) :
  0 < m ->
  ExactZeroStratumSystem m x (ConcreteZeroBlock m).
Proof.
  intros Hm.
  unfold ExactZeroStratumSystem, ConcreteZeroBlock.
  destruct (divisor_one_zero_stratum_transport m x Hm)
    as [Hsystem Hlength].
  replace (m / 1) with m in Hsystem by
    (symmetry; apply Z.div_1_r).
  split.
  - exact Hsystem.
  - exact Hlength.
Qed.

Lemma concrete_nonunit_block_exact
    (m x divisor : Z) :
  0 < m ->
  Z.gcd x m = 1 ->
  In divisor (concrete_nonunit_divisors m) ->
  1 < divisor /\
  (divisor | m) /\
  P090_OrbitQuotient.StratumRepresentativeSystem
    m x (m / divisor) (ConcreteNonUnitBlock m x divisor) /\
  Zlength (ConcreteNonUnitBlock m x divisor) =
    CycleTerm x divisor.
Proof.
  intros Hm Hxm Hin.
  apply concrete_nonunit_divisor_spec in Hin; [| exact Hm].
  destruct Hin as [Hdivisor [Hdivisor_le Hdivide]].
  assert (Hxd : Z.gcd x divisor = 1).
  { eapply coprime_with_positive_divisor; eauto. }
  destruct
    (reduced_unit_representatives_exact x divisor
       ltac:(lia) Hxd)
    as [Hunit_system [Hunit_length Hunit_partition]].
  destruct
    (transport_unit_stratum_system
       m divisor x
       (UnitRepresentatives divisor (x mod divisor))
       Hm Hdivisor Hdivide Hxm Hunit_system)
    as [Hlifted_system Hlifted_length].
  split; [exact Hdivisor |].
  split; [exact Hdivide |].
  split.
  - unfold ConcreteNonUnitBlock. exact Hlifted_system.
  - unfold ConcreteNonUnitBlock.
    rewrite Hlifted_length, Hunit_length.
    unfold CycleTerm.
    assert (Hnotone : Z.eqb divisor 1 = false).
    { apply Z.eqb_neq. lia. }
    rewrite Hnotone.
    reflexivity.
Qed.

Lemma concrete_nonunit_subsystems
    (m x : Z) (divisors : list Z) :
  0 < m ->
  Z.gcd x m = 1 ->
  (forall divisor,
      In divisor divisors ->
      In divisor (concrete_nonunit_divisors m)) ->
  ExactNonUnitDivisorSystems
    m x divisors (map (ConcreteNonUnitBlock m x) divisors).
Proof.
  intros Hm Hxm Hsubset.
  induction divisors as [| divisor divisors IH].
  - constructor.
  - simpl. constructor.
    + apply concrete_nonunit_block_exact; try assumption.
      apply Hsubset. simpl; auto.
    + apply IH.
      intros tail_divisor Htail.
      apply Hsubset. simpl; auto.
Qed.

Theorem concrete_exact_nonunit_divisor_systems
    (m x : Z) :
  0 < m ->
  Z.gcd x m = 1 ->
  ExactNonUnitDivisorSystems
    m x (concrete_nonunit_divisors m)
    (ConcreteNonUnitBlocks m x).
Proof.
  intros Hm Hxm.
  unfold ConcreteNonUnitBlocks.
  apply concrete_nonunit_subsystems; try assumption.
  intros divisor Hin. exact Hin.
Qed.

Theorem concrete_room_zero_cycle_spec
    (m x : Z) :
  2 <= m ->
  Z.gcd x m = 1 ->
  Spec m x (RoomZeroCycleTotal m x).
Proof.
  intros Hm Hxm.
  pose proof
    (concrete_divisor_strata_key_premises m ltac:(lia))
    as [Hkeys Hclassify].
  apply concrete_divisor_strata_imply_spec with
    (zero_block := ConcreteZeroBlock m)
    (nonunit_blocks := ConcreteNonUnitBlocks m x);
    try assumption; try lia.
  - apply concrete_zero_block_exact. lia.
  - apply concrete_exact_nonunit_divisor_systems;
      [lia | exact Hxm].
Qed.

Theorem valid_factor_table_walk_spec
    (m x : Z) (pr pe : list Z) :
  2 <= m ->
  Z.gcd x m = 1 ->
  ValidFactorTable m pr pe ->
  Spec m x (1 + WalkSuffix pr pe x 0 1).
Proof.
  intros Hm Hxm Hvalid.
  rewrite (room_zero_final_decomposition m x pr pe Hvalid).
  apply concrete_room_zero_cycle_spec; assumption.
Qed.

(** The C expression returns the accumulated divisor sum before adding the
    distinguished zero-room contribution.  This commuted form matches that
    source-level expression without asking symbolic execution to normalize
    the addition order. *)
Corollary valid_factor_table_walk_spec_solver_order
    (m x : Z) (pr pe : list Z) :
  2 <= m ->
  Z.gcd x m = 1 ->
  ValidFactorTable m pr pe ->
  Spec m x (WalkSuffix pr pe x 0 1 + 1).
Proof.
  intros Hm Hxm Hvalid.
  rewrite Z.add_comm.
  apply valid_factor_table_walk_spec; assumption.
Qed.

(** Direct consumer wrapper for the state carried by the top-level walk. *)
Corollary walk_global_bounds_factor_table_spec
    (m x : Z) (pr pe : list Z) :
  WalkGlobalBounds m x ->
  ValidFactorTable m pr pe ->
  Spec m x (WalkSuffix pr pe x 0 1 + 1).
Proof.
  intros (Hm & _ & Hxm) Hvalid.
  apply valid_factor_table_walk_spec_solver_order; try lia; assumption.
Qed.

(** This is the complete non-circular mathematical endpoint needed by the C
    walk: factor-table enumeration determines the sum, while the concrete
    orbit construction proves that the same value is globally optimal. *)
End P090_FinalOrbitInstantiation.
Export P090_FinalOrbitInstantiation.

Lemma order_trial_exit_bounded_ex
    x modulus phi candidate remainder ord :
  OrderTrialStateEx x modulus phi candidate remainder ord ->
  0 < remainder ->
  remainder <= 1 ->
  OrderResult x modulus ord.
Proof.
  intros Hstate Hpositive Hupper.
  assert (remainder = 1) by lia.
  subst remainder.
  eapply order_trial_exit_exhausted_ex; eauto.
Qed.

Lemma order_final_step_div_ex x modulus phi active ord :
  OrderFinalStateEx x modulus phi active ord ->
  ord mod active = 0 ->
  Z.pow x (ord / active) mod modulus = 1 ->
  OrderFinalStateEx x modulus phi active (ord / active).
Proof.
  intros Hstate Hmod Hpow.
  apply (order_final_step_ex x modulus phi active ord (ord / active) Hstate);
    [| exact Hpow].
  unfold OrderFinalStateEx in Hstate.
  destruct Hstate as (_ & Hprime & _).
  pose proof (order_ex_prime_positive active Hprime).
  pose proof (Z.div_mod ord active ltac:(lia)) as Hdivision.
  nia.
Qed.

Lemma order_final_exit_mod_ex x modulus phi active ord :
  OrderFinalStateEx x modulus phi active ord ->
  ord mod active <> 0 ->
  OrderResult x modulus ord.
Proof.
  intros Hstate Hmod.
  apply (order_final_exit_nodiv_ex x modulus phi active ord Hstate).
  intro Hdiv.
  unfold OrderFinalStateEx in Hstate.
  destruct Hstate as (_ & Hprime & _).
  apply Hmod.
  apply (proj2 (Z.mod_divide ord active ltac:(
    pose proof (order_ex_prime_positive active Hprime); lia)));
    exact Hdiv.
Qed.

Lemma order_final_exit_power_guard_ex
    x modulus phi active ord retval :
  OrderFinalStateEx x modulus phi active ord ->
  ord mod active = 0 ->
  retval = Z.pow x (ord / active) mod modulus ->
  retval <> 1 ->
  OrderResult x modulus ord.
Proof.
  intros Hstate Hmod Hretval Hfailure.
  apply (order_final_exit_pow_failure_ex x modulus phi active ord
           (ord / active) Hstate).
  - unfold OrderFinalStateEx in Hstate.
    destruct Hstate as (_ & Hprime & _).
    pose proof (order_ex_prime_positive active Hprime).
    pose proof (Z.div_mod ord active ltac:(lia)) as Hdivision.
    nia.
  - rewrite <- Hretval; exact Hfailure.
Qed.

Require Import Coq.setoid_ring.Ring.
Lemma pow_mod_base__powmod_loop :
  forall x m n,
    m <> 0 ->
    0 <= n ->
    ((x mod m) ^ n) mod m = (x ^ n) mod m.
Proof.
  intros x m n Hm Hn.
  replace n with (Z.of_nat (Z.to_nat n)) by
      (apply Z2Nat.id; exact Hn).
  generalize (Z.to_nat n).
  intros k.
  induction k as [| k IHk].
  - reflexivity.
  - rewrite Nat2Z.inj_succ.
    rewrite !Z.pow_succ_r by lia.
    rewrite (Z.mul_mod (x mod m) ((x mod m) ^ Z.of_nat k) m Hm).
    rewrite Z.mod_mod by exact Hm.
    rewrite IHk.
    symmetry.
    apply Z.mul_mod.
    exact Hm.
Qed.
Lemma land_one_mod_two__powmod_loop :
  forall e, Z.land e 1 = e mod 2.
Proof.
  intros e.
  change (Z.land e (Z.ones 1) = e mod 2).
  rewrite Z.land_ones by lia.
  reflexivity.
Qed.
Lemma pow_loop_odd_step__powmod_loop :
  forall original_base original_exponent m b e r,
    0 < m ->
    0 <= e ->
    Z.land e 1 <> 0 ->
    PowLoopState original_base original_exponent m b e r ->
    PowLoopState original_base original_exponent m
      ((b * b) mod m) (Z.shiftr e 1) ((r * b) mod m).
Proof.
  intros original_base original_exponent m b e r
    Hm He Hodd Hprogress.
  assert (Hm0 : m <> 0) by lia.
  rewrite land_one_mod_two__powmod_loop in Hodd.
  pose proof (Z.mod_pos_bound e 2 ltac:(lia)) as He_mod.
  assert (He_odd : e mod 2 = 1) by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 1) with 2.
  set (q := e / 2).
  assert (Hq : 0 <= q) by
      (unfold q; apply Z.div_pos; lia).
  pose proof (Z.div_mod e 2 ltac:(lia)) as Hdecomp.
  fold q in Hdecomp.
  rewrite He_odd in Hdecomp.
  unfold PowLoopState in *.
  fold q.
  transitivity ((r * b ^ e) mod m).
  - rewrite
      (Z.mul_mod ((r * b) mod m)
        (((b * b) mod m) ^ q) m Hm0).
    rewrite Z.mod_mod by exact Hm0.
    rewrite (pow_mod_base__powmod_loop (b * b) m q Hm0 Hq).
    rewrite <- (Z.mul_mod (r * b) ((b * b) ^ q) m Hm0).
    apply (f_equal (fun z => z mod m)).
    rewrite Hdecomp.
    rewrite Z.pow_add_r by lia.
    rewrite Z.pow_twice_r.
    rewrite Z.pow_mul_l.
    cbn.
    ring.
  - exact Hprogress.
Qed.
Lemma pow_loop_even_step__powmod_loop :
  forall original_base original_exponent m b e r,
    0 < m ->
    0 <= e ->
    Z.land e 1 = 0 ->
    PowLoopState original_base original_exponent m b e r ->
    PowLoopState original_base original_exponent m
      ((b * b) mod m) (Z.shiftr e 1) r.
Proof.
  intros original_base original_exponent m b e r
    Hm He Heven Hprogress.
  assert (Hm0 : m <> 0) by lia.
  rewrite land_one_mod_two__powmod_loop in Heven.
  rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 1) with 2.
  set (q := e / 2).
  assert (Hq : 0 <= q) by
      (unfold q; apply Z.div_pos; lia).
  pose proof (Z.div_mod e 2 ltac:(lia)) as Hdecomp.
  fold q in Hdecomp.
  rewrite Heven in Hdecomp.
  unfold PowLoopState in *.
  fold q.
  transitivity ((r * b ^ e) mod m).
  - rewrite (Z.mul_mod r (((b * b) mod m) ^ q) m Hm0).
    rewrite (pow_mod_base__powmod_loop (b * b) m q Hm0 Hq).
    rewrite <- (Z.mul_mod r ((b * b) ^ q) m Hm0).
    apply (f_equal (fun z => z mod m)).
    rewrite Hdecomp.
    replace (2 * q + 0) with (2 * q) by ring.
    rewrite Z.pow_twice_r.
    rewrite Z.pow_mul_l.
    reflexivity.
  - exact Hprogress.
Qed.
Lemma rem_one_implies_mod_one__order_entry_and_factorization a modulus :
  0 < modulus ->
  Z.rem a modulus = 1 ->
  a mod modulus = 1.
Proof.
  intros Hmodulus Hrem.
  remember a as value eqn:Hvalue in *.
  rewrite Z.rem_mod in Hrem by lia.
  rewrite (Z.abs_eq modulus) in Hrem by lia.
  destruct value as [|p|p].
  - cbn in Hrem; lia.
  - cbn in Hrem.
    destruct (Z.pos p mod modulus); simpl in Hrem |- *; congruence.
  - cbn in Hrem.
    pose proof (Z.mod_pos_bound (Z.pos p) modulus ltac:(lia)).
    destruct (Z.pos p mod modulus); simpl in Hrem, H; try congruence; lia.
Qed.
Lemma rem_eq_mod_of_nonnegative_remainder__order_strip_and_exits a b :
  0 < b ->
  0 <= Z.rem a b ->
  Z.rem a b = Z.modulo a b.
Proof.
  intros Hb Hrem.
  destruct (Z_le_gt_dec 0 a) as [Ha | Ha].
  - apply Z.rem_mod_nonneg; lia.
  - assert (Z.rem a b <= 0) by (apply Z.rem_nonpos; lia).
    assert (Z.rem a b = 0) by lia.
    rewrite H0.
    symmetry.
    apply (proj2 (Z.mod_divide a b ltac:(lia))).
    apply (proj1 (Z.rem_divide a b ltac:(lia))).
    exact H0.
Qed.
