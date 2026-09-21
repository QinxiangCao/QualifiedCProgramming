Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Psatz.
Require Import AUXLib.ListLib.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.

Import ListNotations.
Local Open Scope Z_scope.
Import naive_C_Rules.
Local Open Scope sac.

Definition digit_sum_modulus : Z := 1000000007.

Inductive Base10DigitSum : Z -> Z -> Prop :=
| Base10DigitSum_zero : Base10DigitSum 0 0
| Base10DigitSum_positive :
    forall n quotient quotient_sum,
      0 < n ->
      quotient = n / 10 ->
      Base10DigitSum quotient quotient_sum ->
      Base10DigitSum n (quotient_sum + n mod 10).

(** Decimal decomposition is independent of the DP tables and machine bounds. *)
Definition decimal_digit_sum (n : Z) : Z :=
  epsilon (inhabits 0) (Base10DigitSum n).

(** Inclusive sums use the shared finite-range sum. Empty ranges sum to zero. *)
Definition PrefixDigitSum (x answer : Z) : Prop :=
  answer = sum_range 1 x decimal_digit_sum mod digit_sum_modulus.

Definition InclusiveDigitSum (lo hi total : Z) : Prop :=
  total = sum_range lo hi decimal_digit_sum.

Definition IntervalDigitSum (lo hi answer : Z) : Prop :=
  answer = sum_range lo hi decimal_digit_sum mod digit_sum_modulus.

Definition PowerTable (power : list Z) : Prop :=
  forall i, 0 <= i < 20 ->
    Znth i power 0 = (10 ^ i) mod digit_sum_modulus.

Definition PowerPrefix (power : list Z) (hi : Z) : Prop :=
  forall i, 0 <= i < hi ->
    Znth i power 0 = (10 ^ i) mod digit_sum_modulus.

Definition DigitDPValue (places leading : Z) : Z :=
  if Z.eq_dec places 1 then leading mod digit_sum_modulus
  else
    (leading * 10 ^ (places - 1) +
     45 * (places - 1) * 10 ^ (places - 2)) mod digit_sum_modulus.

Definition DigitDPTable (dp : list Z) : Prop :=
  (Forall (eq 0) (sublist 0 10 dp)) /\
  forall places leading,
    1 <= places < 20 -> 0 <= leading < 10 ->
    Znth (places * 10 + leading) dp 0 = DigitDPValue places leading.

Definition DigitDPBaseProgress (dp : list Z) (next : Z) : Prop :=
  (forall j, 0 <= j < next -> Znth (10 + j) dp 0 = j) /\
  Forall (eq 0) (sublist 0 10 dp ++ sublist (10 + next) 200 dp).

Definition DigitDPOuterProgress (dp : list Z) (next_places : Z) : Prop :=
  (Forall (eq 0) (sublist 0 10 dp)) /\
  (forall places leading,
     1 <= places < next_places -> 0 <= leading < 10 ->
     Znth (places * 10 + leading) dp 0 = DigitDPValue places leading) /\
  Forall (eq 0) (sublist (next_places * 10) 200 dp).

Definition DigitDPRowProgress
    (dp : list Z) (places next_leading : Z) : Prop :=
  (Forall (eq 0) (sublist 0 10 dp)) /\
  (forall p d, 1 <= p < places -> 0 <= d < 10 ->
     Znth (p * 10 + d) dp 0 = DigitDPValue p d) /\
  (forall d, 0 <= d < next_leading ->
     Znth (places * 10 + d) dp 0 = DigitDPValue places d) /\
  Forall (eq 0) (sublist (places * 10 + next_leading) ((places + 1) * 10) dp) /\
  Forall (eq 0) (sublist ((places + 1) * 10) 200 dp).

Definition InnerCandidateDigitSum
    (dp : list Z) (places count partial : Z) : Prop :=
  partial = sum_range 0 (count - 1)
    (fun digit => Znth (places * 10 + digit) dp 0) mod digit_sum_modulus.

Definition DigitDPCellProgress
    (dp : list Z) (places leading next_suffix : Z) : Prop :=
  (Forall (eq 0) (sublist 0 10 dp)) /\
  (forall p d, 1 <= p < places -> 0 <= d < 10 ->
     Znth (p * 10 + d) dp 0 = DigitDPValue p d) /\
  (forall d, 0 <= d < leading ->
     Znth (places * 10 + d) dp 0 = DigitDPValue places d) /\
  Forall (eq 0) (sublist (places * 10 + leading + 1) ((places + 1) * 10) dp) /\
  Forall (eq 0) (sublist ((places + 1) * 10) 200 dp) /\
  exists partial,
    InnerCandidateDigitSum dp (places - 1) next_suffix partial /\
    Znth (places * 10 + leading) dp 0 =
      (partial + next_suffix * (10 ^ (places - 2)) * leading)
        mod digit_sum_modulus.

Definition ExtractedDigitBuffer
    (x : Z) (digits : list Z) (count remaining : Z) : Prop :=
  remaining = x / 10 ^ count /\
  (forall k, 1 <= k <= count ->
     Znth k digits 0 = (x / 10 ^ (k - 1)) mod 10) /\
  Forall (eq 0) (sublist (count + 1) 20 digits).

Definition ExtractedDigitCount (x count : Z) : Prop :=
  10 ^ (count - 1) <= x < 10 ^ count.

Definition DigitPositionPower (position power : Z) : Prop :=
  power = 10 ^ (position - 1).

Definition OuterDigitPositionPower (position power : Z) : Prop :=
  (position = 0 /\ power = 0) \/
  (1 <= position /\ power = 10 ^ (position - 1)).

Definition AccumulatedDigitSumCorrect
    (x position answer : Z) : Prop :=
  (position = 0 /\ PrefixDigitSum x answer) \/
  (1 <= position /\
   exists high high_digit_sum before,
     high = x / 10 ^ position /\
     Base10DigitSum high high_digit_sum /\
     PrefixDigitSum (high - 1) before /\
     answer =
       (10 ^ position * before +
        45 * high * position * 10 ^ (position - 1) +
        (x mod 10 ^ position + 1) * high_digit_sum)
         mod digit_sum_modulus).

Definition InnerCandidateDigitProgress
    (dp : list Z) (places next_digit answer_before answer : Z) : Prop :=
  exists choice_sum,
    InnerCandidateDigitSum dp places next_digit choice_sum /\
    answer = (answer_before + choice_sum) mod digit_sum_modulus.

Lemma Base10DigitSum_deterministic__interval_bridge :
  forall n first second,
    Base10DigitSum n first -> Base10DigitSum n second -> first = second.
Proof.
  intros n first second Hfirst. revert second.
  induction Hfirst; intros second Hsecond; inversion Hsecond; subst; try lia.
  f_equal. eapply IHHfirst; eauto.
Qed.

Lemma Base10DigitSum_exists : forall n, 0 <= n -> exists total, Base10DigitSum n total.
Proof.
  apply Zlt_0_ind. intros n H Hn.
  destruct (Z.eq_dec n 0) as [->|Hnz].
  - exists 0. constructor.
  - destruct (H (n / 10) ltac:(split; [apply Z.div_pos; lia|apply Z.div_lt; lia])) as [total Htotal].
    exists (total + n mod 10). eapply Base10DigitSum_positive; eauto; lia.
Qed.

Lemma decimal_digit_sum_correct : forall n total,
  Base10DigitSum n total -> decimal_digit_sum n = total.
Proof.
  intros n total Htotal. unfold decimal_digit_sum.
  apply Base10DigitSum_deterministic__interval_bridge with n.
  - apply epsilon_spec. eauto.
  - exact Htotal.
Qed.

Lemma PrefixDigitSum_nonpositive : forall x, x <= 0 -> PrefixDigitSum x 0.
Proof.
  intros x Hx. unfold PrefixDigitSum, sum_range.
  rewrite sum_Z_range_empty by lia. reflexivity.
Qed.

Lemma PrefixDigitSum_positive_base : PrefixDigitSum 1 1.
Proof.
  unfold PrefixDigitSum, sum_range. rewrite sum_Z_range_single.
  assert (Hdigit : Base10DigitSum 1 1).
  { change (Base10DigitSum 1 (0 + 1 mod 10)).
    eapply Base10DigitSum_positive with (quotient := 0); try reflexivity; try lia.
    constructor. }
  rewrite (decimal_digit_sum_correct _ _ Hdigit). reflexivity.
Qed.

Lemma PrefixDigitSum_positive_step : forall x total next_digit_sum,
  1 <= x -> PrefixDigitSum x total -> Base10DigitSum (x + 1) next_digit_sum ->
  PrefixDigitSum (x + 1) ((total + next_digit_sum) mod digit_sum_modulus).
Proof.
  intros x total next_digit_sum Hx Htotal Hdigit.
  unfold PrefixDigitSum, sum_range in *.
  rewrite Htotal, Z.add_mod_idemp_l by (unfold digit_sum_modulus; lia).
  rewrite (sum_Z_range_extend_right 1 (x + 1) decimal_digit_sum) by lia.
  rewrite (decimal_digit_sum_correct _ _ Hdigit). reflexivity.
Qed.

Lemma PrefixDigitSum_range : forall x total,
  PrefixDigitSum x total -> 0 <= total < digit_sum_modulus.
Proof.
  intros x total ->. apply Z.mod_pos_bound. unfold digit_sum_modulus; lia.
Qed.

Lemma PrefixDigitSum_deterministic__interval_bridge : forall n first second,
  PrefixDigitSum n first -> PrefixDigitSum n second -> first = second.
Proof. unfold PrefixDigitSum; intros; congruence. Qed.

Lemma PrefixDigitSum_predecessor : forall n total,
  1 <= n -> PrefixDigitSum n total -> exists before digit_sum,
  PrefixDigitSum (n - 1) before /\ Base10DigitSum n digit_sum /\
  total = (before + digit_sum) mod digit_sum_modulus.
Proof.
  intros n total Hn Htotal.
  destruct (Base10DigitSum_exists n ltac:(lia)) as [digit Hdigit].
  exists (sum_range 1 (n - 1) decimal_digit_sum mod digit_sum_modulus), digit.
  split; [reflexivity|]. split; [exact Hdigit|].
  unfold PrefixDigitSum, sum_range in *. rewrite Htotal.
  rewrite Z.add_mod_idemp_l by (unfold digit_sum_modulus; lia).
  replace (n - 1 + 1) with n by lia.
  rewrite (sum_Z_range_extend_right 1 n decimal_digit_sum) by lia.
  rewrite (decimal_digit_sum_correct _ _ Hdigit). reflexivity.
Qed.

Lemma InnerCandidateDigitSum_zero : forall dp places, InnerCandidateDigitSum dp places 0 0.
Proof.
  intros. unfold InnerCandidateDigitSum, sum_range.
  rewrite sum_Z_range_empty by lia. reflexivity.
Qed.

Lemma InnerCandidateDigitSum_step : forall dp places next partial,
  0 <= next -> InnerCandidateDigitSum dp places next partial ->
  InnerCandidateDigitSum dp places (next + 1)
    ((partial + Znth (places * 10 + next) dp 0) mod digit_sum_modulus).
Proof.
  intros dp places next partial Hnext Hpartial.
  unfold InnerCandidateDigitSum, sum_range in *.
  rewrite Hpartial, Z.add_mod_idemp_l by (unfold digit_sum_modulus; lia).
  replace (next - 1 + 1) with next by lia.
  replace (next + 1 - 1 + 1) with (next + 1) by lia.
  rewrite (sum_Z_range_extend_right 0 next) by lia. reflexivity.
Qed.

Lemma InnerCandidateDigitSum_ind : forall dp places (P : Z -> Z -> Prop),
  P 0 0 ->
  (forall next partial, 0 <= next -> InnerCandidateDigitSum dp places next partial ->
    P next partial -> P (next + 1)
      ((partial + Znth (places * 10 + next) dp 0) mod digit_sum_modulus)) ->
  forall next partial, 0 <= next -> InnerCandidateDigitSum dp places next partial -> P next partial.
Proof.
  intros dp places P Hzero Hstep.
  assert (Hind : forall next, 0 <= next -> forall partial, InnerCandidateDigitSum dp places next partial -> P next partial).
  { refine (Zlt_0_ind (fun next => forall partial, InnerCandidateDigitSum dp places next partial -> P next partial) _).
    intros next IH Hnext partial Hpartial.
  destruct (Z.eq_dec next 0) as [->|Hnz].
  - unfold InnerCandidateDigitSum, sum_range in Hpartial.
    rewrite sum_Z_range_empty in Hpartial by lia. subst partial. exact Hzero.
  - set (before := sum_range 0 (next - 1 - 1)
      (fun digit => Znth (places * 10 + digit) dp 0) mod digit_sum_modulus).
    assert (Hbefore : InnerCandidateDigitSum dp places (next - 1) before) by reflexivity.
    pose proof (InnerCandidateDigitSum_step dp places (next - 1) before ltac:(lia) Hbefore) as Hafter.
    assert (partial = (before + Znth (places * 10 + (next - 1)) dp 0) mod digit_sum_modulus).
    { unfold InnerCandidateDigitSum in *. replace (next - 1 + 1) with next in Hafter by lia. congruence. }
    subst partial. replace next with (next - 1 + 1) at 1 by lia.
    apply Hstep; try lia; auto.
    apply IH; try lia. exact Hbefore. }
  intros; eapply Hind; eauto.
Qed.

Lemma Znth_app_left__digits_power_and_zero_init :
  forall (l1 l2 : list Z) (d : Z) (i : Z),
    0 <= i < Zlength l1 ->
    Znth i (l1 ++ l2) d = Znth i l1 d.
Proof.
  intros l1 l2 d i Hi.
  unfold Znth.
  rewrite app_nth1; [reflexivity |].
  rewrite Zlength_correct in Hi.
  lia.
Qed.

Lemma Znth_app_last__digits_power_and_zero_init :
  forall (l : list Z) (d x : Z),
    Znth (Zlength l) (l ++ x :: nil) d = x.
Proof.
  intros l d x.
  unfold Znth.
  rewrite app_nth2.
  - rewrite Zlength_correct.
    replace (Z.to_nat (Z.of_nat (length l)) - length l)%nat with 0%nat by lia.
    reflexivity.
  - rewrite Zlength_correct.
    lia.
Qed.

Lemma digits_dp_previous_term_bounds__digits_dp_cell :
  forall (power_l dp_l : list Z) (k j i : Z),
    k < 10 -> 2 <= i -> i < 20 -> 0 <= j -> j < 10 ->
    0 <= k -> k <= 10 ->
    DigitDPCellProgress dp_l i j k -> PowerTable power_l ->
    0 <= Znth ((i - 1) * 10 + k) dp_l 0 +
      Z.rem (Znth (i - 2) power_l 0 * j) 1000000007 <
      1000000007 + 1000000007.
Proof.
  intros power_l dp_l k j i Hk10 Hi2 Hi20 Hj0 Hj10 Hk0 Hk_le Hcell Hpower.
  unfold DigitDPCellProgress in Hcell.
  destruct Hcell as [_ [Hprev _]].
  specialize (Hprev (i - 1) k ltac:(lia) ltac:(lia)).
  unfold PowerTable in Hpower.
  rename Hpower into Hpow.
  specialize (Hpow (i - 2) ltac:(lia)).
  assert (Hprev_nonneg : 0 <= Znth ((i - 1) * 10 + k) dp_l 0).
  { rewrite Hprev. unfold DigitDPValue.
    destruct (Z.eq_dec (i - 1) 1);
      exact (proj1 (Z.mod_pos_bound _ digit_sum_modulus
        ltac:(unfold digit_sum_modulus; lia))). }
  assert (Hprev_lt : Znth ((i - 1) * 10 + k) dp_l 0 < 1000000007).
  { rewrite Hprev. unfold DigitDPValue.
    destruct (Z.eq_dec (i - 1) 1);
      exact (proj2 (Z.mod_pos_bound _ digit_sum_modulus
        ltac:(unfold digit_sum_modulus; lia))). }
  assert (Hpow_nonneg : 0 <= Znth (i - 2) power_l 0).
  { rewrite Hpow.
    exact (proj1 (Z.mod_pos_bound _ digit_sum_modulus
      ltac:(unfold digit_sum_modulus; lia))). }
  assert (Hprod : 0 <= Znth (i - 2) power_l 0 * j)
    by (apply Z.mul_nonneg_nonneg; assumption).
  pose proof (Z.rem_bound_pos_pos
    (Znth (i - 2) power_l 0 * j) 1000000007 ltac:(lia) Hprod) as Hrem.
  lia.
Qed.

Lemma digits_dp_current_plus_moving_bounds__digits_dp_cell :
  forall (power_l dp_l : list Z) (k j i : Z),
    k < 10 -> 2 <= i -> i < 20 -> 0 <= j -> j < 10 ->
    0 <= k -> k <= 10 ->
    DigitDPCellProgress dp_l i j k -> PowerTable power_l ->
    0 <= Znth (i * 10 + j) dp_l 0 +
      Z.rem
        (Znth ((i - 1) * 10 + k) dp_l 0 +
          Z.rem (Znth (i - 2) power_l 0 * j) 1000000007)
        1000000007 <
      1000000007 + 1000000007.
Proof.
  intros power_l dp_l k j i Hk10 Hi2 Hi20 Hj0 Hj10 Hk0 Hk_le Hcell Hpower.
  pose proof (digits_dp_previous_term_bounds__digits_dp_cell
    power_l dp_l k j i Hk10 Hi2 Hi20 Hj0 Hj10 Hk0 Hk_le Hcell Hpower)
    as Hmoving_num.
  unfold DigitDPCellProgress in Hcell.
  destruct Hcell as
    [_ [_ [_ [_ [_ [partial [_ Hcurrent]]]]]]].
  assert (Hcurrent_bounds : 0 <= Znth (i * 10 + j) dp_l 0 < 1000000007).
  { rewrite Hcurrent.
    exact (Z.mod_pos_bound _ digit_sum_modulus
      ltac:(unfold digit_sum_modulus; lia)). }
  pose proof (Z.rem_bound_pos_pos
    (Znth ((i - 1) * 10 + k) dp_l 0 +
      Z.rem (Znth (i - 2) power_l 0 * j) 1000000007)
    1000000007 ltac:(lia) ltac:(lia)) as Hmoving.
  lia.
Qed.

Lemma Zlength_replace_Znth__digits_dp_cell :
  forall {A : Type} (i : Z) (x : A) (l : list A),
    Zlength (replace_Znth i x l) = Zlength l.
Proof.
  intros A i x l.
  unfold replace_Znth.
  repeat rewrite Zlength_correct.
  assert (Hlength : forall n, length (replace_nth n l x) = length l).
  { intros n. revert n. induction l as [|a l IH]; intros [|n]; simpl; auto. }
  rewrite Hlength. reflexivity.
Qed.

Lemma InnerCandidateDigitSum_replace_other__digits_dp_cell :
  forall dp places count partial idx value,
    0 <= idx < Zlength dp ->
    (forall next, 0 <= next < count ->
       0 <= places * 10 + next < Zlength dp /\
       places * 10 + next <> idx) ->
    InnerCandidateDigitSum dp places count partial ->
    InnerCandidateDigitSum (replace_Znth idx value dp) places count partial.
Proof.
  intros dp places count partial idx value Hidx Haway Hinner.
  unfold InnerCandidateDigitSum, sum_range in *.
  rewrite Hinner. f_equal. apply sum_ext. intros next Hnext.
  rewrite Znth_replace_Znth_Diff; try reflexivity; try assumption;
    specialize (Haway next ltac:(lia)); lia.
Qed.

Lemma digit_dp_cell_mod_update__digits_dp_cell :
  forall a b p k j modulus,
    modulus <> 0 ->
    (((a + k * p * j) mod modulus +
       (b + ((p mod modulus) * j) mod modulus) mod modulus) mod modulus) =
    (((a + b) mod modulus + (k + 1) * p * j) mod modulus).
Proof.
  intros a b p k j modulus Hmod.
  rewrite Z.add_mod_idemp_l by exact Hmod.
  rewrite Z.add_mod_idemp_r by exact Hmod.
  rewrite Z.mul_mod_idemp_l by exact Hmod.
  rewrite Z.add_mod_idemp_l by exact Hmod.
  replace (a + k * p * j + (b + (p * j) mod modulus))
    with (a + k * p * j + b + (p * j) mod modulus) by ring.
  rewrite Z.add_mod_idemp_r by exact Hmod.
  f_equal. ring.
Qed.

Lemma InnerCandidateDigitSum_next_inv__digits_dp_row :
  forall dp places next total,
    0 <= next ->
    InnerCandidateDigitSum dp places (next + 1) total ->
    exists partial,
      InnerCandidateDigitSum dp places next partial /\
      total =
        (partial + Znth (places * 10 + next) dp 0)
          mod digit_sum_modulus.
Proof.
  intros dp places next total Hnext Hsum.
  exists (sum_range 0 (next - 1) (fun digit => Znth (places * 10 + digit) dp 0)
    mod digit_sum_modulus).
  split; [reflexivity|].
  pose proof (InnerCandidateDigitSum_step dp places next
    (sum_range 0 (next - 1) (fun digit => Znth (places * 10 + digit) dp 0)
      mod digit_sum_modulus) Hnext eq_refl) as Hstep.
  unfold InnerCandidateDigitSum in *. congruence.
Qed.

Lemma InnerCandidateDigitSum_formula_ge2__digits_dp_row :
  forall dp places next partial,
    0 <= next ->
    2 <= places ->
    (forall d, 0 <= d < next ->
       Znth (places * 10 + d) dp 0 = DigitDPValue places d) ->
    InnerCandidateDigitSum dp places next partial ->
    partial =
      (5 * next * (next - 1) * 10 ^ (places - 2) +
       next * 45 * (places - 1) * 10 ^ (places - 2))
        mod digit_sum_modulus.
Proof.
  intros dp places next partial Hcount Hplaces Hvalues Hsum.
  revert Hvalues.
  refine (InnerCandidateDigitSum_ind dp places
    (fun next partial => (forall d, 0 <= d < next ->
      Znth (places * 10 + d) dp 0 = DigitDPValue places d) ->
      partial = (5 * next * (next - 1) * 10 ^ (places - 2) +
        next * 45 * (places - 1) * 10 ^ (places - 2)) mod digit_sum_modulus)
    _ _ next partial Hcount Hsum); clear next partial Hcount Hsum.
  - intros Hvalues.
    replace
      (5 * 0 * (0 - 1) * 10 ^ (places - 2) +
       0 * 45 * (places - 1) * 10 ^ (places - 2))
      with 0 by ring.
    unfold digit_sum_modulus.
    reflexivity.
  - intros next partial Hnext Hsum IH Hvalues.
    specialize (IH (fun d Hd => Hvalues d ltac:(lia))).
    rewrite Hvalues by lia.
    unfold DigitDPValue.
    destruct (Z.eq_dec places 1) as [Heq | Hneq]; [lia |].
    assert (Hpow :
      10 ^ (places - 1) = 10 * 10 ^ (places - 2)).
    {
      replace (places - 1) with (Z.succ (places - 2)) by lia.
      rewrite Z.pow_succ_r by lia.
      ring.
    }
    rewrite IH, Hpow.
    rewrite Z.add_mod_idemp_l by
      (unfold digit_sum_modulus; lia).
    rewrite Z.add_mod_idemp_r by
      (unfold digit_sum_modulus; lia).
    f_equal.
    ring.
Qed.

Lemma InnerCandidateDigitSum_ten__digits_dp_row :
  forall dp places partial,
    1 <= places ->
    (forall d, 0 <= d < 10 ->
       Znth (places * 10 + d) dp 0 = DigitDPValue places d) ->
    InnerCandidateDigitSum dp places 10 partial ->
    partial =
      (45 * places * 10 ^ (places - 1)) mod digit_sum_modulus.
Proof.
  intros dp places partial Hplaces Hvalues Hsum10.
  destruct (Z.eq_dec places 1) as [Heq | Hneq].
  - subst places.
    destruct (InnerCandidateDigitSum_next_inv__digits_dp_row
      dp 1 9 partial ltac:(lia) Hsum10)
      as [partial9 [Hsum9 Hpartial]].
    destruct (InnerCandidateDigitSum_next_inv__digits_dp_row
      dp 1 8 partial9 ltac:(lia) Hsum9)
      as [partial8 [Hsum8 Hpartial9]].
    destruct (InnerCandidateDigitSum_next_inv__digits_dp_row
      dp 1 7 partial8 ltac:(lia) Hsum8)
      as [partial7 [Hsum7 Hpartial8]].
    destruct (InnerCandidateDigitSum_next_inv__digits_dp_row
      dp 1 6 partial7 ltac:(lia) Hsum7)
      as [partial6 [Hsum6 Hpartial7]].
    destruct (InnerCandidateDigitSum_next_inv__digits_dp_row
      dp 1 5 partial6 ltac:(lia) Hsum6)
      as [partial5 [Hsum5 Hpartial6]].
    destruct (InnerCandidateDigitSum_next_inv__digits_dp_row
      dp 1 4 partial5 ltac:(lia) Hsum5)
      as [partial4 [Hsum4 Hpartial5]].
    destruct (InnerCandidateDigitSum_next_inv__digits_dp_row
      dp 1 3 partial4 ltac:(lia) Hsum4)
      as [partial3 [Hsum3 Hpartial4]].
    destruct (InnerCandidateDigitSum_next_inv__digits_dp_row
      dp 1 2 partial3 ltac:(lia) Hsum3)
      as [partial2 [Hsum2 Hpartial3]].
    destruct (InnerCandidateDigitSum_next_inv__digits_dp_row
      dp 1 1 partial2 ltac:(lia) Hsum2)
      as [partial1 [Hsum1 Hpartial2]].
    destruct (InnerCandidateDigitSum_next_inv__digits_dp_row
      dp 1 0 partial1 ltac:(lia) Hsum1)
      as [partial0 [Hsum0 Hpartial1]].
    assert (partial0 = 0).
    {
      unfold InnerCandidateDigitSum, sum_range in Hsum0.
      rewrite sum_Z_range_empty in Hsum0 by lia. exact Hsum0.
    }
    subst partial0 partial1 partial2 partial3 partial4.
    subst partial5 partial6 partial7 partial8 partial9 partial.
    repeat rewrite Hvalues by lia.
    unfold DigitDPValue.
    vm_compute.
    reflexivity.
  - pose proof (InnerCandidateDigitSum_formula_ge2__digits_dp_row
      dp places 10 partial ltac:(lia) ltac:(lia) Hvalues Hsum10) as Hpartial.
    rewrite Hpartial.
    assert (Hpow :
      10 ^ (places - 1) = 10 * 10 ^ (places - 2)).
    {
      replace (places - 1) with (Z.succ (places - 2)) by lia.
      rewrite Z.pow_succ_r by lia.
      ring.
    }
    rewrite Hpow.
    f_equal.
    ring.
Qed.

Lemma signed_last_nbits_small : forall x n,
  n > 0 ->
  0 <= x < 2 ^ (n - 1) ->
  signed_last_nbits x n = x.
Proof.
  intros x n Hn Hrange.
  unfold signed_last_nbits.
  replace (x mod 2 ^ n) with x.
  - destruct (Coqlib.zlt x (2 ^ (n - 1))) as [Hlt | Hge].
    + reflexivity.
    + exfalso; lia.
  - pose proof Z.mod_small as Hmod.
    assert (2 ^ (n - 1) < 2 ^ n).
    {
      apply Z.pow_lt_mono_r; lia.
    }
    assert (Hrange': 0 <= x < 2 ^ n) by lia.
    specialize (Hmod x (2^n) Hrange').
    lia.
Qed.

Lemma DigitDPValue_nonnegative__prefix_inner_outer_scan :
  forall places leading,
    0 <= DigitDPValue places leading.
Proof.
  intros places leading.
  unfold DigitDPValue.
  destruct (Z.eq_dec places 1);
    apply Z.mod_pos_bound;
    unfold digit_sum_modulus; lia.
Qed.

Lemma outer_power_predecessor__prefix_inner_outer_scan :
  forall i power,
    1 <= i ->
    OuterDigitPositionPower i power ->
    OuterDigitPositionPower (i - 1) (Z.quot power 10).
Proof.
  intros i power Hi Hpower.
  unfold OuterDigitPositionPower in *.
  destruct Hpower as [[Hz _] | [Hile Hpower]]; [lia|].
  subst power.
  destruct (Z.eq_dec i 1) as [Heq | Hneq].
  - left.
    subst i; vm_compute; auto.
  - right.
    split; [lia|].
    assert (Hpow : 10 ^ (i - 1) = 10 ^ (i - 2) * 10).
    { replace (i - 1) with (Z.succ (i - 2)) by lia.
      rewrite Z.pow_succ_r by lia.
      ring. }
    rewrite Hpow, Z.quot_mul by lia.
    f_equal; lia.
Qed.

Lemma signed_modulus_range__prefix_inner_outer_scan :
  forall value,
    0 <= signed_last_nbits (value mod 1000000007) 32 < 1000000007.
Proof.
  intros value.
  pose proof (Z.mod_pos_bound value 1000000007 ltac:(lia)) as Hmod.
  rewrite signed_last_nbits_eq; lia.
Qed.

Lemma interval_answer_upper__interval_bridge :
  forall retval retval_2 : Z,
    ((Z.rem (retval - retval_2) digit_sum_modulus + digit_sum_modulus)
       mod digit_sum_modulus) < digit_sum_modulus.
Proof.
  intros retval retval_2.
  apply Z.mod_pos_bound.
  unfold digit_sum_modulus; lia.
Qed.

Lemma interval_answer_lower__interval_bridge :
  forall retval retval_2 : Z,
    0 <= ((Z.rem (retval - retval_2) digit_sum_modulus + digit_sum_modulus)
            mod digit_sum_modulus).
Proof.
  intros retval retval_2.
  apply Z.mod_pos_bound.
  unfold digit_sum_modulus; lia.
Qed.

Lemma normalized_outer_rem__interval_bridge :
  forall value : Z,
    Z.rem (Z.rem value digit_sum_modulus + digit_sum_modulus)
      digit_sum_modulus =
    (Z.rem value digit_sum_modulus + digit_sum_modulus) mod
      digit_sum_modulus.
Proof.
  intros value.
  apply Z.rem_mod_nonneg.
  - pose proof (Z.rem_bound_abs value digit_sum_modulus
      ltac:(unfold digit_sum_modulus; lia)) as Hrem.
    apply Z.abs_lt in Hrem.
    unfold digit_sum_modulus in *; lia.
  - unfold digit_sum_modulus; lia.
Qed.

Lemma normalized_rem_mod__interval_bridge :
  forall value : Z,
    (Z.rem value digit_sum_modulus + digit_sum_modulus) mod
      digit_sum_modulus = value mod digit_sum_modulus.
Proof.
  intros value.
  pose proof (Z.quot_rem value digit_sum_modulus
    ltac:(unfold digit_sum_modulus; lia)) as Hqr.
  replace (Z.rem value digit_sum_modulus + digit_sum_modulus)
    with (value + (1 - Z.quot value digit_sum_modulus) * digit_sum_modulus)
    by lia.
  apply Z.mod_add.
  unfold digit_sum_modulus; lia.
Qed.

Lemma PrefixDigitSum_interval_bridge__interval_bridge :
  forall lo hi before after,
    1 <= lo ->
    lo <= hi ->
    PrefixDigitSum (lo - 1) before ->
    PrefixDigitSum hi after ->
    exists total,
      InclusiveDigitSum lo hi total /\
      after = (before + total) mod digit_sum_modulus.
Proof.
  intros lo hi before after Hlo Hle Hbefore Hafter.
  exists (sum_range lo hi decimal_digit_sum). split; [reflexivity|].
  unfold PrefixDigitSum, sum_range in *.
  rewrite Hbefore, Hafter, Z.add_mod_idemp_l by (unfold digit_sum_modulus; lia).
  replace (lo - 1 + 1) with lo by lia.
  rewrite (sum_Z_range_split 1 lo (hi + 1) decimal_digit_sum) by lia.
  reflexivity.
Qed.

Lemma IntervalDigitSum_from_prefixes__interval_bridge :
  forall lo hi before after,
    1 <= lo ->
    lo <= hi ->
    PrefixDigitSum (lo - 1) before ->
    PrefixDigitSum hi after ->
    IntervalDigitSum lo hi
      ((Z.rem (after - before) digit_sum_modulus + digit_sum_modulus)
        mod digit_sum_modulus).
Proof.
  intros lo hi before after Hlo Hle Hbefore Hafter.
  destruct (PrefixDigitSum_interval_bridge__interval_bridge
    lo hi before after Hlo Hle Hbefore Hafter)
    as [total [Hrange Hafter_eq]].
  unfold IntervalDigitSum.
  unfold InclusiveDigitSum in Hrange. rewrite <- Hrange.
  rewrite normalized_rem_mod__interval_bridge.
  rewrite Hafter_eq.
  replace ((before + total) mod digit_sum_modulus - before)
    with ((before + total) mod digit_sum_modulus + - before) by ring.
  rewrite Z.add_mod_idemp_l by (unfold digit_sum_modulus; lia).
  replace (before + total + - before) with total by ring.
  reflexivity.
Qed.

Lemma Base10DigitSum_append_digit :
  forall high digit high_sum,
    0 <= high ->
    0 <= digit < 10 ->
    Base10DigitSum high high_sum ->
    Base10DigitSum (10 * high + digit) (high_sum + digit).
Proof.
  intros high digit high_sum Hhigh Hdigit Hsum.
  destruct (Z.eq_dec (10 * high + digit) 0) as [Hzero | Hpositive].
  - assert (high = 0) by nia.
    assert (digit = 0) by nia.
    subst high digit.
    inversion Hsum; subst; try lia.
    constructor.
  - replace (high_sum + digit) with
      (high_sum + (10 * high + digit) mod 10).
    + eapply Base10DigitSum_positive
        with (quotient := high) (quotient_sum := high_sum).
      * nia.
      * replace (10 * high + digit) with (high * 10 + digit) by ring.
        rewrite Z.div_add_l by lia.
        rewrite Z.div_small by lia.
        lia.
      * exact Hsum.
    + replace (10 * high + digit) with (digit + high * 10) by ring.
      rewrite Z.mod_add by lia.
      rewrite Z.mod_small by lia.
      reflexivity.
Qed.

Lemma PrefixDigitSum_append_decimal_digits :
  forall high count high_sum start triangle,
    0 < high ->
    0 <= count <= 10 ->
    2 * triangle = count * (count - 1) ->
    Base10DigitSum high high_sum ->
    PrefixDigitSum (10 * high - 1) start ->
    PrefixDigitSum (10 * high + count - 1)
      ((start + count * high_sum + triangle) mod digit_sum_modulus).
Proof.
  intros high count high_sum start triangle
    Hhigh Hcount Htriangle Hhighsum Hstart.
  assert (Hcount_nat : count = Z.of_nat (Z.to_nat count)).
  { rewrite Z2Nat.id by lia. reflexivity. }
  remember (Z.to_nat count) as count_nat.
  rewrite Hcount_nat in Hcount, Htriangle |- *.
  clear Hcount_nat count Heqcount_nat.
  revert triangle Hcount Htriangle.
  induction count_nat as [|count_nat IH];
    intros triangle Hcount Htriangle.
  - rewrite Nat2Z.inj_0 in Hcount, Htriangle |- *.
    assert (triangle = 0) by lia.
    subst triangle.
    replace (10 * high + 0 - 1) with (10 * high - 1) by ring.
    replace (start + 0 * high_sum + 0) with start by ring.
    rewrite Z.mod_small.
    + exact Hstart.
    + apply PrefixDigitSum_range in Hstart.
      exact Hstart.
  - rewrite Nat2Z.inj_succ in *.
    set (count := Z.of_nat count_nat) in *.
    replace (Z.succ count) with (count + 1) in * by lia.
    assert (Hcount_bounds : 0 <= count <= 9) by lia.
    assert (Hprevious_triangle :
      2 * (triangle - count) = count * (count - 1)) by nia.
    specialize (IH (triangle - count) ltac:(lia) Hprevious_triangle).
    replace (10 * high + (count + 1) - 1)
      with ((10 * high + count - 1) + 1) by ring.
    replace
      ((start + (count + 1) * high_sum + triangle)
         mod digit_sum_modulus)
      with
      ((((start + count * high_sum + (triangle - count))
           mod digit_sum_modulus) +
         (high_sum + count)) mod digit_sum_modulus).
    + eapply PrefixDigitSum_positive_step.
      * nia.
      * exact IH.
      * replace ((10 * high + count - 1) + 1)
          with (10 * high + count) by ring.
        apply Base10DigitSum_append_digit.
        -- lia.
        -- lia.
        -- exact Hhighsum.
    + rewrite Z.add_mod_idemp_l by
        (unfold digit_sum_modulus; lia).
      f_equal.
      ring.
Qed.

Lemma PrefixDigitSum_small_decimal_block :
  forall count triangle,
    0 <= count <= 10 ->
    2 * triangle = count * (count - 1) ->
    PrefixDigitSum (count - 1)
      (triangle mod digit_sum_modulus).
Proof.
  intros count triangle Hcount Htriangle.
  assert (Hcount_nat : count = Z.of_nat (Z.to_nat count)).
  { rewrite Z2Nat.id by lia. reflexivity. }
  remember (Z.to_nat count) as count_nat.
  rewrite Hcount_nat in Hcount, Htriangle |- *.
  clear Hcount_nat count Heqcount_nat.
  revert triangle Hcount Htriangle.
  induction count_nat as [|count_nat IH];
    intros triangle Hcount Htriangle.
  - rewrite Nat2Z.inj_0 in Hcount, Htriangle |- *.
    assert (triangle = 0) by lia.
    subst triangle.
    apply PrefixDigitSum_nonpositive.
    lia.
  - rewrite Nat2Z.inj_succ in *.
    set (count := Z.of_nat count_nat) in *.
    replace (Z.succ count) with (count + 1) in * by lia.
    assert (Hcount_bounds : 0 <= count <= 9) by lia.
    destruct (Z.eq_dec count 0) as [Hzero | Hnonzero].
    + rewrite Hzero in *.
      assert (triangle = 0) by nia.
      subst triangle.
      apply PrefixDigitSum_nonpositive.
      lia.
    + destruct (Z.eq_dec count 1) as [Hone | Hnotone].
      * rewrite Hone in *.
        assert (triangle = 1) by nia.
        subst triangle.
        change (PrefixDigitSum 1 1). apply PrefixDigitSum_positive_base.
      * assert (Hprevious_triangle :
          2 * (triangle - count) = count * (count - 1)) by nia.
        specialize (IH (triangle - count) ltac:(lia)
          Hprevious_triangle).
        replace (count + 1 - 1) with ((count - 1) + 1) by ring.
        replace (triangle mod digit_sum_modulus)
          with
          ((((triangle - count) mod digit_sum_modulus) + count)
             mod digit_sum_modulus).
        -- eapply PrefixDigitSum_positive_step.
           ++ lia.
           ++ exact IH.
           ++ replace ((count - 1) + 1) with count by ring.
              replace count with (10 * 0 + count) by ring.
              apply Base10DigitSum_append_digit.
              ** lia.
              ** lia.
              ** constructor.
        -- rewrite Z.add_mod_idemp_l by
             (unfold digit_sum_modulus; lia).
           f_equal.
           ring.
Qed.

Lemma PrefixDigitSum_decimal_block :
  forall high count high_sum before triangle,
    0 <= high ->
    0 <= count <= 10 ->
    2 * triangle = count * (count - 1) ->
    Base10DigitSum high high_sum ->
    PrefixDigitSum (high - 1) before ->
    PrefixDigitSum (10 * high + count - 1)
      ((10 * before + 45 * high + count * high_sum + triangle)
         mod digit_sum_modulus).
Proof.
  intros high count high_sum before triangle
    Hhigh Hcount Htriangle Hhighsum Hbefore.
  assert (Hhigh_nat : high = Z.of_nat (Z.to_nat high)).
  { rewrite Z2Nat.id by lia. reflexivity. }
  remember (Z.to_nat high) as high_nat.
  rewrite Hhigh_nat in Hhigh, Hhighsum, Hbefore |- *.
  clear Hhigh_nat high Heqhigh_nat.
  revert count high_sum before triangle
    Hcount Htriangle Hhighsum Hbefore.
  induction high_nat as [|high_nat IH];
    intros count high_sum before triangle
      Hcount Htriangle Hhighsum Hbefore.
  - rewrite Nat2Z.inj_0 in Hhighsum, Hbefore |- *.
    assert (high_sum = 0).
    { eapply Base10DigitSum_deterministic__interval_bridge.
      - exact Hhighsum.
      - constructor. }
    assert (before = 0).
    { eapply PrefixDigitSum_deterministic__interval_bridge.
      - exact Hbefore.
      - apply PrefixDigitSum_nonpositive; lia. }
    subst high_sum before.
    replace (10 * 0 + count - 1) with (count - 1) by ring.
    replace (10 * 0 + 45 * 0 + count * 0 + triangle)
      with triangle by ring.
    apply PrefixDigitSum_small_decimal_block; assumption.
  - rewrite Nat2Z.inj_succ in *.
    set (previous_high := Z.of_nat high_nat) in *.
    replace (Z.succ previous_high) with (previous_high + 1) in * by lia.
    replace (previous_high + 1 - 1) with previous_high in Hbefore by ring.
    assert (Hprevious_high : 0 <= previous_high) by lia.
    destruct (Z.eq_dec previous_high 0)
      as [Hprevious_zero | Hprevious_nonzero].
    + rewrite Hprevious_zero in *.
      assert (Hbefore_zero : before = 0).
      { eapply PrefixDigitSum_deterministic__interval_bridge.
        - exact Hbefore.
        - apply PrefixDigitSum_nonpositive; lia. }
      subst before.
      assert (Hprevious_sum : Base10DigitSum 0 0) by constructor.
      assert (Hprevious_before : PrefixDigitSum (0 - 1) 0).
      { apply PrefixDigitSum_nonpositive; lia. }
      pose proof (IH ltac:(lia) 10 0 0 45
        ltac:(lia) ltac:(lia) Hprevious_sum Hprevious_before)
        as Hdecade.
      assert (Hstart :
        PrefixDigitSum (10 * (0 + 1) - 1)
          ((10 * 0 + 45 * (0 + 1)) mod digit_sum_modulus)).
      { replace (10 * (0 + 1) - 1) with (10 * 0 + 10 - 1) by ring.
        replace (10 * 0 + 45 * (0 + 1))
          with (10 * 0 + 45 * 0 + 10 * 0 + 45) by ring.
        exact Hdecade. }
      replace
        ((10 * 0 + 45 * (0 + 1) +
           count * high_sum + triangle) mod digit_sum_modulus)
        with
        ((((10 * 0 + 45 * (0 + 1))
             mod digit_sum_modulus) +
           count * high_sum + triangle) mod digit_sum_modulus).
      * apply PrefixDigitSum_append_decimal_digits;
          try assumption; lia.
      * replace
          (((10 * 0 + 45 * (0 + 1)) mod digit_sum_modulus) +
             count * high_sum + triangle)
          with
          (((10 * 0 + 45 * (0 + 1)) mod digit_sum_modulus) +
             (count * high_sum + triangle)) by ring.
        rewrite Z.add_mod_idemp_l by
          (unfold digit_sum_modulus; lia).
        f_equal; ring.
    + assert (Hprevious_positive : 1 <= previous_high) by lia.
      destruct (PrefixDigitSum_predecessor
        previous_high before Hprevious_positive Hbefore)
        as [previous_before [previous_sum
          [Hprevious_before [Hprevious_sum Hprevious_relation]]]].
      pose proof (IH ltac:(lia) 10 previous_sum previous_before 45
        ltac:(lia) ltac:(lia) Hprevious_sum Hprevious_before)
        as Hdecade.
      assert (Hstart :
        PrefixDigitSum (10 * (previous_high + 1) - 1)
          ((10 * before + 45 * (previous_high + 1))
             mod digit_sum_modulus)).
      { replace
          ((10 * before + 45 * (previous_high + 1))
             mod digit_sum_modulus)
          with
          ((10 * previous_before + 45 * previous_high +
             10 * previous_sum + 45) mod digit_sum_modulus).
        - replace (10 * (previous_high + 1) - 1)
            with (10 * previous_high + 10 - 1) by ring.
          exact Hdecade.
        - rewrite Hprevious_relation.
          assert (Hmul :
            (10 * ((previous_before + previous_sum)
                     mod digit_sum_modulus)) mod digit_sum_modulus =
            (10 * (previous_before + previous_sum))
              mod digit_sum_modulus).
          { apply Z.mul_mod_idemp_r.
            unfold digit_sum_modulus; lia. }
          rewrite <- (Z.add_mod_idemp_l
            (10 * ((previous_before + previous_sum)
                    mod digit_sum_modulus))
            (45 * (previous_high + 1)) digit_sum_modulus)
            by (unfold digit_sum_modulus; lia).
          rewrite Hmul.
          rewrite Z.add_mod_idemp_l by
            (unfold digit_sum_modulus; lia).
          f_equal; ring. }
      replace
        ((10 * before + 45 * (previous_high + 1) +
           count * high_sum + triangle) mod digit_sum_modulus)
        with
        ((((10 * before + 45 * (previous_high + 1))
             mod digit_sum_modulus) +
           count * high_sum + triangle) mod digit_sum_modulus).
      * apply PrefixDigitSum_append_decimal_digits;
          try assumption; lia.
      * replace
          (((10 * before + 45 * (previous_high + 1))
              mod digit_sum_modulus) +
             count * high_sum + triangle)
          with
          (((10 * before + 45 * (previous_high + 1))
              mod digit_sum_modulus) +
             (count * high_sum + triangle)) by ring.
        rewrite Z.add_mod_idemp_l by
          (unfold digit_sum_modulus; lia).
        f_equal; ring.
Qed.

Lemma AccumulatedDigitSumCorrect_initial :
  forall x count,
    1 <= count ->
    1 <= x ->
    ExtractedDigitCount x count ->
    AccumulatedDigitSumCorrect x count 0.
Proof.
  intros x count Hcount_low Hx Hcount.
  unfold ExtractedDigitCount in Hcount.
  destruct Hcount as [Hx_low Hx_high].
  unfold AccumulatedDigitSumCorrect.
  right.
  split; [exact Hcount_low|].
  exists 0, 0, 0.
  repeat split.
  - symmetry.
    apply Z.div_small.
    split; [lia|exact Hx_high].
  - constructor.
  - replace
      (10 ^ count * 0 +
       45 * 0 * count * 10 ^ (count - 1) +
       (x mod 10 ^ count + 1) * 0) with 0 by ring.
    unfold digit_sum_modulus.
    reflexivity.
Qed.

Lemma InnerCandidateDigitSum_one_formula :
  forall dp digit partial triangle,
    0 <= digit < 10 ->
    2 * triangle = digit * (digit - 1) ->
    DigitDPTable dp ->
    InnerCandidateDigitSum dp 1 digit partial ->
    partial = triangle mod digit_sum_modulus.
Proof.
  intros dp digit partial triangle Hdigit Htriangle Htable Hsum.
  unfold DigitDPTable in Htable.
  destruct Htable as [_ Htable].
  assert (Hcount : 0 <= digit) by lia.
  revert triangle Hdigit Htriangle.
  refine (InnerCandidateDigitSum_ind dp 1
    (fun digit partial => forall triangle, 0 <= digit < 10 ->
      2 * triangle = digit * (digit - 1) ->
      partial = triangle mod digit_sum_modulus)
    _ _ digit partial Hcount Hsum); clear digit partial Hcount Hsum.
  - intros triangle Hdigit Htriangle.
    assert (triangle = 0) by nia.
    subst triangle.
    unfold digit_sum_modulus.
    reflexivity.
  - intros next partial Hnext Hsum IH triangle Hdigit Htriangle.
    assert (Hnext_bounds : 0 <= next < 10) by lia.
    assert (Hprevious_triangle :
      2 * (triangle - next) = next * (next - 1)) by nia.
    specialize (IH (triangle - next) ltac:(lia) Hprevious_triangle).
    rewrite (Htable 1 next ltac:(lia) Hnext_bounds).
    unfold DigitDPValue.
    destruct (Z.eq_dec 1 1) as [_ | Hneq]; [|contradiction].
    assert (Hnext_mod : next mod digit_sum_modulus = next).
    {
      apply Z.mod_small.
      split; [lia|].
      unfold digit_sum_modulus.
      lia.
    }
    rewrite Hnext_mod.
    rewrite IH.
    rewrite Z.add_mod_idemp_l by
      (unfold digit_sum_modulus; lia).
    f_equal.
    ring.
Qed.

Lemma mod_program_update :
  forall first second low digit modulus,
    modulus <> 0 ->
    (((first mod modulus) + (second mod modulus) +
       (low mod modulus) * digit) mod modulus) =
    (first + second + low * digit) mod modulus.
Proof.
  intros first second low digit modulus Hmodulus.
  rewrite (Z.mod_eq first modulus) by assumption.
  rewrite (Z.mod_eq second modulus) by assumption.
  rewrite (Z.mod_eq low modulus) by assumption.
  replace
    ((first - modulus * (first / modulus)) +
     (second - modulus * (second / modulus)) +
     (low - modulus * (low / modulus)) * digit)
    with
    ((first + second + low * digit) +
     (-(first / modulus) - second / modulus -
        (low / modulus) * digit) * modulus) by ring.
  rewrite Z.mod_add by assumption.
  reflexivity.
Qed.

Lemma mod_scaled_add :
  forall scale base rest modulus,
    modulus <> 0 ->
    (scale * (base mod modulus) + rest) mod modulus =
    (scale * base + rest) mod modulus.
Proof.
  intros scale base rest modulus Hmodulus.
  rewrite (Z.mod_eq base modulus) by assumption.
  replace
    (scale * (base - modulus * (base / modulus)) + rest)
    with
    ((scale * base + rest) + (-scale * (base / modulus)) * modulus)
    by ring.
  rewrite Z.mod_add by assumption.
  reflexivity.
Qed.

Lemma AccumulatedDigitSumCorrect_step :
  forall x dp digits count position answer choice_sum,
    1 <= x ->
    1 <= position <= count ->
    count <= 19 ->
    ExtractedDigitBuffer x digits count 0 ->
    DigitDPTable dp ->
    InnerCandidateDigitSum dp position
      (Znth position digits 0) choice_sum ->
    AccumulatedDigitSumCorrect x position answer ->
    AccumulatedDigitSumCorrect x (position - 1)
      ((answer + choice_sum +
        (((x mod 10 ^ (position - 1)) + 1) mod digit_sum_modulus) *
          Znth position digits 0) mod digit_sum_modulus).
Proof.
  intros x dp digits count position answer choice_sum
    Hx Hposition Hcount Hbuffer Htable Hchoice Hcorrect.
  pose proof Hbuffer as Hbuffer_digits.
  unfold ExtractedDigitBuffer in Hbuffer_digits.
  destruct Hbuffer_digits as [_ [Hdigits _]].
  specialize (Hdigits position ltac:(lia)).
  set (digit := Znth position digits 0) in *.
  pose proof (Z.mod_pos_bound
    (x / 10 ^ (position - 1)) 10 ltac:(lia)) as Hdigit.
  rewrite <- Hdigits in Hdigit.
  assert (Hpower_positive : 0 < 10 ^ (position - 1)).
  { apply Z.pow_pos_nonneg; lia. }
  assert (Hpower :
    10 ^ position = 10 ^ (position - 1) * 10).
  { replace position with (Z.succ (position - 1)) at 1 by lia.
    rewrite Z.pow_succ_r at 1 by lia.
    ring. }
  unfold AccumulatedDigitSumCorrect in Hcorrect.
  destruct Hcorrect as [[Hposition_zero _] |
    [Hposition_positive
      [high [high_sum [before
        [Hhigh [Hhigh_sum [Hbefore Hanswer]]]]]]]]; [lia|].
  assert (Hhigh_nonnegative : 0 <= high).
  { rewrite Hhigh.
    apply Z.div_pos; lia. }
  assert (Hhigh_quotient :
    x / (10 ^ (position - 1) * 10) = high).
  { rewrite <- Hpower.
    symmetry.
    exact Hhigh. }
  assert (Hnext_high :
    x / 10 ^ (position - 1) = 10 * high + digit).
  { pose proof (Z.div_mod (x / 10 ^ (position - 1)) 10
      ltac:(lia)) as Hdivision.
    assert (Hdivided_high :
      x / 10 ^ (position - 1) / 10 = high).
    { rewrite Z.div_div by lia.
      exact Hhigh_quotient. }
    rewrite Hdivided_high in Hdivision.
    rewrite <- Hdigits in Hdivision.
    lia. }
  assert (Hcurrent_remainder :
    x mod 10 ^ position =
      digit * 10 ^ (position - 1) +
      x mod 10 ^ (position - 1)).
  { rewrite Hpower.
    rewrite (Z.mod_eq x (10 ^ (position - 1) * 10)) by lia.
    rewrite (Z.mod_eq x (10 ^ (position - 1))) by lia.
    rewrite Hhigh_quotient.
    rewrite Hnext_high.
    ring. }
  assert (Htriangle_exists :
    exists triangle, 2 * triangle = digit * (digit - 1)).
  { assert (Hdigit_cases :
      digit = 0 \/ digit = 1 \/ digit = 2 \/ digit = 3 \/
      digit = 4 \/ digit = 5 \/ digit = 6 \/ digit = 7 \/
      digit = 8 \/ digit = 9) by lia.
    destruct Hdigit_cases as
      [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]].
    - exists 0; reflexivity.
    - exists 0; reflexivity.
    - exists 1; reflexivity.
    - exists 3; reflexivity.
    - exists 6; reflexivity.
    - exists 10; reflexivity.
    - exists 15; reflexivity.
    - exists 21; reflexivity.
    - exists 28; reflexivity.
    - exists 36; reflexivity. }
  destruct Htriangle_exists as [triangle Htriangle].
  assert (Hnext_high_sum :
    Base10DigitSum (10 * high + digit) (high_sum + digit)).
  { apply Base10DigitSum_append_digit; assumption. }
  destruct (Z.eq_dec position 1) as [Hlast | Hnot_last].
  - subst position.
    assert (Hchoice_formula :
      choice_sum = triangle mod digit_sum_modulus).
    { eapply InnerCandidateDigitSum_one_formula; eauto. }
    assert (Hx_decimal : x = 10 * high + digit).
    { replace (10 ^ (1 - 1)) with 1 in Hnext_high by reflexivity.
      rewrite Z.div_1_r in Hnext_high.
      exact Hnext_high. }
    assert (Hx_mod_ten : x mod 10 = digit).
    { replace (10 ^ 1) with 10 in Hcurrent_remainder by reflexivity.
      replace (10 ^ (1 - 1)) with 1 in Hcurrent_remainder
        by reflexivity.
      rewrite Z.mod_1_r in Hcurrent_remainder.
      lia. }
    assert (Hprefix :
      PrefixDigitSum x
        ((10 * before + 45 * high +
          (digit + 1) * high_sum + (triangle + digit))
           mod digit_sum_modulus)).
    { replace x with (10 * high + (digit + 1) - 1) by lia.
      apply PrefixDigitSum_decimal_block; try assumption.
      - lia.
      - nia. }
    left.
    split; [lia|].
    replace
      ((answer + choice_sum +
        (((x mod 10 ^ (1 - 1)) + 1) mod digit_sum_modulus) *
          digit) mod digit_sum_modulus)
      with
      ((10 * before + 45 * high +
        (digit + 1) * high_sum + (triangle + digit))
         mod digit_sum_modulus).
    + exact Hprefix.
    + rewrite Hanswer, Hchoice_formula.
      replace (10 ^ 1) with 10 by reflexivity.
      replace (10 ^ (1 - 1)) with 1 by reflexivity.
      rewrite Hx_mod_ten.
      rewrite Z.mod_1_r.
      rewrite mod_program_update by
        (unfold digit_sum_modulus; lia).
      f_equal.
      ring.
  - assert (Hposition_two : 2 <= position) by lia.
    pose proof Htable as Htable_values.
    unfold DigitDPTable in Htable_values.
    destruct Htable_values as [_ Htable_values].
    assert (Hchoice_formula :
      choice_sum =
        (5 * digit * (digit - 1) * 10 ^ (position - 2) +
         digit * 45 * (position - 1) * 10 ^ (position - 2))
          mod digit_sum_modulus).
    { eapply InnerCandidateDigitSum_formula_ge2__digits_dp_row.
      - lia.
      - exact Hposition_two.
      - intros candidate Hcandidate.
        apply Htable_values; lia.
      - exact Hchoice. }
    assert (Hnext_before :
      PrefixDigitSum (10 * high + digit - 1)
        ((10 * before + 45 * high +
          digit * high_sum + triangle) mod digit_sum_modulus)).
    { apply PrefixDigitSum_decimal_block.
      - exact Hhigh_nonnegative.
      - lia.
      - exact Htriangle.
      - exact Hhigh_sum.
      - exact Hbefore. }
    assert (Hprevious_power :
      10 ^ (position - 1) = 10 * 10 ^ (position - 2)).
    { replace (position - 1) with (Z.succ (position - 2)) by lia.
      rewrite Z.pow_succ_r by lia.
      ring. }
    right.
    split; [lia|].
    exists (10 * high + digit), (high_sum + digit),
      ((10 * before + 45 * high +
        digit * high_sum + triangle) mod digit_sum_modulus).
    repeat split.
    + symmetry.
      exact Hnext_high.
    + exact Hnext_high_sum.
    + exact Hnext_before.
    + rewrite Hanswer, Hchoice_formula.
      rewrite mod_program_update by
        (unfold digit_sum_modulus; lia).
      replace
        (10 ^ (position - 1) *
           ((10 * before + 45 * high +
             digit * high_sum + triangle) mod digit_sum_modulus) +
         45 * (10 * high + digit) * (position - 1) *
           10 ^ (position - 1 - 1) +
         (x mod 10 ^ (position - 1) + 1) * (high_sum + digit))
        with
        (10 ^ (position - 1) *
           ((10 * before + 45 * high +
             digit * high_sum + triangle) mod digit_sum_modulus) +
         (45 * (10 * high + digit) * (position - 1) *
            10 ^ (position - 1 - 1) +
          (x mod 10 ^ (position - 1) + 1) * (high_sum + digit)))
        by ring.
      rewrite mod_scaled_add by
        (unfold digit_sum_modulus; lia).
      rewrite Hcurrent_remainder.
      rewrite Hpower, Hprevious_power.
      replace (position - 1 - 1) with (position - 2) by lia.
      replace
        (5 * digit * (digit - 1) * 10 ^ (position - 2))
        with
        (10 * triangle * 10 ^ (position - 2)) by nia.
      f_equal.
      ring.
Qed.

(** Proof views recover the old proof layout from explicit annotation bounds.
    These lemmas add no assumptions to the mathematical predicates. *)
Lemma zeros_sublist_view : forall values lo hi,
  0 <= lo <= hi -> hi <= Zlength values ->
  Forall (eq 0) (sublist lo hi values) <->
  (forall k, lo <= k < hi -> Znth k values 0 = 0).
Proof.
  intros values lo hi Hrange Hlen.
  rewrite (Forall_Znth (eq 0) 0), Zlength_sublist by lia.
  split; intros H k Hk.
  - specialize (H (k - lo) ltac:(lia)).
    rewrite Znth_sublist in H by lia.
    replace (k - lo + lo) with k in H by lia. symmetry. exact H.
  - rewrite Znth_sublist by lia. symmetry. apply H. lia.
Qed.

Lemma zero_rows_view : forall values lo hi,
  0 <= lo <= hi -> hi * 10 <= Zlength values ->
  Forall (eq 0) (sublist (lo * 10) (hi * 10) values) <->
  (forall p d, lo <= p < hi -> 0 <= d < 10 -> Znth (p * 10 + d) values 0 = 0).
Proof.
  intros values lo hi Hrange Hlen.
  rewrite zeros_sublist_view by lia.
  split; intros H.
  - intros p d Hp Hd. apply H. lia.
  - intros k Hk.
    pose proof (Z.mod_pos_bound k 10 ltac:(lia)) as Hmod.
    pose proof (Z.div_mod k 10 ltac:(lia)) as Hdiv.
    replace k with (k / 10 * 10 + k mod 10) by lia.
    apply H; lia.
Qed.

Lemma zero_row_slice_view : forall values p lo hi,
  0 <= p -> 0 <= lo <= hi -> hi <= 10 ->
  (p + 1) * 10 <= Zlength values ->
  Forall (eq 0) (sublist (p * 10 + lo) (p * 10 + hi) values) <->
  (forall d, lo <= d < hi -> Znth (p * 10 + d) values 0 = 0).
Proof.
  intros values p lo hi Hp Hrange Hhi Hlen.
  rewrite zeros_sublist_view by lia.
  split; intros H.
  - intros d Hd. apply H; lia.
  - intros k Hk. replace k with (p * 10 + (k - p * 10)) by lia. apply H; lia.
Qed.

Lemma PowerPrefix_view : forall (power : list Z) (hi : Z),
  Zlength power = hi -> 1 <= hi <= 20 ->
  PowerPrefix power hi <->
  Zlength power = hi /\
  1 <= hi <= 20 /\
  forall i, 0 <= i < hi ->
    Znth i power 0 = (10 ^ i) mod digit_sum_modulus.
Proof.
  intros power hi Hb0 Hb1.
  unfold PowerPrefix; tauto.
Qed.

Lemma DigitDPBaseProgress_view : forall (dp : list Z) (next : Z),
  Zlength dp = 200 -> 0 <= next <= 10 ->
  DigitDPBaseProgress dp next <->
  Zlength dp = 200 /\
  0 <= next <= 10 /\
  (forall j, 0 <= j < next -> Znth (10 + j) dp 0 = j) /\
  (forall k, 0 <= k < 200 ->
     (k < 10 \/ 20 <= k \/ 10 + next <= k) -> Znth k dp 0 = 0).
Proof.
  intros dp next Hb0 Hb1.
  unfold DigitDPBaseProgress.
  rewrite Forall_app, !zeros_sublist_view by lia.
  split; intros H; repeat split; try tauto; try lia.
  - intros k Hk Hcase. destruct H as [_ [Hlo Hhi]].
    destruct (Z_lt_ge_dec k 10); [apply Hlo|apply Hhi]; lia.
  - intros k Hk. destruct H as [_ [_ [_ Hzero]]]. apply Hzero; lia.
  - intros k Hk. destruct H as [_ [_ [_ Hzero]]]. apply Hzero; lia.
Qed.

Lemma DigitDPOuterProgress_view : forall (dp : list Z) (next_places : Z),
  Zlength dp = 200 -> 2 <= next_places <= 20 ->
  DigitDPOuterProgress dp next_places <->
  Zlength dp = 200 /\
  2 <= next_places <= 20 /\
  (forall d, 0 <= d < 10 -> Znth d dp 0 = 0) /\
  (forall places leading,
     1 <= places < next_places -> 0 <= leading < 10 ->
     Znth (places * 10 + leading) dp 0 = DigitDPValue places leading) /\
  (forall places leading,
     next_places <= places < 20 -> 0 <= leading < 10 ->
     Znth (places * 10 + leading) dp 0 = 0).
Proof.
  intros dp next_places Hb0 Hb1.
  unfold DigitDPOuterProgress.
  replace 200 with (20 * 10) at 1 by lia.
  rewrite zero_rows_view by lia.
  rewrite zeros_sublist_view by lia. tauto.
Qed.

Lemma DigitDPRowProgress_view : forall (dp : list Z) (places next_leading : Z),
  Zlength dp = 200 -> 2 <= places < 20 -> 0 <= next_leading <= 10 ->
  DigitDPRowProgress dp places next_leading <->
  Zlength dp = 200 /\
  2 <= places < 20 /\
  0 <= next_leading <= 10 /\
  (forall d, 0 <= d < 10 -> Znth d dp 0 = 0) /\
  (forall p d, 1 <= p < places -> 0 <= d < 10 ->
     Znth (p * 10 + d) dp 0 = DigitDPValue p d) /\
  (forall d, 0 <= d < next_leading ->
     Znth (places * 10 + d) dp 0 = DigitDPValue places d) /\
  (forall d, next_leading <= d < 10 ->
     Znth (places * 10 + d) dp 0 = 0) /\
  forall p d, places < p < 20 -> 0 <= d < 10 ->
    Znth (p * 10 + d) dp 0 = 0.
Proof.
  intros dp places next_leading Hb0 Hb1 Hb2.
  unfold DigitDPRowProgress.
  replace ((places + 1) * 10) with (places * 10 + 10) at 1 by lia.
  rewrite zero_row_slice_view by lia.
  replace 200 with (20 * 10) at 1 by lia.
  rewrite zero_rows_view by lia.
  rewrite zeros_sublist_view by lia.
  assert ((forall p d, places + 1 <= p < 20 -> 0 <= d < 10 -> Znth (p * 10 + d) dp 0 = 0) <->
          (forall p d, places < p < 20 -> 0 <= d < 10 -> Znth (p * 10 + d) dp 0 = 0)) by (split; intros Hz; intros; apply Hz; lia).
  tauto.
Qed.

Lemma DigitDPCellProgress_view : forall (dp : list Z) (places leading next_suffix : Z),
  Zlength dp = 200 -> 2 <= places < 20 -> 0 <= leading < 10 -> 0 <= next_suffix <= 10 ->
  DigitDPCellProgress dp places leading next_suffix <->
  Zlength dp = 200 /\
  2 <= places < 20 /\
  0 <= leading < 10 /\
  0 <= next_suffix <= 10 /\
  (forall d, 0 <= d < 10 -> Znth d dp 0 = 0) /\
  (forall p d, 1 <= p < places -> 0 <= d < 10 ->
     Znth (p * 10 + d) dp 0 = DigitDPValue p d) /\
  (forall d, 0 <= d < leading ->
     Znth (places * 10 + d) dp 0 = DigitDPValue places d) /\
  (forall d, leading < d < 10 ->
     Znth (places * 10 + d) dp 0 = 0) /\
  (forall p d, places < p < 20 -> 0 <= d < 10 ->
     Znth (p * 10 + d) dp 0 = 0) /\
  exists partial,
    InnerCandidateDigitSum dp (places - 1) next_suffix partial /\
    Znth (places * 10 + leading) dp 0 =
      (partial + next_suffix * (10 ^ (places - 2)) * leading)
        mod digit_sum_modulus.
Proof.
  intros dp places leading next_suffix Hb0 Hb1 Hb2 Hb3.
  unfold DigitDPCellProgress.
  replace ((places + 1) * 10) with (places * 10 + 10) at 1 by lia.
  replace (places * 10 + leading + 1) with (places * 10 + (leading + 1)) by lia.
  rewrite zero_row_slice_view by lia.
  replace 200 with (20 * 10) at 1 by lia.
  rewrite zero_rows_view by lia.
  rewrite zeros_sublist_view by lia.
  assert ((forall p d, places + 1 <= p < 20 -> 0 <= d < 10 -> Znth (p * 10 + d) dp 0 = 0) <->
          (forall p d, places < p < 20 -> 0 <= d < 10 -> Znth (p * 10 + d) dp 0 = 0)) by (split; intros Hz; intros; apply Hz; lia).
  assert ((forall d, leading + 1 <= d < 10 -> Znth (places * 10 + d) dp 0 = 0) <->
          (forall d, leading < d < 10 -> Znth (places * 10 + d) dp 0 = 0)) by (split; intros Hz; intros; apply Hz; lia).
  tauto.
Qed.

Lemma ExtractedDigitBuffer_view : forall (x : Z) (digits : list Z) (count remaining : Z),
  Zlength digits = 20 -> 0 <= count <= 19 ->
  ExtractedDigitBuffer x digits count remaining <->
  Zlength digits = 20 /\
  0 <= count <= 19 /\
  remaining = x / 10 ^ count /\
  (forall k, 1 <= k <= count ->
     Znth k digits 0 = (x / 10 ^ (k - 1)) mod 10) /\
  (forall k, count < k < 20 -> Znth k digits 0 = 0).
Proof.
  intros x digits count remaining Hb0 Hb1.
  unfold ExtractedDigitBuffer.
  rewrite zeros_sublist_view by lia.
  assert ((forall k, count + 1 <= k < 20 -> Znth k digits 0 = 0) <->
          (forall k, count < k < 20 -> Znth k digits 0 = 0)) by (split; intros Hz; intros; apply Hz; lia).
  tauto.
Qed.

Lemma ExtractedDigitCount_view : forall (x count : Z),
  1 <= count <= 19 ->
  ExtractedDigitCount x count <->
  1 <= count <= 19 /\
  10 ^ (count - 1) <= x < 10 ^ count.
Proof.
  intros x count Hb0.
  unfold ExtractedDigitCount; tauto.
Qed.

Lemma DigitPositionPower_view : forall (position power : Z),
  1 <= position <= 19 ->
  DigitPositionPower position power <->
  1 <= position <= 19 /\
  power = 10 ^ (position - 1).
Proof.
  intros position power Hb0.
  unfold DigitPositionPower; tauto.
Qed.

Lemma OuterDigitPositionPower_view : forall (position power : Z),
  0 <= position <= 19 ->
  OuterDigitPositionPower position power <->
  (position = 0 /\ power = 0) \/
  (1 <= position <= 19 /\ power = 10 ^ (position - 1)).
Proof.
  intros position power Hb0.
  unfold OuterDigitPositionPower; intuition lia.
Qed.
