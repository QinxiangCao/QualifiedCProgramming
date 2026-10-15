Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition PrefixStep (a b : list Z) : Prop :=
  Zlength b = Zlength a /\ forall i, 0 <= i < Zlength a ->
  Znth i b 0 = (sum_range 0 i (fun j => Znth j a 0)) mod 1000000007.
Definition IteratePrefix (a b : list Z) (k : Z) : Prop :=
  exists st : list (list Z), Zlength st = k + 1 /\ Znth 0 st [] = a /\ Znth k st [] = b /\
    forall i, 0 <= i < k -> PrefixStep (Znth i st []) (Znth (i + 1) st []).
Definition Pre (k : Z) (a : list Z) : Prop :=
  (* Stated explicitly in the P064 solver Require, so dropped here:
       1 <= Zlength a <= 2000 /\
       Forall (fun x => 0 <= x <= 1000000000) a /\
       0 <= k <= 1000000000  *)
  True.

Definition Spec (k : Z) (a out : list Z) : Prop := IteratePrefix a out k.

Definition ModPower (base exponent result : Z) : Prop :=
  result = (base ^ exponent) mod 1000000007.

Definition PowerLoopState
    (original_base original_exponent accumulator current_base
     remaining_exponent : Z) : Prop :=
  (accumulator * (current_base ^ remaining_exponent)) mod 1000000007 =
  (original_base ^ original_exponent) mod 1000000007.

Definition IdentityPrefix (values written : list Z) : Prop :=
  forall i, 0 <= i < Zlength written ->
    Znth i written 0 = Znth i values 0.

Definition CoefficientPrefix (k : Z) (coefficients : list Z) : Prop :=
  (0 < Zlength coefficients -> Znth 0 coefficients 0 = 1) /\
  forall d, 1 <= d < Zlength coefficients ->
    Znth d coefficients 0 =
      ((((Znth (d - 1) coefficients 0) mod 1000000007) *
         ((k - 1 + d) mod 1000000007)) mod 1000000007 *
        ((d ^ 1000000005) mod 1000000007)) mod 1000000007.

Definition ConvolutionPrefix
    (values coefficients written : list Z) : Prop :=
  forall i, 0 <= i < Zlength written ->
    Znth i written 0 =
      (sum_range 0 i
         (fun j =>
            Znth (i - j) coefficients 0 *
            ((Znth j values 0) mod 1000000007))) mod 1000000007.

Definition ConvolutionAccumulator
    (values coefficients : list Z) (output_index scanned accumulator : Z) : Prop :=
  accumulator =
    (sum_range 0 (scanned - 1)
       (fun j =>
          Znth (output_index - j) coefficients 0 *
          ((Znth j values 0) mod 1000000007))) mod 1000000007.

Require Import Coq.micromega.Lia.
Require Import Coq.setoid_ring.Ring.
Require Import Coq.micromega.Psatz.
Require Import Coq.ZArith.Zpow_facts.
Require Import Coq.Bool.Bool.
Lemma mod_congruent_pow__power_loop :
  forall p x y e,
    p <> 0 ->
    0 <= e ->
    x mod p = y mod p ->
    (x ^ e) mod p = (y ^ e) mod p.
Proof.
  intros p x y e Hp He Hxy.
  rewrite <- (Z2Nat.id e) by lia.
  remember (Z.to_nat e) as n eqn:Hn.
  clear He Hn e.
  induction n as [| n IH].
  - simpl. repeat rewrite Z.pow_0_r. reflexivity.
  - replace (Z.of_nat (S n)) with (Z.succ (Z.of_nat n)) by lia.
    repeat rewrite Z.pow_succ_r by lia.
    rewrite <- (Z.mul_mod_idemp_l x (x ^ Z.of_nat n) p) by exact Hp.
    rewrite <- (Z.mul_mod_idemp_l y (y ^ Z.of_nat n) p) by exact Hp.
    rewrite Hxy.
    rewrite <- (Z.mul_mod_idemp_r (y mod p) (x ^ Z.of_nat n) p) by exact Hp.
    rewrite <- (Z.mul_mod_idemp_r (y mod p) (y ^ Z.of_nat n) p) by exact Hp.
    rewrite IH.
    reflexivity.
Qed.
Lemma mod_mul_congruent__power_loop :
  forall p x1 x2 y1 y2,
    p <> 0 ->
    x1 mod p = x2 mod p ->
    y1 mod p = y2 mod p ->
    (x1 * y1) mod p = (x2 * y2) mod p.
Proof.
  intros p x1 x2 y1 y2 Hp Hx Hy.
  rewrite <- (Z.mul_mod_idemp_l x1 y1 p) by exact Hp.
  rewrite <- (Z.mul_mod_idemp_r (x1 mod p) y1 p) by exact Hp.
  rewrite Hx, Hy.
  rewrite (Z.mul_mod_idemp_r (x2 mod p) y2 p) by exact Hp.
  rewrite (Z.mul_mod_idemp_l x2 y2 p) by exact Hp.
  reflexivity.
Qed.
Lemma pow_odd_decompose__power_loop :
  forall b q,
    0 <= q ->
    b ^ (2 * q + 1) = b * (b * b) ^ q.
Proof.
  intros b q Hq.
  rewrite Z.pow_add_r by lia.
  rewrite Z.pow_1_r.
  rewrite Z.pow_mul_r by lia.
  rewrite Z.pow_2_r.
  ring.
Qed.
Lemma pow_even_decompose__power_loop :
  forall b q,
    0 <= q ->
    b ^ (2 * q) = (b * b) ^ q.
Proof.
  intros b q Hq.
  rewrite Z.pow_mul_r by lia.
  rewrite Z.pow_2_r.
  reflexivity.
Qed.
Lemma exponent_odd_decompose__power_loop :
  forall e,
    0 <= e ->
    Z.land e 1 <> 0 ->
    e = 2 * Z.shiftr e 1 + 1.
Proof.
  intros e He Hodd.
  replace 1 with (Z.ones 1) in Hodd by reflexivity.
  rewrite Z.land_ones in Hodd by lia.
  change (e mod 2 <> 0) in Hodd.
  pose proof (Z.mod_pos_bound e 2 ltac:(lia)) as Hmod.
  pose proof (Z.div_mod e 2 ltac:(lia)) as Hdivmod.
  rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 1) with 2.
  lia.
Qed.
Lemma exponent_even_decompose__power_loop :
  forall e,
    0 <= e ->
    Z.land e 1 = 0 ->
    e = 2 * Z.shiftr e 1.
Proof.
  intros e He Heven.
  replace 1 with (Z.ones 1) in Heven by reflexivity.
  rewrite Z.land_ones in Heven by lia.
  change (e mod 2 = 0) in Heven.
  pose proof (Z.div_mod e 2 ltac:(lia)) as Hdivmod.
  rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 1) with 2.
  lia.
Qed.
Lemma modulo_nonnegative__power_loop :
  forall x,
    0 <= x mod 1000000007.
Proof.
  intro x.
  pose proof (Z.mod_pos_bound x 1000000007 ltac:(lia)).
  lia.
Qed.
Lemma modulo_strict_upper_bound__power_loop :
  forall x,
    x mod 1000000007 < 1000000007.
Proof.
  intro x.
  pose proof (Z.mod_pos_bound x 1000000007 ltac:(lia)).
  lia.
Qed.
Lemma shiftr_one_nonnegative__power_loop :
  forall e,
    0 <= e ->
    0 <= Z.shiftr e 1.
Proof.
  intros e He.
  apply Z.shiftr_nonneg.
  lia.
Qed.
Lemma shiftr_one_le__power_loop :
  forall e,
    0 <= e ->
    Z.shiftr e 1 <= e.
Proof.
  intros e He.
  rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 1) with 2.
  apply Z.div_le_upper_bound; lia.
Qed.
Lemma power_loop_state_init__power_loop :
  forall b e,
    0 <= e ->
    PowerLoopState b e 1 (b mod 1000000007) e.
Proof.
  intros b e He.
  unfold PowerLoopState.
  rewrite Z.mul_1_l.
  apply mod_congruent_pow__power_loop; try lia.
  rewrite Z.mod_mod by lia.
  reflexivity.
Qed.
Lemma power_loop_state_odd_step__power_loop :
  forall original_base original_exponent accumulator current_base
         remaining_exponent,
    0 <= remaining_exponent ->
    Z.land remaining_exponent 1 <> 0 ->
    PowerLoopState original_base original_exponent accumulator
      current_base remaining_exponent ->
    PowerLoopState original_base original_exponent
      ((accumulator * current_base) mod 1000000007)
      ((current_base * current_base) mod 1000000007)
      (Z.shiftr remaining_exponent 1).
Proof.
  intros original_base original_exponent accumulator current_base
    remaining_exponent Hnonneg Hodd Hstate.
  pose proof
    (exponent_odd_decompose__power_loop remaining_exponent Hnonneg Hodd)
    as Hdecompose.
  assert (Hshift : 0 <= Z.shiftr remaining_exponent 1).
  { apply shiftr_one_nonnegative__power_loop. exact Hnonneg. }
  assert (Hpow :
      current_base ^ remaining_exponent =
      current_base *
        (current_base * current_base) ^ Z.shiftr remaining_exponent 1).
  { rewrite Hdecompose at 1.
    apply pow_odd_decompose__power_loop.
    exact Hshift. }
  unfold PowerLoopState in *.
  transitivity
    (((accumulator * current_base) *
       ((current_base * current_base) ^ Z.shiftr remaining_exponent 1))
       mod 1000000007).
  - apply mod_mul_congruent__power_loop; try lia.
    + rewrite Z.mod_mod by lia. reflexivity.
    + apply mod_congruent_pow__power_loop; try lia.
      rewrite Z.mod_mod by lia. reflexivity.
  - transitivity
      ((accumulator * (current_base ^ remaining_exponent))
       mod 1000000007).
    + f_equal.
      rewrite Hpow.
      ring.
    + exact Hstate.
Qed.
Lemma power_loop_state_even_step__power_loop :
  forall original_base original_exponent accumulator current_base
         remaining_exponent,
    0 <= remaining_exponent ->
    Z.land remaining_exponent 1 = 0 ->
    PowerLoopState original_base original_exponent accumulator
      current_base remaining_exponent ->
    PowerLoopState original_base original_exponent accumulator
      ((current_base * current_base) mod 1000000007)
      (Z.shiftr remaining_exponent 1).
Proof.
  intros original_base original_exponent accumulator current_base
    remaining_exponent Hnonneg Heven Hstate.
  pose proof
    (exponent_even_decompose__power_loop remaining_exponent Hnonneg Heven)
    as Hdecompose.
  assert (Hshift : 0 <= Z.shiftr remaining_exponent 1).
  { apply shiftr_one_nonnegative__power_loop. exact Hnonneg. }
  assert (Hpow :
      current_base ^ remaining_exponent =
      (current_base * current_base) ^ Z.shiftr remaining_exponent 1).
  { rewrite Hdecompose at 1.
    apply pow_even_decompose__power_loop.
    exact Hshift. }
  unfold PowerLoopState in *.
  transitivity
    ((accumulator *
      ((current_base * current_base) ^ Z.shiftr remaining_exponent 1))
      mod 1000000007).
  - apply mod_mul_congruent__power_loop; try lia.
    + apply mod_congruent_pow__power_loop; try lia.
      rewrite Z.mod_mod by lia. reflexivity.
  - transitivity
      ((accumulator * (current_base ^ remaining_exponent))
       mod 1000000007).
    + f_equal.
      rewrite Hpow.
      reflexivity.
    + exact Hstate.
Qed.
Lemma power_loop_state_finish__power_loop :
  forall original_base original_exponent accumulator current_base,
    0 <= accumulator < 1000000007 ->
    PowerLoopState original_base original_exponent accumulator current_base 0 ->
    ModPower original_base original_exponent accumulator.
Proof.
  intros original_base original_exponent accumulator current_base
    Haccumulator Hstate.
  unfold PowerLoopState in Hstate.
  unfold ModPower.
  rewrite Z.pow_0_r, Z.mul_1_r in Hstate.
  rewrite Z.mod_small in Hstate by exact Haccumulator.
  exact Hstate.
Qed.
Lemma two_mod_factors_fit_int64__overflow_bounds :
  forall x y : Z,
    0 <= x < 1000000007 ->
    0 <= y < 1000000007 ->
    -9223372036854775808 <= x * y <= 9223372036854775807.
Proof.
  intros x y Hx Hy.
  nia.
Qed.
Lemma mod_product_plus_residue_fit_int64__overflow_bounds :
  forall s x y : Z,
    0 <= s < 1000000007 ->
    0 <= x < 1000000007 ->
    0 <= y < 1000000007 ->
    -9223372036854775808 <= s + x * y <= 9223372036854775807.
Proof.
  intros s x y Hs Hx Hy.
  nia.
Qed.
Lemma identity_prefix_snoc_mod__identity_prefix :
  forall (values written : list Z) (i : Z),
    Zlength written = i ->
    IdentityPrefix values written ->
    0 <= Znth i values 0 < 1000000007 ->
    IdentityPrefix values
      (written ++ [Z.rem (Znth i values 0) 1000000007]).
Proof.
  intros values written i Hlen Hprefix Hvalue.
  subst i.
  unfold IdentityPrefix in *.
  intros q Hq.
  rewrite Zlength_app, Zlength_cons, Zlength_nil in Hq.
  destruct (Z_lt_ge_dec q (Zlength written)) as [Hlt | Hge].
  - unfold Znth.
    rewrite app_nth1.
    + apply Hprefix. lia.
    + rewrite Zlength_correct in Hlt. lia.
  - assert (q = Zlength written) by lia.
    subst q.
    unfold Znth at 1.
    rewrite app_nth2.
    + replace (Z.to_nat (Zlength written) - length written)%nat
        with 0%nat by (rewrite Zlength_correct; lia).
      simpl.
      rewrite Z.rem_small.
      * reflexivity.
      * lia.
    + rewrite Zlength_correct. lia.
Qed.
Lemma rem_range_nonneg__coefficient_construction :
  forall x, 0 <= x -> 0 <= Z.rem x 1000000007 < 1000000007.
Proof.
  intros x Hx.
  rewrite Z.rem_mod_nonneg by lia.
  apply Z.mod_pos_bound.
  lia.
Qed.
Lemma coefficient_prefix_singleton__coefficient_construction :
  forall k, 1 <= k -> CoefficientPrefix k [1].
Proof.
  intros k Hk.
  unfold CoefficientPrefix.
  split.
  - intros _. reflexivity.
  - intros d Hd.
    rewrite Zlength_cons, Zlength_nil in Hd.
    lia.
Qed.
Lemma coefficient_prefix_snoc__coefficient_construction :
  forall k coefficients d retval,
    1 <= k ->
    1 <= d ->
    Zlength coefficients = d ->
    (forall q, 0 <= q < d ->
       0 <= Znth q coefficients 0 < 1000000007) ->
    0 <= retval ->
    CoefficientPrefix k coefficients ->
    ModPower d (1000000007 - 2) retval ->
    CoefficientPrefix k
      (coefficients ++
       [Z.rem
          (Z.rem
             (Z.rem (Znth (d - 1) coefficients 0) 1000000007 *
              Z.rem (k - 1 + d) 1000000007)
             1000000007 * retval)
          1000000007]).
Proof.
  intros k coefficients d retval Hk Hd Hlen Hrange Hretval Hprefix Hpower.
  unfold CoefficientPrefix in Hprefix |- *.
  destruct Hprefix as [Hhead Hstep].
  split.
  - intros _.
    rewrite app_Znth1 by (rewrite Hlen; clear - Hd; lia).
    apply Hhead. clear - Hd Hlen. lia.
  - intros q Hq.
    rewrite Zlength_app, Zlength_cons, Zlength_nil, Hlen in Hq.
    destruct (Z_lt_ge_dec q d) as [Hlt | Hge].
    + rewrite app_Znth1 by (rewrite Hlen; clear - Hq Hlt; lia).
      rewrite app_Znth1 by (rewrite Hlen; clear - Hq Hlt; lia).
      apply Hstep. rewrite Hlen. clear - Hq Hlt. lia.
    + assert (q = d) by (clear - Hq Hge; lia). subst q.
      rewrite app_Znth2 by (rewrite Hlen; clear - Hd; lia).
      rewrite Hlen.
      replace (d - d) with 0 by (clear - d; lia).
      rewrite Znth0_cons.
      rewrite app_Znth1 by (rewrite Hlen; clear - Hd; lia).
      unfold ModPower in Hpower.
      replace (1000000007 - 2) with 1000000005 in Hpower by reflexivity.
      pose proof (Hrange (d - 1) ltac:(clear - Hd; lia)) as Ha.
      assert (Ha_rem :
        Z.rem (Znth (d - 1) coefficients 0) 1000000007 =
        Znth (d - 1) coefficients 0 mod 1000000007).
      { apply Z.rem_mod_nonneg.
        - exact (proj1 Ha).
        - reflexivity. }
      assert (Hb_rem :
        Z.rem (k - 1 + d) 1000000007 =
        (k - 1 + d) mod 1000000007).
      { apply Z.rem_mod_nonneg.
        - clear - Hk Hd. lia.
        - reflexivity. }
      rewrite Ha_rem, Hb_rem.
      assert (Ha_mod :
        0 <= Znth (d - 1) coefficients 0 mod 1000000007).
      { apply Z.mod_pos_bound. reflexivity. }
      assert (Hb_mod : 0 <= (k - 1 + d) mod 1000000007).
      { apply Z.mod_pos_bound. reflexivity. }
      assert (Hproduct_rem :
        Z.rem
          ((Znth (d - 1) coefficients 0 mod 1000000007) *
           ((k - 1 + d) mod 1000000007))
          1000000007 =
        ((Znth (d - 1) coefficients 0 mod 1000000007) *
         ((k - 1 + d) mod 1000000007)) mod 1000000007).
      { apply Z.rem_mod_nonneg.
        - clear - Ha_mod Hb_mod. nia.
        - reflexivity. }
      rewrite Hproduct_rem.
      assert (Hproduct_mod :
        0 <= ((Znth (d - 1) coefficients 0 mod 1000000007) *
              ((k - 1 + d) mod 1000000007)) mod 1000000007).
      { apply Z.mod_pos_bound. reflexivity. }
      assert (Hfinal_rem :
        Z.rem
          (((Znth (d - 1) coefficients 0 mod 1000000007) *
            ((k - 1 + d) mod 1000000007)) mod 1000000007 * retval)
          1000000007 =
        (((Znth (d - 1) coefficients 0 mod 1000000007) *
          ((k - 1 + d) mod 1000000007)) mod 1000000007 * retval)
          mod 1000000007).
      { apply Z.rem_mod_nonneg.
        - clear - Hproduct_mod Hretval. nia.
        - reflexivity. }
      rewrite Hfinal_rem, Hpower.
      reflexivity.
Qed.
Lemma convolution_accumulator_zero__convolution_loop :
  forall values coefficients i,
    ConvolutionAccumulator values coefficients i 0 0.
Proof.
  intros values coefficients i.
  unfold ConvolutionAccumulator, sum_range.
  replace (0 - 1 + 1) with 0 by lia.
  rewrite sum_Z_range_empty by lia.
  reflexivity.
Qed.
Lemma convolution_accumulator_step__convolution_loop :
  forall values coefficients i j s,
    0 <= j ->
    ConvolutionAccumulator values coefficients i j s ->
    ConvolutionAccumulator values coefficients i (j + 1)
      ((s + Znth (i - j) coefficients 0 *
             (Znth j values 0 mod 1000000007)) mod 1000000007).
Proof.
  intros values coefficients i j s Hj Hacc.
  unfold ConvolutionAccumulator in *.
  rewrite Hacc.
  replace (j + 1 - 1) with j by lia.
  unfold sum_range.
  replace (j - 1 + 1) with j by lia.
  rewrite sum_Z_range_extend_right by lia.
  rewrite Z.add_mod_idemp_l by lia.
  reflexivity.
Qed.
Lemma Znth_app_left__convolution_loop :
  forall (l1 l2 : list Z) (d i : Z),
    0 <= i < Zlength l1 ->
    Znth i (l1 ++ l2) d = Znth i l1 d.
Proof.
  intros l1 l2 d i Hi.
  unfold Znth.
  rewrite app_nth1; [reflexivity |].
  rewrite Zlength_correct in Hi.
  lia.
Qed.
Lemma Znth_app_last__convolution_loop :
  forall (l : list Z) (d x : Z),
    Znth (Zlength l) (l ++ [x]) d = x.
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
Lemma convolution_prefix_snoc__convolution_loop :
  forall values coefficients written i j s,
    Zlength written = i ->
    ConvolutionPrefix values coefficients written ->
    j > i ->
    j <= i + 1 ->
    ConvolutionAccumulator values coefficients i j s ->
    ConvolutionPrefix values coefficients (written ++ [s]).
Proof.
  intros values coefficients written i j s Hlen Hprefix Hgt Hle Hacc.
  assert (Hj : j = i + 1) by lia.
  subst j.
  unfold ConvolutionPrefix in *.
  intros q Hq.
  rewrite Zlength_app, Zlength_cons, Zlength_nil in Hq.
  destruct (Z_lt_ge_dec q i) as [Hlt | Hge].
  - rewrite Znth_app_left__convolution_loop by (rewrite Hlen; lia).
    apply Hprefix.
    rewrite Hlen.
    lia.
  - assert (q = i) by lia.
    subst q.
    assert (Hlast : Znth i (written ++ [s]) 0 = s).
    { rewrite <- Hlen.
      apply Znth_app_last__convolution_loop. }
    rewrite Hlast.
    unfold ConvolutionAccumulator in Hacc.
    replace (i + 1 - 1) with i in Hacc by lia.
    exact Hacc.
Qed.
Lemma identity_prefix_spec_zero__zero_final_result :
  forall values written,
    Zlength values = Zlength written ->
    IdentityPrefix values written ->
    Spec 0 values written.
Proof.
  intros values written Hlen Hidentity.
  assert (Hvalues : values = written).
  {
    apply (proj2 (list_eq_ext values written 0)).
    split; [exact Hlen |].
    intros j Hj.
    symmetry.
    apply Hidentity.
    rewrite <- Hlen.
    exact Hj.
  }
  subst written.
  unfold Spec, IteratePrefix.
  exists [values].
  split.
  - reflexivity.
  - split.
    + simpl. reflexivity.
    + split.
      * simpl. reflexivity.
      * intros j Hj. lia.
Qed.
Lemma coefficient_kernel_unique_generic__positive_final_result :
  forall (kernel : Z -> Z -> Z) k coefficients,
  (forall q, 1 <= q -> kernel q 0 = 1) ->
  (forall q d, 1 <= q -> 1 <= d < 2000 ->
    kernel q d =
      ((((kernel q (d - 1)) mod 1000000007) *
         ((q - 1 + d) mod 1000000007)) mod 1000000007 *
        ((d ^ 1000000005) mod 1000000007)) mod 1000000007) ->
  1 <= k -> Zlength coefficients <= 2000 ->
  CoefficientPrefix k coefficients ->
  forall d, 0 <= d < Zlength coefficients ->
    Znth d coefficients 0 = kernel k d.
Proof.
  intros kernel k coefficients Hzero Hrec Hk Hlen [Hzero_coeff Hstep].
  assert (Hnat : forall (m : nat) d,
    0 <= d -> Z.to_nat d = m -> d < Zlength coefficients ->
    Znth d coefficients 0 = kernel k d).
  {
    induction m as [|m IH]; intros d Hd Hto Hbound.
    - assert (d = 0) by lia. subst d.
      rewrite Hzero_coeff by lia.
      symmetry. apply Hzero. exact Hk.
    - assert (Hd1 : 1 <= d) by
        (destruct d; simpl in Hto; try discriminate; lia).
      rewrite Hstep by lia.
      rewrite (IH (d - 1)) by
        (try lia; rewrite Z2Nat.inj_sub by lia; simpl in Hto; lia).
      symmetry. apply Hrec; lia.
  }
  intros d Hd.
  apply (Hnat (Z.to_nat d) d); auto; lia.
Qed.
Lemma convolution_prefix_generic__positive_final_result :
  forall (conv : Z -> list Z -> Z -> Z),
  (forall k values, 1 <= k ->
    conv k values 0 = Znth 0 values 0 mod 1000000007) ->
  (forall k values i, 1 <= k -> 1 <= i ->
    conv (k + 1) values i =
      (conv (k + 1) values (i - 1) + conv k values i) mod 1000000007) ->
  forall k values i, 1 <= k -> 0 <= i ->
    sum_range 0 i (fun r => conv k values r) mod 1000000007 =
    conv (k + 1) values i.
Proof.
  intros conv Hzero Hrec k values i Hk Hi.
  assert (Hnat : forall (m : nat) d,
    0 <= d -> Z.to_nat d = m ->
    sum_range 0 d (fun r => conv k values r) mod 1000000007 =
    conv (k + 1) values d).
  {
    induction m as [|m IH]; intros d Hd Hto.
    - assert (d = 0) by lia. subst d.
      unfold sum_range. rewrite sum_Z_range_single.
      rewrite Hzero by lia. rewrite Hzero by lia.
      apply Z.mod_mod. lia.
    - assert (Hd1 : 1 <= d) by
        (destruct d; simpl in Hto; try discriminate; lia).
      unfold sum_range at 1.
      rewrite sum_Z_range_extend_right by lia.
      rewrite Z.add_mod by lia.
      pose proof (IH (d - 1) ltac:(lia) ltac:(
        rewrite Z2Nat.inj_sub by lia; simpl in Hto; lia)) as IHd.
      unfold sum_range in IHd.
      replace (d - 1 + 1) with d in IHd by lia.
      rewrite IHd.
      rewrite Z.add_mod_idemp_r by lia.
      symmetry. apply Hrec; lia.
  }
  apply (Hnat (Z.to_nat i) i); auto.
Qed.
Lemma coefficient_convolution_iterate_prefix__positive_final_result :
  forall k values coefficients written,
  1 <= k ->
  Zlength values <= 2000 ->
  Zlength coefficients = Zlength values ->
  Zlength written = Zlength values ->
  CoefficientPrefix k coefficients ->
  ConvolutionPrefix values coefficients written ->
  IteratePrefix values written k.
Proof.
  intros target_k target_values target_coefficients target_written
    target_Hk target_Hbound target_Hclen target_Hwlen target_Hcoef target_Hconv.
  set (bigexp__positive_final_result := 1000000005%positive).
  set (inverse_check__positive_final_result :=
    fun d : Z =>
      Z.eqb
        ((d * Zpow_mod_pos d bigexp__positive_final_result 1000000007)
           mod 1000000007) 1).
  set (binom_nat__positive_final_result :=
    fix binom (n r : nat) {struct n} : nat :=
      match n, r with
      | _, O => 1%nat
      | O, S _ => 0%nat
      | S n', S r' => (binom n' r' + binom n' (S r'))%nat
      end).
  set (binomZ__positive_final_result :=
    fun n r : Z =>
      Z.of_nat
        (binom_nat__positive_final_result (Z.to_nat n) (Z.to_nat r))).
  set (kernel__positive_final_result :=
    fun k d : Z =>
      binomZ__positive_final_result (k - 1 + d) d mod 1000000007).
  set (convolution__positive_final_result :=
    fun (k : Z) (values : list Z) (i : Z) =>
      sum_range 0 i
        (fun j =>
           kernel__positive_final_result k (i - j) *
           (Znth j values 0 mod 1000000007)) mod 1000000007).
  set (canonical_state__positive_final_result :=
    fun (t : Z) (values : list Z) =>
      if Z.eq_dec t 0 then values
      else map
        (fun i => convolution__positive_final_result t values i)
        (Zrange 0 (Zlength values))).

  assert (inverse_checks__positive_final_result :forallb inverse_check__positive_final_result
    (map Z.of_nat (seq 1 1999)) = true).
  {
    vm_compute. reflexivity.
  }

  assert (fermat_inverse_small__positive_final_result :forall d, 1 <= d < 2000 ->
    (d * ((d ^ 1000000005) mod 1000000007)) mod 1000000007 = 1).
  {
    intros d Hd.
      assert (Hin : In d (map Z.of_nat (seq 1 1999))).
      { apply in_map_iff.
        exists (Z.to_nat d).
        split.
        - rewrite Z2Nat.id; lia.
        - apply in_seq. lia. }
      pose proof inverse_checks__positive_final_result as Hall.
      rewrite forallb_forall in Hall.
      specialize (Hall d Hin).
      unfold inverse_check__positive_final_result in Hall.
      apply Z.eqb_eq in Hall.
      change
        ((d * ((Z.pow_pos d bigexp__positive_final_result) mod 1000000007)) mod
          1000000007 = 1).
      rewrite <- Zpow_mod_pos_correct by lia.
      exact Hall.
  }

  assert (binom_nat_zero__positive_final_result :forall n,
  binom_nat__positive_final_result n 0%nat = 1%nat).
  {
    intros [|n]; reflexivity.
  }

  assert (binom_nat_gt__positive_final_result :forall n r,
  (n < r)%nat -> binom_nat__positive_final_result n r = 0%nat).
  {
    induction n as [|n IH]; intros [|r] H; simpl; try lia.
      rewrite IH by lia.
      rewrite IH by lia.
      reflexivity.
  }

  assert (binom_nat_diag__positive_final_result :forall n,
  binom_nat__positive_final_result n n = 1%nat).
  {
    induction n as [|n IH]; simpl; auto.
      rewrite (binom_nat_gt__positive_final_result n (S n)) by lia.
      lia.
  }

  assert (binom_nat_one__positive_final_result :forall n,
  binom_nat__positive_final_result n 1%nat = n).
  {
    induction n as [|n IH]; simpl; [reflexivity|].
      rewrite IH.
      rewrite binom_nat_zero__positive_final_result.
      lia.
  }

  assert (binom_nat_pred__positive_final_result :forall n,
  binom_nat__positive_final_result (S n) n = S n).
  {
    induction n as [|n IH].
      - reflexivity.
      - change
          (binom_nat__positive_final_result (S n) n +
           binom_nat__positive_final_result (S n) (S n) = S (S n))%nat.
        rewrite IH, binom_nat_diag__positive_final_result.
        lia.
  }

  assert (binom_nat_mul__positive_final_result :forall n r,
  (r < n)%nat ->
  (S r * binom_nat__positive_final_result n (S r) =
   (n - r) * binom_nat__positive_final_result n r)%nat).
  {
    induction n as [|n IH]; intros r Hr; [lia|].
      destruct r as [|r].
      - rewrite binom_nat_one__positive_final_result.
        rewrite binom_nat_zero__positive_final_result.
        lia.
      - simpl binom_nat__positive_final_result.
        destruct (Nat.eq_dec (S r) n) as [Heq | Hneq].
        + subst n.
          rewrite (binom_nat_gt__positive_final_result (S r) (S (S r))) by lia.
          rewrite (binom_nat_diag__positive_final_result (S r)).
          rewrite (binom_nat_pred__positive_final_result r).
          lia.
        + assert (Hr1 : (S r < n)%nat) by lia.
          assert (Hr0 : (r < n)%nat) by lia.
          pose proof (IH (S r) Hr1) as IH1.
          pose proof (IH r Hr0) as IH0.
          nia.
  }

  assert (binom_nat_mul_upper__positive_final_result :forall n r,
  (0 < r <= n)%nat ->
  (r * binom_nat__positive_final_result n r =
   n * binom_nat__positive_final_result (n - 1) (r - 1))%nat).
  {
    intros [|n] [|r] Hr; try lia.
      replace (S n - 1)%nat with n by lia.
      replace (S r - 1)%nat with r by lia.
      change
        (S r *
           (binom_nat__positive_final_result n r +
            binom_nat__positive_final_result n (S r)) =
         S n * binom_nat__positive_final_result n r)%nat.
      destruct (Nat.eq_dec r n) as [Heq | Hneq].
      - subst n.
        rewrite binom_nat_diag__positive_final_result.
        rewrite binom_nat_gt__positive_final_result by lia.
        lia.
      - pose proof (binom_nat_mul__positive_final_result n r ltac:(lia)) as Hmul.
        rewrite Nat.mul_add_distr_l.
        rewrite Hmul.
        transitivity
          ((S r + (n - r)) * binom_nat__positive_final_result n r)%nat.
        + symmetry. apply Nat.mul_add_distr_r.
        + assert (Harith : (S r + (n - r) = S n)%nat) by lia.
          rewrite Harith. reflexivity.
  }

  assert (binomZ_zero__positive_final_result :forall n,
  0 <= n -> binomZ__positive_final_result n 0 = 1).
  {
    intros; unfold binomZ__positive_final_result.
      rewrite binom_nat_zero__positive_final_result.
      reflexivity.
  }

  assert (binomZ_pascal__positive_final_result :forall n r,
  0 <= r < n ->
  binomZ__positive_final_result n r +
  binomZ__positive_final_result n (r + 1) =
  binomZ__positive_final_result (n + 1) (r + 1)).
  {
    intros n r Hr.
      unfold binomZ__positive_final_result.
      rewrite Z2Nat.inj_add, Z2Nat.inj_add by lia.
      replace (Z.to_nat n + Z.to_nat 1)%nat with (S (Z.to_nat n)) by lia.
      replace (Z.to_nat r + Z.to_nat 1)%nat with (S (Z.to_nat r)) by lia.
      change
        (Z.of_nat (binom_nat__positive_final_result (Z.to_nat n) (Z.to_nat r)) +
         Z.of_nat (binom_nat__positive_final_result (Z.to_nat n) (S (Z.to_nat r))) =
         Z.of_nat
           (binom_nat__positive_final_result (Z.to_nat n) (Z.to_nat r) +
            binom_nat__positive_final_result (Z.to_nat n) (S (Z.to_nat r)))).
      symmetry. apply Nat2Z.inj_add.
  }

  assert (binomZ_mul__positive_final_result :forall n r,
  0 <= r < n ->
  (r + 1) * binomZ__positive_final_result n (r + 1) =
  (n - r) * binomZ__positive_final_result n r).
  {
    intros n r Hr.
      unfold binomZ__positive_final_result.
      pose proof
        (binom_nat_mul__positive_final_result (Z.to_nat n) (Z.to_nat r)
           ltac:(lia)) as Hmul.
      apply (f_equal Z.of_nat) in Hmul.
      rewrite !Nat2Z.inj_mul in Hmul.
      replace (Z.of_nat (S (Z.to_nat r))) with (r + 1) in Hmul by lia.
      replace (Z.of_nat (Z.to_nat n - Z.to_nat r)) with (n - r) in Hmul.
      2: { rewrite Nat2Z.inj_sub by lia. rewrite !Z2Nat.id by lia. reflexivity. }
      replace (Z.to_nat (r + 1)) with (S (Z.to_nat r)) by lia.
      exact Hmul.
  }

  assert (binomZ_mul_upper__positive_final_result :forall n r,
  0 < r <= n ->
  r * binomZ__positive_final_result n r =
  n * binomZ__positive_final_result (n - 1) (r - 1)).
  {
    intros n r Hr.
      unfold binomZ__positive_final_result.
      pose proof
        (binom_nat_mul_upper__positive_final_result (Z.to_nat n) (Z.to_nat r)
           ltac:(lia)) as Hmul.
      apply (f_equal Z.of_nat) in Hmul.
      rewrite !Nat2Z.inj_mul in Hmul.
      replace (Z.of_nat (Z.to_nat r)) with r in Hmul by lia.
      replace (Z.of_nat (Z.to_nat n)) with n in Hmul by lia.
      replace (Z.to_nat (n - 1)) with (Z.to_nat n - 1)%nat by lia.
      replace (Z.to_nat (r - 1)) with (Z.to_nat r - 1)%nat by lia.
      exact Hmul.
  }

  assert (kernel_zero__positive_final_result :forall k,
  1 <= k -> kernel__positive_final_result k 0 = 1).
  {
    intros k Hk. unfold kernel__positive_final_result.
      rewrite binomZ_zero__positive_final_result by lia.
      reflexivity.
  }

  assert (kernel_pascal__positive_final_result :forall k d,
  1 <= k -> 1 <= d ->
  kernel__positive_final_result (k + 1) d =
  (kernel__positive_final_result (k + 1) (d - 1) +
   kernel__positive_final_result k d) mod 1000000007).
  {
    intros k d Hk Hd.
      unfold kernel__positive_final_result.
      pose proof
        (binomZ_pascal__positive_final_result (k - 1 + d) (d - 1)
           ltac:(lia)) as Hpascal.
      replace (d - 1 + 1) with d in Hpascal by lia.
      replace (k + 1 - 1 + d) with (k - 1 + d + 1) by lia.
      replace (k + 1 - 1 + (d - 1)) with (k - 1 + d) by lia.
      rewrite <- Hpascal.
      rewrite Z.add_mod by lia.
      reflexivity.
  }

  assert (kernel_recurrence__positive_final_result :forall k d,
  1 <= k -> 1 <= d < 2000 ->
  kernel__positive_final_result k d =
    ((((kernel__positive_final_result k (d - 1)) mod 1000000007) *
       ((k - 1 + d) mod 1000000007)) mod 1000000007 *
      ((d ^ 1000000005) mod 1000000007)) mod 1000000007).
  {
    intros k d Hk Hd.
      unfold kernel__positive_final_result.
      set (c := binomZ__positive_final_result (k - 1 + d) d) in *.
      set (cp :=
        binomZ__positive_final_result (k - 1 + (d - 1)) (d - 1)) in *.
      set (x := k - 1 + d) in *.
      pose proof
        (binomZ_mul_upper__positive_final_result (k - 1 + d) d
           ltac:(lia)) as Hmul.
      replace (k - 1 + d - 1) with (k - 1 + (d - 1)) in Hmul by lia.
      change (d * c = x * cp) in Hmul.
      pose proof (fermat_inverse_small__positive_final_result d Hd) as Hinv.
      set (dinv := d ^ 1000000005) in Hinv |- *.
      change ((d * (dinv mod 1000000007)) mod 1000000007 = 1) in Hinv.
      change
        (c mod 1000000007 =
          (((((cp mod 1000000007) mod 1000000007) *
              (x mod 1000000007)) mod 1000000007 *
             (dinv mod 1000000007)) mod 1000000007)).
      clearbody c cp x dinv.
      assert (Hinv2 : (d * dinv) mod 1000000007 = 1).
      { rewrite Z.mul_mod by lia.
        replace (d mod 1000000007) with d by
          (symmetry; apply Z.mod_small; lia).
        exact Hinv. }
      rewrite Z.mod_mod by lia.
      rewrite <- (Z.mul_mod cp x 1000000007) by lia.
      rewrite <- (Z.mul_mod (cp * x) dinv 1000000007) by lia.
      replace (cp * x * dinv) with ((d * c) * dinv) by
        (rewrite Hmul; f_equal; apply Z.mul_comm).
      replace ((d * c) * dinv) with (c * (d * dinv)) by
        (rewrite Z.mul_assoc; f_equal; apply Z.mul_comm).
      rewrite Z.mul_mod by lia.
      rewrite Hinv2.
      rewrite Z.mul_1_r.
      symmetry. apply Z.mod_mod. lia.
  }

  assert (coefficient_kernel_unique__positive_final_result : forall k coefficients, 1 <= k -> Zlength coefficients <= 2000 -> CoefficientPrefix k coefficients -> forall d, 0 <= d < Zlength coefficients -> Znth d coefficients 0 = kernel__positive_final_result k d).
  { intros q coeff Hq Hlen Hprefix d Hd. eapply coefficient_kernel_unique_generic__positive_final_result; eauto using kernel_zero__positive_final_result, kernel_recurrence__positive_final_result. }

  assert (binomZ_diag__positive_final_result :forall n,
  0 <= n -> binomZ__positive_final_result n n = 1).
  {
    intros n Hn. unfold binomZ__positive_final_result.
      change
        (Z.of_nat
           (binom_nat__positive_final_result (Z.to_nat n) (Z.to_nat n)) =
         Z.of_nat 1%nat).
      f_equal. apply binom_nat_diag__positive_final_result.
  }

  assert (kernel_one__positive_final_result :forall d,
  0 <= d -> kernel__positive_final_result 1 d = 1).
  {
    intros d Hd. unfold kernel__positive_final_result.
      replace (1 - 1 + d) with d by lia.
      pose proof (binomZ_diag__positive_final_result d Hd) as Hdiag.
      apply (f_equal (fun x => x mod 1000000007)) in Hdiag.
      simpl in Hdiag. exact Hdiag.
  }

  assert (fold_mod_ext__positive_final_result :forall xs (f g : Z -> Z),
  (forall x, In x xs -> f x mod 1000000007 = g x mod 1000000007) ->
  fold_right (fun x acc => f x + acc) 0 xs mod 1000000007 =
  fold_right (fun x acc => g x + acc) 0 xs mod 1000000007).
  {
    induction xs as [|x xs IH]; intros f g Hfg; simpl.
      - reflexivity.
      - rewrite (Z.add_mod (f x)
          (fold_right (fun x0 acc => f x0 + acc) 0 xs) 1000000007) by lia.
        rewrite (Z.add_mod (g x)
          (fold_right (fun x0 acc => g x0 + acc) 0 xs) 1000000007) by lia.
        rewrite (Hfg x) by (left; reflexivity).
        rewrite (IH f g) by (intros y Hy; apply Hfg; right; exact Hy).
        reflexivity.
  }

  assert (sum_range_mod_ext__positive_final_result :forall low high f g,
  (forall x, low <= x <= high ->
     f x mod 1000000007 = g x mod 1000000007) ->
  sum_range low high f mod 1000000007 =
  sum_range low high g mod 1000000007).
  {
    intros low high f g Hfg. unfold sum_range.
      rewrite !sum_range_unfold.
      apply fold_mod_ext__positive_final_result.
      intros x Hx. apply Hfg.
      rewrite <- In_Zrange in Hx. lia.
  }


  assert (convolution_recurrence__positive_final_result :forall k values i,
  1 <= k -> 1 <= i ->
  convolution__positive_final_result (k + 1) values i =
    (convolution__positive_final_result (k + 1) values (i - 1) +
     convolution__positive_final_result k values i) mod 1000000007).
  {
    intros k values i Hk Hi.
      unfold convolution__positive_final_result.
      assert (Hprefix :
        sum_range 0 (i - 1)
          (fun j => kernel__positive_final_result (k + 1) (i - j) *
                    (Znth j values 0 mod 1000000007)) mod 1000000007 =
        sum_range 0 (i - 1)
          (fun j =>
            (kernel__positive_final_result (k + 1) (i - 1 - j) *
               (Znth j values 0 mod 1000000007)) +
            (kernel__positive_final_result k (i - j) *
               (Znth j values 0 mod 1000000007))) mod 1000000007).
      {
        apply sum_range_mod_ext__positive_final_result.
        intros j Hj.
        pose proof
          (kernel_pascal__positive_final_result k (i - j) Hk ltac:(lia)) as Hp.
        replace (i - j - 1) with (i - 1 - j) in Hp by lia.
        rewrite Hp.
        set (a := kernel__positive_final_result (k + 1) (i - 1 - j)).
        set (b := kernel__positive_final_result k (i - j)).
        set (v := Znth j values 0 mod 1000000007).
        replace (a * v + b * v) with ((a + b) * v) by ring.
        rewrite (Z.mul_mod ((a + b) mod 1000000007) v 1000000007) by lia.
        rewrite (Z.mul_mod (a + b) v 1000000007) by lia.
        rewrite Z.mod_mod by lia. reflexivity.
      }
      unfold sum_range at 1.
      rewrite sum_Z_range_extend_right by lia.
      replace (i - i) with 0 by lia.
      rewrite kernel_zero__positive_final_result by lia.
      rewrite Z.add_mod by lia.
      unfold sum_range in Hprefix.
      replace (i - 1 + 1) with i in Hprefix by lia.
      rewrite Hprefix.
      unfold sum_range at 1 2.
      rewrite sum_Z_range_add.
      fold (sum_range 0 (i - 1)
          (fun j => kernel__positive_final_result (k + 1) (i - 1 - j) *
                    (Znth j values 0 mod 1000000007))).
      fold (sum_range 0 (i - 1)
          (fun j => kernel__positive_final_result k (i - j) *
                    (Znth j values 0 mod 1000000007))).
      rewrite sum_Z_range_extend_right by lia.
      replace (i - i) with 0 by lia.
      rewrite kernel_zero__positive_final_result by lia.
      set (A := sum (fun x => 0 <= x < i)
          (fun j => kernel__positive_final_result (k + 1) (i - 1 - j) *
                    (Znth j values 0 mod 1000000007))).
      set (B := sum (fun x => 0 <= x < i)
          (fun j => kernel__positive_final_result k (i - j) *
                    (Znth j values 0 mod 1000000007))).
      set (v := Znth i values 0 mod 1000000007).
      fold A. fold B.
      unfold sum_range at 1.
      replace (i - 1 + 1) with i by lia.
      fold A.
      clearbody A B v.
      change
        (((A + B) mod 1000000007 + (1 * v) mod 1000000007) mod 1000000007 =
         (A mod 1000000007 + (B + 1 * v) mod 1000000007) mod 1000000007).
      rewrite Z.mul_1_l.
      rewrite <- (Z.add_mod (A + B) v 1000000007) by lia.
      rewrite <- (Z.add_mod A (B + v) 1000000007) by lia.
      f_equal. ring.
  }


  assert (convolution_zero__positive_final_result :forall k values,
  1 <= k ->
  convolution__positive_final_result k values 0 =
    Znth 0 values 0 mod 1000000007).
  {
    intros k values Hk. unfold convolution__positive_final_result, sum_range.
      rewrite sum_Z_range_single.
      replace (0 - 0) with 0 by lia.
      rewrite kernel_zero__positive_final_result by lia.
      rewrite Z.mul_1_l. apply Z.mod_mod. lia.
  }


  assert (convolution_prefix__positive_final_result :forall k values i,
  1 <= k -> 0 <= i ->
  sum_range 0 i (fun r => convolution__positive_final_result k values r)
    mod 1000000007 =
  convolution__positive_final_result (k + 1) values i).
  {
    eapply convolution_prefix_generic__positive_final_result;
      eauto using convolution_zero__positive_final_result,
        convolution_recurrence__positive_final_result.
  }


  assert (Zlength_map__positive_final_result :forall {A B : Type} (f : A -> B) xs,
  Zlength (map f xs) = Zlength xs).
  {
    intros. rewrite !Zlength_correct, length_map. reflexivity.
  }

  assert (Znth_map__positive_final_result :forall {A B : Type} (f : A -> B) xs
    (da : A) (db : B) i,
  0 <= i < Zlength xs ->
  Znth i (map f xs) db = f (Znth i xs da)).
  {
    intros A B f xs. induction xs as [|x xs IH]; intros da db i Hi.
      - rewrite Zlength_nil in Hi. lia.
      - destruct (Z.eq_dec i 0) as [-> | Hne].
        + simpl. rewrite !Znth0_cons. reflexivity.
        + simpl. rewrite !Znth_cons by lia.
          apply IH. rewrite Zlength_cons in Hi. lia.
  }

  assert (Zlength_Zrange_aux__positive_final_result :forall low m,
  Zlength (Zrange_aux low m) = Z.of_nat m).
  {
    intros low m. revert low. induction m as [|m IH]; intros low; simpl.
      - reflexivity.
      - rewrite Zlength_cons, IH. lia.
  }

  assert (Zlength_Zrange__positive_final_result :forall low high,
  low <= high -> Zlength (Zrange low high) = high - low).
  {
    intros low high Hle. unfold Zrange.
      rewrite Zlength_Zrange_aux__positive_final_result. lia.
  }

  assert (Znth_Zrange_aux__positive_final_result :forall m low i,
  0 <= i < Z.of_nat m ->
  Znth i (Zrange_aux low m) 0 = low + i).
  {
    induction m as [|m IH]; intros low i Hi; [lia |].
      simpl. destruct (Z.eq_dec i 0) as [-> | Hne].
      - rewrite Znth0_cons. lia.
      - rewrite Znth_cons by lia.
        rewrite IH by (rewrite Nat2Z.inj_succ in Hi; lia). lia.
  }

  assert (Znth_Zrange__positive_final_result :forall low high i,
  low <= high -> 0 <= i < high - low ->
  Znth i (Zrange low high) 0 = low + i).
  {
    intros low high i Hle Hi. unfold Zrange.
      rewrite Znth_Zrange_aux__positive_final_result by lia. lia.
  }

  assert (canonical_state_zero__positive_final_result :forall values,
  canonical_state__positive_final_result 0 values = values).
  {
    intros. unfold canonical_state__positive_final_result.
      destruct (Z.eq_dec 0 0); [reflexivity | contradiction].
  }

  assert (canonical_state_length__positive_final_result :forall t values,
  Zlength (canonical_state__positive_final_result t values) = Zlength values).
  {
    intros t values. unfold canonical_state__positive_final_result.
      destruct (Z.eq_dec t 0); [reflexivity |].
      rewrite Zlength_map__positive_final_result.
      rewrite Zlength_Zrange__positive_final_result by
        (pose proof (Zlength_nonneg values); lia).
      lia.
  }

  assert (canonical_state_Znth__positive_final_result :forall t values i,
  t <> 0 -> 0 <= i < Zlength values ->
  Znth i (canonical_state__positive_final_result t values) 0 =
  convolution__positive_final_result t values i).
  {
    intros t values i Ht Hi. unfold canonical_state__positive_final_result.
      destruct (Z.eq_dec t 0); [contradiction |].
      rewrite Znth_map__positive_final_result with (da := 0) by
        (rewrite Zlength_Zrange__positive_final_result;
         [lia | pose proof (Zlength_nonneg values); lia]).
      rewrite Znth_Zrange__positive_final_result by
        (pose proof (Zlength_nonneg values); lia).
      replace (0 + i) with i by lia. reflexivity.
  }

  assert (canonical_state_step_zero__positive_final_result :forall values,
  PrefixStep
    (canonical_state__positive_final_result 0 values)
    (canonical_state__positive_final_result 1 values)).
  {
    intros values. unfold PrefixStep.
      rewrite !canonical_state_length__positive_final_result.
      split; [reflexivity |].
      intros i Hi.
      rewrite canonical_state_zero__positive_final_result.
      rewrite canonical_state_Znth__positive_final_result by lia.
      unfold convolution__positive_final_result.
      apply sum_range_mod_ext__positive_final_result.
      intros j Hj.
      rewrite kernel_one__positive_final_result by lia.
      rewrite Z.mul_1_l.
      rewrite Z.mod_mod by lia. reflexivity.
  }

  assert (canonical_state_step_pos__positive_final_result :forall t values,
  1 <= t ->
  PrefixStep
    (canonical_state__positive_final_result t values)
    (canonical_state__positive_final_result (t + 1) values)).
  {
    intros t values Ht. unfold PrefixStep.
      rewrite !canonical_state_length__positive_final_result.
      split; [reflexivity |].
      intros i Hi.
      rewrite canonical_state_Znth__positive_final_result by lia.
      symmetry.
      transitivity
        (sum_range 0 i
           (fun j => convolution__positive_final_result t values j)
           mod 1000000007).
      - apply sum_range_mod_ext__positive_final_result.
        intros j Hj.
        rewrite canonical_state_Znth__positive_final_result by lia.
        reflexivity.
      - apply convolution_prefix__positive_final_result; lia.
  }

  assert (canonical_state_step__positive_final_result :forall t values,
  0 <= t ->
  PrefixStep
    (canonical_state__positive_final_result t values)
    (canonical_state__positive_final_result (t + 1) values)).
  {
    intros t values Ht. destruct (Z.eq_dec t 0) as [-> | Hne].
      - apply canonical_state_step_zero__positive_final_result.
      - apply canonical_state_step_pos__positive_final_result. lia.
  }

  assert (canonical_state_iterate__positive_final_result :forall k values,
  0 <= k ->
  IteratePrefix values (canonical_state__positive_final_result k values) k).
  {
    intros k values Hk. unfold IteratePrefix.
      exists
        (map (fun t => canonical_state__positive_final_result t values)
             (Zrange 0 (k + 1))).
      rewrite Zlength_map__positive_final_result.
      rewrite Zlength_Zrange__positive_final_result by lia.
      split; [lia |].
      split.
      - rewrite Znth_map__positive_final_result with (da := 0) by
          (rewrite Zlength_Zrange__positive_final_result; lia).
        rewrite Znth_Zrange__positive_final_result by lia.
        replace (0 + 0) with 0 by lia.
        apply canonical_state_zero__positive_final_result.
      - split.
        + rewrite Znth_map__positive_final_result with (da := 0) by
            (rewrite Zlength_Zrange__positive_final_result; lia).
          rewrite Znth_Zrange__positive_final_result by lia.
          replace (0 + k) with k by lia. reflexivity.
        + intros i Hi.
          rewrite !Znth_map__positive_final_result with (da := 0) by
            (rewrite Zlength_Zrange__positive_final_result; lia).
          rewrite !Znth_Zrange__positive_final_result by lia.
          replace (0 + i) with i by lia.
          replace (0 + (i + 1)) with (i + 1) by lia.
          apply canonical_state_step__positive_final_result. lia.
  }

  assert (convolution_written_state__positive_final_result :forall k values coefficients written,
  1 <= k ->
  Zlength values <= 2000 ->
  Zlength coefficients = Zlength values ->
  Zlength written = Zlength values ->
  CoefficientPrefix k coefficients ->
  ConvolutionPrefix values coefficients written ->
  written = canonical_state__positive_final_result k values).
  {
    intros k values coefficients written Hk Hbound Hclen Hwlen Hcoef Hconv.
      apply (proj2 (list_eq_ext written
        (canonical_state__positive_final_result k values) 0)).
      split.
      - rewrite canonical_state_length__positive_final_result. exact Hwlen.
      - intros i Hi.
        rewrite canonical_state_Znth__positive_final_result by lia.
        rewrite Hconv by lia.
        unfold convolution__positive_final_result.
        apply sum_range_mod_ext__positive_final_result.
        intros j Hj.
        rewrite (coefficient_kernel_unique__positive_final_result k coefficients)
          by (try exact Hcoef; lia).
        reflexivity.
  }
  rewrite (convolution_written_state__positive_final_result
    target_k target_values target_coefficients target_written
    target_Hk target_Hbound target_Hclen target_Hwlen target_Hcoef target_Hconv).
  apply canonical_state_iterate__positive_final_result. lia.
Qed.
