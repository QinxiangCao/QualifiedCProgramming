Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.QCP_demos_human.simple_arith Require Import exgcd_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma Zabs_triangle: forall a b, Zabs(a - b) <= Zabs a + Zabs b.
Proof. lia. Qed.

Lemma Z_gcd_divide_l: forall a b, exists a', a = a' * (Zgcd a b).
Proof.
  intros.
  pose proof Z.gcd_divide_l a b.
  unfold Z.divide in H.
  exact H.
Qed.

Lemma Z_gcd_divide_r: forall a b, exists b', b = b' * (Zgcd a b).
Proof.
  intros.
  pose proof Z.gcd_divide_r a b.
  unfold Z.divide in H.
  exact H.
Qed.

Lemma Z_abs_quot_rem:
  forall a b: Z, b <> 0 -> Zabs (a % (b)) + Zabs (a ÷ b) * Zabs b = Zabs a.
Proof.
  intros.
  assert(Zabs b <> 0) by lia.
  pose proof Z.quot_rem (Zabs a) (Zabs b) H0.
  rewrite <- Z.quot_abs. 2 : lia.
  rewrite <- Z.rem_abs. 2 : lia.
  lia.
Qed.

Lemma Z_gcd_pos_l:
  forall a b, a <> 0 -> Zgcd a b > 0.
Proof.
  intros.
  assert(Zgcd a b <> 0). {
    intros. intro.
    pose proof Z.gcd_eq_0_l a b.
    lia.
  }
  pose proof Z.gcd_nonneg a b.
  lia.
Qed.

Lemma Z_gcd_pos_r:
  forall a b, b <> 0 -> Zgcd a b > 0.
Proof.
  intros.
  assert(Zgcd a b <> 0). {
    intros. intro.
    pose proof Z.gcd_eq_0_r a b.
    lia.
  }
  pose proof Z.gcd_nonneg a b.
  lia.
Qed.

(* Proof goal: 
  |x'| <= |(a % b) / g|
  |y'| <= |b / g|
  x = y'
  y = x' - (a / b) * y'
  ===> 
  |x| <= |b / g|
  |y| <= |a / g|

  informal Proof:
  |y| =  |x' - (a / b) * y'|
      <= |x'| + |a / b| * |y'|
      <= |(a % b) / g| + |a / b| * |b / g|
      =  |(|a % b| + |a / b| * |b|) / g|     (since g | (a % b) and g | b)
      =  |a / g|
*)

Lemma exgcd_reduction_pre:
  forall a b y, 
  b <> 0 ->
  Zabs y <= Zabs b ÷ Zgcd b (a % (b)) ->
  Zabs (a ÷ b * y) <= Zabs (a ÷ b) * (Zabs b ÷ Zgcd b (a % (b))).
Proof.
  intros.
  rewrite Z.abs_mul. nia.
Qed.

Lemma exgcd_reduction':
  forall a b x y, 
  b <> 0 ->
  Zabs x <= Zabs (a % (b)) ÷ Zgcd b (a % (b)) -> 
  Zabs y <= Zabs b ÷ Zgcd b (a % (b)) ->
  Zabs (x) + Zabs (a ÷ b * y) <= Zabs a ÷ Zgcd b (a % (b)).
Proof.
  intros.
  eapply Z.le_trans. 1: apply (Zplus_le_compat_r _ _ _ H0).
  pose proof exgcd_reduction_pre a b y H H1.
  eapply Z.le_trans. 1: apply (Zplus_le_compat_l _ _ _ H2).
  replace (Zabs (a % (b)) ÷ Zgcd b (a % (b)) + 
          Zabs (a ÷ b) * (Zabs b ÷ Zgcd b (a % (b)))) 
    with (Zabs(((Zabs(a % (b))) + Zabs(a ÷ b) * Zabs(b)) ÷ Zgcd b (a % (b)))).
  2: {
    replace (Zgcd b (a % (b))) with (Zgcd a b) in *.
    2: { rewrite Z.gcd_comm. rewrite <- Z.gcd_rem. rewrite Z.gcd_comm. lia. lia. }
    pose proof Z_gcd_divide_l a b as H_adiv.
    pose proof Z_gcd_divide_r a b as H_bdiv.
    destruct H_adiv as [a' H_adiv].
    destruct H_bdiv as [b' H_bdiv].
    pose proof Z_gcd_pos_r a b H.
    set (g := Zgcd a b) in *.
    replace (a % (b)) with (a' % (b') * g).
    2: { rewrite H_adiv, H_bdiv. rewrite Zquot.Zmult_rem_distr_r. reflexivity. }
    replace (a ÷ b) with (a' ÷ b').
    2: { rewrite H_adiv, H_bdiv. rewrite Zquot.Zquot_mult_cancel_r; lia. }
    replace (Zabs (a' ÷ b') * (Zabs b ÷ g)) with (Zabs (a' ÷ b') * Zabs b ÷ g).
    2: { rewrite Z.divide_quot_mul_exact; try lia. 
        unfold Z.divide.
        exists (Z.abs b').
        rewrite H_bdiv.
        replace g with (Zabs g) at 2 by lia.
        apply Z.abs_mul. }
    replace (Zabs ((Zabs (a' % (b') * g) + Zabs (a' ÷ b') * Zabs b) ÷ g)) 
      with ((Zabs (a' % (b') * g) + Zabs (a' ÷ b') * Zabs b) ÷ g).
    2: {
      pose proof Z.abs_eq_iff ((Zabs (a' % (b') * g) + Zabs (a' ÷ b') * Zabs b) ÷ g) as H_abspos.
      rewrite (proj2 H_abspos). 1 : reflexivity.
      assert((Zabs (a' % (b') * g) + Zabs (a' ÷ b') * Zabs b) >= 0) by lia.
      apply Z.quot_pos; lia.
    }
    replace (Zabs b) with (Zabs b' * g) by lia.
    rewrite Z.mul_assoc.
    rewrite Zquot.Z_quot_plus.
    + rewrite Z.quot_mul; lia.
    + lia.
    + lia. 
  }
  pose proof Z_gcd_pos_l b (a % (b)) H.
  rewrite <- Z.quot_abs by ltac:(lia).
  rewrite Z_abs_quot_rem by ltac:(lia).
  rewrite Z.abs_idemp.
  replace (Zabs (Zgcd b (a % (b)))) with (Zgcd b (a % (b))) by lia.
  lia.
Qed.

Lemma exgcd_reduction:
  forall a b x y, 
  b <> 0 ->
  Zabs x <= Zabs (a % (b)) ÷ Zgcd b (a % (b)) -> 
  Zabs y <= Zabs b ÷ Zgcd b (a % (b)) ->
  Zabs (x - a ÷ b * y) <= Zabs a ÷ Zgcd b (a % (b)).
Proof.
  intros.
  eapply Z.le_trans. 1: apply Zabs_triangle.
  apply (exgcd_reduction' _ _ _ _ H H0 H1).
Qed.

Lemma proof_of_exgcd_return_wit_6_split_goal_2 : exgcd_return_wit_6_split_goal_2.
Proof. pre_process. subst. rewrite Z.gcd_0_r. lia. Qed.

Lemma proof_of_exgcd_return_wit_6_split_goal_3 : exgcd_return_wit_6_split_goal_3.
Proof. pre_process. subst. rewrite Z.gcd_0_r. lia. Qed.

Lemma proof_of_exgcd_return_wit_6 : exgcd_return_wit_6.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_exgcd_return_wit_6_split_goal_2.
  + Goal_apply proof_of_exgcd_return_wit_6_split_goal_3.
Qed.

Lemma proof_of_exgcd_return_wit_5_split_goal_2 : exgcd_return_wit_5_split_goal_2.
Proof. pre_process. subst. rewrite Z.gcd_0_r. lia. Qed.

Lemma proof_of_exgcd_return_wit_5_split_goal_3 : exgcd_return_wit_5_split_goal_3.
Proof. pre_process. subst. rewrite Z.gcd_0_r. lia. Qed.

Lemma proof_of_exgcd_return_wit_5 : exgcd_return_wit_5.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_exgcd_return_wit_5_split_goal_2.
  + Goal_apply proof_of_exgcd_return_wit_5_split_goal_3.
Qed.

Lemma proof_of_exgcd_return_wit_4_split_goal_2 : exgcd_return_wit_4_split_goal_2.
Proof. pre_process. subst. rewrite Z.gcd_0_r. lia. Qed.

Lemma proof_of_exgcd_return_wit_4_split_goal_3 : exgcd_return_wit_4_split_goal_3.
Proof. pre_process. subst. rewrite Z.gcd_0_r. lia. Qed.

Lemma proof_of_exgcd_return_wit_4 : exgcd_return_wit_4.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_exgcd_return_wit_4_split_goal_2.
  + Goal_apply proof_of_exgcd_return_wit_4_split_goal_3.
Qed.

Lemma proof_of_exgcd_return_wit_1_split_goal_2 : exgcd_return_wit_1_split_goal_2.
Proof. 
  pre_process. 
  rewrite Z.gcd_comm.
  rewrite <- (Z.gcd_rem a_pre b_pre PreH6).
  rewrite Z.gcd_comm. 
  lia. 
Qed.

Lemma proof_of_exgcd_return_wit_1_split_goal_3 : exgcd_return_wit_1_split_goal_3.
Proof. 
  pre_process. 
  rewrite Z.gcd_comm.
  rewrite <- (Z.gcd_rem a_pre b_pre PreH6).
  rewrite Z.gcd_comm. 
  lia. 
Qed.


Lemma proof_of_exgcd_return_wit_1 : exgcd_return_wit_1.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_exgcd_return_wit_1_split_goal_2.
  + Goal_apply proof_of_exgcd_return_wit_1_split_goal_3.
Qed.

Lemma proof_of_exgcd_return_wit_2 : exgcd_return_wit_2.
Proof.
  pre_process.
  Exists (x_callee_v - a_pre ÷ b_pre * y_callee_v) y_callee_v .
  subst x_callee_v.
  rewrite Z.gcd_comm.
  rewrite <- (Z.gcd_rem a_pre b_pre PreH7).
  rewrite Z.gcd_comm.
  replace (0 - a_pre ÷ b_pre * y_callee_v) with (-(a_pre ÷ b_pre * y_callee_v)) by lia.
  replace (Zabs (-(a_pre ÷ b_pre * y_callee_v))) with (Zabs(a_pre ÷ b_pre * y_callee_v)) by lia.
  replace (Zgcd b_pre (a_pre % (b_pre))) with (Zabs (a_pre % (b_pre))) in *.
  2: { rewrite Z.gcd_comm.
      rewrite <- (Z.gcd_rem b_pre (a_pre % (b_pre)) ltac:(lia)).
      rewrite PreH4.
      symmetry.
      apply Z.gcd_0_l.  }
  entailer!. 
  + rewrite Z.abs_mul.
    apply (Z.le_trans _ (Zabs (a_pre ÷ b_pre))).
    1: nia.
    pose proof Z.rem_bound_abs a_pre b_pre PreH7.
    rewrite <- (Z.quot_abs _ _ PreH7).
    pose proof Z.abs_nonneg a_pre.
    apply Z.quot_le_compat_l; lia.
  + apply (Z.le_trans _ (Zabs b_pre ÷ Zabs b_pre)).
    1: { rewrite Z.quot_same; lia. }
    pose proof Z.rem_bound_abs a_pre b_pre PreH7.
    apply Z.quot_le_compat_l; lia.
  + pose proof Z.quot_rem a_pre b_pre PreH7.
    rewrite <- PreH2.
    pose proof (Z.quot_rem a_pre b_pre ltac:(lia)).
    lia.
Qed.

Lemma proof_of_exgcd_return_wit_3 : exgcd_return_wit_3.
Proof.
  pre_process.
  Exists (x_callee_v - a_pre ÷ b_pre * y_callee_v) y_callee_v .
  rewrite Z.gcd_comm.
  rewrite <- (Z.gcd_rem a_pre b_pre PreH7).
  rewrite Z.gcd_comm.
  entailer!.
  + apply (exgcd_reduction _ _ _ _ PreH7 PreH5 PreH6).
  + rewrite <- PreH2.
    pose proof (Z.quot_rem a_pre b_pre ltac:(lia)).
    lia.
Qed.

Lemma proof_of_exgcd_partial_solve_wit_4_pure : exgcd_partial_solve_wit_4_pure.
Proof.
  pre_process.
  pose proof Z.rem_bound_abs a_pre b_pre PreH1.
  entailer!.
Qed.

Lemma proof_of_exgcd_safety_wit_18 : exgcd_safety_wit_18.
Proof.
  pre_process.
  pose proof exgcd_reduction _ _ _ _ PreH7 PreH5 PreH6.
  assert(Zgcd b_pre (a_pre % (b_pre)) >= 1). {
    pose proof (Z_gcd_pos_l b_pre (a_pre % (b_pre)) PreH7).
    lia.
  }
  assert(Zabs a_pre ÷ Zgcd b_pre (a_pre % (b_pre)) <= 2147483647). {
    apply Z.quot_le_upper_bound; lia.
  }
  entailer!.
Qed.

Lemma proof_of_exgcd_safety_wit_19 : exgcd_safety_wit_19.
Proof.
  pre_process.
  pose proof exgcd_reduction' a_pre b_pre x_callee_v y_callee_v PreH7 PreH5 PreH6.
  assert(Zgcd b_pre (a_pre % (b_pre)) >= 1). {
    pose proof (Z_gcd_pos_l b_pre (a_pre % (b_pre)) PreH7).
    lia.
  }
  assert(Zabs a_pre ÷ Zgcd b_pre (a_pre % (b_pre)) <= 2147483647). {
    apply Z.quot_le_upper_bound; lia.
  }
  assert(Zabs (a_pre ÷ b_pre * y_callee_v) <= Zabs x_callee_v + Zabs (a_pre ÷ b_pre * y_callee_v)) by lia.
  entailer!.
Qed.

Lemma proof_of_exgcd_safety_wit_15 : exgcd_safety_wit_15.
Proof.
  pre_process.
  assert(Zabs(a_pre ÷ b_pre * y_callee_v) <= 2147483647). {
    rewrite Z.abs_mul.
    rewrite <- Z.quot_abs by ltac:(lia).
    pose proof Z.quot_le_upper_bound (Zabs(a_pre)) (Zabs(b_pre)) 2147483647 ltac:(lia) ltac:(lia).
    nia.
  }
  entailer!.
Qed.

Lemma proof_of_exgcd_safety_wit_16 : exgcd_safety_wit_16.
Proof.
  pre_process.
  assert(Zabs(a_pre ÷ b_pre * y_callee_v) <= 2147483647). {
    rewrite Z.abs_mul.
    rewrite <- Z.quot_abs by ltac:(lia).
    pose proof Z.quot_le_upper_bound (Zabs(a_pre)) (Zabs(b_pre)) 2147483647 ltac:(lia) ltac:(lia).
    nia.
  }
  entailer!.
Qed.

Lemma proof_of_exgcd_derive_Inter_by_Proof: exgcd_derive_Inter_by_Proof.
Proof.
  pre_process.
  entailer!.
  apply derivable1_wand_sepcon_adjoint.
  entailer!.
  repeat apply derivable1_orp_elim; Intros x y ret; Exists x y ret; entailer!.
Qed.
