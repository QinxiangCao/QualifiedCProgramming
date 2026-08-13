Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpn_gcd_11_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpn_gcd_11_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

Lemma proof_of_gmp_ctz_return_wit_1 : gmp_ctz_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  destruct (gmp_ctz_from_lowbit_clz x_pre retval PreH5 PreH1 PreH2 PreH3 PreH4)
    as [odd [Hret0 [Hret32 [Hoddpos [Hoddmod Hx]]]]].
  Exists odd.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial.
    + exact Hret0.
    + exact Hret32.
    + exact Hoddpos.
    + apply gmp_mod1_to_rem1; [lia | exact Hoddmod].
    + exact Hx.
Qed.

Lemma proof_of_gmp_ctz_partial_solve_wit_1_pure : gmp_ctz_partial_solve_wit_1_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (gmp_lowbit_pos_bound x_pre PreH1) as [Hpos Hle].
  split_pures; dump_pre_spatial.
  - lia.
  - exact Hpos.
Qed.

Lemma proof_of_mpn_gcd_11_entail_wit_1_1_split_goal_1 :
  mpn_gcd_11_entail_wit_1_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hoddmod : odd mod 2 = 1)
    by (apply gmp_rem1_to_mod1; [lia | exact PreH5]).
  pose proof (gmp_lor_ctz_prepare u_pre v_pre odd retval 4294967295
    PreH9 PreH10 PreH11 PreH12 PreH8 PreH7 PreH2 Hoddmod PreH6)
    as [Hu_pos [Hu_le [Hv_pos [Hv_le Hgcd]]]].
  rewrite (Z.gcd_comm (Z.shiftr v_pre retval) (Z.shiftr u_pre retval)).
  exact Hgcd.
Qed.

Lemma proof_of_mpn_gcd_11_entail_wit_1_1_split_goal_2 :
  mpn_gcd_11_entail_wit_1_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hoddmod : odd mod 2 = 1)
    by (apply gmp_rem1_to_mod1; [lia | exact PreH5]).
  pose proof (gmp_lor_shifted_odd_r u_pre v_pre odd retval
    PreH2 Hoddmod PreH6 PreH1) as Hv_odd.
  exact Hv_odd.
Qed.

Lemma proof_of_mpn_gcd_11_entail_wit_1_1_split_goal_3 :
  mpn_gcd_11_entail_wit_1_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hoddmod : odd mod 2 = 1)
    by (apply gmp_rem1_to_mod1; [lia | exact PreH5]).
  pose proof (gmp_lor_ctz_prepare u_pre v_pre odd retval 4294967295
    PreH9 PreH10 PreH11 PreH12 PreH8 PreH7 PreH2 Hoddmod PreH6)
    as [Hu_pos [Hu_le [Hv_pos [Hv_le Hgcd]]]].
  exact Hu_le.
Qed.

Lemma proof_of_mpn_gcd_11_entail_wit_1_1_split_goal_4 :
  mpn_gcd_11_entail_wit_1_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hoddmod : odd mod 2 = 1)
    by (apply gmp_rem1_to_mod1; [lia | exact PreH5]).
  pose proof (gmp_lor_ctz_prepare u_pre v_pre odd retval 4294967295
    PreH9 PreH10 PreH11 PreH12 PreH8 PreH7 PreH2 Hoddmod PreH6)
    as [Hu_pos [Hu_le [Hv_pos [Hv_le Hgcd]]]].
  exact Hu_pos.
Qed.

Lemma proof_of_mpn_gcd_11_entail_wit_1_1_split_goal_5 :
  mpn_gcd_11_entail_wit_1_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hoddmod : odd mod 2 = 1)
    by (apply gmp_rem1_to_mod1; [lia | exact PreH5]).
  pose proof (gmp_lor_ctz_prepare u_pre v_pre odd retval 4294967295
    PreH9 PreH10 PreH11 PreH12 PreH8 PreH7 PreH2 Hoddmod PreH6)
    as [Hu_pos [Hu_le [Hv_pos [Hv_le Hgcd]]]].
  exact Hv_le.
Qed.

Lemma proof_of_mpn_gcd_11_entail_wit_1_1_split_goal_6 :
  mpn_gcd_11_entail_wit_1_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hoddmod : odd mod 2 = 1)
    by (apply gmp_rem1_to_mod1; [lia | exact PreH5]).
  pose proof (gmp_lor_ctz_prepare u_pre v_pre odd retval 4294967295
    PreH9 PreH10 PreH11 PreH12 PreH8 PreH7 PreH2 Hoddmod PreH6)
    as [Hu_pos [Hu_le [Hv_pos [Hv_le Hgcd]]]].
  exact Hv_pos.
Qed.

Lemma proof_of_mpn_gcd_11_entail_wit_1_1 : mpn_gcd_11_entail_wit_1_1.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_mpn_gcd_11_entail_wit_1_1_split_goal_1.
  + Goal_apply proof_of_mpn_gcd_11_entail_wit_1_1_split_goal_2.
  + Goal_apply proof_of_mpn_gcd_11_entail_wit_1_1_split_goal_3.
  + Goal_apply proof_of_mpn_gcd_11_entail_wit_1_1_split_goal_4.
  + Goal_apply proof_of_mpn_gcd_11_entail_wit_1_1_split_goal_5.
  + Goal_apply proof_of_mpn_gcd_11_entail_wit_1_1_split_goal_6.
Qed.

Lemma proof_of_mpn_gcd_11_entail_wit_1_2_split_goal_1 :
  mpn_gcd_11_entail_wit_1_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hoddmod : odd mod 2 = 1)
    by (apply gmp_rem1_to_mod1; [lia | exact PreH5]).
  pose proof (gmp_lor_ctz_prepare u_pre v_pre odd retval 4294967295
    PreH9 PreH10 PreH11 PreH12 PreH8 PreH7 PreH2 Hoddmod PreH6)
    as [Hu_pos [Hu_le [Hv_pos [Hv_le Hgcd]]]].
  exact Hgcd.
Qed.

Lemma proof_of_mpn_gcd_11_entail_wit_1_2_split_goal_2 :
  mpn_gcd_11_entail_wit_1_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hoddmod : odd mod 2 = 1)
    by (apply gmp_rem1_to_mod1; [lia | exact PreH5]).
  pose proof (gmp_lor_ctz_prepare u_pre v_pre odd retval 4294967295
    PreH9 PreH10 PreH11 PreH12 PreH8 PreH7 PreH2 Hoddmod PreH6)
    as [Hu_pos [Hu_le [Hv_pos [Hv_le Hgcd]]]].
  exact Hv_le.
Qed.

Lemma proof_of_mpn_gcd_11_entail_wit_1_2_split_goal_3 :
  mpn_gcd_11_entail_wit_1_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hoddmod : odd mod 2 = 1)
    by (apply gmp_rem1_to_mod1; [lia | exact PreH5]).
  pose proof (gmp_lor_ctz_prepare u_pre v_pre odd retval 4294967295
    PreH9 PreH10 PreH11 PreH12 PreH8 PreH7 PreH2 Hoddmod PreH6)
    as [Hu_pos [Hu_le [Hv_pos [Hv_le Hgcd]]]].
  exact Hv_pos.
Qed.

Lemma proof_of_mpn_gcd_11_entail_wit_1_2_split_goal_4 :
  mpn_gcd_11_entail_wit_1_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hoddmod : odd mod 2 = 1)
    by (apply gmp_rem1_to_mod1; [lia | exact PreH5]).
  pose proof (gmp_lor_ctz_prepare u_pre v_pre odd retval 4294967295
    PreH9 PreH10 PreH11 PreH12 PreH8 PreH7 PreH2 Hoddmod PreH6)
    as [Hu_pos [Hu_le [Hv_pos [Hv_le Hgcd]]]].
  exact Hu_le.
Qed.

Lemma proof_of_mpn_gcd_11_entail_wit_1_2_split_goal_5 :
  mpn_gcd_11_entail_wit_1_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hoddmod : odd mod 2 = 1)
    by (apply gmp_rem1_to_mod1; [lia | exact PreH5]).
  pose proof (gmp_lor_ctz_prepare u_pre v_pre odd retval 4294967295
    PreH9 PreH10 PreH11 PreH12 PreH8 PreH7 PreH2 Hoddmod PreH6)
    as [Hu_pos [Hu_le [Hv_pos [Hv_le Hgcd]]]].
  exact Hu_pos.
Qed.

Lemma proof_of_mpn_gcd_11_entail_wit_1_2 : mpn_gcd_11_entail_wit_1_2.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_mpn_gcd_11_entail_wit_1_2_split_goal_1.
  + Goal_apply proof_of_mpn_gcd_11_entail_wit_1_2_split_goal_2.
  + Goal_apply proof_of_mpn_gcd_11_entail_wit_1_2_split_goal_3.
  + Goal_apply proof_of_mpn_gcd_11_entail_wit_1_2_split_goal_4.
  + Goal_apply proof_of_mpn_gcd_11_entail_wit_1_2_split_goal_5.
Qed.

Lemma proof_of_mpn_gcd_11_entail_wit_2_split_goal_1 :
  mpn_gcd_11_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (gmp_gcd_shiftr1_even_r u v PreH8 PreH10 PreH12 PreH1) as Hg.
  rewrite <- Hg in PreH13.
  exact PreH13.
Qed.

Lemma proof_of_mpn_gcd_11_entail_wit_2_split_goal_2 :
  mpn_gcd_11_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (gmp_shiftr1_even_pos_bound v 4294967295 PreH10 PreH11 PreH1)
    as [Hv_pos Hv_le].
  exact Hv_le.
Qed.

Lemma proof_of_mpn_gcd_11_entail_wit_2_split_goal_3 :
  mpn_gcd_11_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (gmp_shiftr1_even_pos_bound v 4294967295 PreH10 PreH11 PreH1)
    as [Hv_pos Hv_le].
  exact Hv_pos.
Qed.

Lemma proof_of_mpn_gcd_11_entail_wit_2 : mpn_gcd_11_entail_wit_2.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_mpn_gcd_11_entail_wit_2_split_goal_1.
  + Goal_apply proof_of_mpn_gcd_11_entail_wit_2_split_goal_2.
  + Goal_apply proof_of_mpn_gcd_11_entail_wit_2_split_goal_3.
Qed.

Lemma proof_of_mpn_gcd_11_entail_wit_4_split_goal_1 :
  mpn_gcd_11_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (gmp_gcd_shiftr1_even_l u v PreH8 PreH10 PreH1 PreH12) as Hg.
  rewrite <- Hg in PreH13.
  exact PreH13.
Qed.

Lemma proof_of_mpn_gcd_11_entail_wit_4_split_goal_2 :
  mpn_gcd_11_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (gmp_shiftr1_even_pos_bound u 4294967295 PreH8 PreH9 PreH1)
    as [Hu_pos Hu_le].
  exact Hu_le.
Qed.

Lemma proof_of_mpn_gcd_11_entail_wit_4_split_goal_3 :
  mpn_gcd_11_entail_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (gmp_shiftr1_even_pos_bound u 4294967295 PreH8 PreH9 PreH1)
    as [Hu_pos Hu_le].
  exact Hu_pos.
Qed.

Lemma proof_of_mpn_gcd_11_entail_wit_4 : mpn_gcd_11_entail_wit_4.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_mpn_gcd_11_entail_wit_4_split_goal_1.
  + Goal_apply proof_of_mpn_gcd_11_entail_wit_4_split_goal_2.
  + Goal_apply proof_of_mpn_gcd_11_entail_wit_4_split_goal_3.
Qed.

Lemma proof_of_mpn_gcd_11_entail_wit_5_split_goal_1 :
  mpn_gcd_11_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (gmp_gcd_sub_odd_shiftr_l u v PreH1 PreH11 PreH13 PreH14) as Hg.
  rewrite <- Hg in PreH15.
  exact PreH15.
Qed.

Lemma proof_of_mpn_gcd_11_entail_wit_5_split_goal_2 :
  mpn_gcd_11_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (gmp_odd_sub_even_land u v ltac:(lia) PreH9 PreH11 PreH13 PreH14)
    as Hdiff_even.
  pose proof (gmp_shiftr1_even_pos_bound (u - v) 4294967295
    ltac:(lia) ltac:(lia) Hdiff_even) as [Hdiff_pos Hdiff_le].
  exact Hdiff_le.
Qed.

Lemma proof_of_mpn_gcd_11_entail_wit_5_split_goal_3 :
  mpn_gcd_11_entail_wit_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (gmp_odd_sub_even_land u v ltac:(lia) PreH9 PreH11 PreH13 PreH14)
    as Hdiff_even.
  pose proof (gmp_shiftr1_even_pos_bound (u - v) 4294967295
    ltac:(lia) ltac:(lia) Hdiff_even) as [Hdiff_pos Hdiff_le].
  exact Hdiff_pos.
Qed.

Lemma proof_of_mpn_gcd_11_entail_wit_5 : mpn_gcd_11_entail_wit_5.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_mpn_gcd_11_entail_wit_5_split_goal_1.
  + Goal_apply proof_of_mpn_gcd_11_entail_wit_5_split_goal_2.
  + Goal_apply proof_of_mpn_gcd_11_entail_wit_5_split_goal_3.
Qed.

Lemma proof_of_mpn_gcd_11_entail_wit_6_split_goal_1 :
  mpn_gcd_11_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (gmp_gcd_shiftr1_even_r u v PreH8 PreH10 PreH12 PreH1) as Hg.
  rewrite <- Hg in PreH13.
  exact PreH13.
Qed.

Lemma proof_of_mpn_gcd_11_entail_wit_6_split_goal_2 :
  mpn_gcd_11_entail_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (gmp_shiftr1_even_pos_bound v 4294967295 PreH10 PreH11 PreH1)
    as [Hv_pos Hv_le].
  exact Hv_le.
Qed.

Lemma proof_of_mpn_gcd_11_entail_wit_6_split_goal_3 :
  mpn_gcd_11_entail_wit_6_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (gmp_shiftr1_even_pos_bound v 4294967295 PreH10 PreH11 PreH1)
    as [Hv_pos Hv_le].
  exact Hv_pos.
Qed.

Lemma proof_of_mpn_gcd_11_entail_wit_6 : mpn_gcd_11_entail_wit_6.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_mpn_gcd_11_entail_wit_6_split_goal_1.
  + Goal_apply proof_of_mpn_gcd_11_entail_wit_6_split_goal_2.
  + Goal_apply proof_of_mpn_gcd_11_entail_wit_6_split_goal_3.
Qed.

Lemma proof_of_mpn_gcd_11_entail_wit_7_split_goal_1 :
  mpn_gcd_11_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (Hgt : v > u) by lia.
  pose proof (gmp_gcd_sub_odd_shiftr_r u v Hgt PreH9 PreH13 PreH14) as Hg.
  rewrite <- Hg in PreH15.
  exact PreH15.
Qed.

Lemma proof_of_mpn_gcd_11_entail_wit_7_split_goal_2 :
  mpn_gcd_11_entail_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (gmp_odd_sub_even_land v u ltac:(lia) PreH11 PreH9 PreH14 PreH13)
    as Hdiff_even.
  pose proof (gmp_shiftr1_even_pos_bound (v - u) 4294967295
    ltac:(lia) ltac:(lia) Hdiff_even) as [Hdiff_pos Hdiff_le].
  exact Hdiff_le.
Qed.

Lemma proof_of_mpn_gcd_11_entail_wit_7_split_goal_3 :
  mpn_gcd_11_entail_wit_7_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (gmp_odd_sub_even_land v u ltac:(lia) PreH11 PreH9 PreH14 PreH13)
    as Hdiff_even.
  pose proof (gmp_shiftr1_even_pos_bound (v - u) 4294967295
    ltac:(lia) ltac:(lia) Hdiff_even) as [Hdiff_pos Hdiff_le].
  exact Hdiff_pos.
Qed.

Lemma proof_of_mpn_gcd_11_entail_wit_7 : mpn_gcd_11_entail_wit_7.
Proof.
  aggressive_pre_process.
  + Goal_apply proof_of_mpn_gcd_11_entail_wit_7_split_goal_1.
  + Goal_apply proof_of_mpn_gcd_11_entail_wit_7_split_goal_2.
  + Goal_apply proof_of_mpn_gcd_11_entail_wit_7_split_goal_3.
Qed.

Lemma proof_of_mpn_gcd_11_return_wit_1_split_goal_1 :
  mpn_gcd_11_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (gmp_gcd_final_shift_return_32 u_pre v_pre u v shift
    PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH14)
    as Hret.
  rewrite <- PreH1.
  exact Hret.
Qed.

Lemma proof_of_mpn_gcd_11_return_wit_1 : mpn_gcd_11_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpn_gcd_11_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_mpn_gcd_11_return_wit_2 : mpn_gcd_11_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    rewrite PreH1, Z.gcd_0_r.
    rewrite Z.abs_eq; lia.
Qed.

Lemma proof_of_mpn_gcd_11_return_wit_3 : mpn_gcd_11_return_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial.
    rewrite PreH1, Z.gcd_0_l.
    rewrite Z.abs_eq; lia.
Qed.

Lemma proof_of_mpn_gcd_11_partial_solve_wit_1_pure : mpn_gcd_11_partial_solve_wit_1_pure.
Proof.
  LLM_pre_process ltac:(int_auto).
  pose proof (gmp_lor_pos_bound_32 u_pre v_pre
    PreH3 PreH4 PreH5 PreH6 PreH2 PreH1) as [Hpos Hle].
  split_pures; dump_pre_spatial.
  - exact Hle.
  - exact Hpos.
Qed.
