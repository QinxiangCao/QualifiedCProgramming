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
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_tdiv_r_read0_goal.
From SimpleC.EE.Applications_human.fme_ge_gmp.gmp Require Import mpz_tdiv_r_read0_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.fme_ge_gmp.gmp.gmp_lib.
Local Open Scope sac.

(* Already discharged by mpz_tdiv_r_read0_proof_auto after solver regeneration.
Lemma proof_of_mpz_div_qr_return_wit_1_nonalias_done : mpz_div_qr_return_wit_1_nonalias_done.
Proof.
  LLM_pre_process ltac:(int_auto).
  Left.
  Exists qout rout.
  split_pure_spatial.
  - normalize.
    repeat cancel.
  - split_pures; dump_pre_spatial; try assumption;
      unfold mpz_div_qr_ret_ok in *; lia.
Qed.
*)

Lemma proof_of_mpz_div_qr_return_wit_2_nonalias_done : mpz_div_qr_return_wit_2_nonalias_done.
Proof.
  LLM_pre_process ltac:(int_auto).
  Left.
  Exists qout rout.
  split_pure_spatial.
  - normalize.
    repeat cancel.
  - split_pures; dump_pre_spatial; try assumption;
      unfold mpz_div_qr_ret_ok in *; lia.
Qed.

(* Already discharged by mpz_tdiv_r_read0_proof_auto after solver regeneration.
Lemma proof_of_mpz_div_qr_return_wit_3_r_eq_n_done : mpz_div_qr_return_wit_3_r_eq_n_done.
Proof.
  LLM_pre_process ltac:(int_auto).
  Right.
  Exists qout rout.
  split_pure_spatial.
  - normalize.
    repeat cancel.
  - split_pures; dump_pre_spatial; try assumption;
      unfold mpz_div_qr_ret_ok in *; lia.
Qed.
*)

Lemma proof_of_mpz_div_qr_return_wit_4_r_eq_n_done : mpz_div_qr_return_wit_4_r_eq_n_done.
Proof.
  LLM_pre_process ltac:(int_auto).
  Right.
  Exists qout rout.
  split_pure_spatial.
  - normalize.
    repeat cancel.
  - split_pures; dump_pre_spatial; try assumption;
      unfold mpz_div_qr_ret_ok in *; lia.
Qed.

Lemma proof_of_mpz_div_qr_return_wit_5_nonalias : mpz_div_qr_return_wit_5_nonalias.
Proof.
  (LLM_pre_process ltac:(int_auto)); Exists 0 zn_nonalias.
  assert (Hzn_nz : zn_nonalias <> 0).
  { assert (0 < Zabs zn_nonalias).
    { eapply is_compact_Z_size_pos_value_pos; eauto; lia. }
    lia. }
  assert (Habs_lt : Zabs zn_nonalias < Zabs zd_nonalias).
  { eapply is_compact_Z_size_lt_value_lt; eauto; lia. }
  assert (Hmath : mpz_div_qr_math mode0_nonalias zn_nonalias zd_nonalias 0 zn_nonalias).
  { eapply (mpz_div_qr_math_small_remainder
      mode0_nonalias zn_nonalias zd_nonalias size size_2).
    - unfold valid_mpz_div_round_mode, GMP_DIV_TRUNC; lia.
    - unfold mpz_div_qr_small_q0_case, GMP_DIV_TRUNC; lia.
    - exact Hzn_nz.
    - assumption.
    - assumption.
    - assumption.
    - exact Habs_lt. }
  sep_apply (store_Z_from_fields d0_nonalias ptr size_2 cap_2
    zd_nonalias ltac:(assumption) ltac:(assumption)).
  sep_apply (store_Z_zero_from_fields q0_nonalias ptr_2 size_3 cap_3
    old_q_nonalias ltac:(assumption) ltac:(assumption)).
  sep_apply (store_Z_to_optional_store_Z_nonzero q0_nonalias 0
    ltac:(unfold NULL in *; lia)).
  sep_apply (store_Z_to_optional_store_Z_nonzero r0_nonalias zn_nonalias
    ltac:(unfold NULL in *; lia)).
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    unfold mpz_div_qr_ret_ok; lia.
Qed.

Lemma proof_of_mpz_div_qr_return_wit_6_r_eq_n_read0 : mpz_div_qr_return_wit_6_r_eq_n_read0.
Proof.
  (LLM_pre_process ltac:(int_auto)); Exists 0 zn_r_eq_n_read0.
  assert (Hzn_nz : zn_r_eq_n_read0 <> 0).
  { assert (0 < Zabs zn_r_eq_n_read0).
    { eapply is_compact_Z_size_pos_value_pos; eauto; lia. }
    lia. }
  assert (Habs_lt : Zabs zn_r_eq_n_read0 < Zabs zd_r_eq_n_read0).
  { eapply is_compact_Z_size_lt_value_lt; eauto; lia. }
  assert (Hmath :
    mpz_div_qr_math mode0_r_eq_n_read0 zn_r_eq_n_read0
      zd_r_eq_n_read0 0 zn_r_eq_n_read0).
  { eapply (mpz_div_qr_math_small_remainder
      mode0_r_eq_n_read0 zn_r_eq_n_read0 zd_r_eq_n_read0 size size_2).
    - unfold valid_mpz_div_round_mode, GMP_DIV_TRUNC; lia.
    - unfold mpz_div_qr_small_q0_case, GMP_DIV_TRUNC; lia.
    - exact Hzn_nz.
    - assumption.
    - assumption.
    - assumption.
    - exact Habs_lt. }
  sep_apply (store_Z_to_store_Z_read0_nonzero
    n0_r_eq_n_read0 zn_r_eq_n_read0 Hzn_nz).
  sep_apply (store_Z_from_fields d0_r_eq_n_read0 ptr size_2 cap_2
    zd_r_eq_n_read0 ltac:(assumption) ltac:(assumption)).
  sep_apply (store_Z_zero_from_fields q0_r_eq_n_read0 ptr_2 size_3 cap_3
    old_q_r_eq_n_read0 ltac:(assumption) ltac:(assumption)).
  sep_apply (store_Z_to_optional_store_Z_nonzero q0_r_eq_n_read0 0
    ltac:(unfold NULL in *; lia)).
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    unfold mpz_div_qr_ret_ok; lia.
Qed.

Lemma proof_of_mpz_div_qr_return_wit_7_nonalias : mpz_div_qr_return_wit_7_nonalias.
Proof.
  (LLM_pre_process ltac:(int_auto)); Exists 0 zn_nonalias.
  prop_apply (mpd_store_Z_compact_pos UINT_MOD UINT_MOD_pos ptr
    (Zabs zn_nonalias) (Zabs size) ltac:(lia)).
  Intros.
  prop_apply (mpd_store_Z_to_is_compact_Z ptr (Zabs zn_nonalias) (Zabs size)).
  Intros.
  prop_apply (mpd_store_Z_to_is_compact_Z ptr_2 (Zabs zd_nonalias) (Zabs size_2)).
  Intros.
  sep_apply (store_Z_from_fields n0_nonalias ptr size cap zn_nonalias
    ltac:(assumption) ltac:(assumption)).
  sep_apply (store_Z_from_fields d0_nonalias ptr_2 size_2 cap_2
    zd_nonalias ltac:(assumption) ltac:(assumption)).
  sep_apply (store_Z_zero_from_fields q0_nonalias ptr_3 size_3 cap_3
    old_q_nonalias ltac:(assumption) ltac:(assumption)).
  sep_apply (store_Z_to_optional_store_Z_nonzero q0_nonalias 0
    ltac:(unfold NULL in *; lia)).
  split_pure_spatial.
  - sep_apply_right (emp_to_optional_store_Z_null r0_nonalias
      zn_nonalias ltac:(unfold NULL in *; lia)).
    normalize.
    repeat cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    + unfold mpz_div_qr_math; left.
      unfold mpz_div_qr_math_trunc, GMP_DIV_TRUNC.
      repeat split; try lia; try ring.
      * eapply is_compact_Z_size_lt_value_lt; eauto; lia.
      * right; apply same_sign_refl.
    + unfold mpz_div_qr_ret_ok; split; lia.
Qed.

Lemma proof_of_mpz_div_qr_return_wit_8_nonalias : mpz_div_qr_return_wit_8_nonalias.
Proof.
  (LLM_pre_process ltac:(int_auto)); Exists 0 zn_nonalias.
  assert (Hzn_nz : zn_nonalias <> 0).
  { assert (0 < Zabs zn_nonalias).
    { eapply is_compact_Z_size_pos_value_pos; eauto; lia. }
    lia. }
  assert (Habs_lt : Zabs zn_nonalias < Zabs zd_nonalias).
  { eapply is_compact_Z_size_lt_value_lt; eauto; lia. }
  assert (Hmath : mpz_div_qr_math mode0_nonalias zn_nonalias zd_nonalias 0 zn_nonalias).
  { eapply (mpz_div_qr_math_small_remainder
      mode0_nonalias zn_nonalias zd_nonalias size size_2).
    - unfold valid_mpz_div_round_mode, GMP_DIV_TRUNC; lia.
    - unfold mpz_div_qr_small_q0_case, GMP_DIV_TRUNC; lia.
    - exact Hzn_nz.
    - assumption.
    - assumption.
    - assumption.
    - exact Habs_lt. }
  sep_apply (store_Z_from_fields d0_nonalias ptr size_2 cap_2
    zd_nonalias ltac:(assumption) ltac:(assumption)).
  sep_apply (optional_store_Z_null_change q0_nonalias old_q_nonalias 0
    ltac:(unfold NULL in *; lia)).
  sep_apply (store_Z_to_optional_store_Z_nonzero r0_nonalias zn_nonalias
    ltac:(unfold NULL in *; lia)).
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    unfold mpz_div_qr_ret_ok; lia.
Qed.

Lemma proof_of_mpz_div_qr_return_wit_9_r_eq_n_read0 : mpz_div_qr_return_wit_9_r_eq_n_read0.
Proof.
  (LLM_pre_process ltac:(int_auto)); Exists 0 zn_r_eq_n_read0.
  assert (Hzn_nz : zn_r_eq_n_read0 <> 0).
  { assert (0 < Zabs zn_r_eq_n_read0).
    { eapply is_compact_Z_size_pos_value_pos; eauto; lia. }
    lia. }
  assert (Habs_lt : Zabs zn_r_eq_n_read0 < Zabs zd_r_eq_n_read0).
  { eapply is_compact_Z_size_lt_value_lt; eauto; lia. }
  assert (Hmath :
    mpz_div_qr_math mode0_r_eq_n_read0 zn_r_eq_n_read0
      zd_r_eq_n_read0 0 zn_r_eq_n_read0).
  { eapply (mpz_div_qr_math_small_remainder
      mode0_r_eq_n_read0 zn_r_eq_n_read0 zd_r_eq_n_read0 size size_2).
    - unfold valid_mpz_div_round_mode, GMP_DIV_TRUNC; lia.
    - unfold mpz_div_qr_small_q0_case, GMP_DIV_TRUNC; lia.
    - exact Hzn_nz.
    - assumption.
    - assumption.
    - assumption.
    - exact Habs_lt. }
  sep_apply (store_Z_to_store_Z_read0_nonzero
    n0_r_eq_n_read0 zn_r_eq_n_read0 Hzn_nz).
  sep_apply (store_Z_from_fields d0_r_eq_n_read0 ptr size_2 cap_2
    zd_r_eq_n_read0 ltac:(assumption) ltac:(assumption)).
  sep_apply (optional_store_Z_null_change q0_r_eq_n_read0
    old_q_r_eq_n_read0 0 ltac:(unfold NULL in *; lia)).
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    unfold mpz_div_qr_ret_ok; lia.
Qed.

Lemma proof_of_mpz_div_qr_return_wit_10_nonalias : mpz_div_qr_return_wit_10_nonalias.
Proof.
  (LLM_pre_process ltac:(int_auto)); Exists 0 zn_nonalias.
  prop_apply (mpd_store_Z_compact_pos UINT_MOD UINT_MOD_pos ptr
    (Zabs zn_nonalias) (Zabs size) ltac:(lia)).
  Intros.
  prop_apply (mpd_store_Z_to_is_compact_Z ptr (Zabs zn_nonalias) (Zabs size)).
  Intros.
  prop_apply (mpd_store_Z_to_is_compact_Z ptr_2 (Zabs zd_nonalias) (Zabs size_2)).
  Intros.
  sep_apply (store_Z_from_fields n0_nonalias ptr size cap zn_nonalias
    ltac:(assumption) ltac:(assumption)).
  sep_apply (store_Z_from_fields d0_nonalias ptr_2 size_2 cap_2
    zd_nonalias ltac:(assumption) ltac:(assumption)).
  sep_apply (optional_store_Z_null_change q0_nonalias old_q_nonalias 0
    ltac:(unfold NULL in *; lia)).
  sep_apply (optional_store_Z_null_change r0_nonalias old_r_nonalias
    zn_nonalias ltac:(unfold NULL in *; lia)).
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    + unfold mpz_div_qr_math; left.
      unfold mpz_div_qr_math_trunc, GMP_DIV_TRUNC.
      repeat split; try lia; try ring.
      * eapply is_compact_Z_size_lt_value_lt; eauto; lia.
      * right; apply same_sign_refl.
    + unfold mpz_div_qr_ret_ok; split; lia.
Qed.

Lemma proof_of_mpz_div_qr_return_wit_11_nonalias : mpz_div_qr_return_wit_11_nonalias.
Proof.
  (LLM_pre_process ltac:(int_auto)); Exists 0 0.
  prop_apply (mpd_store_Z_to_is_compact_Z ptr (Zabs zn_nonalias) (Zabs size)).
  Intros.
  assert (Hzn0 : zn_nonalias = 0).
  { pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos
      (Zabs zn_nonalias) (Zabs size) H) as [_ [[Hsize Hz] | [Hsize _]]]; lia. }
  subst zn_nonalias.
  sep_apply (store_Z_from_fields n0_nonalias ptr size cap 0
    ltac:(assumption) ltac:(assumption)).
  sep_apply (store_Z_from_fields d0_nonalias ptr_2 size_2 cap_2
    zd_nonalias ltac:(assumption) ltac:(assumption)).
  sep_apply (store_Z_zero_from_fields q0_nonalias ptr_3 size_3 cap_3
    old_q_nonalias ltac:(assumption) ltac:(assumption)).
  sep_apply (store_Z_zero_from_fields r0_nonalias ptr_4 size_4 cap_4
    old_r_nonalias ltac:(assumption) ltac:(assumption)).
  sep_apply (store_Z_to_optional_store_Z_nonzero q0_nonalias 0
    ltac:(unfold NULL in *; lia)).
  sep_apply (store_Z_to_optional_store_Z_nonzero r0_nonalias 0
    ltac:(unfold NULL in *; lia)).
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    + eapply mpz_div_qr_math_zero_all_modes.
      * unfold valid_mpz_div_round_mode, GMP_DIV_TRUNC; lia.
      * assumption.
    + unfold mpz_div_qr_ret_ok; split; lia.
Qed.

Lemma proof_of_mpz_div_qr_return_wit_12_r_eq_n_read0 : mpz_div_qr_return_wit_12_r_eq_n_read0.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos
    (Zabs zn_r_eq_n_read0) (Zabs size) PreH4)
    as [_ [[Hsize Hzn] | [Hsize _]]];
  exfalso; lia.
Qed.

Lemma proof_of_mpz_div_qr_return_wit_13_nonalias : mpz_div_qr_return_wit_13_nonalias.
Proof.
  (LLM_pre_process ltac:(int_auto)); Exists 0 0.
  prop_apply (mpd_store_Z_to_is_compact_Z ptr (Zabs zn_nonalias) (Zabs size)).
  Intros.
  assert (Hzn0 : zn_nonalias = 0).
  { pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos
      (Zabs zn_nonalias) (Zabs size) H) as [_ [[Hsize Hz] | [Hsize _]]]; lia. }
  subst zn_nonalias.
  sep_apply (store_Z_from_fields n0_nonalias ptr size cap 0
    ltac:(assumption) ltac:(assumption)).
  sep_apply (store_Z_from_fields d0_nonalias ptr_2 size_2 cap_2
    zd_nonalias ltac:(assumption) ltac:(assumption)).
  sep_apply (store_Z_zero_from_fields r0_nonalias ptr_3 size_3 cap_3
    old_r_nonalias ltac:(assumption) ltac:(assumption)).
  sep_apply (store_Z_to_optional_store_Z_nonzero r0_nonalias 0
    ltac:(unfold NULL in *; lia)).
  split_pure_spatial.
  - sep_apply_right (emp_to_optional_store_Z_null q0_nonalias 0
      ltac:(unfold NULL in *; lia)).
    normalize.
    repeat cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    + eapply mpz_div_qr_math_zero_all_modes.
      * unfold valid_mpz_div_round_mode, GMP_DIV_TRUNC; lia.
      * assumption.
    + unfold mpz_div_qr_ret_ok; split; lia.
Qed.

Lemma proof_of_mpz_div_qr_return_wit_14_r_eq_n_read0 : mpz_div_qr_return_wit_14_r_eq_n_read0.
Proof.
  LLM_pre_process ltac:(int_auto).
  intros.
  pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos
    (Zabs zn_r_eq_n_read0) (Zabs size) PreH2)
    as [_ [[Hsize Hzn] | [Hsize _]]];
  exfalso; lia.
Qed.

Lemma proof_of_mpz_div_qr_return_wit_15_nonalias : mpz_div_qr_return_wit_15_nonalias.
Proof.
  (LLM_pre_process ltac:(int_auto)); Exists 0 0.
  prop_apply (mpd_store_Z_to_is_compact_Z ptr (Zabs zn_nonalias) (Zabs size)).
  Intros.
  assert (Hzn0 : zn_nonalias = 0).
  { pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos
      (Zabs zn_nonalias) (Zabs size) H) as [_ [[Hsize Hz] | [Hsize _]]]; lia. }
  subst zn_nonalias.
  sep_apply (store_Z_from_fields n0_nonalias ptr size cap 0
    ltac:(assumption) ltac:(assumption)).
  sep_apply (store_Z_from_fields d0_nonalias ptr_2 size_2 cap_2
    zd_nonalias ltac:(assumption) ltac:(assumption)).
  sep_apply (store_Z_zero_from_fields q0_nonalias ptr_3 size_3 cap_3
    old_q_nonalias ltac:(assumption) ltac:(assumption)).
  sep_apply (store_Z_to_optional_store_Z_nonzero q0_nonalias 0
    ltac:(unfold NULL in *; lia)).
  sep_apply (optional_store_Z_null_change r0_nonalias old_r_nonalias 0
    ltac:(unfold NULL in *; lia)).
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    + eapply mpz_div_qr_math_zero_all_modes.
      * unfold valid_mpz_div_round_mode, GMP_DIV_TRUNC; lia.
      * assumption.
    + unfold mpz_div_qr_ret_ok; split; lia.
Qed.

Lemma proof_of_mpz_div_qr_return_wit_16_nonalias : mpz_div_qr_return_wit_16_nonalias.
Proof.
  (LLM_pre_process ltac:(int_auto)); Exists 0 0.
  prop_apply (mpd_store_Z_to_is_compact_Z ptr (Zabs zn_nonalias) (Zabs size)).
  Intros.
  assert (Hzn0 : zn_nonalias = 0).
  { pose proof (is_compact_Z_bounds UINT_MOD UINT_MOD_pos
      (Zabs zn_nonalias) (Zabs size) H) as [_ [[Hsize Hz] | [Hsize _]]]; lia. }
  subst zn_nonalias.
  sep_apply (store_Z_from_fields n0_nonalias ptr size cap 0
    ltac:(assumption) ltac:(assumption)).
  sep_apply (store_Z_from_fields d0_nonalias ptr_2 size_2 cap_2
    zd_nonalias ltac:(assumption) ltac:(assumption)).
  sep_apply (optional_store_Z_null_change q0_nonalias old_q_nonalias 0
    ltac:(unfold NULL in *; lia)).
  sep_apply (optional_store_Z_null_change r0_nonalias old_r_nonalias 0
    ltac:(unfold NULL in *; lia)).
  split_pure_spatial.
  - cancel.
  - repeat split_pures; dump_pre_spatial;
      try assumption; try reflexivity; try lia.
    + eapply mpz_div_qr_math_zero_all_modes.
      * unfold valid_mpz_div_round_mode, GMP_DIV_TRUNC; lia.
      * assumption.
    + unfold mpz_div_qr_ret_ok; split; lia.
Qed.

Lemma proof_of_mpz_div_qr_partial_solve_wit_11_nonalias_pure_split_goal_1 :
  mpz_div_qr_partial_solve_wit_11_nonalias_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_div_qr_partial_solve_wit_11_nonalias_pure : mpz_div_qr_partial_solve_wit_11_nonalias_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_div_qr_partial_solve_wit_11_nonalias_pure_split_goal_1.
Qed.

Lemma proof_of_mpz_div_qr_partial_solve_wit_12_r_eq_n_read0_pure_split_goal_1 :
  mpz_div_qr_partial_solve_wit_12_r_eq_n_read0_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_div_qr_partial_solve_wit_12_r_eq_n_read0_pure : mpz_div_qr_partial_solve_wit_12_r_eq_n_read0_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_div_qr_partial_solve_wit_12_r_eq_n_read0_pure_split_goal_1.
Qed.

Lemma proof_of_mpz_div_qr_partial_solve_wit_13_nonalias_pure_split_goal_1 :
  mpz_div_qr_partial_solve_wit_13_nonalias_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_div_qr_partial_solve_wit_13_nonalias_pure : mpz_div_qr_partial_solve_wit_13_nonalias_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_div_qr_partial_solve_wit_13_nonalias_pure_split_goal_1.
Qed.

Lemma proof_of_mpz_div_qr_partial_solve_wit_14_r_eq_n_read0_pure_split_goal_1 :
  mpz_div_qr_partial_solve_wit_14_r_eq_n_read0_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_mpz_div_qr_partial_solve_wit_14_r_eq_n_read0_pure : mpz_div_qr_partial_solve_wit_14_r_eq_n_read0_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_div_qr_partial_solve_wit_14_r_eq_n_read0_pure_split_goal_1.
Qed.

Lemma proof_of_mpz_tdiv_r_entail_wit_1_split_goal_spatial :
  mpz_tdiv_r_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold optional_store_Z.
  Left.
  split_pure_spatial.
  - normalize.
    repeat cancel.
  - dump_pre_spatial; unfold NULL; lia.
Qed.

Lemma proof_of_mpz_tdiv_r_entail_wit_1 : mpz_tdiv_r_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_tdiv_r_entail_wit_1_split_goal_spatial.
Qed.

Lemma proof_of_mpz_tdiv_r_return_wit_1_split_goal_spatial :
  mpz_tdiv_r_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(int_auto).
  unfold optional_store_Z.
  Split.
  - Intros.
    normalize.
    repeat cancel.
  - Intros.
    exfalso.
    unfold NULL in *; lia.
Qed.

Lemma proof_of_mpz_tdiv_r_return_wit_1 : mpz_tdiv_r_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_mpz_tdiv_r_return_wit_1_split_goal_spatial.
Qed.
