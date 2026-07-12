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
From SimpleC.EE.LLM_bench.Algorithms.sort_point Require Import sort_point_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.sort_point.sort_point_lib.
Local Open Scope sac.

Lemma proof_of_cmp_polar_values_safety_wit_1 : cmp_polar_values_safety_wit_1.
Proof.
  pre_process; entailer!; unfold CoordInBounds in *; nia.
Qed.

Lemma proof_of_cmp_polar_values_safety_wit_2 : cmp_polar_values_safety_wit_2.
Proof.
  pre_process; entailer!; unfold CoordInBounds in *; nia.
Qed.

Lemma proof_of_cmp_polar_values_safety_wit_3 : cmp_polar_values_safety_wit_3.
Proof.
  pre_process; entailer!; unfold CoordInBounds in *; nia.
Qed.

Lemma proof_of_cmp_polar_values_safety_wit_4 : cmp_polar_values_safety_wit_4.
Proof.
  pre_process; entailer!; unfold CoordInBounds in *; nia.
Qed.

Lemma proof_of_cmp_polar_values_safety_wit_5 : cmp_polar_values_safety_wit_5.
Proof.
  pre_process; entailer!; unfold CoordInBounds in *; nia.
Qed.

Lemma proof_of_cmp_polar_values_safety_wit_6 : cmp_polar_values_safety_wit_6.
Proof.
  pre_process; entailer!; unfold CoordInBounds in *; nia.
Qed.

Lemma proof_of_cmp_polar_values_safety_wit_7 : cmp_polar_values_safety_wit_7.
Proof.
  pre_process; entailer!; unfold CoordInBounds in *; nia.
Qed.

Lemma proof_of_cmp_polar_values_safety_wit_8 : cmp_polar_values_safety_wit_8.
Proof.
  pre_process; entailer!; unfold CoordInBounds in *; nia.
Qed.

Lemma proof_of_cmp_polar_values_safety_wit_9 : cmp_polar_values_safety_wit_9.
Proof.
  pre_process; entailer!; unfold CoordInBounds in *; nia.
Qed.

Lemma proof_of_cmp_polar_values_safety_wit_10 : cmp_polar_values_safety_wit_10.
Proof.
  pre_process; entailer!; unfold CoordInBounds in *; nia.
Qed.

Lemma proof_of_cmp_polar_values_safety_wit_11 : cmp_polar_values_safety_wit_11.
Proof.
  pre_process; entailer!; unfold CoordInBounds in *; nia.
Qed.

Lemma proof_of_cmp_polar_values_safety_wit_12 : cmp_polar_values_safety_wit_12.
Proof.
  pre_process; entailer!; unfold CoordInBounds in *; nia.
Qed.

Lemma proof_of_cmp_polar_values_safety_wit_13 : cmp_polar_values_safety_wit_13.
Proof.
  pre_process; entailer!; unfold CoordInBounds in *; nia.
Qed.

Lemma proof_of_cmp_polar_values_return_wit_1 : cmp_polar_values_return_wit_1.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - cbv [derivable1 emp andp coq_prop].
    intros m Hm.
    split.
    + split.
      * unfold PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y; simpl.
        assert (Heqy : a_y_pre = b_y_pre) by lia.
        assert (Heqx : a_x_pre = b_x_pre) by lia.
        subst b_y_pre b_x_pre.
        repeat right.
        repeat split; try reflexivity; try ring.
      * lia.
    + lia.
Qed. 

Lemma proof_of_cmp_polar_values_return_wit_2 : cmp_polar_values_return_wit_2.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - cbv [derivable1 emp andp coq_prop].
    intros m Hm.
    split.
    + split.
      * unfold PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y; simpl.
        assert (Heqy : a_y_pre = b_y_pre) by lia.
        assert (Heqx : a_x_pre = b_x_pre) by lia.
        subst b_y_pre b_x_pre.
        repeat right.
        repeat split; try reflexivity; try ring.
      * lia.
    + lia.
Qed. 

Lemma proof_of_cmp_polar_values_return_wit_3 : cmp_polar_values_return_wit_3.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - cbv [derivable1 emp andp coq_prop].
    intros m Hm.
    split.
    + split.
      * unfold PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y; simpl.
        assert (Heqy : a_y_pre = b_y_pre) by lia.
        assert (Heqx : a_x_pre = b_x_pre) by lia.
        subst b_y_pre b_x_pre.
        repeat right.
        repeat split; try reflexivity; try ring.
      * lia.
    + lia.
Qed. 

Lemma proof_of_cmp_polar_values_return_wit_4 : cmp_polar_values_return_wit_4.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - cbv [derivable1 emp andp coq_prop].
    intros m Hm.
    split.
    + split.
      * unfold PolarCmpResult, polar_upper_half, polar_cross, point_dist2, point_x, point_y; simpl.
        assert (Heqy : a_y_pre = b_y_pre) by lia.
        assert (Heqx : a_x_pre = b_x_pre) by lia.
        subst b_y_pre b_x_pre.
        repeat right.
        repeat split; try reflexivity; try ring.
      * lia.
    + lia.
Qed. 

Lemma proof_of_cmp_polar_values_return_wit_5 : cmp_polar_values_return_wit_5.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - repeat split_pures.
    + dump_pre_spatial.
      unfold PolarCmpResult.
      cbn.
      do 9 right; left.
      repeat split; try lia.
      * rewrite (polar_upper_half_true_of_pos_y gx_pre gy_pre a_x_pre a_y_pre) by lia.
        rewrite (polar_upper_half_true_of_pos_y gx_pre gy_pre b_x_pre b_y_pre) by lia.
        reflexivity.
      * unfold polar_cross. cbn. lia.
      * unfold point_dist2. cbn. nia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
Qed.

Lemma proof_of_cmp_polar_values_return_wit_6 : cmp_polar_values_return_wit_6.
Proof.
  pre_process.
Qed.

Lemma proof_of_cmp_polar_values_return_wit_7 : cmp_polar_values_return_wit_7.
Proof.
  aggressive_pre_process. 
  entailer!.
  unfold PolarCmpResult.
  cbn.
  do 9 right; left.
  repeat split; try lia.
  - rewrite (polar_upper_half_false_of_nonpos_nonzero_y gx_pre gy_pre a_x_pre a_y_pre) by lia.
    rewrite (polar_upper_half_false_of_nonpos_nonzero_y gx_pre gy_pre b_x_pre b_y_pre) by lia.
    reflexivity.
  - unfold polar_cross. cbn. lia.
  - unfold point_dist2. cbn. nia.
Qed.

Lemma proof_of_cmp_polar_values_return_wit_8 : cmp_polar_values_return_wit_8.
Proof.
  pre_process.
  entailer!.
  unfold PolarCmpResult.
  cbn.
  do 8 right; left.
  repeat split; try lia.
  - rewrite (polar_upper_half_true_of_pos_y gx_pre gy_pre a_x_pre a_y_pre) by lia.
    rewrite (polar_upper_half_true_of_pos_y gx_pre gy_pre b_x_pre b_y_pre) by lia.
    reflexivity.
  - unfold polar_cross. cbn. lia.
  - unfold point_dist2. cbn. nia.
Qed.

Lemma proof_of_cmp_polar_values_return_wit_9 : cmp_polar_values_return_wit_9.
Proof.
  pre_process.
Qed.

Lemma proof_of_cmp_polar_values_return_wit_10 : cmp_polar_values_return_wit_10.
Proof.
  pre_process.
  entailer!.
  unfold PolarCmpResult.
  cbn.
  do 8 right; left.
  repeat split; try lia.
  - rewrite (polar_upper_half_false_of_nonpos_nonzero_y gx_pre gy_pre a_x_pre a_y_pre) by lia.
    rewrite (polar_upper_half_false_of_nonpos_nonzero_y gx_pre gy_pre b_x_pre b_y_pre) by lia.
    reflexivity.
  - unfold polar_cross. cbn. lia.
  - unfold point_dist2. cbn. lia.
Qed.

Lemma proof_of_cmp_polar_values_return_wit_11 : cmp_polar_values_return_wit_11.
Proof.
  pre_process.
  try
      (unfold PolarCmpResult, polar_upper_half, polar_cross, point_dist2 in *;
       simpl in *; entailer!).
Qed.

Lemma proof_of_cmp_polar_values_return_wit_12 : cmp_polar_values_return_wit_12.
Proof.
  pre_process;
    try
      (unfold PolarCmpResult, polar_upper_half, polar_cross, point_dist2 in *;
       simpl in *; entailer!).
Qed.

Lemma proof_of_cmp_polar_values_return_wit_13 : cmp_polar_values_return_wit_13.
Proof.
  pre_process;
     try
       (unfold PolarCmpResult, polar_upper_half, polar_cross, point_dist2 in *;
        simpl in *; entailer!).
Qed. 

Lemma proof_of_cmp_polar_values_return_wit_14 : cmp_polar_values_return_wit_14.
Proof.
  pre_process;
    try
      (unfold PolarCmpResult, polar_upper_half, polar_cross, point_dist2 in *;
       simpl in *; entailer!).
Qed. 

Lemma proof_of_cmp_polar_values_return_wit_15 : cmp_polar_values_return_wit_15.
Proof.
  pre_process;
    try
      (unfold PolarCmpResult, polar_upper_half, polar_cross, point_dist2 in *;
       simpl in *; entailer!).
Qed. 

Lemma proof_of_cmp_polar_values_return_wit_16 : cmp_polar_values_return_wit_16.
Proof.
  pre_process;
    try
      (unfold PolarCmpResult, polar_upper_half, polar_cross, point_dist2 in *;
       simpl in *; entailer!).
Qed. 

Lemma proof_of_cmp_polar_values_return_wit_17 : cmp_polar_values_return_wit_17.
Proof.
  pre_process;
    try
      (unfold PolarCmpResult, polar_upper_half, polar_cross, point_dist2 in *;
       simpl in *; entailer!).
Qed. 

Lemma proof_of_cmp_polar_values_return_wit_18 : cmp_polar_values_return_wit_18.
Proof.
  pre_process;
    try
      (unfold PolarCmpResult, polar_upper_half, polar_cross, point_dist2 in *;
       simpl in *; entailer!).
Qed. 

Lemma proof_of_cmp_polar_values_return_wit_19 : cmp_polar_values_return_wit_19.
Proof.
  pre_process;
    try
      (unfold PolarCmpResult, polar_upper_half, polar_cross, point_dist2 in *;
       simpl in *; entailer!).
Qed. 

Lemma proof_of_cmp_polar_values_return_wit_20 : cmp_polar_values_return_wit_20.
Proof.
  pre_process;
    try
      (unfold PolarCmpResult, polar_upper_half, polar_cross, point_dist2 in *;
       simpl in *; entailer!).
Qed. 

Lemma proof_of_cmp_polar_values_return_wit_21 : cmp_polar_values_return_wit_21.
Proof.
  pre_process;
    try
      (unfold PolarCmpResult, polar_upper_half, polar_cross, point_dist2 in *;
       simpl in *; entailer!).
Qed. 

Lemma proof_of_cmp_polar_values_return_wit_22 : cmp_polar_values_return_wit_22.
Proof.
  pre_process;
    try
      (unfold PolarCmpResult, polar_upper_half, polar_cross, point_dist2 in *;
       simpl in *; entailer!).
Qed. 

Lemma proof_of_cmp_polar_values_return_wit_23 : cmp_polar_values_return_wit_23.
Proof.
  pre_process;
    try
      (unfold PolarCmpResult, polar_upper_half, polar_cross, point_dist2 in *;
       simpl in *; entailer!).
Qed. 

Lemma proof_of_cmp_polar_values_return_wit_24 : cmp_polar_values_return_wit_24.
Proof.
  pre_process;
    try
      (unfold PolarCmpResult, polar_upper_half, polar_cross, point_dist2 in *;
       simpl in *; entailer!).
Qed. 

Lemma proof_of_cmp_polar_values_return_wit_25 : cmp_polar_values_return_wit_25.
Proof.
  pre_process;
    try
      (unfold PolarCmpResult, polar_upper_half, polar_cross, point_dist2 in *;
       simpl in *; entailer!).
Qed. 

Lemma proof_of_cmp_polar_values_return_wit_26 : cmp_polar_values_return_wit_26.
Proof.
  pre_process;
    try
      (unfold PolarCmpResult, polar_upper_half, polar_cross, point_dist2 in *;
       simpl in *; entailer!).
Qed. 

Lemma proof_of_cmp_polar_values_return_wit_27 : cmp_polar_values_return_wit_27.
Proof.
  pre_process;
    try
      (unfold PolarCmpResult, polar_upper_half, polar_cross, point_dist2 in *;
       simpl in *; entailer!).
Qed. 

Lemma proof_of_cmp_polar_values_return_wit_28 : cmp_polar_values_return_wit_28.
Proof.
  pre_process;
    try
      (unfold PolarCmpResult, polar_upper_half, polar_cross, point_dist2 in *;
       simpl in *; entailer!).
Qed. 

Lemma proof_of_cmp_polar_values_return_wit_29 : cmp_polar_values_return_wit_29.
Proof.
  pre_process;
    try (
      unfold PolarCmpResult; entailer!;
      first
        [ do 2 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 3 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 5 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 4 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        ]).
Qed.

Lemma proof_of_cmp_polar_values_return_wit_30 : cmp_polar_values_return_wit_30.
Proof.
  pre_process;
    try (
      unfold PolarCmpResult; entailer!;
      first
        [ do 2 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 3 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 5 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 4 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        ]).
Qed.

Lemma proof_of_cmp_polar_values_return_wit_31 : cmp_polar_values_return_wit_31.
Proof.
  pre_process;
    try (
      unfold PolarCmpResult; entailer!;
      first
        [ do 2 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 3 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 5 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 4 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        ]).
Qed.

Lemma proof_of_cmp_polar_values_return_wit_32 : cmp_polar_values_return_wit_32.
Proof.
  pre_process;
    try (
      unfold PolarCmpResult; entailer!;
      first
        [ do 2 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 3 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 5 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 4 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        ]).
Qed.

Lemma proof_of_cmp_polar_values_return_wit_33 : cmp_polar_values_return_wit_33.
Proof.
  pre_process;
    try (
      unfold PolarCmpResult; entailer!;
      first
        [ do 3 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 5 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 4 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        ]).
Qed.

Lemma proof_of_cmp_polar_values_return_wit_34 : cmp_polar_values_return_wit_34.
Proof.
  pre_process;
    try (
      unfold PolarCmpResult; entailer!;
      first
        [ do 3 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 5 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 4 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        ]).
Qed.

Lemma proof_of_cmp_polar_values_return_wit_35 : cmp_polar_values_return_wit_35.
Proof.
  pre_process;
    try (
      unfold PolarCmpResult; entailer!;
      first
        [ do 3 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 5 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 4 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        ]).
Qed.

Lemma proof_of_cmp_polar_values_return_wit_36 : cmp_polar_values_return_wit_36.
Proof.
  pre_process;
    try (
      unfold PolarCmpResult; entailer!;
      first
        [ do 3 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 5 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 4 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        ]).
Qed.

Lemma proof_of_cmp_polar_values_return_wit_37 : cmp_polar_values_return_wit_37.
Proof.
  pre_process;
    try (
      unfold PolarCmpResult; entailer!;
      first
        [ do 3 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 5 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 4 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        ]).
Qed.

Lemma proof_of_cmp_polar_values_return_wit_38 : cmp_polar_values_return_wit_38.
Proof.
  pre_process;
    try (
      unfold PolarCmpResult; entailer!;
      first
        [ do 3 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 5 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        | do 4 right; left; repeat split;
          unfold polar_upper_half, polar_cross, point_dist2; simpl; lia
        ]).
Qed.

Lemma proof_of_cmp_polar_values_return_wit_39 : cmp_polar_values_return_wit_39.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - repeat split_pures.
    + dump_pre_spatial.
      unfold PolarCmpResult.
      cbn.
      do 2 right; left.
      repeat split; try lia.
      * rewrite (polar_upper_half_true_of_pos_y gx_pre gy_pre a_x_pre a_y_pre) by lia.
        rewrite (polar_upper_half_true_of_pos_y gx_pre gy_pre b_x_pre b_y_pre) by lia.
        reflexivity.
      * unfold polar_cross. cbn. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
Qed.

Lemma proof_of_cmp_polar_values_return_wit_40 : cmp_polar_values_return_wit_40.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - repeat split_pures.
    + dump_pre_spatial.
      unfold PolarCmpResult.
      cbn.
      do 2 right; left.
      repeat split; try lia.
      * rewrite (polar_upper_half_true_of_zero_y_nonneg_x gx_pre gy_pre a_x_pre a_y_pre) by lia.
        rewrite (polar_upper_half_true_of_pos_y gx_pre gy_pre b_x_pre b_y_pre) by lia.
        reflexivity.
      * unfold polar_cross. cbn. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
Qed.

Lemma proof_of_cmp_polar_values_return_wit_41 : cmp_polar_values_return_wit_41.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - repeat split_pures.
    + dump_pre_spatial.
      unfold PolarCmpResult.
      cbn.
      do 2 right; left.
      repeat split; try lia.
      * rewrite (polar_upper_half_false_of_zero_y_neg_x gx_pre gy_pre a_x_pre a_y_pre) by lia.
        rewrite (polar_upper_half_false_of_nonpos_nonzero_y gx_pre gy_pre b_x_pre b_y_pre) by lia.
        reflexivity.
      * unfold polar_cross. cbn. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
Qed.

Lemma proof_of_cmp_polar_values_return_wit_42 : cmp_polar_values_return_wit_42.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - repeat split_pures.
    + dump_pre_spatial.
      unfold PolarCmpResult.
      cbn.
      do 2 right; left.
      repeat split; try lia.
      * rewrite (polar_upper_half_false_of_nonpos_nonzero_y gx_pre gy_pre a_x_pre a_y_pre) by lia.
        rewrite (polar_upper_half_false_of_nonpos_nonzero_y gx_pre gy_pre b_x_pre b_y_pre) by lia.
        reflexivity.
      * unfold polar_cross. cbn. lia.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
Qed.

Lemma proof_of_cmp_polar_values_return_wit_43 : cmp_polar_values_return_wit_43.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - repeat split_pures.
    + dump_pre_spatial.
      unfold PolarCmpResult.
      cbn.
      right; left.
      repeat split; try lia.
      * rewrite (polar_upper_half_false_of_zero_y_neg_x gx_pre gy_pre a_x_pre a_y_pre) by lia.
        reflexivity.
      * rewrite (polar_upper_half_true_of_pos_y gx_pre gy_pre b_x_pre b_y_pre) by lia.
        reflexivity.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
Qed.

Lemma proof_of_cmp_polar_values_return_wit_44 : cmp_polar_values_return_wit_44.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - repeat split_pures.
    + dump_pre_spatial.
      unfold PolarCmpResult.
      cbn.
      right; left.
      repeat split; try lia.
      * rewrite (polar_upper_half_false_of_nonpos_nonzero_y gx_pre gy_pre a_x_pre a_y_pre) by lia.
        reflexivity.
      * rewrite (polar_upper_half_true_of_pos_y gx_pre gy_pre b_x_pre b_y_pre) by lia.
        reflexivity.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
Qed.

Lemma proof_of_cmp_polar_values_return_wit_45 : cmp_polar_values_return_wit_45.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - repeat split_pures.
    + dump_pre_spatial.
      unfold PolarCmpResult.
      cbn.
      right; left.
      repeat split; try lia.
      * rewrite (polar_upper_half_false_of_zero_y_neg_x gx_pre gy_pre a_x_pre a_y_pre) by lia.
        reflexivity.
      * rewrite (polar_upper_half_true_of_zero_y_nonneg_x gx_pre gy_pre b_x_pre b_y_pre) by lia.
        reflexivity.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
Qed. 

Lemma proof_of_cmp_polar_values_return_wit_46 : cmp_polar_values_return_wit_46.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - repeat split_pures.
    + dump_pre_spatial.
      unfold PolarCmpResult.
      cbn.
      right; left.
      repeat split; try lia.
      * rewrite (polar_upper_half_false_of_nonpos_nonzero_y gx_pre gy_pre a_x_pre a_y_pre) by lia.
        reflexivity.
      * rewrite (polar_upper_half_true_of_zero_y_nonneg_x gx_pre gy_pre b_x_pre b_y_pre) by lia.
        reflexivity.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
Qed. 

Lemma proof_of_cmp_polar_values_return_wit_47 : cmp_polar_values_return_wit_47.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - repeat split_pures.
    + dump_pre_spatial.
      unfold PolarCmpResult.
      cbn.
      left.
      repeat split; try lia.
      * rewrite (polar_upper_half_true_of_pos_y gx_pre gy_pre a_x_pre a_y_pre) by lia.
        reflexivity.
      * rewrite (polar_upper_half_false_of_zero_y_neg_x gx_pre gy_pre b_x_pre b_y_pre) by lia.
        reflexivity.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
Qed. 

Lemma proof_of_cmp_polar_values_return_wit_48 : cmp_polar_values_return_wit_48.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - repeat split_pures.
    + dump_pre_spatial.
      unfold PolarCmpResult.
      cbn.
      left.
      repeat split; try lia.
      * rewrite (polar_upper_half_true_of_zero_y_nonneg_x gx_pre gy_pre a_x_pre a_y_pre) by lia.
        reflexivity.
      * rewrite (polar_upper_half_false_of_zero_y_neg_x gx_pre gy_pre b_x_pre b_y_pre) by lia.
        reflexivity.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
Qed. 

Lemma proof_of_cmp_polar_values_return_wit_49 : cmp_polar_values_return_wit_49.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - repeat split_pures.
    + dump_pre_spatial.
      unfold PolarCmpResult.
      cbn.
      left.
      repeat split; try lia.
      * rewrite (polar_upper_half_true_of_pos_y gx_pre gy_pre a_x_pre a_y_pre) by lia.
        reflexivity.
      * rewrite (polar_upper_half_false_of_nonpos_nonzero_y gx_pre gy_pre b_x_pre b_y_pre) by lia.
        reflexivity.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
Qed. 

Lemma proof_of_cmp_polar_values_return_wit_50 : cmp_polar_values_return_wit_50.
Proof.
  pre_process.
  split_pure_spatial.
  - cancel.
  - repeat split_pures.
    + dump_pre_spatial.
      unfold PolarCmpResult.
      cbn.
      left.
      repeat split; try lia.
      * rewrite (polar_upper_half_true_of_zero_y_nonneg_x gx_pre gy_pre a_x_pre a_y_pre) by lia.
        reflexivity.
      * rewrite (polar_upper_half_false_of_nonpos_nonzero_y gx_pre gy_pre b_x_pre b_y_pre) by lia.
        reflexivity.
    + dump_pre_spatial. lia.
    + dump_pre_spatial. lia.
Qed. 

Lemma proof_of_swap_points_return_wit_1 : swap_points_return_wit_1.
Proof.
  pre_process.
  pose proof PreH8 as Hflat.
  destruct PreH8 as [Hflat_len _].
  replace
    (replace_Znth (2 * j_pre + 1) (Znth (2 * i_pre + 1) flat 0)
      (replace_Znth (2 * j_pre) (Znth (2 * i_pre) flat 0)
        (replace_Znth (2 * i_pre + 1)
          (Znth (2 * j_pre + 1)
            (replace_Znth (2 * i_pre) (Znth (2 * j_pre) flat 0) flat) 0)
          (replace_Znth (2 * i_pre) (Znth (2 * j_pre) flat 0) flat))))
    with (point_swap_flat flat i_pre j_pre).
  2:{
    symmetry.
    apply point_swap_flat_preprocess_form with (n := n_pre); try lia.
  }
  entailer!.
  - eapply PointCoordsBound_permutation.
    + apply PointPermutation_swap_points_any; lia.
    + exact PreH9.
  - apply PointPermutation_swap_points_any; lia.
  - apply FlatPoints_swap_points.
    + exact Hflat.
    + lia.
    + lia.
Qed.

Lemma proof_of_partition_points_entail_wit_1 : partition_points_entail_wit_1.
Proof.
  pre_process.
  assert (Hhigh : 0 <= high_pre < Zlength pts_l).
  { rewrite PreH6. lia. }
  assert (Hpts_bound : PointCoordsBound pts_l).
  { unfold PointCoordsBound in PreH8 |- *.
    inversion PreH8; subst.
    assumption.
  }
  pose proof (flat_points_lookup_point flat pts_l high_pre Hhigh PreH7) as Hpivot.
  Exists flat. Exists pts_l.
  split_pure_spatial.
  - cancel.
  - entailer!.
    + unfold PointPartitionScanInv, PointSameOutsideRange.
      repeat split.
      * apply Permutation_refl.
      * symmetry. exact Hpivot.
      * intros k Hk. exfalso. lia.
      * intros k Hk. exfalso. lia.
Qed.

Lemma proof_of_partition_points_entail_wit_2_1 : partition_points_entail_wit_2_1.
Proof.
  pre_process.
  assert (Hjrange : 0 <= j < Zlength pts_cur_2) by (rewrite PreH18; lia).
  assert (Hi1 : 0 <= i + 1 < Zlength pts_cur_2) by (rewrite PreH18; lia).
  assert (Hhighrange : 0 <= high_pre < Zlength pts_cur_2) by (rewrite PreH18; lia).
  assert (
    Hjpt :
      Znth j pts_cur_2 default_point =
      mk_point (Znth (2 * j) flat_cur_2 0) (Znth (2 * j + 1) flat_cur_2 0)
  ) by (apply FlatPoints_Znth_point; auto).
  assert (
    Hjle_cur :
      PolarLe
        (mk_point gx_pre gy_pre)
        (Znth j pts_cur_2 default_point)
        (mk_point pivot_x pivot_y)
  ).
  {
    pose proof (PolarCmpResult_nonpos_le _ _ _ _ PreH5 PreH4) as Hle.
    rewrite <- Hjpt in Hle.
    exact Hle.
  }
  assert (Hgxy : CoordInBounds gx_pre /\ CoordInBounds gy_pre).
  {
    inversion PreH22; subst; auto.
  }
  destruct PreH23 as [Hperm [Hsame [Hpivot [Hleft Hmid]]]].
  destruct Hsame as [Hsame_len Hsame].
  Exists (point_swap_flat flat_cur_2 (i + 1) j).
  Exists (point_swap_points pts_cur_2 (i + 1) j).
  split_pure_spatial.
  - cancel.
  - split.
    + repeat split.
      * exact PreH9.
      * exact PreH10.
      * exact PreH11.
      * exact PreH12.
      * exact PreH13.
      * assert (low_pre - 1 <= i + 1) by lia; assumption.
      * assert (i + 1 < j + 1) by lia; assumption.
      * assert (j + 1 <= high_pre) by lia; assumption.
      * exact PreH17.
      * rewrite Zlength_point_swap_points.
        exact PreH18.
      * replace (Znth high_pre (point_swap_points pts_cur_2 (i + 1) j) default_point)
          with (Znth high_pre pts_cur_2 default_point).
        -- exact PreH19.
        -- symmetry.
           apply Znth_point_swap_points_other.
           ++ exact Hi1.
           ++ exact Hjrange.
           ++ exact Hhighrange.
           ++ lia.
           ++ lia.
      * pose proof PreH1 as Hflat_swap.
        destruct Hflat_swap as [Hflat_len _].
        exact Hflat_len.
      * pose proof PreH1 as Hflat_swap.
        destruct Hflat_swap as [_ Hflat_rec].
        exact Hflat_rec.
      * exact PreH3.
      * constructor.
        -- exact Hgxy.
        -- exact PreH3.
    + unfold PointPartitionScanInv.
      repeat split.
      * eapply Permutation_trans.
        -- exact Hperm.
        -- exact PreH2.
      * rewrite Zlength_point_swap_points.
        lia.
      * intros k Hk Hout.
        replace (Znth k (point_swap_points pts_cur_2 (i + 1) j) default_point)
          with (Znth k pts_cur_2 default_point).
        -- apply Hsame; auto.
        -- symmetry.
           apply Znth_point_swap_points_other.
           ++ exact Hi1.
           ++ exact Hjrange.
           ++ rewrite Hsame_len in Hk.
              exact Hk.
           ++ destruct Hout as [Hlt | Hgt]; lia.
           ++ destruct Hout as [Hlt | Hgt]; lia.
      * replace (Znth high_pre (point_swap_points pts_cur_2 (i + 1) j) default_point)
          with (Znth high_pre pts_cur_2 default_point).
        -- exact Hpivot.
        -- symmetry.
           apply Znth_point_swap_points_other.
           ++ exact Hi1.
           ++ exact Hjrange.
           ++ exact Hhighrange.
           ++ lia.
           ++ lia.
      * intros k Hk.
        destruct (Z.eq_dec k (i + 1)) as [-> | Hneq].
        -- rewrite Znth_point_swap_points_left.
           ++ exact Hjle_cur.
           ++ exact Hi1.
           ++ exact Hjrange.
        -- replace (Znth k (point_swap_points pts_cur_2 (i + 1) j) default_point)
             with (Znth k pts_cur_2 default_point).
           ++ apply Hleft.
              lia.
           ++ symmetry.
              apply Znth_point_swap_points_other.
              ** exact Hi1.
              ** exact Hjrange.
               ** rewrite PreH18.
                 lia.
              ** exact Hneq.
              ** lia.
      * intros k Hk.
        destruct (Z.eq_dec k j) as [-> | Hneq].
        -- rewrite Znth_point_swap_points_right.
           ++ apply Hmid.
              lia.
           ++ exact Hi1.
           ++ exact Hjrange.
        -- replace (Znth k (point_swap_points pts_cur_2 (i + 1) j) default_point)
             with (Znth k pts_cur_2 default_point).
           ++ apply Hmid.
              lia.
           ++ symmetry.
              apply Znth_point_swap_points_other.
              ** exact Hi1.
              ** exact Hjrange.
               ** rewrite PreH18.
                 lia.
              ** lia.
              ** exact Hneq.
Qed. 

Lemma proof_of_partition_points_entail_wit_2_2 : partition_points_entail_wit_2_2.
Proof.
  pre_process.
  assert (Hret1 : retval = 1) by lia.
  assert (Hjrange : 0 <= j < Zlength pts_cur_2) by (rewrite PreH15; lia).
  assert (
    Hjpt :
      Znth j pts_cur_2 default_point =
      mk_point (Znth (2 * j) flat_cur_2 0) (Znth (2 * j + 1) flat_cur_2 0)
  ) by (apply FlatPoints_Znth_point; auto).
  assert (
    Hjgt :
      PolarLt
        (mk_point gx_pre gy_pre)
        (mk_point pivot_x pivot_y)
        (Znth j pts_cur_2 default_point)
  ).
  {
    rewrite Hret1 in PreH2.
    pose proof (PolarCmpResult_one_implies_PolarLt_flip _ _ _ PreH2) as Hlt.
    rewrite <- Hjpt in Hlt.
    exact Hlt.
  }
  destruct PreH20 as [Hperm [Hsame [Hpivot [Hleft Hmid]]]].
  destruct Hsame as [Hsame_len Hsame_out].
  Exists flat_cur_2.
  Exists pts_cur_2.
  split_pure_spatial.
  - cancel.
  - split.
    + repeat split.
      * exact PreH6.
      * exact PreH7.
      * exact PreH8.
      * exact PreH9.
      * exact PreH10.
      * exact PreH11.
      * assert (i < j + 1) by lia; assumption.
      * assert (j + 1 <= high_pre) by lia; assumption.
      * exact PreH14.
      * exact PreH15.
      * exact PreH16.
      * pose proof PreH17 as Hflat_cur.
        destruct Hflat_cur as [Hflat_len _].
        exact Hflat_len.
      * pose proof PreH17 as Hflat_cur.
        destruct Hflat_cur as [_ Hflat_rec].
        exact Hflat_rec.
      * exact PreH18.
      * exact PreH19.
    + unfold PointPartitionScanInv.
      repeat split.
      * exact Hperm.
      * exact Hsame_len.
      * exact Hsame_out.
      * exact Hpivot.
      * exact Hleft.
      * intros k Hk.
        destruct (Z.eq_dec k j) as [-> | Hneq].
        -- exact Hjgt.
        -- apply Hmid.
           lia.
Qed. 

Lemma proof_of_partition_points_return_wit_1 : partition_points_return_wit_1.
Proof.
  pre_process.
  assert (Hj : j = high_pre) by lia.
  subst j.
  assert (Hgpbound : CoordInBounds gx_pre /\ CoordInBounds gy_pre).
  {
    match goal with
    | Hbound : PointCoordsBound (cons (mk_point gx_pre gy_pre) pts_cur) |- _ =>
        inversion Hbound; subst; assumption
    end.
  }
  Exists (point_swap_flat flat_cur (i + 1) high_pre).
  Exists (point_swap_points pts_cur (i + 1) high_pre).
  split_pure_spatial.
  - cancel.
  - entailer!.
    + eapply PointPartitionedAt_after_final_swap; eauto; lia.
    + pose proof PreH19 as Hscan.
      destruct Hscan as [_ [Hsame _]].
      eapply PointSameOutsideRange_trans.
      * exact Hsame.
      * apply PointSameOutsideRange_swap_inside; lia.
    + pose proof PreH19 as Hscan.
      destruct Hscan as [Hperm_scan _].
      eapply Permutation_trans.
      * exact Hperm_scan.
      * exact PreH2.
    + constructor; [exact Hgpbound | exact PreH3].
Qed. 

Lemma proof_of_partition_points_partial_solve_wit_5_pure : partition_points_partial_solve_wit_5_pure.
Proof.
  pre_process.
  assert (Hjrange : 0 <= j < Zlength pts_cur).
  { rewrite PreH11. lia. }
  assert (Hhigh : 0 <= high_pre < Zlength pts_cur).
  { rewrite PreH11. lia. }
  assert (Hgxy : CoordInBounds gx_pre /\ CoordInBounds gy_pre).
  { unfold PointCoordsBound in PreH15.
    inversion PreH15; subst.
    tauto.
  }
  pose proof (point_coords_bound_lookup pts_cur j Hjrange PreH14) as Hjcoords.
  pose proof (point_coords_bound_lookup pts_cur high_pre Hhigh PreH14) as Hpivotcoords.
  pose proof (flat_points_lookup_point flat_cur pts_cur j Hjrange PreH13) as Hlookupj.
  entailer!.
  - change (Znth (2 * j) flat_cur 0) with
      (point_x (mk_point (Znth (2 * j) flat_cur 0) (Znth (2 * j + 1) flat_cur 0))).
    rewrite Hlookupj.
    exact (proj1 Hjcoords).
  - change (Znth (2 * j + 1) flat_cur 0) with
      (point_y (mk_point (Znth (2 * j) flat_cur 0) (Znth (2 * j + 1) flat_cur 0))).
    rewrite Hlookupj.
    exact (proj2 Hjcoords).
  - change pivot_x with (point_x (mk_point pivot_x pivot_y)).
    rewrite PreH12.
    exact (proj1 Hpivotcoords).
  - change pivot_y with (point_y (mk_point pivot_x pivot_y)).
    rewrite PreH12.
    exact (proj2 Hpivotcoords).
Qed.

Lemma proof_of_quicksort_points_range_entail_wit_1 : quicksort_points_range_entail_wit_1.
Proof.
  intros.
  pre_process.
  unfold PointMemoryModel in PreH7.
  destruct PreH7 as [pts_l [? [? ?]]].
  Exists pts_l.
  entailer!.
  unfold PointMemoryModel.
  eauto 10.
Qed. 

Lemma proof_of_quicksort_points_range_return_wit_4 : quicksort_points_range_return_wit_4.
Proof.
  pre_process.
  assert (Hge : left_pre >= right_pre) by lia.
  destruct PreH7 as [pts_l [Hlen [Hflat_mem Hbound_mem]]].
  Exists flat. Exists pts_l.
  split_pure_spatial.
  - cancel.
  - split; [split; auto|].
    unfold PointRangeSortResult.
    intros pts_in Hflat_in _.
    assert (pts_in = pts_l) by (eapply FlatPoints_functional; eauto).
    subst pts_in.
    split.
    + apply Permutation_refl.
    + split.
      * apply PointSameOutsideRange_refl.
      * apply PointSortedRange_degenerate. exact Hge.
Qed. 

Lemma proof_of_quicksort_points_range_return_wit_3 : quicksort_points_range_return_wit_3.
Proof.
  pre_process.
  prop_apply (IntArray.full_length coords_pre (2 * n_pre) flat_out_3).
  Intros.
  assert (Hretval : retval = right_pre) by lia.
  subst retval.
  Exists flat_out_3.
  Exists pts_out_3.
  split_pure_spatial.
  - cancel.
  - entailer!.
    match goal with
    | Hflat3 : FlatPoints flat_out_3 pts_out_3 |- _ =>
        destruct Hflat3 as [Hlenflat3 _]
    end.
    assert (Hlen3 : Zlength pts_out_3 = n_pre).
    {
      match goal with
      | Hlen_full : Z.of_nat (Datatypes.length flat_out_3) = 2 * n_pre |- _ =>
          rewrite <- Zlength_correct in Hlen_full;
          rewrite Hlenflat3 in Hlen_full;
          lia
      end.
    }
    assert (Hlen2 : Zlength pts_out_2 = n_pre).
    {
      rewrite <- PreH19.
      repeat rewrite Zlength_correct.
      rewrite (Permutation_length PreH10).
      reflexivity.
    }
    unfold PointRangeSortResult.
    intros pts_in Hflat_in Hbound_in.
    assert (pts_in = pts_l) by (eapply FlatPoints_functional; eauto).
    subst pts_in.
    specialize (PreH4 pts_out_2 PreH8 PreH9).
    destruct PreH4 as [Hperm23 [Hsame23 Hsorted23]].
    split.
    + eapply Permutation_trans; [exact PreH10 | exact Hperm23].
    + split.
      * assert (Hsame23_full : PointSameOutsideRange pts_out_2 pts_out_3 left_pre right_pre).
        {
          eapply (PointSameOutsideRange_weaken
                    pts_out_2 pts_out_3 left_pre (right_pre - 1) left_pre right_pre).
          - lia.
          - lia.
          - exact Hsame23.
        }
        eapply PointSameOutsideRange_trans; [exact PreH11 | exact Hsame23_full].
      * assert (Hpart3 : PointPartitionedAt (mk_point gx_pre gy_pre) pts_out_3 left_pre right_pre right_pre).
        {
          eapply PointPartitionedAt_preserved_by_left.
          - exact Hperm23.
          - lia.
          - exact Hsame23.
          - rewrite Hlen2. lia.
          - exact PreH12.
        }
        eapply PointSortedRange_from_left_boundary with (p := right_pre).
        -- lia.
        -- lia.
        -- rewrite Hlen3. lia.
        -- exact Hpart3.
        -- exact Hsorted23.
Qed. 

Lemma proof_of_quicksort_points_range_return_wit_1 : quicksort_points_range_return_wit_1.
Proof.
  pre_process.
  prop_apply (IntArray.full_length coords_pre (2 * n_pre) flat_out_4).
  Intros.
  Exists flat_out_4.
  Exists pts_out_4.
  split_pure_spatial.
  - cancel.
  - entailer!.
    match goal with
    | Hflat4 : FlatPoints flat_out_4 pts_out_4 |- _ =>
        destruct Hflat4 as [Hlenflat4 _]
    end.
    assert (Hlen2 : Zlength pts_out_2 = n_pre).
    {
      rewrite <- PreH22.
      repeat rewrite Zlength_correct.
      rewrite <- (Permutation_length PreH13).
      reflexivity.
    }
    assert (Hlen4 : Zlength pts_out_4 = n_pre).
    {
      match goal with
      | Hlen_full : Z.of_nat (Datatypes.length flat_out_4) = 2 * n_pre |- _ =>
          rewrite <- Zlength_correct in Hlen_full;
          rewrite Hlenflat4 in Hlen_full;
          lia
      end.
    }
    unfold PointRangeSortResult.
    intros pts_in Hflat_in Hbound_in.
    assert (pts_in = pts_l) by (eapply FlatPoints_functional; eauto).
    subst pts_in.
    specialize (PreH7 pts_out_2 PreH11 PreH12).
    destruct PreH7 as [Hperm23 [Hsame23 Hsorted23]].
    specialize (PreH3 pts_out_3 PreH5 PreH6).
    destruct PreH3 as [Hperm34 [Hsame34 Hsorted34]].
    assert (Hlen3 : Zlength pts_out_3 = n_pre).
    {
      rewrite <- Hlen2.
      repeat rewrite Zlength_correct.
      rewrite <- (Permutation_length Hperm23).
      reflexivity.
    }
    split.
    + eapply Permutation_trans.
      * exact PreH13.
      * eapply Permutation_trans; [exact Hperm23 | exact Hperm34].
    + split.
      * assert (Hsame23_full : PointSameOutsideRange pts_out_2 pts_out_3 left_pre right_pre).
        {
          eapply (PointSameOutsideRange_weaken
                    pts_out_2 pts_out_3 left_pre (retval - 1) left_pre right_pre).
          - lia.
          - lia.
          - exact Hsame23.
        }
        assert (Hsame34_full : PointSameOutsideRange pts_out_3 pts_out_4 left_pre right_pre).
        {
          eapply (PointSameOutsideRange_weaken
                    pts_out_3 pts_out_4 (retval + 1) right_pre left_pre right_pre).
          - lia.
          - lia.
          - exact Hsame34.
        }
        eapply PointSameOutsideRange_trans.
        -- eapply PointSameOutsideRange_trans; [exact PreH14 | exact Hsame23_full].
        -- exact Hsame34_full.
      * assert (Hpart3 : PointPartitionedAt (mk_point gx_pre gy_pre) pts_out_3 left_pre right_pre retval).
        {
          eapply PointPartitionedAt_preserved_by_left.
          - exact Hperm23.
          - lia.
          - exact Hsame23.
          - rewrite Hlen2. lia.
          - exact PreH15.
        }
        assert (Hpart4 : PointPartitionedAt (mk_point gx_pre gy_pre) pts_out_4 left_pre right_pre retval).
        {
          eapply PointPartitionedAt_preserved_by_right.
          - exact Hperm34.
          - lia.
          - exact Hsame34.
          - rewrite Hlen3. lia.
          - exact Hpart3.
        }
        assert (Hsorted_left4 :
          PointSortedRange (mk_point gx_pre gy_pre) pts_out_4 left_pre (retval - 1)).
        {
          eapply PointSortedRange_ext with (l := pts_out_3).
          - lia.
          - rewrite Hlen3. lia.
          - rewrite Hlen3, Hlen4. reflexivity.
          - intros k Hk.
            destruct Hsame34 as [_ Heq34].
            apply Heq34.
            + rewrite Hlen3. lia.
            + left. lia.
          - exact Hsorted23.
        }
        eapply PointSortedRange_from_middle_partition with (p := retval).
        -- lia.
        -- lia.
        -- lia.
        -- rewrite Hlen4. lia.
        -- exact Hpart4.
        -- exact Hsorted_left4.
        -- exact Hsorted34.
Qed. 

Lemma proof_of_quicksort_points_range_return_wit_2 : quicksort_points_range_return_wit_2.
Proof.
  pre_process.
  prop_apply (IntArray.full_length coords_pre (2 * n_pre) flat_out_3).
  Intros.
  assert (Hretval : retval = left_pre) by lia.
  subst retval.
  Exists flat_out_3.
  Exists pts_out_3.
  split_pure_spatial.
  - cancel.
  - entailer!.
    match goal with
    | Hflat3 : FlatPoints flat_out_3 pts_out_3 |- _ =>
        destruct Hflat3 as [Hlenflat3 _]
    end.
    assert (Hlen3 : Zlength pts_out_3 = n_pre).
    {
      match goal with
      | Hflat_len : Z.of_nat (Datatypes.length flat_out_3) = 2 * n_pre |- _ =>
          rewrite <- Zlength_correct in Hflat_len;
          rewrite Hlenflat3 in Hflat_len; lia
      end.
    }
    assert (Hlen2 : Zlength pts_out_2 = n_pre).
    {
      assert (Hperm_len := Permutation_length PreH10).
      assert (Hperm_zlen : Zlength pts_l = Zlength pts_out_2).
      { repeat rewrite Zlength_correct. rewrite Hperm_len. reflexivity. }
      lia.
    }
    unfold PointRangeSortResult.
    intros pts_in Hflat_in _.
    assert (pts_in = pts_l) by (eapply FlatPoints_functional; eauto).
    subst pts_in.
    specialize (PreH3 pts_out_2 PreH8 PreH9).
    destruct PreH3 as [Hperm23 [Hsame23 Hsorted23]].
    split.
    + eapply Permutation_trans; [exact PreH10 | exact Hperm23].
    + split.
      * assert (Hsame23_full : PointSameOutsideRange pts_out_2 pts_out_3 left_pre right_pre).
        {
          eapply (PointSameOutsideRange_weaken
                    pts_out_2 pts_out_3 (left_pre + 1) right_pre left_pre right_pre).
          - lia.
          - lia.
          - exact Hsame23.
        }
        eapply PointSameOutsideRange_trans; [exact PreH11 | exact Hsame23_full].
      * assert (Hpart3 : PointPartitionedAt (mk_point gx_pre gy_pre) pts_out_3 left_pre right_pre left_pre).
        {
          eapply PointPartitionedAt_preserved_by_right.
          - exact Hperm23.
          - lia.
          - exact Hsame23.
          - rewrite Hlen2. lia.
          - exact PreH12.
        }
        eapply PointSortedRange_from_right_boundary with (p := left_pre).
        -- lia.
        -- lia.
        -- rewrite Hlen3. lia.
        -- exact Hpart3.
        -- exact Hsorted23.
Qed. 

Lemma proof_of_quicksort_points_range_partial_solve_wit_2_pure : quicksort_points_range_partial_solve_wit_2_pure.
Proof.
  intros.
  pre_process.
  entailer!.
  unfold PointMemoryModel.
  exists pts_out.
  repeat split; auto.
  - rewrite <- PreH15.
    repeat rewrite Zlength_correct.
    rewrite (Permutation_length PreH6).
    reflexivity.
  - unfold FlatPoints in PreH4.
    tauto.
  - unfold FlatPoints in PreH4.
    tauto.
Qed. 

Lemma proof_of_quicksort_points_range_partial_solve_wit_3_pure : quicksort_points_range_partial_solve_wit_3_pure.
Proof.
  intros.
  pre_process.
  entailer!.
  unfold PointMemoryModel.
  exists pts_out_2.
  repeat split; auto.
  - specialize (PreH4 pts_out PreH8 PreH9) as [Hperm_out _].
    assert (Hperm : PointPermutation pts_l pts_out_2).
    { eapply Permutation_trans; [exact PreH10 | exact Hperm_out]. }
    rewrite <- PreH19.
    repeat rewrite Zlength_correct.
    rewrite (Permutation_length Hperm).
    reflexivity.
  - unfold FlatPoints in PreH2; tauto.
  - unfold FlatPoints in PreH2; tauto.
Qed. 

Lemma proof_of_quicksort_points_range_partial_solve_wit_4_pure : quicksort_points_range_partial_solve_wit_4_pure.
Proof.
  intros.
  pre_process.
  entailer!.
  unfold PointMemoryModel.
  exists pts_out.
  repeat split; auto.
  - rewrite <- PreH16.
    repeat rewrite Zlength_correct.
    rewrite (Permutation_length PreH7).
    reflexivity.
  - unfold FlatPoints in PreH5; tauto.
  - unfold FlatPoints in PreH5; tauto.
Qed. 

Lemma proof_of_sort_return_wit_1 : sort_return_wit_1.
Proof.
  pre_process.
  Exists flat_out_2. Exists pts_out_2.
  split_pure_spatial.
  - cancel.
  - entailer!.
    + destruct (PreH3 pts_l PreH7 PreH8) as [Hperm [_ Hsorted]].
      unfold PolarSorted.
      intros i j Hi Hij Hj.
      assert (HZlen : Zlength pts_out_2 = n_pre).
      {
        rewrite <- PreH6.
        rewrite !Zlength_correct.
        rewrite <- (Permutation_length Hperm).
        reflexivity.
      }
      eapply Hsorted; lia.
    + destruct (PreH3 pts_l PreH7 PreH8) as [Hperm _].
      exact Hperm.
Qed. 

Lemma proof_of_sort_partial_solve_wit_1_pure : sort_partial_solve_wit_1_pure.
Proof.
  pre_process.
  entailer!.
  unfold PointMemoryModel.
  exists pts_l.
  auto.
Qed. 
