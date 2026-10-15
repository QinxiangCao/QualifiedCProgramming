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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P047_1582D_vupsen_pupsen_and_0_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P047_1582D_vupsen_pupsen_and_0_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P047_1582D_vupsen_pupsen_and_0_lib.
Local Open Scope sac.

Lemma proof_of_llabs_return_wit_1_split_goal_1 : llabs_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_llabs_return_wit_1 : llabs_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_llabs_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_llabs_return_wit_2_split_goal_1 : llabs_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_llabs_return_wit_2 : llabs_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_llabs_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_gcdll_entail_wit_2_split_goal_1 : gcdll_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold GcdValue in *.
  pose proof (Z.gcd_rem a b PreH6) as Hg.
  transitivity (Z.gcd (Z.rem a b) b).
  - exact (Z.gcd_comm b (Z.rem a b)).
  - transitivity (Z.gcd b a).
    + exact Hg.
    + transitivity (Z.gcd a b).
      * exact (Z.gcd_comm b a).
      * exact PreH5.
Qed.

Lemma proof_of_gcdll_entail_wit_2_split_goal_2 : gcdll_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (Z.rem_bound_pos a b ltac:(lia) ltac:(lia)) as Hrem.
  lia.
Qed.

Lemma proof_of_gcdll_entail_wit_2_split_goal_3 : gcdll_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (Z.rem_bound_pos a b ltac:(lia) ltac:(lia)) as Hrem.
  lia.
Qed.

Lemma proof_of_gcdll_entail_wit_2 : gcdll_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_gcdll_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_gcdll_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_gcdll_entail_wit_2_split_goal_3.
Qed.

Lemma proof_of_gcdll_return_wit_1_split_goal_1 : gcdll_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst b.
  unfold GcdValue in *.
  rewrite Z.gcd_0_r in PreH6.
  rewrite Z.abs_eq in PreH6 by lia.
  exact PreH6.
Qed.

Lemma proof_of_gcdll_return_wit_1 : gcdll_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_gcdll_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_pair_fill_safety_wit_2_split_goal_1 : pair_fill_safety_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_pair_fill_safety_wit_2_split_goal_2 : pair_fill_safety_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold GcdValue in PreH1.
  dump_pre_spatial.
  rewrite PreH1, PreH2, PreH3.
  pose proof (gcd_abs_positive__pair_fill a_pre b_pre PreH6 PreH9).
  lia.
Qed.

Lemma proof_of_pair_fill_safety_wit_2 : pair_fill_safety_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pair_fill_safety_wit_2_split_goal_1.
  - Goal_apply proof_of_pair_fill_safety_wit_2_split_goal_2.
Qed.

Lemma proof_of_pair_fill_safety_wit_4_split_goal_1 : pair_fill_safety_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_pair_fill_safety_wit_4_split_goal_2 : pair_fill_safety_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold GcdValue in PreH1.
  dump_pre_spatial.
  rewrite PreH1, PreH2, PreH3.
  pose proof (gcd_abs_positive__pair_fill a_pre b_pre PreH6 PreH9).
  lia.
Qed.

Lemma proof_of_pair_fill_safety_wit_4 : pair_fill_safety_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pair_fill_safety_wit_4_split_goal_1.
  - Goal_apply proof_of_pair_fill_safety_wit_4_split_goal_2.
Qed.

Lemma proof_of_pair_fill_return_wit_1 : pair_fill_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists (cons (b_pre ÷ retval_3)
    (cons ((-a_pre) ÷ retval_3) (@nil Z))).
  split_pure_spatial.
  - rewrite Int64Array.full_unfold.
    rewrite Int64Array.seg_unfold.
    rewrite Int64Array.seg_empty.
    cancel.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial. lia.
  - dump_pre_spatial.
    unfold GcdValue in PreH5.
    subst retval_3.
    subst retval_2.
    subst retval.
    apply pair_output_prefix__pair_fill; lia.
Qed.

Lemma proof_of_pair_fill_partial_solve_wit_3_pure_split_goal_1 : pair_fill_partial_solve_wit_3_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_pair_fill_partial_solve_wit_3_pure_split_goal_2 : pair_fill_partial_solve_wit_3_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_pair_fill_partial_solve_wit_3_pure_split_goal_3 : pair_fill_partial_solve_wit_3_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_pair_fill_partial_solve_wit_3_pure_split_goal_4 : pair_fill_partial_solve_wit_3_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_pair_fill_partial_solve_wit_3_pure : pair_fill_partial_solve_wit_3_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_pair_fill_partial_solve_wit_3_pure_split_goal_1.
  - Goal_apply proof_of_pair_fill_partial_solve_wit_3_pure_split_goal_2.
  - Goal_apply proof_of_pair_fill_partial_solve_wit_3_pure_split_goal_3.
  - Goal_apply proof_of_pair_fill_partial_solve_wit_3_pure_split_goal_4.
Qed.

Lemma proof_of_solver_safety_wit_19_split_goal_1 : solver_safety_wit_19_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH6 0 ltac:(lia)) as Hx.
  specialize (PreH6 2 ltac:(lia)) as Hz.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_19 : solver_safety_wit_19.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_safety_wit_19_split_goal_1.
Qed.

Lemma proof_of_solver_safety_wit_20_split_goal_1 : solver_safety_wit_20_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH6 0 ltac:(lia)) as Hx.
  specialize (PreH6 2 ltac:(lia)) as Hz.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_20_split_goal_2 : solver_safety_wit_20_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH6 0 ltac:(lia)) as Hx.
  specialize (PreH6 2 ltac:(lia)) as Hz.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_20 : solver_safety_wit_20.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_20_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_20_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (Z.eq_dec n_pre 2) as [Heq | Hneq].
  - exfalso. apply PreH9. rewrite Heq. reflexivity.
  - lia.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_spatial : solver_entail_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold repeat_Z.
  replace (Z.to_nat (n_pre - 1)) with
    (S (S (Z.to_nat (n_pre - 3)))) by lia.
  unfold replace_Znth.
  simpl.
  rewrite (Int64Array.mixed_seg_unfold b_pre 1 n_pre
    (Some (Znth 1 values 0) :: repeat None (Z.to_nat (n_pre - 3))) None).
  rewrite (Int64Array.mixed_seg_unfold b_pre 2 n_pre
    (repeat None (Z.to_nat (n_pre - 3))) (Some (Znth 1 values 0))).
  simpl Int64Array.mixedstoreA.
  sep_apply_l_atomic (Int64Array.mixed_seg_to_undef_seg b_pre 3 n_pre
    (repeat None (Z.to_nat (n_pre - 3)))).
  sep_apply_l_atomic (Int64Array.seg_single b_pre 0 (Znth 1 values 0)).
  sep_apply_l_atomic (Int64Array.undef_seg_single b_pre 1).
  sep_apply_l_atomic (Int64Array.seg_single b_pre 2 (Znth 1 values 0)).
  simpl.
  cancel.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_3_1 : solver_entail_wit_3_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH7 0 ltac:(lia)) as Hx.
  pose proof (PreH7 1 ltac:(lia)) as Hy.
  pose proof (PreH7 2 ltac:(lia)) as Hz.
  assert (Hsub : sublist 0 3 values =
    Znth 0 values 0 :: Znth 1 values 0 :: Znth 2 values 0 :: nil).
  {
    apply (proj2 (list_eq_ext _ _ 0)).
    split.
    - rewrite Zlength_sublist by lia.
      rewrite !Zlength_cons, Zlength_nil.
      lia.
    - intros i Hi.
      rewrite Zlength_sublist in Hi by lia.
      rewrite Znth_sublist by lia.
      assert (i = 0 \/ i = 1 \/ i = 2) by lia.
      destruct H as [-> | [-> | ->]]; reflexivity.
  }
  assert (Hop : OutputPrefix (sublist 0 3 values)
    (Znth 2 values 0 :: Znth 2 values 0 ::
      -(Znth 0 values 0 + Znth 1 values 0) :: nil) 10000).
  {
    rewrite Hsub.
    apply output_prefix_three_case1__solver_initialization; lia.
  }
  Exists (Znth 2 values 0 :: Znth 2 values 0 ::
    -(Znth 0 values 0 + Znth 1 values 0) :: nil).
  split_pure_spatial.
  - replace ((1 + 1) + 1) with 3 by lia.
    cancel (IntArray.full a_pre n_pre values).
    cancel (Int64Array.undef_seg b_pre 3 n_pre).
    rewrite (Int64Array.seg_unfold b_pre 0 3
      (Znth 2 values 0 :: -(Znth 0 values 0 + Znth 1 values 0) :: nil)
      (Znth 2 values 0)).
    rewrite (Int64Array.seg_unfold b_pre 1 3
      (-(Znth 0 values 0 + Znth 1 values 0) :: nil)
      (Znth 2 values 0)).
    rewrite (Int64Array.seg_unfold b_pre 2 3 nil
      (-(Znth 0 values 0 + Znth 1 values 0))).
    rewrite (Int64Array.seg_empty b_pre 3 3).
    cancel.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial. lia.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    change (Z.rem n_pre 2 = 1).
    pose proof (Z.rem_bound_pos n_pre 2 ltac:(lia) ltac:(lia)) as Hmod.
    lia.
Qed.

Lemma proof_of_solver_entail_wit_3_2 : solver_entail_wit_3_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH6 0 ltac:(lia)) as Hx.
  pose proof (PreH6 1 ltac:(lia)) as Hy.
  pose proof (PreH6 2 ltac:(lia)) as Hz.
  assert (Hsub : sublist 0 3 values =
    Znth 0 values 0 :: Znth 1 values 0 :: Znth 2 values 0 :: nil).
  {
    apply (proj2 (list_eq_ext _ _ 0)).
    split.
    - rewrite Zlength_sublist by lia.
      rewrite !Zlength_cons, Zlength_nil.
      lia.
    - intros i Hi.
      rewrite Zlength_sublist in Hi by lia.
      rewrite Znth_sublist by lia.
      assert (i = 0 \/ i = 1 \/ i = 2) by lia.
      destruct H as [-> | [-> | ->]]; reflexivity.
  }
  assert (Hop : OutputPrefix (sublist 0 3 values)
    (y :: -(x + z) :: y :: nil) 10000).
  {
    rewrite Hsub.
    rewrite <- PreH7, <- PreH8, <- PreH9.
    apply output_prefix_three_case2__solver_initialization; lia.
  }
  Exists (y :: -(x + z) :: y :: nil).
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre values).
    cancel (Int64Array.undef_seg b_pre 3 n_pre).
    simpl.
    sep_apply_r_atomic (Int64Array.seg_merge_to_seg b_pre 0 2 3
      (y :: -(x + z) :: nil) (y :: nil)).
    + dump_pre_spatial. lia.
    + simpl.
      cancel.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    change (Z.rem n_pre 2 = 1).
    pose proof (Z.rem_bound_pos n_pre 2 ltac:(lia) ltac:(lia)) as Hmod.
    lia.
Qed.

Lemma proof_of_solver_entail_wit_3_3 : solver_entail_wit_3_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH8 0 ltac:(lia)) as Hx.
  pose proof (PreH8 1 ltac:(lia)) as Hy.
  pose proof (PreH8 2 ltac:(lia)) as Hz.
  assert (Hsub : sublist 0 3 values =
    Znth 0 values 0 :: Znth 1 values 0 :: Znth 2 values 0 :: nil).
  {
    apply (proj2 (list_eq_ext _ _ 0)).
    split.
    - rewrite Zlength_sublist by lia.
      rewrite !Zlength_cons, Zlength_nil.
      lia.
    - intros i Hi.
      rewrite Zlength_sublist in Hi by lia.
      rewrite Znth_sublist by lia.
      assert (i = 0 \/ i = 1 \/ i = 2) by lia.
      destruct H as [-> | [-> | ->]]; reflexivity.
  }
  assert (Hop : OutputPrefix (sublist 0 3 values)
    (-(Znth 1 values 0 + Znth 2 values 0) ::
      Znth 0 values 0 :: Znth 0 values 0 :: nil) 10000).
  {
    rewrite Hsub.
    apply output_prefix_three_case3__solver_initialization; lia.
  }
  Exists (-(Znth 1 values 0 + Znth 2 values 0) ::
    Znth 0 values 0 :: Znth 0 values 0 :: nil).
  split_pure_spatial.
  - cancel (IntArray.full a_pre n_pre values).
    unfold repeat_Z.
    replace (Z.to_nat n_pre) with
      (S (S (S (Z.to_nat (n_pre - 3))))) by lia.
    unfold replace_Znth.
    simpl.
    rewrite (Int64Array.mixed_full_unfold b_pre n_pre
      (Some (Znth 0 values 0) :: Some (Znth 0 values 0) ::
        repeat None (Z.to_nat (n_pre - 3)))
      (Some (-(Znth 1 values 0 + Znth 2 values 0)))).
    rewrite (Int64Array.mixed_seg_unfold b_pre 1 n_pre
      (Some (Znth 0 values 0) :: repeat None (Z.to_nat (n_pre - 3)))
      (Some (Znth 0 values 0))).
    rewrite (Int64Array.mixed_seg_unfold b_pre 2 n_pre
      (repeat None (Z.to_nat (n_pre - 3)))
      (Some (Znth 0 values 0))).
    simpl Int64Array.mixedstoreA.
    sep_apply_l_atomic (Int64Array.mixed_seg_to_undef_seg b_pre 3 n_pre
      (repeat None (Z.to_nat (n_pre - 3)))).
    cancel (Int64Array.undef_seg b_pre 3 n_pre).
    rewrite (Int64Array.seg_unfold b_pre 0 3
      (Znth 0 values 0 :: Znth 0 values 0 :: nil)
      (-(Znth 1 values 0 + Znth 2 values 0))).
    rewrite (Int64Array.seg_unfold b_pre 1 3
      (Znth 0 values 0 :: nil) (Znth 0 values 0)).
    rewrite (Int64Array.seg_unfold b_pre 2 3 nil (Znth 0 values 0)).
    rewrite (Int64Array.seg_empty b_pre 3 3).
    simpl.
    cancel.
    split_pure_spatial.
    + cancel.
    + dump_pre_spatial. lia.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    change (Z.rem n_pre 2 = 1).
    pose proof (Z.rem_bound_pos n_pre 2 ltac:(lia) ltac:(lia)) as Hmod.
    lia.
Qed.

Lemma proof_of_solver_entail_wit_3_4_split_goal_1 : solver_entail_wit_3_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold OutputPrefix.
  simpl.
  repeat split; try reflexivity; try lia.
  constructor.
Qed.

Lemma proof_of_solver_entail_wit_3_4_split_goal_2 : solver_entail_wit_3_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply PreH3; lia.
Qed.

Lemma proof_of_solver_entail_wit_3_4 : solver_entail_wit_3_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_3_4_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_1 : solver_entail_wit_4_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  rename PreH4 into Hrange.
  exact (Hrange j H).
Qed.

Lemma proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_4_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_4_2_split_goal_1 : solver_entail_wit_4_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  rename PreH4 into Hrange.
  exact (Hrange j H).
Qed.

Lemma proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_4_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_5_1_split_goal_1 : solver_entail_wit_5_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
Qed.

Lemma proof_of_solver_entail_wit_5_1_split_goal_spatial : solver_entail_wit_5_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(idtac).
  sep_apply_l_atomic
    (Int64Array.undef_seg_split_to_undef_seg b_pre i (i + 2) n_pre).
  - dump_pre_spatial. lia.
  - sep_apply_l_atomic
      (Int64Array.undef_seg_to_undef_full b_pre i (i + 2)).
    replace (i + 2 - i) with 2 by lia.
    cancel.
Qed.

Lemma proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_1_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_5_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_5_2_split_goal_1 : solver_entail_wit_5_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
Qed.

Lemma proof_of_solver_entail_wit_5_2_split_goal_spatial : solver_entail_wit_5_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  sep_apply_l_atomic
    (Int64Array.undef_seg_split_to_undef_seg b_pre i (i + 2) n_pre).
  - dump_pre_spatial. lia.
  - sep_apply_l_atomic
      (Int64Array.undef_seg_to_undef_full b_pre i (i + 2)).
    replace (i + 2 - i) with 2 by lia.
    cancel.
Qed.

Lemma proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_2_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_5_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_6_1 : solver_entail_wit_6_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists (written_2 ++ pair_out).
  split_pure_spatial.
  - sep_apply_l_atomic
      (Int64Array.full_to_seg
        (b_pre + i * sizeof(INT64)) 2 pair_out).
    rewrite <- (Int64Array.seg_shift b_pre i 0 2 pair_out).
    replace (i + 0) with i by lia.
    sep_apply_l_atomic
      (Int64Array.seg_merge_to_seg b_pre 0 i (i + 2)
        written_2 pair_out).
    + dump_pre_spatial. lia.
    + cancel (IntArray.full a_pre n_pre values).
      cancel (Int64Array.seg b_pre 0 (i + 2) (written_2 ++ pair_out)).
      cancel (Int64Array.undef_seg b_pre (i + 2) n_pre).
  - split_pures; dump_pre_spatial; try lia; try assumption.
    + replace (i + 2 - start) with ((i - start) + 1 * 2) by lia.
      rewrite Z.rem_add by nia. exact PreH11.
    + apply output_prefix_append_pair__loop_extension; try assumption; lia.
Qed.

Lemma proof_of_solver_entail_wit_6_2 : solver_entail_wit_6_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists (written_2 ++ pair_out).
  split_pure_spatial.
  - sep_apply_l_atomic
      (Int64Array.full_to_seg
        (b_pre + i * sizeof(INT64)) 2 pair_out).
    rewrite <- (Int64Array.seg_shift b_pre i 0 2 pair_out).
    replace (i + 0) with i by lia.
    sep_apply_l_atomic
      (Int64Array.seg_merge_to_seg b_pre 0 i (i + 2)
        written_2 pair_out).
    + dump_pre_spatial. lia.
    + cancel (IntArray.full a_pre n_pre values).
      cancel (Int64Array.seg b_pre 0 (i + 2) (written_2 ++ pair_out)).
      cancel (Int64Array.undef_seg b_pre (i + 2) n_pre).
  - split_pures; dump_pre_spatial; try lia; try assumption.
    + replace (i + 2 - start) with ((i - start) + 1 * 2) by lia.
      rewrite Z.rem_add by nia. exact PreH11.
    + apply output_prefix_append_pair__loop_extension; try assumption; lia.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (output_prefix_to_spec_by_parity__final_result
       n_pre values written i start
       PreH1 PreH2 PreH3 PreH4 (or_introl PreH6)
       PreH8 PreH9 PreH10 PreH11 PreH12) as [Hi Hspec].
  subst i.
  Exists written.
  rewrite Int64Array.undef_seg_empty.
  split_pure_spatial.
  - sep_apply (Int64Array.seg_to_full b_pre 0 n_pre written).
    replace (b_pre + 0 * sizeof(INT64)) with b_pre by lia.
    replace (n_pre - 0) with n_pre by lia.
    cancel.
  - dump_pre_spatial.
    exact Hspec.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (output_prefix_to_spec_by_parity__final_result
       n_pre values written i start
       PreH1 PreH2 PreH3 PreH4 (or_intror PreH6)
       PreH8 PreH9 PreH10 PreH11 PreH12) as [Hi Hspec].
  subst i.
  Exists written.
  rewrite Int64Array.undef_seg_empty.
  split_pure_spatial.
  - sep_apply (Int64Array.seg_to_full b_pre 0 n_pre written).
    replace (b_pre + 0 * sizeof(INT64)) with b_pre by lia.
    replace (n_pre - 0) with n_pre by lia.
    cancel.
  - dump_pre_spatial.
    exact Hspec.
Qed.
