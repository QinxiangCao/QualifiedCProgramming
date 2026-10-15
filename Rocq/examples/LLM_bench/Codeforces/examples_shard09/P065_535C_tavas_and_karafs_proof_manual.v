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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P065_535C_tavas_and_karafs_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P065_535C_tavas_and_karafs_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P065_535C_tavas_and_karafs_lib.
Local Open Scope sac.

Lemma proof_of_range_sum_return_wit_1_split_goal_1 : range_sum_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  f_equal.
  ring.
Qed.

Lemma proof_of_range_sum_return_wit_1 : range_sum_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_range_sum_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_answer_query_safety_wit_5_split_goal_1 : answer_query_safety_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Z.quot_div_nonneg by lia.
  assert (((hi - lo) + 1) / 2 <= hi - lo) by
    (apply Z.div_le_upper_bound; lia).
  lia.
Qed.

Lemma proof_of_answer_query_safety_wit_5_split_goal_2 : answer_query_safety_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Z.quot_div_nonneg by lia.
  assert (0 <= ((hi - lo) + 1) / 2) by
    (apply Z_div_nonneg_nonneg; lia).
  lia.
Qed.

Lemma proof_of_answer_query_safety_wit_5 : answer_query_safety_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_answer_query_safety_wit_5_split_goal_1.
  - Goal_apply proof_of_answer_query_safety_wit_5_split_goal_2.
Qed.

Lemma proof_of_answer_query_safety_wit_14_split_goal_1 : answer_query_safety_wit_14_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_answer_query_safety_wit_14_split_goal_2 : answer_query_safety_wit_14_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Z.quot_div_nonneg by lia.
  assert (1 <= ((hi - lo) + 1) / 2) by
    (apply Z.div_le_lower_bound; lia).
  lia.
Qed.

Lemma proof_of_answer_query_safety_wit_14 : answer_query_safety_wit_14.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_answer_query_safety_wit_14_split_goal_1.
  - Goal_apply proof_of_answer_query_safety_wit_14_split_goal_2.
Qed.

Lemma proof_of_answer_query_entail_wit_1 : answer_query_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: destruct (query_answer_exists_standard__query_semantic_core
    A_pre B_pre l_pre t_pre m_pre PreH3 PreH5
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as [ans [Hans HQ]].
  all: Exists ans.
  all: (split_pure_spatial;
    [ cancel
    | split_pures; dump_pre_spatial; try lia; try assumption ]).
Qed.

Lemma proof_of_answer_query_entail_wit_2 : answer_query_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists ans_2.
  split_pure_spatial.
  - cancel emp.
  - split_pures.
    all: dump_pre_spatial; try assumption; nia.
Qed.

Lemma proof_of_answer_query_entail_wit_3 : answer_query_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: pose proof (query_answer_height_infeasible_upper__query_semantic_core
    A_pre B_pre l_pre t_pre m_pre hi ans_2
    PreH3 PreH5 PreH7 PreH9 PreH11 PreH13 ltac:(lia) PreH17)
    as Hans_hi.
  all: Exists ans_2.
  all: (split_pure_spatial;
    [ cancel
    | split_pures; dump_pre_spatial; try lia; try assumption ]).
Qed.

Lemma proof_of_answer_query_entail_wit_4 : answer_query_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists ans_2.
  split_pure_spatial.
  - cancel emp.
  - split_pures.
    all: dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_answer_query_entail_wit_5_1 : answer_query_entail_wit_5_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: pose proof (midpoint_bounds__query_semantic_core lo hi PreH5)
    as Hmid_bounds.
  all: destruct Hmid_bounds as [Hmid_low Hmid_high].
  all: assert (Hmid_quot :
    (hi - lo + 1) ÷ 2 = (hi - lo + 1) / 2) by
    (apply Z.quot_div_nonneg; lia).
  all: rewrite Hmid_quot in *.
  all: assert (Hleft_nonneg :
    0 <= A_pre + (l_pre - 1) * B_pre) by nia.
  all: assert (Hright_nonneg :
    0 <= A_pre + (lo + (hi - lo + 1) / 2 - 1) * B_pre) by nia.
  all: assert (Hcount_nonneg :
    0 <= lo + (hi - lo + 1) / 2 - l_pre + 1) by lia.
  all: assert (Hsum_nonneg :
    0 <= (A_pre + (l_pre - 1) * B_pre +
      A_pre + (lo + (hi - lo + 1) / 2 - 1) * B_pre) *
      (lo + (hi - lo + 1) / 2 - l_pre + 1)) by
    (apply Z.mul_nonneg_nonneg; lia).
  all: rewrite Z.quot_div_nonneg in PreH2 by lia.
  all: assert (Hmid_height :
    A_pre + (lo + (hi - lo + 1) / 2 - 1) * B_pre <= t_pre) by
    (rewrite <- PreH4; exact PreH3).
  all: assert (Hmid_budget :
    ((A_pre + (l_pre - 1) * B_pre +
      A_pre + (lo + (hi - lo + 1) / 2 - 1) * B_pre) *
      (lo + (hi - lo + 1) / 2 - l_pre + 1)) / 2 <=
      t_pre * m_pre) by (rewrite <- PreH2; exact PreH1).
  all: assert (Hmid_eatable :
    Eatable A_pre B_pre l_pre t_pre m_pre
      (lo + (hi - lo + 1) / 2)) by
    (apply (proj2 (arithmetic_segment_eatable_iff__query_semantic_core
       A_pre B_pre l_pre t_pre m_pre
       (lo + (hi - lo + 1) / 2)
       PreH6 PreH8 PreH10 PreH12 PreH14 ltac:(lia)));
     exact (conj Hmid_height Hmid_budget)).
  all: pose proof (query_answer_feasible_lower__query_semantic_core
    A_pre B_pre l_pre t_pre m_pre (lo + (hi - lo + 1) / 2) ans_2
    PreH6 PreH8 PreH10 PreH12 PreH14 ltac:(lia) Hmid_eatable PreH20)
    as Hmid_ans.
  all: Exists ans_2.
  all: (split_pure_spatial;
    [ cancel
    | split_pures; dump_pre_spatial; try lia; try assumption ]).
Qed.

Lemma proof_of_answer_query_entail_wit_5_2 : answer_query_entail_wit_5_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: pose proof (midpoint_bounds__query_semantic_core lo hi PreH3)
    as Hmid_bounds.
  all: destruct Hmid_bounds as [Hmid_low Hmid_high].
  all: assert (Hmid_quot :
    (hi - lo + 1) ÷ 2 = (hi - lo + 1) / 2) by
    (apply Z.quot_div_nonneg; lia).
  all: rewrite Hmid_quot in *.
  all: assert (Hmid_height_fail :
    A_pre + (lo + (hi - lo + 1) / 2 - 1) * B_pre > t_pre) by
    (rewrite <- PreH2; exact PreH1).
  all: pose proof (query_answer_height_infeasible_upper__query_semantic_core
    A_pre B_pre l_pre t_pre m_pre (lo + (hi - lo + 1) / 2) ans_2
    PreH4 PreH6 PreH8 PreH10 PreH12 ltac:(lia) Hmid_height_fail PreH18)
    as Hans_mid.
  all: Exists ans_2.
  all: (split_pure_spatial;
    [ cancel
    | split_pures; dump_pre_spatial; try lia; try assumption ]).
Qed.

Lemma proof_of_answer_query_entail_wit_5_3 : answer_query_entail_wit_5_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: pose proof (midpoint_bounds__query_semantic_core lo hi PreH5)
    as Hmid_bounds.
  all: destruct Hmid_bounds as [Hmid_low Hmid_high].
  all: assert (Hmid_quot :
    (hi - lo + 1) ÷ 2 = (hi - lo + 1) / 2) by
    (apply Z.quot_div_nonneg; lia).
  all: rewrite Hmid_quot in *.
  all: assert (Hleft_nonneg :
    0 <= A_pre + (l_pre - 1) * B_pre) by nia.
  all: assert (Hright_nonneg :
    0 <= A_pre + (lo + (hi - lo + 1) / 2 - 1) * B_pre) by nia.
  all: assert (Hcount_nonneg :
    0 <= lo + (hi - lo + 1) / 2 - l_pre + 1) by lia.
  all: assert (Hsum_nonneg :
    0 <= (A_pre + (l_pre - 1) * B_pre +
      A_pre + (lo + (hi - lo + 1) / 2 - 1) * B_pre) *
      (lo + (hi - lo + 1) / 2 - l_pre + 1)) by
    (apply Z.mul_nonneg_nonneg; lia).
  all: rewrite Z.quot_div_nonneg in PreH2 by lia.
  all: assert (Hmid_budget_fail :
    ((A_pre + (l_pre - 1) * B_pre +
      A_pre + (lo + (hi - lo + 1) / 2 - 1) * B_pre) *
      (lo + (hi - lo + 1) / 2 - l_pre + 1)) / 2 >
      t_pre * m_pre) by (rewrite <- PreH2; exact PreH1).
  all: pose proof (query_answer_budget_infeasible_upper__query_semantic_core
    A_pre B_pre l_pre t_pre m_pre (lo + (hi - lo + 1) / 2) ans_2
    PreH6 PreH8 PreH10 PreH12 PreH14 ltac:(lia) Hmid_budget_fail PreH20)
    as Hans_mid.
  all: Exists ans_2.
  all: (split_pure_spatial;
    [ cancel
    | split_pures; dump_pre_spatial; try lia; try assumption ]).
Qed.

Lemma proof_of_answer_query_return_wit_1_split_goal_1 : answer_query_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (lo = ans) by lia.
  subst ans.
  exact PreH16.
Qed.

Lemma proof_of_answer_query_return_wit_1 : answer_query_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_answer_query_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_answer_query_return_wit_2_split_goal_1 : answer_query_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply query_answer_minus_one_height__query_semantic_core; lia.
Qed.

Lemma proof_of_answer_query_return_wit_2 : answer_query_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_answer_query_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_answer_query_partial_solve_wit_3_pure_split_goal_1 : answer_query_partial_solve_wit_3_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Z.quot_div_nonneg by lia.
  assert (1 <= ((hi - lo) + 1) / 2) by
    (apply Z.div_le_lower_bound; lia).
  lia.
Qed.

Lemma proof_of_answer_query_partial_solve_wit_3_pure_split_goal_2 : answer_query_partial_solve_wit_3_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Z.quot_div_nonneg by lia.
  assert (((hi - lo) + 1) / 2 <= hi - lo) by
    (apply Z.div_le_upper_bound; lia).
  lia.
Qed.

Lemma proof_of_answer_query_partial_solve_wit_3_pure : answer_query_partial_solve_wit_3_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_answer_query_partial_solve_wit_3_pure_split_goal_1.
  - Goal_apply proof_of_answer_query_partial_solve_wit_3_pure_split_goal_2.
Qed.

Lemma proof_of_answer_query_partial_solve_wit_4_pure_split_goal_1 : answer_query_partial_solve_wit_4_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Z.quot_div_nonneg by lia.
  assert (0 <= ((hi - lo) + 1) / 2) by
    (apply Z_div_nonneg_nonneg; lia).
  lia.
Qed.

Lemma proof_of_answer_query_partial_solve_wit_4_pure : answer_query_partial_solve_wit_4_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_answer_query_partial_solve_wit_4_pure_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_4 : solver_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_spatial : solver_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  sep_apply_l_atomic (Int64Array.full_shape_to_undef_full out_pre n_pre).
  sep_apply_l_atomic (Int64Array.undef_full_to_undef_seg out_pre n_pre).
  cancel.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_1_split_goal_spatial.
  Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
  Goal_apply proof_of_solver_entail_wit_1_split_goal_3.
  Goal_apply proof_of_solver_entail_wit_1_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i = n_pre) by lia.
  rewrite Hi in *.
  rewrite Int64Array.undef_seg_empty.
  sep_apply (Int64Array.seg_to_full out_pre 0 n_pre result_2).
  replace (out_pre + 0 * sizeof(INT64)) with out_pre by lia.
  replace (n_pre - 0) with n_pre by lia.
  Exists result_2.
  split_pure_spatial.
  - cancel.
    cancel.
  - dump_pre_spatial.
    unfold Spec.
    split.
    + lia.
    + intros k Hk.
      rewrite (Znth_indep queries k (0, 0, 0)
                 __default__Prod__Prod_Z_Z_Z) by lia.
      apply PreH17.
      lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_4_pure_split_goal_1 : solver_partial_solve_wit_4_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH20 i ltac:(lia)).
  specialize (PreH21 i ltac:(lia)).
  destruct PreH20 as [[[[[Hllow Hlup] Htlow] Htup] Hmlow] Hmup].
  destruct PreH21 as [[Hleft Htime] Hmax].
  rewrite Hleft.
  dump_pre_spatial.
  exact Hllow.
Qed.

Lemma proof_of_solver_partial_solve_wit_4_pure_split_goal_2 : solver_partial_solve_wit_4_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH20 i ltac:(lia)).
  specialize (PreH21 i ltac:(lia)).
  destruct PreH20 as [[[[[Hllow Hlup] Htlow] Htup] Hmlow] Hmup].
  destruct PreH21 as [[Hleft Htime] Hmax].
  rewrite Hleft.
  dump_pre_spatial.
  exact Hlup.
Qed.

Lemma proof_of_solver_partial_solve_wit_4_pure_split_goal_3 : solver_partial_solve_wit_4_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH20 i ltac:(lia)).
  specialize (PreH21 i ltac:(lia)).
  destruct PreH20 as [[[[[Hllow Hlup] Htlow] Htup] Hmlow] Hmup].
  destruct PreH21 as [[Hleft Htime] Hmax].
  rewrite Htime.
  dump_pre_spatial.
  exact Htlow.
Qed.

Lemma proof_of_solver_partial_solve_wit_4_pure_split_goal_4 : solver_partial_solve_wit_4_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH20 i ltac:(lia)).
  specialize (PreH21 i ltac:(lia)).
  destruct PreH20 as [[[[[Hllow Hlup] Htlow] Htup] Hmlow] Hmup].
  destruct PreH21 as [[Hleft Htime] Hmax].
  rewrite Htime.
  dump_pre_spatial.
  exact Htup.
Qed.

Lemma proof_of_solver_partial_solve_wit_4_pure_split_goal_5 : solver_partial_solve_wit_4_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH20 i ltac:(lia)).
  specialize (PreH21 i ltac:(lia)).
  destruct PreH20 as [[[[[Hllow Hlup] Htlow] Htup] Hmlow] Hmup].
  destruct PreH21 as [[Hleft Htime] Hmax].
  rewrite Hmax.
  dump_pre_spatial.
  exact Hmlow.
Qed.

Lemma proof_of_solver_partial_solve_wit_4_pure_split_goal_6 : solver_partial_solve_wit_4_pure_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  specialize (PreH20 i ltac:(lia)).
  specialize (PreH21 i ltac:(lia)).
  destruct PreH20 as [[[[[Hllow Hlup] Htlow] Htup] Hmlow] Hmup].
  destruct PreH21 as [[Hleft Htime] Hmax].
  rewrite Hmax.
  dump_pre_spatial.
  exact Hmup.
Qed.

Lemma proof_of_solver_partial_solve_wit_4_pure : solver_partial_solve_wit_4_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_4_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_4_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_4_pure_split_goal_3.
  - Goal_apply proof_of_solver_partial_solve_wit_4_pure_split_goal_4.
  - Goal_apply proof_of_solver_partial_solve_wit_4_pure_split_goal_5.
  - Goal_apply proof_of_solver_partial_solve_wit_4_pure_split_goal_6.
Qed.
