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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P033_1737B_elas_fitness_and_the_luxury_number_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P033_1737B_elas_fitness_and_the_luxury_number_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P033_1737B_elas_fitness_and_the_luxury_number_lib.
Local Open Scope sac.

Lemma proof_of_isqrt_safety_wit_3_split_goal_1 : isqrt_safety_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv by lia.
  assert (Hhalf : (hi - lo + 1) / 2 <= hi - lo).
  { apply Z.div_le_upper_bound; lia. }
  lia.
Qed.

Lemma proof_of_isqrt_safety_wit_3_split_goal_2 : isqrt_safety_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv by lia.
  assert (Hnonneg : 0 <= (hi - lo + 1) / 2).
  { apply Z.div_pos; lia. }
  lia.
Qed.

Lemma proof_of_isqrt_safety_wit_3 : isqrt_safety_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_isqrt_safety_wit_3_split_goal_1.
  - Goal_apply proof_of_isqrt_safety_wit_3_split_goal_2.
Qed.

Lemma proof_of_isqrt_safety_wit_9_split_goal_1 : isqrt_safety_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_isqrt_safety_wit_9_split_goal_2 : isqrt_safety_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv by lia.
  assert (Hpos : 1 <= (hi - lo + 1) / 2).
  { apply Z.div_le_lower_bound; lia. }
  lia.
Qed.

Lemma proof_of_isqrt_safety_wit_9 : isqrt_safety_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_isqrt_safety_wit_9_split_goal_1.
  - Goal_apply proof_of_isqrt_safety_wit_9_split_goal_2.
Qed.

Lemma proof_of_isqrt_safety_wit_10_split_goal_1 : isqrt_safety_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv by lia.
  assert (Hhalf : (hi - lo + 1) / 2 <= hi - lo).
  { apply Z.div_le_upper_bound; lia. }
  lia.
Qed.

Lemma proof_of_isqrt_safety_wit_10_split_goal_2 : isqrt_safety_wit_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite zdiv_equiv by lia.
  assert (Hpos : 1 <= (hi - lo + 1) / 2).
  { apply Z.div_le_lower_bound; lia. }
  lia.
Qed.

Lemma proof_of_isqrt_safety_wit_10 : isqrt_safety_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_isqrt_safety_wit_10_split_goal_1.
  - Goal_apply proof_of_isqrt_safety_wit_10_split_goal_2.
Qed.

Lemma proof_of_isqrt_entail_wit_1_split_goal_1 : isqrt_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold SqrtSearchBounds.
  nia.
Qed.

Lemma proof_of_isqrt_entail_wit_1 : isqrt_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_isqrt_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_isqrt_entail_wit_2_1_split_goal_1 : isqrt_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (zdiv_equiv ((hi - lo) + 1) 2) in * by lia.
  pose proof (Z.div_mod ((hi - lo) + 1) 2 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound ((hi - lo) + 1) 2 ltac:(lia)) as Hmod.
  assert (Hmidpos : 0 < lo + ((hi - lo) + 1) / 2) by lia.
  rewrite (zdiv_equiv v_pre (lo + ((hi - lo) + 1) / 2)) in PreH1 by lia.
  unfold SqrtSearchBounds in *.
  split.
  - apply div_upper_implies_square_le__isqrt_invariant; assumption.
  - exact (proj2 PreH8).
Qed.

Lemma proof_of_isqrt_entail_wit_2_1_split_goal_2 : isqrt_entail_wit_2_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (zdiv_equiv ((hi - lo) + 1) 2) in * by lia.
  pose proof (Z.div_mod ((hi - lo) + 1) 2 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound ((hi - lo) + 1) 2 ltac:(lia)) as Hmod.
  lia.
Qed.

Lemma proof_of_isqrt_entail_wit_2_1_split_goal_3 : isqrt_entail_wit_2_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (zdiv_equiv ((hi - lo) + 1) 2) in * by lia.
  pose proof (Z.div_mod ((hi - lo) + 1) 2 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound ((hi - lo) + 1) 2 ltac:(lia)) as Hmod.
  lia.
Qed.

Lemma proof_of_isqrt_entail_wit_2_1 : isqrt_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_isqrt_entail_wit_2_1_split_goal_1.
  - Goal_apply proof_of_isqrt_entail_wit_2_1_split_goal_2.
  - Goal_apply proof_of_isqrt_entail_wit_2_1_split_goal_3.
Qed.

Lemma proof_of_isqrt_entail_wit_2_2_split_goal_1 : isqrt_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (zdiv_equiv ((hi - lo) + 1) 2) in * by lia.
  pose proof (Z.div_mod ((hi - lo) + 1) 2 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound ((hi - lo) + 1) 2 ltac:(lia)) as Hmod.
  assert (Hmidpos : 0 < lo + ((hi - lo) + 1) / 2) by lia.
  rewrite (zdiv_equiv v_pre (lo + ((hi - lo) + 1) / 2)) in PreH1 by lia.
  unfold SqrtSearchBounds in *.
  split.
  - exact (proj1 PreH8).
  - assert (Hlower :
        v_pre / (lo + ((hi - lo) + 1) / 2) < lo + ((hi - lo) + 1) / 2) by lia.
    pose proof
      (div_lower_implies_square_gt__isqrt_invariant
         v_pre (lo + ((hi - lo) + 1) / 2) PreH3 Hmidpos Hlower) as Hsquare.
    nia.
Qed.

Lemma proof_of_isqrt_entail_wit_2_2_split_goal_2 : isqrt_entail_wit_2_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (zdiv_equiv ((hi - lo) + 1) 2) in * by lia.
  pose proof (Z.div_mod ((hi - lo) + 1) 2 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound ((hi - lo) + 1) 2 ltac:(lia)) as Hmod.
  lia.
Qed.

Lemma proof_of_isqrt_entail_wit_2_2_split_goal_3 : isqrt_entail_wit_2_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite (zdiv_equiv ((hi - lo) + 1) 2) in * by lia.
  pose proof (Z.div_mod ((hi - lo) + 1) 2 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound ((hi - lo) + 1) 2 ltac:(lia)) as Hmod.
  lia.
Qed.

Lemma proof_of_isqrt_entail_wit_2_2 : isqrt_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_isqrt_entail_wit_2_2_split_goal_1.
  - Goal_apply proof_of_isqrt_entail_wit_2_2_split_goal_2.
  - Goal_apply proof_of_isqrt_entail_wit_2_2_split_goal_3.
Qed.

Lemma proof_of_isqrt_return_wit_1_split_goal_1 : isqrt_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold SqrtSearchBounds in PreH7.
  unfold ISqrtSpec.
  nia.
Qed.

Lemma proof_of_isqrt_return_wit_1 : isqrt_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_isqrt_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_count_upto_safety_wit_3_split_goal_1 : count_upto_safety_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (isqrt_root_range__count_setup x_pre retval ltac:(lia) PreH4 PreH1)
    as Hrange.
  destruct Hrange as [Hlo Hhi].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_count_upto_safety_wit_3_split_goal_2 : count_upto_safety_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (isqrt_root_range__count_setup x_pre retval ltac:(lia) PreH4 PreH1)
    as Hrange.
  destruct Hrange as [Hlo Hhi].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_count_upto_safety_wit_3 : count_upto_safety_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_count_upto_safety_wit_3_split_goal_1.
  - Goal_apply proof_of_count_upto_safety_wit_3_split_goal_2.
Qed.

Lemma proof_of_count_upto_safety_wit_4_split_goal_1 : count_upto_safety_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (isqrt_root_range__count_setup x_pre retval ltac:(lia) PreH4 PreH1)
    as Hrange.
  destruct Hrange as [Hlo Hhi].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_count_upto_safety_wit_4_split_goal_2 : count_upto_safety_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (isqrt_root_range__count_setup x_pre retval ltac:(lia) PreH4 PreH1)
    as Hrange.
  destruct Hrange as [Hlo Hhi].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_count_upto_safety_wit_4 : count_upto_safety_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_count_upto_safety_wit_4_split_goal_1.
  - Goal_apply proof_of_count_upto_safety_wit_4_split_goal_2.
Qed.

Lemma proof_of_count_upto_safety_wit_7_split_goal_1 : count_upto_safety_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold ISqrtSpec in PreH1.
  destruct PreH1 as [Hroot [Hsq Hnext]].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_count_upto_safety_wit_7_split_goal_2 : count_upto_safety_wit_7_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_count_upto_safety_wit_7 : count_upto_safety_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_count_upto_safety_wit_7_split_goal_1.
  - Goal_apply proof_of_count_upto_safety_wit_7_split_goal_2.
Qed.

Lemma proof_of_count_upto_entail_wit_1_split_goal_1 : count_upto_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold LuxuryBlockPrefix.
  rewrite set_card_empty__count_setup.
  - lia.
  - intros k Hk.
    lia.
Qed.

Lemma proof_of_count_upto_entail_wit_1_split_goal_2 : count_upto_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (isqrt_root_range__count_setup x_pre retval ltac:(lia) PreH4 PreH1)
    as Hrange.
  destruct Hrange as [Hlo Hhi].
  lia.
Qed.

Lemma proof_of_count_upto_entail_wit_1_split_goal_3 : count_upto_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (isqrt_root_range__count_setup x_pre retval ltac:(lia) PreH4 PreH1)
    as Hrange.
  destruct Hrange as [Hlo Hhi].
  lia.
Qed.

Lemma proof_of_count_upto_entail_wit_1_split_goal_4 : count_upto_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (isqrt_root_range__count_setup x_pre retval ltac:(lia) PreH4 PreH1)
    as Hrange.
  destruct Hrange as [Hlo Hhi].
  lia.
Qed.

Lemma proof_of_count_upto_entail_wit_1_split_goal_5 : count_upto_entail_wit_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (isqrt_root_range__count_setup x_pre retval ltac:(lia) PreH4 PreH1)
    as Hrange.
  destruct Hrange as [Hlo Hhi].
  lia.
Qed.

Lemma proof_of_count_upto_entail_wit_1 : count_upto_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_count_upto_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_count_upto_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_count_upto_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_count_upto_entail_wit_1_split_goal_4.
  - Goal_apply proof_of_count_upto_entail_wit_1_split_goal_5.
Qed.

Lemma proof_of_count_upto_entail_wit_2_1_split_goal_1 : count_upto_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst base.
  pose proof (luxury_block_prefix_hit_step__count_transitions
    x_pre s m cnt PreH5 (conj PreH9 PreH2) PreH14 PreH1) as Hstep.
  exact (proj1 Hstep).
Qed.

Lemma proof_of_count_upto_entail_wit_2_1_split_goal_2 : count_upto_entail_wit_2_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst base.
  pose proof (luxury_block_prefix_hit_step__count_transitions
    x_pre s m cnt PreH5 (conj PreH9 PreH2) PreH14 PreH1) as Hstep.
  pose proof (proj2 Hstep) as Hbound.
  lia.
Qed.

Lemma proof_of_count_upto_entail_wit_2_1_split_goal_3 : count_upto_entail_wit_2_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst base.
  pose proof (luxury_block_prefix_hit_step__count_transitions
    x_pre s m cnt PreH5 (conj PreH9 PreH2) PreH14 PreH1) as Hstep.
  exact (proj2 Hstep).
Qed.

Lemma proof_of_count_upto_entail_wit_2_1 : count_upto_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_count_upto_entail_wit_2_1_split_goal_1.
  - Goal_apply proof_of_count_upto_entail_wit_2_1_split_goal_2.
  - Goal_apply proof_of_count_upto_entail_wit_2_1_split_goal_3.
Qed.

Lemma proof_of_count_upto_entail_wit_2_2_split_goal_1 : count_upto_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst base.
  apply (luxury_block_prefix_miss_step__count_transitions
    x_pre s m cnt PreH5 (conj PreH9 PreH2) PreH14).
  lia.
Qed.

Lemma proof_of_count_upto_entail_wit_2_2 : count_upto_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_count_upto_entail_wit_2_2_split_goal_1.
Qed.

Lemma proof_of_count_upto_return_wit_1_split_goal_1 : count_upto_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply luxury_block_prefix_complete__count_final; eauto.
  replace 3 with m by lia.
  assumption.
Qed.

Lemma proof_of_count_upto_return_wit_1 : count_upto_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_count_upto_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_count_upto_return_wit_2_split_goal_1 : count_upto_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (x_pre = 0) by lia.
  subst x_pre.
  unfold LuxuryCountUpto.
  symmetry.
  apply set_card_empty__count_final.
  intros z [[Hzlo Hzhi] Hzlux].
  lia.
Qed.

Lemma proof_of_count_upto_return_wit_2 : count_upto_return_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_count_upto_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply luxury_count_interval_difference__solver_final; assumption.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.
