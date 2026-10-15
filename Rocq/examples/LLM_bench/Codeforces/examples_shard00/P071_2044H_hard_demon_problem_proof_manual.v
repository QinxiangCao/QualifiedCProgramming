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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P071_2044H_hard_demon_problem_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard00 Require Import P071_2044H_hard_demon_problem_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P071_2044H_hard_demon_problem_lib.
Local Open Scope sac.

Lemma proof_of_rect_safety_wit_1_split_goal_1 : rect_safety_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  cancel.
  pose proof (PreH20 x1_pre y1_pre x2_pre y2_pre
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hrect.
  unfold RectLookup in Hrect.
  destruct Hrect as [_ Hupper].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_rect_safety_wit_1_split_goal_2 : rect_safety_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  cancel.
  pose proof (PreH20 x1_pre y1_pre x2_pre y2_pre
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hrect.
  unfold RectLookup in Hrect.
  destruct Hrect as [Hlower _].
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_rect_safety_wit_1 : rect_safety_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rect_safety_wit_1_split_goal_1.
  - Goal_apply proof_of_rect_safety_wit_1_split_goal_2.
Qed. 

Lemma proof_of_rect_safety_wit_6_split_goal_1 : rect_safety_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  cancel.
  pose proof (PreH21 x1_pre y1_pre x2_pre y2_pre
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hsafe.
  cbn in Hsafe.
  destruct Hsafe as [_ [_ Hupper]].
  dump_pre_spatial.
  exact Hupper.
Qed.

Lemma proof_of_rect_safety_wit_6_split_goal_2 : rect_safety_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  cancel.
  pose proof (PreH21 x1_pre y1_pre x2_pre y2_pre
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hsafe.
  cbn in Hsafe.
  destruct Hsafe as [_ [Hlower _]].
  dump_pre_spatial.
  exact Hlower.
Qed.

Lemma proof_of_rect_safety_wit_6 : rect_safety_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rect_safety_wit_6_split_goal_1.
  - Goal_apply proof_of_rect_safety_wit_6_split_goal_2.
Qed. 

Lemma proof_of_rect_safety_wit_10_split_goal_1 : rect_safety_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  cancel.
  pose proof (PreH21 x1_pre y1_pre x2_pre y2_pre
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hsafe.
  cbn in Hsafe.
  destruct Hsafe as [[_ Hupper] _].
  dump_pre_spatial.
  exact Hupper.
Qed.

Lemma proof_of_rect_safety_wit_10_split_goal_2 : rect_safety_wit_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  cancel.
  pose proof (PreH21 x1_pre y1_pre x2_pre y2_pre
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hsafe.
  cbn in Hsafe.
  destruct Hsafe as [[Hlower _] _].
  dump_pre_spatial.
  exact Hlower.
Qed.

Lemma proof_of_rect_safety_wit_10 : rect_safety_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rect_safety_wit_10_split_goal_1.
  - Goal_apply proof_of_rect_safety_wit_10_split_goal_2.
Qed. 

Lemma proof_of_rect_entail_wit_1_split_goal_1 : rect_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(nia).
Qed.

Lemma proof_of_rect_entail_wit_1_split_goal_2 : rect_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(nia).
Qed.

Lemma proof_of_rect_entail_wit_1_split_goal_3 : rect_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(nia).
Qed.

Lemma proof_of_rect_entail_wit_1_split_goal_4 : rect_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(nia).
Qed.

Lemma proof_of_rect_entail_wit_1 : rect_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rect_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_rect_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_rect_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_rect_entail_wit_1_split_goal_4.
Qed. 

Lemma proof_of_rect_return_wit_1_split_goal_1 : rect_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH20 x1_pre y1_pre x2_pre y2_pre
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hrect.
  unfold RectLookup in Hrect.
  destruct Hrect as [_ Hupper].
  exact Hupper.
Qed.

Lemma proof_of_rect_return_wit_1_split_goal_2 : rect_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (PreH20 x1_pre y1_pre x2_pre y2_pre
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hrect.
  unfold RectLookup in Hrect.
  destruct Hrect as [Hlower _].
  exact Hlower.
Qed.

Lemma proof_of_rect_return_wit_1_split_goal_3 : rect_return_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_rect_return_wit_1 : rect_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_rect_return_wit_1_split_goal_1.
  - Goal_apply proof_of_rect_return_wit_1_split_goal_2.
  - Goal_apply proof_of_rect_return_wit_1_split_goal_3.
Qed. 

Lemma proof_of_solver_safety_wit_11_split_goal_1 : solver_safety_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold PrefixTables in PreH41.
  destruct PreH41 as [Hslen [Hrlen [Hclen [Hzero Hprefix]]]].
  pose proof (prefix_predecessor_indices__prefix_sum_safety S i j ltac:(lia))
    as [Htopidx [Hleftidx [Hdiagidx [Htoplt [Hleftlt Hdiaglt]]]]].
  pose proof (Hprefix (i - 1) j ltac:(lia) ltac:(lia) Htoplt) as Htop.
  pose proof (Hprefix i (j - 1) ltac:(lia) ltac:(lia) Hleftlt) as Hleft.
  pose proof (Hprefix (i - 1) (j - 1) ltac:(lia) ltac:(lia) Hdiaglt) as Hdiag.
  destruct Htop as [Htop _].
  destruct Hleft as [Hleft _].
  destruct Hdiag as [Hdiag _].
  assert (Htopv : Znth (i * S + j - S) sum_l 0 =
      PrefixSumValue matrix_data n_pre (i - 1) j).
  { rewrite Htopidx. exact Htop. }
  assert (Hleftv : Znth (i * S + j - 1) sum_l 0 =
      PrefixSumValue matrix_data n_pre i (j - 1)).
  { rewrite Hleftidx. exact Hleft. }
  assert (Hdiagv : Znth (i * S + j - S - 1) sum_l 0 =
      PrefixSumValue matrix_data n_pre (i - 1) (j - 1)).
  { rewrite Hdiagidx. exact Hdiag. }
  pose proof (matrix_cell_index__prefix_sum_safety matrix_data n_pre i j) as Hcell.
  pose proof (prefix_sum_value_cell_recurrence__prefix_sum_safety
    matrix_data n_pre i j PreH37 PreH39) as Hrec.
  pose proof (prefix_sum_value_bounds__prefix_sum_safety
    matrix_data n_pre i j PreH34 ltac:(lia) ltac:(lia) ltac:(lia)) as Hbound.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_11_split_goal_2 : solver_safety_wit_11_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold PrefixTables in PreH41.
  destruct PreH41 as [Hslen [Hrlen [Hclen [Hzero Hprefix]]]].
  pose proof (prefix_predecessor_indices__prefix_sum_safety S i j ltac:(lia))
    as [Htopidx [Hleftidx [Hdiagidx [Htoplt [Hleftlt Hdiaglt]]]]].
  pose proof (Hprefix (i - 1) j ltac:(lia) ltac:(lia) Htoplt) as Htop.
  pose proof (Hprefix i (j - 1) ltac:(lia) ltac:(lia) Hleftlt) as Hleft.
  pose proof (Hprefix (i - 1) (j - 1) ltac:(lia) ltac:(lia) Hdiaglt) as Hdiag.
  destruct Htop as [Htop _].
  destruct Hleft as [Hleft _].
  destruct Hdiag as [Hdiag _].
  assert (Htopv : Znth (i * S + j - S) sum_l 0 =
      PrefixSumValue matrix_data n_pre (i - 1) j).
  { rewrite Htopidx. exact Htop. }
  assert (Hleftv : Znth (i * S + j - 1) sum_l 0 =
      PrefixSumValue matrix_data n_pre i (j - 1)).
  { rewrite Hleftidx. exact Hleft. }
  assert (Hdiagv : Znth (i * S + j - S - 1) sum_l 0 =
      PrefixSumValue matrix_data n_pre (i - 1) (j - 1)).
  { rewrite Hdiagidx. exact Hdiag. }
  pose proof (matrix_cell_index__prefix_sum_safety matrix_data n_pre i j) as Hcell.
  pose proof (prefix_sum_value_cell_recurrence__prefix_sum_safety
    matrix_data n_pre i j PreH37 PreH39) as Hrec.
  pose proof (prefix_sum_value_bounds__prefix_sum_safety
    matrix_data n_pre i j PreH34 ltac:(lia) ltac:(lia) ltac:(lia)) as Hbound.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_11 : solver_safety_wit_11.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_11_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_11_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_12_split_goal_1 : solver_safety_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold PrefixTables in PreH41.
  destruct PreH41 as [Hslen [Hrlen [Hclen [Hzero Hprefix]]]].
  pose proof (prefix_predecessor_indices__prefix_sum_safety S i j ltac:(lia))
    as [Htopidx [Hleftidx [Hdiagidx [Htoplt [Hleftlt Hdiaglt]]]]].
  pose proof (Hprefix (i - 1) j ltac:(lia) ltac:(lia) Htoplt) as Htop.
  pose proof (Hprefix i (j - 1) ltac:(lia) ltac:(lia) Hleftlt) as Hleft.
  destruct Htop as [Htop _].
  destruct Hleft as [Hleft _].
  assert (Htopv : Znth (i * S + j - S) sum_l 0 =
      PrefixSumValue matrix_data n_pre (i - 1) j).
  { rewrite Htopidx. exact Htop. }
  assert (Hleftv : Znth (i * S + j - 1) sum_l 0 =
      PrefixSumValue matrix_data n_pre i (j - 1)).
  { rewrite Hleftidx. exact Hleft. }
  pose proof (prefix_sum_value_bounds__prefix_sum_safety
    matrix_data n_pre (i - 1) j PreH34 ltac:(lia) ltac:(lia) ltac:(lia)) as Htopbound.
  pose proof (prefix_sum_value_bounds__prefix_sum_safety
    matrix_data n_pre i (j - 1) PreH34 ltac:(lia) ltac:(lia) ltac:(lia)) as Hleftbound.
  specialize (PreH34 (((i - 1) * n_pre + j) - 1) ltac:(lia)).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_12_split_goal_2 : solver_safety_wit_12_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold PrefixTables in PreH41.
  destruct PreH41 as [Hslen [Hrlen [Hclen [Hzero Hprefix]]]].
  pose proof (prefix_predecessor_indices__prefix_sum_safety S i j ltac:(lia))
    as [Htopidx [Hleftidx [Hdiagidx [Htoplt [Hleftlt Hdiaglt]]]]].
  pose proof (Hprefix (i - 1) j ltac:(lia) ltac:(lia) Htoplt) as Htop.
  pose proof (Hprefix i (j - 1) ltac:(lia) ltac:(lia) Hleftlt) as Hleft.
  destruct Htop as [Htop _].
  destruct Hleft as [Hleft _].
  assert (Htopv : Znth (i * S + j - S) sum_l 0 =
      PrefixSumValue matrix_data n_pre (i - 1) j).
  { rewrite Htopidx. exact Htop. }
  assert (Hleftv : Znth (i * S + j - 1) sum_l 0 =
      PrefixSumValue matrix_data n_pre i (j - 1)).
  { rewrite Hleftidx. exact Hleft. }
  pose proof (prefix_sum_value_bounds__prefix_sum_safety
    matrix_data n_pre (i - 1) j PreH34 ltac:(lia) ltac:(lia) ltac:(lia)) as Htopbound.
  pose proof (prefix_sum_value_bounds__prefix_sum_safety
    matrix_data n_pre i (j - 1) PreH34 ltac:(lia) ltac:(lia) ltac:(lia)) as Hleftbound.
  specialize (PreH34 (((i - 1) * n_pre + j) - 1) ltac:(lia)).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_12 : solver_safety_wit_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_12_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_12_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_13_split_goal_1 : solver_safety_wit_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold PrefixTables in PreH41.
  destruct PreH41 as [Hslen [Hrlen [Hclen [Hzero Hprefix]]]].
  pose proof (prefix_predecessor_indices__prefix_sum_safety S i j ltac:(lia))
    as [Htopidx [Hleftidx [Hdiagidx [Htoplt [Hleftlt Hdiaglt]]]]].
  pose proof (Hprefix (i - 1) j ltac:(lia) ltac:(lia) Htoplt) as Htop.
  destruct Htop as [Htop _].
  assert (Htopv : Znth (i * S + j - S) sum_l 0 =
      PrefixSumValue matrix_data n_pre (i - 1) j).
  { rewrite Htopidx. exact Htop. }
  pose proof (prefix_sum_value_bounds__prefix_sum_safety
    matrix_data n_pre (i - 1) j PreH34 ltac:(lia) ltac:(lia) ltac:(lia)) as Htopbound.
  specialize (PreH34 (((i - 1) * n_pre + j) - 1) ltac:(lia)).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_13_split_goal_2 : solver_safety_wit_13_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold PrefixTables in PreH41.
  destruct PreH41 as [Hslen [Hrlen [Hclen [Hzero Hprefix]]]].
  pose proof (prefix_predecessor_indices__prefix_sum_safety S i j ltac:(lia))
    as [Htopidx [Hleftidx [Hdiagidx [Htoplt [Hleftlt Hdiaglt]]]]].
  pose proof (Hprefix (i - 1) j ltac:(lia) ltac:(lia) Htoplt) as Htop.
  destruct Htop as [Htop _].
  assert (Htopv : Znth (i * S + j - S) sum_l 0 =
      PrefixSumValue matrix_data n_pre (i - 1) j).
  { rewrite Htopidx. exact Htop. }
  pose proof (prefix_sum_value_bounds__prefix_sum_safety
    matrix_data n_pre (i - 1) j PreH34 ltac:(lia) ltac:(lia) ltac:(lia)) as Htopbound.
  specialize (PreH34 (((i - 1) * n_pre + j) - 1) ltac:(lia)).
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_13 : solver_safety_wit_13.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_13_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_13_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_16_split_goal_1 : solver_safety_wit_16_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH41 as (_ & _ & _ & _ & Htables).
  pose proof (Htables (i - 1) (j - 1) ltac:(lia) ltac:(lia) ltac:(nia)) as [_ [Hpp _]].
  pose proof (Htables (i - 1) j ltac:(lia) ltac:(lia) ltac:(nia)) as [_ [Hup _]].
  pose proof (Htables i (j - 1) ltac:(lia) ltac:(lia) ltac:(nia)) as [_ [Hleft _]].
  replace ((i - 1) * S + (j - 1)) with (((i * S + j) - S) - 1) in Hpp by ring.
  replace ((i - 1) * S + j) with ((i * S + j) - S) in Hup by ring.
  replace (i * S + (j - 1)) with ((i * S + j) - 1) in Hleft by ring.
  pose proof (prefix_row_value_cell_recurrence__prefix_row_safety matrix_data n_pre i j ltac:(lia) ltac:(lia)) as Hrec.
  unfold MatrixCell in Hrec.
  replace ((i - 1) * n_pre + (j - 1)) with (((i - 1) * n_pre + j) - 1) in Hrec by ring.
  pose proof (prefix_row_value_bounds__prefix_row_safety matrix_data n_pre i j PreH34 ltac:(lia) ltac:(lia) ltac:(lia)) as Hbound.
  rewrite Hpp, Hup, Hleft, Hrec.
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_safety_wit_16_split_goal_2 : solver_safety_wit_16_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH41 as (_ & _ & _ & _ & Htables).
  pose proof (Htables (i - 1) (j - 1) ltac:(lia) ltac:(lia) ltac:(nia)) as [_ [Hpp _]].
  pose proof (Htables (i - 1) j ltac:(lia) ltac:(lia) ltac:(nia)) as [_ [Hup _]].
  pose proof (Htables i (j - 1) ltac:(lia) ltac:(lia) ltac:(nia)) as [_ [Hleft _]].
  replace ((i - 1) * S + (j - 1)) with (((i * S + j) - S) - 1) in Hpp by ring.
  replace ((i - 1) * S + j) with ((i * S + j) - S) in Hup by ring.
  replace (i * S + (j - 1)) with ((i * S + j) - 1) in Hleft by ring.
  pose proof (prefix_row_value_cell_recurrence__prefix_row_safety matrix_data n_pre i j ltac:(lia) ltac:(lia)) as Hrec.
  unfold MatrixCell in Hrec.
  replace ((i - 1) * n_pre + (j - 1)) with (((i - 1) * n_pre + j) - 1) in Hrec by ring.
  pose proof (prefix_row_value_bounds__prefix_row_safety matrix_data n_pre i j PreH34 ltac:(lia) ltac:(lia) ltac:(lia)) as Hbound.
  rewrite Hpp, Hup, Hleft, Hrec.
  dump_pre_spatial. lia.
Qed.

Lemma proof_of_solver_safety_wit_16 : solver_safety_wit_16.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_16_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_16_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_17_split_goal_1 : solver_safety_wit_17_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH41 as (_ & _ & _ & _ & Htables).
  pose proof (Htables (i - 1) j ltac:(lia) ltac:(lia) ltac:(nia)) as [_ [Hup _]].
  pose proof (Htables i (j - 1) ltac:(lia) ltac:(lia) ltac:(nia)) as [_ [Hleft _]].
  replace ((i - 1) * S + j) with ((i * S + j) - S) in Hup by ring.
  replace (i * S + (j - 1)) with ((i * S + j) - 1) in Hleft by ring.
  pose proof (prefix_row_value_bounds__prefix_row_safety matrix_data n_pre (i - 1) j PreH34 ltac:(lia) ltac:(lia) ltac:(lia)) as Hup_bound.
  pose proof (prefix_row_value_bounds__prefix_row_safety matrix_data n_pre i (j - 1) PreH34 ltac:(lia) ltac:(lia) ltac:(lia)) as Hleft_bound.
  unfold MatrixValuesBounded in PreH34.
  pose proof (PreH34 (((i - 1) * n_pre + j) - 1) ltac:(lia)) as Hcell.
  rewrite Hup, Hleft.
  dump_pre_spatial. nia.
Qed.

Lemma proof_of_solver_safety_wit_17_split_goal_2 : solver_safety_wit_17_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH41 as (_ & _ & _ & _ & Htables).
  pose proof (Htables (i - 1) j ltac:(lia) ltac:(lia) ltac:(nia)) as [_ [Hup _]].
  pose proof (Htables i (j - 1) ltac:(lia) ltac:(lia) ltac:(nia)) as [_ [Hleft _]].
  replace ((i - 1) * S + j) with ((i * S + j) - S) in Hup by ring.
  replace (i * S + (j - 1)) with ((i * S + j) - 1) in Hleft by ring.
  pose proof (prefix_row_value_bounds__prefix_row_safety matrix_data n_pre (i - 1) j PreH34 ltac:(lia) ltac:(lia) ltac:(lia)) as Hup_bound.
  pose proof (prefix_row_value_bounds__prefix_row_safety matrix_data n_pre i (j - 1) PreH34 ltac:(lia) ltac:(lia) ltac:(lia)) as Hleft_bound.
  unfold MatrixValuesBounded in PreH34.
  pose proof (PreH34 (((i - 1) * n_pre + j) - 1) ltac:(lia)) as Hcell.
  rewrite Hup, Hleft.
  dump_pre_spatial. nia.
Qed.

Lemma proof_of_solver_safety_wit_17 : solver_safety_wit_17.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_17_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_17_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_18_split_goal_1 : solver_safety_wit_18_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH41 as (_ & _ & _ & _ & Htables).
  pose proof (Htables (i - 1) j ltac:(lia) ltac:(lia) ltac:(nia)) as [_ [Hup _]].
  replace ((i - 1) * S + j) with ((i * S + j) - S) in Hup by ring.
  pose proof (prefix_row_value_bounds__prefix_row_safety matrix_data n_pre (i - 1) j PreH34 ltac:(lia) ltac:(lia) ltac:(lia)) as Hup_bound.
  unfold MatrixValuesBounded in PreH34.
  pose proof (PreH34 (((i - 1) * n_pre + j) - 1) ltac:(lia)) as Hcell.
  rewrite Hup.
  dump_pre_spatial. nia.
Qed.

Lemma proof_of_solver_safety_wit_18_split_goal_2 : solver_safety_wit_18_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH41 as (_ & _ & _ & _ & Htables).
  pose proof (Htables (i - 1) j ltac:(lia) ltac:(lia) ltac:(nia)) as [_ [Hup _]].
  replace ((i - 1) * S + j) with ((i * S + j) - S) in Hup by ring.
  pose proof (prefix_row_value_bounds__prefix_row_safety matrix_data n_pre (i - 1) j PreH34 ltac:(lia) ltac:(lia) ltac:(lia)) as Hup_bound.
  unfold MatrixValuesBounded in PreH34.
  pose proof (PreH34 (((i - 1) * n_pre + j) - 1) ltac:(lia)) as Hcell.
  rewrite Hup.
  dump_pre_spatial. nia.
Qed.

Lemma proof_of_solver_safety_wit_18 : solver_safety_wit_18.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_18_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_18_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_19_split_goal_1 : solver_safety_wit_19_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixValuesBounded in PreH34.
  pose proof (PreH34 (((i - 1) * n_pre + j) - 1) ltac:(lia)) as Hcell.
  dump_pre_spatial. nia.
Qed.

Lemma proof_of_solver_safety_wit_19_split_goal_2 : solver_safety_wit_19_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  unfold MatrixValuesBounded in PreH34.
  pose proof (PreH34 (((i - 1) * n_pre + j) - 1) ltac:(lia)) as Hcell.
  dump_pre_spatial. nia.
Qed.

Lemma proof_of_solver_safety_wit_19 : solver_safety_wit_19.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_19_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_19_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_22_split_goal_1 : solver_safety_wit_22_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  unfold PrefixTables in PreH41.
  destruct PreH41 as [_ [_ [_ [_ Htable]]]].
  pose proof (Htable (i - 1) j ltac:(lia) ltac:(lia) ltac:(lia)) as [_ [_ Hup]].
  pose proof (Htable i (j - 1) ltac:(lia) ltac:(lia) ltac:(lia)) as [_ [_ Hleft]].
  pose proof (Htable (i - 1) (j - 1) ltac:(lia) ltac:(lia) ltac:(lia)) as [_ [_ Hdiag]].
  pose proof (prefix_col_value_cell_recurrence__prefix_col_safety matrix_data n_pre i j
    ltac:(lia) ltac:(lia)) as Hrec.
  pose proof (prefix_col_value_bounds__prefix_col_safety matrix_data n_pre i j
    PreH34 ltac:(lia) ltac:(lia) ltac:(lia)) as Hbound.
  unfold MatrixCell in Hrec.
  replace (i * S + j - S) with ((i - 1) * S + j) by ring.
  replace (i * S + j - 1) with (i * S + (j - 1)) by ring.
  replace (i * S + j - S - 1) with ((i - 1) * S + (j - 1)) by ring.
  replace ((i - 1) * S + j - 1) with ((i - 1) * S + (j - 1)) by ring.
  replace ((i - 1) * n_pre + j - 1) with ((i - 1) * n_pre + (j - 1)) by ring.
  rewrite Hup, Hleft, Hdiag.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_22_split_goal_2 : solver_safety_wit_22_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  unfold PrefixTables in PreH41.
  destruct PreH41 as [_ [_ [_ [_ Htable]]]].
  pose proof (Htable (i - 1) j ltac:(lia) ltac:(lia) ltac:(lia)) as [_ [_ Hup]].
  pose proof (Htable i (j - 1) ltac:(lia) ltac:(lia) ltac:(lia)) as [_ [_ Hleft]].
  pose proof (Htable (i - 1) (j - 1) ltac:(lia) ltac:(lia) ltac:(lia)) as [_ [_ Hdiag]].
  pose proof (prefix_col_value_cell_recurrence__prefix_col_safety matrix_data n_pre i j
    ltac:(lia) ltac:(lia)) as Hrec.
  pose proof (prefix_col_value_bounds__prefix_col_safety matrix_data n_pre i j
    PreH34 ltac:(lia) ltac:(lia) ltac:(lia)) as Hbound.
  unfold MatrixCell in Hrec.
  replace (i * S + j - S) with ((i - 1) * S + j) by ring.
  replace (i * S + j - 1) with (i * S + (j - 1)) by ring.
  replace (i * S + j - S - 1) with ((i - 1) * S + (j - 1)) by ring.
  replace ((i - 1) * S + j - 1) with ((i - 1) * S + (j - 1)) by ring.
  replace ((i - 1) * n_pre + j - 1) with ((i - 1) * n_pre + (j - 1)) by ring.
  rewrite Hup, Hleft, Hdiag.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_22 : solver_safety_wit_22.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_22_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_22_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_23_split_goal_1 : solver_safety_wit_23_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  unfold PrefixTables in PreH41.
  destruct PreH41 as [_ [_ [_ [_ Htable]]]].
  pose proof (Htable (i - 1) j ltac:(lia) ltac:(lia) ltac:(lia)) as [_ [_ Hup]].
  pose proof (Htable i (j - 1) ltac:(lia) ltac:(lia) ltac:(lia)) as [_ [_ Hleft]].
  pose proof (prefix_col_value_bounds__prefix_col_safety matrix_data n_pre (i - 1) j
    PreH34 ltac:(lia) ltac:(lia) ltac:(lia)) as Hup_bound.
  pose proof (prefix_col_value_bounds__prefix_col_safety matrix_data n_pre i (j - 1)
    PreH34 ltac:(lia) ltac:(lia) ltac:(lia)) as Hleft_bound.
  unfold MatrixValuesBounded in PreH34.
  specialize (PreH34 (((i - 1) * n_pre + j) - 1) ltac:(lia)).
  pose proof (weighted_cell_bounds__prefix_col_safety
    (Znth (((i - 1) * n_pre + j) - 1) matrix_data 0) j PreH34 ltac:(lia)) as Hweighted.
  replace (i * S + j - S) with ((i - 1) * S + j) by ring.
  replace (i * S + j - 1) with (i * S + (j - 1)) by ring.
  rewrite Hup, Hleft.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_23_split_goal_2 : solver_safety_wit_23_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  unfold PrefixTables in PreH41.
  destruct PreH41 as [_ [_ [_ [_ Htable]]]].
  pose proof (Htable (i - 1) j ltac:(lia) ltac:(lia) ltac:(lia)) as [_ [_ Hup]].
  pose proof (Htable i (j - 1) ltac:(lia) ltac:(lia) ltac:(lia)) as [_ [_ Hleft]].
  pose proof (prefix_col_value_bounds__prefix_col_safety matrix_data n_pre (i - 1) j
    PreH34 ltac:(lia) ltac:(lia) ltac:(lia)) as Hup_bound.
  pose proof (prefix_col_value_bounds__prefix_col_safety matrix_data n_pre i (j - 1)
    PreH34 ltac:(lia) ltac:(lia) ltac:(lia)) as Hleft_bound.
  unfold MatrixValuesBounded in PreH34.
  specialize (PreH34 (((i - 1) * n_pre + j) - 1) ltac:(lia)).
  pose proof (weighted_cell_bounds__prefix_col_safety
    (Znth (((i - 1) * n_pre + j) - 1) matrix_data 0) j PreH34 ltac:(lia)) as Hweighted.
  replace (i * S + j - S) with ((i - 1) * S + j) by ring.
  replace (i * S + j - 1) with (i * S + (j - 1)) by ring.
  rewrite Hup, Hleft.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_23 : solver_safety_wit_23.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_23_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_23_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_24_split_goal_1 : solver_safety_wit_24_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  unfold PrefixTables in PreH41.
  destruct PreH41 as [_ [_ [_ [_ Htable]]]].
  pose proof (Htable (i - 1) j ltac:(lia) ltac:(lia) ltac:(lia)) as [_ [_ Hup]].
  pose proof (prefix_col_value_bounds__prefix_col_safety matrix_data n_pre (i - 1) j
    PreH34 ltac:(lia) ltac:(lia) ltac:(lia)) as Hup_bound.
  unfold MatrixValuesBounded in PreH34.
  specialize (PreH34 (((i - 1) * n_pre + j) - 1) ltac:(lia)).
  pose proof (weighted_cell_bounds__prefix_col_safety
    (Znth (((i - 1) * n_pre + j) - 1) matrix_data 0) j PreH34 ltac:(lia)) as Hweighted.
  replace (i * S + j - S) with ((i - 1) * S + j) by ring.
  rewrite Hup.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_24_split_goal_2 : solver_safety_wit_24_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  unfold PrefixTables in PreH41.
  destruct PreH41 as [_ [_ [_ [_ Htable]]]].
  pose proof (Htable (i - 1) j ltac:(lia) ltac:(lia) ltac:(lia)) as [_ [_ Hup]].
  pose proof (prefix_col_value_bounds__prefix_col_safety matrix_data n_pre (i - 1) j
    PreH34 ltac:(lia) ltac:(lia) ltac:(lia)) as Hup_bound.
  unfold MatrixValuesBounded in PreH34.
  specialize (PreH34 (((i - 1) * n_pre + j) - 1) ltac:(lia)).
  pose proof (weighted_cell_bounds__prefix_col_safety
    (Znth (((i - 1) * n_pre + j) - 1) matrix_data 0) j PreH34 ltac:(lia)) as Hweighted.
  replace (i * S + j - S) with ((i - 1) * S + j) by ring.
  rewrite Hup.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_24 : solver_safety_wit_24.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_24_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_24_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_25_split_goal_1 : solver_safety_wit_25_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  unfold MatrixValuesBounded in PreH34.
  specialize (PreH34 (((i - 1) * n_pre + j) - 1) ltac:(lia)).
  pose proof (weighted_cell_bounds__prefix_col_safety
    (Znth (((i - 1) * n_pre + j) - 1) matrix_data 0) j PreH34 ltac:(lia)) as Hweighted.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_25_split_goal_2 : solver_safety_wit_25_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia).
  unfold MatrixValuesBounded in PreH34.
  specialize (PreH34 (((i - 1) * n_pre + j) - 1) ltac:(lia)).
  pose proof (weighted_cell_bounds__prefix_col_safety
    (Znth (((i - 1) * n_pre + j) - 1) matrix_data 0) j PreH34 ltac:(lia)) as Hweighted.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_25 : solver_safety_wit_25.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_25_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_25_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_48_split_goal_1 : solver_safety_wit_48_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: cbn [Z.pow] in *.
  all: unfold QueryArithmeticSafe in *.
  all: cbn zeta in *.
  all: subst retval_3; subst retval_2; subst retval.
  all: dump_pre_spatial.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: nia.
Qed.

Lemma proof_of_solver_safety_wit_48_split_goal_2 : solver_safety_wit_48_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: cbn [Z.pow] in *.
  all: unfold QueryArithmeticSafe in *.
  all: cbn zeta in *.
  all: subst retval_3; subst retval_2; subst retval.
  all: dump_pre_spatial.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: nia.
Qed.

Lemma proof_of_solver_safety_wit_48 : solver_safety_wit_48.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_48_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_48_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_49_split_goal_1 : solver_safety_wit_49_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: cbn [Z.pow] in *.
  all: unfold QueryArithmeticSafe in *.
  all: cbn zeta in *.
  all: subst retval_3; subst retval_2; subst retval.
  all: dump_pre_spatial.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: nia.
Qed.

Lemma proof_of_solver_safety_wit_49_split_goal_2 : solver_safety_wit_49_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: cbn [Z.pow] in *.
  all: unfold QueryArithmeticSafe in *.
  all: cbn zeta in *.
  all: subst retval_3; subst retval_2; subst retval.
  all: dump_pre_spatial.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: nia.
Qed.

Lemma proof_of_solver_safety_wit_49 : solver_safety_wit_49.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_49_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_49_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_51_split_goal_1 : solver_safety_wit_51_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: cbn [Z.pow] in *.
  all: unfold QueryArithmeticSafe in *.
  all: cbn zeta in *.
  all: subst retval_3; subst retval_2; subst retval.
  all: dump_pre_spatial.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: nia.
Qed.

Lemma proof_of_solver_safety_wit_51_split_goal_2 : solver_safety_wit_51_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: cbn [Z.pow] in *.
  all: unfold QueryArithmeticSafe in *.
  all: cbn zeta in *.
  all: subst retval_3; subst retval_2; subst retval.
  all: dump_pre_spatial.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: nia.
Qed.

Lemma proof_of_solver_safety_wit_51 : solver_safety_wit_51.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_51_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_51_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_52_split_goal_1 : solver_safety_wit_52_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: cbn [Z.pow] in *.
  all: unfold QueryArithmeticSafe in *.
  all: cbn zeta in *.
  all: subst retval_3; subst retval_2; subst retval.
  all: dump_pre_spatial.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: nia.
Qed.

Lemma proof_of_solver_safety_wit_52_split_goal_2 : solver_safety_wit_52_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: cbn [Z.pow] in *.
  all: unfold QueryArithmeticSafe in *.
  all: cbn zeta in *.
  all: subst retval_3; subst retval_2; subst retval.
  all: dump_pre_spatial.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: nia.
Qed.

Lemma proof_of_solver_safety_wit_52 : solver_safety_wit_52.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_52_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_52_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_53_split_goal_1 : solver_safety_wit_53_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: cbn [Z.pow] in *.
  all: unfold QueryArithmeticSafe in *.
  all: cbn zeta in *.
  all: subst retval_3; subst retval_2; subst retval.
  all: dump_pre_spatial.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: nia.
Qed.

Lemma proof_of_solver_safety_wit_53_split_goal_2 : solver_safety_wit_53_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: cbn [Z.pow] in *.
  all: unfold QueryArithmeticSafe in *.
  all: cbn zeta in *.
  all: subst retval_3; subst retval_2; subst retval.
  all: dump_pre_spatial.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: nia.
Qed.

Lemma proof_of_solver_safety_wit_53 : solver_safety_wit_53.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_53_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_53_split_goal_2.
Qed. 

Lemma proof_of_solver_safety_wit_54_split_goal_1 : solver_safety_wit_54_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: cbn [Z.pow] in *.
  all: unfold QueryArithmeticSafe in *.
  all: cbn zeta in *.
  all: subst retval_3; subst retval_2; subst retval.
  all: dump_pre_spatial.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: nia.
Qed.

Lemma proof_of_solver_safety_wit_54_split_goal_2 : solver_safety_wit_54_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: cbn [Z.pow] in *.
  all: unfold QueryArithmeticSafe in *.
  all: cbn zeta in *.
  all: subst retval_3; subst retval_2; subst retval.
  all: dump_pre_spatial.
  all: repeat match goal with H : _ /\ _ |- _ => destruct H end.
  all: nia.
Qed.

Lemma proof_of_solver_safety_wit_54 : solver_safety_wit_54.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_54_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_54_split_goal_2.
Qed. 

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (1 * (n_pre + 1)) with (n_pre + 1) by ring.
  apply prefix_tables_repeat_zero_initial__prefix_init_boundary.
  assumption.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
Qed. 

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite PreH2 in PreH15.
  eapply prefix_tables_extend_zero_column__prefix_init_boundary; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
Qed. 

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: nia.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
Qed. 

Lemma proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: nia.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_2 : solver_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: nia.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_3 : solver_entail_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: nia.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_4 : solver_entail_wit_4_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: nia.
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_4.
Qed. 

Lemma proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hj : j = n_pre + 1) by lia.
  rewrite PreH2, Hj in PreH17.
  replace ((i + 1) * (n_pre + 1)) with
    (i * (n_pre + 1) + (n_pre + 1)) by ring.
  exact PreH17.
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_5_split_goal_1.
Qed. 

Lemma proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia).
  subst S.
  apply prefix_tables_replace_step__prefix_transition; try lia; assumption.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_6_split_goal_1.
Qed. 

Lemma proof_of_solver_entail_wit_7_split_goal_1 : solver_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (i = n_pre + 1) by lia.
  subst i. subst S.
  eapply full_prefix_tables_imply_tables_ready__tables_ready; eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_7 : solver_entail_wit_7.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_7_split_goal_1.
Qed. 

Lemma proof_of_solver_entail_wit_8_split_goal_1 : solver_entail_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold OutputPrefix.
  split; [reflexivity |].
  rewrite Zsublist_nil by lia.
  constructor.
Qed.

Lemma proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_8_split_goal_1.
Qed. 

Lemma proof_of_solver_entail_wit_9_split_goal_1 : solver_entail_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (raw_queries_encode_nth__query_setup
    queries_data raw_queries n_pre i ltac:(lia) PreH12 PreH11) as Hraw.
  destruct Hraw as
    (Hx1 & Hy1 & Hx2 & Hy2 & Hxb & Hx2b & Hyb & Hy2b).
  subst S.
  unfold TablesReady in PreH15.
  destruct PreH15 as (_ & _ & _ & _ & _ & _ & _ & Hsafe).
  apply Hsafe.
  - rewrite Hx1, Hx2. lia.
  - rewrite Hx2. lia.
  - rewrite Hy1, Hy2. lia.
  - rewrite Hy2. lia.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_2 : solver_entail_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst S.
  unfold TablesReady in PreH15.
  tauto.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_3 : solver_entail_wit_9_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst S.
  unfold TablesReady in PreH15.
  tauto.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_4 : solver_entail_wit_9_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst S.
  unfold TablesReady in PreH15.
  tauto.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_5 : solver_entail_wit_9_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst S.
  unfold TablesReady in PreH15.
  tauto.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_6 : solver_entail_wit_9_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst S.
  unfold TablesReady in PreH15.
  tauto.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_7 : solver_entail_wit_9_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  subst S.
  unfold TablesReady in PreH15.
  tauto.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_8 : solver_entail_wit_9_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (raw_queries_encode_nth__query_setup
    queries_data raw_queries n_pre i ltac:(lia) PreH12 PreH11) as Hraw.
  destruct Hraw as
    (_ & _ & _ & Hy2 & _ & _ & _ & Hy2b).
  rewrite Hy2.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_9 : solver_entail_wit_9_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (raw_queries_encode_nth__query_setup
    queries_data raw_queries n_pre i ltac:(lia) PreH12 PreH11) as Hraw.
  destruct Hraw as
    (_ & Hy1 & _ & Hy2 & _ & _ & Hyb & _).
  rewrite Hy1, Hy2.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_10 : solver_entail_wit_9_split_goal_10.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (raw_queries_encode_nth__query_setup
    queries_data raw_queries n_pre i ltac:(lia) PreH12 PreH11) as Hraw.
  destruct Hraw as
    (_ & Hy1 & _ & _ & _ & _ & Hyb & _).
  rewrite Hy1.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_11 : solver_entail_wit_9_split_goal_11.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (raw_queries_encode_nth__query_setup
    queries_data raw_queries n_pre i ltac:(lia) PreH12 PreH11) as Hraw.
  destruct Hraw as
    (_ & _ & Hx2 & _ & _ & Hx2b & _ & _).
  rewrite Hx2.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_12 : solver_entail_wit_9_split_goal_12.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (raw_queries_encode_nth__query_setup
    queries_data raw_queries n_pre i ltac:(lia) PreH12 PreH11) as Hraw.
  destruct Hraw as
    (Hx1 & _ & Hx2 & _ & Hxb & _ & _ & _).
  rewrite Hx1, Hx2.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_13 : solver_entail_wit_9_split_goal_13.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (raw_queries_encode_nth__query_setup
    queries_data raw_queries n_pre i ltac:(lia) PreH12 PreH11) as Hraw.
  destruct Hraw as
    (Hx1 & _ & _ & _ & Hxb & _ & _ & _).
  rewrite Hx1.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_14 : solver_entail_wit_9_split_goal_14.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (raw_queries_encode_nth__query_setup
    queries_data raw_queries n_pre i ltac:(lia) PreH12 PreH11) as Hraw.
  destruct Hraw as (_ & _ & _ & Hy2 & _).
  rewrite (Znth_indep queries_data i __default__Prod__Prod__Prod_Z_Z_Z_Z
    (0, 0, 0, 0)) by lia.
  exact Hy2.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_15 : solver_entail_wit_9_split_goal_15.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (raw_queries_encode_nth__query_setup
    queries_data raw_queries n_pre i ltac:(lia) PreH12 PreH11) as Hraw.
  destruct Hraw as (_ & _ & Hx2 & _).
  rewrite (Znth_indep queries_data i __default__Prod__Prod__Prod_Z_Z_Z_Z
    (0, 0, 0, 0)) by lia.
  exact Hx2.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_16 : solver_entail_wit_9_split_goal_16.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (raw_queries_encode_nth__query_setup
    queries_data raw_queries n_pre i ltac:(lia) PreH12 PreH11) as Hraw.
  destruct Hraw as (_ & Hy1 & _).
  rewrite (Znth_indep queries_data i __default__Prod__Prod__Prod_Z_Z_Z_Z
    (0, 0, 0, 0)) by lia.
  exact Hy1.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_17 : solver_entail_wit_9_split_goal_17.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (raw_queries_encode_nth__query_setup
    queries_data raw_queries n_pre i ltac:(lia) PreH12 PreH11) as Hraw.
  destruct Hraw as (Hx1 & _).
  rewrite (Znth_indep queries_data i __default__Prod__Prod__Prod_Z_Z_Z_Z
    (0, 0, 0, 0)) by lia.
  exact Hx1.
Qed.

Lemma proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_6.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_7.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_8.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_9.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_10.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_11.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_12.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_13.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_14.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_15.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_16.
  - Goal_apply proof_of_solver_entail_wit_9_split_goal_17.
Qed. 

Lemma proof_of_solver_entail_wit_10_split_goal_1 : solver_entail_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply output_prefix_snoc__output_step with (d := __default__Prod__Prod__Prod_Z_Z_Z_Z).
  - exact PreH41.
  - lia.
  - destruct PreH33 as [Htables _].
    pose proof (rectlookup_weighted_flattened_sum__output_step
      matrix_data sum_l_2 row_l_2 col_l_2 n_pre S x1 y1 x2 y2
      PreH12 PreH10 Htables ltac:(lia) PreH29 ltac:(lia) PreH32) as Hweighted.
    subst retval. subst retval_2. subst retval_3.
    remember (Znth i queries_data __default__Prod__Prod__Prod_Z_Z_Z_Z) as query eqn:Hquery.
    destruct query as [[[qx1 qy1] qx2] qy2].
    unfold zquad_1, zquad_2, zquad_3, zquad_4 in *.
    simpl in PreH23, PreH24, PreH25, PreH26.
    subst x1. subst y1. subst x2. subst y2.
    replace (qx1 + 1 - 1) with qx1 in Hweighted by ring.
    replace (qy1 + 1 - 1) with qy1 in Hweighted by ring.
    replace (qx2 + 1 - 1) with qx2 in Hweighted by ring.
    replace (qy2 + 1 - 1) with qy2 in Hweighted by ring.
    replace (qy1 + 1 - 1) with qy1 by ring.
    exact Hweighted.
Qed.

Lemma proof_of_solver_entail_wit_10 : solver_entail_wit_10.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_10_split_goal_1.
Qed. 

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (i = q_pre) by lia.
  subst i.
  Exists result_2.
  split_pure_spatial.
  - sep_apply_l_atomic
      (Int64Array.seg_to_full out_pre 0 q_pre result_2).
    replace (out_pre + 0 * sizeof(INT64)) with out_pre by lia.
    replace (q_pre - 0) with q_pre by lia.
    cancel (Int64Array.full matrix_pre (n_pre * n_pre) matrix_data).
    cancel (IntArray.full queries_pre (4 * q_pre) raw_queries).
    cancel (Int64Array.full out_pre q_pre result_2).
  - dump_pre_spatial.
    eapply output_prefix_complete_spec__final_result; eauto.
Qed. 

Lemma proof_of_solver_partial_solve_wit_21_pure_split_goal_1 : solver_partial_solve_wit_21_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(fail).
  unfold TablesReady, PrefixTables in PreH52.
  destruct PreH52 as [[_ [_ [Hlen _]]] _].
  dump_pre_spatial.
  rewrite <- PreH29. exact Hlen.
Qed.

Lemma proof_of_solver_partial_solve_wit_21_pure_split_goal_2 : solver_partial_solve_wit_21_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(fail).
  unfold TablesReady, PrefixTables in PreH52.
  destruct PreH52 as [[_ [_ [Hlen _]]] _].
  dump_pre_spatial.
  rewrite <- PreH29. exact Hlen.
Qed.

Lemma proof_of_solver_partial_solve_wit_21_pure : solver_partial_solve_wit_21_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_21_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_21_pure_split_goal_2.
Qed. 

Lemma proof_of_solver_partial_solve_wit_22_pure_split_goal_1 : solver_partial_solve_wit_22_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(fail).
  unfold TablesReady, PrefixTables in PreH47.
  destruct PreH47 as [[_ [Hlen _]] _].
  dump_pre_spatial.
  rewrite <- PreH24. exact Hlen.
Qed.

Lemma proof_of_solver_partial_solve_wit_22_pure_split_goal_2 : solver_partial_solve_wit_22_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(fail).
  unfold TablesReady, PrefixTables in PreH47.
  destruct PreH47 as [[_ [Hlen _]] _].
  dump_pre_spatial.
  rewrite <- PreH24. exact Hlen.
Qed.

Lemma proof_of_solver_partial_solve_wit_22_pure : solver_partial_solve_wit_22_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_22_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_22_pure_split_goal_2.
Qed. 

Lemma proof_of_solver_partial_solve_wit_23_pure_split_goal_1 : solver_partial_solve_wit_23_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(fail).
  dump_pre_spatial. vm_compute. easy.
Qed.

Lemma proof_of_solver_partial_solve_wit_23_pure_split_goal_2 : solver_partial_solve_wit_23_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(fail).
  dump_pre_spatial. vm_compute. easy.
Qed.

Lemma proof_of_solver_partial_solve_wit_23_pure_split_goal_3 : solver_partial_solve_wit_23_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(fail).
  unfold TablesReady, PrefixTables in PreH42.
  destruct PreH42 as [[Hlen _] _].
  dump_pre_spatial.
  rewrite <- PreH19. exact Hlen.
Qed.

Lemma proof_of_solver_partial_solve_wit_23_pure_split_goal_4 : solver_partial_solve_wit_23_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(fail).
  unfold TablesReady, PrefixTables in PreH42.
  destruct PreH42 as [[Hlen _] _].
  dump_pre_spatial.
  rewrite <- PreH19. exact Hlen.
Qed.

Lemma proof_of_solver_partial_solve_wit_23_pure : solver_partial_solve_wit_23_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_23_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_23_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_23_pure_split_goal_3.
  - Goal_apply proof_of_solver_partial_solve_wit_23_pure_split_goal_4.
Qed. 

