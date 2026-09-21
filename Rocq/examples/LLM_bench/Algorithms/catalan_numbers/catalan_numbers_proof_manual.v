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
From SimpleC.EE.LLM_bench.Algorithms.catalan_numbers Require Import catalan_numbers_goal.
From SimpleC.EE.LLM_bench.Algorithms.catalan_numbers Require Import catalan_numbers_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.catalan_numbers.catalan_numbers_lib.
Local Open Scope sac.
Local Opaque IntArray.full IntArray.seg IntArray.undef_full IntArray.undef_seg IntArray.mixed_full IntArray.mixed_seg.
Import ListNotations.
Local Open Scope list_scope.

Lemma proof_of_solve_safety_wit_10_split_goal_1 : solve_safety_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst retval retval_2.
  assert (Hsum : 0 <=
      Znth (StackCellIndex n_pre (i - 1) (j + 1)) table 0 +
      Znth (StackCellIndex n_pre i (j - 1)) table 0 <= 2 ^ (2 * i + j)).
  { apply table_add_bound__cell_dp; try lia.
    intros r c Hr Hc Hlt. apply PreH17.
    unfold StackCellIndex in Hlt. lia. }
  pose proof (StackCellBound_int_range__cell_dp i j
    (Znth (StackCellIndex n_pre (i - 1) (j + 1)) table 0 +
     Znth (StackCellIndex n_pre i (j - 1)) table 0)
    ltac:(lia) ltac:(lia) ltac:(repeat split; tauto || lia)) as Hrange.
  dump_pre_spatial.
  unfold StackCellIndex in Hrange.
  repeat rewrite Z.sub_0_r. exact (proj2 Hrange).
Qed.

Lemma proof_of_solve_safety_wit_10_split_goal_2 : solve_safety_wit_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst retval retval_2.
  pose proof (table_add_bound__cell_dp n_pre table i j
    ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(intros r c Hr Hc Hlt; apply PreH17;
      unfold StackCellIndex in Hlt; lia)) as Hsum.
  dump_pre_spatial.
  unfold StackCellIndex in Hsum.
  repeat rewrite Z.sub_0_r. lia.
Qed.

Lemma proof_of_solve_safety_wit_10 : solve_safety_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_safety_wit_10_split_goal_1.
  - Goal_apply proof_of_solve_safety_wit_10_split_goal_2.
Qed.

Lemma proof_of_solve_entail_wit_1 : solve_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (@nil Z).
  replace (0 * (n_pre + 1)) with 0 by ring.
  sep_apply_l_atomic
    (IntArray.undef_full_split_to_undef_seg (&("f")) ((n_pre + 1) * (n_pre + 1)) 64 ltac:(nia)).
  rewrite (IntArray.seg_empty (&("f")) 0 0).
  split_pure_spatial.
  - cancel (IntArray.undef_seg (&("f")) 0 ((n_pre + 1) * (n_pre + 1))).
    cancel (IntArray.undef_seg (&("f")) ((n_pre + 1) * (n_pre + 1)) 64).
  - split_pures; dump_pre_spatial; try lia; try reflexivity.
    + unfold StackTablePrefix, StackCellIndex. intros. nia.
Qed.

Lemma proof_of_solve_entail_wit_2 : solve_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists table_2.
  replace (i * (n_pre + 1) + 0) with (i * (n_pre + 1)) by lia.
  split_pure_spatial.
  - cancel (IntArray.seg (&("f")) 0 (i * (n_pre + 1)) table_2).
    cancel (IntArray.undef_seg (&("f")) (i * (n_pre + 1))
      ((n_pre + 1) * (n_pre + 1))).
    cancel (IntArray.undef_seg (&("f")) ((n_pre + 1) * (n_pre + 1)) 64).
  - split_pures; dump_pre_spatial; try lia; assumption.
Qed.

Lemma proof_of_solve_entail_wit_3_split_goal_1 : solve_entail_wit_3_split_goal_1.
Proof. unfold solve_entail_wit_3_split_goal_1. intros. apply PreH11. assumption. Qed.
Lemma proof_of_solve_entail_wit_3_split_goal_2 : solve_entail_wit_3_split_goal_2.
Proof. LLM_pre_process ltac:(lia || int_auto); auto. Qed.
Lemma proof_of_solve_entail_wit_3_split_goal_3 : solve_entail_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Z.mul_le_mono_nonneg_r i n_pre (n_pre + 1)
    ltac:(lia) ltac:(lia)).
  rewrite Z.mul_add_distr_r. lia.
Qed.
Lemma proof_of_solve_entail_wit_3 : solve_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_3_split_goal_2.
  - Goal_apply proof_of_solve_entail_wit_3_split_goal_3.
Qed.

Lemma proof_of_solve_entail_wit_4_split_goal_1 : solve_entail_wit_4_split_goal_1.
Proof. unfold solve_entail_wit_4_split_goal_1. intros. apply PreH11. assumption. Qed.
Lemma proof_of_solve_entail_wit_4_split_goal_2 : solve_entail_wit_4_split_goal_2.
Proof. LLM_pre_process ltac:(lia || int_auto); auto. Qed.
Lemma proof_of_solve_entail_wit_4_split_goal_3 : solve_entail_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (Z.mul_le_mono_nonneg_r i n_pre (n_pre + 1)
    ltac:(lia) ltac:(lia)).
  rewrite Z.mul_add_distr_r. lia.
Qed.
Lemma proof_of_solve_entail_wit_4 : solve_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solve_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_solve_entail_wit_4_split_goal_2.
  - Goal_apply proof_of_solve_entail_wit_4_split_goal_3.
Qed.

Lemma proof_of_solve_entail_wit_5_1 : solve_entail_wit_5_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst i. repeat rewrite Z.mul_0_l in *. repeat rewrite Z.add_0_l in *.
  prop_apply (IntArray.seg_Zlength (&("f")) 0 (j + 1) (table_2 ++ [1])).
  Intros_p Hlen.
  rewrite Zlength_app_cons in Hlen.
  assert (Hprefix : StackTablePrefix n_pre (table_2 ++ [1]) (j + 1)).
  { apply StackTablePrefix_zero_row_extend__cell_dp; try lia; assumption. }
  pose proof (table_snoc_pointwise
    (fun r c v => 0 <= v <= 2 ^ (2 * r + c))
    n_pre table_2 0 j 1 ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(intros r c Hr Hc Hlt; apply PreH11;
      unfold StackCellIndex in Hlt; lia)
    ltac:(pose proof (StackCellBound_zero_row__cell_dp j ltac:(lia)); tauto))
    as Hbounds.
  Exists (table_2 ++ [1]).
  split_pure_spatial.
  - cancel (IntArray.seg (&("f")) 0 (j + 1) (table_2 ++ [1])).
    cancel (IntArray.undef_seg (&("f")) (j + 1) ((n_pre + 1) * (n_pre + 1))).
    cancel (IntArray.undef_seg (&("f")) ((n_pre + 1) * (n_pre + 1)) 64).
  - split_pures; dump_pre_spatial; try lia; try assumption.
    intros r c Hrc. apply Hbounds; unfold StackCellIndex; lia.
Qed.

Lemma proof_of_solve_entail_wit_5_2 : solve_entail_wit_5_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst j retval_2.
  repeat rewrite Z.add_0_r in *.
  repeat rewrite Z.sub_0_r in *.
  repeat rewrite Z.add_0_l in *.
  set (v := Znth (StackCellIndex n_pre (i - 1) 1) table_2 0).
  change (Znth ((i - 1) * (n_pre + 1) + 1) table_2 0) with v in *.
  prop_apply (IntArray.seg_Zlength (&("f")) 0 (i * (n_pre + 1) + 1) (table_2 ++ [v])).
  Intros_p Hlen.
  rewrite Zlength_app_cons in Hlen.
  assert (Hprefix : StackTablePrefix n_pre (table_2 ++ [v]) (i * (n_pre + 1) + 1)).
  { apply StackTablePrefix_copy_boundary_extend__cell_dp; try lia; assumption. }
  assert (Hsrc : 0 <= v <= 2 ^ (2 * (i - 1) + 1)).
  { unfold v, StackCellIndex. apply PreH13. nia. }
  pose proof (StackCellBound_copy_boundary__cell_dp i v ltac:(lia)
    ltac:(repeat split; tauto || lia)) as [_ [_ Hv]].
  pose proof (table_snoc_pointwise
    (fun r c v => 0 <= v <= 2 ^ (2 * r + c))
    n_pre table_2 i 0 v ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(intros r c Hr Hc Hlt; apply PreH13;
      unfold StackCellIndex in Hlt; lia) Hv) as Hbounds.
  Exists (table_2 ++ [v]).
  split_pure_spatial.
  - cancel (IntArray.seg (&("f")) 0 (i * (n_pre + 1) + 1) (table_2 ++ [v])).
    cancel (IntArray.undef_seg (&("f")) (i * (n_pre + 1) + 1) ((n_pre + 1) * (n_pre + 1))).
    cancel (IntArray.undef_seg (&("f")) ((n_pre + 1) * (n_pre + 1)) 64).
  - split_pures; dump_pre_spatial; try lia; try assumption.
    intros r c Hrc. apply Hbounds; unfold StackCellIndex; lia.
Qed.

Lemma proof_of_solve_entail_wit_5_3 : solve_entail_wit_5_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  subst retval_2 retval_3.
  repeat rewrite Z.sub_0_r in *.
  set (v := Znth (StackCellIndex n_pre (i - 1) (j + 1)) table_2 0 +
            Znth (StackCellIndex n_pre i (j - 1)) table_2 0).
  change (Znth ((i - 1) * (n_pre + 1) + (j + 1)) table_2 0 +
          Znth (i * (n_pre + 1) + (j - 1)) table_2 0) with v in *.
  prop_apply (IntArray.seg_Zlength (&("f")) 0 (i * (n_pre + 1) + j + 1) (table_2 ++ [v])).
  Intros_p Hlen.
  rewrite Zlength_app_cons in Hlen.
  assert (Hprefix : StackTablePrefix n_pre (table_2 ++ [v]) (i * (n_pre + 1) + (j + 1))).
  { apply StackTablePrefix_add_step_extend__cell_dp; try lia; assumption. }
  assert (Hv : 0 <= v <= 2 ^ (2 * i + j)).
  { unfold v. apply table_add_bound__cell_dp; try lia.
    intros r c Hr Hc Hlt. apply PreH17.
    unfold StackCellIndex in Hlt. lia. }
  pose proof (table_snoc_pointwise
    (fun r c v => 0 <= v <= 2 ^ (2 * r + c))
    n_pre table_2 i j v ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(intros r c Hr Hc Hlt; apply PreH17;
      unfold StackCellIndex in Hlt; lia) Hv) as Hbounds.
  Exists (table_2 ++ [v]).
  replace (i * (n_pre + 1) + j + 1) with (i * (n_pre + 1) + (j + 1)) by lia.
  split_pure_spatial.
  - cancel (IntArray.seg (&("f")) 0 (i * (n_pre + 1) + (j + 1)) (table_2 ++ [v])).
    cancel (IntArray.undef_seg (&("f")) (i * (n_pre + 1) + (j + 1)) ((n_pre + 1) * (n_pre + 1))).
    cancel (IntArray.undef_seg (&("f")) ((n_pre + 1) * (n_pre + 1)) 64).
  - split_pures; dump_pre_spatial; try lia; try assumption.
    intros r c Hrc. apply Hbounds; unfold StackCellIndex; lia.
Qed.

Lemma proof_of_solve_entail_wit_6 : solve_entail_wit_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (j = n_pre + 1) by lia. subst j.
  replace (i * (n_pre + 1) + (n_pre + 1))
    with ((i + 1) * (n_pre + 1)) in * by ring.
  Exists table_2.
  split_pure_spatial.
  - cancel (IntArray.seg (&("f")) 0 ((i + 1) * (n_pre + 1)) table_2).
    cancel (IntArray.undef_seg (&("f")) ((i + 1) * (n_pre + 1)) ((n_pre + 1) * (n_pre + 1))).
    cancel (IntArray.undef_seg (&("f")) ((n_pre + 1) * (n_pre + 1)) 64).
  - split_pures; dump_pre_spatial; try lia; assumption.
Qed.

Lemma proof_of_solve_entail_wit_7 : solve_entail_wit_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace i with (n_pre + 1) in * by lia.
  Exists table_2.
  split_pure_spatial.
  - rewrite IntArray.undef_seg_empty.
    sep_apply (IntArray.seg_to_full (&("f")) 0 ((n_pre + 1) * (n_pre + 1)) table_2).
    replace ((&("f")) + 0 * sizeof (INT)) with (&("f")) by lia.
    replace ((n_pre + 1) * (n_pre + 1) - 0)
      with ((n_pre + 1) * (n_pre + 1)) by lia.
    cancel (IntArray.full (&("f")) ((n_pre + 1) * (n_pre + 1)) table_2).
    cancel (IntArray.undef_seg (&("f")) ((n_pre + 1) * (n_pre + 1)) 64).
  - split_pures; dump_pre_spatial; try nia.
    apply StackOperationWordCount_to_output; [lia |].
    apply StackTablePrefix_result; assumption.
Qed.

Lemma proof_of_solve_entail_wit_8_split_goal_1 : solve_entail_wit_8_split_goal_1.
Proof. LLM_pre_process ltac:(lia || int_auto). rewrite Z.add_0_r. dump_pre_spatial. assumption. Qed.
Lemma proof_of_solve_entail_wit_8_split_goal_spatial : solve_entail_wit_8_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply (IntArray.full_to_undef_full (&("f")) ((n_pre + 1) * (n_pre + 1)) table).
  sep_apply (IntArray.undef_full_to_undef_seg (&("f")) ((n_pre + 1) * (n_pre + 1))).
  sep_apply (IntArray.undef_seg_merge_to_undef_full (&("f")) 0 ((n_pre + 1) * (n_pre + 1)) 64 ltac:(nia)).
  replace ((&("f")) + 0 * sizeof (INT)) with (&("f")) by lia.
  replace (64 - 0) with 64 by lia. entailer!.
Qed.
Lemma proof_of_solve_entail_wit_8 : solve_entail_wit_8.
Proof.
  unfold solve_entail_wit_8; left; intros. subst retval. rewrite Z.add_0_r.
  sep_apply (IntArray.full_to_undef_full (&("f")) ((n_pre + 1) * (n_pre + 1)) table).
  sep_apply (IntArray.undef_full_to_undef_seg (&("f")) ((n_pre + 1) * (n_pre + 1))).
  sep_apply (IntArray.undef_seg_merge_to_undef_full (&("f")) 0 ((n_pre + 1) * (n_pre + 1)) 64 ltac:(nia)).
  replace ((&("f")) + 0 * sizeof (INT)) with (&("f")) by lia.
  replace (64 - 0) with 64 by lia. entailer!.
Qed.
