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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P002_1382A_common_subsequence_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P002_1382A_common_subsequence_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P002_1382A_common_subsequence_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_spatial : solver_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  simpl.
  rewrite Z.add_0_r.
  cancel (CharArray.undef_full &( "seen") 1001).
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists (repeat_Z 0 1001).
  simpl.
  rewrite Z.add_0_r.
  split_pure_spatial.
  - cancel (CharArray.full &( "seen") 1001 (repeat_Z 0 1001)).
    cancel (IntArray.full a_pre n_pre left).
    cancel (IntArray.full b_pre m_pre right).
  - split_pures.
    all: dump_pre_spatial.
    all: try firstorder; try lia.
    + left. unfold repeat_Z. apply Znth_repeat.
    + unfold repeat_Z in H0.
      rewrite Znth_repeat in H0.
      lia.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_replace_Znth.
  exact PreH13.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_2 : solver_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  firstorder lia.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_3 : solver_entail_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  firstorder lia.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_4 : solver_entail_wit_4_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_5 : solver_entail_wit_4_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH9.
  assumption.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_6 : solver_entail_wit_4_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH8.
  assumption.
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_6.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hmember : forall (x : Z) (xs l : list Z),
      ListLib.General.IndexedElements.is_subsequence (x :: xs) l ->
      exists k, 0 <= k < Zlength l /\ Znth k l 0 = x).
  {
    intros x xs l. revert x xs.
    induction l as [| a l IH]; intros x xs Hsub.
    - simpl in Hsub. contradiction.
    - simpl in Hsub. destruct Hsub as [Htail | [Hx Htail]].
      + specialize (IH x xs Htail) as [k [[Hk0 Hklen] Hval]].
        exists (k + 1). split.
        * rewrite Zlength_cons. lia.
        * rewrite Znth_cons by lia.
          replace (k + 1 - 1) with k by lia. exact Hval.
      + subst x. exists 0. split.
        * rewrite Zlength_cons. pose proof (Zlength_nonneg l). lia.
        * apply Znth0_cons.
  }
  Left.
  Exists None.
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial.
      unfold Spec. left. split; [reflexivity |].
      intros [c [Hnonempty [Hleft Hright]]].
      destruct c as [| x xs]; [contradiction |].
      destruct (Hmember x xs left Hleft) as [kl [[Hkl0 Hkln] Hkl]].
      destruct (Hmember x xs right Hright) as [kr [[Hkr0 Hkrn] Hkr]].
      specialize (PreH14 kl ltac:(lia)).
      specialize (PreH16 kr ltac:(lia)).
      rewrite Hkl in PreH14.
      rewrite Hkr in PreH16.
      lia.
    + dump_pre_spatial. reflexivity.
    + dump_pre_spatial. reflexivity.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hsingle : forall (x : Z) (l : list Z) (k : Z),
      0 <= k < Zlength l -> Znth k l 0 = x ->
      ListLib.General.IndexedElements.is_subsequence (x :: nil) l).
  {
    intros x l. induction l as [| a l IH]; intros k Hrange Hval.
    - rewrite Zlength_nil in Hrange. lia.
    - simpl. destruct (Z.eq_dec k 0) as [-> | Hk].
      + right. split.
        * rewrite Znth0_cons in Hval. symmetry. exact Hval.
        * destruct l; simpl; trivial.
      + left. apply (IH (k - 1)).
        * rewrite Zlength_cons in Hrange. split; lia.
        * rewrite Znth_cons in Hval by lia. exact Hval.
  }
  assert (Hxrange : 0 <= Znth j right 0 < 1001).
  { specialize (PreH10 j ltac:(lia)). lia. }
  specialize (PreH14 (Znth j right 0) Hxrange).
  assert (Hseen : Znth (Znth j right 0) seen_l 0 = 1) by lia.
  destruct (PreH16 (Znth j right 0) ltac:(tauto))
    as [kl [[Hkl0 Hkln] Hkl]].
  Right.
  Exists (Some (Znth j right 0 :: nil)).
  split_pure_spatial.
  - cancel.
  - split_pures.
    + dump_pre_spatial.
      unfold Spec. right. exists (Znth j right 0 :: nil). split; [reflexivity |].
      unfold MaxMin.min_object_of_subset. split.
      * unfold CommonNonempty. split; [discriminate |]. split.
        -- apply (Hsingle (Znth j right 0) left kl); [lia | exact Hkl].
        -- apply (Hsingle (Znth j right 0) right j); [lia | reflexivity].
      * intros c Hcommon. unfold CommonNonempty in Hcommon.
        destruct Hcommon as [Hnonempty _].
        destruct c as [| y ys]; [contradiction |].
        rewrite !Zlength_cons, Zlength_nil.
        pose proof (Zlength_nonneg ys). lia.
    + dump_pre_spatial. reflexivity.
Qed.
