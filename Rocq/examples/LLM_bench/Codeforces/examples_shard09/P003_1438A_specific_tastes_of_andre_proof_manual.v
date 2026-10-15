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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P003_1438A_specific_tastes_of_andre_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P003_1438A_specific_tastes_of_andre_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P003_1438A_specific_tastes_of_andre_lib.
Local Open Scope sac.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_app, Zlength_cons, Zlength_nil, PreH6.
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
  subst i.
  assert (HZnth_Forall :
    forall xs : list Z,
      (forall k : Z, 0 <= k < Zlength xs -> Znth k xs 0 = 1) ->
      Forall (fun x : Z => x = 1) xs).
  {
    intros xs Hxs.
    apply (proj2 (Forall_forall (fun x : Z => x = 1) xs)).
    intros x Hinx.
    destruct (In_nth_error xs x Hinx) as [j Hj].
    pose proof (nth_error_nth xs j 0 Hj) as Hnth.
    assert (Hjlen : (j < length xs)%nat).
    {
      apply (proj1 (nth_error_Some xs j)).
      rewrite Hj. discriminate.
    }
    specialize (Hxs (Z.of_nat j)).
    assert (HjZ : 0 <= Z.of_nat j < Zlength xs).
    {
      rewrite Zlength_correct.
      lia.
    }
    specialize (Hxs HjZ).
    unfold Znth in Hxs.
    rewrite Nat2Z.id in Hxs.
    congruence.
  }
  assert (Hsum_ones :
    forall xs : list Z,
      Forall (fun x : Z => x = 1) xs ->
      fold_right Z.add 0 xs = Zlength xs).
  {
    intros xs Hxs.
    induction Hxs.
    - rewrite Zlength_nil. reflexivity.
    - simpl. rewrite Zlength_cons. subst x. lia.
  }
  assert (Hones : Forall (fun x : Z => x = 1) written).
  {
    apply HZnth_Forall.
    exact PreH7.
  }
  assert (Hspec : Spec n_pre written).
  {
    unfold Spec, Perfect.
    split.
    - exact Hi.
    - split.
      + rewrite Forall_forall in Hones |- *.
        intros x Hinx.
        specialize (Hones x Hinx).
        subst x. lia.
      + intros l r Hlr.
        destruct Hlr as [[Hl Hlt] Hr].
        assert (Hsubbounds : 0 <= l <= r /\ r <= Zlength written).
        { rewrite Hi. lia. }
        assert (Hsubones :
          Forall (fun x : Z => x = 1) (sublist l r written)).
        {
          apply HZnth_Forall.
          intros k Hk.
          rewrite Zlength_sublist in Hk by exact Hsubbounds.
          rewrite Znth_sublist by lia.
          apply PreH7.
          lia.
        }
        pose proof (Hsum_ones _ Hsubones) as Hsum.
        rewrite Zlength_sublist in Hsum by exact Hsubbounds.
        exists 1.
        lia.
  }
  Exists written.
  split_pure_spatial.
  - rewrite Hi.
    rewrite IntArray.undef_seg_empty.
    sep_apply_l_atomic (IntArray.seg_to_full out_pre 0 n_pre written).
    replace (out_pre + 0 * sizeof(INT)) with out_pre by lia.
    replace (n_pre - 0) with n_pre by lia.
    cancel (IntArray.full out_pre n_pre written).
  - dump_pre_spatial.
    exact Hspec.
Qed.
