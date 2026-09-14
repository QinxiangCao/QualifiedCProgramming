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
From SimpleC.EE.Applications_human.hashtable Require Import hashtbl_goal.
From SimpleC.EE.Applications_human.hashtable Require Import hashtbl_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.Applications_human.hashtable.hashtbl_lib.
Local Open Scope sac.

Lemma proof_of_create_bucks_entail_wit_1_split_goal_1 : create_bucks_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(unfold sublist, zeros; reflexivity).
Qed.

Lemma proof_of_create_bucks_entail_wit_1 : create_bucks_entail_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_create_bucks_entail_wit_1_split_goal_1.
Qed.

Lemma proof_of_create_bucks_entail_wit_2_split_goal_1 : create_bucks_entail_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_create_bucks_entail_wit_2 : create_bucks_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply (PtrArray.full_Zlength bucks_base_2 211
    (replace_Znth i 0 content_2)).
  Intros_p Hlen.
  Exists (replace_Znth i 0 content_2) bucks_base_2.
  split_pure_spatial.
  - cancel (PtrArray.full bucks_base_2 211
      (replace_Znth i 0 content_2)).
    cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
    apply sublist_replace_Znth_zero_succ__create_bucks.
    + assert (Hcontent_len : Zlength content_2 = 211).
      { rewrite <- Hlen.
        symmetry.
        apply Zlength_replace_Znth. }
      lia.
    + exact PreH5.
Qed.

Lemma proof_of_create_bucks_return_wit_1_split_goal_1 : create_bucks_return_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_create_bucks_return_wit_1 : create_bucks_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi : i = 211) by lia.
  subst i.
  prop_apply (PtrArray.full_Zlength bucks_base_2 211 content).
  Intros_p Hlen.
  assert (Hcontent : content = zeros 211).
  { apply (sublist_full_zeros_eq__create_bucks content 211).
    - exact Hlen.
    - exact PreH5. }
  rewrite Hcontent.
  Exists bucks_base_2.
  split_pure_spatial.
  - cancel (PtrArray.full bucks_base_2 211 (zeros 211)).
    cancel.
  - dump_pre_spatial.
    exact PreH4.
Qed.

