Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.LLM_bench.Engineering.string Require Import strcmp_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.StdLib.string_lib.
Local Open Scope sac.

Lemma proof_of_strcmp_safety_wit_4 : strcmp_safety_wit_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  match goal with
  | Hvalid : valid_string str1,
    Hlo : 0 <= i,
    Hhi : i <= string_length str1 |- _ =>
      pose proof (c_string_char_bound str1 i Hvalid ltac:(lia)) as Hbound1
  end.
  match goal with
  | Hvalid : valid_string str2,
    Hlo : 0 <= i,
    Hhi : i <= string_length str2 |- _ =>
      pose proof (c_string_char_bound str2 i Hvalid ltac:(lia)) as Hbound2
  end.
  split_pures.
  all: dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_strcmp_safety_wit_5 : strcmp_safety_wit_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  match goal with
  | Hvalid : valid_string str1,
    Hlo : 0 <= i,
    Hhi : i <= string_length str1 |- _ =>
      pose proof (c_string_char_bound str1 i Hvalid ltac:(lia)) as Hbound1
  end.
  match goal with
  | Hvalid : valid_string str2,
    Hlo : 0 <= i,
    Hhi : i <= string_length str2 |- _ =>
      pose proof (c_string_char_bound str2 i Hvalid ltac:(lia)) as Hbound2
  end.
  split_pures.
  all: dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_strcmp_entail_wit_1 : strcmp_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (0 <= string_length str1) by (unfold string_length; apply Zlength_nonneg).
  assert (0 <= string_length str2) by (unfold string_length; apply Zlength_nonneg).
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_strcmp_entail_wit_2 : strcmp_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  match goal with
  | Hvalid : valid_string str1,
    Hlo : 0 <= i,
    Hhi : i <= string_length str1,
    Hnz : Znth i (c_string str1) 0 <> 0 |- _ =>
      pose proof (c_string_nonzero_lt_length str1 i Hvalid ltac:(lia) Hnz)
  end.
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
    + match goal with
    | Hvalid : valid_string str2,
      Hlo : 0 <= i,
      Hhi : i <= string_length str2,
      Heq : Znth i (c_string str1) 0 = Znth i (c_string str2) 0,
      Hnz : Znth i (c_string str1) 0 <> 0 |- _ =>
        pose proof (c_string_nonzero_lt_length str2 i Hvalid ltac:(lia)
                      ltac:(rewrite <- Heq; exact Hnz))
    end.
    auto with zarith.
    + apply prefix_eq_extend; auto.
Qed.

Lemma proof_of_strcmp_return_wit_1 : strcmp_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (strcmp_result str1 str2
            (Znth i (c_string str1) 0 - Znth i (c_string str2) 0)).
  { exists i. repeat split; auto with zarith. }
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial; exact H.
Qed.

Lemma proof_of_strcmp_return_wit_2 : strcmp_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (strcmp_result str1 str2
            (Znth i (c_string str1) 0 - Znth i (c_string str2) 0)).
  { exists i. repeat split; auto with zarith. }
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial; exact H.
Qed.

Lemma proof_of_strncmp_safety_wit_8 : strncmp_safety_wit_8.
Proof.
  LLM_pre_process ltac:(int_auto).
  match goal with
  | Hvalid : valid_string str1,
    Hlo : 0 <= i,
    Hhi : i <= string_length str1 |- _ =>
      pose proof (c_string_char_bound str1 i Hvalid ltac:(lia)) as Hbound1
  end.
  match goal with
  | Hvalid : valid_string str2,
    Hlo : 0 <= i,
    Hhi : i <= string_length str2 |- _ =>
      pose proof (c_string_char_bound str2 i Hvalid ltac:(lia)) as Hbound2
  end.
  split_pures.
  all: dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_strncmp_safety_wit_9 : strncmp_safety_wit_9.
Proof.
  LLM_pre_process ltac:(int_auto).
  match goal with
  | Hvalid : valid_string str1,
    Hlo : 0 <= i,
    Hhi : i <= string_length str1 |- _ =>
      pose proof (c_string_char_bound str1 i Hvalid ltac:(lia)) as Hbound1
  end.
  match goal with
  | Hvalid : valid_string str2,
    Hlo : 0 <= i,
    Hhi : i <= string_length str2 |- _ =>
      pose proof (c_string_char_bound str2 i Hvalid ltac:(lia)) as Hbound2
  end.
  split_pures.
  all: dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_strncmp_entail_wit_1 : strncmp_entail_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (0 <= string_length str1) by (unfold string_length; apply Zlength_nonneg).
  assert (0 <= string_length str2) by (unfold string_length; apply Zlength_nonneg).
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
Qed.

Lemma proof_of_strncmp_entail_wit_2 : strncmp_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  match goal with
  | Hvalid : valid_string str1,
    Hlo : 0 <= i,
    Hhi : i <= string_length str1,
    Hnz : Znth i (c_string str1) 0 <> 0 |- _ =>
      pose proof (c_string_nonzero_lt_length str1 i Hvalid ltac:(lia) Hnz)
  end.
  split_pure_spatial.
  - cancel.
  - split_pures.
    all: dump_pre_spatial; try lia; try assumption.
    + match goal with
    | Hvalid : valid_string str2,
      Hlo : 0 <= i,
      Hhi : i <= string_length str2,
      Heq : Znth i (c_string str1) 0 = Znth i (c_string str2) 0,
      Hnz : Znth i (c_string str1) 0 <> 0 |- _ =>
        pose proof (c_string_nonzero_lt_length str2 i Hvalid ltac:(lia)
                      ltac:(rewrite <- Heq; exact Hnz))
    end.
    auto with zarith.
    + apply prefix_eq_extend; auto.
Qed.

Lemma proof_of_strncmp_return_wit_1 : strncmp_return_wit_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (strncmp_result str1 str2 n_pre
            (Znth i (c_string str1) 0 - Znth i (c_string str2) 0)).
  { exists i. repeat split; auto with zarith. }
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial; exact H.
Qed.

Lemma proof_of_strncmp_return_wit_2 : strncmp_return_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (strncmp_result str1 str2 n_pre
            (Znth i (c_string str1) 0 - Znth i (c_string str2) 0)).
  { exists i. repeat split; auto with zarith. }
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial; exact H.
Qed.

Lemma proof_of_strncmp_return_wit_3 : strncmp_return_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  assert (strncmp_result str1 str2 n_pre 0).
  { exists i. repeat split; auto with zarith. }
  split_pure_spatial.
  - cancel.
  - dump_pre_spatial; exact H.
Qed.
