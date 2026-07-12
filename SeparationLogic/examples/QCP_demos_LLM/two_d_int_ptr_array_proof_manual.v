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
From SimpleC.EE.QCP_demos_LLM Require Import two_d_int_ptr_array_goal.
From SimpleC.EE.QCP_demos_LLM Require Import two_d_int_ptr_array_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_max_fill_safety_wit_6_split_goal_1 : max_fill_safety_wit_6_split_goal_1.
Proof. Abort.

Lemma proof_of_max_fill_safety_wit_6_split_goal_2 : max_fill_safety_wit_6_split_goal_2.
Proof. Abort.

Lemma proof_of_max_fill_safety_wit_6 : max_fill_safety_wit_6.
Proof.
  pre_process_default; try entailer!.
  all: try match goal with
  | Hlen : forall r : Z, _ -> Zlength (Znth r ?rs ?d) = ?m
    |- Zlength (Znth ?r ?rs ?d2) = ?m =>
      rewrite (Znth_indep rs r d2 d) by lia; apply Hlen; lia
  end.
  all: try match goal with
  | Hrows : Zlength ?rows = ?n
    |- context[Znth ?c (Znth ?r ?rows nil) 0] =>
      rewrite (Znth_indep rows r nil __default__List_Z) by lia
  end.
  all: try match goal with
  | Hcell : forall r c : Z, _ -> _
    |- context[Znth ?c (Znth ?r ?rs ?d) 0] =>
      pose proof (Hcell r c ltac:(repeat split; lia))
  end.
  all: try match goal with
  | |- context[Z.quot (?s - 1) ?cap] =>
      assert (0 <= Z.quot (s - 1) cap <= s - 1) by
        (split; [apply Z.quot_pos; lia | apply Z.quot_le_upper_bound; nia])
  end.
  all: try lia; try nia.
Qed.
Lemma proof_of_max_fill_safety_wit_8_split_goal_1 : max_fill_safety_wit_8_split_goal_1.
Proof. Abort.

Lemma proof_of_max_fill_safety_wit_8_split_goal_2 : max_fill_safety_wit_8_split_goal_2.
Proof. Abort.

Lemma proof_of_max_fill_safety_wit_8 : max_fill_safety_wit_8.
Proof.
  pre_process_default; try entailer!.
  all: try match goal with
  | Hlen : forall r : Z, _ -> Zlength (Znth r ?rs ?d) = ?m
    |- Zlength (Znth ?r ?rs ?d2) = ?m =>
      rewrite (Znth_indep rs r d2 d) by lia; apply Hlen; lia
  end.
  all: try match goal with
  | Hrows : Zlength ?rows = ?n
    |- context[Znth ?c (Znth ?r ?rows nil) 0] =>
      rewrite (Znth_indep rows r nil __default__List_Z) by lia
  end.
  all: try match goal with
  | Hcell : forall r c : Z, _ -> _
    |- context[Znth ?c (Znth ?r ?rs ?d) 0] =>
      pose proof (Hcell r c ltac:(repeat split; lia))
  end.
  all: try match goal with
  | |- context[Z.quot (?s - 1) ?cap] =>
      assert (0 <= Z.quot (s - 1) cap <= s - 1) by
        (split; [apply Z.quot_pos; lia | apply Z.quot_le_upper_bound; nia])
  end.
  all: try lia; try nia.
Qed.
Lemma proof_of_max_fill_safety_wit_9_split_goal_1 : max_fill_safety_wit_9_split_goal_1.
Proof. Abort.

Lemma proof_of_max_fill_safety_wit_9_split_goal_2 : max_fill_safety_wit_9_split_goal_2.
Proof. Abort.

Lemma proof_of_max_fill_safety_wit_9 : max_fill_safety_wit_9.
Proof.
  pre_process_default; try entailer!.
  all: try match goal with
  | Hlen : forall r : Z, _ -> Zlength (Znth r ?rs ?d) = ?m
    |- Zlength (Znth ?r ?rs ?d2) = ?m =>
      rewrite (Znth_indep rs r d2 d) by lia; apply Hlen; lia
  end.
  all: try match goal with
  | Hrows : Zlength ?rows = ?n
    |- context[Znth ?c (Znth ?r ?rows nil) 0] =>
      rewrite (Znth_indep rows r nil __default__List_Z) by lia
  end.
  all: try match goal with
  | Hcell : forall r c : Z, _ -> _
    |- context[Znth ?c (Znth ?r ?rs ?d) 0] =>
      pose proof (Hcell r c ltac:(repeat split; lia))
  end.
  all: try match goal with
  | |- context[Z.quot (?s - 1) ?cap] =>
      assert (0 <= Z.quot (s - 1) cap <= s - 1) by
        (split; [apply Z.quot_pos; lia | apply Z.quot_le_upper_bound; nia])
  end.
  all: try lia; try nia.
Qed.
Lemma proof_of_max_fill_entail_wit_1_split_goal_1 : max_fill_entail_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_max_fill_entail_wit_1 : max_fill_entail_wit_1.
Proof.
  pre_process_default; try entailer!.
  all: try match goal with
  | Hlen : forall r : Z, _ -> Zlength (Znth r ?rs ?d) = ?m
    |- Zlength (Znth ?r ?rs ?d2) = ?m =>
      rewrite (Znth_indep rs r d2 d) by lia; apply Hlen; lia
  end.
  all: try match goal with
  | Hrows : Zlength ?rows = ?n
    |- context[Znth ?c (Znth ?r ?rows nil) 0] =>
      rewrite (Znth_indep rows r nil __default__List_Z) by lia
  end.
  all: try match goal with
  | Hcell : forall r c : Z, _ -> _
    |- context[Znth ?c (Znth ?r ?rs ?d) 0] =>
      pose proof (Hcell r c ltac:(repeat split; lia))
  end.
  all: try match goal with
  | |- context[Z.quot (?s - 1) ?cap] =>
      assert (0 <= Z.quot (s - 1) cap <= s - 1) by
        (split; [apply Z.quot_pos; lia | apply Z.quot_le_upper_bound; nia])
  end.
  all: try lia; try nia.
Qed.
Lemma proof_of_max_fill_entail_wit_2_split_goal_1 : max_fill_entail_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_max_fill_entail_wit_2_split_goal_2 : max_fill_entail_wit_2_split_goal_2.
Proof. Abort.

Lemma proof_of_max_fill_entail_wit_2_split_goal_spatial : max_fill_entail_wit_2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_max_fill_entail_wit_2 : max_fill_entail_wit_2.
Proof.
  pre_process_default.
  sep_apply_l_atomic (IntPtrArray2.full_split_to_missing_i
    grid_pre i grid_rows_pre rows).
  - dump_pre_spatial.
    lia.
  - Intros row_ptr.
    Exists row_ptr.
    rewrite (Znth_indep rows i nil __default__List_Z) by lia.
    unfold StorePtrAsElement.storeA.
    change (IntPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth i rows __default__List_Z))
      (Znth i rows __default__List_Z)) with
      (IntArray.full row_ptr (Zlength (Znth i rows __default__List_Z))
        (Znth i rows __default__List_Z)).
    entailer!.
Qed.

Lemma proof_of_max_fill_entail_wit_3_split_goal_1 : max_fill_entail_wit_3_split_goal_1.
Proof. Abort.

Lemma proof_of_max_fill_entail_wit_3 : max_fill_entail_wit_3.
Proof.
  pre_process_default.
  Exists row_ptr_2.
  entailer!.
Qed.
Lemma proof_of_max_fill_entail_wit_4_split_goal_1 : max_fill_entail_wit_4_split_goal_1.
Proof. Abort.

Lemma proof_of_max_fill_entail_wit_4_split_goal_2 : max_fill_entail_wit_4_split_goal_2.
Proof. Abort.

Lemma proof_of_max_fill_entail_wit_4_split_goal_3 : max_fill_entail_wit_4_split_goal_3.
Proof. Abort.

Lemma proof_of_max_fill_entail_wit_4_split_goal_4 : max_fill_entail_wit_4_split_goal_4.
Proof. Abort.

Lemma proof_of_max_fill_entail_wit_4 : max_fill_entail_wit_4.
Proof.
  pre_process_default.
  rewrite (Znth_indep rows i nil __default__List_Z) by lia.
  pose proof (PreH18 i j ltac:(repeat split; lia)).
  Exists row_ptr_2.
  entailer!.
Qed.
Lemma proof_of_max_fill_entail_wit_5_split_goal_1 : max_fill_entail_wit_5_split_goal_1.
Proof. Abort.

Lemma proof_of_max_fill_entail_wit_5_split_goal_spatial : max_fill_entail_wit_5_split_goal_spatial.
Proof. Abort.

Lemma proof_of_max_fill_entail_wit_5 : max_fill_entail_wit_5.
Proof.
  pre_process_default.
  rewrite (Znth_indep rows i nil __default__List_Z) by lia.
  pose proof (IntPtrArray2.missing_i_merge_to_full
    grid_pre i grid_rows_pre row_ptr rows
    (Znth i rows __default__List_Z)) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  rewrite sizeof_ptr.
  change (IntPtrArray2.ElemArray.full row_ptr
    (Zlength (Znth i rows __default__List_Z))
    (Znth i rows __default__List_Z)) with
    (IntArray.full row_ptr (Zlength (Znth i rows __default__List_Z))
      (Znth i rows __default__List_Z)) in Hmerge.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  entailer!.
Qed.
Lemma proof_of_max_fill_entail_wit_6_1_split_goal_1 : max_fill_entail_wit_6_1_split_goal_1.
Proof. Abort.

Lemma proof_of_max_fill_entail_wit_6_1_split_goal_2 : max_fill_entail_wit_6_1_split_goal_2.
Proof. Abort.

Lemma proof_of_max_fill_entail_wit_6_1_split_goal_3 : max_fill_entail_wit_6_1_split_goal_3.
Proof. Abort.

Lemma proof_of_max_fill_entail_wit_6_1 : max_fill_entail_wit_6_1.
Proof.
  pre_process_default; try entailer!.
  all: try match goal with
  | Hlen : forall r : Z, _ -> Zlength (Znth r ?rs ?d) = ?m
    |- Zlength (Znth ?r ?rs ?d2) = ?m =>
      rewrite (Znth_indep rs r d2 d) by lia; apply Hlen; lia
  end.
  all: try match goal with
  | Hrows : Zlength ?rows = ?n
    |- context[Znth ?c (Znth ?r ?rows nil) 0] =>
      rewrite (Znth_indep rows r nil __default__List_Z) by lia
  end.
  all: try match goal with
  | Hcell : forall r c : Z, _ -> _
    |- context[Znth ?c (Znth ?r ?rs ?d) 0] =>
      pose proof (Hcell r c ltac:(repeat split; lia))
  end.
  all: try match goal with
  | |- context[Z.quot (?s - 1) ?cap] =>
      assert (0 <= Z.quot (s - 1) cap <= s - 1) by
        (split; [apply Z.quot_pos; lia | apply Z.quot_le_upper_bound; nia])
  end.
  all: try lia; try nia.
Qed.
Lemma proof_of_max_fill_entail_wit_6_2_split_goal_1 : max_fill_entail_wit_6_2_split_goal_1.
Proof. Abort.

Lemma proof_of_max_fill_entail_wit_6_2_split_goal_2 : max_fill_entail_wit_6_2_split_goal_2.
Proof. Abort.

Lemma proof_of_max_fill_entail_wit_6_2 : max_fill_entail_wit_6_2.
Proof.
  pre_process_default; try entailer!.
  all: try match goal with
  | Hlen : forall r : Z, _ -> Zlength (Znth r ?rs ?d) = ?m
    |- Zlength (Znth ?r ?rs ?d2) = ?m =>
      rewrite (Znth_indep rs r d2 d) by lia; apply Hlen; lia
  end.
  all: try match goal with
  | Hrows : Zlength ?rows = ?n
    |- context[Znth ?c (Znth ?r ?rows nil) 0] =>
      rewrite (Znth_indep rows r nil __default__List_Z) by lia
  end.
  all: try match goal with
  | Hcell : forall r c : Z, _ -> _
    |- context[Znth ?c (Znth ?r ?rs ?d) 0] =>
      pose proof (Hcell r c ltac:(repeat split; lia))
  end.
  all: try match goal with
  | |- context[Z.quot (?s - 1) ?cap] =>
      assert (0 <= Z.quot (s - 1) cap <= s - 1) by
        (split; [apply Z.quot_pos; lia | apply Z.quot_le_upper_bound; nia])
  end.
  all: try lia; try nia.
Qed.
