From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.QCP_demos_LLM Require Import CharPtrArray2D_goal.
From SimpleC.EE.QCP_demos_LLM Require Import CharPtrArray2D_proof_auto.
Import naive_C_Rules.
Local Open Scope sac.

Lemma proof_of_check_dict_case_safety_wit_39_split_goal_1 : check_dict_case_safety_wit_39_split_goal_1.
Proof. Abort.

Lemma proof_of_check_dict_case_safety_wit_39_split_goal_2 : check_dict_case_safety_wit_39_split_goal_2.
Proof. Abort.

Lemma proof_of_check_dict_case_safety_wit_39 : check_dict_case_safety_wit_39.
Proof.
  pre_process_default.
  all: try match goal with
  | Hlast : forall r : Z, _ -> _
    |- context[Zlength (Znth ?k ?rows nil)] =>
      pose proof (Hlast k ltac:(repeat split; lia))
  | Hlast : forall r : Z, _ -> _
    |- context[Znth (Zlength (Znth ?k ?rows nil) - 1) (Znth ?k ?rows nil) 0] =>
      pose proof (Hlast k ltac:(repeat split; lia))
  | Hnz : forall r i : Z, _ -> _
    |- context[Znth ?i (Znth ?k ?rows nil) 0] =>
      pose proof (Hnz k i ltac:(repeat split; lia))
  end.
  all: try match goal with
  | H : forall r : Z, 0 <= r < ?n -> 0 < Zlength (Znth r ?rows nil) <= 100 /\ _
    |- _ => pose proof (H k ltac:(lia))
  end.
  all: try match goal with
  | Hlast : forall r : Z, 0 <= r < ?n -> 0 < Zlength (Znth r ?rows nil) <= 100 /\
              Znth (Zlength (Znth r ?rows nil) - 1) (Znth r ?rows nil) 0 = 0,
    Hnz : Znth ?i (Znth ?k ?rows nil) 0 <> 0
    |- ?i + 1 < Zlength (Znth ?k ?rows nil) =>
      let Hshape := fresh "Hshape" in
      destruct (Hlast k ltac:(lia)) as [Hshape HlastEq];
      assert (i <> Zlength (Znth k rows nil) - 1) by congruence;
      lia
  end.  all: try lia; try nia.
  split_pures.
  - dump_pre_spatial; lia.
  - dump_pre_spatial; lia.
Qed.
Lemma proof_of_check_dict_case_safety_wit_40_split_goal_1 : check_dict_case_safety_wit_40_split_goal_1.
Proof. Abort.

Lemma proof_of_check_dict_case_safety_wit_40_split_goal_2 : check_dict_case_safety_wit_40_split_goal_2.
Proof. Abort.

Lemma proof_of_check_dict_case_safety_wit_40 : check_dict_case_safety_wit_40.
Proof.
  pre_process_default.
  all: try match goal with
  | Hlast : forall r : Z, _ -> _
    |- context[Zlength (Znth ?k ?rows nil)] =>
      pose proof (Hlast k ltac:(repeat split; lia))
  | Hlast : forall r : Z, _ -> _
    |- context[Znth (Zlength (Znth ?k ?rows nil) - 1) (Znth ?k ?rows nil) 0] =>
      pose proof (Hlast k ltac:(repeat split; lia))
  | Hnz : forall r i : Z, _ -> _
    |- context[Znth ?i (Znth ?k ?rows nil) 0] =>
      pose proof (Hnz k i ltac:(repeat split; lia))
  end.
  all: try match goal with
  | H : forall r : Z, 0 <= r < ?n -> 0 < Zlength (Znth r ?rows nil) <= 100 /\ _
    |- _ => pose proof (H k ltac:(lia))
  end.
  all: try match goal with
  | Hlast : forall r : Z, 0 <= r < ?n -> 0 < Zlength (Znth r ?rows nil) <= 100 /\
              Znth (Zlength (Znth r ?rows nil) - 1) (Znth r ?rows nil) 0 = 0,
    Hnz : Znth ?i (Znth ?k ?rows nil) 0 <> 0
    |- ?i + 1 < Zlength (Znth ?k ?rows nil) =>
      let Hshape := fresh "Hshape" in
      destruct (Hlast k ltac:(lia)) as [Hshape HlastEq];
      assert (i <> Zlength (Znth k rows nil) - 1) by congruence;
      lia
  end.  all: try lia; try nia.
  split_pures.
  - dump_pre_spatial; lia.
  - dump_pre_spatial; lia.
Qed.
Lemma proof_of_check_dict_case_entail_wit_1_split_goal_1 : check_dict_case_entail_wit_1_split_goal_1.
Proof. Abort.

Lemma proof_of_check_dict_case_entail_wit_1 : check_dict_case_entail_wit_1.
Proof.
  pre_process_default.
  all: try match goal with
  | Hlast : forall r : Z, _ -> _
    |- context[Zlength (Znth ?k ?rows nil)] =>
      pose proof (Hlast k ltac:(repeat split; lia))
  | Hlast : forall r : Z, _ -> _
    |- context[Znth (Zlength (Znth ?k ?rows nil) - 1) (Znth ?k ?rows nil) 0] =>
      pose proof (Hlast k ltac:(repeat split; lia))
  | Hnz : forall r i : Z, _ -> _
    |- context[Znth ?i (Znth ?k ?rows nil) 0] =>
      pose proof (Hnz k i ltac:(repeat split; lia))
  end.
  all: try match goal with
  | H : forall r : Z, 0 <= r < ?n -> 0 < Zlength (Znth r ?rows nil) <= 100 /\ _
    |- _ => pose proof (H k ltac:(lia))
  end.
  all: try match goal with
  | Hlast : forall r : Z, 0 <= r < ?n -> 0 < Zlength (Znth r ?rows nil) <= 100 /\
              Znth (Zlength (Znth r ?rows nil) - 1) (Znth r ?rows nil) 0 = 0,
    Hnz : Znth ?i (Znth ?k ?rows nil) 0 <> 0
    |- ?i + 1 < Zlength (Znth ?k ?rows nil) =>
      let Hshape := fresh "Hshape" in
      destruct (Hlast k ltac:(lia)) as [Hshape HlastEq];
      assert (i <> Zlength (Znth k rows nil) - 1) by congruence;
      lia
  end.  all: try lia; try nia.
Qed.
Lemma proof_of_check_dict_case_entail_wit_2_split_goal_1 : check_dict_case_entail_wit_2_split_goal_1.
Proof. Abort.

Lemma proof_of_check_dict_case_entail_wit_2_split_goal_spatial : check_dict_case_entail_wit_2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_check_dict_case_entail_wit_2 : check_dict_case_entail_wit_2.
Proof.
  left.
  pre_process_default.
  sep_apply_l_atomic (CharPtrArray2.full_split_to_missing_i
    keys_pre k dict_size_pre rows).
  - dump_pre_spatial; lia.
  - Intros row_ptr.
    Exists row_ptr.
    unfold StorePtrAsElement.storeA.
    change (CharPtrArray2.ElemArray.full row_ptr
      (Zlength (Znth k rows nil)) (Znth k rows nil)) with
      (CharArray.full row_ptr (Zlength (Znth k rows nil))
        (Znth k rows nil)).
    normalize.
    repeat (eapply derivable1s_coq_prop_andp_r;
      [ | try solve [
        auto | lia | nia
      | match goal with
        | H : forall r : Z, 0 <= r < ?n ->
              0 < Zlength (Znth r ?rows nil) <= 100 /\ _,
          Hr : 0 <= ?r < ?n |- _ => destruct (H r Hr); lia
        end
      ]]).
    cancel (CharArray.full row_ptr (Zlength (Znth k rows nil)) (Znth k rows nil)).
    cancel (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows).
    cancel.
Qed.
Lemma proof_of_check_dict_case_entail_wit_3_split_goal_1 : check_dict_case_entail_wit_3_split_goal_1.
Proof. Abort.

Lemma proof_of_check_dict_case_entail_wit_3 : check_dict_case_entail_wit_3.
Proof.
  pre_process_default.
  all: try match goal with
  | Hlast : forall r : Z, _ -> _
    |- context[Zlength (Znth ?k ?rows nil)] =>
      pose proof (Hlast k ltac:(repeat split; lia))
  | Hlast : forall r : Z, _ -> _
    |- context[Znth (Zlength (Znth ?k ?rows nil) - 1) (Znth ?k ?rows nil) 0] =>
      pose proof (Hlast k ltac:(repeat split; lia))
  | Hnz : forall r i : Z, _ -> _
    |- context[Znth ?i (Znth ?k ?rows nil) 0] =>
      pose proof (Hnz k i ltac:(repeat split; lia))
  end.
  all: try match goal with
  | H : forall r : Z, 0 <= r < ?n -> 0 < Zlength (Znth r ?rows nil) <= 100 /\ _
    |- _ => pose proof (H k ltac:(lia))
  end.
  all: try match goal with
  | Hlast : forall r : Z, 0 <= r < ?n -> 0 < Zlength (Znth r ?rows nil) <= 100 /\
              Znth (Zlength (Znth r ?rows nil) - 1) (Znth r ?rows nil) 0 = 0,
    Hnz : Znth ?i (Znth ?k ?rows nil) 0 <> 0
    |- ?i + 1 < Zlength (Znth ?k ?rows nil) =>
      let Hshape := fresh "Hshape" in
      destruct (Hlast k ltac:(lia)) as [Hshape HlastEq];
      assert (i <> Zlength (Znth k rows nil) - 1) by congruence;
      lia
  end.  all: try lia; try nia.
Qed.
Lemma proof_of_check_dict_case_entail_wit_4_split_goal_1 : check_dict_case_entail_wit_4_split_goal_1.
Proof. Abort.

Lemma proof_of_check_dict_case_entail_wit_4_split_goal_2 : check_dict_case_entail_wit_4_split_goal_2.
Proof. Abort.

Lemma proof_of_check_dict_case_entail_wit_4 : check_dict_case_entail_wit_4.
Proof.
  pre_process_default.
  all: try match goal with
  | Hlast : forall r : Z, _ -> _
    |- context[Zlength (Znth ?k ?rows nil)] =>
      pose proof (Hlast k ltac:(repeat split; lia))
  | Hlast : forall r : Z, _ -> _
    |- context[Znth (Zlength (Znth ?k ?rows nil) - 1) (Znth ?k ?rows nil) 0] =>
      pose proof (Hlast k ltac:(repeat split; lia))
  | Hnz : forall r i : Z, _ -> _
    |- context[Znth ?i (Znth ?k ?rows nil) 0] =>
      pose proof (Hnz k i ltac:(repeat split; lia))
  end.
  all: try match goal with
  | H : forall r : Z, 0 <= r < ?n -> 0 < Zlength (Znth r ?rows nil) <= 100 /\ _
    |- _ => pose proof (H k ltac:(lia))
  end.
  all: try match goal with
  | Hlast : forall r : Z, 0 <= r < ?n -> 0 < Zlength (Znth r ?rows nil) <= 100 /\
              Znth (Zlength (Znth r ?rows nil) - 1) (Znth r ?rows nil) 0 = 0,
    Hnz : Znth ?i (Znth ?k ?rows nil) 0 <> 0
    |- ?i + 1 < Zlength (Znth ?k ?rows nil) =>
      let Hshape := fresh "Hshape" in
      destruct (Hlast k ltac:(lia)) as [Hshape HlastEq];
      assert (i <> Zlength (Znth k rows nil) - 1) by congruence;
      lia
  end.  all: try lia; try nia.
  repeat (eapply derivable1s_coq_prop_andp_r;
    [ | try solve [auto | lia | nia | destruct H; lia]]).
  cancel (CharPtrArray2.missing_i keys_pre dict_size_pre k row_ptr rows).
  cancel.
Qed.
Lemma proof_of_check_dict_case_entail_wit_5_1_split_goal_1 : check_dict_case_entail_wit_5_1_split_goal_1.
Proof. Abort.

Lemma proof_of_check_dict_case_entail_wit_5_1 : check_dict_case_entail_wit_5_1.
Proof.
  pre_process_default.
  all: try match goal with
  | Hlast : forall r : Z, _ -> _
    |- context[Zlength (Znth ?k ?rows nil)] =>
      pose proof (Hlast k ltac:(repeat split; lia))
  | Hlast : forall r : Z, _ -> _
    |- context[Znth (Zlength (Znth ?k ?rows nil) - 1) (Znth ?k ?rows nil) 0] =>
      pose proof (Hlast k ltac:(repeat split; lia))
  | Hnz : forall r i : Z, _ -> _
    |- context[Znth ?i (Znth ?k ?rows nil) 0] =>
      pose proof (Hnz k i ltac:(repeat split; lia))
  end.
  all: try match goal with
  | H : forall r : Z, 0 <= r < ?n -> 0 < Zlength (Znth r ?rows nil) <= 100 /\ _
    |- _ => pose proof (H k ltac:(lia))
  end.
  all: try match goal with
  | Hlast : forall r : Z, 0 <= r < ?n -> 0 < Zlength (Znth r ?rows nil) <= 100 /\
              Znth (Zlength (Znth r ?rows nil) - 1) (Znth r ?rows nil) 0 = 0,
    Hnz : Znth ?i (Znth ?k ?rows nil) 0 <> 0
    |- ?i + 1 < Zlength (Znth ?k ?rows nil) =>
      let Hshape := fresh "Hshape" in
      destruct (Hlast k ltac:(lia)) as [Hshape HlastEq];
      assert (i <> Zlength (Znth k rows nil) - 1) by congruence;
      lia
  end.  all: try lia; try nia.
  repeat (eapply derivable1s_coq_prop_andp_r;
    [ | try solve [auto | lia | nia | destruct H; lia]]).
  cancel.
  destruct (PreH18 k ltac:(lia)) as [Hshape HlastEq].
  assert (i <> Zlength (Znth k rows nil) - 1) by congruence.
  lia.
Qed.
Lemma proof_of_check_dict_case_entail_wit_5_2_split_goal_1 : check_dict_case_entail_wit_5_2_split_goal_1.
Proof. Abort.

Lemma proof_of_check_dict_case_entail_wit_5_2 : check_dict_case_entail_wit_5_2.
Proof.
  pre_process_default.
  all: try match goal with
  | Hlast : forall r : Z, _ -> _
    |- context[Zlength (Znth ?k ?rows nil)] =>
      pose proof (Hlast k ltac:(repeat split; lia))
  | Hlast : forall r : Z, _ -> _
    |- context[Znth (Zlength (Znth ?k ?rows nil) - 1) (Znth ?k ?rows nil) 0] =>
      pose proof (Hlast k ltac:(repeat split; lia))
  | Hnz : forall r i : Z, _ -> _
    |- context[Znth ?i (Znth ?k ?rows nil) 0] =>
      pose proof (Hnz k i ltac:(repeat split; lia))
  end.
  all: try match goal with
  | H : forall r : Z, 0 <= r < ?n -> 0 < Zlength (Znth r ?rows nil) <= 100 /\ _
    |- _ => pose proof (H k ltac:(lia))
  end.
  all: try match goal with
  | Hlast : forall r : Z, 0 <= r < ?n -> 0 < Zlength (Znth r ?rows nil) <= 100 /\
              Znth (Zlength (Znth r ?rows nil) - 1) (Znth r ?rows nil) 0 = 0,
    Hnz : Znth ?i (Znth ?k ?rows nil) 0 <> 0
    |- ?i + 1 < Zlength (Znth ?k ?rows nil) =>
      let Hshape := fresh "Hshape" in
      destruct (Hlast k ltac:(lia)) as [Hshape HlastEq];
      assert (i <> Zlength (Znth k rows nil) - 1) by congruence;
      lia
  end.  all: try lia; try nia.
  repeat (eapply derivable1s_coq_prop_andp_r;
    [ | try solve [auto | lia | nia | destruct H; lia]]).
  cancel.
  destruct (PreH16 k ltac:(lia)) as [Hshape HlastEq].
  assert (i <> Zlength (Znth k rows nil) - 1) by congruence.
  lia.
Qed.
Lemma proof_of_check_dict_case_entail_wit_6_split_goal_1 : check_dict_case_entail_wit_6_split_goal_1.
Proof. Abort.

Lemma proof_of_check_dict_case_entail_wit_6_split_goal_spatial : check_dict_case_entail_wit_6_split_goal_spatial.
Proof. Abort.

Lemma proof_of_check_dict_case_entail_wit_6 : check_dict_case_entail_wit_6.
Proof.
  pre_process_default.
  pose proof (CharPtrArray2.missing_i_merge_to_full
    keys_pre k dict_size_pre row_ptr rows (Znth k rows nil)) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  change (CharPtrArray2.ElemArray.full row_ptr
    (Zlength (Znth k rows nil)) (Znth k rows nil)) with
    (CharArray.full row_ptr (Zlength (Znth k rows nil))
      (Znth k rows nil)) in Hmerge.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  repeat (eapply derivable1s_coq_prop_andp_r;
    [ | try solve [auto | lia | nia]]).
  cancel.
Qed.
Lemma proof_of_check_dict_case_entail_wit_7_split_goal_1 : check_dict_case_entail_wit_7_split_goal_1.
Proof. Abort.

Lemma proof_of_check_dict_case_entail_wit_7 : check_dict_case_entail_wit_7.
Proof.
  pre_process_default.
  all: try match goal with
  | Hlast : forall r : Z, _ -> _
    |- context[Zlength (Znth ?k ?rows nil)] =>
      pose proof (Hlast k ltac:(repeat split; lia))
  | Hlast : forall r : Z, _ -> _
    |- context[Znth (Zlength (Znth ?k ?rows nil) - 1) (Znth ?k ?rows nil) 0] =>
      pose proof (Hlast k ltac:(repeat split; lia))
  | Hnz : forall r i : Z, _ -> _
    |- context[Znth ?i (Znth ?k ?rows nil) 0] =>
      pose proof (Hnz k i ltac:(repeat split; lia))
  end.
  all: try match goal with
  | H : forall r : Z, 0 <= r < ?n -> 0 < Zlength (Znth r ?rows nil) <= 100 /\ _
    |- _ => pose proof (H k ltac:(lia))
  end.
  all: try match goal with
  | Hlast : forall r : Z, 0 <= r < ?n -> 0 < Zlength (Znth r ?rows nil) <= 100 /\
              Znth (Zlength (Znth r ?rows nil) - 1) (Znth r ?rows nil) 0 = 0,
    Hnz : Znth ?i (Znth ?k ?rows nil) 0 <> 0
    |- ?i + 1 < Zlength (Znth ?k ?rows nil) =>
      let Hshape := fresh "Hshape" in
      destruct (Hlast k ltac:(lia)) as [Hshape HlastEq];
      assert (i <> Zlength (Znth k rows nil) - 1) by congruence;
      lia
  end.  all: try lia; try nia.
Qed.
Lemma proof_of_check_dict_case_return_wit_2_split_goal_spatial : check_dict_case_return_wit_2_split_goal_spatial.
Proof. Abort.

Lemma proof_of_check_dict_case_return_wit_2 : check_dict_case_return_wit_2.
Proof.
  pre_process_default.
  pose proof (CharPtrArray2.missing_i_merge_to_full
    keys_pre k dict_size_pre row_ptr rows (Znth k rows nil)) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  change (CharPtrArray2.ElemArray.full row_ptr
    (Zlength (Znth k rows nil)) (Znth k rows nil)) with
    (CharArray.full row_ptr (Zlength (Znth k rows nil))
      (Znth k rows nil)) in Hmerge.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  repeat (eapply derivable1s_coq_prop_andp_r;
    [ | try solve [auto | lia | nia]]).
  cancel.
Qed.
Lemma proof_of_check_dict_case_return_wit_3_split_goal_spatial : check_dict_case_return_wit_3_split_goal_spatial.
Proof. Abort.

Lemma proof_of_check_dict_case_return_wit_3 : check_dict_case_return_wit_3.
Proof.
  pre_process_default.
  pose proof (CharPtrArray2.missing_i_merge_to_full
    keys_pre k dict_size_pre row_ptr rows (Znth k rows nil)) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  change (CharPtrArray2.ElemArray.full row_ptr
    (Zlength (Znth k rows nil)) (Znth k rows nil)) with
    (CharArray.full row_ptr (Zlength (Znth k rows nil))
      (Znth k rows nil)) in Hmerge.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  repeat (eapply derivable1s_coq_prop_andp_r;
    [ | try solve [auto | lia | nia]]).
  cancel.
Qed.
Lemma proof_of_check_dict_case_return_wit_4_split_goal_spatial : check_dict_case_return_wit_4_split_goal_spatial.
Proof. Abort.

Lemma proof_of_check_dict_case_return_wit_4 : check_dict_case_return_wit_4.
Proof.
  pre_process_default.
  pose proof (CharPtrArray2.missing_i_merge_to_full
    keys_pre k dict_size_pre row_ptr rows (Znth k rows nil)) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  change (CharPtrArray2.ElemArray.full row_ptr
    (Zlength (Znth k rows nil)) (Znth k rows nil)) with
    (CharArray.full row_ptr (Zlength (Znth k rows nil))
      (Znth k rows nil)) in Hmerge.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  repeat (eapply derivable1s_coq_prop_andp_r;
    [ | try solve [auto | lia | nia]]).
  cancel.
Qed.
Lemma proof_of_check_dict_case_return_wit_5_split_goal_spatial : check_dict_case_return_wit_5_split_goal_spatial.
Proof. Abort.

Lemma proof_of_check_dict_case_return_wit_5 : check_dict_case_return_wit_5.
Proof.
  pre_process_default.
  pose proof (CharPtrArray2.missing_i_merge_to_full
    keys_pre k dict_size_pre row_ptr rows (Znth k rows nil)) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  change (CharPtrArray2.ElemArray.full row_ptr
    (Zlength (Znth k rows nil)) (Znth k rows nil)) with
    (CharArray.full row_ptr (Zlength (Znth k rows nil))
      (Znth k rows nil)) in Hmerge.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  repeat (eapply derivable1s_coq_prop_andp_r;
    [ | try solve [auto | lia | nia]]).
  cancel.
Qed.
Lemma proof_of_check_dict_case_return_wit_6_split_goal_spatial : check_dict_case_return_wit_6_split_goal_spatial.
Proof. Abort.

Lemma proof_of_check_dict_case_return_wit_6 : check_dict_case_return_wit_6.
Proof.
  pre_process_default.
  pose proof (CharPtrArray2.missing_i_merge_to_full
    keys_pre k dict_size_pre row_ptr rows (Znth k rows nil)) as Hmerge.
  unfold StorePtrAsElement.storeA in Hmerge.
  change (CharPtrArray2.ElemArray.full row_ptr
    (Zlength (Znth k rows nil)) (Znth k rows nil)) with
    (CharArray.full row_ptr (Zlength (Znth k rows nil))
      (Znth k rows nil)) in Hmerge.
  sep_apply Hmerge; try lia.
  rewrite replace_Znth_Znth by lia.
  repeat (eapply derivable1s_coq_prop_andp_r;
    [ | try solve [auto | lia | nia]]).
  cancel.
Qed.
