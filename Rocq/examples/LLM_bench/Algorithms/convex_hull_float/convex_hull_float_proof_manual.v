Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import MonotonicList int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
From SimpleC.EE.LLM_bench.Algorithms.convex_hull_float Require Import convex_hull_float_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.convex_hull_float.convex_hull_float_lib.
Local Open Scope sac.

(** The public contracts expose safety assumptions; compatibility predicates
    below are reconstructed locally to reuse the established helper proofs. *)
Lemma convex_lower_pop_positive : forall sorted before chain read top,
  pointf_lower_pop_inv_legacy sorted before chain read top ->
  0 < read -> 0 < top.
Proof.
  intros sorted before chain read top [Hscan [Htrace Htop]] Hread.
  destruct Hscan as [Hrange [_ [Hscan Hdone]]].
  assert (Hbefore : 0 < Zlength before).
  { eapply pointf_scan_from_nonempty_length__andrew_lower; [exact Hscan | reflexivity |].
    rewrite Zlength_sublist by lia. lia. }
  pose proof (pointf_pop_trace_positive_length__andrew_lower _ _ _ Htrace Hbefore).
  lia.
Qed.
Lemma convex_upper_pop_length : forall sorted lower before chain read top lower_n,
  pointf_upper_pop_inv_legacy sorted lower before chain read top lower_n ->
  top <= Zlength before.
Proof.
  intros sorted lower before chain read top lower_n [_ [Htrace [Htop _]]].
  pose proof (pointf_upper_pop_trace_length_le__andrew_upper _ _ _ _ Htrace).
  lia.
Qed.
Ltac convex_arith :=
  repeat rewrite Zlength_replace_Znth;
  try rewrite pointf_swap_length__swap_partition;
  repeat rewrite Zlength_sublist by lia;
  lia.
Ltac convex_pose T tac :=
  match goal with
  | _ : T |- _ => fail 1
  | _ => let HH := fresh "Hconvex" in assert T as HH by tac
  end.
Ltac convex_prepare :=
  repeat first
  [ multimatch goal with
    | HX : Forall fp32_isFinite (map pointf_get_x ?l),
      HY : Forall fp32_isFinite (map pointf_get_y ?l) |- _ =>
      convex_pose (pointsf_finite l)
        ltac:(apply (proj2 (pointsf_finite_fields l)); auto)
    end
  | multimatch goal with
    | H : forall a b c : PointF, ((In a ?l /\ In b ?l) /\ In c ?l) -> _ |- _ =>
      convex_pose (all_pointf_cross_finite l)
        ltac:(unfold all_pointf_cross_finite; intros a b c Ha Hb Hc;
          pose proof (H a b c ltac:(tauto)) as HC;
          unfold pointf_cross_finite;
          cbn [pointf_get_x pointf_get_y] in HC; tauto)
    end
  | multimatch goal with
    | HP : pointf_permutation ?before ?after, HF : pointsf_finite ?before |- _ =>
      convex_pose (pointsf_finite after)
        ltac:(eapply pointsf_finite_permutation__swap_partition; [exact HP | exact HF])
    end
  | multimatch goal with
    | HP : pointf_permutation ?before ?after, HF : all_pointf_cross_finite ?before |- _ =>
      convex_pose (all_pointf_cross_finite after)
        ltac:(eapply all_pointf_cross_finite_permutation__swap_partition; [exact HP | exact HF])
    end
  | multimatch goal with
    | HP : pointf_permutation ?before ?after |- _ =>
      convex_pose (Zlength before = Zlength after)
        ltac:(rewrite !Zlength_correct; rewrite (Permutation_length HP); reflexivity)
    end
  | multimatch goal with
    | H : is_andrew_hull_float ?input ?sorted ?hull |- _ =>
      convex_pose (pointf_permutation input sorted) ltac:(exact (proj1 H))
    end
  | multimatch goal with
    | H : is_andrew_hull_float ?input ?sorted ?hull |- _ =>
      convex_pose (pointf_xy_sorted sorted) ltac:(exact (proj1 (proj2 H)))
    end
  | multimatch goal with
    | H : is_andrew_hull_float ?input ?sorted ?hull |- _ =>
      convex_pose (is_andrew_hull_float_legacy input sorted hull)
        ltac:(apply is_andrew_hull_float_equiv; exact H)
    end
  | multimatch goal with
    | H : pointf_xy_partition_scan_inv ?before ?cur ?lo ?hi ?pivot ?split ?scan |- _ =>
      convex_pose (pointf_xy_partition_scan_inv_legacy before cur lo hi pivot split scan)
        ltac:(apply (proj1 (pointf_partition_scan_math_iff before cur lo hi pivot split scan
          ltac:(convex_arith) ltac:(convex_arith) ltac:(convex_arith) ltac:(convex_arith))); exact H)
    end
  | multimatch goal with
    | H : pointf_lower_scan_inv ?sorted ?chain ?read ?top |- _ =>
      convex_pose (pointf_lower_scan_inv_legacy sorted chain read top)
        ltac:(apply pointf_lower_scan_legacy_view; repeat split; try assumption; convex_arith)
    end
  | multimatch goal with
    | H : pointf_lower_pop_inv ?sorted ?before ?chain ?read ?top |- _ =>
      convex_pose (pointf_lower_pop_inv_legacy sorted before chain read top)
        ltac:(apply pointf_lower_pop_legacy_view; unfold pointf_lower_pop_inv in H; repeat split; try tauto; convex_arith)
    end
  | multimatch goal with
    | H : pointf_upper_scan_inv ?sorted ?lower ?chain ?read ?top ?lower_n |- _ =>
      convex_pose (pointf_upper_scan_inv_legacy sorted lower chain read top lower_n)
        ltac:(apply pointf_upper_scan_legacy_view; unfold pointf_upper_scan_inv in H; repeat split; try tauto;
          try unfold pointf_upper_capacity; repeat split; try assumption; convex_arith)
    end
  | multimatch goal with
    | H : pointf_upper_pop_inv ?sorted ?lower ?before ?chain ?read ?top ?lower_n |- _ =>
      convex_pose (pointf_upper_pop_inv_legacy sorted lower before chain read top lower_n)
        ltac:(apply pointf_upper_pop_legacy_view; unfold pointf_upper_pop_inv, pointf_upper_scan_inv in H; repeat split; try tauto;
          try unfold pointf_upper_capacity; repeat split; try assumption; convex_arith)
    end
  | multimatch goal with
    | H : pointf_lower_pop_inv_legacy ?sorted ?before ?chain ?read ?top |- _ =>
      convex_pose (0 < read -> 0 < top)
        ltac:(eapply convex_lower_pop_positive; exact H)
    end
  | multimatch goal with
    | H : pointf_upper_pop_inv_legacy ?sorted ?lower ?before ?chain ?read ?top ?lower_n |- _ =>
      convex_pose (top <= Zlength before)
        ltac:(eapply convex_upper_pop_length; exact H)
    end
  | multimatch goal with
    | H : pointsf_finite ?l |- _ =>
      convex_pose (Forall fp32_isFinite (map pointf_get_x l))
        ltac:(exact (proj1 (proj1 (pointsf_finite_fields l) H)))
    end
  | multimatch goal with
    | H : pointsf_finite ?l |- _ =>
      convex_pose (Forall fp32_isFinite (map pointf_get_y l))
        ltac:(exact (proj2 (proj1 (pointsf_finite_fields l) H)))
    end
  ].
Ltac convex_legacy_goal :=
  try match goal with
  | |- pointf_xy_partition_scan_inv ?before ?cur ?lo ?hi ?pivot ?split ?scan =>
      apply (proj2 (pointf_partition_scan_math_iff before cur lo hi pivot split scan
        ltac:(convex_arith) ltac:(convex_arith) ltac:(convex_arith) ltac:(convex_arith)))
  | |- pointf_lower_scan_inv _ _ _ _ => apply pointf_lower_scan_math_of_legacy
  | |- pointf_lower_pop_inv _ _ _ _ _ => apply pointf_lower_pop_math_of_legacy
  | |- pointf_upper_scan_inv _ _ _ _ _ _ => apply pointf_upper_scan_math_of_legacy
  | |- pointf_upper_pop_inv _ _ _ _ _ _ _ => apply pointf_upper_pop_math_of_legacy
  | |- is_andrew_hull_float ?input ?sorted ?hull =>
      apply (proj2 (is_andrew_hull_float_equiv input sorted hull))
  end.
Ltac convex_facts :=
  try dump_pre_spatial;
  convex_prepare;
  try assumption;
  try match goal with
  | |- Forall fp32_isFinite (map ?getter ?values) =>
      let HF := fresh "Hfinite" in
      assert (HF : pointsf_finite values) by
        first [assumption
              |solve [eapply pointsf_finite_permutation__swap_partition;
                [apply pointf_swap_permutation__swap_partition; convex_arith |eassumption]]
              |solve [eapply pointsf_finite_lower_store__andrew_lower; eauto; convex_arith]
              |solve [eapply pointsf_finite_upper_store__andrew_upper; eauto; convex_arith]];
      pose proof (proj1 (pointsf_finite_fields values) HF); tauto
  end;
  try match goal with
  | HF : pointsf_finite ?values |- context [Znth ?index ?values ?default] =>
      let HP := fresh "Helement" in
      assert (HP : pointf_finite (Znth index values default)) by
        (apply (proj1 (Forall_Znth pointf_finite default values) HF); convex_arith);
      try solve [unfold pointf_get_x; apply pointf_x_eq_self__partition; exact HP
                |unfold pointf_get_y; apply pointf_y_eq_self__partition; exact HP];
      unfold pointf_finite in HP
  end;
  try match goal with
  | |- pointf_finite _ => unfold pointf_finite
  | |- pointf_cross_finite _ _ _ => unfold pointf_cross_finite
  | |- all_pointf_cross_finite _ => unfold all_pointf_cross_finite
  end;
  intros;
  try match goal with
  | H : all_pointf_cross_finite ?l |- context [pointf_cross ?a ?b ?c] =>
      let HC := fresh "Hcross" in
      pose proof (H a b c ltac:(tauto) ltac:(tauto) ltac:(tauto)) as HC;
      unfold pointf_cross_finite in HC
  end;
  cbn [pointf_get_x pointf_get_y] in *;
  try tauto; try convex_arith.
Ltac build_lower_andrew_cross_finite Hcross :=
  match goal with
  | Hacf : all_pointf_cross_finite ?sorted,
    Hpop : pointf_lower_pop_inv_legacy ?sorted ?before (sublist 0 ?k ?hull) ?i ?k,
    Hsorted_len : Zlength ?sorted = ?n,
    Hhull_len : Zlength ?hull = _ |- context [Znth _ ?hull ?d] =>
      assert (Hcross : pointf_cross_finite
        (Znth (k - 2) hull d)
        (Znth (k - 1) hull d)
        (Znth i sorted d));
      [ apply Hacf;
        [ eapply pointf_lower_pop_inv_chain_member_sorted__andrew_lower;
          [ exact Hpop
          | apply Znth_In_sublist0__andrew; [lia | rewrite Hhull_len; lia] ]
        | eapply pointf_lower_pop_inv_chain_member_sorted__andrew_lower;
          [ exact Hpop
          | apply Znth_In_sublist0__andrew; [lia | rewrite Hhull_len; lia] ]
        | apply Znth_In_range__andrew; rewrite Hsorted_len; lia ]
      | idtac ]
  end.

Ltac build_upper_andrew_cross_finite Hcross :=
  match goal with
  | Hacf : all_pointf_cross_finite ?sorted,
    Hpop : pointf_upper_pop_inv_legacy ?sorted ?lower ?before
      (sublist 0 ?k ?hull) ?i ?k ?lower_n,
    Hsorted_len : Zlength ?sorted = ?n,
    Hhull_len : Zlength ?hull = _ |- _ =>
      match goal with
      | |- context [Znth _ _ ?d] =>
        assert (Hcross : pointf_cross_finite
          (Znth (k - 2) hull d)
          (Znth (k - 1) hull d)
          (Znth i sorted d));
        [ apply Hacf;
          [ eapply (pointf_upper_pop_inv_chain_member_sorted__andrew_upper
              sorted lower before (sublist 0 k hull) i k lower_n);
            [ rewrite Hsorted_len; lia
            | exact Hpop
            | apply Znth_In_sublist0__andrew; [lia | rewrite Hhull_len; lia] ]
          | eapply (pointf_upper_pop_inv_chain_member_sorted__andrew_upper
              sorted lower before (sublist 0 k hull) i k lower_n);
            [ rewrite Hsorted_len; lia
            | exact Hpop
            | apply Znth_In_sublist0__andrew; [lia | rewrite Hhull_len; lia] ]
          | apply Znth_In_range__andrew; rewrite Hsorted_len; lia ]
        | idtac ]
      end
  end.

Ltac finish_andrew_cross_projection Hcross :=
  unfold pointf_cross_finite, pointf_cross in Hcross; cbn in Hcross;
  destruct Hcross as
    [Hdx [Hdyc [Hdyb [Hdxc [Hmul1 [Hmul2 Hcross_val]]]]]];
  dump_pre_spatial;
  first
    [ exact Hcross_val
    | exact Hmul2
    | exact Hdxc
    | exact Hdyb
    | exact Hmul1
    | exact Hdyc
    | exact Hdx ].

Ltac prove_lower_andrew_cross_projection :=
  LLM_pre_process ltac:(int_auto); convex_prepare;
  match goal with
  | Hacf : all_pointf_cross_finite ?sorted,
    Hpop : pointf_lower_pop_inv_legacy ?sorted ?before (sublist 0 ?k ?hull) ?i ?k,
    Hsorted_len : Zlength ?sorted = ?n,
    Hhull_len : Zlength ?hull = _ |- context [Znth _ ?hull ?d] =>
      let Hcross := fresh "Hcross" in
      assert (Hcross : pointf_cross_finite
        (Znth (k - 2) hull d)
        (Znth (k - 1) hull d)
        (Znth i sorted d));
      [ apply Hacf;
        [ eapply pointf_lower_pop_inv_chain_member_sorted__andrew_lower;
          [ exact Hpop
          | apply Znth_In_sublist0__andrew; [lia | rewrite Hhull_len; lia] ]
        | eapply pointf_lower_pop_inv_chain_member_sorted__andrew_lower;
          [ exact Hpop
          | apply Znth_In_sublist0__andrew; [lia | rewrite Hhull_len; lia] ]
        | apply Znth_In_range__andrew; rewrite Hsorted_len; lia ]
      | finish_andrew_cross_projection Hcross ]
  end.

Ltac prove_upper_andrew_cross_projection :=
  LLM_pre_process ltac:(int_auto); convex_prepare;
  match goal with
  | Hacf : all_pointf_cross_finite ?sorted,
    Hpop : pointf_upper_pop_inv_legacy ?sorted ?lower ?before
      (sublist 0 ?k ?hull) ?i ?k ?lower_n,
    Hsorted_len : Zlength ?sorted = ?n,
    Hhull_len : Zlength ?hull = _ |- context [Znth _ ?hull ?d] =>
      let Hcross := fresh "Hcross" in
      assert (Hcross : pointf_cross_finite
        (Znth (k - 2) hull d)
        (Znth (k - 1) hull d)
        (Znth i sorted d));
      [ apply Hacf;
        [ eapply pointf_upper_pop_inv_chain_member_sorted__andrew_upper;
          [ rewrite Hsorted_len; lia
          | exact Hpop
          | apply Znth_In_sublist0__andrew; [lia | rewrite Hhull_len; lia] ]
        | eapply pointf_upper_pop_inv_chain_member_sorted__andrew_upper;
          [ rewrite Hsorted_len; lia
          | exact Hpop
          | apply Znth_In_sublist0__andrew; [lia | rewrite Hhull_len; lia] ]
        | apply Znth_In_range__andrew; rewrite Hsorted_len; lia ]
      | finish_andrew_cross_projection Hcross ]
  end.

Lemma proof_of_point_cmp_xy_safety_wit_1_split_goal_1 : point_cmp_xy_safety_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_point_cmp_xy_safety_wit_1_split_goal_2 : point_cmp_xy_safety_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_point_cmp_xy_safety_wit_1 : point_cmp_xy_safety_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_point_cmp_xy_safety_wit_1_split_goal_1.
  - Goal_apply proof_of_point_cmp_xy_safety_wit_1_split_goal_2.
Qed.

Lemma proof_of_point_cmp_xy_safety_wit_4_split_goal_1 : point_cmp_xy_safety_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_point_cmp_xy_safety_wit_4_split_goal_2 : point_cmp_xy_safety_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_point_cmp_xy_safety_wit_4 : point_cmp_xy_safety_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_point_cmp_xy_safety_wit_4_split_goal_1.
  - Goal_apply proof_of_point_cmp_xy_safety_wit_4_split_goal_2.
Qed.

Lemma proof_of_point_cmp_xy_safety_wit_6_split_goal_1 : point_cmp_xy_safety_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_point_cmp_xy_safety_wit_6_split_goal_2 : point_cmp_xy_safety_wit_6_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_point_cmp_xy_safety_wit_6 : point_cmp_xy_safety_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_point_cmp_xy_safety_wit_6_split_goal_1.
  - Goal_apply proof_of_point_cmp_xy_safety_wit_6_split_goal_2.
Qed.

Lemma proof_of_point_cmp_xy_safety_wit_9_split_goal_1 : point_cmp_xy_safety_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_point_cmp_xy_safety_wit_9_split_goal_2 : point_cmp_xy_safety_wit_9_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_point_cmp_xy_safety_wit_9 : point_cmp_xy_safety_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_point_cmp_xy_safety_wit_9_split_goal_1.
  - Goal_apply proof_of_point_cmp_xy_safety_wit_9_split_goal_2.
Qed.

Lemma proof_of_point_cmp_xy_return_wit_1_split_goal_1 : point_cmp_xy_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  unfold pointf_cmp_xy, fp32_le, fp32_ge in *; simpl in *.
  destruct (fp32_compare ax_pre bx_pre) as [[]|] eqn:Hx; simpl in *; try contradiction.
  destruct (fp32_compare ay_pre b_y_pre) as [[]|] eqn:Hy; simpl in *; try contradiction;
    reflexivity.
Qed.

Lemma proof_of_point_cmp_xy_return_wit_1 : point_cmp_xy_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_point_cmp_xy_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_point_cmp_xy_return_wit_2_split_goal_1 : point_cmp_xy_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  unfold pointf_cmp_xy, fp32_le, fp32_ge, fp32_gt in *; simpl in *.
  destruct (fp32_compare ax_pre bx_pre) as [[]|] eqn:Hx; simpl in *; try contradiction.
  rewrite PreH1.
  reflexivity.
Qed.

Lemma proof_of_point_cmp_xy_return_wit_2 : point_cmp_xy_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_point_cmp_xy_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_point_cmp_xy_return_wit_3_split_goal_1 : point_cmp_xy_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  unfold pointf_cmp_xy, fp32_le, fp32_ge, fp32_lt in *; simpl in *.
  destruct (fp32_compare ax_pre bx_pre) as [[]|] eqn:Hx; simpl in *; try contradiction.
  rewrite PreH1.
  reflexivity.
Qed.

Lemma proof_of_point_cmp_xy_return_wit_3 : point_cmp_xy_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_point_cmp_xy_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_point_cmp_xy_return_wit_4_split_goal_1 : point_cmp_xy_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  unfold pointf_cmp_xy, fp32_gt in *; simpl in *.
  rewrite PreH1.
  reflexivity.
Qed.

Lemma proof_of_point_cmp_xy_return_wit_4 : point_cmp_xy_return_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_point_cmp_xy_return_wit_4_split_goal_1.
Qed.

Lemma proof_of_point_cmp_xy_return_wit_5_split_goal_1 : point_cmp_xy_return_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  unfold pointf_cmp_xy, fp32_lt in *; simpl in *.
  rewrite PreH1.
  reflexivity.
Qed.

Lemma proof_of_point_cmp_xy_return_wit_5 : point_cmp_xy_return_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_point_cmp_xy_return_wit_5_split_goal_1.
Qed.

Lemma proof_of_point_cross_safety_wit_1_split_goal_1 : point_cross_safety_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_point_cross_safety_wit_1 : point_cross_safety_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_point_cross_safety_wit_1_split_goal_1.
Qed.

Lemma proof_of_point_cross_safety_wit_2_split_goal_1 : point_cross_safety_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_point_cross_safety_wit_2 : point_cross_safety_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_point_cross_safety_wit_2_split_goal_1.
Qed.

Lemma proof_of_point_cross_safety_wit_3_split_goal_1 : point_cross_safety_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_point_cross_safety_wit_3 : point_cross_safety_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_point_cross_safety_wit_3_split_goal_1.
Qed.

Lemma proof_of_point_cross_safety_wit_4_split_goal_1 : point_cross_safety_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_point_cross_safety_wit_4 : point_cross_safety_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_point_cross_safety_wit_4_split_goal_1.
Qed.

Lemma proof_of_point_cross_safety_wit_5_split_goal_1 : point_cross_safety_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_point_cross_safety_wit_5 : point_cross_safety_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_point_cross_safety_wit_5_split_goal_1.
Qed.

Lemma proof_of_point_cross_safety_wit_6_split_goal_1 : point_cross_safety_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_point_cross_safety_wit_6 : point_cross_safety_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_point_cross_safety_wit_6_split_goal_1.
Qed.

Lemma proof_of_point_cross_safety_wit_7_split_goal_1 : point_cross_safety_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_point_cross_safety_wit_7 : point_cross_safety_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_point_cross_safety_wit_7_split_goal_1.
Qed.

Lemma proof_of_point_cross_return_wit_1_split_goal_1 : point_cross_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  assert (OldPreH4 : (pointf_cross_finite (pointf_mk (ax_pre) (ay_pre)) (pointf_mk (bx_pre) (b_y_pre)) (pointf_mk (cx_pre) (cy_pre)) )) by convex_facts.
  convex_legacy_goal.

  unfold pointf_cross_finite in OldPreH4.
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  end.
  unfold pointf_cross, fp32_eq, fp32_compare, fp32_isFinite in *.
  rewrite Binary.Bcompare_correct by assumption.
  rewrite Raux.Rcompare_Eq by reflexivity.
  reflexivity.
Qed.

Lemma proof_of_point_cross_return_wit_1 : point_cross_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_point_cross_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_swap_points_return_wit_1_split_goal_1 : swap_points_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  destruct (Z.eq_dec i_pre j_pre) as [Hij | Hij].
  - subst j_pre.
    unfold pointf_swap.
    repeat rewrite Znth_replace_Znth_Same by (rewrite ?Zlength_replace_Znth; lia).
    repeat rewrite replace_Znth_Znth by lia.
    repeat rewrite (Znth_indep l i_pre __default_PointF default_pointf) by lia.
    destruct (Znth i_pre l default_pointf) eqn:Hzi.
    cbn.
    repeat rewrite <- Hzi.
    repeat rewrite replace_Znth_Znth by lia.
    reflexivity.
  - unfold pointf_swap.
    repeat rewrite Znth_replace_Znth_Same by (rewrite ?Zlength_replace_Znth; lia).
    repeat rewrite Znth_replace_Znth_Diff by (rewrite ?Zlength_replace_Znth; lia).
    repeat rewrite replace_Znth_Znth by lia.
    repeat rewrite (Znth_indep l i_pre __default_PointF default_pointf) by lia.
    repeat rewrite (Znth_indep l j_pre __default_PointF default_pointf) by lia.
    destruct (Znth i_pre l default_pointf) eqn:Hzi.
    destruct (Znth j_pre l default_pointf) eqn:Hzj.
    cbn.
    repeat rewrite <- Hzi.
    repeat rewrite <- Hzj.
    apply (proj2 (list_eq_ext _ _ default_pointf)).
    split.
    + repeat rewrite Zlength_replace_Znth. reflexivity.
    + intros k Hk.
      repeat rewrite Zlength_replace_Znth in Hk.
      destruct (Z.eq_dec k j_pre) as [Hkj | Hkj].
      * subst k.
        repeat rewrite Znth_replace_Znth_Same by (rewrite ?Zlength_replace_Znth; lia).
        reflexivity.
      * destruct (Z.eq_dec k i_pre) as [Hki | Hki].
        -- subst k.
           repeat rewrite Znth_replace_Znth_Diff by (rewrite ?Zlength_replace_Znth; lia).
           repeat rewrite Znth_replace_Znth_Same by (rewrite ?Zlength_replace_Znth; lia).
           repeat rewrite Znth_replace_Znth_Diff by (rewrite ?Zlength_replace_Znth; lia).
           repeat rewrite Znth_replace_Znth_Same by (rewrite ?Zlength_replace_Znth; lia).
           reflexivity.
        -- repeat rewrite Znth_replace_Znth_Diff by (rewrite ?Zlength_replace_Znth; lia).
           reflexivity.
Qed.

Lemma proof_of_swap_points_return_wit_1 : swap_points_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_swap_points_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_1_split_goal_1 : partition_xy_points_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  assert (Hpivot :
      Znth high_pre l default_pointf =
      pointf_mk (pointf_get_x (Znth high_pre l __default_PointF))
        (pointf_get_y (Znth high_pre l __default_PointF))).
  {
    unfold pointf_get_x, pointf_get_y.
    rewrite <- (Znth_indep l high_pre __default_PointF default_pointf) by lia.
    destruct (Znth high_pre l __default_PointF); reflexivity.
  }
  rewrite <- Hpivot.
  apply pointf_partition_scan_inv_init__swap_partition; lia.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_1_split_goal_2 : partition_xy_points_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_1_split_goal_3 : partition_xy_points_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_1_split_goal_4 : partition_xy_points_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_1_split_goal_5 : partition_xy_points_entail_wit_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  unfold pointf_get_y.
  apply pointf_y_eq_self__partition.
  rewrite (Znth_indep l high_pre __default_PointF default_pointf) by lia.
  apply pointsf_finite_Znth__swap_partition; auto; lia.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_1_split_goal_6 : partition_xy_points_entail_wit_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  unfold pointf_get_x.
  apply pointf_x_eq_self__partition.
    rewrite (Znth_indep l high_pre __default_PointF default_pointf) by lia.
    apply pointsf_finite_Znth__swap_partition; auto; lia.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_1 : partition_xy_points_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_partition_xy_points_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_partition_xy_points_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_partition_xy_points_entail_wit_1_split_goal_3.
  - Goal_apply proof_of_partition_xy_points_entail_wit_1_split_goal_4.
  - Goal_apply proof_of_partition_xy_points_entail_wit_1_split_goal_5.
  - Goal_apply proof_of_partition_xy_points_entail_wit_1_split_goal_6.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_2_1_split_goal_1 : partition_xy_points_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  assert (Hcmp_le :
      pointf_cmp_xy (Znth j cur_2 default_pointf)
        (pointf_mk pivot_x pivot_y) <= 0).
  {
    rewrite <- (Znth_indep cur_2 j __default_PointF default_pointf) by lia.
    replace (Znth j cur_2 __default_PointF)
      with (pointf_mk (pointf_get_x (Znth j cur_2 __default_PointF))
            (pointf_get_y (Znth j cur_2 __default_PointF))).
    - rewrite <- PreH3. exact PreH2.
    - unfold pointf_get_x, pointf_get_y.
      destruct (Znth j cur_2 __default_PointF); reflexivity.
  }
  eapply pointf_partition_scan_inv_step_le__swap_partition; eauto; try lia.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_2_1_split_goal_2 : partition_xy_points_entail_wit_2_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_2_1_split_goal_3 : partition_xy_points_entail_wit_2_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_2_1_split_goal_4 : partition_xy_points_entail_wit_2_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  rewrite (Znth_indep (pointf_swap cur_2 (i + 1) j) high_pre
             __default_PointF default_pointf)
    by (rewrite pointf_swap_length__swap_partition; lia).
  rewrite pointf_swap_Znth_other__swap_partition by lia.
  rewrite (Znth_indep cur_2 high_pre default_pointf __default_PointF) by lia.
  exact PreH15.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_2_1_split_goal_5 : partition_xy_points_entail_wit_2_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  rewrite (Znth_indep (pointf_swap cur_2 (i + 1) j) high_pre
             __default_PointF default_pointf)
    by (rewrite pointf_swap_length__swap_partition; lia).
  rewrite pointf_swap_Znth_other__swap_partition by lia.
  rewrite (Znth_indep cur_2 high_pre default_pointf __default_PointF) by lia.
  exact PreH14.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_2_1_split_goal_6 : partition_xy_points_entail_wit_2_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  rewrite pointf_swap_length__swap_partition. exact PreH13.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_2_1 : partition_xy_points_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_partition_xy_points_entail_wit_2_1_split_goal_1.
  - Goal_apply proof_of_partition_xy_points_entail_wit_2_1_split_goal_2.
  - Goal_apply proof_of_partition_xy_points_entail_wit_2_1_split_goal_3.
  - Goal_apply proof_of_partition_xy_points_entail_wit_2_1_split_goal_4.
  - Goal_apply proof_of_partition_xy_points_entail_wit_2_1_split_goal_5.
  - Goal_apply proof_of_partition_xy_points_entail_wit_2_1_split_goal_6.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_2_2_split_goal_1 : partition_xy_points_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  replace cur_2 with (pointf_swap cur_2 (i + 1) j).
  2:{
    rewrite PreH1.
    apply pointf_swap_same__swap_partition. lia.
  }
  assert (Hcmp_le :
    pointf_cmp_xy (Znth j cur_2 default_pointf)
      (pointf_mk pivot_x pivot_y) <= 0).
  {
    rewrite <- (Znth_indep cur_2 j __default_PointF default_pointf) by lia.
    replace (Znth j cur_2 __default_PointF)
      with (pointf_mk (pointf_get_x (Znth j cur_2 __default_PointF))
            (pointf_get_y (Znth j cur_2 __default_PointF))).
    - rewrite <- PreH3. exact PreH2.
    - unfold pointf_get_x, pointf_get_y.
      destruct (Znth j cur_2 __default_PointF); reflexivity.
  }
  symmetry in PreH1; subst j.
  eapply pointf_partition_scan_inv_step_le__swap_partition; eauto; try lia.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_2_2 : partition_xy_points_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_partition_xy_points_entail_wit_2_2_split_goal_1.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_2_3_split_goal_1 : partition_xy_points_entail_wit_2_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  assert (Hcmp :
    pointf_cmp_xy (Znth j cur_2 default_pointf)
      (pointf_mk pivot_x pivot_y) > 0).
  {
    rewrite <- (Znth_indep cur_2 j __default_PointF default_pointf) by lia.
    replace (pointf_mk (pointf_get_x (Znth j cur_2 __default_PointF))
              (pointf_get_y (Znth j cur_2 __default_PointF)))
      with (Znth j cur_2 __default_PointF) in PreH2.
    - rewrite <- PreH2. exact PreH1.
    - unfold pointf_get_x, pointf_get_y.
      destruct (Znth j cur_2 __default_PointF); reflexivity.
  }
  eapply pointf_partition_scan_inv_step_gt__swap_partition; eauto; try lia.
  apply pointf_cmp_xy_gt_flip__partition. exact Hcmp.
Qed.

Lemma proof_of_partition_xy_points_entail_wit_2_3 : partition_xy_points_entail_wit_2_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_partition_xy_points_entail_wit_2_3_split_goal_1.
Qed.

Lemma proof_of_partition_xy_points_return_wit_1_split_goal_1 : partition_xy_points_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  eapply pointf_partition_scan_final_partitioned__swap_partition; eauto; lia.
Qed.

Lemma proof_of_partition_xy_points_return_wit_1_split_goal_2 : partition_xy_points_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  eapply pointf_partition_scan_final_same_outside__swap_partition; eauto; lia.
Qed.

Lemma proof_of_partition_xy_points_return_wit_1_split_goal_3 : partition_xy_points_return_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  eapply pointf_partition_scan_final_permutation__swap_partition; eauto; lia.
Qed.

Lemma proof_of_partition_xy_points_return_wit_1 : partition_xy_points_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_partition_xy_points_return_wit_1_split_goal_1.
  - Goal_apply proof_of_partition_xy_points_return_wit_1_split_goal_2.
  - Goal_apply proof_of_partition_xy_points_return_wit_1_split_goal_3.
Qed.

Lemma proof_of_partition_xy_points_return_wit_2_split_goal_1 : partition_xy_points_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  replace cur with (pointf_swap cur (i + 1) high_pre).
  2:{
    rewrite PreH1.
    apply pointf_swap_same__swap_partition. lia.
  }
  symmetry in PreH1; subst high_pre.
  eapply pointf_partition_scan_final_partitioned__swap_partition; eauto; lia.
Qed.

Lemma proof_of_partition_xy_points_return_wit_2_split_goal_2 : partition_xy_points_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  replace cur with (pointf_swap cur (i + 1) high_pre).
  2:{
    rewrite PreH1.
    apply pointf_swap_same__swap_partition. lia.
  }
  symmetry in PreH1; subst high_pre.
  eapply pointf_partition_scan_final_same_outside__swap_partition; eauto; lia.
Qed.

Lemma proof_of_partition_xy_points_return_wit_2_split_goal_3 : partition_xy_points_return_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  replace cur with (pointf_swap cur (i + 1) high_pre).
  2:{
    rewrite PreH1.
    apply pointf_swap_same__swap_partition. lia.
  }
  symmetry in PreH1; subst high_pre.
  eapply pointf_partition_scan_final_permutation__swap_partition; eauto; lia.
Qed.

Lemma proof_of_partition_xy_points_return_wit_2 : partition_xy_points_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_partition_xy_points_return_wit_2_split_goal_1.
  - Goal_apply proof_of_partition_xy_points_return_wit_2_split_goal_2.
  - Goal_apply proof_of_partition_xy_points_return_wit_2_split_goal_3.
Qed.

Lemma proof_of_partition_xy_points_partial_solve_wit_5_pure_split_goal_1 : partition_xy_points_partial_solve_wit_5_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_partition_xy_points_partial_solve_wit_5_pure_split_goal_2 : partition_xy_points_partial_solve_wit_5_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_partition_xy_points_partial_solve_wit_5_pure : partition_xy_points_partial_solve_wit_5_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_partition_xy_points_partial_solve_wit_5_pure_split_goal_1.
  - Goal_apply proof_of_partition_xy_points_partial_solve_wit_5_pure_split_goal_2.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_1_split_goal_1 : quicksort_xy_points_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  assert (OldPreH2 : (pointsf_finite out_4 )) by convex_facts.
  assert (OldPreH1 : ((Zlength (out_4)) = n_pre)) by convex_facts.
  assert (OldPreH17 : ((Zlength (out_2)) = n_pre)) by convex_facts.
  assert (OldPreH8 : ((Zlength (out_3)) = n_pre)) by convex_facts.
  convex_legacy_goal.

  assert (Hpart3 : pointf_xy_partitioned_at out_3 left_pre right_pre retval).
  {
    pose proof PreH6 as [Hlen23 _].
    eapply pointf_xy_partitioned_at_preserved_by_left__quicksort_top.
    - exact PreH5.
    - exact PreH17.
    - exact PreH6.
    - rewrite OldPreH17. lia.
    - exact PreH13.
  }
  assert (Hpart4 : pointf_xy_partitioned_at out_4 left_pre right_pre retval).
  {
    pose proof PreH2 as [Hlen34 _].
    eapply pointf_xy_partitioned_at_preserved_by_right__quicksort_top.
    - exact PreH1.
    - exact PreH17.
    - exact PreH2.
    - rewrite OldPreH8. lia.
    - exact Hpart3.
  }
  assert (Hsorted_left4 : pointf_xy_sorted_range out_4 left_pre (retval - 1)).
  {
    pose proof (proj1 (pointf_same_outside_range_unfold _ _ _ _) PreH2) as [Hlen34 Heq34].
    eapply pointf_xy_sorted_range_ext__quicksort_top.
    - exact PreH17.
    - rewrite Hlen34, OldPreH1. lia.
    - exact Hlen34.
    - intros k Hk. apply Heq34.
      + rewrite Hlen34, OldPreH1. lia.
      + left. lia.
    - exact PreH7.
  }
  eapply pointf_xy_sorted_range_from_partition__quicksort_top with (p := retval).
  - exact OldPreH2.
  - exact PreH17.
  - rewrite OldPreH1. lia.
  - exact Hpart4.
  - exact Hsorted_left4.
  - exact PreH3.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_1_split_goal_2 : quicksort_xy_points_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  assert (Hsame23_full : pointf_same_outside_range out_2 out_3 left_pre right_pre).
  {
    eapply (pointf_same_outside_range_weaken__quicksort_top
      out_2 out_3 left_pre (retval - 1) left_pre right_pre).
    - lia.
    - lia.
    - exact PreH6.
  }
  assert (Hsame34_full : pointf_same_outside_range out_3 out_4 left_pre right_pre).
  {
    eapply (pointf_same_outside_range_weaken__quicksort_top
      out_3 out_4 (retval + 1) right_pre left_pre right_pre).
    - lia.
    - lia.
    - exact PreH2.
  }
  eapply pointf_same_outside_range_trans__quicksort_top.
  - exact PreH12.
  - eapply pointf_same_outside_range_trans__quicksort_top;
    [exact Hsame23_full | exact Hsame34_full].
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_1_split_goal_3 : quicksort_xy_points_return_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  eapply Permutation_trans.
  - exact PreH11.
  - eapply Permutation_trans; [exact PreH5 | exact PreH1].
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_1 : quicksort_xy_points_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_quicksort_xy_points_return_wit_1_split_goal_1.
  - Goal_apply proof_of_quicksort_xy_points_return_wit_1_split_goal_2.
  - Goal_apply proof_of_quicksort_xy_points_return_wit_1_split_goal_3.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_2_split_goal_1 : quicksort_xy_points_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  assert (OldPreH2 : (pointsf_finite out_3 )) by convex_facts.
  assert (OldPreH1 : ((Zlength (out_3)) = n_pre)) by convex_facts.
  assert (OldPreH11 : ((Zlength (out_2)) = n_pre)) by convex_facts.
  convex_legacy_goal.

  assert (Hpart3 : pointf_xy_partitioned_at out_3 left_pre right_pre retval).
  {
    pose proof PreH2 as [Hlen23 _].
    eapply pointf_xy_partitioned_at_preserved_by_right__quicksort_top.
    - exact PreH1.
    - exact PreH14.
    - exact PreH2.
    - rewrite OldPreH11. lia.
    - exact PreH10.
  }
  eapply pointf_xy_sorted_range_from_partition__quicksort_top with (p := retval).
  - exact OldPreH2.
  - exact PreH14.
  - rewrite OldPreH1. lia.
  - exact Hpart3.
  - apply pointf_xy_sorted_range_base__quicksort_top; auto; lia.
  - exact PreH3.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_2_split_goal_2 : quicksort_xy_points_return_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  assert (Hsame23_full : pointf_same_outside_range out_2 out_3 left_pre right_pre).
  {
    eapply (pointf_same_outside_range_weaken__quicksort_top
      out_2 out_3 (retval + 1) right_pre left_pre right_pre).
    - lia.
    - lia.
    - exact PreH2.
  }
  eapply pointf_same_outside_range_trans__quicksort_top.
  - exact PreH9.
  - exact Hsame23_full.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_2_split_goal_3 : quicksort_xy_points_return_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  eapply Permutation_trans; [exact PreH8 | exact PreH1].
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_2 : quicksort_xy_points_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_quicksort_xy_points_return_wit_2_split_goal_1.
  - Goal_apply proof_of_quicksort_xy_points_return_wit_2_split_goal_2.
  - Goal_apply proof_of_quicksort_xy_points_return_wit_2_split_goal_3.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_3_split_goal_1 : quicksort_xy_points_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  assert (OldPreH2 : ((Zlength (out_3)) = n_pre)) by convex_facts.
  assert (OldPreH11 : ((Zlength (out_2)) = n_pre)) by convex_facts.
  assert (OldPreH3 : (pointsf_finite out_3 )) by convex_facts.
  convex_legacy_goal.

  assert (Hpart3 : pointf_xy_partitioned_at out_3 left_pre right_pre retval).
  {
    pose proof PreH3 as [Hlen23 _].
    eapply pointf_xy_partitioned_at_preserved_by_left__quicksort_top.
    - exact PreH2.
    - exact PreH14.
    - exact PreH3.
    - rewrite OldPreH11. lia.
    - exact PreH10.
  }
  eapply pointf_xy_sorted_range_from_partition__quicksort_top with (p := retval).
  - exact OldPreH3.
  - exact PreH14.
  - rewrite OldPreH2. lia.
  - exact Hpart3.
  - exact PreH4.
  - apply pointf_xy_sorted_range_base__quicksort_top; auto; lia.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_3_split_goal_2 : quicksort_xy_points_return_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  assert (Hsame23_full : pointf_same_outside_range out_2 out_3 left_pre right_pre).
  {
    eapply (pointf_same_outside_range_weaken__quicksort_top
      out_2 out_3 left_pre (retval - 1) left_pre right_pre).
    - lia.
    - lia.
    - exact PreH3.
  }
  eapply pointf_same_outside_range_trans__quicksort_top.
  - exact PreH9.
  - exact Hsame23_full.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_3_split_goal_3 : quicksort_xy_points_return_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  eapply Permutation_trans; [exact PreH8 | exact PreH2].
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_3 : quicksort_xy_points_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_quicksort_xy_points_return_wit_3_split_goal_1.
  - Goal_apply proof_of_quicksort_xy_points_return_wit_3_split_goal_2.
  - Goal_apply proof_of_quicksort_xy_points_return_wit_3_split_goal_3.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_4_split_goal_1 : quicksort_xy_points_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  apply pointf_xy_sorted_range_base__quicksort_top; auto; lia.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_4_split_goal_2 : quicksort_xy_points_return_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  apply pointf_same_outside_range_refl__swap_partition.
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_4_split_goal_3 : quicksort_xy_points_return_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
Qed.

Lemma proof_of_quicksort_xy_points_return_wit_4 : quicksort_xy_points_return_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_quicksort_xy_points_return_wit_4_split_goal_1.
  - Goal_apply proof_of_quicksort_xy_points_return_wit_4_split_goal_2.
  - Goal_apply proof_of_quicksort_xy_points_return_wit_4_split_goal_3.
Qed.

Lemma proof_of_quicksort_xy_points_partial_solve_wit_1_pure_split_goal_1 : quicksort_xy_points_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_quicksort_xy_points_partial_solve_wit_1_pure : quicksort_xy_points_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_quicksort_xy_points_partial_solve_wit_1_pure_split_goal_1.
Qed.

Lemma proof_of_quicksort_xy_points_partial_solve_wit_2_pure_split_goal_1 : quicksort_xy_points_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_quicksort_xy_points_partial_solve_wit_2_pure_split_goal_2 : quicksort_xy_points_partial_solve_wit_2_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_quicksort_xy_points_partial_solve_wit_2_pure_split_goal_3 : quicksort_xy_points_partial_solve_wit_2_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_quicksort_xy_points_partial_solve_wit_2_pure : quicksort_xy_points_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_quicksort_xy_points_partial_solve_wit_2_pure_split_goal_1.
  - Goal_apply proof_of_quicksort_xy_points_partial_solve_wit_2_pure_split_goal_2.
  - Goal_apply proof_of_quicksort_xy_points_partial_solve_wit_2_pure_split_goal_3.
Qed.

Lemma proof_of_quicksort_xy_points_partial_solve_wit_3_pure_split_goal_1 : quicksort_xy_points_partial_solve_wit_3_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_quicksort_xy_points_partial_solve_wit_3_pure_split_goal_2 : quicksort_xy_points_partial_solve_wit_3_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_quicksort_xy_points_partial_solve_wit_3_pure_split_goal_3 : quicksort_xy_points_partial_solve_wit_3_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_quicksort_xy_points_partial_solve_wit_3_pure : quicksort_xy_points_partial_solve_wit_3_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_quicksort_xy_points_partial_solve_wit_3_pure_split_goal_1.
  - Goal_apply proof_of_quicksort_xy_points_partial_solve_wit_3_pure_split_goal_2.
  - Goal_apply proof_of_quicksort_xy_points_partial_solve_wit_3_pure_split_goal_3.
Qed.

Lemma proof_of_quicksort_xy_points_partial_solve_wit_4_pure_split_goal_1 : quicksort_xy_points_partial_solve_wit_4_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_quicksort_xy_points_partial_solve_wit_4_pure_split_goal_2 : quicksort_xy_points_partial_solve_wit_4_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_quicksort_xy_points_partial_solve_wit_4_pure_split_goal_3 : quicksort_xy_points_partial_solve_wit_4_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_quicksort_xy_points_partial_solve_wit_4_pure : quicksort_xy_points_partial_solve_wit_4_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_quicksort_xy_points_partial_solve_wit_4_pure_split_goal_1.
  - Goal_apply proof_of_quicksort_xy_points_partial_solve_wit_4_pure_split_goal_2.
  - Goal_apply proof_of_quicksort_xy_points_partial_solve_wit_4_pure_split_goal_3.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_4_split_goal_1 : andrew_build_from_sorted_safety_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  build_lower_andrew_cross_finite Hcross.
  finish_andrew_cross_projection Hcross.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_4_split_goal_2 : andrew_build_from_sorted_safety_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  dump_pre_spatial.
  exact fp32_of_real_zero_finite__andrew.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_4 : andrew_build_from_sorted_safety_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_andrew_build_from_sorted_safety_wit_4_split_goal_1.
  - Goal_apply proof_of_andrew_build_from_sorted_safety_wit_4_split_goal_2.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_5_split_goal_1 : andrew_build_from_sorted_safety_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  build_lower_andrew_cross_finite Hcross.
  finish_andrew_cross_projection Hcross.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_5 : andrew_build_from_sorted_safety_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_andrew_build_from_sorted_safety_wit_5_split_goal_1.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_6_split_goal_1 : andrew_build_from_sorted_safety_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  build_lower_andrew_cross_finite Hcross.
  finish_andrew_cross_projection Hcross.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_6 : andrew_build_from_sorted_safety_wit_6.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_andrew_build_from_sorted_safety_wit_6_split_goal_1.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_7_split_goal_1 : andrew_build_from_sorted_safety_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  build_lower_andrew_cross_finite Hcross.
  finish_andrew_cross_projection Hcross.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_7 : andrew_build_from_sorted_safety_wit_7.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_andrew_build_from_sorted_safety_wit_7_split_goal_1.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_9_split_goal_1 : andrew_build_from_sorted_safety_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  build_lower_andrew_cross_finite Hcross.
  finish_andrew_cross_projection Hcross.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_9 : andrew_build_from_sorted_safety_wit_9.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_andrew_build_from_sorted_safety_wit_9_split_goal_1.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_12_split_goal_1 : andrew_build_from_sorted_safety_wit_12_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  build_lower_andrew_cross_finite Hcross.
  finish_andrew_cross_projection Hcross.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_12 : andrew_build_from_sorted_safety_wit_12.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_andrew_build_from_sorted_safety_wit_12_split_goal_1.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_13_split_goal_1 : andrew_build_from_sorted_safety_wit_13_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  build_lower_andrew_cross_finite Hcross.
  finish_andrew_cross_projection Hcross.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_13 : andrew_build_from_sorted_safety_wit_13.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_andrew_build_from_sorted_safety_wit_13_split_goal_1.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_15_split_goal_1 : andrew_build_from_sorted_safety_wit_15_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  build_lower_andrew_cross_finite Hcross.
  finish_andrew_cross_projection Hcross.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_15 : andrew_build_from_sorted_safety_wit_15.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_andrew_build_from_sorted_safety_wit_15_split_goal_1.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_32_split_goal_1 : andrew_build_from_sorted_safety_wit_32_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  build_upper_andrew_cross_finite Hcross.
  finish_andrew_cross_projection Hcross.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_32_split_goal_2 : andrew_build_from_sorted_safety_wit_32_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  dump_pre_spatial.
  exact fp32_of_real_zero_finite__andrew.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_32 : andrew_build_from_sorted_safety_wit_32.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_andrew_build_from_sorted_safety_wit_32_split_goal_1.
  - Goal_apply proof_of_andrew_build_from_sorted_safety_wit_32_split_goal_2.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_33_split_goal_1 : andrew_build_from_sorted_safety_wit_33_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  build_upper_andrew_cross_finite Hcross.
  finish_andrew_cross_projection Hcross.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_33 : andrew_build_from_sorted_safety_wit_33.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_andrew_build_from_sorted_safety_wit_33_split_goal_1.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_34_split_goal_1 : andrew_build_from_sorted_safety_wit_34_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  build_upper_andrew_cross_finite Hcross.
  finish_andrew_cross_projection Hcross.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_34 : andrew_build_from_sorted_safety_wit_34.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_andrew_build_from_sorted_safety_wit_34_split_goal_1.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_35_split_goal_1 : andrew_build_from_sorted_safety_wit_35_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  build_upper_andrew_cross_finite Hcross.
  finish_andrew_cross_projection Hcross.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_35 : andrew_build_from_sorted_safety_wit_35.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_andrew_build_from_sorted_safety_wit_35_split_goal_1.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_37_split_goal_1 : andrew_build_from_sorted_safety_wit_37_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  build_upper_andrew_cross_finite Hcross.
  finish_andrew_cross_projection Hcross.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_37 : andrew_build_from_sorted_safety_wit_37.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_andrew_build_from_sorted_safety_wit_37_split_goal_1.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_40_split_goal_1 : andrew_build_from_sorted_safety_wit_40_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  build_upper_andrew_cross_finite Hcross.
  finish_andrew_cross_projection Hcross.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_40 : andrew_build_from_sorted_safety_wit_40.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_andrew_build_from_sorted_safety_wit_40_split_goal_1.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_41_split_goal_1 : andrew_build_from_sorted_safety_wit_41_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  build_upper_andrew_cross_finite Hcross.
  finish_andrew_cross_projection Hcross.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_41 : andrew_build_from_sorted_safety_wit_41.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_andrew_build_from_sorted_safety_wit_41_split_goal_1.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_43_split_goal_1 : andrew_build_from_sorted_safety_wit_43_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  build_upper_andrew_cross_finite Hcross.
  finish_andrew_cross_projection Hcross.
Qed.

Lemma proof_of_andrew_build_from_sorted_safety_wit_43 : andrew_build_from_sorted_safety_wit_43.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_andrew_build_from_sorted_safety_wit_43_split_goal_1.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_1_split_goal_1 : andrew_build_from_sorted_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  convex_legacy_goal; unfold pointf_lower_scan_inv_legacy.
  repeat split; try lia.
  - simpl. constructor.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_1_split_goal_2 : andrew_build_from_sorted_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_1 : andrew_build_from_sorted_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_2 : andrew_build_from_sorted_entail_wit_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  assert (OldPreH14 : (pointf_lower_scan_inv_legacy sorted (sublist (0) (k) (hull_all_2)) i k )) by convex_facts.
  convex_legacy_goal.

  Exists (sublist 0 k hull_all_2) hull_all_2.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
    convex_legacy_goal; unfold pointf_lower_pop_inv_legacy.
    convex_legacy_goal; unfold pointf_lower_scan_inv_legacy in OldPreH14.
    destruct OldPreH14 as [[Hread_low Hread_high] [Htop [Hscan Hdone]]].
    repeat split; try lia.
    + exact Hscan.
    + constructor.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_3 : andrew_build_from_sorted_entail_wit_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  assert (OldPreH15 : (pointf_lower_pop_inv_legacy sorted before_2 (sublist (0) (k) (hull_all_2)) i k )) by convex_facts.
  convex_legacy_goal.

  Exists before_2 hull_all_2.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; auto; try lia.
  convex_legacy_goal; unfold pointf_lower_pop_inv_legacy in *.
  destruct OldPreH15 as [Hscan [Htrace Htop]].
  convex_legacy_goal; unfold pointf_lower_scan_inv_legacy in Hscan.
  destruct Hscan as [[Hread_low Hread_high] [Hbefore_len [Hscan_from Hdone]]].
  assert (Hsub_remove:
    sublist 0 (k - 1) hull_all_2 =
    removelast (sublist 0 k hull_all_2)).
  {
    rewrite (sublist_split 0 k (k - 1) hull_all_2) by lia.
    replace (sublist (k - 1) k hull_all_2)
      with (sublist (k - 1) ((k - 1) + 1) hull_all_2)
      by (f_equal; lia).
    rewrite (sublist_single default_pointf (k - 1) hull_all_2) by lia.
    rewrite removelast_last.
    reflexivity.
  }
  repeat split; try lia.
  + repeat split; try lia.
    all: try exact Hscan_from.
    all: try constructor.
  + rewrite Hsub_remove.
    eapply pointf_pop_trace_pop; eauto; try lia.
    unfold pointf_ccw, pointf_cross.
    simpl.
    unfold pointf_get_x, pointf_get_y in PreH1.
    unfold fp32_le in PreH1.
    unfold fp32_gt.
    intros Hgt.
    rewrite fp32_compare_zero_of_real__andrew_lower in Hgt.
    rewrite ?Zlength_sublist in Hgt by lia.
    rewrite !Znth_sublist0 in Hgt by lia.
    rewrite ?Zlength_sublist in Hgt by lia.
    repeat rewrite <- (Znth_indep hull_all_2 _ __default_PointF default_pointf) in Hgt by lia.
    rewrite <- (Znth_indep sorted i __default_PointF default_pointf) in Hgt by lia.
    replace (k - 0 - 1) with (k - 1) in Hgt by lia.
    replace (k - 0 - 2) with (k - 2) in Hgt by lia.
    rewrite Hgt in PreH1.
    simpl in PreH1.
    contradiction.
  + rewrite Zlength_sublist by lia. lia.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_4_1_split_goal_1 : andrew_build_from_sorted_entail_wit_4_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_4_1_split_goal_2 : andrew_build_from_sorted_entail_wit_4_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  eapply lower_scan_after_store_short__andrew_lower; eauto.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_4_1_split_goal_3 : andrew_build_from_sorted_entail_wit_4_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_4_1_split_goal_4 : andrew_build_from_sorted_entail_wit_4_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_4_1_split_goal_5 : andrew_build_from_sorted_entail_wit_4_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  repeat rewrite Zlength_replace_Znth. exact PreH13.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_4_1_split_goal_6 : andrew_build_from_sorted_entail_wit_4_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_4_1 : andrew_build_from_sorted_entail_wit_4_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_4_1_split_goal_1.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_4_1_split_goal_2.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_4_1_split_goal_3.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_4_1_split_goal_4.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_4_1_split_goal_5.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_4_1_split_goal_6.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_4_2_split_goal_1 : andrew_build_from_sorted_entail_wit_4_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  eapply lower_scan_after_store_ccw__andrew_lower; eauto.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_4_2_split_goal_2 : andrew_build_from_sorted_entail_wit_4_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_4_2_split_goal_3 : andrew_build_from_sorted_entail_wit_4_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_4_2_split_goal_4 : andrew_build_from_sorted_entail_wit_4_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  repeat rewrite Zlength_replace_Znth. exact PreH14.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_4_2_split_goal_5 : andrew_build_from_sorted_entail_wit_4_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_4_2 : andrew_build_from_sorted_entail_wit_4_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_4_2_split_goal_1.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_4_2_split_goal_2.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_4_2_split_goal_3.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_4_2_split_goal_4.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_4_2_split_goal_5.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_5_split_goal_1 : andrew_build_from_sorted_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  assert (OldPreH14 : (pointf_lower_scan_inv_legacy sorted (sublist (0) (k) (hull_all_2)) i k )) by convex_facts.
  convex_legacy_goal.

  convex_legacy_goal; unfold pointf_lower_scan_inv_legacy in OldPreH14.
  destruct OldPreH14 as [[Hread_low Hread_high] [Htop [Hscan Hdone]]].
  assert (Hi_eq : i = n_pre) by lia. subst i.
  assert (Hk_len : k = Zlength (sublist 0 k hull_all_2)) by lia.
  assert (Hlower_len :
    k = Zlength (sublist 0 k (sublist 0 k hull_all_2))).
  {
    rewrite Zlength_sublist.
    - lia.
    - rewrite Zlength_sublist by lia. lia.
  }
  convex_legacy_goal; unfold pointf_upper_scan_inv_legacy, pointf_upper_capacity.
  repeat split; try lia; try exact Hk_len; try exact Hlower_len;
    try solve [rewrite Zlength_sublist by lia; lia];
    try solve [let H := fresh in intro H; rewrite Zlength_sublist by lia; lia];
    try solve [intro Hbad; lia].
  - replace (sublist 0 k (sublist 0 k hull_all_2))
      with (sublist 0 k hull_all_2) by
      (symmetry; apply sublist_self; rewrite Zlength_sublist by lia; lia).
    replace (sublist 0 n_pre sorted) with sorted in Hscan.
    + exact Hscan.
    + rewrite sublist_self by lia. reflexivity.
  - replace (rev (sublist (n_pre - 2 + 1) (Zlength sorted - 1) sorted))
      with (@nil PointF).
    + replace (sublist 0 k (sublist 0 k hull_all_2))
        with (sublist 0 k hull_all_2) by
        (symmetry; apply sublist_self; rewrite Zlength_sublist by lia; lia).
      constructor.
    + symmetry.
      rewrite PreH8.
      replace (n_pre - 2 + 1) with (n_pre - 1) by lia.
      rewrite (@Zsublist_nil PointF sorted (n_pre - 1) (n_pre - 1)) by lia.
      reflexivity.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_5_split_goal_2 : andrew_build_from_sorted_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_5_split_goal_3 : andrew_build_from_sorted_entail_wit_5_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  rewrite Zlength_sublist.
  - lia.
  - rewrite Zlength_sublist by lia. lia.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_5 : andrew_build_from_sorted_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_5_split_goal_2.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_5_split_goal_3.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_6 : andrew_build_from_sorted_entail_wit_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  assert (OldPreH17 : (pointf_upper_scan_inv_legacy sorted lower_2 (sublist (0) (k) (hull_all_2)) (i + 1 ) k lower_n )) by convex_facts.
  convex_legacy_goal.

  assert (Hk_lt_2n : k < 2 * n_pre).
  {
    pose proof OldPreH17 as Hupper_inv.
    convex_legacy_goal; unfold pointf_upper_scan_inv_legacy in Hupper_inv.
    destruct Hupper_inv as
      [_ [Htop_inv [_ [_ [_ [_ [_ Hcap]]]]]]].
    unfold pointf_upper_capacity in Hcap.
    destruct Hcap as [_ [_ [Hstrict _]]].
    rewrite <- PreH11.
    rewrite Htop_inv.
    apply Hstrict. lia.
  }
  Exists (sublist 0 k hull_all_2) hull_all_2 lower_2.
  assert (Hlower_len :
    Zlength (sublist 0 lower_n (sublist 0 k hull_all_2)) = lower_n).
  {
    rewrite Zlength_sublist by
      (rewrite Zlength_sublist by lia; lia).
    lia.
  }
  assert (Hlower_norm :
    sublist 0 (Zlength (sublist 0 lower_n (sublist 0 k hull_all_2)))
      (sublist 0 k hull_all_2) = lower_2).
  {
    rewrite Hlower_len.
    symmetry. exact PreH10.
  }
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; auto; try lia;
      try solve [rewrite Zlength_sublist by lia; lia];
      try solve [rewrite Zlength_sublist by
        (rewrite Zlength_sublist by lia; lia); lia].
    try solve
      [ rewrite Hlower_len;
        rewrite Zlength_sublist by
          (rewrite Zlength_sublist by lia; lia);
        lia ].
    replace (sublist 0
      (Zlength (sublist 0 lower_n (sublist 0 k hull_all_2)))
      (sublist 0 k hull_all_2)) with lower_2 by
      (symmetry; exact Hlower_norm).
    replace (Zlength (sublist 0 lower_n (sublist 0 k hull_all_2)))
      with lower_n by (symmetry; exact Hlower_len).
    convex_legacy_goal; unfold pointf_upper_pop_inv_legacy.
    replace (Zlength (sublist 0 k hull_all_2)) with k by
      (rewrite Zlength_sublist by lia; lia).
    split; [exact OldPreH17 |].
    split; [constructor |].
    split; [reflexivity |].
    split; [exact PreH10 | lia].
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_7 : andrew_build_from_sorted_entail_wit_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  assert (OldPreH18 : (pointf_upper_pop_inv_legacy sorted lower_2 before_2 (sublist (0) (k) (hull_all_2)) i k lower_n )) by convex_facts.
  convex_legacy_goal.

  Exists before_2 hull_all_2 lower_2.
  assert (Hsub_remove:
    sublist 0 (k - 1) hull_all_2 =
    removelast (sublist 0 k hull_all_2)).
  {
    rewrite (sublist_split 0 k (k - 1) hull_all_2) by lia.
    replace (sublist (k - 1) k hull_all_2)
      with (sublist (k - 1) ((k - 1) + 1) hull_all_2) by
      (f_equal; lia).
    rewrite sublist_single with (d := default_pointf) by lia.
    rewrite removelast_last by (rewrite Zlength_sublist by lia; lia).
    reflexivity.
  }
  assert (Hlower_prefix:
    sublist 0 lower_n (sublist 0 (k - 1) hull_all_2) = lower_2).
  {
    rewrite PreH11.
    rewrite Zsublist_Zsublist00 by lia.
    rewrite Zsublist_Zsublist00 by lia.
    reflexivity.
  }
  assert (Hnccw :
    ~ pointf_ccw
        (Znth (Zlength (sublist 0 k hull_all_2) - 2)
          (sublist 0 k hull_all_2) default_pointf)
        (Znth (Zlength (sublist 0 k hull_all_2) - 1)
          (sublist 0 k hull_all_2) default_pointf)
        (Znth i sorted default_pointf)).
  {
    rewrite Zlength_sublist by lia.
    rewrite !Znth_sublist by lia.
    replace (k - 2 + 0) with (k - 2) by lia.
    replace (k - 1 + 0) with (k - 1) by lia.
    unfold pointf_ccw, pointf_cross.
    repeat rewrite (Znth_indep hull_all_2 _ default_pointf __default_PointF) by lia.
    rewrite (Znth_indep sorted i default_pointf __default_PointF) by lia.
    replace (k - 0 - 2 + 0) with (k - 2) by lia.
    replace (k - 0 - 1 + 0) with (k - 1) by lia.
    unfold pointf_get_x, pointf_get_y in PreH1.
    unfold fp32_le in PreH1.
    unfold fp32_gt.
    rewrite fp32_compare_zero_of_real__andrew_upper.
    match type of PreH1 with
    | context [fp32_compare ?e ?z] =>
      intro Hgt; rewrite Hgt in PreH1; exact PreH1
    end.
  }
  assert (Hlower_len :
    Zlength (sublist 0 lower_n (sublist 0 k hull_all_2)) = lower_n).
  {
    rewrite Zlength_sublist by
      (rewrite Zlength_sublist by lia; lia).
    lia.
  }
  assert (Hlower_norm :
    sublist 0 (Zlength (sublist 0 lower_n (sublist 0 k hull_all_2)))
      (sublist 0 (k - 1) hull_all_2) = lower_2).
  {
    rewrite Hlower_len.
    exact Hlower_prefix.
  }
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; auto; try lia;
      try solve [rewrite Zlength_sublist by lia; lia];
      try solve [rewrite Zlength_sublist by
        (rewrite Zlength_sublist by lia; lia); lia].
    try solve
      [ rewrite Hlower_len;
        rewrite Zlength_sublist by
          (rewrite Zlength_sublist by lia; lia);
        lia ].
    replace (sublist 0
      (Zlength (sublist 0 lower_n (sublist 0 k hull_all_2)))
      (sublist 0 (k - 1) hull_all_2)) with lower_2 by
      (symmetry; exact Hlower_norm).
    replace (Zlength (sublist 0 lower_n (sublist 0 k hull_all_2)))
      with lower_n by (symmetry; exact Hlower_len).
    convex_legacy_goal; unfold pointf_upper_pop_inv_legacy in *.
    destruct OldPreH18 as [Hscan [Htrace [Htop [Hlower Hle]]]].
    replace (Zlength (sublist 0 (k - 1) hull_all_2)) with (k - 1) by
      (rewrite Zlength_sublist by lia; lia).
    split.
    + exact Hscan.
    + split.
      * rewrite Hsub_remove.
        eapply pointf_upper_pop_trace_pop; eauto; try lia.
      * split.
        -- lia.
        -- split; [symmetry; exact Hlower_prefix | lia].
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_8_1_split_goal_1 : andrew_build_from_sorted_entail_wit_8_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  assert (OldPreH17 : (pointf_upper_pop_inv_legacy sorted lower_2 before (sublist (0) (k) (hull_all_2)) i k lower_n )) by convex_facts.
  convex_legacy_goal.

  set (new_all :=
    replace_Znth k
      (pointf_mk
        (pointf_get_x
          (Znth k
            (replace_Znth k
              (pointf_mk (pointf_get_x (Znth i sorted __default_PointF))
                (pointf_get_y (Znth k hull_all_2 __default_PointF))) hull_all_2)
            __default_PointF))
        (pointf_get_y (Znth i sorted __default_PointF)))
      (replace_Znth k
        (pointf_mk (pointf_get_x (Znth i sorted __default_PointF))
          (pointf_get_y (Znth k hull_all_2 __default_PointF))) hull_all_2)).
  assert (Hprefix :
    sublist 0 (k + 1) new_all =
    sublist 0 k hull_all_2 ++ Znth i sorted default_pointf :: nil).
  {
    subst new_all.
    apply upper_store_prefix__andrew_upper; lia.
  }
  assert (Hlower_new :
    sublist 0 lower_n (sublist 0 (k + 1) new_all) = lower_2).
  {
    rewrite Hprefix.
    rewrite (sublist_app_prefix__andrew_upper
      (sublist 0 k hull_all_2) (Znth i sorted default_pointf) lower_n).
    2:{ rewrite Zlength_sublist by lia; lia. }
    rewrite PreH10.
    reflexivity.
  }
  assert (Hinv :
    pointf_upper_scan_inv_legacy sorted lower_2
      (sublist 0 k hull_all_2 ++ Znth i sorted default_pointf :: nil)
      i (k + 1) lower_n).
  {
    eapply pointf_upper_scan_inv_after_append__andrew_upper
      with (before := before) (top := k).
    - rewrite PreH11. lia.
    - exact OldPreH17.
    - apply pointf_upper_pop_until_boundary.
      rewrite Zlength_sublist by lia. lia.
  }
  split_pures; auto; try lia;
    try solve [subst new_all; rewrite Zlength_replace_Znth; lia];
    try solve [rewrite Zlength_sublist by lia; lia].
  rewrite Hlower_new.
  rewrite Hprefix.
  replace ((i - 1) + 1) with i by lia.
  exact Hinv.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_8_1_split_goal_2 : andrew_build_from_sorted_entail_wit_8_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_8_1_split_goal_3 : andrew_build_from_sorted_entail_wit_8_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_8_1_split_goal_4 : andrew_build_from_sorted_entail_wit_8_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  repeat rewrite Zlength_replace_Znth. lia.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_8_1_split_goal_5 : andrew_build_from_sorted_entail_wit_8_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_8_1_split_goal_6 : andrew_build_from_sorted_entail_wit_8_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  rewrite Zlength_sublist.
  - lia.
  - rewrite Zlength_sublist.
    + lia.
    + repeat rewrite Zlength_replace_Znth. lia.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_8_1 : andrew_build_from_sorted_entail_wit_8_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_8_1_split_goal_1.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_8_1_split_goal_2.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_8_1_split_goal_3.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_8_1_split_goal_4.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_8_1_split_goal_5.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_8_1_split_goal_6.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_8_2_split_goal_1 : andrew_build_from_sorted_entail_wit_8_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_8_2_split_goal_2 : andrew_build_from_sorted_entail_wit_8_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_8_2_split_goal_3 : andrew_build_from_sorted_entail_wit_8_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  assert (OldPreH18 : (pointf_upper_pop_inv_legacy sorted lower_2 before (sublist (0) (k) (hull_all_2)) i k lower_n )) by convex_facts.
  convex_legacy_goal.

  set (new_all :=
    replace_Znth k
      (pointf_mk
        (pointf_get_x
          (Znth k
            (replace_Znth k
              (pointf_mk (pointf_get_x (Znth i sorted __default_PointF))
                (pointf_get_y (Znth k hull_all_2 __default_PointF))) hull_all_2)
            __default_PointF))
        (pointf_get_y (Znth i sorted __default_PointF)))
      (replace_Znth k
        (pointf_mk (pointf_get_x (Znth i sorted __default_PointF))
          (pointf_get_y (Znth k hull_all_2 __default_PointF))) hull_all_2)).
  assert (Hprefix :
    sublist 0 (k + 1) new_all =
    sublist 0 k hull_all_2 ++ Znth i sorted default_pointf :: nil).
  {
    subst new_all.
    apply upper_store_prefix__andrew_upper; lia.
  }
  assert (Hlower_new :
    sublist 0 lower_n (sublist 0 (k + 1) new_all) = lower_2).
  {
    rewrite Hprefix.
    rewrite (sublist_app_prefix__andrew_upper
      (sublist 0 k hull_all_2) (Znth i sorted default_pointf) lower_n).
    2:{ rewrite Zlength_sublist by lia; lia. }
    rewrite PreH11.
    reflexivity.
  }
  assert (Hccw :
    pointf_ccw
      (Znth (Zlength (sublist 0 k hull_all_2) - 2)
        (sublist 0 k hull_all_2) default_pointf)
      (Znth (Zlength (sublist 0 k hull_all_2) - 1)
        (sublist 0 k hull_all_2) default_pointf)
      (Znth i sorted default_pointf)).
  {
    unfold pointf_ccw, pointf_cross.
    rewrite ?Zlength_sublist by lia.
    rewrite !Znth_sublist0 by lia.
    repeat rewrite <- (Znth_indep hull_all_2 _ __default_PointF default_pointf)
      by lia.
    rewrite <- (Znth_indep sorted i __default_PointF default_pointf) by lia.
    unfold fp32_gt in *.
    rewrite fp32_compare_zero_of_real__andrew_upper.
    replace (k - 0 - 2) with (k - 2) by lia.
    replace (k - 0 - 1) with (k - 1) by lia.
    exact PreH1.
  }
  assert (Hinv :
    pointf_upper_scan_inv_legacy sorted lower_2
      (sublist 0 k hull_all_2 ++ Znth i sorted default_pointf :: nil)
      i (k + 1) lower_n).
  {
    eapply pointf_upper_scan_inv_after_append__andrew_upper
      with (before := before) (top := k).
    - rewrite PreH12. lia.
    - exact OldPreH18.
    - apply pointf_upper_pop_until_ccw.
      + rewrite Zlength_sublist by lia. lia.
      + rewrite Zlength_sublist by lia. lia.
      + exact Hccw.
  }
  split_pures; auto; try lia;
    try solve [subst new_all; rewrite Zlength_replace_Znth; lia];
    try solve [rewrite Zlength_sublist by lia; lia].
  rewrite Hlower_new.
  rewrite Hprefix.
  replace ((i - 1) + 1) with i by lia.
  exact Hinv.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_8_2_split_goal_4 : andrew_build_from_sorted_entail_wit_8_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_8_2_split_goal_5 : andrew_build_from_sorted_entail_wit_8_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_8_2_split_goal_6 : andrew_build_from_sorted_entail_wit_8_2_split_goal_6.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  repeat rewrite Zlength_replace_Znth. lia.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_8_2_split_goal_7 : andrew_build_from_sorted_entail_wit_8_2_split_goal_7.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_8_2_split_goal_8 : andrew_build_from_sorted_entail_wit_8_2_split_goal_8.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  rewrite Zlength_sublist.
  - lia.
  - rewrite Zlength_sublist.
    + lia.
    + repeat rewrite Zlength_replace_Znth. lia.
Qed.

Lemma proof_of_andrew_build_from_sorted_entail_wit_8_2 : andrew_build_from_sorted_entail_wit_8_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_8_2_split_goal_1.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_8_2_split_goal_2.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_8_2_split_goal_3.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_8_2_split_goal_4.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_8_2_split_goal_5.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_8_2_split_goal_6.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_8_2_split_goal_7.
  - Goal_apply proof_of_andrew_build_from_sorted_entail_wit_8_2_split_goal_8.
Qed.

Lemma proof_of_andrew_build_from_sorted_return_wit_1_split_goal_1 : andrew_build_from_sorted_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  assert (OldPreH17 : (pointf_upper_scan_inv_legacy sorted lower (sublist (0) (k) (hull_all_2)) (i + 1 ) k lower_n )) by convex_facts.
  convex_legacy_goal.

  assert (Hread0 : i + 1 = 0) by lia.
  replace (sublist 0 (k - 1) hull_all_2)
    with (pointf_drop_last (sublist 0 k hull_all_2)).
  2:{
    apply pointf_drop_last_sublist_prefix__andrew_upper.
    rewrite PreH16. lia.
  }
  eapply upper_scan_final_is_andrew_hull__andrew_upper.
  - rewrite PreH11. lia.
  - exact PreH15.
  - replace (sublist (i + 1) k hull_all_2)
      with (sublist 0 k hull_all_2) by
      (replace (i + 1) with 0 by lia; reflexivity).
    pose proof OldPreH17 as Hfinal_inv.
    replace (i + 1) with 0 in Hfinal_inv by lia.
    exact Hfinal_inv.
Qed.

Lemma proof_of_andrew_build_from_sorted_return_wit_1_split_goal_2 : andrew_build_from_sorted_return_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.

  rewrite Zlength_sublist by lia. lia.
Qed.

Lemma proof_of_andrew_build_from_sorted_return_wit_1 : andrew_build_from_sorted_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_andrew_build_from_sorted_return_wit_1_split_goal_1.
  - Goal_apply proof_of_andrew_build_from_sorted_return_wit_1_split_goal_2.
Qed.

Lemma proof_of_convex_hull_float_return_wit_1_split_goal_1 : convex_hull_float_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  convex_prepare.
  convex_legacy_goal.
  eapply is_andrew_hull_float_permutation_input__quicksort_top.
  - exact PreH4.
  - convex_facts.
  - convex_facts.
Qed.

Lemma proof_of_convex_hull_float_return_wit_1 : convex_hull_float_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_convex_hull_float_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_convex_hull_float_partial_solve_wit_1_pure_split_goal_1 : convex_hull_float_partial_solve_wit_1_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_convex_hull_float_partial_solve_wit_1_pure : convex_hull_float_partial_solve_wit_1_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_convex_hull_float_partial_solve_wit_1_pure_split_goal_1.
Qed.

Lemma proof_of_convex_hull_float_partial_solve_wit_2_pure_split_goal_1 : convex_hull_float_partial_solve_wit_2_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_convex_hull_float_partial_solve_wit_2_pure_split_goal_2 : convex_hull_float_partial_solve_wit_2_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_convex_hull_float_partial_solve_wit_2_pure_split_goal_3 : convex_hull_float_partial_solve_wit_2_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_convex_hull_float_partial_solve_wit_2_pure_split_goal_4 : convex_hull_float_partial_solve_wit_2_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(int_auto).
  all: convex_facts.
Qed.

Lemma proof_of_convex_hull_float_partial_solve_wit_2_pure_split_goal_5 : convex_hull_float_partial_solve_wit_2_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(int_auto).
  dump_pre_spatial.
  unfold pointf_xy_sorted.
  replace (Zlength out) with n_pre.
  - exact PreH5.
  - destruct PreH4 as [Hlength _]; lia.
Qed.

Lemma proof_of_convex_hull_float_partial_solve_wit_2_pure : convex_hull_float_partial_solve_wit_2_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_convex_hull_float_partial_solve_wit_2_pure_split_goal_1.
  - Goal_apply proof_of_convex_hull_float_partial_solve_wit_2_pure_split_goal_2.
  - Goal_apply proof_of_convex_hull_float_partial_solve_wit_2_pure_split_goal_3.
  - Goal_apply proof_of_convex_hull_float_partial_solve_wit_2_pure_split_goal_4.
  - Goal_apply proof_of_convex_hull_float_partial_solve_wit_2_pure_split_goal_5.
Qed.
