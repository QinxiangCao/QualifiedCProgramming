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
From SimpleC.EE.LLM_bench.Algorithms.edit_strings Require Import edit_strings_goal.
From SimpleC.EE.LLM_bench.Algorithms.edit_strings Require Import edit_strings_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.edit_strings.edit_strings_lib.
Local Open Scope sac.
Local Opaque IntArray.undef_full IntArray.undef_seg IntArray.full IntArray.seg.


Require Import AUXLib.MonotonicList.
Import ListNotations.
Local Open Scope list_scope.
Ltac edit_cancel :=
  elim_emp; sepcon_right_assoc;
  repeat match goal with
  | |- ?P ** _ |-- _ => progress (cancel P)
  | |- ?P |-- ?P => apply derivable1_refl
  end;
  try cancel.

Ltac edit_split_pures :=
  repeat match goal with |- _ |-- ?A && ?B =>
    _assert_pure A; _assert_pure B; apply _derivable1_andp_intros end.
Ltac edit_observe :=
  repeat match goal with H : Forall (eq 0) ?xs |- _ |-- ?Q =>
    match Q with context [Znth ?i xs 0] => rewrite (edit_zero_read xs i H) end end;
  try match goal with Hlo : Forall (Z.le ?lo) ?xs, Hhi : Forall (Z.ge ?hi) ?xs |- _ |-- ?Q =>
    match Q with context [Znth ?i xs 0] =>
      let Hb := fresh "Hread_bounds" in
      pose proof (edit_bounded_read xs i lo hi Hlo Hhi ltac:(lia)) as Hb end end.

Lemma proof_of_max_edit_string_matches_safety_wit_14 : max_edit_string_matches_safety_wit_14.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  edit_observe.
  edit_split_pures; dump_pre_spatial; lia.
Qed. 

Lemma proof_of_max_edit_string_matches_safety_wit_16 : max_edit_string_matches_safety_wit_16.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  edit_observe.
  edit_split_pures; dump_pre_spatial; lia.
Qed. 

Lemma proof_of_max_edit_string_matches_safety_wit_26 : max_edit_string_matches_safety_wit_26.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  edit_observe.
  edit_split_pures; dump_pre_spatial; lia.
Qed. 

Lemma proof_of_max_edit_string_matches_safety_wit_27 : max_edit_string_matches_safety_wit_27.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  edit_observe.
  edit_split_pures; dump_pre_spatial; lia.
Qed. 

Lemma proof_of_max_edit_string_matches_safety_wit_35 : max_edit_string_matches_safety_wit_35.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  edit_observe.
  edit_split_pures; dump_pre_spatial; lia.
Qed. 

Lemma proof_of_max_edit_string_matches_safety_wit_37 : max_edit_string_matches_safety_wit_37.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  edit_observe.
  edit_split_pures; dump_pre_spatial; lia.
Qed. 

Lemma proof_of_max_edit_string_matches_safety_wit_47 : max_edit_string_matches_safety_wit_47.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  edit_observe.
  edit_split_pures; dump_pre_spatial; lia.
Qed. 

Lemma proof_of_max_edit_string_matches_safety_wit_48 : max_edit_string_matches_safety_wit_48.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  edit_observe.
  edit_split_pures; dump_pre_spatial; lia.
Qed. 

Lemma proof_of_max_edit_string_matches_safety_wit_56 : max_edit_string_matches_safety_wit_56.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  edit_observe.
  edit_split_pures; dump_pre_spatial; lia.
Qed. 

Lemma proof_of_max_edit_string_matches_safety_wit_57 : max_edit_string_matches_safety_wit_57.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  edit_observe.
  edit_split_pures; dump_pre_spatial; lia.
Qed. 

Lemma proof_of_max_edit_string_matches_safety_wit_64 : max_edit_string_matches_safety_wit_64.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  edit_observe.
  edit_split_pures; dump_pre_spatial; lia.
Qed. 

Lemma proof_of_max_edit_string_matches_safety_wit_65 : max_edit_string_matches_safety_wit_65.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  edit_observe.
  edit_split_pures; dump_pre_spatial; lia.
Qed. 

Lemma proof_of_max_edit_string_matches_safety_wit_66 : max_edit_string_matches_safety_wit_66.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  edit_observe.
  edit_split_pures; dump_pre_spatial; lia.
Qed. 

Lemma proof_of_max_edit_string_matches_safety_wit_67 : max_edit_string_matches_safety_wit_67.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  edit_observe.
  edit_split_pures; dump_pre_spatial; lia.
Qed. 

Lemma proof_of_max_edit_string_matches_safety_wit_76 : max_edit_string_matches_safety_wit_76.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  edit_observe.
  edit_split_pures; dump_pre_spatial; lia.
Qed. 

Lemma proof_of_max_edit_string_matches_safety_wit_77 : max_edit_string_matches_safety_wit_77.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  edit_observe.
  edit_split_pures; dump_pre_spatial; lia.
Qed. 

Lemma proof_of_max_edit_string_matches_safety_wit_78 : max_edit_string_matches_safety_wit_78.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  edit_observe.
  edit_split_pures; dump_pre_spatial; lia.
Qed. 

Lemma proof_of_max_edit_string_matches_safety_wit_79 : max_edit_string_matches_safety_wit_79.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  edit_observe.
  edit_split_pures; dump_pre_spatial; lia.
Qed. 

Lemma proof_of_max_edit_string_matches_safety_wit_80 : max_edit_string_matches_safety_wit_80.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  edit_observe.
  edit_split_pures; dump_pre_spatial; lia.
Qed. 

Lemma proof_of_max_edit_string_matches_safety_wit_81 : max_edit_string_matches_safety_wit_81.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  edit_observe.
  edit_split_pures; dump_pre_spatial; lia.
Qed. 

Lemma proof_of_max_edit_string_matches_safety_wit_82 : max_edit_string_matches_safety_wit_82.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  edit_observe.
  edit_split_pures; dump_pre_spatial; lia.
Qed. 

Lemma proof_of_max_edit_string_matches_safety_wit_83 : max_edit_string_matches_safety_wit_83.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  edit_observe.
  edit_split_pures; dump_pre_spatial; lia.
Qed. 

Lemma proof_of_max_edit_string_matches_entail_wit_1_split_goal_1 : max_edit_string_matches_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: constructor.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_1_split_goal_2 : max_edit_string_matches_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: constructor.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_1_split_goal_3 : max_edit_string_matches_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: constructor.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_1_split_goal_4 : max_edit_string_matches_entail_wit_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: constructor.
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_1 : max_edit_string_matches_entail_wit_1.
Proof.
  unfold max_edit_string_matches_entail_wit_1; right; intros.
  remember 100000 as capacity eqn:Hcapacity.
  sep_apply_l_atomic (IntArray.undef_full_split_to_undef_seg (&("seg1")) n_pre capacity ltac:(lia)).
  sep_apply_l_atomic (IntArray.undef_full_split_to_undef_seg (&("seg2")) n_pre capacity ltac:(lia)).
  sep_apply_l_atomic (IntArray.undef_full_split_to_undef_seg (&("cnt10")) n_pre capacity ltac:(lia)).
  sep_apply_l_atomic (IntArray.undef_full_split_to_undef_seg (&("cnt11")) n_pre capacity ltac:(lia)).
  sep_apply_l_atomic (IntArray.undef_full_split_to_undef_seg (&("cnt20")) n_pre capacity ltac:(lia)).
  sep_apply_l_atomic (IntArray.undef_full_split_to_undef_seg (&("cnt21")) n_pre capacity ltac:(lia)).
  sep_apply_l_atomic (IntArray.undef_seg_to_undef_full (&("seg1")) 0 n_pre).
  sep_apply_l_atomic (IntArray.undef_seg_to_undef_full (&("seg2")) 0 n_pre).
  rewrite ?Z.mul_0_l, ?Z.add_0_r, ?Z.sub_0_r.
  split_pure_spatial; [edit_cancel | edit_split_pures; dump_pre_spatial; constructor].
Qed. 

Lemma proof_of_max_edit_string_matches_entail_wit_2_split_goal_1 : max_edit_string_matches_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Forall_app. split; [assumption|repeat constructor].
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_2_split_goal_2 : max_edit_string_matches_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Forall_app. split; [assumption|repeat constructor].
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_2_split_goal_3 : max_edit_string_matches_entail_wit_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Forall_app. split; [assumption|repeat constructor].
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_2_split_goal_4 : max_edit_string_matches_entail_wit_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Forall_app. split; [assumption|repeat constructor].
Qed.

Lemma proof_of_max_edit_string_matches_entail_wit_2 : max_edit_string_matches_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_2_split_goal_2.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_2_split_goal_3.
  - Goal_apply proof_of_max_edit_string_matches_entail_wit_2_split_goal_4.

Qed. 

Lemma proof_of_max_edit_string_matches_entail_wit_3_1 : max_edit_string_matches_entail_wit_3_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (IntArray.full_Zlength (&("cnt10")) i (replace_Znth (0) (((Znth (0 - 0 ) c10_2 0) + 1 )) (c10_2))). Intros_p Harray_length_0.
  prop_apply (IntArray.full_Zlength s1_pre n_pre s1_l). Intros_p Harray_length_1.
  prop_apply (IntArray.full_Zlength s2_pre n_pre s2_l). Intros_p Harray_length_2.
  prop_apply (IntArray.full_Zlength t1_pre n_pre t1_l). Intros_p Harray_length_3.
  prop_apply (IntArray.full_Zlength t2_pre n_pre t2_l). Intros_p Harray_length_4.
  prop_apply (IntArray.seg_Zlength (&("cnt11")) 0 i c11_2). Intros_p Harray_length_5.
  prop_apply (IntArray.seg_Zlength (&("cnt20")) 0 i c20_2). Intros_p Harray_length_6.
  prop_apply (IntArray.seg_Zlength (&("cnt21")) 0 i c21_2). Intros_p Harray_length_7.
  repeat rewrite Zlength_replace_Znth in *;
  repeat rewrite Zlength_app in *;
  repeat rewrite Zlength_cons in *;
  repeat rewrite Zlength_nil in *;
  repeat rewrite Z.sub_0_r in *.
  assert (Hi_end : i = n_pre) by lia. rewrite Hi_end in *. clear i Hi_end.
  assert (Hbuild : EditBuildMeaning s1_l t1_l n_pre 1 [0] (replace_Znth 0 (Znth 0 c10_2 0 + 1) c10_2) c11_2).
  { eapply edit_build_first_zero; eauto; lia. }
  pose proof (edit_counts_bounds s1_l t1_l n_pre 1 (replace_Znth 0 (Znth 0 c10_2 0 + 1) c10_2) c11_2
    ltac:(lia) ltac:(lia) ltac:(rewrite ?Zlength_replace_Znth; lia)
    ltac:(rewrite ?Zlength_replace_Znth; lia) (proj2 Hbuild)) as [[Hzlo Hzhi] [Holo Hohi]].
  pose proof (edit_zero_bounds c20_2 n_pre ltac:(lia) ltac:(eassumption)) as [H20lo H20hi].
  pose proof (edit_zero_bounds c21_2 n_pre ltac:(lia) ltac:(eassumption)) as [H21lo H21hi].
  Exists [0] c21_2 c20_2 c11_2 (replace_Znth 0 (Znth 0 c10_2 0 + 1) c10_2).
  split_pure_spatial.
  - sep_apply (IntArray.seg_single (&("seg1")) 0 0).
    replace (0 + 1) with 1 by lia.
    sep_apply (IntArray.seg_to_full (&("cnt11")) 0 n_pre c11_2).
    replace ((&("cnt11")) + 0 * sizeof(INT)) with (&("cnt11")) by lia.
    sep_apply (IntArray.seg_to_full (&("cnt20")) 0 n_pre c20_2).
    replace ((&("cnt20")) + 0 * sizeof(INT)) with (&("cnt20")) by lia.
    sep_apply (IntArray.seg_to_full (&("cnt21")) 0 n_pre c21_2).
    replace ((&("cnt21")) + 0 * sizeof(INT)) with (&("cnt21")) by lia.
    replace (n_pre - 0) with n_pre by lia.
    edit_cancel.
  - edit_split_pures; dump_pre_spatial; try assumption; try congruence; lia.

Qed. 

Lemma proof_of_max_edit_string_matches_entail_wit_3_2 : max_edit_string_matches_entail_wit_3_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (IntArray.full_Zlength (&("cnt11")) i (replace_Znth (0) (((Znth (0 - 0 ) c11_2 0) + 1 )) (c11_2))). Intros_p Harray_length_0.
  prop_apply (IntArray.full_Zlength s1_pre n_pre s1_l). Intros_p Harray_length_1.
  prop_apply (IntArray.full_Zlength s2_pre n_pre s2_l). Intros_p Harray_length_2.
  prop_apply (IntArray.full_Zlength t1_pre n_pre t1_l). Intros_p Harray_length_3.
  prop_apply (IntArray.full_Zlength t2_pre n_pre t2_l). Intros_p Harray_length_4.
  prop_apply (IntArray.seg_Zlength (&("cnt10")) 0 i c10_2). Intros_p Harray_length_5.
  prop_apply (IntArray.seg_Zlength (&("cnt20")) 0 i c20_2). Intros_p Harray_length_6.
  prop_apply (IntArray.seg_Zlength (&("cnt21")) 0 i c21_2). Intros_p Harray_length_7.
  repeat rewrite Zlength_replace_Znth in *;
  repeat rewrite Zlength_app in *;
  repeat rewrite Zlength_cons in *;
  repeat rewrite Zlength_nil in *;
  repeat rewrite Z.sub_0_r in *.
  assert (Hi_end : i = n_pre) by lia. rewrite Hi_end in *. clear i Hi_end.
  assert (Hbuild : EditBuildMeaning s1_l t1_l n_pre 1 [0] c10_2 (replace_Znth 0 (Znth 0 c11_2 0 + 1) c11_2)).
  { eapply edit_build_first_one; eauto; lia. }
  pose proof (edit_counts_bounds s1_l t1_l n_pre 1 c10_2 (replace_Znth 0 (Znth 0 c11_2 0 + 1) c11_2)
    ltac:(lia) ltac:(lia) ltac:(rewrite ?Zlength_replace_Znth; lia)
    ltac:(rewrite ?Zlength_replace_Znth; lia) (proj2 Hbuild)) as [[Hzlo Hzhi] [Holo Hohi]].
  pose proof (edit_zero_bounds c20_2 n_pre ltac:(lia) ltac:(eassumption)) as [H20lo H20hi].
  pose proof (edit_zero_bounds c21_2 n_pre ltac:(lia) ltac:(eassumption)) as [H21lo H21hi].
  Exists [0] c21_2 c20_2 (replace_Znth 0 (Znth 0 c11_2 0 + 1) c11_2) c10_2.
  split_pure_spatial.
  - sep_apply (IntArray.seg_single (&("seg1")) 0 0).
    replace (0 + 1) with 1 by lia.
    sep_apply (IntArray.seg_to_full (&("cnt10")) 0 n_pre c10_2).
    replace ((&("cnt10")) + 0 * sizeof(INT)) with (&("cnt10")) by lia.
    sep_apply (IntArray.seg_to_full (&("cnt20")) 0 n_pre c20_2).
    replace ((&("cnt20")) + 0 * sizeof(INT)) with (&("cnt20")) by lia.
    sep_apply (IntArray.seg_to_full (&("cnt21")) 0 n_pre c21_2).
    replace ((&("cnt21")) + 0 * sizeof(INT)) with (&("cnt21")) by lia.
    replace (n_pre - 0) with n_pre by lia.
    edit_cancel.
  - edit_split_pures; dump_pre_spatial; try assumption; try congruence; lia.

Qed. 

Lemma proof_of_max_edit_string_matches_entail_wit_4_1 : max_edit_string_matches_entail_wit_4_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (IntArray.seg_Zlength (&("seg1")) 0 (i + 1 ) (app (sg1) ((cons ((Znth ((i - 1 ) - 0 ) sg1 0)) ((@nil Z)))))). Intros_p Harray_length_0.
  prop_apply (IntArray.full_Zlength t1_pre n_pre t1_l). Intros_p Harray_length_1.
  prop_apply (IntArray.full_Zlength s1_pre n_pre s1_l). Intros_p Harray_length_2.
  prop_apply (IntArray.full_Zlength s2_pre n_pre s2_l). Intros_p Harray_length_3.
  prop_apply (IntArray.full_Zlength t2_pre n_pre t2_l). Intros_p Harray_length_4.
  prop_apply (IntArray.full_Zlength (&("cnt10")) n_pre c10_2). Intros_p Harray_length_5.
  prop_apply (IntArray.full_Zlength (&("cnt11")) n_pre c11_2). Intros_p Harray_length_6.
  prop_apply (IntArray.full_Zlength (&("cnt20")) n_pre c20_2). Intros_p Harray_length_7.
  prop_apply (IntArray.full_Zlength (&("cnt21")) n_pre c21_2). Intros_p Harray_length_8.
  repeat rewrite Zlength_replace_Znth in *;
  repeat rewrite Zlength_app in *;
  repeat rewrite Zlength_cons in *;
  repeat rewrite Zlength_nil in *;
  repeat rewrite Z.sub_0_r in *.
  match goal with H : EditBuildMeaning s1_l t1_l n_pre i sg1 c10_2 c11_2 |- _ =>
    pose proof (proj1 H) as Hsegments; pose proof (proj2 H) as Hcounts end.
  assert (Hnewseg : EditSegmentMeaning t1_l (i + 1) (sg1 ++ [Znth (i - 1) sg1 0])).
  { apply edit_segment_extend_same; try assumption; try lia.
    unfold edit_edge_open; split; assumption. }
  pose proof (edit_segment_bound t1_l (sg1 ++ [Znth (i - 1) sg1 0]) (i + 1) i Hnewseg ltac:(lia)) as Hblock_bounds.
  Exists (sg1 ++ [Znth (i - 1) sg1 0]) c21_2 c20_2 c11_2 c10_2.
  split_pure_spatial.
  - edit_cancel.
  - edit_split_pures; dump_pre_spatial; try assumption; try congruence; try (timeout 2 lia).
Qed. 

Lemma proof_of_max_edit_string_matches_entail_wit_4_2 : max_edit_string_matches_entail_wit_4_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (IntArray.seg_Zlength (&("seg1")) 0 (i + 1 ) (app (sg1) ((cons (i) ((@nil Z)))))). Intros_p Harray_length_0.
  prop_apply (IntArray.full_Zlength t1_pre n_pre t1_l). Intros_p Harray_length_1.
  prop_apply (IntArray.full_Zlength s1_pre n_pre s1_l). Intros_p Harray_length_2.
  prop_apply (IntArray.full_Zlength s2_pre n_pre s2_l). Intros_p Harray_length_3.
  prop_apply (IntArray.full_Zlength t2_pre n_pre t2_l). Intros_p Harray_length_4.
  prop_apply (IntArray.full_Zlength (&("cnt10")) n_pre c10_2). Intros_p Harray_length_5.
  prop_apply (IntArray.full_Zlength (&("cnt11")) n_pre c11_2). Intros_p Harray_length_6.
  prop_apply (IntArray.full_Zlength (&("cnt20")) n_pre c20_2). Intros_p Harray_length_7.
  prop_apply (IntArray.full_Zlength (&("cnt21")) n_pre c21_2). Intros_p Harray_length_8.
  repeat rewrite Zlength_replace_Znth in *;
  repeat rewrite Zlength_app in *;
  repeat rewrite Zlength_cons in *;
  repeat rewrite Zlength_nil in *;
  repeat rewrite Z.sub_0_r in *.
  match goal with H : EditBuildMeaning s1_l t1_l n_pre i sg1 c10_2 c11_2 |- _ =>
    pose proof (proj1 H) as Hsegments; pose proof (proj2 H) as Hcounts end.
  assert (Hnewseg : EditSegmentMeaning t1_l (i + 1) (sg1 ++ [i])).
  { apply edit_segment_extend_new; try assumption; try lia.
    unfold edit_edge_open; intros [Hleft Hright]; congruence. }
  pose proof (edit_segment_bound t1_l (sg1 ++ [i]) (i + 1) i Hnewseg ltac:(lia)) as Hblock_bounds.
  Exists (sg1 ++ [i]) c21_2 c20_2 c11_2 c10_2.
  split_pure_spatial.
  - edit_cancel.
  - edit_split_pures; dump_pre_spatial; try assumption; try congruence; try (timeout 2 lia).
Qed. 

Lemma proof_of_max_edit_string_matches_entail_wit_4_3 : max_edit_string_matches_entail_wit_4_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (IntArray.seg_Zlength (&("seg1")) 0 (i + 1 ) (app (sg1) ((cons (i) ((@nil Z)))))). Intros_p Harray_length_0.
  prop_apply (IntArray.full_Zlength t1_pre n_pre t1_l). Intros_p Harray_length_1.
  prop_apply (IntArray.full_Zlength s1_pre n_pre s1_l). Intros_p Harray_length_2.
  prop_apply (IntArray.full_Zlength s2_pre n_pre s2_l). Intros_p Harray_length_3.
  prop_apply (IntArray.full_Zlength t2_pre n_pre t2_l). Intros_p Harray_length_4.
  prop_apply (IntArray.full_Zlength (&("cnt10")) n_pre c10_2). Intros_p Harray_length_5.
  prop_apply (IntArray.full_Zlength (&("cnt11")) n_pre c11_2). Intros_p Harray_length_6.
  prop_apply (IntArray.full_Zlength (&("cnt20")) n_pre c20_2). Intros_p Harray_length_7.
  prop_apply (IntArray.full_Zlength (&("cnt21")) n_pre c21_2). Intros_p Harray_length_8.
  repeat rewrite Zlength_replace_Znth in *;
  repeat rewrite Zlength_app in *;
  repeat rewrite Zlength_cons in *;
  repeat rewrite Zlength_nil in *;
  repeat rewrite Z.sub_0_r in *.
  match goal with H : EditBuildMeaning s1_l t1_l n_pre i sg1 c10_2 c11_2 |- _ =>
    pose proof (proj1 H) as Hsegments; pose proof (proj2 H) as Hcounts end.
  assert (Hnewseg : EditSegmentMeaning t1_l (i + 1) (sg1 ++ [i])).
  { apply edit_segment_extend_new; try assumption; try lia.
    unfold edit_edge_open; intros [Hleft Hright]; congruence. }
  pose proof (edit_segment_bound t1_l (sg1 ++ [i]) (i + 1) i Hnewseg ltac:(lia)) as Hblock_bounds.
  Exists (sg1 ++ [i]) c21_2 c20_2 c11_2 c10_2.
  split_pure_spatial.
  - edit_cancel.
  - edit_split_pures; dump_pre_spatial; try assumption; try congruence; try (timeout 2 lia).
Qed. 

Lemma proof_of_max_edit_string_matches_entail_wit_5_1 : max_edit_string_matches_entail_wit_5_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (IntArray.full_Zlength (&("cnt10")) n_pre (replace_Znth (block1) (((Znth block1 c10_2 0) + 1 )) (c10_2))). Intros_p Harray_length_0.
  prop_apply (IntArray.full_Zlength s1_pre n_pre s1_l). Intros_p Harray_length_1.
  prop_apply (IntArray.full_Zlength s2_pre n_pre s2_l). Intros_p Harray_length_2.
  prop_apply (IntArray.full_Zlength t1_pre n_pre t1_l). Intros_p Harray_length_3.
  prop_apply (IntArray.full_Zlength t2_pre n_pre t2_l). Intros_p Harray_length_4.
  prop_apply (IntArray.seg_Zlength (&("seg1")) 0 (i + 1 ) sg1_2). Intros_p Harray_length_5.
  prop_apply (IntArray.full_Zlength (&("cnt11")) n_pre c11_2). Intros_p Harray_length_6.
  prop_apply (IntArray.full_Zlength (&("cnt20")) n_pre c20_2). Intros_p Harray_length_7.
  prop_apply (IntArray.full_Zlength (&("cnt21")) n_pre c21_2). Intros_p Harray_length_8.
  repeat rewrite Zlength_replace_Znth in *;
  repeat rewrite Zlength_app in *;
  repeat rewrite Zlength_cons in *;
  repeat rewrite Zlength_nil in *;
  repeat rewrite Z.sub_0_r in *.
  assert (Hnewcounts : EditCountsMeaning s1_l t1_l n_pre (i + 1) (replace_Znth block1 (Znth block1 c10_2 0 + 1) c10_2) c11_2).
  { eapply edit_counts_inc_zero; eauto; lia. }
  assert (Hnewbuild : EditBuildMeaning s1_l t1_l n_pre (i + 1) sg1_2 (replace_Znth block1 (Znth block1 c10_2 0 + 1) c10_2) c11_2) by (split; assumption).
  pose proof (edit_counts_bounds s1_l t1_l n_pre (i + 1) (replace_Znth block1 (Znth block1 c10_2 0 + 1) c10_2) c11_2
    ltac:(lia) ltac:(lia) ltac:(rewrite ?Zlength_replace_Znth; lia)
    ltac:(rewrite ?Zlength_replace_Znth; lia) Hnewcounts) as [[Hzlo Hzhi] [Holo Hohi]].
  Exists sg1_2 c21_2 c20_2 c11_2 (replace_Znth block1 (Znth block1 c10_2 0 + 1) c10_2).
  split_pure_spatial.
  - edit_cancel.
  - edit_split_pures; dump_pre_spatial; try assumption; try congruence; try (timeout 2 lia).
Qed. 

Lemma proof_of_max_edit_string_matches_entail_wit_5_2 : max_edit_string_matches_entail_wit_5_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (IntArray.full_Zlength (&("cnt11")) n_pre (replace_Znth (block1) (((Znth block1 c11_2 0) + 1 )) (c11_2))). Intros_p Harray_length_0.
  prop_apply (IntArray.full_Zlength s1_pre n_pre s1_l). Intros_p Harray_length_1.
  prop_apply (IntArray.full_Zlength s2_pre n_pre s2_l). Intros_p Harray_length_2.
  prop_apply (IntArray.full_Zlength t1_pre n_pre t1_l). Intros_p Harray_length_3.
  prop_apply (IntArray.full_Zlength t2_pre n_pre t2_l). Intros_p Harray_length_4.
  prop_apply (IntArray.seg_Zlength (&("seg1")) 0 (i + 1 ) sg1_2). Intros_p Harray_length_5.
  prop_apply (IntArray.full_Zlength (&("cnt10")) n_pre c10_2). Intros_p Harray_length_6.
  prop_apply (IntArray.full_Zlength (&("cnt20")) n_pre c20_2). Intros_p Harray_length_7.
  prop_apply (IntArray.full_Zlength (&("cnt21")) n_pre c21_2). Intros_p Harray_length_8.
  repeat rewrite Zlength_replace_Znth in *;
  repeat rewrite Zlength_app in *;
  repeat rewrite Zlength_cons in *;
  repeat rewrite Zlength_nil in *;
  repeat rewrite Z.sub_0_r in *.
  assert (Hbit : Znth i s1_l 0 = 1).
  { pose proof (edit_bounded_read s1_l i 0 1 ltac:(eassumption) ltac:(eassumption) ltac:(lia)); lia. }
  assert (Hnewcounts : EditCountsMeaning s1_l t1_l n_pre (i + 1) c10_2 (replace_Znth block1 (Znth block1 c11_2 0 + 1) c11_2)).
  { eapply edit_counts_inc_one; eauto; lia. }
  assert (Hnewbuild : EditBuildMeaning s1_l t1_l n_pre (i + 1) sg1_2 c10_2 (replace_Znth block1 (Znth block1 c11_2 0 + 1) c11_2)) by (split; assumption).
  pose proof (edit_counts_bounds s1_l t1_l n_pre (i + 1) c10_2 (replace_Znth block1 (Znth block1 c11_2 0 + 1) c11_2)
    ltac:(lia) ltac:(lia) ltac:(rewrite ?Zlength_replace_Znth; lia)
    ltac:(rewrite ?Zlength_replace_Znth; lia) Hnewcounts) as [[Hzlo Hzhi] [Holo Hohi]].
  Exists sg1_2 c21_2 c20_2 (replace_Znth block1 (Znth block1 c11_2 0 + 1) c11_2) c10_2.
  split_pure_spatial.
  - edit_cancel.
  - edit_split_pures; dump_pre_spatial; try assumption; try congruence; try (timeout 2 lia).
Qed. 

Lemma proof_of_max_edit_string_matches_entail_wit_6_1 : max_edit_string_matches_entail_wit_6_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (IntArray.full_Zlength (&("cnt20")) n_pre (replace_Znth (0) (((Znth 0 c20_2 0) + 1 )) (c20_2))). Intros_p Harray_length_0.
  prop_apply (IntArray.full_Zlength s2_pre n_pre s2_l). Intros_p Harray_length_1.
  prop_apply (IntArray.full_Zlength s1_pre n_pre s1_l). Intros_p Harray_length_2.
  prop_apply (IntArray.full_Zlength t1_pre n_pre t1_l). Intros_p Harray_length_3.
  prop_apply (IntArray.full_Zlength t2_pre n_pre t2_l). Intros_p Harray_length_4.
  prop_apply (IntArray.seg_Zlength (&("seg1")) 0 i sg1_2). Intros_p Harray_length_5.
  prop_apply (IntArray.full_Zlength (&("cnt10")) n_pre c10_2). Intros_p Harray_length_6.
  prop_apply (IntArray.full_Zlength (&("cnt11")) n_pre c11_2). Intros_p Harray_length_7.
  prop_apply (IntArray.full_Zlength (&("cnt21")) n_pre c21_2). Intros_p Harray_length_8.
  repeat rewrite Zlength_replace_Znth in *;
  repeat rewrite Zlength_app in *;
  repeat rewrite Zlength_cons in *;
  repeat rewrite Zlength_nil in *;
  repeat rewrite Z.sub_0_r in *.
  assert (Hi_end : i = n_pre) by lia. rewrite Hi_end in *. clear i Hi_end.
  assert (Hbuild : EditBuildMeaning s2_l t2_l n_pre 1 [0] (replace_Znth 0 (Znth 0 c20_2 0 + 1) c20_2) c21_2).
  { eapply edit_build_first_zero; eauto; lia. }
  pose proof (edit_counts_bounds s2_l t2_l n_pre 1 (replace_Znth 0 (Znth 0 c20_2 0 + 1) c20_2) c21_2
    ltac:(lia) ltac:(lia) ltac:(rewrite ?Zlength_replace_Znth; lia)
    ltac:(rewrite ?Zlength_replace_Znth; lia) (proj2 Hbuild)) as [[Hzlo Hzhi] [Holo Hohi]].
  Exists [0] sg1_2 c21_2 (replace_Znth 0 (Znth 0 c20_2 0 + 1) c20_2) c11_2 c10_2.
  split_pure_spatial.
  - sep_apply (IntArray.seg_single (&("seg2")) 0 0).
    replace (0 + 1) with 1 by lia.
    sep_apply (IntArray.seg_to_full (&("seg1")) 0 n_pre sg1_2).
    replace ((&("seg1")) + 0 * sizeof(INT)) with (&("seg1")) by lia.
    replace (n_pre - 0) with n_pre by lia.
    edit_cancel.
  - edit_split_pures; dump_pre_spatial; try assumption; try congruence; lia.

Qed. 

Lemma proof_of_max_edit_string_matches_entail_wit_6_2 : max_edit_string_matches_entail_wit_6_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (IntArray.full_Zlength (&("cnt21")) n_pre (replace_Znth (0) (((Znth 0 c21_2 0) + 1 )) (c21_2))). Intros_p Harray_length_0.
  prop_apply (IntArray.full_Zlength s2_pre n_pre s2_l). Intros_p Harray_length_1.
  prop_apply (IntArray.full_Zlength s1_pre n_pre s1_l). Intros_p Harray_length_2.
  prop_apply (IntArray.full_Zlength t1_pre n_pre t1_l). Intros_p Harray_length_3.
  prop_apply (IntArray.full_Zlength t2_pre n_pre t2_l). Intros_p Harray_length_4.
  prop_apply (IntArray.seg_Zlength (&("seg1")) 0 i sg1_2). Intros_p Harray_length_5.
  prop_apply (IntArray.full_Zlength (&("cnt10")) n_pre c10_2). Intros_p Harray_length_6.
  prop_apply (IntArray.full_Zlength (&("cnt11")) n_pre c11_2). Intros_p Harray_length_7.
  prop_apply (IntArray.full_Zlength (&("cnt20")) n_pre c20_2). Intros_p Harray_length_8.
  repeat rewrite Zlength_replace_Znth in *;
  repeat rewrite Zlength_app in *;
  repeat rewrite Zlength_cons in *;
  repeat rewrite Zlength_nil in *;
  repeat rewrite Z.sub_0_r in *.
  assert (Hi_end : i = n_pre) by lia. rewrite Hi_end in *. clear i Hi_end.
  assert (Hbuild : EditBuildMeaning s2_l t2_l n_pre 1 [0] c20_2 (replace_Znth 0 (Znth 0 c21_2 0 + 1) c21_2)).
  { eapply edit_build_first_one; eauto; lia. }
  pose proof (edit_counts_bounds s2_l t2_l n_pre 1 c20_2 (replace_Znth 0 (Znth 0 c21_2 0 + 1) c21_2)
    ltac:(lia) ltac:(lia) ltac:(rewrite ?Zlength_replace_Znth; lia)
    ltac:(rewrite ?Zlength_replace_Znth; lia) (proj2 Hbuild)) as [[Hzlo Hzhi] [Holo Hohi]].
  Exists [0] sg1_2 (replace_Znth 0 (Znth 0 c21_2 0 + 1) c21_2) c20_2 c11_2 c10_2.
  split_pure_spatial.
  - sep_apply (IntArray.seg_single (&("seg2")) 0 0).
    replace (0 + 1) with 1 by lia.
    sep_apply (IntArray.seg_to_full (&("seg1")) 0 n_pre sg1_2).
    replace ((&("seg1")) + 0 * sizeof(INT)) with (&("seg1")) by lia.
    replace (n_pre - 0) with n_pre by lia.
    edit_cancel.
  - edit_split_pures; dump_pre_spatial; try assumption; try congruence; lia.

Qed. 

Lemma proof_of_max_edit_string_matches_entail_wit_7_1 : max_edit_string_matches_entail_wit_7_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (IntArray.seg_Zlength (&("seg2")) 0 (i + 1 ) (app (sg2) ((cons ((Znth ((i - 1 ) - 0 ) sg2 0)) ((@nil Z)))))). Intros_p Harray_length_0.
  prop_apply (IntArray.full_Zlength t2_pre n_pre t2_l). Intros_p Harray_length_1.
  prop_apply (IntArray.full_Zlength s1_pre n_pre s1_l). Intros_p Harray_length_2.
  prop_apply (IntArray.full_Zlength s2_pre n_pre s2_l). Intros_p Harray_length_3.
  prop_apply (IntArray.full_Zlength t1_pre n_pre t1_l). Intros_p Harray_length_4.
  prop_apply (IntArray.full_Zlength (&("seg1")) n_pre sg1_2). Intros_p Harray_length_5.
  prop_apply (IntArray.full_Zlength (&("cnt10")) n_pre c10_2). Intros_p Harray_length_6.
  prop_apply (IntArray.full_Zlength (&("cnt11")) n_pre c11_2). Intros_p Harray_length_7.
  prop_apply (IntArray.full_Zlength (&("cnt20")) n_pre c20_2). Intros_p Harray_length_8.
  prop_apply (IntArray.full_Zlength (&("cnt21")) n_pre c21_2). Intros_p Harray_length_9.
  repeat rewrite Zlength_replace_Znth in *;
  repeat rewrite Zlength_app in *;
  repeat rewrite Zlength_cons in *;
  repeat rewrite Zlength_nil in *;
  repeat rewrite Z.sub_0_r in *.
  match goal with H : EditBuildMeaning s2_l t2_l n_pre i sg2 c20_2 c21_2 |- _ =>
    pose proof (proj1 H) as Hsegments; pose proof (proj2 H) as Hcounts end.
  assert (Hnewseg : EditSegmentMeaning t2_l (i + 1) (sg2 ++ [Znth (i - 1) sg2 0])).
  { apply edit_segment_extend_same; try assumption; try lia.
    unfold edit_edge_open; split; assumption. }
  pose proof (edit_segment_bound t2_l (sg2 ++ [Znth (i - 1) sg2 0]) (i + 1) i Hnewseg ltac:(lia)) as Hblock_bounds.
  Exists (sg2 ++ [Znth (i - 1) sg2 0]) sg1_2 c21_2 c20_2 c11_2 c10_2.
  split_pure_spatial.
  - edit_cancel.
  - edit_split_pures; dump_pre_spatial; try assumption; try congruence; try (timeout 2 lia).
Qed. 

Lemma proof_of_max_edit_string_matches_entail_wit_7_2 : max_edit_string_matches_entail_wit_7_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (IntArray.seg_Zlength (&("seg2")) 0 (i + 1 ) (app (sg2) ((cons (i) ((@nil Z)))))). Intros_p Harray_length_0.
  prop_apply (IntArray.full_Zlength t2_pre n_pre t2_l). Intros_p Harray_length_1.
  prop_apply (IntArray.full_Zlength s1_pre n_pre s1_l). Intros_p Harray_length_2.
  prop_apply (IntArray.full_Zlength s2_pre n_pre s2_l). Intros_p Harray_length_3.
  prop_apply (IntArray.full_Zlength t1_pre n_pre t1_l). Intros_p Harray_length_4.
  prop_apply (IntArray.full_Zlength (&("seg1")) n_pre sg1_2). Intros_p Harray_length_5.
  prop_apply (IntArray.full_Zlength (&("cnt10")) n_pre c10_2). Intros_p Harray_length_6.
  prop_apply (IntArray.full_Zlength (&("cnt11")) n_pre c11_2). Intros_p Harray_length_7.
  prop_apply (IntArray.full_Zlength (&("cnt20")) n_pre c20_2). Intros_p Harray_length_8.
  prop_apply (IntArray.full_Zlength (&("cnt21")) n_pre c21_2). Intros_p Harray_length_9.
  repeat rewrite Zlength_replace_Znth in *;
  repeat rewrite Zlength_app in *;
  repeat rewrite Zlength_cons in *;
  repeat rewrite Zlength_nil in *;
  repeat rewrite Z.sub_0_r in *.
  match goal with H : EditBuildMeaning s2_l t2_l n_pre i sg2 c20_2 c21_2 |- _ =>
    pose proof (proj1 H) as Hsegments; pose proof (proj2 H) as Hcounts end.
  assert (Hnewseg : EditSegmentMeaning t2_l (i + 1) (sg2 ++ [i])).
  { apply edit_segment_extend_new; try assumption; try lia.
    unfold edit_edge_open; intros [Hleft Hright]; congruence. }
  pose proof (edit_segment_bound t2_l (sg2 ++ [i]) (i + 1) i Hnewseg ltac:(lia)) as Hblock_bounds.
  Exists (sg2 ++ [i]) sg1_2 c21_2 c20_2 c11_2 c10_2.
  split_pure_spatial.
  - edit_cancel.
  - edit_split_pures; dump_pre_spatial; try assumption; try congruence; try (timeout 2 lia).
Qed. 

Lemma proof_of_max_edit_string_matches_entail_wit_7_3 : max_edit_string_matches_entail_wit_7_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (IntArray.seg_Zlength (&("seg2")) 0 (i + 1 ) (app (sg2) ((cons (i) ((@nil Z)))))). Intros_p Harray_length_0.
  prop_apply (IntArray.full_Zlength t2_pre n_pre t2_l). Intros_p Harray_length_1.
  prop_apply (IntArray.full_Zlength s1_pre n_pre s1_l). Intros_p Harray_length_2.
  prop_apply (IntArray.full_Zlength s2_pre n_pre s2_l). Intros_p Harray_length_3.
  prop_apply (IntArray.full_Zlength t1_pre n_pre t1_l). Intros_p Harray_length_4.
  prop_apply (IntArray.full_Zlength (&("seg1")) n_pre sg1_2). Intros_p Harray_length_5.
  prop_apply (IntArray.full_Zlength (&("cnt10")) n_pre c10_2). Intros_p Harray_length_6.
  prop_apply (IntArray.full_Zlength (&("cnt11")) n_pre c11_2). Intros_p Harray_length_7.
  prop_apply (IntArray.full_Zlength (&("cnt20")) n_pre c20_2). Intros_p Harray_length_8.
  prop_apply (IntArray.full_Zlength (&("cnt21")) n_pre c21_2). Intros_p Harray_length_9.
  repeat rewrite Zlength_replace_Znth in *;
  repeat rewrite Zlength_app in *;
  repeat rewrite Zlength_cons in *;
  repeat rewrite Zlength_nil in *;
  repeat rewrite Z.sub_0_r in *.
  match goal with H : EditBuildMeaning s2_l t2_l n_pre i sg2 c20_2 c21_2 |- _ =>
    pose proof (proj1 H) as Hsegments; pose proof (proj2 H) as Hcounts end.
  assert (Hnewseg : EditSegmentMeaning t2_l (i + 1) (sg2 ++ [i])).
  { apply edit_segment_extend_new; try assumption; try lia.
    unfold edit_edge_open; intros [Hleft Hright]; congruence. }
  pose proof (edit_segment_bound t2_l (sg2 ++ [i]) (i + 1) i Hnewseg ltac:(lia)) as Hblock_bounds.
  Exists (sg2 ++ [i]) sg1_2 c21_2 c20_2 c11_2 c10_2.
  split_pure_spatial.
  - edit_cancel.
  - edit_split_pures; dump_pre_spatial; try assumption; try congruence; try (timeout 2 lia).
Qed. 

Lemma proof_of_max_edit_string_matches_entail_wit_8_1 : max_edit_string_matches_entail_wit_8_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (IntArray.full_Zlength (&("cnt20")) n_pre (replace_Znth (block2) (((Znth block2 c20_2 0) + 1 )) (c20_2))). Intros_p Harray_length_0.
  prop_apply (IntArray.full_Zlength s2_pre n_pre s2_l). Intros_p Harray_length_1.
  prop_apply (IntArray.full_Zlength s1_pre n_pre s1_l). Intros_p Harray_length_2.
  prop_apply (IntArray.full_Zlength t1_pre n_pre t1_l). Intros_p Harray_length_3.
  prop_apply (IntArray.full_Zlength t2_pre n_pre t2_l). Intros_p Harray_length_4.
  prop_apply (IntArray.full_Zlength (&("seg1")) n_pre sg1_2). Intros_p Harray_length_5.
  prop_apply (IntArray.seg_Zlength (&("seg2")) 0 (i + 1 ) sg2_2). Intros_p Harray_length_6.
  prop_apply (IntArray.full_Zlength (&("cnt10")) n_pre c10_2). Intros_p Harray_length_7.
  prop_apply (IntArray.full_Zlength (&("cnt11")) n_pre c11_2). Intros_p Harray_length_8.
  prop_apply (IntArray.full_Zlength (&("cnt21")) n_pre c21_2). Intros_p Harray_length_9.
  repeat rewrite Zlength_replace_Znth in *;
  repeat rewrite Zlength_app in *;
  repeat rewrite Zlength_cons in *;
  repeat rewrite Zlength_nil in *;
  repeat rewrite Z.sub_0_r in *.
  assert (Hnewcounts : EditCountsMeaning s2_l t2_l n_pre (i + 1) (replace_Znth block2 (Znth block2 c20_2 0 + 1) c20_2) c21_2).
  { eapply edit_counts_inc_zero; eauto; lia. }
  assert (Hnewbuild : EditBuildMeaning s2_l t2_l n_pre (i + 1) sg2_2 (replace_Znth block2 (Znth block2 c20_2 0 + 1) c20_2) c21_2) by (split; assumption).
  pose proof (edit_counts_bounds s2_l t2_l n_pre (i + 1) (replace_Znth block2 (Znth block2 c20_2 0 + 1) c20_2) c21_2
    ltac:(lia) ltac:(lia) ltac:(rewrite ?Zlength_replace_Znth; lia)
    ltac:(rewrite ?Zlength_replace_Znth; lia) Hnewcounts) as [[Hzlo Hzhi] [Holo Hohi]].
  Exists sg2_2 sg1_2 c21_2 (replace_Znth block2 (Znth block2 c20_2 0 + 1) c20_2) c11_2 c10_2.
  split_pure_spatial.
  - edit_cancel.
  - edit_split_pures; dump_pre_spatial; try assumption; try congruence; try (timeout 2 lia).
Qed. 

Lemma proof_of_max_edit_string_matches_entail_wit_8_2 : max_edit_string_matches_entail_wit_8_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (IntArray.full_Zlength (&("cnt21")) n_pre (replace_Znth (block2) (((Znth block2 c21_2 0) + 1 )) (c21_2))). Intros_p Harray_length_0.
  prop_apply (IntArray.full_Zlength s2_pre n_pre s2_l). Intros_p Harray_length_1.
  prop_apply (IntArray.full_Zlength s1_pre n_pre s1_l). Intros_p Harray_length_2.
  prop_apply (IntArray.full_Zlength t1_pre n_pre t1_l). Intros_p Harray_length_3.
  prop_apply (IntArray.full_Zlength t2_pre n_pre t2_l). Intros_p Harray_length_4.
  prop_apply (IntArray.full_Zlength (&("seg1")) n_pre sg1_2). Intros_p Harray_length_5.
  prop_apply (IntArray.seg_Zlength (&("seg2")) 0 (i + 1 ) sg2_2). Intros_p Harray_length_6.
  prop_apply (IntArray.full_Zlength (&("cnt10")) n_pre c10_2). Intros_p Harray_length_7.
  prop_apply (IntArray.full_Zlength (&("cnt11")) n_pre c11_2). Intros_p Harray_length_8.
  prop_apply (IntArray.full_Zlength (&("cnt20")) n_pre c20_2). Intros_p Harray_length_9.
  repeat rewrite Zlength_replace_Znth in *;
  repeat rewrite Zlength_app in *;
  repeat rewrite Zlength_cons in *;
  repeat rewrite Zlength_nil in *;
  repeat rewrite Z.sub_0_r in *.
  assert (Hbit : Znth i s2_l 0 = 1).
  { pose proof (edit_bounded_read s2_l i 0 1 ltac:(eassumption) ltac:(eassumption) ltac:(lia)); lia. }
  assert (Hnewcounts : EditCountsMeaning s2_l t2_l n_pre (i + 1) c20_2 (replace_Znth block2 (Znth block2 c21_2 0 + 1) c21_2)).
  { eapply edit_counts_inc_one; eauto; lia. }
  assert (Hnewbuild : EditBuildMeaning s2_l t2_l n_pre (i + 1) sg2_2 c20_2 (replace_Znth block2 (Znth block2 c21_2 0 + 1) c21_2)) by (split; assumption).
  pose proof (edit_counts_bounds s2_l t2_l n_pre (i + 1) c20_2 (replace_Znth block2 (Znth block2 c21_2 0 + 1) c21_2)
    ltac:(lia) ltac:(lia) ltac:(rewrite ?Zlength_replace_Znth; lia)
    ltac:(rewrite ?Zlength_replace_Znth; lia) Hnewcounts) as [[Hzlo Hzhi] [Holo Hohi]].
  Exists sg2_2 sg1_2 (replace_Znth block2 (Znth block2 c21_2 0 + 1) c21_2) c20_2 c11_2 c10_2.
  split_pure_spatial.
  - edit_cancel.
  - edit_split_pures; dump_pre_spatial; try assumption; try congruence; try (timeout 2 lia).
Qed. 

Lemma proof_of_max_edit_string_matches_entail_wit_9 : max_edit_string_matches_entail_wit_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (IntArray.full_Zlength s1_pre n_pre s1_l). Intros_p Harray_length_0.
  prop_apply (IntArray.full_Zlength s2_pre n_pre s2_l). Intros_p Harray_length_1.
  prop_apply (IntArray.full_Zlength t1_pre n_pre t1_l). Intros_p Harray_length_2.
  prop_apply (IntArray.full_Zlength t2_pre n_pre t2_l). Intros_p Harray_length_3.
  prop_apply (IntArray.full_Zlength (&("seg1")) n_pre sg1_2). Intros_p Harray_length_4.
  prop_apply (IntArray.seg_Zlength (&("seg2")) 0 i sg2_2). Intros_p Harray_length_5.
  prop_apply (IntArray.full_Zlength (&("cnt10")) n_pre c10_2). Intros_p Harray_length_6.
  prop_apply (IntArray.full_Zlength (&("cnt11")) n_pre c11_2). Intros_p Harray_length_7.
  prop_apply (IntArray.full_Zlength (&("cnt20")) n_pre c20_2). Intros_p Harray_length_8.
  prop_apply (IntArray.full_Zlength (&("cnt21")) n_pre c21_2). Intros_p Harray_length_9.
  repeat rewrite Zlength_replace_Znth in *;
  repeat rewrite Zlength_app in *;
  repeat rewrite Zlength_cons in *;
  repeat rewrite Zlength_nil in *;
  repeat rewrite Z.sub_0_r in *.
  assert (Hi_end : i = n_pre) by lia. rewrite Hi_end in *. clear i Hi_end.
  assert (Hbinary1 : Forall (fun bit => bit = 0 \/ bit = 1) s1_l).
  { apply (proj2 (Forall_Znth _ 0 s1_l)); intros idx Hidx.
    pose proof (edit_bounded_read s1_l idx 0 1 ltac:(eassumption) ltac:(eassumption) ltac:(lia)); lia. }
  assert (Hbinary2 : Forall (fun bit => bit = 0 \/ bit = 1) s2_l).
  { apply (proj2 (Forall_Znth _ 0 s2_l)); intros idx Hidx.
    pose proof (edit_bounded_read s2_l idx 0 1 ltac:(eassumption) ltac:(eassumption) ltac:(lia)); lia. }
  destruct (edit_initial_remaining s1_l s2_l t1_l t2_l sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2 n_pre
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    Hbinary1 Hbinary2 ltac:(eassumption) ltac:(eassumption)) as [rest [Hremaining Hanswer]].
  match goal with H : EditBuildMeaning s1_l t1_l n_pre n_pre sg1_2 c10_2 c11_2 |- _ =>
    pose proof (proj1 H) as Hsg1 end.
  match goal with H : EditBuildMeaning s2_l t2_l n_pre n_pre sg2_2 c20_2 c21_2 |- _ =>
    pose proof (proj1 H) as Hsg2 end.
  Exists rest (@nil Z) (@nil Z) sg2_2 sg1_2 c21_2 c20_2 c11_2 c10_2.
  split_pure_spatial.
  - rewrite IntArray.undef_seg_empty.
    sep_apply (IntArray.seg_to_full (&("seg2")) 0 n_pre sg2_2).
    replace ((&("seg2")) + 0 * sizeof(INT)) with (&("seg2")) by lia.
    replace (n_pre - 0) with n_pre by lia.
    edit_cancel.
  - edit_split_pures; dump_pre_spatial; try assumption; try reflexivity; lia.

Qed. 

Lemma proof_of_max_edit_string_matches_entail_wit_10 : max_edit_string_matches_entail_wit_10.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (edit_segment_bound t1_l sg1 n_pre i ltac:(eassumption) ltac:(lia)) as Hsg1.
  pose proof (edit_segment_bound t2_l sg2 n_pre i ltac:(eassumption) ltac:(lia)) as Hsg2.
  Exists rest_2 prefix2_2 prefix1_2 sg2 sg1 c21_2 c20_2 c11_2 c10_2.
  split_pure_spatial.
  - edit_cancel.
  - edit_split_pures; dump_pre_spatial; try assumption; try congruence; try (timeout 2 lia).
Qed. 

Lemma proof_of_max_edit_string_matches_entail_wit_11_1 : max_edit_string_matches_entail_wit_11_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (IntArray.full_Zlength (&("cnt20")) n_pre (replace_Znth (b) (((Znth b c20_2 0) - 1 )) (c20_2))). Intros_p Harray_length_0.
  prop_apply (IntArray.full_Zlength (&("cnt10")) n_pre (replace_Znth (a) (((Znth a c10_2 0) - 1 )) (c10_2))). Intros_p Harray_length_1.
  prop_apply (IntArray.full_Zlength s1_pre n_pre s1_l). Intros_p Harray_length_2.
  prop_apply (IntArray.full_Zlength s2_pre n_pre s2_l). Intros_p Harray_length_3.
  prop_apply (IntArray.full_Zlength t1_pre n_pre t1_l). Intros_p Harray_length_4.
  prop_apply (IntArray.full_Zlength t2_pre n_pre t2_l). Intros_p Harray_length_5.
  prop_apply (IntArray.full_Zlength (&("seg1")) n_pre sg1_2). Intros_p Harray_length_6.
  prop_apply (IntArray.full_Zlength (&("seg2")) n_pre sg2_2). Intros_p Harray_length_7.
  prop_apply (IntArray.full_Zlength (&("cnt11")) n_pre c11_2). Intros_p Harray_length_8.
  prop_apply (IntArray.full_Zlength (&("cnt21")) n_pre c21_2). Intros_p Harray_length_9.
  repeat rewrite Zlength_replace_Znth in *;
  repeat rewrite Zlength_app in *;
  repeat rewrite Zlength_cons in *;
  repeat rewrite Zlength_nil in *;
  repeat rewrite Z.sub_0_r in *.
  assert (Hnext : EditRemainingMatches s1_l s2_l t1_l t2_l sg1_2 sg2_2 (prefix1_2 ++ [0]) (prefix2_2 ++ [0]) (i + 1) (replace_Znth a (Znth a c10_2 0 - 1) c10_2) c11_2 (replace_Znth b (Znth b c20_2 0 - 1) c20_2) c21_2 (rest_2 - 1)).
  { eapply edit_remaining_common_step with (n := n_pre) (a := a) (b := b) (bit := 0); eauto; cbn [Z.eqb Pos.eqb]; lia. }
  pose proof (edit_remaining_count_bounds s1_l s2_l t1_l t2_l sg1_2 sg2_2 (prefix1_2 ++ [0]) (prefix2_2 ++ [0]) (i + 1) (replace_Znth a (Znth a c10_2 0 - 1) c10_2) c11_2 (replace_Znth b (Znth b c20_2 0 - 1) c20_2) c21_2 n_pre (rest_2 - 1)
    ltac:(lia) ltac:(lia) ltac:(rewrite ?Zlength_replace_Znth; lia) ltac:(rewrite ?Zlength_replace_Znth; lia)
    ltac:(rewrite ?Zlength_replace_Znth; lia) ltac:(rewrite ?Zlength_replace_Znth; lia) ltac:(lia) Hnext)
    as [[H10lo H10hi] [[H11lo H11hi] [[H20lo H20hi] [H21lo H21hi]]]].
  assert (Hprefix1 : Zlength (prefix1_2 ++ [0]) = i + 1) by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  assert (Hprefix2 : Zlength (prefix2_2 ++ [0]) = i + 1) by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  assert (Hprefix_score : (ans + 1) = EditPairMatches (prefix1_2 ++ [0]) (prefix2_2 ++ [0])).
  { rewrite edit_pair_app by lia. change (EditPairMatches [0] [0]) with 1.
    match goal with H : ans = EditPairMatches prefix1_2 prefix2_2 |- _ => rewrite <- H end; lia. }
  assert (Hanswer : EditStringsAnswer (map (Z.add 48) s1_l) (map (Z.add 48) s2_l)
    (map (Z.add 48) t1_l) (map (Z.add 48) t2_l) ((ans + 1) + (rest_2 - 1))).
  { replace ((ans + 1) + (rest_2 - 1)) with (ans + rest_2) by lia. assumption. }
  Exists (rest_2 - 1) (prefix2_2 ++ [0]) (prefix1_2 ++ [0]) sg2_2 sg1_2 c21_2 (replace_Znth b (Znth b c20_2 0 - 1) c20_2) c11_2 (replace_Znth a (Znth a c10_2 0 - 1) c10_2).
  split_pure_spatial.
  - edit_cancel.
  - edit_split_pures; dump_pre_spatial; try assumption; try congruence; try (timeout 2 lia).
Qed. 

Lemma proof_of_max_edit_string_matches_entail_wit_11_2 : max_edit_string_matches_entail_wit_11_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (IntArray.full_Zlength (&("cnt21")) n_pre (replace_Znth (b) (((Znth b c21_2 0) - 1 )) (c21_2))). Intros_p Harray_length_0.
  prop_apply (IntArray.full_Zlength (&("cnt11")) n_pre (replace_Znth (a) (((Znth a c11_2 0) - 1 )) (c11_2))). Intros_p Harray_length_1.
  prop_apply (IntArray.full_Zlength (&("cnt10")) n_pre c10_2). Intros_p Harray_length_2.
  prop_apply (IntArray.full_Zlength s1_pre n_pre s1_l). Intros_p Harray_length_3.
  prop_apply (IntArray.full_Zlength s2_pre n_pre s2_l). Intros_p Harray_length_4.
  prop_apply (IntArray.full_Zlength t1_pre n_pre t1_l). Intros_p Harray_length_5.
  prop_apply (IntArray.full_Zlength t2_pre n_pre t2_l). Intros_p Harray_length_6.
  prop_apply (IntArray.full_Zlength (&("seg1")) n_pre sg1_2). Intros_p Harray_length_7.
  prop_apply (IntArray.full_Zlength (&("seg2")) n_pre sg2_2). Intros_p Harray_length_8.
  prop_apply (IntArray.full_Zlength (&("cnt20")) n_pre c20_2). Intros_p Harray_length_9.
  repeat rewrite Zlength_replace_Znth in *;
  repeat rewrite Zlength_app in *;
  repeat rewrite Zlength_cons in *;
  repeat rewrite Zlength_nil in *;
  repeat rewrite Z.sub_0_r in *.
  assert (Hnext : EditRemainingMatches s1_l s2_l t1_l t2_l sg1_2 sg2_2 (prefix1_2 ++ [1]) (prefix2_2 ++ [1]) (i + 1) c10_2 (replace_Znth a (Znth a c11_2 0 - 1) c11_2) c20_2 (replace_Znth b (Znth b c21_2 0 - 1) c21_2) (rest_2 - 1)).
  { eapply edit_remaining_common_step with (n := n_pre) (a := a) (b := b) (bit := 1); eauto; cbn [Z.eqb Pos.eqb]; lia. }
  pose proof (edit_remaining_count_bounds s1_l s2_l t1_l t2_l sg1_2 sg2_2 (prefix1_2 ++ [1]) (prefix2_2 ++ [1]) (i + 1) c10_2 (replace_Znth a (Znth a c11_2 0 - 1) c11_2) c20_2 (replace_Znth b (Znth b c21_2 0 - 1) c21_2) n_pre (rest_2 - 1)
    ltac:(lia) ltac:(lia) ltac:(rewrite ?Zlength_replace_Znth; lia) ltac:(rewrite ?Zlength_replace_Znth; lia)
    ltac:(rewrite ?Zlength_replace_Znth; lia) ltac:(rewrite ?Zlength_replace_Znth; lia) ltac:(lia) Hnext)
    as [[H10lo H10hi] [[H11lo H11hi] [[H20lo H20hi] [H21lo H21hi]]]].
  assert (Hprefix1 : Zlength (prefix1_2 ++ [1]) = i + 1) by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  assert (Hprefix2 : Zlength (prefix2_2 ++ [1]) = i + 1) by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  assert (Hprefix_score : (ans + 1) = EditPairMatches (prefix1_2 ++ [1]) (prefix2_2 ++ [1])).
  { rewrite edit_pair_app by lia. change (EditPairMatches [1] [1]) with 1.
    match goal with H : ans = EditPairMatches prefix1_2 prefix2_2 |- _ => rewrite <- H end; lia. }
  assert (Hanswer : EditStringsAnswer (map (Z.add 48) s1_l) (map (Z.add 48) s2_l)
    (map (Z.add 48) t1_l) (map (Z.add 48) t2_l) ((ans + 1) + (rest_2 - 1))).
  { replace ((ans + 1) + (rest_2 - 1)) with (ans + rest_2) by lia. assumption. }
  Exists (rest_2 - 1) (prefix2_2 ++ [1]) (prefix1_2 ++ [1]) sg2_2 sg1_2 (replace_Znth b (Znth b c21_2 0 - 1) c21_2) c20_2 (replace_Znth a (Znth a c11_2 0 - 1) c11_2) c10_2.
  split_pure_spatial.
  - edit_cancel.
  - edit_split_pures; dump_pre_spatial; try assumption; try congruence; try (timeout 2 lia).
Qed. 

Lemma proof_of_max_edit_string_matches_entail_wit_11_3 : max_edit_string_matches_entail_wit_11_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (IntArray.full_Zlength (&("cnt21")) n_pre (replace_Znth (b) (((Znth b c21_2 0) - 1 )) (c21_2))). Intros_p Harray_length_0.
  prop_apply (IntArray.full_Zlength (&("cnt11")) n_pre (replace_Znth (a) (((Znth a c11_2 0) - 1 )) (c11_2))). Intros_p Harray_length_1.
  prop_apply (IntArray.full_Zlength (&("cnt20")) n_pre c20_2). Intros_p Harray_length_2.
  prop_apply (IntArray.full_Zlength (&("cnt10")) n_pre c10_2). Intros_p Harray_length_3.
  prop_apply (IntArray.full_Zlength s1_pre n_pre s1_l). Intros_p Harray_length_4.
  prop_apply (IntArray.full_Zlength s2_pre n_pre s2_l). Intros_p Harray_length_5.
  prop_apply (IntArray.full_Zlength t1_pre n_pre t1_l). Intros_p Harray_length_6.
  prop_apply (IntArray.full_Zlength t2_pre n_pre t2_l). Intros_p Harray_length_7.
  prop_apply (IntArray.full_Zlength (&("seg1")) n_pre sg1_2). Intros_p Harray_length_8.
  prop_apply (IntArray.full_Zlength (&("seg2")) n_pre sg2_2). Intros_p Harray_length_9.
  repeat rewrite Zlength_replace_Znth in *;
  repeat rewrite Zlength_app in *;
  repeat rewrite Zlength_cons in *;
  repeat rewrite Zlength_nil in *;
  repeat rewrite Z.sub_0_r in *.
  assert (Hnext : EditRemainingMatches s1_l s2_l t1_l t2_l sg1_2 sg2_2 (prefix1_2 ++ [1]) (prefix2_2 ++ [1]) (i + 1) c10_2 (replace_Znth a (Znth a c11_2 0 - 1) c11_2) c20_2 (replace_Znth b (Znth b c21_2 0 - 1) c21_2) (rest_2 - 1)).
  { eapply edit_remaining_common_step with (n := n_pre) (a := a) (b := b) (bit := 1); eauto; cbn [Z.eqb Pos.eqb]; lia. }
  pose proof (edit_remaining_count_bounds s1_l s2_l t1_l t2_l sg1_2 sg2_2 (prefix1_2 ++ [1]) (prefix2_2 ++ [1]) (i + 1) c10_2 (replace_Znth a (Znth a c11_2 0 - 1) c11_2) c20_2 (replace_Znth b (Znth b c21_2 0 - 1) c21_2) n_pre (rest_2 - 1)
    ltac:(lia) ltac:(lia) ltac:(rewrite ?Zlength_replace_Znth; lia) ltac:(rewrite ?Zlength_replace_Znth; lia)
    ltac:(rewrite ?Zlength_replace_Znth; lia) ltac:(rewrite ?Zlength_replace_Znth; lia) ltac:(lia) Hnext)
    as [[H10lo H10hi] [[H11lo H11hi] [[H20lo H20hi] [H21lo H21hi]]]].
  assert (Hprefix1 : Zlength (prefix1_2 ++ [1]) = i + 1) by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  assert (Hprefix2 : Zlength (prefix2_2 ++ [1]) = i + 1) by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  assert (Hprefix_score : (ans + 1) = EditPairMatches (prefix1_2 ++ [1]) (prefix2_2 ++ [1])).
  { rewrite edit_pair_app by lia. change (EditPairMatches [1] [1]) with 1.
    match goal with H : ans = EditPairMatches prefix1_2 prefix2_2 |- _ => rewrite <- H end; lia. }
  assert (Hanswer : EditStringsAnswer (map (Z.add 48) s1_l) (map (Z.add 48) s2_l)
    (map (Z.add 48) t1_l) (map (Z.add 48) t2_l) ((ans + 1) + (rest_2 - 1))).
  { replace ((ans + 1) + (rest_2 - 1)) with (ans + rest_2) by lia. assumption. }
  Exists (rest_2 - 1) (prefix2_2 ++ [1]) (prefix1_2 ++ [1]) sg2_2 sg1_2 (replace_Znth b (Znth b c21_2 0 - 1) c21_2) c20_2 (replace_Znth a (Znth a c11_2 0 - 1) c11_2) c10_2.
  split_pure_spatial.
  - edit_cancel.
  - edit_split_pures; dump_pre_spatial; try assumption; try congruence; try (timeout 2 lia).
Qed. 

Lemma proof_of_max_edit_string_matches_entail_wit_11_4 : max_edit_string_matches_entail_wit_11_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (IntArray.full_Zlength (&("cnt21")) n_pre (replace_Znth (b) (((Znth b c21_2 0) - 1 )) (c21_2))). Intros_p Harray_length_0.
  prop_apply (IntArray.full_Zlength (&("cnt10")) n_pre (replace_Znth (a) (((Znth a c10_2 0) - 1 )) (c10_2))). Intros_p Harray_length_1.
  prop_apply (IntArray.full_Zlength (&("cnt11")) n_pre c11_2). Intros_p Harray_length_2.
  prop_apply (IntArray.full_Zlength (&("cnt20")) n_pre c20_2). Intros_p Harray_length_3.
  prop_apply (IntArray.full_Zlength s1_pre n_pre s1_l). Intros_p Harray_length_4.
  prop_apply (IntArray.full_Zlength s2_pre n_pre s2_l). Intros_p Harray_length_5.
  prop_apply (IntArray.full_Zlength t1_pre n_pre t1_l). Intros_p Harray_length_6.
  prop_apply (IntArray.full_Zlength t2_pre n_pre t2_l). Intros_p Harray_length_7.
  prop_apply (IntArray.full_Zlength (&("seg1")) n_pre sg1_2). Intros_p Harray_length_8.
  prop_apply (IntArray.full_Zlength (&("seg2")) n_pre sg2_2). Intros_p Harray_length_9.
  repeat rewrite Zlength_replace_Znth in *;
  repeat rewrite Zlength_app in *;
  repeat rewrite Zlength_cons in *;
  repeat rewrite Zlength_nil in *;
  repeat rewrite Z.sub_0_r in *.
  assert (Hnext : EditRemainingMatches s1_l s2_l t1_l t2_l sg1_2 sg2_2 (prefix1_2 ++ [0]) (prefix2_2 ++ [1]) (i + 1) (replace_Znth a (Znth a c10_2 0 - 1) c10_2) c11_2 c20_2 (replace_Znth b (Znth b c21_2 0 - 1) c21_2) rest_2).
  { eapply edit_remaining_zero_one_step with (n := n_pre); eauto; lia. }
  pose proof (edit_remaining_count_bounds s1_l s2_l t1_l t2_l sg1_2 sg2_2 (prefix1_2 ++ [0]) (prefix2_2 ++ [1]) (i + 1) (replace_Znth a (Znth a c10_2 0 - 1) c10_2) c11_2 c20_2 (replace_Znth b (Znth b c21_2 0 - 1) c21_2) n_pre rest_2
    ltac:(lia) ltac:(lia) ltac:(rewrite ?Zlength_replace_Znth; lia) ltac:(rewrite ?Zlength_replace_Znth; lia)
    ltac:(rewrite ?Zlength_replace_Znth; lia) ltac:(rewrite ?Zlength_replace_Znth; lia) ltac:(lia) Hnext)
    as [[H10lo H10hi] [[H11lo H11hi] [[H20lo H20hi] [H21lo H21hi]]]].
  assert (Hprefix1 : Zlength (prefix1_2 ++ [0]) = i + 1) by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  assert (Hprefix2 : Zlength (prefix2_2 ++ [1]) = i + 1) by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  assert (Hprefix_score : ans = EditPairMatches (prefix1_2 ++ [0]) (prefix2_2 ++ [1])).
  { rewrite edit_pair_app by lia. change (EditPairMatches [0] [1]) with 0.
    match goal with H : ans = EditPairMatches prefix1_2 prefix2_2 |- _ => rewrite <- H end; lia. }
  assert (Hanswer : EditStringsAnswer (map (Z.add 48) s1_l) (map (Z.add 48) s2_l)
    (map (Z.add 48) t1_l) (map (Z.add 48) t2_l) (ans + rest_2)).
  { replace (ans + rest_2) with (ans + rest_2) by lia. assumption. }
  Exists rest_2 (prefix2_2 ++ [1]) (prefix1_2 ++ [0]) sg2_2 sg1_2 (replace_Znth b (Znth b c21_2 0 - 1) c21_2) c20_2 c11_2 (replace_Znth a (Znth a c10_2 0 - 1) c10_2).
  split_pure_spatial.
  - edit_cancel.
  - edit_split_pures; dump_pre_spatial; try assumption; try congruence; try (timeout 2 lia).
Qed. 

Lemma proof_of_max_edit_string_matches_entail_wit_11_5 : max_edit_string_matches_entail_wit_11_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (IntArray.full_Zlength (&("cnt21")) n_pre (replace_Znth (b) (((Znth b c21_2 0) - 1 )) (c21_2))). Intros_p Harray_length_0.
  prop_apply (IntArray.full_Zlength (&("cnt10")) n_pre (replace_Znth (a) (((Znth a c10_2 0) - 1 )) (c10_2))). Intros_p Harray_length_1.
  prop_apply (IntArray.full_Zlength (&("cnt11")) n_pre c11_2). Intros_p Harray_length_2.
  prop_apply (IntArray.full_Zlength (&("cnt20")) n_pre c20_2). Intros_p Harray_length_3.
  prop_apply (IntArray.full_Zlength s1_pre n_pre s1_l). Intros_p Harray_length_4.
  prop_apply (IntArray.full_Zlength s2_pre n_pre s2_l). Intros_p Harray_length_5.
  prop_apply (IntArray.full_Zlength t1_pre n_pre t1_l). Intros_p Harray_length_6.
  prop_apply (IntArray.full_Zlength t2_pre n_pre t2_l). Intros_p Harray_length_7.
  prop_apply (IntArray.full_Zlength (&("seg1")) n_pre sg1_2). Intros_p Harray_length_8.
  prop_apply (IntArray.full_Zlength (&("seg2")) n_pre sg2_2). Intros_p Harray_length_9.
  repeat rewrite Zlength_replace_Znth in *;
  repeat rewrite Zlength_app in *;
  repeat rewrite Zlength_cons in *;
  repeat rewrite Zlength_nil in *;
  repeat rewrite Z.sub_0_r in *.
  assert (Hnext : EditRemainingMatches s1_l s2_l t1_l t2_l sg1_2 sg2_2 (prefix1_2 ++ [0]) (prefix2_2 ++ [1]) (i + 1) (replace_Znth a (Znth a c10_2 0 - 1) c10_2) c11_2 c20_2 (replace_Znth b (Znth b c21_2 0 - 1) c21_2) rest_2).
  { eapply edit_remaining_zero_one_step with (n := n_pre); eauto; lia. }
  pose proof (edit_remaining_count_bounds s1_l s2_l t1_l t2_l sg1_2 sg2_2 (prefix1_2 ++ [0]) (prefix2_2 ++ [1]) (i + 1) (replace_Znth a (Znth a c10_2 0 - 1) c10_2) c11_2 c20_2 (replace_Znth b (Znth b c21_2 0 - 1) c21_2) n_pre rest_2
    ltac:(lia) ltac:(lia) ltac:(rewrite ?Zlength_replace_Znth; lia) ltac:(rewrite ?Zlength_replace_Znth; lia)
    ltac:(rewrite ?Zlength_replace_Znth; lia) ltac:(rewrite ?Zlength_replace_Znth; lia) ltac:(lia) Hnext)
    as [[H10lo H10hi] [[H11lo H11hi] [[H20lo H20hi] [H21lo H21hi]]]].
  assert (Hprefix1 : Zlength (prefix1_2 ++ [0]) = i + 1) by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  assert (Hprefix2 : Zlength (prefix2_2 ++ [1]) = i + 1) by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  assert (Hprefix_score : ans = EditPairMatches (prefix1_2 ++ [0]) (prefix2_2 ++ [1])).
  { rewrite edit_pair_app by lia. change (EditPairMatches [0] [1]) with 0.
    match goal with H : ans = EditPairMatches prefix1_2 prefix2_2 |- _ => rewrite <- H end; lia. }
  assert (Hanswer : EditStringsAnswer (map (Z.add 48) s1_l) (map (Z.add 48) s2_l)
    (map (Z.add 48) t1_l) (map (Z.add 48) t2_l) (ans + rest_2)).
  { replace (ans + rest_2) with (ans + rest_2) by lia. assumption. }
  Exists rest_2 (prefix2_2 ++ [1]) (prefix1_2 ++ [0]) sg2_2 sg1_2 (replace_Znth b (Znth b c21_2 0 - 1) c21_2) c20_2 c11_2 (replace_Znth a (Znth a c10_2 0 - 1) c10_2).
  split_pure_spatial.
  - edit_cancel.
  - edit_split_pures; dump_pre_spatial; try assumption; try congruence; try (timeout 2 lia).
Qed. 

Lemma proof_of_max_edit_string_matches_entail_wit_11_6 : max_edit_string_matches_entail_wit_11_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (IntArray.full_Zlength (&("cnt20")) n_pre (replace_Znth (b) (((Znth b c20_2 0) - 1 )) (c20_2))). Intros_p Harray_length_0.
  prop_apply (IntArray.full_Zlength (&("cnt11")) n_pre (replace_Znth (a) (((Znth a c11_2 0) - 1 )) (c11_2))). Intros_p Harray_length_1.
  prop_apply (IntArray.full_Zlength (&("cnt10")) n_pre c10_2). Intros_p Harray_length_2.
  prop_apply (IntArray.full_Zlength s1_pre n_pre s1_l). Intros_p Harray_length_3.
  prop_apply (IntArray.full_Zlength s2_pre n_pre s2_l). Intros_p Harray_length_4.
  prop_apply (IntArray.full_Zlength t1_pre n_pre t1_l). Intros_p Harray_length_5.
  prop_apply (IntArray.full_Zlength t2_pre n_pre t2_l). Intros_p Harray_length_6.
  prop_apply (IntArray.full_Zlength (&("seg1")) n_pre sg1_2). Intros_p Harray_length_7.
  prop_apply (IntArray.full_Zlength (&("seg2")) n_pre sg2_2). Intros_p Harray_length_8.
  prop_apply (IntArray.full_Zlength (&("cnt21")) n_pre c21_2). Intros_p Harray_length_9.
  repeat rewrite Zlength_replace_Znth in *;
  repeat rewrite Zlength_app in *;
  repeat rewrite Zlength_cons in *;
  repeat rewrite Zlength_nil in *;
  repeat rewrite Z.sub_0_r in *.
  assert (Hnext : EditRemainingMatches s1_l s2_l t1_l t2_l sg1_2 sg2_2 (prefix1_2 ++ [1]) (prefix2_2 ++ [0]) (i + 1) c10_2 (replace_Znth a (Znth a c11_2 0 - 1) c11_2) (replace_Znth b (Znth b c20_2 0 - 1) c20_2) c21_2 rest_2).
  { eapply edit_remaining_one_zero_step with (n := n_pre); eauto; lia. }
  pose proof (edit_remaining_count_bounds s1_l s2_l t1_l t2_l sg1_2 sg2_2 (prefix1_2 ++ [1]) (prefix2_2 ++ [0]) (i + 1) c10_2 (replace_Znth a (Znth a c11_2 0 - 1) c11_2) (replace_Znth b (Znth b c20_2 0 - 1) c20_2) c21_2 n_pre rest_2
    ltac:(lia) ltac:(lia) ltac:(rewrite ?Zlength_replace_Znth; lia) ltac:(rewrite ?Zlength_replace_Znth; lia)
    ltac:(rewrite ?Zlength_replace_Znth; lia) ltac:(rewrite ?Zlength_replace_Znth; lia) ltac:(lia) Hnext)
    as [[H10lo H10hi] [[H11lo H11hi] [[H20lo H20hi] [H21lo H21hi]]]].
  assert (Hprefix1 : Zlength (prefix1_2 ++ [1]) = i + 1) by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  assert (Hprefix2 : Zlength (prefix2_2 ++ [0]) = i + 1) by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  assert (Hprefix_score : ans = EditPairMatches (prefix1_2 ++ [1]) (prefix2_2 ++ [0])).
  { rewrite edit_pair_app by lia. change (EditPairMatches [1] [0]) with 0.
    match goal with H : ans = EditPairMatches prefix1_2 prefix2_2 |- _ => rewrite <- H end; lia. }
  assert (Hanswer : EditStringsAnswer (map (Z.add 48) s1_l) (map (Z.add 48) s2_l)
    (map (Z.add 48) t1_l) (map (Z.add 48) t2_l) (ans + rest_2)).
  { replace (ans + rest_2) with (ans + rest_2) by lia. assumption. }
  Exists rest_2 (prefix2_2 ++ [0]) (prefix1_2 ++ [1]) sg2_2 sg1_2 c21_2 (replace_Znth b (Znth b c20_2 0 - 1) c20_2) (replace_Znth a (Znth a c11_2 0 - 1) c11_2) c10_2.
  split_pure_spatial.
  - edit_cancel.
  - edit_split_pures; dump_pre_spatial; try assumption; try congruence; try (timeout 2 lia).
Qed. 

Lemma proof_of_max_edit_string_matches_entail_wit_11_7 : max_edit_string_matches_entail_wit_11_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (IntArray.full_Zlength (&("cnt20")) n_pre (replace_Znth (b) (((Znth b c20_2 0) - 1 )) (c20_2))). Intros_p Harray_length_0.
  prop_apply (IntArray.full_Zlength (&("cnt11")) n_pre (replace_Znth (a) (((Znth a c11_2 0) - 1 )) (c11_2))). Intros_p Harray_length_1.
  prop_apply (IntArray.full_Zlength (&("cnt10")) n_pre c10_2). Intros_p Harray_length_2.
  prop_apply (IntArray.full_Zlength (&("cnt21")) n_pre c21_2). Intros_p Harray_length_3.
  prop_apply (IntArray.full_Zlength s1_pre n_pre s1_l). Intros_p Harray_length_4.
  prop_apply (IntArray.full_Zlength s2_pre n_pre s2_l). Intros_p Harray_length_5.
  prop_apply (IntArray.full_Zlength t1_pre n_pre t1_l). Intros_p Harray_length_6.
  prop_apply (IntArray.full_Zlength t2_pre n_pre t2_l). Intros_p Harray_length_7.
  prop_apply (IntArray.full_Zlength (&("seg1")) n_pre sg1_2). Intros_p Harray_length_8.
  prop_apply (IntArray.full_Zlength (&("seg2")) n_pre sg2_2). Intros_p Harray_length_9.
  repeat rewrite Zlength_replace_Znth in *;
  repeat rewrite Zlength_app in *;
  repeat rewrite Zlength_cons in *;
  repeat rewrite Zlength_nil in *;
  repeat rewrite Z.sub_0_r in *.
  assert (Hnext : EditRemainingMatches s1_l s2_l t1_l t2_l sg1_2 sg2_2 (prefix1_2 ++ [1]) (prefix2_2 ++ [0]) (i + 1) c10_2 (replace_Znth a (Znth a c11_2 0 - 1) c11_2) (replace_Znth b (Znth b c20_2 0 - 1) c20_2) c21_2 rest_2).
  { eapply edit_remaining_one_zero_step with (n := n_pre); eauto; lia. }
  pose proof (edit_remaining_count_bounds s1_l s2_l t1_l t2_l sg1_2 sg2_2 (prefix1_2 ++ [1]) (prefix2_2 ++ [0]) (i + 1) c10_2 (replace_Znth a (Znth a c11_2 0 - 1) c11_2) (replace_Znth b (Znth b c20_2 0 - 1) c20_2) c21_2 n_pre rest_2
    ltac:(lia) ltac:(lia) ltac:(rewrite ?Zlength_replace_Znth; lia) ltac:(rewrite ?Zlength_replace_Znth; lia)
    ltac:(rewrite ?Zlength_replace_Znth; lia) ltac:(rewrite ?Zlength_replace_Znth; lia) ltac:(lia) Hnext)
    as [[H10lo H10hi] [[H11lo H11hi] [[H20lo H20hi] [H21lo H21hi]]]].
  assert (Hprefix1 : Zlength (prefix1_2 ++ [1]) = i + 1) by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  assert (Hprefix2 : Zlength (prefix2_2 ++ [0]) = i + 1) by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  assert (Hprefix_score : ans = EditPairMatches (prefix1_2 ++ [1]) (prefix2_2 ++ [0])).
  { rewrite edit_pair_app by lia. change (EditPairMatches [1] [0]) with 0.
    match goal with H : ans = EditPairMatches prefix1_2 prefix2_2 |- _ => rewrite <- H end; lia. }
  assert (Hanswer : EditStringsAnswer (map (Z.add 48) s1_l) (map (Z.add 48) s2_l)
    (map (Z.add 48) t1_l) (map (Z.add 48) t2_l) (ans + rest_2)).
  { replace (ans + rest_2) with (ans + rest_2) by lia. assumption. }
  Exists rest_2 (prefix2_2 ++ [0]) (prefix1_2 ++ [1]) sg2_2 sg1_2 c21_2 (replace_Znth b (Znth b c20_2 0 - 1) c20_2) (replace_Znth a (Znth a c11_2 0 - 1) c11_2) c10_2.
  split_pure_spatial.
  - edit_cancel.
  - edit_split_pures; dump_pre_spatial; try assumption; try congruence; try (timeout 2 lia).
Qed. 

Lemma proof_of_max_edit_string_matches_entail_wit_12 : max_edit_string_matches_entail_wit_12.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  prop_apply (IntArray.full_Zlength s1_pre n_pre s1_l). Intros_p Harray_length_0.
  prop_apply (IntArray.full_Zlength s2_pre n_pre s2_l). Intros_p Harray_length_1.
  prop_apply (IntArray.full_Zlength t1_pre n_pre t1_l). Intros_p Harray_length_2.
  prop_apply (IntArray.full_Zlength t2_pre n_pre t2_l). Intros_p Harray_length_3.
  prop_apply (IntArray.full_Zlength (&("seg1")) n_pre sg1). Intros_p Harray_length_4.
  prop_apply (IntArray.full_Zlength (&("seg2")) n_pre sg2). Intros_p Harray_length_5.
  prop_apply (IntArray.full_Zlength (&("cnt10")) n_pre c10). Intros_p Harray_length_6.
  prop_apply (IntArray.full_Zlength (&("cnt11")) n_pre c11). Intros_p Harray_length_7.
  prop_apply (IntArray.full_Zlength (&("cnt20")) n_pre c20). Intros_p Harray_length_8.
  prop_apply (IntArray.full_Zlength (&("cnt21")) n_pre c21). Intros_p Harray_length_9.
  repeat rewrite Zlength_replace_Znth in *;
  repeat rewrite Zlength_app in *;
  repeat rewrite Zlength_cons in *;
  repeat rewrite Zlength_nil in *;
  repeat rewrite Z.sub_0_r in *.
  assert (Hi_end : i = n_pre) by lia. rewrite Hi_end in *. clear i Hi_end.
  pose proof (edit_remaining_empty s1_l s2_l t1_l t2_l sg1 sg2 prefix1 prefix2
    c10 c11 c20 c21 n_pre rest ltac:(lia) ltac:(lia) ltac:(eassumption)) as Hzero.
  subst rest. rewrite Z.add_0_r in *.
  sep_apply_l_atomic (IntArray.full_to_undef_full (&("seg1")) n_pre sg1).
  sep_apply_l_atomic (IntArray.undef_full_to_undef_seg (&("seg1")) n_pre).
  sep_apply_l_atomic (IntArray.undef_seg_merge_to_undef_full (&("seg1")) 0 n_pre 100000 ltac:(lia)).
  sep_apply_l_atomic (IntArray.full_to_undef_full (&("seg2")) n_pre sg2).
  sep_apply_l_atomic (IntArray.undef_full_to_undef_seg (&("seg2")) n_pre).
  sep_apply_l_atomic (IntArray.undef_seg_merge_to_undef_full (&("seg2")) 0 n_pre 100000 ltac:(lia)).
  sep_apply_l_atomic (IntArray.full_to_undef_full (&("cnt10")) n_pre c10).
  sep_apply_l_atomic (IntArray.undef_full_to_undef_seg (&("cnt10")) n_pre).
  sep_apply_l_atomic (IntArray.undef_seg_merge_to_undef_full (&("cnt10")) 0 n_pre 100000 ltac:(lia)).
  sep_apply_l_atomic (IntArray.full_to_undef_full (&("cnt11")) n_pre c11).
  sep_apply_l_atomic (IntArray.undef_full_to_undef_seg (&("cnt11")) n_pre).
  sep_apply_l_atomic (IntArray.undef_seg_merge_to_undef_full (&("cnt11")) 0 n_pre 100000 ltac:(lia)).
  sep_apply_l_atomic (IntArray.full_to_undef_full (&("cnt20")) n_pre c20).
  sep_apply_l_atomic (IntArray.undef_full_to_undef_seg (&("cnt20")) n_pre).
  sep_apply_l_atomic (IntArray.undef_seg_merge_to_undef_full (&("cnt20")) 0 n_pre 100000 ltac:(lia)).
  sep_apply_l_atomic (IntArray.full_to_undef_full (&("cnt21")) n_pre c21).
  sep_apply_l_atomic (IntArray.undef_full_to_undef_seg (&("cnt21")) n_pre).
  sep_apply_l_atomic (IntArray.undef_seg_merge_to_undef_full (&("cnt21")) 0 n_pre 100000 ltac:(lia)).
  rewrite ?Z.mul_0_l, ?Z.add_0_r, ?Z.sub_0_r.
  remember 100000 as scratch_capacity eqn:Hscratch_capacity.
  apply _derivable1_andp_intros.
  - dump_pre_spatial; assumption.
  - cancel (IntArray.undef_full (&("seg1")) scratch_capacity).
    cancel (IntArray.undef_full (&("seg2")) scratch_capacity).
    cancel (IntArray.undef_full (&("cnt10")) scratch_capacity).
    cancel (IntArray.undef_full (&("cnt11")) scratch_capacity).
    cancel (IntArray.undef_full (&("cnt20")) scratch_capacity).
    cancel (IntArray.undef_full (&("cnt21")) scratch_capacity).
    cancel (IntArray.full s1_pre n_pre s1_l).
    cancel (IntArray.full s2_pre n_pre s2_l).
    cancel (IntArray.full t1_pre n_pre t1_l).
    all: apply derivable1_refl.
Qed.
