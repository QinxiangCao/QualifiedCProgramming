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
From SimpleC.EE.QCP_demos_human Require Import int_array_merge_rel_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Local Open Scope list.
Import naive_C_Rules.

From SimpleC.EE.QCP_demos_human Require Import sll_merge_rel_lib.
Local Open Scope monad.
From SimpleC.EE.QCP_demos_human Require Import int_array_merge_rel_lib.
Local Open Scope sac.

Lemma proof_of_merge_entail_wit_1 : merge_entail_wit_1.
Proof. 
  pre_process.
  Exists l0 (@nil Z) (@nil Z).
  Exists s1 s2 (@nil Z).
  entailer!.
  cbn. entailer!.
Qed.  

Lemma proof_of_merge_entail_wit_2_2 : merge_entail_wit_2_2.
Proof. 
  pre_process.
  replace (k - k) with 0 in * by lia.
  replace (j - j) with 0 in * by lia.
  replace (i - i) with 0 in * by lia.
  prop_apply (IntArray.seg_length arr_pre j).
  Intros.
  destruct l2_2; [simpl in H ; lia | ].
  clear H.
  prop_apply (IntArray.seg_length ret_pre k).
  Intros.
  destruct l6_2;[simpl in H ; lia | ].
  clear H.
  rewrite Znth0_cons.
  replace (replace_Znth 0 z (z0 :: l6_2)) with (z :: l6_2) by easy.
  rewrite (IntArray.seg_unfold ret_pre).
  rewrite (IntArray.seg_unfold arr_pre).
  sep_apply (IntArray.seg_single arr_pre).
  sep_apply (IntArray.seg_single ret_pre).
  sep_apply (IntArray.seg_merge_to_seg arr_pre (q_pre + 1) j (j + 1));[ | lia].
  sep_apply (IntArray.seg_merge_to_seg ret_pre p_pre k (k + 1));[ | lia].
  prop_apply (IntArray.seg_length arr_pre i).
  Exists l6_2 (l5_2 ++ z :: nil) l4_2.
  Exists l1_2 l2_2 (l3_2 ++ z :: nil).
  entailer!.
  unfold merge_from_mid_rel in *.
  rewrite (repeat_break_unfold _ _) in PreH4.
  prove_by_one_abs_step (by_continue (l1_2, l2_2, l3_2 ++ z :: nil)).
  destruct l1_2 ; [ simpl in H1; lia | ].
  unfold merge_body.
  rewrite !Znth0_cons in PreH1.
  abs_choice_right.
  abs_test_step; [ lia | ].
  abs_ret_step.
Qed. 

Lemma proof_of_merge_entail_wit_2_1 : merge_entail_wit_2_1.
Proof. 
  pre_process.
  replace (k - k) with 0 in * by lia.
  replace (j - j) with 0 in * by lia.
  replace (i - i) with 0 in * by lia.
  prop_apply (IntArray.seg_length arr_pre i).
  Intros.
  destruct l1_2;[simpl in H ; lia | ].
  clear H.
  prop_apply (IntArray.seg_length ret_pre k).
  Intros.
  destruct l6_2;[simpl in H ; lia | ].
  clear H.
  rewrite Znth0_cons.
  replace (replace_Znth 0 z (z0 :: l6_2)) with (z :: l6_2) by easy.
  rewrite (IntArray.seg_unfold ret_pre).
  rewrite (IntArray.seg_unfold arr_pre).
  sep_apply (IntArray.seg_single arr_pre).
  sep_apply (IntArray.seg_single ret_pre).
  sep_apply (IntArray.seg_merge_to_seg arr_pre p_pre i (i + 1));[ | lia].
  sep_apply (IntArray.seg_merge_to_seg ret_pre p_pre k (k + 1));[ | lia].
  prop_apply (IntArray.seg_length arr_pre j).
  Exists l6_2 l5_2 (l4_2 ++ z :: nil).
  Exists l1_2 l2_2 (l3_2 ++ z :: nil).
  entailer!.
  unfold merge_from_mid_rel in *.
  rewrite (repeat_break_unfold _ _) in PreH4.
  prove_by_one_abs_step (by_continue (l1_2, l2_2, l3_2 ++ z :: nil)).
  destruct l2_2 ; [ simpl in H1 ; lia | ].
  unfold merge_body.
  rewrite !Znth0_cons in PreH1.
  abs_choice_left.
  abs_test_step; [ lia | ].
  abs_ret_step.
Qed. 

Lemma proof_of_merge_entail_wit_3_1 : merge_entail_wit_3_1.
Proof. 
  pre_process.
  Left.
  Exists l6_2 l5_2 l4_2.
  Exists l1_2 l2_2 l3_2.
  prop_apply (IntArray.seg_length arr_pre i).
  Intros.
  assert (i = q_pre + 1) by lia.
  entailer!.
Qed.

Lemma proof_of_merge_entail_wit_3_2 : merge_entail_wit_3_2.
Proof. 
  pre_process.
  Exists l6_2 l5_2 l4_2.
  Exists l1_2 l2_2 l3_2.
  prop_apply (IntArray.seg_length arr_pre j).
  Intros.
  assert (j = r_pre + 1) by lia.
  entailer!.
Qed. 

Lemma proof_of_merge_entail_wit_4 : merge_entail_wit_4.
Proof. 
  pre_process.
  replace (k - k) with 0 in * by lia.
  replace (j - j) with 0 in * by lia.
  replace (i - i) with 0 in * by lia.
  prop_apply (IntArray.seg_length arr_pre i).
  Intros.
  destruct l1_2;[simpl in H ; lia | ].
  clear H.
  prop_apply (IntArray.seg_length ret_pre k).
  Intros.
  destruct l6_2;[simpl in H ; lia | ].
  clear H.
  rewrite Znth0_cons.
  replace (replace_Znth 0 z (z0 :: l6_2)) with (z :: l6_2) by easy.
  rewrite (IntArray.seg_unfold ret_pre).
  rewrite (IntArray.seg_unfold arr_pre).
  sep_apply (IntArray.seg_single arr_pre).
  sep_apply (IntArray.seg_single ret_pre).
  sep_apply (IntArray.seg_merge_to_seg arr_pre p_pre i (i + 1));[ | lia].
  sep_apply (IntArray.seg_merge_to_seg ret_pre p_pre k (k + 1));[ | lia].
  prop_apply (IntArray.seg_length arr_pre j).
  Right.
  Exists l6_2 l5_2 (l4_2 ++ z :: nil).
  Exists l1_2 l2_2 (l3_2 ++ z :: nil).
  entailer!.
  replace (r_pre + 1 - j) with 0 in * by lia.
  destruct l2_2. 2:{ simpl in H1. lia. }
  unfold merge_from_mid_rel in *.
  rewrite (repeat_break_unfold _ _) in PreH2.
  rewrite (repeat_break_unfold _ _).
  cbn [merge_body] in *.
  destruct l1_2.
  rewrite <- app_assoc. easy.
  rewrite <- app_assoc. easy.
Qed. 

Lemma proof_of_merge_entail_wit_5_1 : merge_entail_wit_5_1.
Proof. 
  pre_process.
  prop_apply (IntArray.seg_length arr_pre i).
  Intros.
  destruct l1. 2:{ simpl in H.  lia. }
  Exists l6_2 l5_2 l4_2.
  Exists l2_2 l3_2.
  rewrite (IntArray.seg_empty). entailer!.
Qed. 

Lemma proof_of_merge_entail_wit_5_2 : merge_entail_wit_5_2.
Proof. 
  pre_process.
  prop_apply (IntArray.seg_length arr_pre i).
  Intros.
  destruct l1. 2:{  simpl in H. lia. }
  Exists l6_2 l5_2 l4_2.
  Exists l2_2 l3_2.
  rewrite (IntArray.seg_empty). 
  entailer!.
Qed.

Lemma proof_of_merge_entail_wit_6 : merge_entail_wit_6.
Proof. 
  pre_process.
  replace (k - k) with 0 in * by lia.
  replace (j - j) with 0 in * by lia.
  replace (i - i) with 0 in * by lia.
  prop_apply (IntArray.seg_length arr_pre j).
  Intros.
  destruct l2_2;[simpl in H ;lia | ].
  clear H.
  prop_apply (IntArray.seg_length ret_pre k).
  Intros.
  destruct l6_2;[simpl in H;lia | ].
  clear H.
  rewrite Znth0_cons.
  replace (replace_Znth 0 z (z0 :: l6_2)) with (z :: l6_2) by easy.
  rewrite (IntArray.seg_unfold ret_pre).
  rewrite (IntArray.seg_unfold arr_pre).
  sep_apply (IntArray.seg_single arr_pre).
  sep_apply (IntArray.seg_single ret_pre).
  sep_apply (IntArray.seg_merge_to_seg arr_pre (q_pre + 1) j (j + 1));[ | lia].
  sep_apply (IntArray.seg_merge_to_seg ret_pre p_pre k (k + 1));[ | lia].
  Exists l6_2 (l5_2 ++ z :: nil) l4_2.
  Exists l2_2 (l3_2 ++ z :: nil).
  entailer!.
  unfold merge_from_mid_rel in *.
  rewrite (repeat_break_unfold _ _) in PreH2.
  rewrite (repeat_break_unfold _ _).
  cbn [merge_body] in *.
  rewrite <- app_assoc. easy.
Qed. 

Lemma proof_of_merge_return_wit_1 : merge_return_wit_1.
Proof. 
  pre_process.
  subst i.
  prop_apply (IntArray.seg_length arr_pre j).
  Intros.
  destruct l2 ; simpl in H ; try lia.
  replace j with (r_pre + 1) in * by lia.
  replace k with (r_pre + 1) in * by lia.
  prop_apply (IntArray.seg_length ret_pre (r_pre + 1)).
  Intros.
  destruct l6.
  2: { simpl in H0. lia.  }
  do 2 rewrite (IntArray.seg_empty).
  Intros.
  sep_apply (IntArray.seg_merge_to_seg) ; try lia.
  Exists (l4 ++ l5) l3.
  entailer!.
  unfold merge_from_mid_rel in PreH2.
  rewrite (repeat_break_unfold _ _) in PreH2.
  rewrite <- (app_nil_r l3).
  prove_by_one_abs_step (by_break (l3 ++ nil)).
  abs_ret_step.
Qed.

Lemma proof_of_mergeSort_safety_wit_1 : mergeSort_safety_wit_1.
Proof. 
  pre_process.
  assert (0 <= (r_pre - l_pre) ÷ 2 < r_pre - l_pre ).
  { split.
    apply Z.quot_pos; lia.
    apply Z.quot_lt;lia. }
  entailer!.
Qed. 

Lemma proof_of_mergeSort_entail_wit_1 : mergeSort_entail_wit_1.
Proof. 
  pre_process.
  rename s1_low_level_spec into s1.
  rename X_low_level_spec into X.
  assert (0 <= (r_pre - l_pre) ÷ 2 < r_pre - l_pre ).
  { split.
    apply Z.quot_pos; lia.
    apply Z.quot_lt;lia. }
  prop_apply IntArray.seg_Zlength.
  Intros.
  rewrite IntArray.seg_split_to_seg with (mid :=  (l_pre + (r_pre - l_pre) ÷ 2 + 1)) by lia.
  rewrite IntArray.seg_split_to_seg with (x:= ret_pre) (mid :=  (l_pre + (r_pre - l_pre) ÷ 2 + 1)) by lia.
  Exists (sublist 0 (l_pre + (r_pre - l_pre) ÷ 2 + 1 - l_pre) s1) (sublist (l_pre + (r_pre - l_pre) ÷ 2 + 1 - l_pre) (r_pre + 1 - l_pre) s1).
  entailer!.
  replace ((l_pre + (r_pre - l_pre) ÷ 2 + 1 - l_pre)) with ((r_pre - l_pre) ÷ 2 + 1) by lia.
  assert (Zlength  (sublist ((r_pre - l_pre) ÷ 2 + 1) (r_pre + 1 - l_pre) s1) = (r_pre - l_pre) - ((r_pre - l_pre) ÷ 2)).
  { rewrite Zlength_sublist ; try lia. }
  destruct (sublist ((r_pre - l_pre) ÷ 2 + 1) (r_pre + 1 - l_pre) s1) eqn:?. 
  rewrite Zlength_nil in H1. lia.
  unfold mergesortrec_loc1.
  rewrite (gmergesortrec_unfold s1) in PreH2.
  unfold gmergesortrec_f in PreH2.
  safe_choice_r PreH2 ; try lia.
  prove_by_one_abs_step ((sublist 0 ((r_pre - l_pre) ÷ 2 + 1) s1), (z::l)).
  apply hseval_stateless_ret.
  unfold ext_split.
  rewrite <- Heql.
  rewrite <- sublist_split ; try lia.
  rewrite sublist_self by easy.
  auto.
Qed. 

Lemma proof_of_mergeSort_entail_wit_2 : mergeSort_entail_wit_2.
Proof. 
  pre_process.
  Exists l2_3 l2_2 l1_2.
  entailer!.
Qed. 

Lemma proof_of_mergeSort_entail_wit_3 : mergeSort_entail_wit_3.
Proof. 
  pre_process.
  Exists (l3 ++ l2) l1 l1_2.
  entailer!.
  prop_apply (IntArray.seg_length ret_pre (m + 1)).
  prop_apply (IntArray.seg_length ret_pre l_pre).
  Intros.
  apply (IntArray.seg_merge_to_seg); try lia.
Qed.

Lemma proof_of_mergeSort_return_wit_2 : mergeSort_return_wit_2.
Proof.
  pre_process.
  prop_apply (IntArray.seg_length arr_pre l_pre).
  Intros.
  Exists s1_low_level_spec s1_low_level_spec.
  entailer!.
  destruct s1_low_level_spec. simpl in H. lia.
  destruct s1_low_level_spec. 2:{ simpl in H. lia. }
  rewrite (gmergesortrec_unfold _) in PreH2.
  unfold gmergesortrec_f in PreH2.
  safe_choice_l PreH2.
  eapply highstependret_derive with (P':= (fun _ => ATrue)); eauto.
  apply hseval_stateless_ret.
  unfold ext_sort.
  easy.
Qed.

Lemma proof_of_mergeSort_derive_low_level_spec_aux_by_low_level_spec : mergeSort_derive_low_level_spec_aux_by_low_level_spec.
Proof. 
  pre_process.
  Exists l0_low_level_spec_aux.
  eapply safeExec_bind in H as (X' & ? & ?).
  Exists X'.
  entailer!.
  apply derivable1_wand_sepcon_adjoint.
  Intros s3 s2.
  Exists s3 s2.
  unfold applyf.
  entailer!.
Qed. 
