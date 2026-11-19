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
From SimpleC.EE.stdlib.glibc Require Import two_way_rel_legacy_goal.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
From SimpleC.EE.stdlib.glibc Require Import two_way_rel_lib.
From SimpleC.EE.stdlib.glibc Require Import two_way_critical_factorization_theorem.
From SimpleC.EE.stdlib.glibc Require Import two_way_match.
From SimpleC.EE.stdlib.glibc Require Import two_way_match_long_needle.
From SimpleC.EE.stdlib.glibc Require Import two_way_match_generic.
Local Open Scope monad.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap relations.
From FP Require Import PartialOrder_Setoid BourbakiWitt.
Local Open Scope sac.

Lemma proof_of_critical_factorization_entail_wit_1 : critical_factorization_entail_wit_1.
Proof. unfold critical_factorization_entail_wit_1; intros; Intros; entailer!. Qed. 

Lemma proof_of_critical_factorization_entail_wit_2_1 : critical_factorization_entail_wit_2_1.
Proof.
    unfold critical_factorization_entail_wit_2_1; intros; Intros.
    prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec). Intros.
    entailer!.
    - sep_apply (store_uchar_undef_store_uchar (&("a")) (Znth (j + k) needle0_low_level_spec 0)).
      sep_apply (store_uchar_undef_store_uchar (&("b")) (Znth (max_suffix + k) needle0_low_level_spec 0)).
      entailer!.
    - unfold first_loop_bind in *.
      unfold maxsuf_fwd_from_state in *.
      unfold maxsuf_cal in *.
      unfold_loop in H2.
      prog_nf in H2.
      unfold maxsuf_cal_body in H2 at 1.
      safe_choice_r H2; try lia.
      destruct (Znth (j + k) needle0_low_level_spec 0 ?= Znth (max_suffix + k) needle0_low_level_spec 0) eqn:Hcmp.
      + apply Z.compare_eq in Hcmp. lia.
      + rewrite Z.compare_lt_iff in Hcmp. lia.
      + unfold continue in H2. prog_nf in H2. exact H2.
Qed. 

Lemma proof_of_critical_factorization_entail_wit_2_2 : critical_factorization_entail_wit_2_2.
Proof.
    unfold critical_factorization_entail_wit_2_2; intros; Intros.
    prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec). Intros.
    entailer!.
    - sep_apply (store_uchar_undef_store_uchar (&("a")) (Znth (j + k) needle0_low_level_spec 0)).
      sep_apply (store_uchar_undef_store_uchar (&("b")) (Znth (max_suffix + k) needle0_low_level_spec 0)).
      entailer!.
    - unfold first_loop_bind in *.
      unfold maxsuf_fwd_from_state in *.
      unfold maxsuf_cal in *.
      unfold_loop in H3.
      prog_nf in H3.
      unfold maxsuf_cal_body in H3 at 1.
      safe_choice_r H3; try lia.
      destruct (Znth (j + k) needle0_low_level_spec 0 ?= Znth (max_suffix + k) needle0_low_level_spec 0) eqn:Hcmp.
      + safe_choice_l H3; try lia.
        unfold continue in H3. prog_nf in H3. exact H3.
      + rewrite Z.compare_lt_iff in Hcmp. lia.
      + rewrite Z.compare_gt_iff in Hcmp. lia.
Qed. 

Lemma proof_of_critical_factorization_entail_wit_2_3 : critical_factorization_entail_wit_2_3.
Proof.
    unfold critical_factorization_entail_wit_2_3; intros; Intros.
    prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec). Intros.
    entailer!.
    - sep_apply (store_uchar_undef_store_uchar (&("a")) (Znth (j + k) needle0_low_level_spec 0)).
      sep_apply (store_uchar_undef_store_uchar (&("b")) (Znth (max_suffix + k) needle0_low_level_spec 0)).
      entailer!.
    - unfold first_loop_bind in *.
      unfold maxsuf_fwd_from_state in *.
      unfold maxsuf_cal in *.
      unfold_loop in H3.
      prog_nf in H3.
      unfold maxsuf_cal_body in H3 at 1.
      safe_choice_r H3; try lia.
      destruct (Znth (j + k) needle0_low_level_spec 0 ?= Znth (max_suffix + k) needle0_low_level_spec 0) eqn:Hcmp.
      + safe_choice_r H3; try lia.
        unfold continue in H3. prog_nf in H3. exact H3.
      + rewrite Z.compare_lt_iff in Hcmp. lia.
      + rewrite Z.compare_gt_iff in Hcmp. lia.
Qed. 

Lemma proof_of_critical_factorization_entail_wit_2_4 : critical_factorization_entail_wit_2_4.
Proof.
    unfold critical_factorization_entail_wit_2_4; intros; Intros.
    prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec). Intros.
    entailer!.
    - sep_apply (store_uchar_undef_store_uchar (&("a")) (Znth (j + k) needle0_low_level_spec 0)).
      sep_apply (store_uchar_undef_store_uchar (&("b")) (Znth (max_suffix + k) needle0_low_level_spec 0)).
      entailer!.
    - unfold first_loop_bind in *.
      unfold maxsuf_fwd_from_state in *.
      unfold maxsuf_cal in *.
      unfold_loop in H1.
      prog_nf in H1.
      unfold maxsuf_cal_body in H1 at 1.
      safe_choice_r H1; try lia.
      destruct (Znth (j + k) needle0_low_level_spec 0 ?= Znth (max_suffix + k) needle0_low_level_spec 0) eqn:Hcmp.
      + apply Z.compare_eq in Hcmp. lia.
      + unfold continue in H1. prog_nf in H1. exact H1.
      + rewrite Z.compare_gt_iff in Hcmp. lia.
Qed. 

Lemma proof_of_critical_factorization_entail_wit_3 : critical_factorization_entail_wit_3.
Proof.
    unfold critical_factorization_entail_wit_3; intros; Intros.
    prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec). Intros.
    Exists p. entailer!.
    unfold first_loop_bind in H0.
    unfold maxsuf_fwd_from_state in H0.
    unfold maxsuf_rev_from in H0.
    unfold maxsuf_rev in H0.
    unfold second_loop_bind.
    unfold maxsuf_rev_from_state.
    unfold maxsuf_cal in H0 at 1.
    unfold_loop in H0.
    unfold maxsuf_cal_body in H0 at 1.
    safe_choice_l H0; try lia.
    unfold break in H0. prog_nf in H0. exact H0.
Qed. 

Lemma proof_of_critical_factorization_entail_wit_4_1 : critical_factorization_entail_wit_4_1.
Proof.
    unfold critical_factorization_entail_wit_4_1; intros; Intros.
    prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec). Intros.
    Exists mp_2. entailer!.
    - sep_apply (store_uchar_undef_store_uchar (&("a")) (Znth (j + k) needle0_low_level_spec 0)).
      sep_apply (store_uchar_undef_store_uchar (&("b")) (Znth (max_suffix_rev + k) needle0_low_level_spec 0)).
      entailer!.
    - unfold second_loop_bind in *.
      unfold maxsuf_rev_from_state in *.
      unfold maxsuf_cal in *.
      unfold_loop in H2.
      prog_nf in H2.
      unfold maxsuf_cal_body in H2 at 1.
      safe_choice_r H2; try lia.
      destruct (Znth (max_suffix_rev + k) needle0_low_level_spec 0 ?= Znth (j + k) needle0_low_level_spec 0) eqn:Hcmp.
      + apply Z.compare_eq in Hcmp. lia.
      + rewrite Z.compare_lt_iff in Hcmp. lia.
      + unfold continue in H2. prog_nf in H2. exact H2.
Qed. 

Lemma proof_of_critical_factorization_entail_wit_4_2 : critical_factorization_entail_wit_4_2.
Proof.
    unfold critical_factorization_entail_wit_4_2; intros; Intros.
    prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec). Intros.
    Exists mp_2. entailer!.
    - sep_apply (store_uchar_undef_store_uchar (&("a")) (Znth (j + k) needle0_low_level_spec 0)).
      sep_apply (store_uchar_undef_store_uchar (&("b")) (Znth (max_suffix_rev + k) needle0_low_level_spec 0)).
      entailer!.
    - unfold second_loop_bind in *.
      unfold maxsuf_rev_from_state in *.
      unfold maxsuf_cal in *.
      unfold_loop in H3.
      prog_nf in H3.
      unfold maxsuf_cal_body in H3 at 1.
      safe_choice_r H3; try lia.
      destruct (Znth (max_suffix_rev + k) needle0_low_level_spec 0 ?= Znth (j + k) needle0_low_level_spec 0) eqn:Hcmp.
      + safe_choice_l H3; try lia.
        unfold continue in H3. prog_nf in H3. exact H3.
      + rewrite Z.compare_lt_iff in Hcmp. lia.
      + rewrite Z.compare_gt_iff in Hcmp. lia.
Qed. 

Lemma proof_of_critical_factorization_entail_wit_4_3 : critical_factorization_entail_wit_4_3.
Proof.
    unfold critical_factorization_entail_wit_4_3; intros; Intros.
    prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec). Intros.
    Exists mp_2. entailer!.
    - sep_apply (store_uchar_undef_store_uchar (&("a")) (Znth (j + k) needle0_low_level_spec 0)).
      sep_apply (store_uchar_undef_store_uchar (&("b")) (Znth (max_suffix_rev + k) needle0_low_level_spec 0)).
      entailer!.
    - unfold second_loop_bind in *.
      unfold maxsuf_rev_from_state in *.
      unfold maxsuf_cal in *.
      unfold_loop in H3.
      prog_nf in H3.
      unfold maxsuf_cal_body in H3 at 1.
      safe_choice_r H3; try lia.
      destruct (Znth (max_suffix_rev + k) needle0_low_level_spec 0 ?= Znth (j + k) needle0_low_level_spec 0) eqn:Hcmp.
      + safe_choice_r H3; try lia.
        unfold continue in H3. prog_nf in H3. exact H3.
      + rewrite Z.compare_lt_iff in Hcmp. lia.
      + rewrite Z.compare_gt_iff in Hcmp. lia.
Qed. 

Lemma proof_of_critical_factorization_entail_wit_4_4 : critical_factorization_entail_wit_4_4.
Proof.
    unfold critical_factorization_entail_wit_4_4; intros; Intros.
    prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec). Intros.
    Exists mp_2. entailer!.
    - sep_apply (store_uchar_undef_store_uchar (&("a")) (Znth (j + k) needle0_low_level_spec 0)).
      sep_apply (store_uchar_undef_store_uchar (&("b")) (Znth (max_suffix_rev + k) needle0_low_level_spec 0)).
      entailer!.
    - unfold second_loop_bind in *.
      unfold maxsuf_rev_from_state in *.
      unfold maxsuf_cal in *.
      unfold_loop in H1.
      prog_nf in H1.
      unfold maxsuf_cal_body in H1 at 1.
      safe_choice_r H1; try lia.
      destruct (Znth (max_suffix_rev + k) needle0_low_level_spec 0 ?= Znth (j + k) needle0_low_level_spec 0) eqn:Hcmp.
      + apply Z.compare_eq in Hcmp. lia.
      + unfold continue in H1. prog_nf in H1. exact H1.
      + rewrite Z.compare_gt_iff in Hcmp. lia.
Qed. 

Lemma proof_of_critical_factorization_return_wit_1 : critical_factorization_return_wit_1.
Proof.
    unfold critical_factorization_return_wit_1; intros; Intros.
    prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec). Intros.
    Exists p. entailer!.
    unfold second_loop_bind in H1.
    unfold maxsuf_choose_with_ms in H1.
    unfold maxsuf_rev_from_state in H1.
    unfold maxsuf_cal in H1.
    unfold_loop in H1.
    unfold maxsuf_cal_body in H1 at 1.
    safe_choice_l H1; try lia.
    unfold break in H1. prog_nf in H1.
    safe_choice_r H1; try lia.
    exact H1.
Qed. 

Lemma proof_of_critical_factorization_return_wit_2 : critical_factorization_return_wit_2.
Proof.
    unfold critical_factorization_return_wit_2; intros; Intros.
    prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec). Intros.
    Exists mp_2. entailer!.
    unfold second_loop_bind in H1.
    unfold maxsuf_choose_with_ms in H1.
    unfold maxsuf_rev_from_state in H1.
    unfold maxsuf_cal in H1.
    unfold_loop in H1.
    unfold maxsuf_cal_body in H1 at 1.
    safe_choice_l H1; try lia.
    unfold break in H1. prog_nf in H1.
    safe_choice_l H1; try lia.
    exact H1.
Qed. 

Lemma proof_of_two_way_short_needle_entail_wit_1 : two_way_short_needle_entail_wit_1.
Proof. 
    pre_process.
    prop_apply UCharArray.full_Zlength. Intros.
    (first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; auto; try lia] | cancel]).
    match goal with Hex : safeExec _ (applyf (two_way_generic_after_factorization _ _) _) _ |- _ => rename Hex into Hexec end.
    unfold two_way_generic_after_factorization in Hexec.
    unfold applyf in Hexec. simpl in Hexec.
    unfold generic_match_phase in Hexec.
    safe_choice_l Hexec.
    - prog_nf in Hexec.
      exact Hexec.
    - unfold memcmp_result in H0.
      unfold memcmp_eq in H0.
      unfold repetitive_split.
      replace (0 + retval) with retval in H0 by lia.
      replace (mp + retval) with (retval + mp) in H0 by lia.
      apply H0 in H. exact H.
Qed. 

Lemma proof_of_two_way_short_needle_entail_wit_2_1 : two_way_short_needle_entail_wit_2_1.
Proof.
    pre_process.
    prop_apply (UCharArray.full_Zlength haystack_pre haystack_len_pre hay0_low_level_spec).
    prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
    Intros.
    (first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; auto; try lia] | cancel]).
    match goal with Hex : safeExec _ (generic_match_periodic_from _ _ _ _ _ _) _ |- _ => rename Hex into Hexec end.
    unfold generic_match_periodic_from in Hexec at 1.
    unfold_loop in Hexec.
    prog_nf in Hexec.
    unfold generic_match_periodic_loop_body in Hexec at 1.
    safe_choice_r Hexec.
    unfold match_periodic_loop_body in Hexec at 1.
    prog_nf in Hexec.
    safe_choice_l Hexec; try lia.
    unfold generic_match_periodic_from_right.
    rewrite Z.max_r in Hexec by lia.
    unfold generic_match_periodic_from.
    eapply safeExec_proequiv; [| exact Hexec].
    apply common_step_equiv.
    intros [[pos' memory'] | res]; reflexivity.
Qed. 

Lemma proof_of_two_way_short_needle_entail_wit_2_2 : two_way_short_needle_entail_wit_2_2.
Proof.
    pre_process.
    prop_apply (UCharArray.full_Zlength haystack_pre haystack_len_pre hay0_low_level_spec).
    prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
    Intros.
    (first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; auto; try lia] | cancel]).
    match goal with Hex : safeExec _ (generic_match_periodic_from _ _ _ _ _ _) _ |- _ => rename Hex into Hexec end.
    unfold generic_match_periodic_from in Hexec at 1.
    unfold_loop in Hexec.
    prog_nf in Hexec.
    unfold generic_match_periodic_loop_body in Hexec at 1.
    safe_choice_r Hexec.
    unfold match_periodic_loop_body in Hexec at 1.
    prog_nf in Hexec.
    safe_choice_l Hexec; try lia.
    unfold generic_match_periodic_from_right.
    rewrite Z.max_l in Hexec by lia.
    unfold generic_match_periodic_from.
    eapply safeExec_proequiv; [| exact Hexec].
    apply common_step_equiv.
    intros [[pos' memory'] | res]; reflexivity.
Qed. 

Lemma proof_of_two_way_short_needle_entail_wit_3 : two_way_short_needle_entail_wit_3.
Proof.
    pre_process.
    prop_apply (UCharArray.full_Zlength haystack_pre haystack_len_pre hay0_low_level_spec).
    prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
    Intros.
    rewrite sizeof_uchar.
    replace (needle_pre + i * 1 + 1 * 1) with (needle_pre + (i + 1) * 1) by lia.
    replace (haystack_pre + (i + j) * 1 + 1 * 1) with (haystack_pre + (i + 1 + j) * 1) by lia.
    (first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; auto; try lia] | cancel]).
    match goal with Hex : safeExec _ (generic_match_periodic_from_right _ _ _ _ _ _ _) _ |- _ => rename Hex into Hexec end.
    unfold generic_match_periodic_from_right in Hexec at 1.
    prog_nf in Hexec.
    unfold match_periodic_from_right in Hexec at 1.
    unfold match_right in Hexec at 1.
    unfold_loop in Hexec.
    prog_nf in Hexec.
    unfold match_right_f in Hexec at 1.
    prog_nf in Hexec.
    safe_choice_l Hexec; try lia.
    - unfold continue in Hexec.
      prog_nf in Hexec.
      unfold generic_match_periodic_from_right.
      unfold match_periodic_from_right.
      unfold match_right.
      prog_nf.
      exact Hexec.
    - split; [lia|].
      unfold match_cond.
      replace (j + i) with (i + j) by lia.
      exact H.
Qed. 

Lemma proof_of_two_way_short_needle_entail_wit_4 : two_way_short_needle_entail_wit_4.
Proof.
    pre_process.
    prop_apply (UCharArray.full_Zlength haystack_pre haystack_len_pre hay0_low_level_spec).
    prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
    Intros.
    (first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; auto; try lia] | cancel]).
    match goal with Hex : safeExec _ (generic_match_periodic_from_right _ _ _ _ _ _ _) _ |- _ => rename Hex into Hexec end.
    unfold generic_match_periodic_from_right in Hexec at 1.
    prog_nf in Hexec.
    unfold match_periodic_from_right in Hexec at 1.
    unfold match_right in Hexec at 1.
    unfold_loop in Hexec.
    prog_nf in Hexec.
    unfold match_right_f in Hexec at 1.
    prog_nf in Hexec.
    safe_choice_r Hexec; try lia.
    unfold break in Hexec.
    prog_nf in Hexec.
    unfold match_periodic_after_right in Hexec at 1.
    prog_nf in Hexec.
    safe_choice_l Hexec; try lia.
    unfold generic_match_periodic_from_left.
    exact Hexec.
Qed. 

Lemma proof_of_two_way_short_needle_entail_wit_5 : two_way_short_needle_entail_wit_5.
Proof.
    pre_process.
    prop_apply (UCharArray.full_Zlength haystack_pre haystack_len_pre hay0_low_level_spec).
    prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
    Intros.
    rewrite sizeof_uchar.
    replace (needle_pre + i * 1 - 1 * 1) with (needle_pre + (i - 1) * 1) by lia.
    replace (haystack_pre + (i + j) * 1 - 1 * 1) with (haystack_pre + (i - 1 + j) * 1) by lia.
    (first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; auto; try lia] | cancel]).
    match goal with Hex : safeExec _ (generic_match_periodic_from_left _ _ _ _ _ _ _) _ |- _ => rename Hex into Hexec end.
    unfold generic_match_periodic_from_left in Hexec at 1.
    prog_nf in Hexec.
    unfold match_periodic_from_left in Hexec at 1.
    unfold match_left in Hexec at 1.
    unfold_loop in Hexec.
    prog_nf in Hexec.
    unfold match_left_f in Hexec at 1.
    prog_nf in Hexec.
    safe_choice_l Hexec; try lia.
    - unfold continue in Hexec.
      prog_nf in Hexec.
      unfold generic_match_periodic_from_left.
      unfold match_periodic_from_left.
      unfold match_left.
      prog_nf.
      exact Hexec.
    - split; [lia|].
      unfold match_cond.
      replace (j + i) with (i + j) by lia.
      exact H.
Qed. 

Lemma proof_of_two_way_short_needle_entail_wit_6_1 : two_way_short_needle_entail_wit_6_1.
Proof.
    pre_process.
    prop_apply (UCharArray.full_Zlength haystack_pre haystack_len_pre hay0_low_level_spec).
    prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
    Intros.
    (first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; auto; try lia] | cancel]); try lia.
    - sep_apply (store_int_undef_store_int (&("i")) i).
      cancel.
    - match goal with Hex : safeExec _ (generic_match_periodic_from_right _ _ _ _ _ _ _) _ |- _ => rename Hex into Hexec end.
    unfold generic_match_periodic_from_right in Hexec at 1.
      prog_nf in Hexec.
      unfold match_periodic_from_right in Hexec at 1.
      unfold match_right in Hexec at 1.
      unfold_loop in Hexec.
      prog_nf in Hexec.
      unfold match_right_f in Hexec at 1.
      prog_nf in Hexec.
      safe_choice_r Hexec; [|right; unfold match_cond; intro Hcontra; apply H0; replace (j + i) with (i + j) in Hcontra by lia; exact Hcontra].
      unfold break in Hexec.
      prog_nf in Hexec.
      unfold match_periodic_after_right in Hexec at 1.
      prog_nf in Hexec.
      safe_choice_r Hexec; [|lia].
      unfold continue in Hexec.
      prog_nf in Hexec.
      replace (j + (i - suffix + 1)) with (j + i - suffix + 1) by lia.
      exact Hexec.
Qed. 

Lemma proof_of_two_way_short_needle_entail_wit_6_2 : two_way_short_needle_entail_wit_6_2.
Proof.
    pre_process.
    prop_apply (UCharArray.full_Zlength haystack_pre haystack_len_pre hay0_low_level_spec).
    prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
    Intros.
    (first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; auto; try lia] | cancel]); try lia.
    - sep_apply (store_int_undef_store_int (&("i")) i).
      cancel.
    - match goal with Hex : safeExec _ (generic_match_periodic_from_left _ _ _ _ _ _ _) _ |- _ => rename Hex into Hexec end.
    unfold generic_match_periodic_from_left in Hexec at 1.
      prog_nf in Hexec.
      unfold match_periodic_from_left in Hexec at 1.
      unfold match_left in Hexec at 1.
      unfold_loop in Hexec.
      prog_nf in Hexec.
      unfold match_left_f in Hexec at 1.
      prog_nf in Hexec.
      safe_choice_r Hexec; [|right; unfold match_cond; intro Hcontra; apply H0; replace (j + i) with (i + j) in Hcontra by lia; exact Hcontra].
      unfold break in Hexec.
      prog_nf in Hexec.
      unfold match_periodic_after_left in Hexec at 1.
      prog_nf in Hexec.
      safe_choice_r Hexec; [| lia].
      unfold continue in Hexec.
      prog_nf in Hexec.
      match goal with Hlen : Zlength needle0_low_level_spec = needle_len_pre |- _ => rewrite Hlen in Hexec end.
      exact Hexec.
Qed. 

Lemma proof_of_two_way_short_needle_entail_wit_7_1 : two_way_short_needle_entail_wit_7_1.
Proof.
    pre_process.
    prop_apply (UCharArray.full_Zlength haystack_pre haystack_len_pre hay0_low_level_spec).
    prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
    Intros.
    (first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; auto; try lia] | cancel]); try lia.
    match goal with Hex : safeExec _ (applyf (two_way_generic_after_factorization _ _) _) _ |- _ => rename Hex into Hexec end.
    unfold two_way_generic_after_factorization in Hexec.
    unfold applyf in Hexec. simpl in Hexec.
    unfold generic_match_phase in Hexec.
    unfold memcmp_result in H1.
    assert (Hnot_split : ~ repetitive_split needle0_low_level_spec retval mp).
    {
      intro Hsplit.
      unfold repetitive_split in Hsplit.
      apply H0.
      apply (proj2 H1).
      unfold memcmp_eq.
      replace (0 + retval) with retval by lia.
      replace (mp + retval) with (retval + mp) by lia.
      exact Hsplit.
    }
    safe_choice_r Hexec.
    replace (Z.max retval (Zlength needle0_low_level_spec - retval) + 1) with (retval + 1) in Hexec by lia.
    prog_nf in Hexec.
    exact Hexec.
Qed. 

Lemma proof_of_two_way_short_needle_entail_wit_7_2 : two_way_short_needle_entail_wit_7_2.
Proof.
    pre_process.
    prop_apply (UCharArray.full_Zlength haystack_pre haystack_len_pre hay0_low_level_spec).
    prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
    Intros.
    assert (Hretval_pos : 0 < retval).
    {
      destruct (Z.eq_dec retval 0) as [Hzero | Hnz_ret].
      - subst retval.
        exfalso.
        apply H0.
        unfold memcmp_result in H1.
        apply (proj2 H1).
        unfold memcmp_eq.
        repeat rewrite Zsublist_nil; try lia.
        reflexivity.
      - lia.
    }
    (first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; auto; try lia] | cancel]); try lia.
    match goal with Hex : safeExec _ (applyf (two_way_generic_after_factorization _ _) _) _ |- _ => rename Hex into Hexec end.
    unfold two_way_generic_after_factorization in Hexec.
    unfold applyf in Hexec. simpl in Hexec.
    unfold generic_match_phase in Hexec.
    unfold memcmp_result in H1.
    assert (Hnot_split : ~ repetitive_split needle0_low_level_spec retval mp).
    {
      intro Hsplit.
      unfold repetitive_split in Hsplit.
      apply H0.
      apply (proj2 H1).
      unfold memcmp_eq.
      replace (0 + retval) with retval by lia.
      replace (mp + retval) with (retval + mp) by lia.
      exact Hsplit.
    }
    safe_choice_r Hexec.
    replace (Z.max retval (Zlength needle0_low_level_spec - retval) + 1) with ((needle_len_pre - retval) + 1) in Hexec by lia.
    prog_nf in Hexec.
    exact Hexec.
Qed. 

Lemma proof_of_two_way_short_needle_entail_wit_8 : two_way_short_needle_entail_wit_8.
Proof.
    pre_process. (first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; auto; try lia] | cancel]).
    rewrite sizeof_uchar.
    replace (haystack_pre + (suffix + j) * 1 + 1 * 1)
        with (haystack_pre + (suffix + j + 1) * 1) by lia.
    (first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; auto; try lia] | cancel]).
Qed. 

Lemma proof_of_two_way_short_needle_entail_wit_9 : two_way_short_needle_entail_wit_9.
Proof.
    pre_process.
    prop_apply (UCharArray.full_Zlength haystack_pre haystack_len_pre hay0_low_level_spec).
    prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
    Intros.
    (first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; auto; try lia] | cancel]).
    - rewrite sizeof_uchar.
      replace (haystack_pre + (suffix + j + 1) * 1 + 1 * 1)
          with (haystack_pre + (suffix + (j + 1) + 1) * 1) by lia.
      (first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; auto; try lia] | cancel]).
    - match goal with Hex : safeExec _ (generic_match_from _ _ _ _ _) _ |- _ => rename Hex into Hexec end.
    unfold generic_match_from in Hexec at 1. (* MARK : *)
      unfold_loop in Hexec.
      prog_nf in Hexec.
      unfold generic_match_loop_body in Hexec at 1.
    safe_choice_r Hexec.
    unfold match_loop_body in Hexec at 1.
      prog_nf in Hexec.
      safe_choice_l Hexec; [|lia].
      unfold match_right in Hexec at 1.
      unfold_loop in Hexec.
      prog_nf in Hexec.
      unfold match_right_f in Hexec at 1.
      prog_nf in Hexec.
      safe_choice_r Hexec.
      + unfold break in Hexec.
        prog_nf in Hexec.
        safe_choice_r Hexec; [|lia].
        replace (j + suffix - suffix + 1) with (j + 1) in Hexec by lia. (* subtle, reasonable *)
        unfold continue in Hexec.
        prog_nf in Hexec.
        exact Hexec.
      + right.
        unfold match_cond.
        intro Hcontra.
        apply H0.
        match goal with Heq : phay_ch = Znth (suffix + j) hay0_low_level_spec 0 |- _ => rewrite Heq end.
        replace (suffix + j) with (j + suffix) by lia.
        exact Hcontra.
    - f_equal; lia.
Qed. 

Lemma proof_of_two_way_short_needle_entail_wit_10 : two_way_short_needle_entail_wit_10.
Proof.
    pre_process.
    prop_apply (UCharArray.full_Zlength haystack_pre haystack_len_pre hay0_low_level_spec).
    prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
    Intros. (first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; auto; try lia] | cancel]).
    match goal with Hex : safeExec _ (generic_match_from _ _ _ _ _) _ |- _ => rename Hex into Hexec end.
    unfold generic_match_from in Hexec.
    unfold_loop in Hexec.
    unfold generic_match_loop_body in Hexec at 1.
    safe_choice_r Hexec.
    unfold match_loop_body in Hexec at 1.
    safe_choice_l Hexec; [|lia]. prog_nf in Hexec.
    unfold match_right in Hexec at 1.
    unfold_loop in Hexec.
    prog_nf in Hexec.
    unfold match_right_f in Hexec at 1.
    prog_nf in Hexec.
    safe_choice_l Hexec; try lia.
    - unfold continue in Hexec.
      prog_nf in Hexec.
      eapply safeExec_proequiv; [| exact Hexec].
      unfold generic_match_from_right.
      unfold match_right.
      prog_nf.
      apply common_step_equiv.
      intro a.
      unfold generic_match_after_right.
      rewrite bind_choice_equiv.
      apply choice_case_equiv;
        [unfold generic_match_from_left, generic_match_after_left, generic_match_from
        | unfold generic_match_from].
      + prog_nf.
        apply common_step_equiv.
        intros _.
        rewrite bind_assoc.
        apply common_step_equiv.
        intro b.
        rewrite bind_choice_equiv.
        apply choice_case_equiv; unfold break, continue; prog_nf; reflexivity.
      + prog_nf; reflexivity.
    - split; [lia|].
      unfold match_cond.
      replace (j + suffix) with (suffix + j) by lia.
      rewrite <- H15.
      exact H.
Qed. 

Lemma proof_of_two_way_short_needle_entail_wit_11 : two_way_short_needle_entail_wit_11.
Proof.
    pre_process.
    prop_apply (UCharArray.full_Zlength haystack_pre haystack_len_pre hay0_low_level_spec).
    prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
    Intros.
    rewrite sizeof_uchar.
    replace (needle_pre + i * 1 + 1 * 1) with (needle_pre + (i + 1) * 1) by lia.
    replace (haystack_pre + (i + j) * 1 + 1 * 1) with (haystack_pre + (i + 1 + j) * 1) by lia.
    (first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; auto; try lia] | cancel]).
    match goal with Hex : safeExec _ (generic_match_from_right _ _ _ _ _ _) _ |- _ => rename Hex into Hexec end.
    unfold generic_match_from_right in Hexec at 1.
    prog_nf in Hexec.
    unfold match_right in Hexec at 1.
    unfold_loop in Hexec.
    prog_nf in Hexec.
    unfold match_right_f in Hexec at 1.
    prog_nf in Hexec.
    safe_choice_l Hexec; try lia.
    - unfold continue in Hexec.
      prog_nf in Hexec.
      unfold generic_match_from_right.
      unfold match_right.
      prog_nf.
      exact Hexec.
    - split; [lia|].
      unfold match_cond.
      replace (j + i) with (i + j) by lia.
      exact H.
Qed. 

Lemma proof_of_two_way_short_needle_entail_wit_12 : two_way_short_needle_entail_wit_12.
Proof.
    pre_process.
    prop_apply (UCharArray.full_Zlength haystack_pre haystack_len_pre hay0_low_level_spec).
    prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
    Intros.
    (first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; auto; try lia] | cancel]).
    match goal with Hex : safeExec _ (generic_match_from_right _ _ _ _ _ _) _ |- _ => rename Hex into Hexec end.
    unfold generic_match_from_right in Hexec at 1.
    prog_nf in Hexec.
    unfold match_right in Hexec at 1.
    unfold_loop in Hexec.
    prog_nf in Hexec.
    unfold match_right_f in Hexec at 1.
    prog_nf in Hexec.
    safe_choice_r Hexec; try lia.
    unfold break in Hexec.
    prog_nf in Hexec.
    unfold generic_match_after_right in Hexec at 1.
    prog_nf in Hexec.
    safe_choice_l Hexec; try lia.
    unfold generic_match_from_left.
    exact Hexec.
Qed. 

Lemma proof_of_two_way_short_needle_entail_wit_13 : two_way_short_needle_entail_wit_13.
Proof.
    pre_process.
    prop_apply (UCharArray.full_Zlength haystack_pre haystack_len_pre hay0_low_level_spec).
    prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
    Intros.
    rewrite sizeof_uchar.
    replace (needle_pre + i * 1 - 1 * 1) with (needle_pre + (i - 1) * 1) by lia.
    replace (haystack_pre + (i + j) * 1 - 1 * 1) with (haystack_pre + (i - 1 + j) * 1) by lia.
    (first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; auto; try lia] | cancel]).
    match goal with Hex : safeExec _ (generic_match_from_left _ _ _ _ _ _ _) _ |- _ => rename Hex into Hexec end.
    unfold generic_match_from_left in Hexec at 1.
    prog_nf in Hexec.
    unfold match_left in Hexec at 1.
    unfold_loop in Hexec.
    prog_nf in Hexec.
    unfold match_left_f in Hexec at 1.
    prog_nf in Hexec.
    safe_choice_l Hexec; try lia.
    - unfold continue in Hexec.
      prog_nf in Hexec.
      unfold generic_match_from_left.
      unfold match_left.
      prog_nf.
      exact Hexec.
    - split; [lia|].
      unfold match_cond.
      replace (j + i) with (i + j) by lia.
      exact H.
Qed. 

Lemma proof_of_two_way_short_needle_entail_wit_14_1 : two_way_short_needle_entail_wit_14_1.
Proof.
    pre_process.
    prop_apply (UCharArray.full_Zlength haystack_pre haystack_len_pre hay0_low_level_spec).
    prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
    Intros.
    (first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; auto; try lia] | cancel]); try lia.
    - sep_apply (store_int_undef_store_int (&("i")) i).
      sep_apply (store_ptr_undef_store_ptr (&("phaystack")) (haystack_pre + (i + j) * sizeof(UCHAR))).
      cancel.
    - match goal with Hex : safeExec _ (generic_match_from_right _ _ _ _ _ _) _ |- _ => rename Hex into Hexec end.
    unfold generic_match_from_right in Hexec at 1.
      prog_nf in Hexec.
      unfold match_right in Hexec at 1.
      unfold_loop in Hexec.
      prog_nf in Hexec.
      unfold match_right_f in Hexec at 1.
      prog_nf in Hexec.
      safe_choice_r Hexec; [|right; unfold match_cond; intro Hcontra; apply H0; replace (j + i) with (i + j) in Hcontra by lia; exact Hcontra].
      unfold break in Hexec.
      prog_nf in Hexec.
      unfold generic_match_after_right in Hexec at 1.
      prog_nf in Hexec.
      safe_choice_r Hexec; [|lia].
      replace (j + (i - suffix + 1)) with (j + i - suffix + 1) by lia.
      exact Hexec.
Qed. 

Lemma proof_of_two_way_short_needle_entail_wit_14_2 : two_way_short_needle_entail_wit_14_2.
Proof.
    pre_process.
    prop_apply (UCharArray.full_Zlength haystack_pre haystack_len_pre hay0_low_level_spec).
    prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
    Intros.
    (first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; auto; try lia] | cancel]); try lia.
    - sep_apply (store_int_undef_store_int (&("i")) i).
      sep_apply (store_ptr_undef_store_ptr (&("phaystack")) (haystack_pre + (i + j) * sizeof(UCHAR))).
      cancel.
    - match goal with Hex : safeExec _ (generic_match_from_left _ _ _ _ _ _ _) _ |- _ => rename Hex into Hexec end.
    unfold generic_match_from_left in Hexec at 1.
      prog_nf in Hexec.
      unfold match_left in Hexec at 1.
      unfold_loop in Hexec.
      prog_nf in Hexec.
      unfold match_left_f in Hexec at 1.
      prog_nf in Hexec.
      safe_choice_r Hexec; [|right; unfold match_cond; intro Hcontra; apply H0; replace (j + i) with (i + j) in Hcontra by lia; exact Hcontra].
      unfold break in Hexec.
      prog_nf in Hexec.
      unfold generic_match_after_left in Hexec at 1.
      prog_nf in Hexec.
      safe_choice_r Hexec; [| lia].
      exact Hexec.
Qed. 

Lemma proof_of_two_way_short_needle_return_wit_1 : two_way_short_needle_return_wit_1.
Proof.
    pre_process.
    prop_apply (UCharArray.full_Zlength haystack_pre haystack_len_pre hay0_low_level_spec).
    prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
    Intros.
    (first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; auto; try lia] | cancel]).
    match goal with Hex : safeExec _ (generic_match_periodic_from _ _ _ _ _ _) _ |- _ => rename Hex into Hexec end.
    unfold generic_match_periodic_from in Hexec at 1.
    unfold_loop in Hexec.
    prog_nf in Hexec.
    unfold generic_match_periodic_loop_body in Hexec at 1.
    safe_choice_r Hexec.
    unfold match_periodic_loop_body in Hexec at 1.
    prog_nf in Hexec.
    safe_choice_r Hexec; try lia.
    unfold break in Hexec.
    prog_nf in Hexec.
    unfold uchar_ptr_option_repr.
    unfold NULL.
    destruct (Z.eq_dec 0 0).
    - exact Hexec.
    - lia.
Qed. 

Lemma proof_of_two_way_short_needle_return_wit_2 : two_way_short_needle_return_wit_2.
Proof.
    pre_process.
    prop_apply (UCharArray.full_Zlength haystack_pre haystack_len_pre hay0_low_level_spec).
    prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
    Intros.
    (first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; auto; try lia] | cancel]).
    match goal with Hex : safeExec _ (generic_match_from _ _ _ _ _) _ |- _ => rename Hex into Hexec end.
    unfold generic_match_from in Hexec at 1.
    unfold_loop in Hexec.
    prog_nf in Hexec.
    unfold generic_match_loop_body in Hexec at 1.
    safe_choice_r Hexec.
    unfold match_loop_body in Hexec at 1.
    prog_nf in Hexec.
    safe_choice_r Hexec; try lia.
    unfold break in Hexec.
    prog_nf in Hexec.
    unfold uchar_ptr_option_repr.
    unfold NULL.
    destruct (Z.eq_dec 0 0); [exact Hexec|lia].
Qed. 

Lemma proof_of_two_way_short_needle_return_wit_3 : two_way_short_needle_return_wit_3.
Proof.
    pre_process.
    prop_apply (UCharArray.full_Zlength haystack_pre haystack_len_pre hay0_low_level_spec).
    prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
    Intros. (first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; auto; try lia] | cancel]).
    match goal with Hex : safeExec _ (generic_match_from_left _ _ _ _ _ _ _) _ |- _ => rename Hex into Hexec end.
    unfold generic_match_from_left in Hexec.
    subst i.
    unfold match_left in Hexec.
    unfold_loop in Hexec. prog_nf in Hexec.
    unfold match_left_f in Hexec.
    safe_choice_r Hexec; [|left; lia].
    unfold generic_match_after_left in Hexec.
    unfold break in Hexec. prog_nf in Hexec.
    safe_choice_l Hexec; [| lia].
    unfold uchar_ptr_option_repr.
    unfold NULL.
    rewrite sizeof_uchar.
    destruct (Z.eq_dec (haystack_pre + j * 1) 0) as [Hnull | Hnonnull].
    - lia.
    - replace (haystack_pre + j * 1 - haystack_pre) with j by lia.
      rewrite Z.div_1_r.
      exact Hexec.
Qed. 

Lemma proof_of_two_way_short_needle_return_wit_4 : two_way_short_needle_return_wit_4.
Proof.
    pre_process.
    prop_apply (UCharArray.full_Zlength haystack_pre haystack_len_pre hay0_low_level_spec).
    prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
    Intros.
    (first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; auto; try lia] | cancel]).
    match goal with Hex : safeExec _ (generic_match_from _ _ _ _ _) _ |- _ => rename Hex into Hexec end.
    unfold generic_match_from in Hexec at 1.
    unfold_loop in Hexec.
    prog_nf in Hexec.
    unfold generic_match_loop_body in Hexec at 1.
    safe_choice_r Hexec.
    unfold match_loop_body in Hexec at 1.
    prog_nf in Hexec.
    safe_choice_l Hexec; try lia.
    unfold match_right in Hexec at 1.
    unfold_loop in Hexec.
    prog_nf in Hexec.
    unfold match_right_f in Hexec at 1.
    prog_nf in Hexec.
    safe_choice_r Hexec.
    - unfold break in Hexec.
      prog_nf in Hexec.
      safe_choice_r Hexec; [|lia].
      unfold continue in Hexec.
      prog_nf in Hexec.
      replace (j + suffix - suffix + 1) with (j + 1) in Hexec by lia.
      unfold_loop in Hexec.
      prog_nf in Hexec.
      unfold generic_match_loop_body in Hexec at 1.
    safe_choice_r Hexec.
    unfold match_loop_body in Hexec at 1.
      prog_nf in Hexec.
      safe_choice_r Hexec; try lia.
      unfold break in Hexec.
      prog_nf in Hexec.
      unfold uchar_ptr_option_repr.
      unfold NULL.
      destruct (Z.eq_dec 0 0); [exact Hexec|lia].
    - right.
      unfold match_cond.
      intro Hcontra.
      apply H0.
      rewrite H16.
      replace (suffix + j) with (j + suffix) by lia.
      exact Hcontra.
Qed. 

Lemma proof_of_two_way_short_needle_return_wit_5 : two_way_short_needle_return_wit_5.
Proof.
    pre_process.
    prop_apply (UCharArray.full_Zlength haystack_pre haystack_len_pre hay0_low_level_spec).
    prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
    Intros. (first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; auto; try lia] | cancel]).
    match goal with Hex : safeExec _ (generic_match_periodic_from_left _ _ _ _ _ _ _) _ |- _ => rename Hex into Hexec end.
    unfold generic_match_periodic_from_left in Hexec.
    prog_nf in Hexec.
    unfold match_periodic_from_left in Hexec.
    unfold match_left in Hexec.
    unfold_loop in Hexec.
    prog_nf in Hexec.
    unfold match_left_f in Hexec.
    prog_nf in Hexec.
    safe_choice_r Hexec; [|left; lia].
    unfold break in Hexec.
    prog_nf in Hexec.
    unfold match_periodic_after_left in Hexec.
    prog_nf in Hexec.
    safe_choice_l Hexec; [|lia].
    unfold break in Hexec.
    prog_nf in Hexec.
    unfold uchar_ptr_option_repr.
    unfold NULL.
    rewrite sizeof_uchar.
    destruct (Z.eq_dec (haystack_pre + j * 1) 0) as [Hnull | Hnonnull].
    - lia.
    - replace (haystack_pre + j * 1 - haystack_pre) with j by lia.
      rewrite Z.div_1_r.
      exact Hexec.
Qed. 

Lemma proof_of_two_way_short_needle_partial_solve_wit_1_pure : two_way_short_needle_partial_solve_wit_1_pure.
Proof.
 pre_process.
Qed. 

Lemma proof_of_two_way_long_needle_safety_wit_20 : two_way_long_needle_safety_wit_20.
Proof.
  pre_process.
  prop_apply (UCharArray.full_Zlength haystack_pre haystack_len_pre hay0_low_level_spec).
  Intros.
  try split_pure_spatial; try cancel; try split_pures; try dump_pre_spatial; try assumption; try reflexivity; try lia.
  unfold valid_skip in H3.
  lia.
Qed.

Lemma proof_of_two_way_long_needle_safety_wit_64 : two_way_long_needle_safety_wit_64.
Proof.
  pre_process.
  assert (0 < suffix).
  {
    destruct (Z_lt_le_dec 0 suffix) as [Hsuf | Hsuf]; [exact Hsuf|].
    assert (suffix = 0) by lia.
    subst suffix.
    exfalso.
    apply H0.
    unfold memcmp_result, memcmp_eq in H1.
    apply H1.
    repeat rewrite Zsublist_nil; try lia.
    reflexivity.
  }
  try split_pure_spatial; try cancel; try split_pures; try dump_pre_spatial; try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_two_way_long_needle_safety_wit_74 : two_way_long_needle_safety_wit_74.
Proof.
  pre_process.
  prop_apply (UCharArray.full_Zlength haystack_pre haystack_len_pre hay0_low_level_spec).
  Intros.
  split_pures; dump_pre_spatial; unfold valid_skip in H0; lia.
Qed.

Lemma proof_of_two_way_long_needle_entail_wit_1 : two_way_long_needle_entail_wit_1.
Proof.
  pre_process.
  sep_apply_l_atomic (IntArray.undef_full_to_undef_seg (&("shift_table")) 256).
  try split_pure_spatial; try cancel; try split_pures; try dump_pre_spatial; try assumption; try reflexivity; try lia.
  rewrite IntArray.seg_empty.
  try split_pure_spatial; try cancel; try split_pures; try dump_pre_spatial; try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_two_way_long_needle_entail_wit_2 : two_way_long_needle_entail_wit_2.
Proof.
  pre_process.
  change (Z.shiftl 1 8) with 256 in *.
  rewrite repeat_Z_tail; try lia.
  try split_pure_spatial; try cancel; try split_pures; try dump_pre_spatial; try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_two_way_long_needle_entail_wit_3 : two_way_long_needle_entail_wit_3.
Proof.
  pre_process.
  change (Z.shiftl 1 8) with 256 in H.
  assert (i = 256) by lia.
  subst i.
  Exists (repeat_Z needle_len_pre 256).
  sep_apply (store_int_undef_store_int (&("i")) 256).
  rewrite IntArray.undef_seg_empty.
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
  Intros.
  split_pure_spatial.
  - unfold IntArray.full, IntArray.seg, store_array; cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
  unfold shift_table_build_prefix.
  repeat split; try lia; try apply Zlength_nonneg;
    try (unfold repeat_Z; rewrite Zlength_correct, repeat_length; lia).
  intros c Hc.
  right; split;
    [ intros idx Hidx; lia
    | unfold repeat_Z;
      rewrite Znth_repeat_lt; try lia;
      match goal with
      | Hlen : Zlength needle0_low_level_spec = needle_len_pre |- _ =>
          rewrite Hlen
      end;
      reflexivity ].
Qed.

Lemma proof_of_two_way_long_needle_entail_wit_4 : two_way_long_needle_entail_wit_4.
Proof.
  pre_process.
  prop_apply (UCharArray_full_Znth_range needle_pre needle_len_pre needle0_low_level_spec 0 ltac:(lia)).
  Intros.
  Exists table_2.
  try split_pure_spatial; try cancel; try split_pures; try dump_pre_spatial; try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_two_way_long_needle_entail_wit_5 : two_way_long_needle_entail_wit_5.
Proof.
  pre_process.
  Exists table_2.
  sep_apply_l_atomic (UCharArray.full_split_to_missing_i needle_pre i needle_len_pre needle0_low_level_spec 0 ltac:(lia)).
  try split_pure_spatial; try cancel; try split_pures; try dump_pre_spatial; try assumption; try reflexivity; try lia.
Qed.

Lemma proof_of_two_way_long_needle_entail_wit_6 : two_way_long_needle_entail_wit_6.
Proof.
  pre_process.
  Exists (replace_Znth (Znth i needle0_low_level_spec 0) (needle_len_pre - i - 1) table_2).
  rewrite replace_Znth_Znth by tauto.
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
  Intros.
  prop_apply (UCharArray_full_Znth_range_le needle_pre needle_len_pre needle0_low_level_spec (i + 1) ltac:(lia)).
  Intros.
  try split_pure_spatial; try cancel; try split_pures; try dump_pre_spatial; try assumption; try reflexivity; try lia.
  replace (needle_len_pre - i - 1) with (Zlength needle0_low_level_spec - i - 1) by lia.
  apply shift_table_build_prefix_step; try lia; assumption.
Qed. 

Lemma proof_of_two_way_long_needle_entail_wit_7 : two_way_long_needle_entail_wit_7.
Proof.
  pre_process.
  assert (i = needle_len_pre) by lia.
  subst i.
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
  Intros.
  prop_apply
    (UCharArray_full_all_Znth_range
       haystack_pre haystack_len_pre hay0_low_level_spec).
  Intros.
  assert (Hhay_range :
    forall q, 0 <= q < Zlength hay0_low_level_spec ->
      0 <= Znth q hay0_low_level_spec 0 < 256) by assumption.
  Exists table_2.
  sep_apply (store_int_undef_store_int (&("i")) needle_len_pre).
  try split_pure_spatial; try cancel; try split_pures; try dump_pre_spatial; try assumption; try reflexivity; try lia.
  eapply shift_table_build_prefix_sound.
  - lia.
  - exact Hhay_range.
  - replace (Zlength needle0_low_level_spec) with needle_len_pre by lia.
    exact H2.
Qed. 

Lemma proof_of_two_way_long_needle_entail_wit_8 : two_way_long_needle_entail_wit_8.
Proof.
  pre_process.
  Exists table_2.
  split_pure_spatial; [cancel |].
  assert (Hrep : repetitive_split needle0_low_level_spec suffix mp).
  { unfold repetitive_split, memcmp_result, memcmp_eq in *.
    pose proof (proj1 H0 H) as Htmp.
    rewrite Z.add_0_l in Htmp.
    replace (suffix + mp) with (mp + suffix) by lia.
    exact Htmp. }
  split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
  - match goal with Hsafe : safeExec _ _ _ |- _ =>
      unfold applyf, maketuple, two_way_generic_after_factorization, generic_match_phase in Hsafe;
      prog_nf in Hsafe; safe_choice_l Hsafe; exact Hsafe end.
  - unfold periodic_memory_match.
    split; [exact (proj1 (H4 Hrep)) | split; [left; reflexivity | reflexivity]].
Qed. 

Lemma proof_of_two_way_long_needle_entail_wit_9 : two_way_long_needle_entail_wit_9.
Proof.
  pre_process.
  prop_apply (UCharArray_full_Znth_range haystack_pre haystack_len_pre hay0_low_level_spec (j + needle_len_pre - 1) ltac:(lia)).
  Intros.
  Exists table_2.
  sep_apply_l_atomic (UCharArray.full_split_to_missing_i haystack_pre (j + needle_len_pre - 1) haystack_len_pre hay0_low_level_spec 0 ltac:(lia)).
  try split_pure_spatial; try cancel; try split_pures; try dump_pre_spatial; try assumption; try reflexivity; try lia.
Qed. 

Lemma proof_of_two_way_long_needle_entail_wit_10_1 : two_way_long_needle_entail_wit_10_1.
Proof.
  pre_process.
  rewrite replace_Znth_Znth by lia.
  prop_apply (UCharArray.full_Zlength haystack_pre haystack_len_pre hay0_low_level_spec).
  Intros.
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
  Intros.
  assert (Hskip : valid_skip hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - mp)).
  {
    replace (needle_len_pre - mp) with (Zlength needle0_low_level_spec - mp) by lia.
    eapply (long_needle_periodic_memory_skip_valid
              hay0_low_level_spec needle0_low_level_spec j 0 mp memory table_2);
      try eassumption; try lia.
    - unfold repetitive_split.
      rewrite !Zsublist_nil by lia.
      reflexivity.
    - match goal with Hlen : Zlength needle0_low_level_spec = needle_len_pre |- _ => rewrite Hlen; lia end.
  }
  Exists table_2.
  try split_pure_spatial; try cancel; try split_pures; try dump_pre_spatial; try assumption; try reflexivity; try lia.
  unfold valid_skip in Hskip.
  lia.
Qed. 

Lemma proof_of_two_way_long_needle_entail_wit_10_2 : two_way_long_needle_entail_wit_10_2.
Proof.
  pre_process.
  rewrite replace_Znth_Znth by lia.
  prop_apply (UCharArray.full_Zlength haystack_pre haystack_len_pre hay0_low_level_spec).
  Intros.
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
  Intros.
  Exists table.
  try split_pure_spatial; try cancel; try split_pures; try dump_pre_spatial; try assumption; try reflexivity; try lia.
  match goal with Htable : shift_table_sound _ _ _ |- _ => destruct Htable as [_ Hsound] end.
  specialize (Hsound j (Znth (Znth (j + needle_len_pre - 1) hay0_low_level_spec 0) table 0)).
  specialize (Hsound ltac:(split; try lia)).
  specialize (Hsound ltac:(replace (Zlength needle0_low_level_spec) with needle_len_pre by lia; reflexivity)).
  destruct Hsound as [[Hz _] | Hskip].
  - lia.
  - exact Hskip.
Qed. 

Lemma proof_of_two_way_long_needle_entail_wit_10_3 : two_way_long_needle_entail_wit_10_3.
Proof.
  pre_process.
  rewrite replace_Znth_Znth by lia.
  prop_apply (UCharArray.full_Zlength haystack_pre haystack_len_pre hay0_low_level_spec).
  Intros.
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
  Intros.
  Exists table.
  try split_pure_spatial; try cancel; try split_pures; try dump_pre_spatial; try assumption; try reflexivity; try lia.
  match goal with Htable : shift_table_sound _ _ _ |- _ => destruct Htable as [_ Hsound] end.
  specialize (Hsound j (Znth (Znth (j + needle_len_pre - 1) hay0_low_level_spec 0) table 0)).
  specialize (Hsound ltac:(split; try lia)).
  specialize (Hsound ltac:(replace (Zlength needle0_low_level_spec) with needle_len_pre by lia; reflexivity)).
  destruct Hsound as [[Hz _] | Hskip].
  - exfalso; lia.
  - exact Hskip.
Qed. 

Lemma proof_of_two_way_long_needle_entail_wit_11 : two_way_long_needle_entail_wit_11.
Proof.
  pre_process.
  rewrite replace_Znth_Znth by lia.
  prop_apply (UCharArray.full_Zlength haystack_pre haystack_len_pre hay0_low_level_spec).
  Intros.
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
  Intros.
  assert (Hhay_len : Zlength hay0_low_level_spec = haystack_len_pre).
  {
    match goal with
    | Hlen : Zlength hay0_low_level_spec = haystack_len_pre |- _ => exact Hlen
    end.
  }
  assert (Hneedle_len : Zlength needle0_low_level_spec = needle_len_pre).
  {
    match goal with
    | Hlen : Zlength needle0_low_level_spec = needle_len_pre |- _ => exact Hlen
    end.
  }
  match goal with
  | Htable : shift_table_sound hay0_low_level_spec needle0_low_level_spec ?tbl |- _ =>
      assert (Hshift_match :
        Znth (Znth (j + needle_len_pre - 1) hay0_low_level_spec 0) tbl 0 = 0 /\
        match_cond hay0_low_level_spec needle0_low_level_spec j (needle_len_pre - 1));
      [ destruct Htable as [_ Hsound];
        specialize (Hsound j (Znth (Znth (j + needle_len_pre - 1) hay0_low_level_spec 0) tbl 0));
        specialize (Hsound ltac:(rewrite Hneedle_len, Hhay_len; split; try lia));
        specialize (Hsound ltac:(rewrite Hneedle_len; reflexivity));
        destruct Hsound as [Hzm | Hskip];
        [ destruct Hzm as [Hz Hmatch];
          split; [exact Hz |];
          rewrite Hneedle_len in Hmatch;
          exact Hmatch
        | unfold valid_skip in Hskip;
          lia ]
      | Exists tbl ]
  end.
  try split_pure_spatial; try cancel; try split_pures; try dump_pre_spatial; try assumption; try reflexivity; try lia.
  exact (proj2 Hshift_match).
Qed. 

Lemma proof_of_two_way_long_needle_entail_wit_12_1 : two_way_long_needle_entail_wit_12_1.
Proof.
  pre_process.
  prop_apply (UCharArray.full_Zlength haystack_pre haystack_len_pre hay0_low_level_spec); Intros.
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec); Intros.
  Exists table_2.
  split_pure_spatial.
  - sep_apply (store_int_undef_store_int (&("shift"))); cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
    + match goal with HH : safeExec _ _ _ |- _ => rename HH into Hsafe end.
        unfold generic_match_periodic_from in Hsafe at 1;
        unfold_loop in Hsafe; prog_nf in Hsafe;
        unfold generic_match_periodic_loop_body in Hsafe at 1; prog_nf in Hsafe;
        safe_choice_r Hsafe;
        unfold match_periodic_loop_body in Hsafe at 1; prog_nf in Hsafe;
        safe_choice_l Hsafe;
        try (match goal with Hn : Zlength needle0_low_level_spec = needle_len_pre,
                             Hh : Zlength hay0_low_level_spec = haystack_len_pre |- _ => rewrite Hn, Hh; lia end);
        replace (Z.max suffix memory) with memory in Hsafe by lia;
        unfold generic_match_periodic_from_right, generic_match_periodic_from;
        prog_nf; eapply safeExec_proequiv; [| exact Hsafe];
        apply common_step_equiv; intros [[pos2 mem2] | res]; simpl; reflexivity
      .
    + unfold matched_range, match_cond; intros k Hk.
      match goal with Hmem : periodic_memory_match _ _ _ _ _ |- _ =>
        destruct Hmem as [_ [_ Hmem]];
        apply (f_equal (fun xs => Znth k xs 0)) in Hmem;
        rewrite Znth_sublist0 in Hmem by lia;
        rewrite Znth_sublist in Hmem by lia;
        replace (k + j) with (j + k) in Hmem by lia; exact Hmem
      end.
Qed. 

Lemma proof_of_two_way_long_needle_entail_wit_12_2 : two_way_long_needle_entail_wit_12_2.
Proof.
  pre_process.
  prop_apply (UCharArray.full_Zlength haystack_pre haystack_len_pre hay0_low_level_spec); Intros.
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec); Intros.
  Exists table_2.
  split_pure_spatial.
  - sep_apply (store_int_undef_store_int (&("shift"))); cancel.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
    + match goal with HH : safeExec _ _ _ |- _ => rename HH into Hsafe end.
        unfold generic_match_periodic_from in Hsafe at 1;
        unfold_loop in Hsafe; prog_nf in Hsafe;
        unfold generic_match_periodic_loop_body in Hsafe at 1; prog_nf in Hsafe;
        safe_choice_r Hsafe;
        unfold match_periodic_loop_body in Hsafe at 1; prog_nf in Hsafe;
        safe_choice_l Hsafe;
        try (match goal with Hn : Zlength needle0_low_level_spec = needle_len_pre,
                             Hh : Zlength hay0_low_level_spec = haystack_len_pre |- _ => rewrite Hn, Hh; lia end);
        replace (Z.max suffix memory) with suffix in Hsafe by lia;
        unfold generic_match_periodic_from_right, generic_match_periodic_from;
        prog_nf; eapply safeExec_proequiv; [| exact Hsafe];
        apply common_step_equiv; intros [[pos2 mem2] | res]; simpl; reflexivity
      .
    + unfold matched_range; intros k Hk; lia.
Qed. 

Lemma proof_of_two_way_long_needle_entail_wit_13 : two_way_long_needle_entail_wit_13.
Proof.
  pre_process.
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec); Intros.
  Exists table_2.
  split_pure_spatial.
  - replace (needle_pre + (i + 1) * sizeof(UCHAR))
      with (needle_pre + i * sizeof(UCHAR) + 1 * sizeof(UCHAR)) by (rewrite sizeof_uchar; lia).
    replace (haystack_pre + (i + 1 + j) * sizeof(UCHAR))
      with (haystack_pre + (i + j) * sizeof(UCHAR) + 1 * sizeof(UCHAR)) by (rewrite sizeof_uchar; lia).
    cancel; try reflexivity.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
    + match goal with HH : safeExec _ _ _ |- _ => rename HH into Hsafe end.
        unfold generic_match_periodic_from_right, match_periodic_from_right in Hsafe;
        prog_nf in Hsafe; unfold match_right in Hsafe at 1;
        unfold_loop in Hsafe; prog_nf in Hsafe;
        unfold match_right_f in Hsafe at 1; prog_nf in Hsafe;
        safe_choice_l Hsafe;
        [ unfold continue in Hsafe; prog_nf in Hsafe;
          unfold generic_match_periodic_from_right, match_periodic_from_right, match_right;
          prog_nf; exact Hsafe
        | split; [match goal with Hn : Zlength needle0_low_level_spec = needle_len_pre |- _ => rewrite Hn; lia end | unfold match_cond; replace (j+i) with (i+j) by lia; assumption] ]
      .
    + unfold matched_range in *; intros k Hk.
      destruct (Z.eq_dec k i) as [Heq | Hneq].
      * subst k; unfold match_cond; replace (j+i) with (i+j) by lia; assumption.
      * match goal with Hr : forall k : Z, _ -> match_cond _ _ _ k |- _ => apply Hr; lia end.
Qed. 

Lemma proof_of_two_way_long_needle_entail_wit_14 : two_way_long_needle_entail_wit_14.
Proof.
  pre_process.
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec); Intros.
  assert (Hlen : Zlength needle0_low_level_spec = needle_len_pre) by assumption.
  assert (i = needle_len_pre - 1) by lia; subst i.
  Exists table_2.
  split_pure_spatial; [cancel |].
  split_pures; dump_pre_spatial; try assumption; try lia.
  - match goal with HH : safeExec _ _ _ |- _ => rename HH into Hsafe end.
    unfold generic_match_periodic_from_right, match_periodic_from_right in Hsafe;
    prog_nf in Hsafe; unfold match_right in Hsafe at 1;
    unfold_loop in Hsafe; prog_nf in Hsafe;
    unfold match_right_f in Hsafe at 1; prog_nf in Hsafe;
    safe_choice_l Hsafe.
    2: { split; [lia | assumption]. }
    unfold continue in Hsafe; prog_nf in Hsafe.
    replace (needle_len_pre - 1 + 1) with needle_len_pre in Hsafe by lia.
    unfold_loop in Hsafe; prog_nf in Hsafe;
    unfold match_right_f in Hsafe at 1; prog_nf in Hsafe;
    safe_choice_r Hsafe.
    2: { left; lia. }
    unfold break in Hsafe; prog_nf in Hsafe;
    unfold match_periodic_after_right in Hsafe at 1; prog_nf in Hsafe;
    safe_choice_l Hsafe; try (rewrite Hlen; reflexivity).
    unfold generic_match_periodic_from_left; exact Hsafe.
  - unfold matched_range in *; intros k Hk.
    destruct (Z.eq_dec k (needle_len_pre-1)).
    + subst k; assumption.
    + match goal with Hr : forall k : Z, _ -> match_cond _ _ _ k |- _ => apply Hr; lia end.
Qed. 

Lemma proof_of_two_way_long_needle_entail_wit_15 : two_way_long_needle_entail_wit_15.
Proof.
  pre_process.
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec); Intros.
  Exists table_2.
  split_pure_spatial.
  - replace (needle_pre + i * sizeof(UCHAR) - 1 * sizeof(UCHAR))
      with (needle_pre + (i - 1) * sizeof(UCHAR)) by (rewrite sizeof_uchar; lia).
    replace (haystack_pre + (i + j) * sizeof(UCHAR) - 1 * sizeof(UCHAR))
      with (haystack_pre + (i - 1 + j) * sizeof(UCHAR)) by (rewrite sizeof_uchar; lia).
    cancel; try reflexivity.
  - split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia.
    + match goal with HH : safeExec _ _ _ |- _ => rename HH into Hsafe end.
        unfold generic_match_periodic_from_left, match_periodic_from_left in Hsafe;
        prog_nf in Hsafe; unfold match_left in Hsafe at 1;
        unfold_loop in Hsafe; prog_nf in Hsafe;
        unfold match_left_f in Hsafe at 1; prog_nf in Hsafe;
        safe_choice_l Hsafe;
        [ unfold continue in Hsafe; prog_nf in Hsafe;
          unfold generic_match_periodic_from_left, match_periodic_from_left, match_left;
          prog_nf; exact Hsafe
        | split; [lia | unfold match_cond; replace (j+i) with (i+j) by lia; assumption] ]
      .
    + unfold matched_range in *; intros k Hk.
      destruct (Z.eq_dec k i) as [Heq | Hneq].
      * subst k; unfold match_cond; replace (j+i) with (i+j) by lia; assumption.
      * match goal with Hr : forall k : Z, _ -> match_cond _ _ _ k |- _ => apply Hr; lia end.
Qed. 

Lemma proof_of_two_way_long_needle_entail_wit_16 : two_way_long_needle_entail_wit_16.
Proof.
  pre_process.
  Exists table_2.
  sep_apply (store_ptr_undef_store_ptr (&("pneedle"))
    (needle_pre + i * sizeof(UCHAR))).
  sep_apply (store_ptr_undef_store_ptr (&("phaystack"))
    (haystack_pre + (i + j) * sizeof(UCHAR))).
  sep_apply (IntArray.full_to_undef_full (&("shift_table")) 256 table_2).
  try split_pure_spatial; try cancel; try split_pures; try dump_pre_spatial; try assumption; try reflexivity; try lia.
Qed. 

Lemma proof_of_two_way_long_needle_entail_wit_17_1 : two_way_long_needle_entail_wit_17_1.
Proof.
  pre_process.
  prop_apply (UCharArray.full_Zlength haystack_pre haystack_len_pre hay0_low_level_spec).
  Intros.
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
  Intros.
  assert (Hskip_bound_len : j + shift <= haystack_len_pre).
  {
    pose proof H3 as Hskip.
    unfold valid_skip in Hskip.
    destruct Hskip as [_ [Hbound _]].
    rewrite H17 in Hbound.
    exact Hbound.
  }
  assert (Hloop_bound_len :
    j + Zlength needle0_low_level_spec <= Zlength hay0_low_level_spec).
  {
    rewrite H17, H18.
    lia.
  }
  Exists table_2.
  sep_apply (store_int_undef_store_int (&("shift"))).
  first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia; revgoals] | cancel].
  - unfold periodic_memory_match.
    split; [exact (proj1 (H0 H1)) |].
    split; [left; reflexivity |].
    rewrite !Zsublist_nil by lia.
    reflexivity.
  - match goal with Hs : safeExec _ _ _ |- _ => rename Hs into Hexec end.
  unfold generic_match_periodic_from in Hexec. prog_nf in Hexec.
    unfold_loop in Hexec. prog_nf in Hexec.
    unfold generic_match_periodic_loop_body in Hexec at 1.
    prog_nf in Hexec.
    safe_choice_l Hexec.
    + prog_nf in Hexec. eapply (@safeExec_any_bind _ _ Z _ _ _ shift) in Hexec.
        safe_step Hexec.
        unfold continue in Hexec.
        prog_nf in Hexec.
        unfold generic_match_periodic_from.
        exact Hexec.
Qed. 

Lemma proof_of_two_way_long_needle_entail_wit_17_2 : two_way_long_needle_entail_wit_17_2.
Proof.
  pre_process.
  prop_apply (UCharArray.full_Zlength haystack_pre haystack_len_pre hay0_low_level_spec).
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
  Intros.
  Exists table_2.
  sep_apply (store_int_undef_store_int (&("i")) i).
  first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia; revgoals] | cancel].
  - unfold periodic_memory_match.
    split; [exact (proj1 (H3 H4)) |].
    split; [left; reflexivity |].
    rewrite !Zsublist_nil by lia.
    reflexivity.
  - match goal with Hs : safeExec _ _ _ |- _ => rename Hs into Hexec end.
  unfold generic_match_periodic_from_right in Hexec. prog_nf in Hexec.
    unfold match_periodic_from_right in Hexec. prog_nf in Hexec.
    unfold match_right in Hexec. prog_nf in Hexec.
    unfold_loop in Hexec. prog_nf in Hexec.
    unfold match_right_f in Hexec at 1.
    prog_nf in Hexec.
    safe_choice_r Hexec.
    + prog_nf in Hexec.
      unfold break in Hexec.
      prog_nf in Hexec.
      unfold match_periodic_after_right in Hexec. prog_nf in Hexec.
      safe_choice_r Hexec; try lia.
      unfold continue in Hexec.
      prog_nf in Hexec.
      replace (j + (i - suffix + 1)) with (j + i - suffix + 1) by lia.
      exact Hexec.
    + right. unfold match_cond.
      replace (j + i) with (i + j) by lia.
      exact H0.
Qed. 

Lemma proof_of_two_way_long_needle_entail_wit_17_3 : two_way_long_needle_entail_wit_17_3.
Proof.
  pre_process.
  prop_apply (UCharArray.full_Zlength haystack_pre haystack_len_pre hay0_low_level_spec).
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
  Intros.
  Exists table_2.
  sep_apply (store_int_undef_store_int (&("i")) i).
  first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia; revgoals] | cancel].
  {
    unfold periodic_memory_match.
    split.
    - exact (proj1 (H3 H4)).
    - split.
      + right. lia.
      + apply (proj2 (list_eq_ext _ _ 0)).
        split.
        * rewrite !Zlength_sublist by (split; lia). lia.
        * intros q Hq.
          assert (Hqlen : q < needle_len_pre - mp).
          { rewrite Zlength_sublist in Hq by (split; lia). lia. }
          rewrite Znth_sublist0 by lia.
          rewrite Znth_sublist by lia.
          pose proof (proj1 (H3 H4)) as Hperiod.
          destruct Hperiod as [_ Hperiod].
          rewrite (Hperiod q ltac:(lia) ltac:(lia)).
          unfold matched_range, match_cond in H6.
          pose proof (proj2 (H3 H4)) as Hcut.
          specialize (H6 (q + mp) ltac:(lia)).
          replace (q + (j + mp)) with (j + (q + mp)) by lia.
          exact H6.
  }
  match goal with Hs : safeExec _ _ _ |- _ => rename Hs into Hexec end.
  unfold generic_match_periodic_from_left in Hexec. prog_nf in Hexec.
  unfold match_periodic_from_left in Hexec. prog_nf in Hexec.
  unfold match_left in Hexec. prog_nf in Hexec.
  unfold_loop in Hexec. prog_nf in Hexec.
  unfold match_left_f in Hexec at 1.
  prog_nf in Hexec.
  safe_choice_r Hexec.
  - prog_nf in Hexec.
    unfold match_periodic_after_left in Hexec. prog_nf in Hexec.
    unfold break in Hexec. prog_nf in Hexec.
    safe_choice_r Hexec; try lia.
    unfold continue in Hexec.
    prog_nf in Hexec.
    replace ((Zlength needle0_low_level_spec - mp)) with ((needle_len_pre - mp)) in Hexec by lia.
    exact Hexec.
  - right. unfold match_cond.
    replace (j + i) with (i + j) by lia.
    exact H0.
Qed. 

Lemma proof_of_two_way_long_needle_entail_wit_18_1 : two_way_long_needle_entail_wit_18_1.
Proof.
  pre_process.
  prop_apply (UCharArray.full_Zlength haystack_pre haystack_len_pre hay0_low_level_spec).
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
  Intros.
  assert (Hneedle_len : Zlength needle0_low_level_spec = needle_len_pre).
  {
    match goal with
    | Hlen : Zlength needle0_low_level_spec = needle_len_pre |- _ => exact Hlen
    end.
  }
  Exists table_2.
  first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia; revgoals] | cancel].
  match goal with Hs : safeExec _ _ _ |- _ => rename Hs into Hexec end.
  unfold applyf, maketuple in Hexec. prog_nf in Hexec.
  simpl in Hexec.
  unfold generic_match_phase in Hexec.
  prog_nf in Hexec.
  safe_choice_r Hexec.
  - replace (Z.max suffix (Zlength needle0_low_level_spec - suffix) + 1)
      with (suffix + 1) in Hexec by (rewrite Hneedle_len; lia).
    exact Hexec.
  - unfold repetitive_split, memcmp_result, memcmp_eq in *.
    intro Hr.
    apply H0.
    apply H1.
    replace (0 + suffix) with suffix by lia.
    replace (mp + suffix) with (suffix + mp) by lia.
    exact Hr.
Qed. 

Lemma proof_of_two_way_long_needle_entail_wit_18_2 : two_way_long_needle_entail_wit_18_2.
Proof.
  pre_process.
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
  Intros.
  assert (Hneedle_len : Zlength needle0_low_level_spec = needle_len_pre).
  {
    match goal with
    | Hlen : Zlength needle0_low_level_spec = needle_len_pre |- _ => exact Hlen
    end.
  }
  Exists table_2.
  first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia; revgoals] | cancel].
  - assert (1 <= suffix) by (
      unfold memcmp_result, memcmp_eq in H1;
      destruct (Z.eq_dec suffix 0); subst;
      [ exfalso; apply H0; apply H1; rewrite !Zsublist_nil by lia; reflexivity
      | lia ]).
    lia.
  - assert (1 <= suffix) by (
      unfold memcmp_result, memcmp_eq in H1;
      destruct (Z.eq_dec suffix 0); subst;
      [ exfalso; apply H0; apply H1; rewrite !Zsublist_nil by lia; reflexivity
      | lia ]).
    lia.
  - match goal with Hs : safeExec _ _ _ |- _ => rename Hs into Hexec end.
  unfold applyf, maketuple in Hexec. prog_nf in Hexec.
    simpl in Hexec.
    unfold generic_match_phase in Hexec.
    prog_nf in Hexec.
    safe_choice_r Hexec.
    + replace (Z.max suffix (Zlength needle0_low_level_spec - suffix) + 1)
        with (needle_len_pre - suffix + 1) in Hexec by (rewrite Hneedle_len; lia).
      exact Hexec.
    + unfold repetitive_split, memcmp_result, memcmp_eq in *.
      intro Hr.
      apply H0.
      apply H1.
      replace (0 + suffix) with suffix by lia.
      replace (mp + suffix) with (suffix + mp) by lia.
      exact Hr.
Qed. 

Lemma proof_of_two_way_long_needle_entail_wit_19 : two_way_long_needle_entail_wit_19.
Proof.
  pre_process.
  prop_apply (UCharArray_full_Znth_range haystack_pre haystack_len_pre hay0_low_level_spec (j + needle_len_pre - 1) ltac:(lia)).
  Intros.
  Exists table_2.
  sep_apply_l_atomic (UCharArray.full_split_to_missing_i haystack_pre (j + needle_len_pre - 1) haystack_len_pre hay0_low_level_spec 0 ltac:(lia)).
  first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia; revgoals] | cancel].
Qed. 

Lemma proof_of_two_way_long_needle_entail_wit_20 : two_way_long_needle_entail_wit_20.
Proof.
  pre_process.
  rewrite replace_Znth_Znth by lia.
  prop_apply (UCharArray.full_Zlength haystack_pre haystack_len_pre hay0_low_level_spec).
  Intros.
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
  Intros.
  assert (Hhay_len : Zlength hay0_low_level_spec = haystack_len_pre).
  {
    match goal with
    | Hlen : Zlength hay0_low_level_spec = haystack_len_pre |- _ => exact Hlen
    end.
  }
  assert (Hneedle_len : Zlength needle0_low_level_spec = needle_len_pre).
  {
    match goal with
    | Hlen : Zlength needle0_low_level_spec = needle_len_pre |- _ => exact Hlen
    end.
  }
  Exists table.
  first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia; revgoals] | cancel].
  match goal with Htab : shift_table_sound _ _ _ |- _ => destruct Htab as [_ Hsound] end.
  specialize (Hsound j (Znth (Znth (j + needle_len_pre - 1) hay0_low_level_spec 0) table 0)).
  specialize (Hsound ltac:(split; [lia | rewrite Hhay_len, Hneedle_len; lia])
    ltac:(rewrite Hneedle_len; reflexivity)).
  destruct Hsound as [[Hz _] | Hskip].
  - rewrite Hz in H. lia.
  - exact Hskip.
Qed. 

Lemma proof_of_two_way_long_needle_entail_wit_21 : two_way_long_needle_entail_wit_21.
Proof.
  pre_process.
  rewrite replace_Znth_Znth by lia.
  prop_apply (UCharArray.full_Zlength haystack_pre haystack_len_pre hay0_low_level_spec).
  Intros.
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
  Intros.
  assert (Hhay_len : Zlength hay0_low_level_spec = haystack_len_pre).
  {
    match goal with
    | Hlen : Zlength hay0_low_level_spec = haystack_len_pre |- _ => exact Hlen
    end.
  }
  assert (Hneedle_len : Zlength needle0_low_level_spec = needle_len_pre).
  {
    match goal with
    | Hlen : Zlength needle0_low_level_spec = needle_len_pre |- _ => exact Hlen
    end.
  }
  Exists table.
  first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia; revgoals] | cancel].
  - match goal with Htab : shift_table_sound _ _ _ |- _ => destruct Htab as [_ Hsound] end.
    specialize (Hsound j (Znth (Znth (j + needle_len_pre - 1) hay0_low_level_spec 0) table 0)).
    specialize (Hsound ltac:(split; [lia | rewrite Hhay_len, Hneedle_len; lia])
      ltac:(rewrite Hneedle_len; reflexivity)).
    destruct Hsound as [[_ Hmatch] | Hskip].
    + rewrite Hneedle_len in Hmatch. exact Hmatch.
    + unfold valid_skip in Hskip. lia.
  - match goal with Htab : shift_table_sound _ _ _ |- _ => destruct Htab as [_ Hsound] end.
    specialize (Hsound j (Znth (Znth (j + needle_len_pre - 1) hay0_low_level_spec 0) table 0)).
    specialize (Hsound ltac:(split; [lia | rewrite Hhay_len, Hneedle_len; lia])
      ltac:(rewrite Hneedle_len; reflexivity)).
    destruct Hsound as [[Hz _] | Hskip].
    + exact Hz.
    + unfold valid_skip in Hskip. lia.
Qed. 

Lemma proof_of_two_way_long_needle_entail_wit_22 : two_way_long_needle_entail_wit_22.
Proof.
  pre_process.
  prop_apply (UCharArray.full_Zlength haystack_pre haystack_len_pre hay0_low_level_spec).
  Intros.
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
  Intros.
  assert (Hhay_len : Zlength hay0_low_level_spec = haystack_len_pre).
  {
    match goal with
    | Hlen : Zlength hay0_low_level_spec = haystack_len_pre |- _ => exact Hlen
    end.
  }
  assert (Hneedle_len : Zlength needle0_low_level_spec = needle_len_pre).
  {
    match goal with
    | Hlen : Zlength needle0_low_level_spec = needle_len_pre |- _ => exact Hlen
    end.
  }
  Exists table_2.
  sep_apply (store_int_undef_store_int (&("shift"))).
  first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia; revgoals] | cancel].
  match goal with Hs : safeExec _ _ _ |- _ => rename Hs into Hexec end.
  unfold generic_match_from in Hexec. prog_nf in Hexec.
  unfold_loop in Hexec. prog_nf in Hexec.
  unfold generic_match_loop_body in Hexec at 1.
  prog_nf in Hexec.
  apply safeExec_choice_r in Hexec.
  unfold match_loop_body in Hexec at 1; prog_nf in Hexec.
  safe_choice_l Hexec; [|rewrite Hneedle_len,Hhay_len;lia].
  unfold generic_match_from_right.
  prog_nf in Hexec.
  eapply safeExec_proequiv; [|exact Hexec].
  unfold generic_match_after_right, generic_match_from_left,
    generic_match_after_left, generic_match_from, continue, break.
  repeat first [reflexivity | progress prog_nf | apply common_step_equiv; intro | apply choice_case_equiv].
Qed. 

Lemma proof_of_two_way_long_needle_entail_wit_23 : two_way_long_needle_entail_wit_23.
Proof.
  pre_process.
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
  Intros.
  assert (Hneedle_len : Zlength needle0_low_level_spec = needle_len_pre).
  {
    match goal with
    | Hlen : Zlength needle0_low_level_spec = needle_len_pre |- _ => exact Hlen
    end.
  }
  Exists table_2.
  first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia; revgoals] | cancel].
  - replace (needle_pre + (i + 1) * sizeof(UCHAR))
      with (needle_pre + i * sizeof(UCHAR) + 1 * sizeof(UCHAR))
      by (rewrite sizeof_uchar; lia).
    replace (haystack_pre + (i + 1 + j) * sizeof(UCHAR))
      with (haystack_pre + (i + j) * sizeof(UCHAR) + 1 * sizeof(UCHAR))
      by (rewrite sizeof_uchar; lia).
    first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia; revgoals] | cancel].
  - match goal with Hs : safeExec _ _ _ |- _ => rename Hs into Hexec end.
    unfold generic_match_from_right in Hexec at 1; prog_nf in Hexec.
    unfold match_right in Hexec at 1; prog_nf in Hexec.
    unfold_loop in Hexec; prog_nf in Hexec.
    unfold match_right_f in Hexec at 1; prog_nf in Hexec.
    safe_choice_l Hexec.
    + unfold continue in Hexec at 1; prog_nf in Hexec.
      unfold generic_match_from_right.
      unfold match_right.
      exact Hexec.
    + split.
      * rewrite Hneedle_len; lia.
      * unfold match_cond.
        replace (j + i) with (i + j) by lia.
        exact H.
Qed. 

Lemma proof_of_two_way_long_needle_entail_wit_24 : two_way_long_needle_entail_wit_24.
Proof.
  pre_process.
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
  Intros.
  assert (Hneedle_len : Zlength needle0_low_level_spec = needle_len_pre).
  {
    match goal with
    | Hlen : Zlength needle0_low_level_spec = needle_len_pre |- _ => exact Hlen
    end.
  }
  assert (i = needle_len_pre - 1) by lia.
  subst i.
  Exists table_2.
  first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia; revgoals] | cancel].
  { cancel (&("pneedle") # Ptr |-> (needle_pre + (suffix - 1) * sizeof(UCHAR))).
    cancel (&("phaystack") # Ptr |-> (haystack_pre + (suffix - 1 + j) * sizeof(UCHAR))).
    cancel. }
  match goal with Hs : safeExec _ _ _ |- _ => rename Hs into Hexec end.
  unfold generic_match_from_right in Hexec. prog_nf in Hexec.
  unfold match_right in Hexec. prog_nf in Hexec.
  unfold_loop in Hexec. prog_nf in Hexec.
  unfold match_right_f in Hexec at 1.
  prog_nf in Hexec.
  safe_choice_l Hexec.
  2: { split; [rewrite Hneedle_len; lia |].
       match goal with Hlast : match_cond _ _ _ (needle_len_pre - 1) |- _ => exact Hlast end. }
  unfold continue in Hexec at 1; prog_nf in Hexec.
  replace (needle_len_pre - 1 + 1) with needle_len_pre in Hexec by lia.
  unfold_loop in Hexec; prog_nf in Hexec.
  unfold match_right_f in Hexec at 1; prog_nf in Hexec.
  safe_choice_r Hexec; [|left; rewrite Hneedle_len;lia].
  unfold break in Hexec at 1; prog_nf in Hexec.
  unfold generic_match_after_right in Hexec at 1; prog_nf in Hexec.
  safe_choice_l Hexec; try lia.
  exact Hexec.
Qed. 

Lemma proof_of_two_way_long_needle_entail_wit_25 : two_way_long_needle_entail_wit_25.
Proof.
  pre_process.
  Exists table_2.
  first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia; revgoals] | cancel].
  - replace (needle_pre + i * sizeof(UCHAR) - 1 * sizeof(UCHAR))
      with (needle_pre + (i - 1) * sizeof(UCHAR))
      by (rewrite sizeof_uchar; lia).
    replace (haystack_pre + (i + j) * sizeof(UCHAR) - 1 * sizeof(UCHAR))
      with (haystack_pre + (i - 1 + j) * sizeof(UCHAR))
      by (rewrite sizeof_uchar; lia).
    first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia; revgoals] | cancel].
    cancel (&("pneedle") # Ptr |-> (needle_pre + (i - 1) * sizeof(UCHAR))).
    cancel (&("phaystack") # Ptr |-> (haystack_pre + (i - 1 + j) * sizeof(UCHAR))).
  - match goal with Hs : safeExec _ _ _ |- _ => rename Hs into Hexec end.
    unfold generic_match_from_left in Hexec at 1.
    prog_nf in Hexec.
    unfold match_left in Hexec at 1.
    prog_nf in Hexec.
    unfold_loop in Hexec.
    prog_nf in Hexec.
    unfold match_left_f in Hexec at 1.
    prog_nf in Hexec.
    safe_choice_l Hexec.
    + unfold continue in Hexec at 1.
      prog_nf in Hexec.
      unfold generic_match_from_left.
      prog_nf.
      unfold match_left.
      exact Hexec.
    + split.
      * lia.
      * unfold match_cond.
        replace (j + i) with (i + j) by lia.
        exact H.
Qed. 

Lemma proof_of_two_way_long_needle_entail_wit_26_1 : two_way_long_needle_entail_wit_26_1.
Proof.
  pre_process.
  prop_apply (UCharArray.full_Zlength haystack_pre haystack_len_pre hay0_low_level_spec).
  Intros.
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
  Intros.
  assert (Hskip_bound_len : j + shift <= haystack_len_pre).
  {
    pose proof H0 as Hskip.
    unfold valid_skip in Hskip.
    destruct Hskip as [_ [Hbound _]].
    match goal with
    | Hlen : Zlength hay0_low_level_spec = haystack_len_pre |- _ =>
        rewrite <- Hlen; exact Hbound
    end.
  }
  assert (Hloop_bound_len :
    j + Zlength needle0_low_level_spec <= Zlength hay0_low_level_spec).
  {
    match goal with
    | Hhay : Zlength hay0_low_level_spec = haystack_len_pre,
      Hneedle : Zlength needle0_low_level_spec = needle_len_pre |- _ =>
        rewrite Hhay, Hneedle; lia
    end.
  }
  Exists table_2.
  sep_apply (store_int_undef_store_int (&("shift"))).
  first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia; revgoals] | cancel].
  - match goal with Hs : safeExec _ _ _ |- _ => rename Hs into Hexec end.
  unfold generic_match_from in Hexec. prog_nf in Hexec.
    unfold_loop in Hexec. prog_nf in Hexec.
    unfold generic_match_loop_body in Hexec at 1.
    prog_nf in Hexec.
    safe_choice_l Hexec.
    + prog_nf in Hexec. eapply (@safeExec_any_bind _ _ Z _ _ _ shift) in Hexec.
        safe_step Hexec.
        unfold continue in Hexec.
        prog_nf in Hexec.
        unfold generic_match_from.
        exact Hexec.
Qed. 

Lemma proof_of_two_way_long_needle_entail_wit_26_2 : two_way_long_needle_entail_wit_26_2.
Proof.
  pre_process.
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
  Intros.
  Exists table_2.
  sep_apply (store_int_undef_store_int (&("i")) i).
  first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia; revgoals] | cancel].
  - match goal with Hs : safeExec _ _ _ |- _ => rename Hs into Hexec end.
  unfold generic_match_from_right in Hexec. prog_nf in Hexec.
    unfold match_right in Hexec. prog_nf in Hexec.
    unfold_loop in Hexec. prog_nf in Hexec.
    unfold match_right_f in Hexec at 1.
    prog_nf in Hexec.
    safe_choice_r Hexec.
    + prog_nf in Hexec.
      unfold break in Hexec.
      prog_nf in Hexec.
      unfold generic_match_after_right in Hexec. prog_nf in Hexec.
      safe_choice_r Hexec; try lia.
      unfold continue in Hexec.
      prog_nf in Hexec.
      replace (j + (i - suffix + 1)) with (j + i - suffix + 1) by lia.
      exact Hexec.
      all: try lia.
      all: try (match goal with
        | Hlen : Zlength ?xs = ?n |- _ =>
            rewrite Hlen; lia
        end).
    + right. unfold match_cond.
      replace (j + i) with (i + j) by lia.
      exact H0.
Qed. 

Lemma proof_of_two_way_long_needle_entail_wit_26_3 : two_way_long_needle_entail_wit_26_3.
Proof.
  pre_process.
  Exists table_2.
  sep_apply (store_int_undef_store_int (&("i")) i).
  first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia; revgoals] | cancel].
  match goal with Hs : safeExec _ _ _ |- _ => rename Hs into Hexec end.
  unfold generic_match_from_left in Hexec at 1.
  prog_nf in Hexec.
  unfold match_left in Hexec at 1.
  prog_nf in Hexec.
  unfold_loop in Hexec.
  prog_nf in Hexec.
  unfold match_left_f in Hexec at 1.
  prog_nf in Hexec.
  safe_choice_r Hexec.
  - unfold break in Hexec at 1.
    prog_nf in Hexec.
    unfold generic_match_after_left in Hexec at 1.
    prog_nf in Hexec.
    safe_choice_r Hexec; try lia.
    exact Hexec.
  - right.
    unfold match_cond.
    replace (j + i) with (i + j) by lia.
    exact H0.
Qed. 

Lemma proof_of_two_way_long_needle_return_wit_1 : two_way_long_needle_return_wit_1.
Proof.
  pre_process.
  prop_apply (UCharArray.full_Zlength haystack_pre haystack_len_pre hay0_low_level_spec).
  Intros.
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
  Intros.
  assert (Hhay_len : Zlength hay0_low_level_spec = haystack_len_pre) by
    (match goal with Hlen : Zlength hay0_low_level_spec = haystack_len_pre |- _ => exact Hlen end).
  assert (Hneedle_len : Zlength needle0_low_level_spec = needle_len_pre) by
    (match goal with Hlen : Zlength needle0_low_level_spec = needle_len_pre |- _ => exact Hlen end).
  try split_pure_spatial; try cancel; try split_pures; try dump_pre_spatial; try assumption; try reflexivity; try lia.
  unfold generic_match_periodic_from in H0.
  unfold_loop in H0.
  unfold generic_match_periodic_loop_body in H0 at 1.
  prog_nf in H0.
  safe_choice_r H0.
  unfold match_periodic_loop_body in H0 at 1; prog_nf in H0.
  safe_choice_r H0; try (rewrite Hneedle_len, Hhay_len; lia).
  unfold break in H0.
  prog_nf in H0.
  unfold uchar_ptr_option_repr.
  simpl.
  exact H0.
Qed.

Lemma proof_of_two_way_long_needle_return_wit_2 : two_way_long_needle_return_wit_2.
Proof.
  pre_process.
  prop_apply (UCharArray.full_Zlength haystack_pre haystack_len_pre hay0_low_level_spec).
  Intros.
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_low_level_spec).
  Intros.
  assert (Hhay_len : Zlength hay0_low_level_spec = haystack_len_pre) by
    (match goal with Hlen : Zlength hay0_low_level_spec = haystack_len_pre |- _ => exact Hlen end).
  assert (Hneedle_len : Zlength needle0_low_level_spec = needle_len_pre) by
    (match goal with Hlen : Zlength needle0_low_level_spec = needle_len_pre |- _ => exact Hlen end).
  try split_pure_spatial; try cancel; try split_pures; try dump_pre_spatial; try assumption; try reflexivity; try lia.
  unfold generic_match_from in H0.
  unfold_loop in H0.
  unfold generic_match_loop_body in H0 at 1.
  prog_nf in H0.
  safe_choice_r H0.
  unfold match_loop_body in H0 at 1; prog_nf in H0.
  safe_choice_r H0; try (rewrite Hneedle_len, Hhay_len; lia).
  unfold break in H0.
  prog_nf in H0.
  unfold uchar_ptr_option_repr.
  simpl.
  exact H0.
Qed.

Lemma proof_of_two_way_long_needle_return_wit_3 : two_way_long_needle_return_wit_3.
Proof.
  pre_process.
  subst i.
  first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia; revgoals] | cancel].
  match goal with Hs : safeExec _ _ _ |- _ => rename Hs into Hexec end.
  unfold generic_match_from_left in Hexec. prog_nf in Hexec.
  unfold match_left in Hexec. prog_nf in Hexec.
  unfold_loop in Hexec. prog_nf in Hexec.
  unfold match_left_f in Hexec at 1.
  prog_nf in Hexec.
  safe_choice_r Hexec; try lia.
  unfold break in Hexec.
  prog_nf in Hexec.
  unfold generic_match_after_left in Hexec. prog_nf in Hexec.
  safe_choice_l Hexec; try lia.
  unfold break in Hexec.
  prog_nf in Hexec.
  unfold uchar_ptr_option_repr.
  rewrite sizeof_uchar.
  destruct (Z.eq_dec (haystack_pre + j * 1) NULL) as [Heq | Hneq].
  - change (haystack_pre + j * 1 = 0) in Heq.
    lia.
  - rewrite Z.div_1_r.
    replace (haystack_pre + j * 1 - haystack_pre) with j by lia.
    exact Hexec.
Qed.

Lemma proof_of_two_way_long_needle_return_wit_4 : two_way_long_needle_return_wit_4.
Proof.
  pre_process.
  first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; try assumption; try reflexivity; try lia; revgoals] | cancel].
  match goal with Hs : safeExec _ _ _ |- _ => rename Hs into Hexec end.
  unfold generic_match_periodic_from_left in Hexec. prog_nf in Hexec.
  unfold match_periodic_from_left in Hexec. prog_nf in Hexec.
  unfold match_left in Hexec. prog_nf in Hexec.
  unfold_loop in Hexec. prog_nf in Hexec.
  unfold match_left_f in Hexec at 1.
  prog_nf in Hexec.
  safe_choice_r Hexec; try lia.
  unfold break in Hexec.
  prog_nf in Hexec.
  unfold match_periodic_after_left in Hexec. prog_nf in Hexec.
  safe_choice_l Hexec; try lia.
  unfold break in Hexec.
  prog_nf in Hexec.
  unfold uchar_ptr_option_repr.
  rewrite sizeof_uchar.
  destruct (Z.eq_dec (haystack_pre + j * 1) NULL) as [Heq | Hneq].
  - change (haystack_pre + j * 1 = 0) in Heq.
    lia.
  - rewrite Z.div_1_r.
    replace (haystack_pre + j * 1 - haystack_pre) with j by lia.
    exact Hexec.
Qed.

Lemma proof_of_two_way_long_needle_partial_solve_wit_1_pure : two_way_long_needle_partial_solve_wit_1_pure.
Proof. pre_process. Qed.

Lemma proof_of_two_way_long_needle_derive_high_level_spec_by_low_level_spec : two_way_long_needle_derive_high_level_spec_by_low_level_spec.
Proof.
  pre_process.
  prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_high_level_spec).
  Intros.
  assert (Hneedle_nonempty : needle0_high_level_spec <> nil).
  { intro Hnil.
    subst needle0_high_level_spec.
    match goal with
    | Hlen : Zlength (@nil Z) = needle_len_pre |- _ =>
        rewrite Zlength_nil in Hlen; lia
    | Hlen : needle_len_pre = Zlength (@nil Z) |- _ =>
        rewrite Zlength_nil in Hlen; lia
    end. }
  Exists hay0_high_level_spec needle0_high_level_spec hn_high_level_spec nn_high_level_spec.
  remember (two_way_generic_prog hay0_high_level_spec needle0_high_level_spec) as prog.
  Exists (fun (r: option Z) x => prog.(MonadErr.nrm) tt r x).
  pose proof (two_way_generic_prog_sound hay0_high_level_spec needle0_high_level_spec) as Hsound.
  do 2 apply derivable1_wand_sepcon_adjoint.
  (first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; auto; try lia] | cancel]).
  2:{
    destruct Hsound as [_ Hnoerr].
    specialize (Hnoerr tt Hneedle_nonempty).
    subst prog.
    apply safeExec_monad_Atrue_finnal; tauto.
  }
  cancel (UCharArray.full haystack_pre haystack_len_pre hay0_high_level_spec).
  cancel (UCharArray.full needle_pre needle_len_pre needle0_high_level_spec).
  apply derivable1_wand_sepcon_adjoint.
  (first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; auto; try lia] | cancel]).
  Intros retval.
  destruct Hsound as [Hpost _].
  match goal with
  | Hret : safeExec ATrue _ _ |- _ =>
      apply safeExec_ret_Atrue_finnal in Hret;
      destruct Hret as [sigma Hrun]
  end.
  subst prog.
  specialize (Hpost (uchar_ptr_option_repr haystack_pre retval (sizeof (UCHAR))) tt sigma Hneedle_nonempty Hrun).
  Exists (uchar_ptr_option_repr haystack_pre retval (sizeof (UCHAR))) retval.
  (first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; auto; try lia] | cancel]).
Qed.

Lemma proof_of_two_way_short_needle_derive_high_level_spec_by_low_level_spec : two_way_short_needle_derive_high_level_spec_by_low_level_spec.
Proof.
    pre_process.
    prop_apply (UCharArray.full_Zlength needle_pre needle_len_pre needle0_high_level_spec).
    Intros.
    assert (Hneedle_nonempty : needle0_high_level_spec <> nil).
    { intro Hnil.
      subst needle0_high_level_spec.
      match goal with
      | Hlen : Zlength (@nil Z) = needle_len_pre |- _ =>
          rewrite Zlength_nil in Hlen; lia
      | Hlen : needle_len_pre = Zlength (@nil Z) |- _ =>
          rewrite Zlength_nil in Hlen; lia
      end. }
    Exists hay0_high_level_spec needle0_high_level_spec hn_high_level_spec nn_high_level_spec.
    remember (two_way_generic_prog hay0_high_level_spec needle0_high_level_spec) as prog.
    Exists (fun (r: option Z) x => prog.(MonadErr.nrm) tt r x).
    pose proof (two_way_generic_prog_sound hay0_high_level_spec needle0_high_level_spec) as Hsound.
    do 2 apply derivable1_wand_sepcon_adjoint.
    (first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; auto; try lia] | cancel]).
    2:{
      destruct Hsound as [_ Hnoerr].
      specialize (Hnoerr tt Hneedle_nonempty).
      subst prog.
      apply safeExec_monad_Atrue_finnal; tauto.
    }
    cancel (UCharArray.full haystack_pre haystack_len_pre hay0_high_level_spec).
  cancel (UCharArray.full needle_pre needle_len_pre needle0_high_level_spec).
  apply derivable1_wand_sepcon_adjoint.
    (first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; auto; try lia] | cancel]).
    Intros retval.
    destruct Hsound as [Hpost _].
    match goal with
    | Hret : safeExec ATrue _ _ |- _ =>
        apply safeExec_ret_Atrue_finnal in Hret;
        destruct Hret as [sigma Hrun]
    end.
    subst prog.
    specialize (Hpost (uchar_ptr_option_repr haystack_pre retval (sizeof (UCHAR))) tt sigma Hneedle_nonempty Hrun).
    Exists (uchar_ptr_option_repr haystack_pre retval (sizeof (UCHAR))) retval.
    (first [split_pure_spatial; [try cancel | split_pures; dump_pre_spatial; auto; try lia] | cancel]).
Qed.

Lemma proof_of_critical_factorization_derive_bind_spec_by_low_level_spec : critical_factorization_derive_bind_spec_by_low_level_spec.
Proof.
    unfold critical_factorization_derive_bind_spec_by_low_level_spec; intros; Intros.
    prop_apply UCharArray.full_Zlength. Intros.
    (* TODO(manual): this non-two_way_short_needle proof still uses the
       low-level safeExec_bind decomposition. It compiles, but should be
       revisited if this file is normalized to the wrapper/prog_nf proof
       style used for safeExec goals. *)
    apply safeExec_bind in H as (X_low_level_spec & Hsafe_low & Hsafe_cont).
    Exists needle0_bind_spec.
    Exists n0_bind_spec.
    Exists X_low_level_spec.
    entailer!.
    apply derivable1_wand_sepcon_adjoint.
    entailer!.
    Intros mp_2 retval_2.
    Exists mp_2 retval_2.
    entailer!.
Qed. 

Lemma proof_of_critical_factorization_derive_long_needle_bind_spec_by_low_level_spec :
  critical_factorization_derive_long_needle_bind_spec_by_low_level_spec.
Proof.
  unfold critical_factorization_derive_long_needle_bind_spec_by_low_level_spec; intros; Intros.
  apply safeExec_bind in H as (Xmid & Hlow & Hcont).
  prop_apply UCharArray.full_Zlength. Intros.
  Exists needle0_long_needle_bind_spec n0_long_needle_bind_spec
    (fun r x =>
       Xmid r x /\
       (critical_factorization_prog needle0_long_needle_bind_spec).(MonadErr.nrm)
         tt r x).
  entailer!.
  2: {
    unfold safeExec, safe, ATrue, weakestpre in Hlow |- *.
    destruct Hlow as (s & _ & Herr & Hnrm).
    destruct s.
    exists tt.
    split; [exact I | split].
    - exact Herr.
    - intros r s Hr.
      split; [eapply Hnrm; exact Hr | exact Hr].
  }
  apply derivable1_wand_sepcon_adjoint.
  entailer!.
  Intros mp_2 retval_2.
  unfold safeExec, safe, ATrue, weakestpre in H3.
  unfold_monad in H3.
  destruct H3 as ([] & _ & _ & Hpost).
  specialize (Hpost (maketuple retval_2 mp_2) tt
    ltac:(split; reflexivity)).
  destruct Hpost as [HXmid Hrun].
  assert (Hret_mid :
    safeExec ATrue (ret (maketuple retval_2 mp_2)) Xmid).
  {
    unfold safeExec, safe, ATrue, weakestpre.
    unfold_monad.
    exists tt.
    split; [exact I | split].
    - sets_unfold; tauto.
    - sets_unfold.
      intros r [] [Hr _].
      subst r.
      exact HXmid.
  }
  pose proof (Hcont ATrue (maketuple retval_2 mp_2) Hret_mid) as Hnext.
  change
    ((critical_factorization_prog needle0_long_needle_bind_spec).(MonadErr.nrm)
       tt (maketuple retval_2 mp_2) tt) in Hrun.
  assert (Hneedle_nonempty : needle0_long_needle_bind_spec <> nil).
  {
    intro Hnil.
    subst needle0_long_needle_bind_spec.
    rewrite Zlength_nil in H.
    lia.
  }
  pose proof
    (critical_factorization_prog_sound
       needle0_long_needle_bind_spec Hneedle_nonempty) as Hsound.
  unfold Hoare in Hsound.
  destruct Hsound as [Hsound _].
  specialize (Hsound (maketuple retval_2 mp_2) tt tt I Hrun).
  assert (Hspec :
    critical_factorization_spec needle0_long_needle_bind_spec
      (maketuple retval_2 mp_2)).
  {
    unfold critical_factorization_spec.
    simpl.
    intros Hrep.
    split.
    - unfold pattern_period.
      exact
        (repetitive_split_period needle0_long_needle_bind_spec Hneedle_nonempty
           retval_2 mp_2 Hsound Hrep).
    - pose proof Hsound as Hbounds.
      destruct Hbounds as [[minp [Hmin [Hl Hrest]]]].
      split.
      + lia.
      + eapply
          (repetitive_split_l_lt_p needle0_long_needle_bind_spec
             Hneedle_nonempty retval_2 mp_2); eauto.
  }
  Exists mp_2 retval_2.
  entailer!.
Qed.
