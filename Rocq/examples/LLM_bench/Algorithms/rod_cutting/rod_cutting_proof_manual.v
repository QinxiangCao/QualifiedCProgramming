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
From SimpleC.EE.LLM_bench.Algorithms.rod_cutting Require Import rod_cutting_goal.
From SimpleC.EE.LLM_bench.Algorithms.rod_cutting Require Import rod_cutting_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.rod_cutting.rod_cutting_lib.
Local Open Scope sac.
Local Opaque IntArray.full IntArray.seg IntArray.undef_full IntArray.undef_seg.


From AUXLib Require Import MonotonicList.



Lemma proof_of_rod_cutting_safety_wit_6 : rod_cutting_safety_wit_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply (IntArray.full_Zlength price_pre (n_pre + 1) price_l).
  Intros.
  pose proof (proj1 (Forall_Znth (Z.le 0) 0 price_l) PreH3 i ltac:(lia)) as Hprice_lo.
  pose proof (proj1 (Forall_Znth (Z.ge 1000000) 0 price_l) PreH4 i ltac:(lia)) as Hprice_hi.
  pose proof (PreH13 (j - i) ltac:(lia)) as Hrest.
  replace ((j - i) - 0) with (j - i) by lia.
  split_pures; dump_pre_spatial; int_auto.
Qed.

Lemma proof_of_rod_cutting_entail_wit_1 : rod_cutting_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (0 :: nil).
  split_pure_spatial.
  - cancel (IntArray.full price_pre (n_pre + 1) price_l).
    cancel (IntArray.undef_seg (&( "revenue" )) 1 1001).
    sep_apply_l_atomic (IntArray.seg_single (&( "revenue" )) 0 0).
    change (0 + 1) with 1.
    cancel (IntArray.seg (&( "revenue" )) 0 1 (0 :: nil)).
  - split_pures; dump_pre_spatial; try assumption; try lia.
    + unfold RodCutRevenueTable.
      intros rod_len Hrod_len.
      assert (rod_len = 0) by lia.
      subst rod_len.
      simpl.
      apply rod_cut_optimal_revenue_zero__boundary_states.
    + intros k Hk.
      assert (k = 0) by lia.
      subst k.
      rewrite Znth0_cons.
      split; lia.
Qed.

Lemma proof_of_rod_cutting_entail_wit_2 : rod_cutting_entail_wit_2.
Proof.
  aggressive_pre_process.
  - intros k Hk. apply PreH8. exact Hk.
  - apply rod_cut_scan_best_default_iff.
    apply MaxMin.max_default_default.
    intros piece Hpiece. lia.
Qed.

Lemma proof_of_rod_cutting_entail_wit_3_1 : rod_cutting_entail_wit_3_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply (IntArray.full_Zlength price_pre (n_pre + 1) price_l).
  Intros.
  pose proof (proj1 (Forall_Znth (Z.ge 1000000) 0 price_l) PreH5 i ltac:(lia)) as Hprice_hi.
  pose proof (PreH14 (j - i) ltac:(lia)) as Hrest.
  replace ((j - i) - 0) with (j - i) in * by lia.
  Exists revenue_l_2.
  split_pure_spatial.
  - entailer!.
  - split_pures; dump_pre_spatial; try assumption; try lia.
    apply rod_cut_scan_best_default_iff.
    apply rod_cut_scan_best_default_iff in PreH13.
    eapply rod_cut_scan_best_step__scan_transitions; [lia | exact PreH13 |].
    left; split; [lia | reflexivity].
Qed.

Lemma proof_of_rod_cutting_entail_wit_3_2 : rod_cutting_entail_wit_3_2.
Proof.
  aggressive_pre_process.
  replace ((j - i) - 0) with (j - i) in * by lia.
  apply rod_cut_scan_best_default_iff.
  apply rod_cut_scan_best_default_iff in PreH13.
  eapply rod_cut_scan_best_step__scan_transitions; [lia | exact PreH13 |].
  right; split; [lia | reflexivity].
Qed.

Lemma proof_of_rod_cutting_entail_wit_4 : rod_cutting_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  prop_apply (IntArray.seg_Zlength (&( "revenue" )) 0 (j + 1) (revenue_l_2 ++ (best :: nil))).
  Intros.
  prop_apply (IntArray.full_Zlength price_pre (n_pre + 1) price_l).
  Intros.
  assert (Hlen : Zlength revenue_l_2 = j).
  { rewrite Zlength_app, Zlength_cons, Zlength_nil in *. lia. }
  assert (i = j + 1) by lia.
  subst i.
  pose proof (proj1 (Forall_Znth (Z.le 0) 0 price_l) PreH3 j ltac:(lia)) as Hprice_lo.
  pose proof (rod_cut_revenue_table_snoc__table_extension
    price_l revenue_l_2 j best PreH5 Hlen Hprice_lo PreH11 PreH12) as Htable.
  assert (Hbounds : forall k, 0 <= k < j + 1 ->
    0 <= Znth k (revenue_l_2 ++ (best :: nil)) 0 <= k * 1000000).
  {
    intros k Hk.
    destruct (Z_lt_ge_dec k j) as [Hlt | Hge].
    - rewrite app_Znth1 by lia.
      apply PreH13. lia.
    - assert (k = j) by lia. subst k.
      rewrite app_Znth2 by lia.
      rewrite Hlen.
      replace (j - j) with 0 by lia.
      rewrite Znth0_cons.
      lia.
  }
  Exists (revenue_l_2 ++ (best :: nil)).
  split_pure_spatial.
  - entailer!.
  - split_pures; dump_pre_spatial; try assumption; lia.
Qed.

Lemma proof_of_rod_cutting_entail_wit_5 : rod_cutting_entail_wit_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hj : j = n_pre + 1) by lia.
  split_pure_spatial.
  - sep_apply_l_atomic (IntArray.seg_to_undef_seg (&( "revenue" )) 0 (j) revenue_l).
    sep_apply_l_atomic (IntArray.undef_seg_merge_to_undef_full (&( "revenue" )) 0 (j) 1001 ltac:(lia)).
    simpl. replace ((&( "revenue" )) + 0) with (&( "revenue" )) by lia.
    entailer!.
  - split_pures; dump_pre_spatial; try lia.
    replace (n_pre - 0) with n_pre by lia. apply PreH7. lia.
Qed.