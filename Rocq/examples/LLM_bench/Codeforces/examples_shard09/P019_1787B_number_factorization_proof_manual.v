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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P019_1787B_number_factorization_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P019_1787B_number_factorization_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P019_1787B_number_factorization_lib.
Local Open Scope sac.

Lemma proof_of_solver_safety_wit_10_split_goal_1 : solver_safety_wit_10_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite app_Znth2 by lia.
  rewrite PreH11.
  replace (m - 0 - m) with 0 by lia.
  simpl.
  unfold FactorExtract in PreH13.
  destruct PreH13 as [_ [_ [_ [_ [_ [_ [_ [He _]]]]]]]].
  change (Znth 0 (e :: nil) 0) with e.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_10_split_goal_2 : solver_safety_wit_10_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite app_Znth2 by lia.
  rewrite PreH11.
  replace (m - 0 - m) with 0 by lia.
  simpl.
  unfold FactorExtract in PreH13.
  destruct PreH13 as [_ [_ [_ [_ [_ [_ [_ [He _]]]]]]]].
  change (Znth 0 (e :: nil) 0) with e.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_10 : solver_safety_wit_10.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_10_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_10_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_25_split_goal_1 : solver_safety_wit_25_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (i - 0) with i in PreH1 by lia.
  unfold LayerProductPrefix in PreH20.
  destruct PreH20 as [_ [_ [_ [_ [_ Hfuture]]]]].
  specialize (Hfuture i ltac:(lia) ltac:(lia)).
  replace (i - 0) with i by lia.
  rewrite (Znth_indep ps i 0 1) by lia.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_25_split_goal_2 : solver_safety_wit_25_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold LayerProductPrefix in PreH20.
  destruct PreH20 as [Hfact [_ [_ [_ [Hprod _]]]]].
  destruct Hprod as [Hprod _].
  unfold PrimeFactorization in Hfact.
  destruct Hfact as [_ [_ [Hprofile _]]].
  unfold PrimeExponentProfile in Hprofile.
  destruct Hprofile as [_ [_ [Hprimes _]]].
  rewrite Forall_nth in Hprimes.
  assert (Hi : 0 <= i < Zlength ps) by lia.
  assert (Hi_nat : (Z.to_nat i < length ps)%nat).
  { rewrite Zlength_correct in Hi. lia. }
  pose proof (Hprimes (Z.to_nat i) 1 Hi_nat) as Hp.
  pose proof (Znumtheory.prime_ge_2 _ Hp) as Hp2.
  change (2 <= Znth i ps 1) in Hp2.
  replace (i - 0) with i by lia.
  rewrite (Znth_indep ps i 0 1) by lia.
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_25 : solver_safety_wit_25.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_25_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_25_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_26_split_goal_1 : solver_safety_wit_26_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (i = m) by lia.
  subst i.
  unfold LayerProductPrefix in PreH19.
  destruct PreH19 as [_ [_ [_ [Hprod_eq _]]]].
  unfold LayerSumPrefix in PreH18.
  destruct PreH18 as [_ [_ [_ [_ [_ Hnext]]]]].
  specialize (Hnext ltac:(lia)).
  assert (Hprod_layer : prod = LayerValue ps es k).
  { unfold LayerValue. rewrite PreH8. exact Hprod_eq. }
  rewrite Hprod_layer.
  dump_pre_spatial.
  lia.
Qed.

Lemma proof_of_solver_safety_wit_26_split_goal_2 : solver_safety_wit_26_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold LayerSumPrefix in PreH18.
  destruct PreH18 as [_ [_ [_ [_ [Htotal _]]]]].
  unfold LayerProductPrefix in PreH19.
  destruct PreH19 as [_ [_ [_ [_ [Hprod _]]]]].
  dump_pre_spatial.
  nia.
Qed.

Lemma proof_of_solver_safety_wit_26 : solver_safety_wit_26.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_26_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_26_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold FactorScan, PrimeExponentProfile, FactorPower.
  simpl. repeat split; try lia; try constructor.
  all: intros; simpl in *; try rewrite Zlength_nil in *; try ring; try lia.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto || reflexivity).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto || reflexivity).
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (factor_scan_divisible_starts_extract__extraction_start
      n_pre n d ps_2 es_2 PreH14 PreH1 PreH2)
    as [Hscale Hextract].
  Exists 0 es_2 ps_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial;
      try lia; try assumption; try reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (factor_extract_divide_step__extraction_start
      n_pre n d ps_2 es_2 e_2 PreH13 PreH12 PreH1)
    as [Hscale Hextract].
  pose proof Hextract as Hextract_fields.
  unfold FactorExtract in Hextract_fields.
  destruct Hextract_fields as
    (Horig & Hremb & Hd & Hcap & Hprof & Hlt & Hprime & He & Heq & Hscan & Hzero).
  destruct Hremb as [Hqpos Hqbound].
  assert (Hreplace :
    replace_Znth m (Znth (m - 0) (es_2 ++ (e_2 :: nil)) 0 + 1)
      (es_2 ++ (e_2 :: nil)) = es_2 ++ ((e_2 + 1) :: nil)).
  { replace (m - 0) with m by lia.
    rewrite <- PreH11.
    apply replace_Znth_last_increment__extraction_start. }
  rewrite Hreplace.
  Exists (e_2 + 1) es_2 ps_2.
  split_pure_spatial.
  - sep_apply_l_atomic
      (Int64Array.full_to_seg (&( "ex" )) (m + 1)
        (es_2 ++ ((e_2 + 1) :: nil))).
    repeat cancel.
  - split_pures; dump_pre_spatial;
      try lia; try assumption; try reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_1 : solver_entail_wit_4_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (factor_extract_nondividing_to_scan__scan_completion
    n_pre n d ps_2 es_2 e PreH13 PreH12 PreH1) as Hclose.
  exact (proj1 Hclose).
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_2 : solver_entail_wit_4_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_app_cons. lia.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_3 : solver_entail_wit_4_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_app_cons. lia.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_4 : solver_entail_wit_4_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (factor_extract_nondividing_to_scan__scan_completion
    n_pre n d ps_2 es_2 e PreH13 PreH12 PreH1) as Hclose.
  destruct Hclose as [_ [Hcapacity _]]. lia.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_5 : solver_entail_wit_4_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (factor_extract_nondividing_to_scan__scan_completion
    n_pre n d ps_2 es_2 e PreH13 PreH12 PreH1) as Hclose.
  destruct Hclose as [_ [_ Hdnext]].
  nia.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_6 : solver_entail_wit_4_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (factor_extract_nondividing_to_scan__scan_completion
    n_pre n d ps_2 es_2 e PreH13 PreH12 PreH1) as Hclose.
  destruct Hclose as [_ [_ Hdnext]]. exact Hdnext.
Qed.

Lemma proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_4_1_split_goal_6.
Qed.

Lemma proof_of_solver_entail_wit_4_2_split_goal_1 : solver_entail_wit_4_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply factor_scan_skip_candidate__scan_completion; eauto.
Qed.

Lemma proof_of_solver_entail_wit_4_2_split_goal_2 : solver_entail_wit_4_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_5_1_split_goal_1 : solver_entail_wit_5_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (factor_scan_finish_prime__scan_completion
    n_pre n d ps_2 es_2 ltac:(lia) ltac:(lia) PreH14).
Qed.

Lemma proof_of_solver_entail_wit_5_1_split_goal_2 : solver_entail_wit_5_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_app_cons. lia.
Qed.

Lemma proof_of_solver_entail_wit_5_1_split_goal_3 : solver_entail_wit_5_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite Zlength_app_cons. lia.
Qed.

Lemma proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_5_1_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_5_2_split_goal_1 : solver_entail_wit_5_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (factor_scan_finish_unit__scan_completion
    n_pre n d ps_2 es_2 PreH1 PreH14) as Hfinish.
  tauto.
Qed.

Lemma proof_of_solver_entail_wit_5_2_split_goal_2 : solver_entail_wit_5_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (factor_scan_finish_unit__scan_completion
    n_pre n d ps_2 es_2 PreH1 PreH14) as Hfinish.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply prefix_maximum_zero__maximum_scan.
Qed.

Lemma proof_of_solver_entail_wit_6 : solver_entail_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_6_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_7_1_split_goal_1 : solver_entail_wit_7_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (i - 0) with i in * by lia.
  unfold PrimeFactorization, PrimeExponentProfile in PreH14.
  destruct PreH14 as (_ & _ & (_ & _ & _ & Hexponents) & _).
  eapply prefix_maximum_step_gt__maximum_scan.
  - exact PreH13.
  - lia.
  - apply Hexponents. lia.
  - lia.
Qed.

Lemma proof_of_solver_entail_wit_7_1 : solver_entail_wit_7_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_7_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_7_2_split_goal_1 : solver_entail_wit_7_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (i - 0) with i in * by lia.
  unfold PrimeFactorization, PrimeExponentProfile in PreH14.
  destruct PreH14 as (_ & _ & (_ & _ & _ & Hexponents) & _).
  eapply prefix_maximum_step_le__maximum_scan.
  - exact PreH13.
  - lia.
  - apply Hexponents. lia.
  - lia.
Qed.

Lemma proof_of_solver_entail_wit_7_2 : solver_entail_wit_7_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_7_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_1 : solver_entail_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (prefix_scan_completion__maximum_scan
       n_pre ps_2 es_2 m i maxe PreH13 PreH6 PreH1 PreH11 PreH9 PreH12)
    as (_ & Hmaximum & Hmx).
  pose proof PreH13 as Hfactor_copy.
  unfold PrimeFactorization in Hfactor_copy.
  destruct Hfactor_copy as (_ & _ & Hprofile & Hfactorpower).
  pose proof (layer_value_le_factor_power__prefix_maximum ps_2 es_2 Hprofile)
    as Hlayer.
  unfold LayerSumPrefix.
  split; [exact PreH13 |].
  split; [exact Hmaximum |].
  split; [lia |].
  split; [reflexivity |].
  split.
  - rewrite Hfactorpower. lia.
  - intros _. rewrite Hfactorpower. simpl. lia.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_2 : solver_entail_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (prefix_scan_completion__maximum_scan
       n_pre ps_2 es_2 m i maxe PreH13 PreH6 PreH1 PreH11 PreH9 PreH12)
    as (_ & Hmaximum & _).
  apply LayerOptimalityCertificate_proved; assumption.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_3 : solver_entail_wit_8_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (prefix_scan_completion__maximum_scan
       n_pre ps_2 es_2 m i maxe PreH13 PreH6 PreH1 PreH11 PreH9 PreH12)
    as (_ & Hmaximum & _).
  exact Hmaximum.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_4 : solver_entail_wit_8_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (prefix_scan_completion__maximum_scan
       n_pre ps_2 es_2 m i maxe PreH13 PreH6 PreH1 PreH11 PreH9 PreH12)
    as (_ & _ & Hmx).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_5 : solver_entail_wit_8_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (prefix_scan_completion__maximum_scan
       n_pre ps_2 es_2 m i maxe PreH13 PreH6 PreH1 PreH11 PreH9 PreH12)
    as (_ & _ & Hmx).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_8_split_goal_6 : solver_entail_wit_8_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof
    (prefix_scan_completion__maximum_scan
       n_pre ps_2 es_2 m i maxe PreH13 PreH6 PreH1 PreH11 PreH9 PreH12)
    as (_ & _ & Hmx).
  lia.
Qed.

Lemma proof_of_solver_entail_wit_8 : solver_entail_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_5.
  - Goal_apply proof_of_solver_entail_wit_8_split_goal_6.
Qed.

Lemma proof_of_solver_entail_wit_9_split_goal_1 : solver_entail_wit_9_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exact (layer_product_prefix_zero__layer_accumulation
    n_pre ps_2 es_2 maxe k total PreH1 PreH16).
Qed.

Lemma proof_of_solver_entail_wit_9 : solver_entail_wit_9.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_9_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_10_1_split_goal_1 : solver_entail_wit_10_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (i - 0) with i in * by lia.
  exact (layer_product_prefix_step_in__layer_accumulation
    n_pre ps_2 es_2 k i prod PreH20 ltac:(lia) ltac:(lia)).
Qed.

Lemma proof_of_solver_entail_wit_10_1 : solver_entail_wit_10_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_10_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_10_2_split_goal_1 : solver_entail_wit_10_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (i - 0) with i in * by lia.
  exact (layer_product_prefix_step_out__layer_accumulation
    n_pre ps_2 es_2 k i prod PreH20 ltac:(lia) ltac:(lia)).
Qed.

Lemma proof_of_solver_entail_wit_10_2 : solver_entail_wit_10_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_10_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_11_split_goal_1 : solver_entail_wit_11_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  eapply layer_sum_prefix_step__layer_accumulation with (upto := i); eauto; lia.
Qed.

Lemma proof_of_solver_entail_wit_11 : solver_entail_wit_11.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_11_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_12 : solver_entail_wit_12.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (layer_sum_completion_answer__final_result
    n_pre ps_2 es_2 maxe k total ltac:(lia) PreH13 PreH16) as Hanswer.
  assert (Hk : k = maxe + 1) by lia.
  rewrite Hk in PreH16.
  Exists es_2 ps_2.
  split_pure_spatial.
  - sep_apply_l_atomic
      (Int64Array.seg_to_undef_seg (&( "pr" )) 0 m ps_2).
    sep_apply_l_atomic
      (Int64Array.undef_seg_merge_to_undef_full (&( "pr" )) 0 m 40).
    + dump_pre_spatial. lia.
    + sep_apply_l_atomic
        (Int64Array.seg_to_undef_seg (&( "ex" )) 0 m es_2).
      sep_apply_l_atomic
        (Int64Array.undef_seg_merge_to_undef_full (&( "ex" )) 0 m 40).
      * dump_pre_spatial. lia.
      * replace (&( "pr" ) + 0 * sizeof(INT64)) with (&( "pr" )) by lia.
        replace (40 - 0) with 40 by lia.
        replace (&( "ex" ) + 0 * sizeof(INT64)) with (&( "ex" )) by lia.
        cancel (Int64Array.undef_full (&( "pr" )) 40).
        cancel (Int64Array.undef_full (&( "ex" )) 40).
  - split_pures.
    all: dump_pre_spatial; try assumption; try lia.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply LayerOptimalityCertificate_spec with
      (ps := ps) (es := es) (mx := maxe).
  - exact PreH10.
  - unfold LayerSumPrefix in PreH11.
    destruct PreH11 as
        [_ [_ [_ [Htotal [_ _]]]]].
    replace (maxe + 1 - 1) with maxe in Htotal by lia.
    exact Htotal.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.
