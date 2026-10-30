From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P082_623B_array_gcd_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P082_623B_array_gcd_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P082_623B_array_gcd_lib.
Local Open Scope sac.

Lemma proof_of_add_factors_entail_wit_1 : add_factors_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists all_2 (@nil Z).
  rewrite Zlength_nil, Z.add_0_r, app_nil_r.
  subst v_pre.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
    apply scan_init__addfac_scan_invariant. lia.
Qed.

Lemma proof_of_add_factors_entail_wit_2 : add_factors_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Left.
  Exists (replace_Znth (k0 + Zlength fs_2) d all_2) (fs_2 ++ [d]).
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  replace (k0 + (Zlength fs_2 + Z.succ 0)) with (k0 + Zlength fs_2 + 1) by lia.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
    + rewrite Zlength_replace_Znth. assumption.
    + rewrite replace_Znth_sublist_append__addfac_scan_invariant by lia.
      rewrite PreH15, app_assoc. reflexivity.
    + apply scan_to_extract__addfac_scan_invariant; try assumption.
      apply (proj1 (rem_zero_iff_divide__addfac_scan_invariant v d ltac:(lia) ltac:(lia))). assumption.
Qed.

Lemma proof_of_add_factors_entail_wit_3_1 : add_factors_entail_wit_3_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Heq : v = d * (v ÷ d)).
  { pose proof (Z.quot_rem v d ltac:(lia)) as Hqr. nia. }
  assert (Hw : 1 <= v ÷ d) by nia.
  assert (Hwv : v ÷ d <= v) by nia.
  destruct PreH16 as [HF [Hsmall [Hd [Hin Hbound]]]].
  assert (HFnew : FactorsSoFar v0 (v ÷ d) fs_2).
  { eapply factors_so_far_quot__addfac_division_residual; eauto. }
  assert (Hsmallnew : forall q, 2 <= q -> q < d -> ~ Z.divide q (v ÷ d)).
  { intros q Hq Hqd Hdiv. apply (Hsmall q Hq Hqd).
    eapply Z.divide_trans; [exact Hdiv |].
    exists d. rewrite Heq at 1. ring. }
  assert (Hpow : 0 <= 2 ^ (Zlength fs_2 - 1)).
  { apply Z.pow_nonneg. lia. }
  assert (HE : AddFactorsExtract v0 (v ÷ d) d fs_2).
  { unfold AddFactorsExtract. split; [exact HFnew |].
    split; [exact Hsmallnew |]. split; [exact Hd |].
    split; [exact Hin |]. nia. }
  assert (HS : AddFactorsScan v0 (v ÷ d) d fs_2).
  { unfold AddFactorsScan. split; [exact HFnew |].
    split; [exact Hsmallnew |].
    eapply doubling_bound_quot__addfac_division_residual; eauto. }
  Right. Exists all_2 fs_2.
  split_pure_spatial; [cancel |].
  split_pures; dump_pre_spatial; first [assumption | lia].
Qed.

Lemma proof_of_add_factors_entail_wit_3_2 : add_factors_entail_wit_3_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Heq : v = d * (v ÷ d)).
  { pose proof (Z.quot_rem v d ltac:(lia)) as Hqr. nia. }
  assert (Hw : 1 <= v ÷ d) by nia.
  assert (Hwv : v ÷ d <= v) by nia.
  destruct PreH16 as [HF [Hsmall [Hd [Hin Hbound]]]].
  assert (HFnew : FactorsSoFar v0 (v ÷ d) fs_2).
  { eapply factors_so_far_quot__addfac_division_residual; eauto. }
  assert (Hsmallnew : forall q, 2 <= q -> q < d -> ~ Z.divide q (v ÷ d)).
  { intros q Hq Hqd Hdiv. apply (Hsmall q Hq Hqd).
    eapply Z.divide_trans; [exact Hdiv |].
    exists d. rewrite Heq at 1. ring. }
  assert (Hpow : 0 <= 2 ^ (Zlength fs_2 - 1)).
  { apply Z.pow_nonneg. lia. }
  assert (HE : AddFactorsExtract v0 (v ÷ d) d fs_2).
  { unfold AddFactorsExtract. split; [exact HFnew |].
    split; [exact Hsmallnew |]. split; [exact Hd |].
    split; [exact Hin |]. nia. }
  assert (HS : AddFactorsScan v0 (v ÷ d) d fs_2).
  { unfold AddFactorsScan. split; [exact HFnew |].
    split; [exact Hsmallnew |].
    eapply doubling_bound_quot__addfac_division_residual; eauto. }
  Right. Exists all_2 fs_2.
  split_pure_spatial; [cancel |].
  split_pures; dump_pre_spatial; first [assumption | lia].
Qed.

Lemma proof_of_add_factors_entail_wit_4 : add_factors_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  destruct PreH15 as [HF [Hsmall Hbound]].
  assert (HR : AddFactorsResidual v0 v fs_2).
  { unfold AddFactorsResidual. split; [exact HF |].
    split; [| exact Hbound].
    eapply residual_is_one_or_prime__addfac_division_residual; eauto. }
  Exists all_2 fs_2.
  split_pure_spatial; [cancel |].
  split_pures; dump_pre_spatial; assumption.
Qed.

Lemma proof_of_add_factors_entail_wit_5_1 : add_factors_entail_wit_5_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists all_2 fs_2.
  assert (Hlen : Zlength fs_2 <= 29).
  { apply (scan_length_bound__addfac_scan_invariant v0 v (Zlength fs_2)); try lia.
    exact (proj2 (proj2 PreH17)). }
  assert (Hdnext : d + 1 <= 31624) by nia.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
    apply scan_step_divisor__addfac_scan_invariant; assumption.
Qed.

Lemma proof_of_add_factors_entail_wit_5_2 : add_factors_entail_wit_5_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists all_2 fs_2.
  assert (Hdnext : d + 1 <= 31624) by nia.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
    apply scan_step_divisor__addfac_scan_invariant; assumption.
Qed.

Lemma proof_of_add_factors_return_wit_1 : add_factors_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists (fs_2 ++ [v]).
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  replace (k0 + (Zlength fs_2 + Z.succ 0)) with (k0 + Zlength fs_2 + 1) by lia.
  rewrite sublist_replace_Znth_snoc__addfac_frame_result by lia.
  rewrite PreH12, app_assoc.
  split_pure_spatial; [repeat progress cancel |].
  split_pures; dump_pre_spatial.
  - apply add_factors_result_append_prime__addfac_frame_result; assumption.
  - lia.
  - lia.
Qed.

Lemma proof_of_add_factors_return_wit_2 : add_factors_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  Exists fs_2. rewrite PreH12.
  split_pure_spatial; [repeat progress cancel |].
  split_pures; dump_pre_spatial.
  - eapply add_factors_result_of_residual_one__addfac_frame_result; eassumption.
  - lia.
  - lia.
Qed.

Lemma proof_of_add_factors_partial_solve_wit_5_pure_split_goal_1 : add_factors_partial_solve_wit_5_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite Zlength_replace_Znth__addfac_frame_result. assumption.
Qed.

Lemma proof_of_add_factors_partial_solve_wit_5_pure : add_factors_partial_solve_wit_5_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_add_factors_partial_solve_wit_5_pure_split_goal_1.
Qed.

Lemma proof_of_add_factors_which_implies_wit_1 : add_factors_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hshape : forall (n : nat) (lo : Z),
    Int64Array.seg_shape primes lo (lo + Z.of_nat n) |--
    EX tail, Int64Array.seg primes lo (lo + Z.of_nat n) tail).
  { induction n as [|n IH]; intros lo.
    - rewrite Z.add_0_r, Int64Array.seg_shape_empty.
      Exists (@nil Z). rewrite Int64Array.seg_empty.
      split_pure_spatial; [repeat progress cancel | dump_pre_spatial; reflexivity].
    - rewrite Int64Array.seg_shape_unfold by lia. Intros a.
      replace (lo + Z.of_nat (S n)) with ((lo + 1) + Z.of_nat n) by lia.
      sep_apply_l_atomic (IH (lo + 1)). Intros tail.
      Exists (a :: tail). rewrite Int64Array.seg_unfold. repeat progress cancel. }
  replace 256 with (k0 + Z.of_nat (Z.to_nat (256 - k0))) at 1 by lia.
  sep_apply_l_atomic (Hshape (Z.to_nat (256 - k0)) k0). Intros tail.
  replace (k0 + Z.of_nat (Z.to_nat (256 - k0))) with 256 by lia.
  prop_apply_p (Int64Array.seg_Zlength primes k0 256 tail). Intros_p Htail.
  Exists (pre ++ tail).
  split_pure_spatial.
  - sep_apply_l_atomic (Int64Array.seg_merge_to_full primes 0 k0 256 pre tail ltac:(lia)).
    rewrite Z.mul_0_l, Z.add_0_r.
    replace (256 - 0) with 256 by lia. repeat progress cancel.
  - split_pures; dump_pre_spatial.
    + rewrite Zlength_app. lia.
    + rewrite <- PreH3. apply sublist_app_exact1.
Qed.

Lemma proof_of_add_factors_which_implies_wit_2_split_goal_spatial : add_factors_which_implies_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_l_atomic (Int64Array.full_split_to_seg primes m 256 all ltac:(lia)).
  sep_apply_l_atomic (Int64Array.seg_to_seg_shape primes m 256 (sublist m 256 all)).
  repeat progress cancel.
Qed.

Lemma proof_of_add_factors_which_implies_wit_2 : add_factors_which_implies_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_add_factors_which_implies_wit_2_split_goal_spatial.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_1_split_goal_1 : cost_for_prime_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  change (CostForPrimeState values a_pre b_pre p_pre 0 0 0 INF INF).
  apply cost_for_prime_state_init__cfp_core_init_elemcost.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_1_split_goal_2 : cost_for_prime_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(auto).
  auto.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_1 : cost_for_prime_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_2_1_split_goal_1 : cost_for_prime_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH10 i ltac:(lia)) as Hvalue.
  destruct (elem_cost_rem_mod__cfp_core_init_elemcost b_pre p_pre (Znth i values 0) ltac:(lia) PreH11) as [Hcost0 [Hcost1 [Hcost2 HcostInf]]].
  symmetry. apply Hcost0; assumption.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_2_1_split_goal_2 : cost_for_prime_entail_wit_2_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(auto).
  auto.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_2_1 : cost_for_prime_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_2_1_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_2_1_split_goal_2.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_2_2_split_goal_1 : cost_for_prime_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH11 i ltac:(lia)) as Hvalue.
  destruct (elem_cost_rem_mod__cfp_core_init_elemcost b_pre p_pre (Znth i values 0) ltac:(lia) PreH12) as [Hcost0 [Hcost1 [Hcost2 HcostInf]]].
  symmetry. apply Hcost1; assumption.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_2_2_split_goal_2 : cost_for_prime_entail_wit_2_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(auto).
  auto.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_2_2 : cost_for_prime_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_2_2_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_2_2_split_goal_2.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_2_3_split_goal_1 : cost_for_prime_entail_wit_2_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH12 i ltac:(lia)) as Hvalue.
  destruct (elem_cost_rem_mod__cfp_core_init_elemcost b_pre p_pre (Znth i values 0) ltac:(lia) PreH13) as [Hcost0 [Hcost1 [Hcost2 HcostInf]]].
  symmetry. apply Hcost2; assumption.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_2_3_split_goal_2 : cost_for_prime_entail_wit_2_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(auto).
  auto.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_2_3 : cost_for_prime_entail_wit_2_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_2_3_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_2_3_split_goal_2.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_2_4_split_goal_1 : cost_for_prime_entail_wit_2_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  pose proof (PreH12 i ltac:(lia)) as Hvalue.
  destruct (elem_cost_rem_mod__cfp_core_init_elemcost b_pre p_pre (Znth i values 0) ltac:(lia) PreH13) as [Hcost0 [Hcost1 [Hcost2 HcostInf]]].
  change (INF = ElemCost b_pre p_pre (Znth i values 0)).
  symmetry. apply HcostInf; assumption.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_2_4_split_goal_2 : cost_for_prime_entail_wit_2_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(auto).
  auto.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_2_4 : cost_for_prime_entail_wit_2_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_2_4_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_2_4_split_goal_2.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_split_goal_1 : cost_for_prime_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: change (Z.shiftl 1 62) with 4611686018427387904 in *.
  all: repeat rewrite Z.min_id.
  all: repeat match goal with
       | |- context [Z.min ?x (Z.max ?x ?y)] =>
           rewrite (Z.min_l x (Z.max x y)) by apply Z.le_max_l
       end.
  all: rewrite Z.min_l by (try apply Z.min_glb; lia).
  all: reflexivity.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3 : cost_for_prime_entail_wit_3.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cost_for_prime_entail_wit_3_split_goal_1.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_4_split_goal_1 : cost_for_prime_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: change (Z.shiftl 1 62) with 4611686018427387904 in *.
  all: repeat rewrite Z.min_id.
  all: repeat match goal with
       | |- context [Z.min ?x (Z.max ?x ?y)] =>
           rewrite (Z.min_l x (Z.max x y)) by apply Z.le_max_l
       end.
  all: rewrite Z.min_l by (try apply Z.min_glb; lia).
  all: reflexivity.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_4 : cost_for_prime_entail_wit_4.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cost_for_prime_entail_wit_4_split_goal_1.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_5_1_split_goal_1 : cost_for_prime_entail_wit_5_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: change (Z.shiftl 1 62) with 4611686018427387904 in *.
  all: repeat rewrite Z.min_id.
  all: repeat match goal with
       | |- context [Z.min ?x (Z.max ?x ?y)] =>
           rewrite (Z.min_l x (Z.max x y)) by apply Z.le_max_l
       end.
  all: rewrite Z.min_l by (try apply Z.min_glb; lia).
  all: reflexivity.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_5_1 : cost_for_prime_entail_wit_5_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cost_for_prime_entail_wit_5_1_split_goal_1.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_5_2_split_goal_1 : cost_for_prime_entail_wit_5_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: change (Z.shiftl 1 62) with 4611686018427387904 in *.
  all: repeat rewrite Z.min_id.
  all: repeat match goal with
       | |- context [Z.min ?x (Z.max ?x ?y)] =>
           rewrite (Z.min_l x (Z.max x y)) by apply Z.le_max_l
       end.
  all: rewrite Z.min_l by (try apply Z.min_glb; lia).
  all: reflexivity.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_5_2 : cost_for_prime_entail_wit_5_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cost_for_prime_entail_wit_5_2_split_goal_1.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_6_split_goal_1 : cost_for_prime_entail_wit_6_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: change (Z.shiftl 1 62) with 4611686018427387904 in *.
  all: repeat rewrite Z.min_id.
  all: repeat match goal with
       | |- context [Z.min ?x (Z.max ?x ?y)] =>
           rewrite (Z.min_l x (Z.max x y)) by apply Z.le_max_l
       end.
  all: rewrite Z.min_l by (try apply Z.min_glb; lia).
  all: reflexivity.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_6 : cost_for_prime_entail_wit_6.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cost_for_prime_entail_wit_6_split_goal_1.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_7_split_goal_1 : cost_for_prime_entail_wit_7_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: change (Z.shiftl 1 62) with 4611686018427387904 in *.
  all: repeat rewrite Z.min_id.
  all: repeat match goal with
       | |- context [Z.min ?x (Z.max ?x ?y)] =>
           rewrite (Z.min_l x (Z.max x y)) by apply Z.le_max_l
       end.
  all: rewrite Z.min_l by (try apply Z.min_glb; lia).
  all: reflexivity.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_7 : cost_for_prime_entail_wit_7.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_cost_for_prime_entail_wit_7_split_goal_1.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_8_split_goal_1 : cost_for_prime_entail_wit_8_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exfalso.
  match goal with
  | HS : CostForPrimeState ?vs ?a ?b ?p ?i ?k ?cf ?ca ?af |- _ =>
    pose proof (cfp_state_cutfresh_bound__cfp_step_08 vs a b p i k cf ca af
      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HS) as HB
  end.
  vm_compute in PreH5. lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_8_split_goal_2 : cost_for_prime_entail_wit_8_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: change (Z.shiftl 1 62) with 4611686018427387904 in *.
  all: repeat match goal with
  | |- context [Z.min ?a ?b] => destruct (Z.min_spec a b) as [[? ->] | [? ->]]
  | |- context [Z.max ?a ?b] => destruct (Z.max_spec a b) as [[? ->] | [? ->]]
  end; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_8_split_goal_3 : cost_for_prime_entail_wit_8_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: change (Z.shiftl 1 62) with 4611686018427387904 in *.
  all: repeat match goal with
  | |- context [Z.min ?a ?b] => destruct (Z.min_spec a b) as [[? ->] | [? ->]]
  | |- context [Z.max ?a ?b] => destruct (Z.max_spec a b) as [[? ->] | [? ->]]
  end; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_8_split_goal_4 : cost_for_prime_entail_wit_8_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: change (Z.shiftl 1 62) with 4611686018427387904 in *.
  all: repeat match goal with
  | |- context [Z.min ?a ?b] => destruct (Z.min_spec a b) as [[? ->] | [? ->]]
  | |- context [Z.max ?a ?b] => destruct (Z.max_spec a b) as [[? ->] | [? ->]]
  end; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_8_split_goal_5 : cost_for_prime_entail_wit_8_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: change (Z.shiftl 1 62) with 4611686018427387904 in *.
  all: repeat match goal with
  | |- context [Z.min ?a ?b] => destruct (Z.min_spec a b) as [[? ->] | [? ->]]
  | |- context [Z.max ?a ?b] => destruct (Z.max_spec a b) as [[? ->] | [? ->]]
  end; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_8_split_goal_6 : cost_for_prime_entail_wit_8_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: change (Z.shiftl 1 62) with 4611686018427387904 in *.
  all: repeat match goal with
  | |- context [Z.min ?a ?b] => destruct (Z.min_spec a b) as [[? ->] | [? ->]]
  | |- context [Z.max ?a ?b] => destruct (Z.max_spec a b) as [[? ->] | [? ->]]
  end; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_8_split_goal_7 : cost_for_prime_entail_wit_8_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: change (Z.shiftl 1 62) with 4611686018427387904 in *.
  all: repeat match goal with
  | |- context [Z.min ?a ?b] => destruct (Z.min_spec a b) as [[? ->] | [? ->]]
  | |- context [Z.max ?a ?b] => destruct (Z.max_spec a b) as [[? ->] | [? ->]]
  end; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_8_split_goal_8 : cost_for_prime_entail_wit_8_split_goal_8.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: change (Z.shiftl 1 62) with 4611686018427387904 in *.
  all: repeat match goal with
  | |- context [Z.min ?a ?b] => destruct (Z.min_spec a b) as [[? ->] | [? ->]]
  | |- context [Z.max ?a ?b] => destruct (Z.max_spec a b) as [[? ->] | [? ->]]
  end; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_8_split_goal_9 : cost_for_prime_entail_wit_8_split_goal_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: change (Z.shiftl 1 62) with 4611686018427387904 in *.
  all: repeat match goal with
  | |- context [Z.min ?a ?b] => destruct (Z.min_spec a b) as [[? ->] | [? ->]]
  | |- context [Z.max ?a ?b] => destruct (Z.max_spec a b) as [[? ->] | [? ->]]
  end; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_8_split_goal_10 : cost_for_prime_entail_wit_8_split_goal_10.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  all: auto.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_8 : cost_for_prime_entail_wit_8.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_8_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_8_split_goal_2.
  - Goal_apply proof_of_cost_for_prime_entail_wit_8_split_goal_3.
  - Goal_apply proof_of_cost_for_prime_entail_wit_8_split_goal_4.
  - Goal_apply proof_of_cost_for_prime_entail_wit_8_split_goal_5.
  - Goal_apply proof_of_cost_for_prime_entail_wit_8_split_goal_6.
  - Goal_apply proof_of_cost_for_prime_entail_wit_8_split_goal_7.
  - Goal_apply proof_of_cost_for_prime_entail_wit_8_split_goal_8.
  - Goal_apply proof_of_cost_for_prime_entail_wit_8_split_goal_9.
  - Goal_apply proof_of_cost_for_prime_entail_wit_8_split_goal_10.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_9 : cost_for_prime_entail_wit_9.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hout : CostForPrime values a_pre b_pre p_pre keep).
  { pose proof (cost_for_prime_exit__cfp_exit_min values a_pre b_pre p_pre i keep cutFresh cutAfterKeep after
      ltac:(lia) ltac:(lia) PreH23) as HE.
    rewrite Z.min_l in HE; [exact HE | destruct (Z.min_spec cutAfterKeep after) as [[? ->] | [? ->]]; lia]. }
  destruct (Z.eq_dec keep INF) as [Heq | Hne].
  - Left. split_pure_spatial; [cancel | split_pures; dump_pre_spatial; unfold INF in *; auto; lia].
  - pose proof (cost_for_prime_bound__cfp_exit_min values a_pre b_pre p_pre keep
      ltac:(lia) ltac:(lia) ltac:(lia) Hout Hne) as HB.
    Right. split_pure_spatial; [cancel | split_pures; dump_pre_spatial; auto; lia].
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  apply candidate_coverage_init__solver_candidate_coverage.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto); try (dump_pre_spatial; reflexivity).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto); try (dump_pre_spatial; assumption).
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_spatial : solver_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_spatial.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply candidate_coverage_extend__solver_candidate_coverage; eassumption.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  repeat rewrite Zlength_app.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply best_prefix_cost_empty__solver_candidate_coverage.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (d = 2) by lia.
  subst d. assumption.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_3 : solver_entail_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  eapply candidate_coverage_Znth__solver_candidate_coverage; eauto; try lia.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_4 : solver_entail_wit_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exact (PreH9 j H).
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_4_1_split_goal_1 : solver_entail_wit_4_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (i - 0) with i in PreH2 by lia.
  eapply best_prefix_cost_step__solver_best_prefix.
  - lia.
  - eassumption.
  - exact PreH2.
  - lia.
Qed.

Lemma proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_4_1_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_4_2_split_goal_1 : solver_entail_wit_4_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  replace (i - 0) with i in PreH2 by lia.
  eapply best_prefix_cost_step__solver_best_prefix.
  - lia.
  - eassumption.
  - exact PreH2.
  - lia.
Qed.

Lemma proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_4_2_split_goal_1.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  apply (best_prefix_gives_spec__solver_spec_final values a_pre b_pre ps best).
  - lia.
  - lia.
  - lia.
  - intros j Hj. destruct (PreH11 j ltac:(lia)). lia.
  - intros j Hj. apply PreH17. lia.
  - rewrite <- PreH10. exact PreH18.
  - replace (Zlength ps) with i by lia. exact PreH21.
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_entail_wit_5_split_goal_1.
Qed.

Lemma proof_of_solver_partial_solve_wit_4_pure_split_goal_1 : solver_partial_solve_wit_4_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  rewrite Zlength_app. lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_4_pure : solver_partial_solve_wit_4_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_4_pure_split_goal_1.
Qed.

Lemma proof_of_solver_partial_solve_wit_6_pure_split_goal_1 : solver_partial_solve_wit_6_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_6_pure : solver_partial_solve_wit_6_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_partial_solve_wit_6_pure_split_goal_1.
Qed.

Lemma proof_of_solver_which_implies_wit_1_split_goal_spatial : solver_which_implies_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply_l_atomic (Int64Array.seg_to_seg_shape primes 0 nprime ps).
  sep_apply_l_atomic (Int64Array.seg_shape_merge_to_full_shape primes 0 nprime 256 ltac:(lia)).
  rewrite Z.mul_0_l, Z.add_0_r.
  replace (256 - 0) with 256 by lia. repeat progress cancel.
Qed.

Lemma proof_of_solver_which_implies_wit_1 : solver_which_implies_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_which_implies_wit_1_split_goal_spatial.
Qed.

