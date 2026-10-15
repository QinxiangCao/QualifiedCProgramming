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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P082_623B_array_gcd_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P082_623B_array_gcd_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P082_623B_array_gcd_lib.
Local Open Scope sac.

Lemma proof_of_add_factors_entail_wit_1 : add_factors_entail_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists all_2 (@nil Z).
  rewrite Zlength_nil.
  replace (k0 + 0) with k0 by lia.
  rewrite app_nil_r.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
    subst v_pre. apply scan_init__addfac_scan_invariant. lia.
Qed. 

Lemma proof_of_add_factors_entail_wit_2 : add_factors_entail_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Left.
  Exists (replace_Znth (k0 + Zlength fs_2) d all_2) (fs_2 ++ (d :: nil)).
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  replace (k0 + (Zlength fs_2 + Z.succ 0)) with (k0 + Zlength fs_2 + 1) by lia.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
    + rewrite Zlength_replace_Znth. exact PreH14.
    + rewrite replace_Znth_sublist_append__addfac_scan_invariant by lia.
      rewrite PreH15, app_assoc. reflexivity.
    + apply scan_to_extract__addfac_scan_invariant; try assumption; try lia.
      apply (proj1 (rem_zero_iff_divide__addfac_scan_invariant v d ltac:(lia) ltac:(lia))).
      exact PreH1.
Qed. 

Lemma proof_of_add_factors_entail_wit_3_1 : add_factors_entail_wit_3_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hd0 : d <> 0) by lia.
  pose proof (Z.quot_rem v d Hd0) as Hqr.
  rewrite PreH1 in Hqr.
  set (w := v ÷ d) in *.
  assert (Hvw : v = d * w) by lia.
  assert (Hw1 : 1 <= w) by nia.
  assert (Hwlev : w <= v) by nia.
  assert (Hwv0 : w <= v0) by lia.
  assert (Hwv : Z.divide w v) by (exists d; lia).
  destruct PreH16 as [HF [Hscan [Hd2 [Hin Hbound]]]].
  assert (HFw : FactorsSoFar v0 w fs_2).
  { apply (factors_so_far_quot__addfac_division_residual v0 v d w fs_2); auto. }
  assert (Hscanw : forall q, 2 <= q -> q < d -> ~ Z.divide q w).
  { intros q Hq1 Hq2 Hqw. apply (Hscan q Hq1 Hq2).
    apply (Z.divide_trans q w v); assumption. }
  assert (Hpow : 0 <= 2 ^ (Zlength fs_2 - 1)) by (apply Z.pow_nonneg; lia).
  assert (Hextract : AddFactorsExtract v0 w d fs_2).
  { split; [ exact HFw | ]. split; [ exact Hscanw | ].
    split; [ lia | ]. split; [ exact Hin | ]. nia. }
  assert (Hscanres : AddFactorsScan v0 w d fs_2).
  { split; [ exact HFw | ]. split; [ exact Hscanw | ].
    apply (doubling_bound_quot__addfac_division_residual
             (Zlength fs_2) v0 v d w); try assumption; lia. }
  Right.
  Exists all_2 fs_2.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; solve [ assumption | lia ].
Qed. 

Lemma proof_of_add_factors_entail_wit_3_2 : add_factors_entail_wit_3_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hd0 : d <> 0) by lia.
  pose proof (Z.quot_rem v d Hd0) as Hqr.
  rewrite PreH1 in Hqr.
  set (w := v ÷ d) in *.
  assert (Hvw : v = d * w) by lia.
  assert (Hw1 : 1 <= w) by nia.
  assert (Hwlev : w <= v) by nia.
  assert (Hwv0 : w <= v0) by lia.
  assert (Hwv : Z.divide w v) by (exists d; lia).
  destruct PreH16 as [HF [Hscan [Hd2 [Hin Hbound]]]].
  assert (HFw : FactorsSoFar v0 w fs_2).
  { apply (factors_so_far_quot__addfac_division_residual v0 v d w fs_2); auto. }
  assert (Hscanw : forall q, 2 <= q -> q < d -> ~ Z.divide q w).
  { intros q Hq1 Hq2 Hqw. apply (Hscan q Hq1 Hq2).
    apply (Z.divide_trans q w v); assumption. }
  assert (Hpow : 0 <= 2 ^ (Zlength fs_2 - 1)) by (apply Z.pow_nonneg; lia).
  assert (Hextract : AddFactorsExtract v0 w d fs_2).
  { split; [ exact HFw | ]. split; [ exact Hscanw | ].
    split; [ lia | ]. split; [ exact Hin | ]. nia. }
  assert (Hscanres : AddFactorsScan v0 w d fs_2).
  { split; [ exact HFw | ]. split; [ exact Hscanw | ].
    apply (doubling_bound_quot__addfac_division_residual
             (Zlength fs_2) v0 v d w); try assumption; lia. }
  Right.
  Exists all_2 fs_2.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; solve [ assumption | lia ].
Qed. 

Lemma proof_of_add_factors_entail_wit_4 : add_factors_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct PreH15 as [HF [Hscan Hbound]].
  assert (Hres : AddFactorsResidual v0 v fs_2).
  { split; [ exact HF | ]. split; [ | exact Hbound ].
    apply (residual_is_one_or_prime__addfac_division_residual v d);
      try assumption; lia. }
  Exists all_2 fs_2.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; solve [ assumption | lia ].
Qed. 

Lemma proof_of_add_factors_entail_wit_5_1 : add_factors_entail_wit_5_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists all_2 fs_2.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
    + destruct PreH17 as [_ [_ Hb]].
      apply (scan_length_bound__addfac_scan_invariant v0 v (Zlength fs_2)); lia.
    + apply scan_step_divisor__addfac_scan_invariant; assumption.
Qed. 

Lemma proof_of_add_factors_entail_wit_5_2 : add_factors_entail_wit_5_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  Exists all_2 fs_2.
  split_pure_spatial.
  - cancel.
  - split_pures; dump_pre_spatial; try lia; try assumption.
    apply scan_step_divisor__addfac_scan_invariant; assumption.
Qed. 

Lemma proof_of_add_factors_return_wit_1 : add_factors_return_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hz : Zlength (fs_2 ++ (cons v nil)) = Zlength fs_2 + 1)
    by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  assert (Hsub : sublist 0 (k0 + Zlength fs_2 + 1)
                   (replace_Znth (k0 + Zlength fs_2) v all)
                 = app pre (fs_2 ++ (cons v nil))).
  { rewrite sublist_replace_Znth_snoc__addfac_frame_result
      by (rewrite PreH11; lia).
    rewrite PreH12.
    rewrite <- app_assoc.
    reflexivity. }
  assert (Hres : AddFactorsResult v0 (fs_2 ++ (cons v nil)))
    by (apply (add_factors_result_append_prime__addfac_frame_result v0 v fs_2);
        [ exact PreH13 | lia | lia ]).
  Exists (fs_2 ++ (cons v nil)).
  rewrite Hz.
  replace (k0 + (Zlength fs_2 + 1)) with (k0 + Zlength fs_2 + 1) by lia.
  rewrite Hsub.
  entailer_with ltac:(lia || nia || int_auto).
Qed. 

Lemma proof_of_add_factors_return_wit_2 : add_factors_return_wit_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hres : AddFactorsResult v0 fs_2)
    by (apply (add_factors_result_of_residual_one__addfac_frame_result v0 v fs_2);
        [ exact PreH13 | lia | lia ]).
  Exists fs_2.
  rewrite PreH12.
  entailer_with ltac:(lia || nia || int_auto).
Qed. 

Lemma proof_of_add_factors_partial_solve_wit_5_pure_split_goal_1 : add_factors_partial_solve_wit_5_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Zlength_replace_Znth.
  lia.
Qed.

Lemma proof_of_add_factors_partial_solve_wit_5_pure : add_factors_partial_solve_wit_5_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_add_factors_partial_solve_wit_5_pure_split_goal_1.
Qed. 

Lemma proof_of_add_factors_which_implies_wit_1 : add_factors_which_implies_wit_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Haux : forall (n : nat) (x lo hi : Z),
            hi - lo = Z.of_nat n ->
            Int64Array.seg_shape x lo hi |-- EX l : list Z, Int64Array.seg x lo hi l).
  { induction n; intros x lo hi Hn.
    - assert (hi = lo) by lia. subst hi.
      rewrite Int64Array.seg_shape_empty.
      Exists (@nil Z).
      rewrite Int64Array.seg_empty.
      entailer_with ltac:(lia || nia || int_auto).
    - rewrite (Int64Array.seg_shape_unfold x lo hi) by lia.
      Intros a.
      sep_apply (IHn x (lo + 1) hi); try lia.
      Intros l.
      Exists (a :: l).
      rewrite (Int64Array.seg_unfold x lo hi l a).
      cancel. }
  sep_apply (Haux (Z.to_nat (256 - k0)) primes k0 256); try lia.
  Intros tail.
  prop_apply (Int64Array.seg_Zlength primes k0 256 tail).
  Intros.
  Exists (app pre tail).
  sep_apply (Int64Array.seg_merge_to_full primes 0 k0 256 pre tail); try lia.
  rewrite Z.mul_0_l, Z.add_0_r, Z.sub_0_r.
  assert (Hs : sublist 0 k0 (app pre tail) = pre).
  { rewrite <- PreH3. apply sublist_app_exact1. }
  assert (Hz : Zlength (app pre tail) = 256).
  { rewrite Zlength_app. lia. }
  rewrite Hs, Hz.
  entailer_with ltac:(lia || nia || int_auto).
Qed. 

Lemma proof_of_add_factors_which_implies_wit_2_split_goal_spatial : add_factors_which_implies_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  sep_apply (Int64Array.full_split_to_seg primes m 256 all); try lia.
  sep_apply (Int64Array.seg_to_seg_shape primes m 256 (sublist m 256 all)).
  cancel.
Qed.

Lemma proof_of_add_factors_which_implies_wit_2 : add_factors_which_implies_wit_2.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_add_factors_which_implies_wit_2_split_goal_spatial.
Qed. 

Lemma proof_of_cost_for_prime_entail_wit_1_split_goal_1 : cost_for_prime_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply cost_for_prime_state_init__cfp_core_init_elemcost.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_1_split_goal_2 : cost_for_prime_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH8; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_1 : cost_for_prime_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_1_split_goal_2.
Qed. 

Lemma proof_of_cost_for_prime_entail_wit_2_1_split_goal_1 : cost_for_prime_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (PreH10 i ltac:(lia)) as [Hlo Hhi].
  pose proof (elem_cost_rem_mod__cfp_core_init_elemcost
                b_pre p_pre (Znth i values 0) Hlo ltac:(lia)) as HE.
  destruct HE as [HE1 [HE2 [HE3 HE4]]].
  symmetry.
  apply HE1; exact PreH1.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_2_1_split_goal_2 : cost_for_prime_entail_wit_2_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH10; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_2_1 : cost_for_prime_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_2_1_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_2_1_split_goal_2.
Qed. 

Lemma proof_of_cost_for_prime_entail_wit_2_2_split_goal_1 : cost_for_prime_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (PreH11 i ltac:(lia)) as [Hlo Hhi].
  pose proof (elem_cost_rem_mod__cfp_core_init_elemcost
                b_pre p_pre (Znth i values 0) Hlo ltac:(lia)) as HE.
  destruct HE as [HE1 [HE2 [HE3 HE4]]].
  symmetry.
  apply HE2; [exact PreH2 | exact PreH1].
Qed.

Lemma proof_of_cost_for_prime_entail_wit_2_2_split_goal_2 : cost_for_prime_entail_wit_2_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH11; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_2_2 : cost_for_prime_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_2_2_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_2_2_split_goal_2.
Qed. 

Lemma proof_of_cost_for_prime_entail_wit_2_3_split_goal_1 : cost_for_prime_entail_wit_2_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (PreH12 i ltac:(lia)) as [Hlo Hhi].
  pose proof (elem_cost_rem_mod__cfp_core_init_elemcost
                b_pre p_pre (Znth i values 0) Hlo ltac:(lia)) as HE.
  destruct HE as [HE1 [HE2 [HE3 HE4]]].
  symmetry.
  apply HE3; [exact PreH3 | exact PreH2 | exact PreH1].
Qed.

Lemma proof_of_cost_for_prime_entail_wit_2_3_split_goal_2 : cost_for_prime_entail_wit_2_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH12; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_2_3 : cost_for_prime_entail_wit_2_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_2_3_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_2_3_split_goal_2.
Qed. 

Lemma proof_of_cost_for_prime_entail_wit_2_4_split_goal_1 : cost_for_prime_entail_wit_2_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (PreH12 i ltac:(lia)) as [Hlo Hhi].
  pose proof (elem_cost_rem_mod__cfp_core_init_elemcost
                b_pre p_pre (Znth i values 0) Hlo ltac:(lia)) as HE.
  destruct HE as [HE1 [HE2 [HE3 HE4]]].
  symmetry.
  apply HE4; [exact PreH3 | exact PreH2 | exact PreH1].
Qed.

Lemma proof_of_cost_for_prime_entail_wit_2_4_split_goal_2 : cost_for_prime_entail_wit_2_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH12; lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_2_4 : cost_for_prime_entail_wit_2_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_2_4_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_2_4_split_goal_2.
Qed. 

Lemma proof_of_cost_for_prime_entail_wit_3_1_split_goal_1 : cost_for_prime_entail_wit_3_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i _ _ _ _ |- _ =>
      pose proof (cfp_state_cut_fresh_finite__cfp_step_06 a d c p i _ _ _ _
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H) as Hcf;
      assert (Hb : i * d <= 1000000000000000) by nia
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_1_split_goal_2 : cost_for_prime_entail_wit_3_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | H : forall x : Z, _ -> (2 <= Znth x _ 0 /\ _) |- _ =>
      first [ apply H; lia | intros ? ?; apply H; lia ]
  end.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_1 : cost_for_prime_entail_wit_3_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_1_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_1_split_goal_2.
Qed. 

Lemma proof_of_cost_for_prime_entail_wit_3_2_split_goal_1 : cost_for_prime_entail_wit_3_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  exfalso.
  match goal with
  | H : CostForPrimeState ?a ?d ?c ?p ?i _ _ _ _ |- _ =>
      pose proof (cfp_state_cut_fresh_finite__cfp_step_06 a d c p i _ _ _ _
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) H) as Hcf;
      assert (Hb : i * d <= 1000000000000000) by nia
  end.
  lia.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_2_split_goal_2 : cost_for_prime_entail_wit_3_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  match goal with
  | H : forall x : Z, _ -> (2 <= Znth x _ 0 /\ _) |- _ =>
      first [ apply H; lia | intros ? ?; apply H; lia ]
  end.
Qed.

Lemma proof_of_cost_for_prime_entail_wit_3_2 : cost_for_prime_entail_wit_3_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_2_split_goal_1.
  - Goal_apply proof_of_cost_for_prime_entail_wit_3_2_split_goal_2.
Qed. 

Lemma proof_of_cost_for_prime_entail_wit_4 : cost_for_prime_entail_wit_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hi : i = Zlength values) by lia.
  pose proof (cost_for_prime_exit__cfp_exit_min values a_pre b_pre p_pre i keep
                cutFresh cutAfterKeep after ltac:(lia) Hi PreH23) as Hcfp.
  replace (Z.min keep (Z.min cutAfterKeep after)) with keep in Hcfp by lia.
  destruct (Z.eq_dec keep 4611686018427387904) as [Heq | Hne].
  - Left.
    split_pure_spatial.
    + cancel (IntArray.full arr_pre n_pre values).
    + split_pures; dump_pre_spatial; first [ exact Hcfp | lia ].
  - assert (Hb : 0 <= keep <= 2000000000000000).
    { apply (cost_for_prime_bound__cfp_exit_min values a_pre b_pre p_pre keep
               ltac:(lia) ltac:(lia) ltac:(lia) Hcfp).
      unfold INF. lia. }
    Right.
    split_pure_spatial.
    + cancel (IntArray.full arr_pre n_pre values).
    + split_pures; dump_pre_spatial; first [ exact Hcfp | lia ].
Qed. 

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial.
  all: apply candidate_coverage_init__solver_candidate_coverage.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial.
  all: apply Zlength_nil.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_3 : solver_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: dump_pre_spatial.
  all: intros j Hj.
  all: apply PreH7.
  all: exact Hj.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_spatial : solver_entail_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: apply Int64Array.full_shape_to_seg_shape.
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
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: apply candidate_coverage_extend__solver_candidate_coverage.
  all: assumption.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: rewrite Zlength_app.
  all: rewrite Zlength_app.
  all: lia.
Qed.

Lemma proof_of_solver_entail_wit_2 : solver_entail_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_2_split_goal_2.
Qed. 

Lemma proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: apply best_prefix_cost_empty__solver_candidate_coverage.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: assert (Hd : d = 2) by lia.
  all: subst d.
  all: exact PreH15.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_3 : solver_entail_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: apply (candidate_coverage_Znth__solver_candidate_coverage _ _ _ _ _ PreH15).
  all: lia.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_4 : solver_entail_wit_3_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  all: apply PreH9.
  all: lia.
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
  LLM_pre_process ltac:(lia || nia || int_auto).
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
  LLM_pre_process ltac:(lia || nia || int_auto).
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
  LLM_pre_process ltac:(lia || nia || int_auto).
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
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  rewrite Zlength_app.
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_4_pure : solver_partial_solve_wit_4_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_partial_solve_wit_4_pure_split_goal_1.
Qed. 

Lemma proof_of_solver_partial_solve_wit_6_pure_split_goal_1 : solver_partial_solve_wit_6_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_6_pure : solver_partial_solve_wit_6_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_partial_solve_wit_6_pure_split_goal_1.
Qed. 

Lemma proof_of_solver_which_implies_wit_1_split_goal_spatial : solver_which_implies_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  sep_apply (Int64Array.seg_to_seg_shape primes 0 nprime ps).
  sep_apply (Int64Array.seg_shape_merge_to_seg_shape primes 0 nprime 256); try lia.
  sep_apply (Int64Array.seg_shape_to_full_shape primes 0 256).
  rewrite Z.mul_0_l, Z.add_0_r.
  replace (256 - 0) with 256 by lia.
  cancel.
Qed.

Lemma proof_of_solver_which_implies_wit_1 : solver_which_implies_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_which_implies_wit_1_split_goal_spatial.
Qed. 

