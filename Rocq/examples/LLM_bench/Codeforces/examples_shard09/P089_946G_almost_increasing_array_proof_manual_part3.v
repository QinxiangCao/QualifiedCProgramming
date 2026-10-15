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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P089_946G_almost_increasing_array_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P089_946G_almost_increasing_array_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P089_946G_almost_increasing_array_lib.
Local Open Scope sac.



Lemma proof_of_solver_entail_wit_12_38 : solver_entail_wit_12_38.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hsi : StrictIncPrefix vals_l_2 nvals) by (destruct PreH53 as [HH _]; exact HH).
  assert (Hci : Znth i c_l_2 0 = KeyAt values i) by (apply PreH50; lia).
  assert (Hci1 : Znth (i - 1) c_l_2 0 = KeyAt values (i - 1)) by (apply PreH50; lia).
  rewrite Hci in PreH31, PreH34. rewrite Hci1 in PreH5.
  assert (HdpL : Zlength (replace_Znth i (0 + 1) dp0_l_2) = n_pre).
  { rewrite Zlength_replace_Znth__dp_body_branches_k4. exact PreH49. }
  assert (Hkeep : forall j, 0 <= j < i ->
            Znth j (replace_Znth i (0 + 1) dp0_l_2) 0 = Znth j dp0_l_2 0).
  { intros j Hj. apply Znth_replace_Znth_Diff; lia. }
  assert (Hnew : Znth i (replace_Znth i (0 + 1) dp0_l_2) 0 = 0 + 1).
  { apply Znth_replace_Znth_Same. lia. }
  assert (Hkeep1 : Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0
                   = Znth (i - 1) dp0_l_2 0) by (apply Hkeep; lia).
  assert (Hbest0 : Best0EndingAt values i (0 + 1)).
  { apply (best0_step_val__dp_body_branches_k4 values vals_l_2 dp0_l_2 m0_2 nvals i
             retval_2 retval_4 (0 + 1));
      [lia | exact PreH53 | exact PreH62 | exact PreH64 | exact PreH34 | exact PreH28 | lia]. }
  assert (Hbest1 : Best1EndingAt values i (retval + 1)).
  { apply (best1_step__dp_body_branches_k4 values vals_l_2 dp0_l_2 m1_2 mX_2 nvals i
             retval_3 retval retval_5 retval);
      [lia | exact PreH53 | exact PreH62 | exact PreH65 | exact PreH66 | exact PreH31
      | exact PreH23 | exact PreH19 | lia]. }
  assert (Hd0b : 0 + 1 <= n_pre).
  { pose proof (best0_value_bound__dp_body_branches_k4 values i (0 + 1) ltac:(lia) Hbest0).
    lia. }
  assert (Hd1b : retval + 1 <= n_pre).
  { pose proof (best1_value_bound__dp_body_branches_k4 values i (retval + 1) ltac:(lia) Hbest1).
    lia. }
  assert (HDP : DP0Prefix values (replace_Znth i (0 + 1) dp0_l_2) (i + 1)).
  { apply (dp0prefix_step__dp_body_branches_k4 values dp0_l_2
             (replace_Znth i (0 + 1) dp0_l_2) i (0 + 1));
      [exact PreH62 | lia | exact Hkeep | exact Hnew | exact Hbest0]. }
  assert (Hdpb : forall k_4, 0 <= k_4 < i + 1 ->
            1 <= Znth k_4 (replace_Znth i (0 + 1) dp0_l_2) 0 <= n_pre).
  { intros k4 Hk4. destruct (Z.eq_dec k4 i) as [He | Hne].
    - subst k4. rewrite Hnew. lia.
    - rewrite (Hkeep k4 ltac:(lia)). apply PreH63. lia. }
  assert (HB0 : Bit0Model values vals_l_2 (replace_Znth i (0 + 1) dp0_l_2)
                  (MaxBitInsert m0_2 retval_2 (0 + 1)) (i + 1) nvals).
  { apply (bit_model_insert__dp_body_branches_k4 values vals_l_2 dp0_l_2
             (replace_Znth i (0 + 1) dp0_l_2) m0_2 nvals i retval_2 (0 + 1));
      [lia | exact Hsi | exact PreH64 | exact PreH34 | exact Hkeep | exact Hnew]. }
  assert (HB1 : Bit1Model values vals_l_2 (MaxBitInsert m1_2 retval_3 (retval + 1))
                  (i + 1) nvals).
  { apply (bit1_model_insert__dp_body_branches_k4 values vals_l_2 m1_2 nvals i retval_3
             (retval + 1));
      [lia | exact Hsi | exact PreH65 | exact PreH31 | exact Hbest1]. }
  assert (HBX : Bit0Model values vals_l_2 (replace_Znth i (0 + 1) dp0_l_2)
                  (MaxBitInsert mX_2 retval_6
                     (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)) (i + 1 - 1) nvals).
  { replace (i + 1 - 1) with (i - 1 + 1) by lia.
    apply (bit_model_insert__dp_body_branches_k4 values vals_l_2 dp0_l_2
             (replace_Znth i (0 + 1) dp0_l_2) mX_2 nvals (i - 1) retval_6
             (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0));
      [lia | exact Hsi | exact PreH66 | exact PreH5 | | reflexivity].
    intros j Hj. apply Hkeep. lia. }
  assert (HCP : ClampedPrefixMax (replace_Znth i (0 + 1) dp0_l_2) (i + 1) (0 + 1)).
  { apply (clamped_step__dp_body_branches_k4 dp0_l_2 (replace_Znth i (0 + 1) dp0_l_2)
             i best0 (0 + 1) (0 + 1));
      [lia | exact PreH67 | exact Hkeep | exact Hnew | lia | lia]. }
  assert (HCB : ClampedBest1Upto values (i + 1) (retval + 1)).
  { apply (clamped_best1_step__dp_body_branches_k4 values i best1 (retval + 1) (retval + 1));
      [lia | exact PreH68 | exact Hbest1 | lia | lia]. }
  assert (HCPp : ClampedPrefixMax (replace_Znth i (0 + 1) dp0_l_2) (i + 1 - 1) best0_prefix).
  { replace (i + 1 - 1) with (i - 1 + 1) by lia.
    apply (clamped_keep_step__dp_body_branches_k4 dp0_l_2 (replace_Znth i (0 + 1) dp0_l_2)
             (i - 1) best0_prefix);
      [lia | exact PreH69 | | exact PreH1].
    intros j Hj. apply Hkeep. lia. }
  assert (Hm0L : Zlength m0_2 = nvals + 1) by (destruct PreH64 as [HH _]; exact HH).
  assert (Hm1L : Zlength m1_2 = nvals + 1) by (destruct PreH65 as [HH _]; exact HH).
  assert (HmXL : Zlength mX_2 = nvals + 1) by (destruct PreH66 as [HH _]; exact HH).
  assert (HmXv : 1 <= Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0 <= n_pre).
  { rewrite Hkeep1. apply PreH63. lia. }
  assert (Hmb : forall r, 0 <= r <= nvals ->
     (((-1000000000 <= Znth r (MaxBitInsert m0_2 retval_2 (0 + 1)) 0 <= n_pre /\
        -1000000000 <= Znth r (MaxBitInsert m1_2 retval_3 (retval + 1)) 0) /\
       Znth r (MaxBitInsert m1_2 retval_3 (retval + 1)) 0 <= n_pre) /\
      -1000000000 <= Znth r (MaxBitInsert mX_2 retval_6
        (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)) 0) /\
     Znth r (MaxBitInsert mX_2 retval_6
        (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)) 0 <= n_pre).
  { intros r Hr.
    pose proof (maxbitinsert_bound__dp_body_branches_k4 m0_2 retval_2 (0 + 1)
                  (-1000000000) n_pre nvals Hm0L ltac:(lia)
                  ltac:(intros q Hq; pose proof (PreH61 q Hq); lia) ltac:(lia) r Hr) as H0.
    pose proof (maxbitinsert_bound__dp_body_branches_k4 m1_2 retval_3 (retval + 1)
                  (-1000000000) n_pre nvals Hm1L ltac:(lia)
                  ltac:(intros q Hq; pose proof (PreH61 q Hq); lia) ltac:(lia) r Hr) as H1.
    pose proof (maxbitinsert_bound__dp_body_branches_k4 mX_2 retval_6
                  (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)
                  (-1000000000) n_pre nvals HmXL ltac:(lia)
                  ltac:(intros q Hq; pose proof (PreH61 q Hq); lia) ltac:(lia) r Hr) as H2.
    lia. }
  assert (Hbb : forall k_3, 0 <= k_3 < nvals + 1 ->
     (((-1000000000 <= Znth k_3 bit_l1 0 <= 1000000000 /\
        -1000000000 <= Znth k_3 bit_l1_2 0) /\
       Znth k_3 bit_l1_2 0 <= 1000000000) /\ -1000000000 <= Znth k_3 bit_l1_3 0) /\
      Znth k_3 bit_l1_3 0 <= 1000000000).
  { intros k3 Hk3. pose proof (PreH14 k3 Hk3). pose proof (PreH10 k3 Hk3).
    pose proof (PreH3 k3 Hk3). lia. }
  Exists (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_3 (retval + 1))
         (MaxBitInsert m0_2 retval_2 (0 + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (0 + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - do 12 cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed.

Lemma proof_of_solver_entail_wit_12_39 : solver_entail_wit_12_39.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hsi : StrictIncPrefix vals_l_2 nvals) by (destruct PreH53 as [HH _]; exact HH).
  assert (Hci : Znth i c_l_2 0 = KeyAt values i) by (apply PreH50; lia).
  assert (Hci1 : Znth (i - 1) c_l_2 0 = KeyAt values (i - 1)) by (apply PreH50; lia).
  rewrite Hci in PreH31, PreH34. rewrite Hci1 in PreH5.
  assert (HdpL : Zlength (replace_Znth i (retval + 1) dp0_l_2) = n_pre).
  { rewrite Zlength_replace_Znth__dp_body_branches_k4. exact PreH49. }
  assert (Hkeep : forall j, 0 <= j < i ->
            Znth j (replace_Znth i (retval + 1) dp0_l_2) 0 = Znth j dp0_l_2 0).
  { intros j Hj. apply Znth_replace_Znth_Diff; lia. }
  assert (Hnew : Znth i (replace_Znth i (retval + 1) dp0_l_2) 0 = retval + 1).
  { apply Znth_replace_Znth_Same. lia. }
  assert (Hkeep1 : Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0
                   = Znth (i - 1) dp0_l_2 0) by (apply Hkeep; lia).
  assert (Hbest0 : Best0EndingAt values i (retval + 1)).
  { apply (best0_step_val__dp_body_branches_k4 values vals_l_2 dp0_l_2 m0_2 nvals i
             retval_2 retval (retval + 1));
      [lia | exact PreH53 | exact PreH62 | exact PreH64 | exact PreH34 | exact PreH28 | lia]. }
  assert (Hbest1 : Best1EndingAt values i (0 + 1)).
  { apply (best1_step__dp_body_branches_k4 values vals_l_2 dp0_l_2 m1_2 mX_2 nvals i
             retval_3 retval_4 retval_5 0);
      [lia | exact PreH53 | exact PreH62 | exact PreH65 | exact PreH66 | exact PreH31
      | exact PreH23 | exact PreH19 | lia]. }
  assert (Hd0b : retval + 1 <= n_pre).
  { pose proof (best0_value_bound__dp_body_branches_k4 values i (retval + 1) ltac:(lia) Hbest0).
    lia. }
  assert (Hd1b : 0 + 1 <= n_pre).
  { pose proof (best1_value_bound__dp_body_branches_k4 values i (0 + 1) ltac:(lia) Hbest1).
    lia. }
  assert (HDP : DP0Prefix values (replace_Znth i (retval + 1) dp0_l_2) (i + 1)).
  { apply (dp0prefix_step__dp_body_branches_k4 values dp0_l_2
             (replace_Znth i (retval + 1) dp0_l_2) i (retval + 1));
      [exact PreH62 | lia | exact Hkeep | exact Hnew | exact Hbest0]. }
  assert (Hdpb : forall k_4, 0 <= k_4 < i + 1 ->
            1 <= Znth k_4 (replace_Znth i (retval + 1) dp0_l_2) 0 <= n_pre).
  { intros k4 Hk4. destruct (Z.eq_dec k4 i) as [He | Hne].
    - subst k4. rewrite Hnew. lia.
    - rewrite (Hkeep k4 ltac:(lia)). apply PreH63. lia. }
  assert (HB0 : Bit0Model values vals_l_2 (replace_Znth i (retval + 1) dp0_l_2)
                  (MaxBitInsert m0_2 retval_2 (retval + 1)) (i + 1) nvals).
  { apply (bit_model_insert__dp_body_branches_k4 values vals_l_2 dp0_l_2
             (replace_Znth i (retval + 1) dp0_l_2) m0_2 nvals i retval_2 (retval + 1));
      [lia | exact Hsi | exact PreH64 | exact PreH34 | exact Hkeep | exact Hnew]. }
  assert (HB1 : Bit1Model values vals_l_2 (MaxBitInsert m1_2 retval_3 (0 + 1))
                  (i + 1) nvals).
  { apply (bit1_model_insert__dp_body_branches_k4 values vals_l_2 m1_2 nvals i retval_3
             (0 + 1));
      [lia | exact Hsi | exact PreH65 | exact PreH31 | exact Hbest1]. }
  assert (HBX : Bit0Model values vals_l_2 (replace_Znth i (retval + 1) dp0_l_2)
                  (MaxBitInsert mX_2 retval_6
                     (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0)) (i + 1 - 1) nvals).
  { replace (i + 1 - 1) with (i - 1 + 1) by lia.
    apply (bit_model_insert__dp_body_branches_k4 values vals_l_2 dp0_l_2
             (replace_Znth i (retval + 1) dp0_l_2) mX_2 nvals (i - 1) retval_6
             (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0));
      [lia | exact Hsi | exact PreH66 | exact PreH5 | | reflexivity].
    intros j Hj. apply Hkeep. lia. }
  assert (HCP : ClampedPrefixMax (replace_Znth i (retval + 1) dp0_l_2) (i + 1) (retval + 1)).
  { apply (clamped_step__dp_body_branches_k4 dp0_l_2 (replace_Znth i (retval + 1) dp0_l_2)
             i best0 (retval + 1) (retval + 1));
      [lia | exact PreH67 | exact Hkeep | exact Hnew | lia | lia]. }
  assert (HCB : ClampedBest1Upto values (i + 1) (0 + 1)).
  { apply (clamped_best1_step__dp_body_branches_k4 values i best1 (0 + 1) (0 + 1));
      [lia | exact PreH68 | exact Hbest1 | lia | lia]. }
  assert (HCPp : ClampedPrefixMax (replace_Znth i (retval + 1) dp0_l_2) (i + 1 - 1) best0_prefix).
  { replace (i + 1 - 1) with (i - 1 + 1) by lia.
    apply (clamped_keep_step__dp_body_branches_k4 dp0_l_2 (replace_Znth i (retval + 1) dp0_l_2)
             (i - 1) best0_prefix);
      [lia | exact PreH69 | | exact PreH1].
    intros j Hj. apply Hkeep. lia. }
  assert (Hm0L : Zlength m0_2 = nvals + 1) by (destruct PreH64 as [HH _]; exact HH).
  assert (Hm1L : Zlength m1_2 = nvals + 1) by (destruct PreH65 as [HH _]; exact HH).
  assert (HmXL : Zlength mX_2 = nvals + 1) by (destruct PreH66 as [HH _]; exact HH).
  assert (HmXv : 1 <= Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0 <= n_pre).
  { rewrite Hkeep1. apply PreH63. lia. }
  assert (Hmb : forall r, 0 <= r <= nvals ->
     (((-1000000000 <= Znth r (MaxBitInsert m0_2 retval_2 (retval + 1)) 0 <= n_pre /\
        -1000000000 <= Znth r (MaxBitInsert m1_2 retval_3 (0 + 1)) 0) /\
       Znth r (MaxBitInsert m1_2 retval_3 (0 + 1)) 0 <= n_pre) /\
      -1000000000 <= Znth r (MaxBitInsert mX_2 retval_6
        (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0)) 0) /\
     Znth r (MaxBitInsert mX_2 retval_6
        (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0)) 0 <= n_pre).
  { intros r Hr.
    pose proof (maxbitinsert_bound__dp_body_branches_k4 m0_2 retval_2 (retval + 1)
                  (-1000000000) n_pre nvals Hm0L ltac:(lia)
                  ltac:(intros q Hq; pose proof (PreH61 q Hq); lia) ltac:(lia) r Hr) as H0.
    pose proof (maxbitinsert_bound__dp_body_branches_k4 m1_2 retval_3 (0 + 1)
                  (-1000000000) n_pre nvals Hm1L ltac:(lia)
                  ltac:(intros q Hq; pose proof (PreH61 q Hq); lia) ltac:(lia) r Hr) as H1.
    pose proof (maxbitinsert_bound__dp_body_branches_k4 mX_2 retval_6
                  (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0)
                  (-1000000000) n_pre nvals HmXL ltac:(lia)
                  ltac:(intros q Hq; pose proof (PreH61 q Hq); lia) ltac:(lia) r Hr) as H2.
    lia. }
  assert (Hbb : forall k_3, 0 <= k_3 < nvals + 1 ->
     (((-1000000000 <= Znth k_3 bit_l1 0 <= 1000000000 /\
        -1000000000 <= Znth k_3 bit_l1_2 0) /\
       Znth k_3 bit_l1_2 0 <= 1000000000) /\ -1000000000 <= Znth k_3 bit_l1_3 0) /\
      Znth k_3 bit_l1_3 0 <= 1000000000).
  { intros k3 Hk3. pose proof (PreH14 k3 Hk3). pose proof (PreH10 k3 Hk3).
    pose proof (PreH3 k3 Hk3). lia. }
  Exists (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_3 (0 + 1))
         (MaxBitInsert m0_2 retval_2 (retval + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (retval + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - do 12 cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed.

Lemma proof_of_solver_entail_wit_12_40 : solver_entail_wit_12_40.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hsi : StrictIncPrefix vals_l_2 nvals) by (destruct PreH53 as [HH _]; exact HH).
  assert (Hci : Znth i c_l_2 0 = KeyAt values i) by (apply PreH50; lia).
  assert (Hci1 : Znth (i - 1) c_l_2 0 = KeyAt values (i - 1)) by (apply PreH50; lia).
  rewrite Hci in PreH31, PreH34. rewrite Hci1 in PreH5.
  assert (HdpL : Zlength (replace_Znth i (0 + 1) dp0_l_2) = n_pre).
  { rewrite Zlength_replace_Znth__dp_body_branches_k4. exact PreH49. }
  assert (Hkeep : forall j, 0 <= j < i ->
            Znth j (replace_Znth i (0 + 1) dp0_l_2) 0 = Znth j dp0_l_2 0).
  { intros j Hj. apply Znth_replace_Znth_Diff; lia. }
  assert (Hnew : Znth i (replace_Znth i (0 + 1) dp0_l_2) 0 = 0 + 1).
  { apply Znth_replace_Znth_Same. lia. }
  assert (Hkeep1 : Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0
                   = Znth (i - 1) dp0_l_2 0) by (apply Hkeep; lia).
  assert (Hbest0 : Best0EndingAt values i (0 + 1)).
  { apply (best0_step_val__dp_body_branches_k4 values vals_l_2 dp0_l_2 m0_2 nvals i
             retval retval_3 (0 + 1));
      [lia | exact PreH53 | exact PreH62 | exact PreH64 | exact PreH34 | exact PreH28 | lia]. }
  assert (Hbest1 : Best1EndingAt values i (0 + 1)).
  { apply (best1_step__dp_body_branches_k4 values vals_l_2 dp0_l_2 m1_2 mX_2 nvals i
             retval_2 retval_4 retval_5 0);
      [lia | exact PreH53 | exact PreH62 | exact PreH65 | exact PreH66 | exact PreH31
      | exact PreH23 | exact PreH19 | lia]. }
  assert (Hd0b : 0 + 1 <= n_pre).
  { pose proof (best0_value_bound__dp_body_branches_k4 values i (0 + 1) ltac:(lia) Hbest0).
    lia. }
  assert (Hd1b : 0 + 1 <= n_pre).
  { pose proof (best1_value_bound__dp_body_branches_k4 values i (0 + 1) ltac:(lia) Hbest1).
    lia. }
  assert (HDP : DP0Prefix values (replace_Znth i (0 + 1) dp0_l_2) (i + 1)).
  { apply (dp0prefix_step__dp_body_branches_k4 values dp0_l_2
             (replace_Znth i (0 + 1) dp0_l_2) i (0 + 1));
      [exact PreH62 | lia | exact Hkeep | exact Hnew | exact Hbest0]. }
  assert (Hdpb : forall k_4, 0 <= k_4 < i + 1 ->
            1 <= Znth k_4 (replace_Znth i (0 + 1) dp0_l_2) 0 <= n_pre).
  { intros k4 Hk4. destruct (Z.eq_dec k4 i) as [He | Hne].
    - subst k4. rewrite Hnew. lia.
    - rewrite (Hkeep k4 ltac:(lia)). apply PreH63. lia. }
  assert (HB0 : Bit0Model values vals_l_2 (replace_Znth i (0 + 1) dp0_l_2)
                  (MaxBitInsert m0_2 retval (0 + 1)) (i + 1) nvals).
  { apply (bit_model_insert__dp_body_branches_k4 values vals_l_2 dp0_l_2
             (replace_Znth i (0 + 1) dp0_l_2) m0_2 nvals i retval (0 + 1));
      [lia | exact Hsi | exact PreH64 | exact PreH34 | exact Hkeep | exact Hnew]. }
  assert (HB1 : Bit1Model values vals_l_2 (MaxBitInsert m1_2 retval_2 (0 + 1))
                  (i + 1) nvals).
  { apply (bit1_model_insert__dp_body_branches_k4 values vals_l_2 m1_2 nvals i retval_2
             (0 + 1));
      [lia | exact Hsi | exact PreH65 | exact PreH31 | exact Hbest1]. }
  assert (HBX : Bit0Model values vals_l_2 (replace_Znth i (0 + 1) dp0_l_2)
                  (MaxBitInsert mX_2 retval_6
                     (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)) (i + 1 - 1) nvals).
  { replace (i + 1 - 1) with (i - 1 + 1) by lia.
    apply (bit_model_insert__dp_body_branches_k4 values vals_l_2 dp0_l_2
             (replace_Znth i (0 + 1) dp0_l_2) mX_2 nvals (i - 1) retval_6
             (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0));
      [lia | exact Hsi | exact PreH66 | exact PreH5 | | reflexivity].
    intros j Hj. apply Hkeep. lia. }
  assert (HCP : ClampedPrefixMax (replace_Znth i (0 + 1) dp0_l_2) (i + 1) (0 + 1)).
  { apply (clamped_step__dp_body_branches_k4 dp0_l_2 (replace_Znth i (0 + 1) dp0_l_2)
             i best0 (0 + 1) (0 + 1));
      [lia | exact PreH67 | exact Hkeep | exact Hnew | lia | lia]. }
  assert (HCB : ClampedBest1Upto values (i + 1) (0 + 1)).
  { apply (clamped_best1_step__dp_body_branches_k4 values i best1 (0 + 1) (0 + 1));
      [lia | exact PreH68 | exact Hbest1 | lia | lia]. }
  assert (HCPp : ClampedPrefixMax (replace_Znth i (0 + 1) dp0_l_2) (i + 1 - 1) best0_prefix).
  { replace (i + 1 - 1) with (i - 1 + 1) by lia.
    apply (clamped_keep_step__dp_body_branches_k4 dp0_l_2 (replace_Znth i (0 + 1) dp0_l_2)
             (i - 1) best0_prefix);
      [lia | exact PreH69 | | exact PreH1].
    intros j Hj. apply Hkeep. lia. }
  assert (Hm0L : Zlength m0_2 = nvals + 1) by (destruct PreH64 as [HH _]; exact HH).
  assert (Hm1L : Zlength m1_2 = nvals + 1) by (destruct PreH65 as [HH _]; exact HH).
  assert (HmXL : Zlength mX_2 = nvals + 1) by (destruct PreH66 as [HH _]; exact HH).
  assert (HmXv : 1 <= Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0 <= n_pre).
  { rewrite Hkeep1. apply PreH63. lia. }
  assert (Hmb : forall r, 0 <= r <= nvals ->
     (((-1000000000 <= Znth r (MaxBitInsert m0_2 retval (0 + 1)) 0 <= n_pre /\
        -1000000000 <= Znth r (MaxBitInsert m1_2 retval_2 (0 + 1)) 0) /\
       Znth r (MaxBitInsert m1_2 retval_2 (0 + 1)) 0 <= n_pre) /\
      -1000000000 <= Znth r (MaxBitInsert mX_2 retval_6
        (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)) 0) /\
     Znth r (MaxBitInsert mX_2 retval_6
        (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)) 0 <= n_pre).
  { intros r Hr.
    pose proof (maxbitinsert_bound__dp_body_branches_k4 m0_2 retval (0 + 1)
                  (-1000000000) n_pre nvals Hm0L ltac:(lia)
                  ltac:(intros q Hq; pose proof (PreH61 q Hq); lia) ltac:(lia) r Hr) as H0.
    pose proof (maxbitinsert_bound__dp_body_branches_k4 m1_2 retval_2 (0 + 1)
                  (-1000000000) n_pre nvals Hm1L ltac:(lia)
                  ltac:(intros q Hq; pose proof (PreH61 q Hq); lia) ltac:(lia) r Hr) as H1.
    pose proof (maxbitinsert_bound__dp_body_branches_k4 mX_2 retval_6
                  (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)
                  (-1000000000) n_pre nvals HmXL ltac:(lia)
                  ltac:(intros q Hq; pose proof (PreH61 q Hq); lia) ltac:(lia) r Hr) as H2.
    lia. }
  assert (Hbb : forall k_3, 0 <= k_3 < nvals + 1 ->
     (((-1000000000 <= Znth k_3 bit_l1 0 <= 1000000000 /\
        -1000000000 <= Znth k_3 bit_l1_2 0) /\
       Znth k_3 bit_l1_2 0 <= 1000000000) /\ -1000000000 <= Znth k_3 bit_l1_3 0) /\
      Znth k_3 bit_l1_3 0 <= 1000000000).
  { intros k3 Hk3. pose proof (PreH14 k3 Hk3). pose proof (PreH10 k3 Hk3).
    pose proof (PreH3 k3 Hk3). lia. }
  Exists (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_2 (0 + 1))
         (MaxBitInsert m0_2 retval (0 + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (0 + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - do 12 cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed.

Lemma proof_of_solver_entail_wit_12_41 : solver_entail_wit_12_41.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hsi : StrictIncPrefix vals_l_2 nvals) by (destruct PreH53 as [HH _]; exact HH).
  assert (Hci : Znth i c_l_2 0 = KeyAt values i) by (apply PreH50; lia).
  assert (Hci1 : Znth (i - 1) c_l_2 0 = KeyAt values (i - 1)) by (apply PreH50; lia).
  rewrite Hci in PreH31, PreH34. rewrite Hci1 in PreH5.
  assert (HdpL : Zlength (replace_Znth i (retval_4 + 1) dp0_l_2) = n_pre).
  { rewrite Zlength_replace_Znth__dp_body_branches_k4. exact PreH49. }
  assert (Hkeep : forall j, 0 <= j < i ->
            Znth j (replace_Znth i (retval_4 + 1) dp0_l_2) 0 = Znth j dp0_l_2 0).
  { intros j Hj. apply Znth_replace_Znth_Diff; lia. }
  assert (Hnew : Znth i (replace_Znth i (retval_4 + 1) dp0_l_2) 0 = retval_4 + 1).
  { apply Znth_replace_Znth_Same. lia. }
  assert (Hkeep1 : Znth (i - 1) (replace_Znth i (retval_4 + 1) dp0_l_2) 0
                   = Znth (i - 1) dp0_l_2 0) by (apply Hkeep; lia).
  assert (Hbest0 : Best0EndingAt values i (retval_4 + 1)).
  { apply (best0_step_val__dp_body_branches_k4 values vals_l_2 dp0_l_2 m0_2 nvals i
             retval_2 retval_4 (retval_4 + 1));
      [lia | exact PreH53 | exact PreH62 | exact PreH64 | exact PreH34 | exact PreH28 | lia]. }
  assert (Hbest1 : Best1EndingAt values i (retval + 1)).
  { apply (best1_step__dp_body_branches_k4 values vals_l_2 dp0_l_2 m1_2 mX_2 nvals i
             retval_3 retval_5 retval retval);
      [lia | exact PreH53 | exact PreH62 | exact PreH65 | exact PreH66 | exact PreH31
      | exact PreH23 | exact PreH19 | lia]. }
  assert (Hd0b : retval_4 + 1 <= n_pre).
  { pose proof (best0_value_bound__dp_body_branches_k4 values i (retval_4 + 1) ltac:(lia) Hbest0).
    lia. }
  assert (Hd1b : retval + 1 <= n_pre).
  { pose proof (best1_value_bound__dp_body_branches_k4 values i (retval + 1) ltac:(lia) Hbest1).
    lia. }
  assert (HDP : DP0Prefix values (replace_Znth i (retval_4 + 1) dp0_l_2) (i + 1)).
  { apply (dp0prefix_step__dp_body_branches_k4 values dp0_l_2
             (replace_Znth i (retval_4 + 1) dp0_l_2) i (retval_4 + 1));
      [exact PreH62 | lia | exact Hkeep | exact Hnew | exact Hbest0]. }
  assert (Hdpb : forall k_4, 0 <= k_4 < i + 1 ->
            1 <= Znth k_4 (replace_Znth i (retval_4 + 1) dp0_l_2) 0 <= n_pre).
  { intros k4 Hk4. destruct (Z.eq_dec k4 i) as [He | Hne].
    - subst k4. rewrite Hnew. lia.
    - rewrite (Hkeep k4 ltac:(lia)). apply PreH63. lia. }
  assert (HB0 : Bit0Model values vals_l_2 (replace_Znth i (retval_4 + 1) dp0_l_2)
                  (MaxBitInsert m0_2 retval_2 (retval_4 + 1)) (i + 1) nvals).
  { apply (bit_model_insert__dp_body_branches_k4 values vals_l_2 dp0_l_2
             (replace_Znth i (retval_4 + 1) dp0_l_2) m0_2 nvals i retval_2 (retval_4 + 1));
      [lia | exact Hsi | exact PreH64 | exact PreH34 | exact Hkeep | exact Hnew]. }
  assert (HB1 : Bit1Model values vals_l_2 (MaxBitInsert m1_2 retval_3 (retval + 1))
                  (i + 1) nvals).
  { apply (bit1_model_insert__dp_body_branches_k4 values vals_l_2 m1_2 nvals i retval_3
             (retval + 1));
      [lia | exact Hsi | exact PreH65 | exact PreH31 | exact Hbest1]. }
  assert (HBX : Bit0Model values vals_l_2 (replace_Znth i (retval_4 + 1) dp0_l_2)
                  (MaxBitInsert mX_2 retval_6
                     (Znth (i - 1) (replace_Znth i (retval_4 + 1) dp0_l_2) 0)) (i + 1 - 1) nvals).
  { replace (i + 1 - 1) with (i - 1 + 1) by lia.
    apply (bit_model_insert__dp_body_branches_k4 values vals_l_2 dp0_l_2
             (replace_Znth i (retval_4 + 1) dp0_l_2) mX_2 nvals (i - 1) retval_6
             (Znth (i - 1) (replace_Znth i (retval_4 + 1) dp0_l_2) 0));
      [lia | exact Hsi | exact PreH66 | exact PreH5 | | reflexivity].
    intros j Hj. apply Hkeep. lia. }
  assert (HCP : ClampedPrefixMax (replace_Znth i (retval_4 + 1) dp0_l_2) (i + 1) best0).
  { apply (clamped_step__dp_body_branches_k4 dp0_l_2 (replace_Znth i (retval_4 + 1) dp0_l_2)
             i best0 (retval_4 + 1) best0);
      [lia | exact PreH67 | exact Hkeep | exact Hnew | lia | lia]. }
  assert (HCB : ClampedBest1Upto values (i + 1) (retval + 1)).
  { apply (clamped_best1_step__dp_body_branches_k4 values i best1 (retval + 1) (retval + 1));
      [lia | exact PreH68 | exact Hbest1 | lia | lia]. }
  assert (HCPp : ClampedPrefixMax (replace_Znth i (retval_4 + 1) dp0_l_2) (i + 1 - 1) best0_prefix).
  { replace (i + 1 - 1) with (i - 1 + 1) by lia.
    apply (clamped_keep_step__dp_body_branches_k4 dp0_l_2 (replace_Znth i (retval_4 + 1) dp0_l_2)
             (i - 1) best0_prefix);
      [lia | exact PreH69 | | exact PreH1].
    intros j Hj. apply Hkeep. lia. }
  assert (Hm0L : Zlength m0_2 = nvals + 1) by (destruct PreH64 as [HH _]; exact HH).
  assert (Hm1L : Zlength m1_2 = nvals + 1) by (destruct PreH65 as [HH _]; exact HH).
  assert (HmXL : Zlength mX_2 = nvals + 1) by (destruct PreH66 as [HH _]; exact HH).
  assert (HmXv : 1 <= Znth (i - 1) (replace_Znth i (retval_4 + 1) dp0_l_2) 0 <= n_pre).
  { rewrite Hkeep1. apply PreH63. lia. }
  assert (Hmb : forall r, 0 <= r <= nvals ->
     (((-1000000000 <= Znth r (MaxBitInsert m0_2 retval_2 (retval_4 + 1)) 0 <= n_pre /\
        -1000000000 <= Znth r (MaxBitInsert m1_2 retval_3 (retval + 1)) 0) /\
       Znth r (MaxBitInsert m1_2 retval_3 (retval + 1)) 0 <= n_pre) /\
      -1000000000 <= Znth r (MaxBitInsert mX_2 retval_6
        (Znth (i - 1) (replace_Znth i (retval_4 + 1) dp0_l_2) 0)) 0) /\
     Znth r (MaxBitInsert mX_2 retval_6
        (Znth (i - 1) (replace_Znth i (retval_4 + 1) dp0_l_2) 0)) 0 <= n_pre).
  { intros r Hr.
    pose proof (maxbitinsert_bound__dp_body_branches_k4 m0_2 retval_2 (retval_4 + 1)
                  (-1000000000) n_pre nvals Hm0L ltac:(lia)
                  ltac:(intros q Hq; pose proof (PreH61 q Hq); lia) ltac:(lia) r Hr) as H0.
    pose proof (maxbitinsert_bound__dp_body_branches_k4 m1_2 retval_3 (retval + 1)
                  (-1000000000) n_pre nvals Hm1L ltac:(lia)
                  ltac:(intros q Hq; pose proof (PreH61 q Hq); lia) ltac:(lia) r Hr) as H1.
    pose proof (maxbitinsert_bound__dp_body_branches_k4 mX_2 retval_6
                  (Znth (i - 1) (replace_Znth i (retval_4 + 1) dp0_l_2) 0)
                  (-1000000000) n_pre nvals HmXL ltac:(lia)
                  ltac:(intros q Hq; pose proof (PreH61 q Hq); lia) ltac:(lia) r Hr) as H2.
    lia. }
  assert (Hbb : forall k_3, 0 <= k_3 < nvals + 1 ->
     (((-1000000000 <= Znth k_3 bit_l1 0 <= 1000000000 /\
        -1000000000 <= Znth k_3 bit_l1_2 0) /\
       Znth k_3 bit_l1_2 0 <= 1000000000) /\ -1000000000 <= Znth k_3 bit_l1_3 0) /\
      Znth k_3 bit_l1_3 0 <= 1000000000).
  { intros k3 Hk3. pose proof (PreH14 k3 Hk3). pose proof (PreH10 k3 Hk3).
    pose proof (PreH3 k3 Hk3). lia. }
  Exists (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (retval_4 + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_3 (retval + 1))
         (MaxBitInsert m0_2 retval_2 (retval_4 + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (retval_4 + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - do 12 cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed.

Lemma proof_of_solver_entail_wit_12_42 : solver_entail_wit_12_42.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hsi : StrictIncPrefix vals_l_2 nvals) by (destruct PreH53 as [HH _]; exact HH).
  assert (Hci : Znth i c_l_2 0 = KeyAt values i) by (apply PreH50; lia).
  assert (Hci1 : Znth (i - 1) c_l_2 0 = KeyAt values (i - 1)) by (apply PreH50; lia).
  rewrite Hci in PreH31, PreH34. rewrite Hci1 in PreH5.
  assert (HdpL : Zlength (replace_Znth i (0 + 1) dp0_l_2) = n_pre).
  { rewrite Zlength_replace_Znth__dp_body_branches_k4. exact PreH49. }
  assert (Hkeep : forall j, 0 <= j < i ->
            Znth j (replace_Znth i (0 + 1) dp0_l_2) 0 = Znth j dp0_l_2 0).
  { intros j Hj. apply Znth_replace_Znth_Diff; lia. }
  assert (Hnew : Znth i (replace_Znth i (0 + 1) dp0_l_2) 0 = 0 + 1).
  { apply Znth_replace_Znth_Same. lia. }
  assert (Hkeep1 : Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0
                   = Znth (i - 1) dp0_l_2 0) by (apply Hkeep; lia).
  assert (Hbest0 : Best0EndingAt values i (0 + 1)).
  { apply (best0_step_val__dp_body_branches_k4 values vals_l_2 dp0_l_2 m0_2 nvals i
             retval_2 retval_4 (0 + 1));
      [lia | exact PreH53 | exact PreH62 | exact PreH64 | exact PreH34 | exact PreH28 | lia]. }
  assert (Hbest1 : Best1EndingAt values i (retval + 1)).
  { apply (best1_step__dp_body_branches_k4 values vals_l_2 dp0_l_2 m1_2 mX_2 nvals i
             retval_3 retval_5 retval retval);
      [lia | exact PreH53 | exact PreH62 | exact PreH65 | exact PreH66 | exact PreH31
      | exact PreH23 | exact PreH19 | lia]. }
  assert (Hd0b : 0 + 1 <= n_pre).
  { pose proof (best0_value_bound__dp_body_branches_k4 values i (0 + 1) ltac:(lia) Hbest0).
    lia. }
  assert (Hd1b : retval + 1 <= n_pre).
  { pose proof (best1_value_bound__dp_body_branches_k4 values i (retval + 1) ltac:(lia) Hbest1).
    lia. }
  assert (HDP : DP0Prefix values (replace_Znth i (0 + 1) dp0_l_2) (i + 1)).
  { apply (dp0prefix_step__dp_body_branches_k4 values dp0_l_2
             (replace_Znth i (0 + 1) dp0_l_2) i (0 + 1));
      [exact PreH62 | lia | exact Hkeep | exact Hnew | exact Hbest0]. }
  assert (Hdpb : forall k_4, 0 <= k_4 < i + 1 ->
            1 <= Znth k_4 (replace_Znth i (0 + 1) dp0_l_2) 0 <= n_pre).
  { intros k4 Hk4. destruct (Z.eq_dec k4 i) as [He | Hne].
    - subst k4. rewrite Hnew. lia.
    - rewrite (Hkeep k4 ltac:(lia)). apply PreH63. lia. }
  assert (HB0 : Bit0Model values vals_l_2 (replace_Znth i (0 + 1) dp0_l_2)
                  (MaxBitInsert m0_2 retval_2 (0 + 1)) (i + 1) nvals).
  { apply (bit_model_insert__dp_body_branches_k4 values vals_l_2 dp0_l_2
             (replace_Znth i (0 + 1) dp0_l_2) m0_2 nvals i retval_2 (0 + 1));
      [lia | exact Hsi | exact PreH64 | exact PreH34 | exact Hkeep | exact Hnew]. }
  assert (HB1 : Bit1Model values vals_l_2 (MaxBitInsert m1_2 retval_3 (retval + 1))
                  (i + 1) nvals).
  { apply (bit1_model_insert__dp_body_branches_k4 values vals_l_2 m1_2 nvals i retval_3
             (retval + 1));
      [lia | exact Hsi | exact PreH65 | exact PreH31 | exact Hbest1]. }
  assert (HBX : Bit0Model values vals_l_2 (replace_Znth i (0 + 1) dp0_l_2)
                  (MaxBitInsert mX_2 retval_6
                     (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)) (i + 1 - 1) nvals).
  { replace (i + 1 - 1) with (i - 1 + 1) by lia.
    apply (bit_model_insert__dp_body_branches_k4 values vals_l_2 dp0_l_2
             (replace_Znth i (0 + 1) dp0_l_2) mX_2 nvals (i - 1) retval_6
             (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0));
      [lia | exact Hsi | exact PreH66 | exact PreH5 | | reflexivity].
    intros j Hj. apply Hkeep. lia. }
  assert (HCP : ClampedPrefixMax (replace_Znth i (0 + 1) dp0_l_2) (i + 1) best0).
  { apply (clamped_step__dp_body_branches_k4 dp0_l_2 (replace_Znth i (0 + 1) dp0_l_2)
             i best0 (0 + 1) best0);
      [lia | exact PreH67 | exact Hkeep | exact Hnew | lia | lia]. }
  assert (HCB : ClampedBest1Upto values (i + 1) (retval + 1)).
  { apply (clamped_best1_step__dp_body_branches_k4 values i best1 (retval + 1) (retval + 1));
      [lia | exact PreH68 | exact Hbest1 | lia | lia]. }
  assert (HCPp : ClampedPrefixMax (replace_Znth i (0 + 1) dp0_l_2) (i + 1 - 1) best0_prefix).
  { replace (i + 1 - 1) with (i - 1 + 1) by lia.
    apply (clamped_keep_step__dp_body_branches_k4 dp0_l_2 (replace_Znth i (0 + 1) dp0_l_2)
             (i - 1) best0_prefix);
      [lia | exact PreH69 | | exact PreH1].
    intros j Hj. apply Hkeep. lia. }
  assert (Hm0L : Zlength m0_2 = nvals + 1) by (destruct PreH64 as [HH _]; exact HH).
  assert (Hm1L : Zlength m1_2 = nvals + 1) by (destruct PreH65 as [HH _]; exact HH).
  assert (HmXL : Zlength mX_2 = nvals + 1) by (destruct PreH66 as [HH _]; exact HH).
  assert (HmXv : 1 <= Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0 <= n_pre).
  { rewrite Hkeep1. apply PreH63. lia. }
  assert (Hmb : forall r, 0 <= r <= nvals ->
     (((-1000000000 <= Znth r (MaxBitInsert m0_2 retval_2 (0 + 1)) 0 <= n_pre /\
        -1000000000 <= Znth r (MaxBitInsert m1_2 retval_3 (retval + 1)) 0) /\
       Znth r (MaxBitInsert m1_2 retval_3 (retval + 1)) 0 <= n_pre) /\
      -1000000000 <= Znth r (MaxBitInsert mX_2 retval_6
        (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)) 0) /\
     Znth r (MaxBitInsert mX_2 retval_6
        (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)) 0 <= n_pre).
  { intros r Hr.
    pose proof (maxbitinsert_bound__dp_body_branches_k4 m0_2 retval_2 (0 + 1)
                  (-1000000000) n_pre nvals Hm0L ltac:(lia)
                  ltac:(intros q Hq; pose proof (PreH61 q Hq); lia) ltac:(lia) r Hr) as H0.
    pose proof (maxbitinsert_bound__dp_body_branches_k4 m1_2 retval_3 (retval + 1)
                  (-1000000000) n_pre nvals Hm1L ltac:(lia)
                  ltac:(intros q Hq; pose proof (PreH61 q Hq); lia) ltac:(lia) r Hr) as H1.
    pose proof (maxbitinsert_bound__dp_body_branches_k4 mX_2 retval_6
                  (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)
                  (-1000000000) n_pre nvals HmXL ltac:(lia)
                  ltac:(intros q Hq; pose proof (PreH61 q Hq); lia) ltac:(lia) r Hr) as H2.
    lia. }
  assert (Hbb : forall k_3, 0 <= k_3 < nvals + 1 ->
     (((-1000000000 <= Znth k_3 bit_l1 0 <= 1000000000 /\
        -1000000000 <= Znth k_3 bit_l1_2 0) /\
       Znth k_3 bit_l1_2 0 <= 1000000000) /\ -1000000000 <= Znth k_3 bit_l1_3 0) /\
      Znth k_3 bit_l1_3 0 <= 1000000000).
  { intros k3 Hk3. pose proof (PreH14 k3 Hk3). pose proof (PreH10 k3 Hk3).
    pose proof (PreH3 k3 Hk3). lia. }
  Exists (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_3 (retval + 1))
         (MaxBitInsert m0_2 retval_2 (0 + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (0 + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - do 12 cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed.

Lemma proof_of_solver_entail_wit_12_43 : solver_entail_wit_12_43.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hsi : StrictIncPrefix vals_l_2 nvals) by (destruct PreH53 as [HH _]; exact HH).
  assert (Hci : Znth i c_l_2 0 = KeyAt values i) by (apply PreH50; lia).
  assert (Hci1 : Znth (i - 1) c_l_2 0 = KeyAt values (i - 1)) by (apply PreH50; lia).
  rewrite Hci in PreH31, PreH34. rewrite Hci1 in PreH5.
  assert (HdpL : Zlength (replace_Znth i (retval_4 + 1) dp0_l_2) = n_pre).
  { rewrite Zlength_replace_Znth__dp_body_branches_k4. exact PreH49. }
  assert (Hkeep : forall j, 0 <= j < i ->
            Znth j (replace_Znth i (retval_4 + 1) dp0_l_2) 0 = Znth j dp0_l_2 0).
  { intros j Hj. apply Znth_replace_Znth_Diff; lia. }
  assert (Hnew : Znth i (replace_Znth i (retval_4 + 1) dp0_l_2) 0 = retval_4 + 1).
  { apply Znth_replace_Znth_Same. lia. }
  assert (Hkeep1 : Znth (i - 1) (replace_Znth i (retval_4 + 1) dp0_l_2) 0
                   = Znth (i - 1) dp0_l_2 0) by (apply Hkeep; lia).
  assert (Hbest0 : Best0EndingAt values i (retval_4 + 1)).
  { apply (best0_step_val__dp_body_branches_k4 values vals_l_2 dp0_l_2 m0_2 nvals i
             retval_2 retval_4 (retval_4 + 1));
      [lia | exact PreH53 | exact PreH62 | exact PreH64 | exact PreH34 | exact PreH28 | lia]. }
  assert (Hbest1 : Best1EndingAt values i (retval + 1)).
  { apply (best1_step__dp_body_branches_k4 values vals_l_2 dp0_l_2 m1_2 mX_2 nvals i
             retval_3 retval_5 retval retval);
      [lia | exact PreH53 | exact PreH62 | exact PreH65 | exact PreH66 | exact PreH31
      | exact PreH23 | exact PreH19 | lia]. }
  assert (Hd0b : retval_4 + 1 <= n_pre).
  { pose proof (best0_value_bound__dp_body_branches_k4 values i (retval_4 + 1) ltac:(lia) Hbest0).
    lia. }
  assert (Hd1b : retval + 1 <= n_pre).
  { pose proof (best1_value_bound__dp_body_branches_k4 values i (retval + 1) ltac:(lia) Hbest1).
    lia. }
  assert (HDP : DP0Prefix values (replace_Znth i (retval_4 + 1) dp0_l_2) (i + 1)).
  { apply (dp0prefix_step__dp_body_branches_k4 values dp0_l_2
             (replace_Znth i (retval_4 + 1) dp0_l_2) i (retval_4 + 1));
      [exact PreH62 | lia | exact Hkeep | exact Hnew | exact Hbest0]. }
  assert (Hdpb : forall k_4, 0 <= k_4 < i + 1 ->
            1 <= Znth k_4 (replace_Znth i (retval_4 + 1) dp0_l_2) 0 <= n_pre).
  { intros k4 Hk4. destruct (Z.eq_dec k4 i) as [He | Hne].
    - subst k4. rewrite Hnew. lia.
    - rewrite (Hkeep k4 ltac:(lia)). apply PreH63. lia. }
  assert (HB0 : Bit0Model values vals_l_2 (replace_Znth i (retval_4 + 1) dp0_l_2)
                  (MaxBitInsert m0_2 retval_2 (retval_4 + 1)) (i + 1) nvals).
  { apply (bit_model_insert__dp_body_branches_k4 values vals_l_2 dp0_l_2
             (replace_Znth i (retval_4 + 1) dp0_l_2) m0_2 nvals i retval_2 (retval_4 + 1));
      [lia | exact Hsi | exact PreH64 | exact PreH34 | exact Hkeep | exact Hnew]. }
  assert (HB1 : Bit1Model values vals_l_2 (MaxBitInsert m1_2 retval_3 (retval + 1))
                  (i + 1) nvals).
  { apply (bit1_model_insert__dp_body_branches_k4 values vals_l_2 m1_2 nvals i retval_3
             (retval + 1));
      [lia | exact Hsi | exact PreH65 | exact PreH31 | exact Hbest1]. }
  assert (HBX : Bit0Model values vals_l_2 (replace_Znth i (retval_4 + 1) dp0_l_2)
                  (MaxBitInsert mX_2 retval_6
                     (Znth (i - 1) (replace_Znth i (retval_4 + 1) dp0_l_2) 0)) (i + 1 - 1) nvals).
  { replace (i + 1 - 1) with (i - 1 + 1) by lia.
    apply (bit_model_insert__dp_body_branches_k4 values vals_l_2 dp0_l_2
             (replace_Znth i (retval_4 + 1) dp0_l_2) mX_2 nvals (i - 1) retval_6
             (Znth (i - 1) (replace_Znth i (retval_4 + 1) dp0_l_2) 0));
      [lia | exact Hsi | exact PreH66 | exact PreH5 | | reflexivity].
    intros j Hj. apply Hkeep. lia. }
  assert (HCP : ClampedPrefixMax (replace_Znth i (retval_4 + 1) dp0_l_2) (i + 1) best0).
  { apply (clamped_step__dp_body_branches_k4 dp0_l_2 (replace_Znth i (retval_4 + 1) dp0_l_2)
             i best0 (retval_4 + 1) best0);
      [lia | exact PreH67 | exact Hkeep | exact Hnew | lia | lia]. }
  assert (HCB : ClampedBest1Upto values (i + 1) (retval + 1)).
  { apply (clamped_best1_step__dp_body_branches_k4 values i best1 (retval + 1) (retval + 1));
      [lia | exact PreH68 | exact Hbest1 | lia | lia]. }
  assert (HCPp : ClampedPrefixMax (replace_Znth i (retval_4 + 1) dp0_l_2) (i + 1 - 1) best0_prefix).
  { replace (i + 1 - 1) with (i - 1 + 1) by lia.
    apply (clamped_keep_step__dp_body_branches_k4 dp0_l_2 (replace_Znth i (retval_4 + 1) dp0_l_2)
             (i - 1) best0_prefix);
      [lia | exact PreH69 | | exact PreH1].
    intros j Hj. apply Hkeep. lia. }
  assert (Hm0L : Zlength m0_2 = nvals + 1) by (destruct PreH64 as [HH _]; exact HH).
  assert (Hm1L : Zlength m1_2 = nvals + 1) by (destruct PreH65 as [HH _]; exact HH).
  assert (HmXL : Zlength mX_2 = nvals + 1) by (destruct PreH66 as [HH _]; exact HH).
  assert (HmXv : 1 <= Znth (i - 1) (replace_Znth i (retval_4 + 1) dp0_l_2) 0 <= n_pre).
  { rewrite Hkeep1. apply PreH63. lia. }
  assert (Hmb : forall r, 0 <= r <= nvals ->
     (((-1000000000 <= Znth r (MaxBitInsert m0_2 retval_2 (retval_4 + 1)) 0 <= n_pre /\
        -1000000000 <= Znth r (MaxBitInsert m1_2 retval_3 (retval + 1)) 0) /\
       Znth r (MaxBitInsert m1_2 retval_3 (retval + 1)) 0 <= n_pre) /\
      -1000000000 <= Znth r (MaxBitInsert mX_2 retval_6
        (Znth (i - 1) (replace_Znth i (retval_4 + 1) dp0_l_2) 0)) 0) /\
     Znth r (MaxBitInsert mX_2 retval_6
        (Znth (i - 1) (replace_Znth i (retval_4 + 1) dp0_l_2) 0)) 0 <= n_pre).
  { intros r Hr.
    pose proof (maxbitinsert_bound__dp_body_branches_k4 m0_2 retval_2 (retval_4 + 1)
                  (-1000000000) n_pre nvals Hm0L ltac:(lia)
                  ltac:(intros q Hq; pose proof (PreH61 q Hq); lia) ltac:(lia) r Hr) as H0.
    pose proof (maxbitinsert_bound__dp_body_branches_k4 m1_2 retval_3 (retval + 1)
                  (-1000000000) n_pre nvals Hm1L ltac:(lia)
                  ltac:(intros q Hq; pose proof (PreH61 q Hq); lia) ltac:(lia) r Hr) as H1.
    pose proof (maxbitinsert_bound__dp_body_branches_k4 mX_2 retval_6
                  (Znth (i - 1) (replace_Znth i (retval_4 + 1) dp0_l_2) 0)
                  (-1000000000) n_pre nvals HmXL ltac:(lia)
                  ltac:(intros q Hq; pose proof (PreH61 q Hq); lia) ltac:(lia) r Hr) as H2.
    lia. }
  assert (Hbb : forall k_3, 0 <= k_3 < nvals + 1 ->
     (((-1000000000 <= Znth k_3 bit_l1 0 <= 1000000000 /\
        -1000000000 <= Znth k_3 bit_l1_2 0) /\
       Znth k_3 bit_l1_2 0 <= 1000000000) /\ -1000000000 <= Znth k_3 bit_l1_3 0) /\
      Znth k_3 bit_l1_3 0 <= 1000000000).
  { intros k3 Hk3. pose proof (PreH14 k3 Hk3). pose proof (PreH10 k3 Hk3).
    pose proof (PreH3 k3 Hk3). lia. }
  Exists (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (retval_4 + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_3 (retval + 1))
         (MaxBitInsert m0_2 retval_2 (retval_4 + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (retval_4 + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - do 12 cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed.

Lemma proof_of_solver_entail_wit_12_44 : solver_entail_wit_12_44.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hsi : StrictIncPrefix vals_l_2 nvals) by (destruct PreH53 as [HH _]; exact HH).
  assert (Hci : Znth i c_l_2 0 = KeyAt values i) by (apply PreH50; lia).
  assert (Hci1 : Znth (i - 1) c_l_2 0 = KeyAt values (i - 1)) by (apply PreH50; lia).
  rewrite Hci in PreH31, PreH34. rewrite Hci1 in PreH5.
  assert (HdpL : Zlength (replace_Znth i (0 + 1) dp0_l_2) = n_pre).
  { rewrite Zlength_replace_Znth__dp_body_branches_k4. exact PreH49. }
  assert (Hkeep : forall j, 0 <= j < i ->
            Znth j (replace_Znth i (0 + 1) dp0_l_2) 0 = Znth j dp0_l_2 0).
  { intros j Hj. apply Znth_replace_Znth_Diff; lia. }
  assert (Hnew : Znth i (replace_Znth i (0 + 1) dp0_l_2) 0 = 0 + 1).
  { apply Znth_replace_Znth_Same. lia. }
  assert (Hkeep1 : Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0
                   = Znth (i - 1) dp0_l_2 0) by (apply Hkeep; lia).
  assert (Hbest0 : Best0EndingAt values i (0 + 1)).
  { apply (best0_step_val__dp_body_branches_k4 values vals_l_2 dp0_l_2 m0_2 nvals i
             retval_2 retval_4 (0 + 1));
      [lia | exact PreH53 | exact PreH62 | exact PreH64 | exact PreH34 | exact PreH28 | lia]. }
  assert (Hbest1 : Best1EndingAt values i (retval + 1)).
  { apply (best1_step__dp_body_branches_k4 values vals_l_2 dp0_l_2 m1_2 mX_2 nvals i
             retval_3 retval_5 retval retval);
      [lia | exact PreH53 | exact PreH62 | exact PreH65 | exact PreH66 | exact PreH31
      | exact PreH23 | exact PreH19 | lia]. }
  assert (Hd0b : 0 + 1 <= n_pre).
  { pose proof (best0_value_bound__dp_body_branches_k4 values i (0 + 1) ltac:(lia) Hbest0).
    lia. }
  assert (Hd1b : retval + 1 <= n_pre).
  { pose proof (best1_value_bound__dp_body_branches_k4 values i (retval + 1) ltac:(lia) Hbest1).
    lia. }
  assert (HDP : DP0Prefix values (replace_Znth i (0 + 1) dp0_l_2) (i + 1)).
  { apply (dp0prefix_step__dp_body_branches_k4 values dp0_l_2
             (replace_Znth i (0 + 1) dp0_l_2) i (0 + 1));
      [exact PreH62 | lia | exact Hkeep | exact Hnew | exact Hbest0]. }
  assert (Hdpb : forall k_4, 0 <= k_4 < i + 1 ->
            1 <= Znth k_4 (replace_Znth i (0 + 1) dp0_l_2) 0 <= n_pre).
  { intros k4 Hk4. destruct (Z.eq_dec k4 i) as [He | Hne].
    - subst k4. rewrite Hnew. lia.
    - rewrite (Hkeep k4 ltac:(lia)). apply PreH63. lia. }
  assert (HB0 : Bit0Model values vals_l_2 (replace_Znth i (0 + 1) dp0_l_2)
                  (MaxBitInsert m0_2 retval_2 (0 + 1)) (i + 1) nvals).
  { apply (bit_model_insert__dp_body_branches_k4 values vals_l_2 dp0_l_2
             (replace_Znth i (0 + 1) dp0_l_2) m0_2 nvals i retval_2 (0 + 1));
      [lia | exact Hsi | exact PreH64 | exact PreH34 | exact Hkeep | exact Hnew]. }
  assert (HB1 : Bit1Model values vals_l_2 (MaxBitInsert m1_2 retval_3 (retval + 1))
                  (i + 1) nvals).
  { apply (bit1_model_insert__dp_body_branches_k4 values vals_l_2 m1_2 nvals i retval_3
             (retval + 1));
      [lia | exact Hsi | exact PreH65 | exact PreH31 | exact Hbest1]. }
  assert (HBX : Bit0Model values vals_l_2 (replace_Znth i (0 + 1) dp0_l_2)
                  (MaxBitInsert mX_2 retval_6
                     (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)) (i + 1 - 1) nvals).
  { replace (i + 1 - 1) with (i - 1 + 1) by lia.
    apply (bit_model_insert__dp_body_branches_k4 values vals_l_2 dp0_l_2
             (replace_Znth i (0 + 1) dp0_l_2) mX_2 nvals (i - 1) retval_6
             (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0));
      [lia | exact Hsi | exact PreH66 | exact PreH5 | | reflexivity].
    intros j Hj. apply Hkeep. lia. }
  assert (HCP : ClampedPrefixMax (replace_Znth i (0 + 1) dp0_l_2) (i + 1) best0).
  { apply (clamped_step__dp_body_branches_k4 dp0_l_2 (replace_Znth i (0 + 1) dp0_l_2)
             i best0 (0 + 1) best0);
      [lia | exact PreH67 | exact Hkeep | exact Hnew | lia | lia]. }
  assert (HCB : ClampedBest1Upto values (i + 1) (retval + 1)).
  { apply (clamped_best1_step__dp_body_branches_k4 values i best1 (retval + 1) (retval + 1));
      [lia | exact PreH68 | exact Hbest1 | lia | lia]. }
  assert (HCPp : ClampedPrefixMax (replace_Znth i (0 + 1) dp0_l_2) (i + 1 - 1) best0_prefix).
  { replace (i + 1 - 1) with (i - 1 + 1) by lia.
    apply (clamped_keep_step__dp_body_branches_k4 dp0_l_2 (replace_Znth i (0 + 1) dp0_l_2)
             (i - 1) best0_prefix);
      [lia | exact PreH69 | | exact PreH1].
    intros j Hj. apply Hkeep. lia. }
  assert (Hm0L : Zlength m0_2 = nvals + 1) by (destruct PreH64 as [HH _]; exact HH).
  assert (Hm1L : Zlength m1_2 = nvals + 1) by (destruct PreH65 as [HH _]; exact HH).
  assert (HmXL : Zlength mX_2 = nvals + 1) by (destruct PreH66 as [HH _]; exact HH).
  assert (HmXv : 1 <= Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0 <= n_pre).
  { rewrite Hkeep1. apply PreH63. lia. }
  assert (Hmb : forall r, 0 <= r <= nvals ->
     (((-1000000000 <= Znth r (MaxBitInsert m0_2 retval_2 (0 + 1)) 0 <= n_pre /\
        -1000000000 <= Znth r (MaxBitInsert m1_2 retval_3 (retval + 1)) 0) /\
       Znth r (MaxBitInsert m1_2 retval_3 (retval + 1)) 0 <= n_pre) /\
      -1000000000 <= Znth r (MaxBitInsert mX_2 retval_6
        (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)) 0) /\
     Znth r (MaxBitInsert mX_2 retval_6
        (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)) 0 <= n_pre).
  { intros r Hr.
    pose proof (maxbitinsert_bound__dp_body_branches_k4 m0_2 retval_2 (0 + 1)
                  (-1000000000) n_pre nvals Hm0L ltac:(lia)
                  ltac:(intros q Hq; pose proof (PreH61 q Hq); lia) ltac:(lia) r Hr) as H0.
    pose proof (maxbitinsert_bound__dp_body_branches_k4 m1_2 retval_3 (retval + 1)
                  (-1000000000) n_pre nvals Hm1L ltac:(lia)
                  ltac:(intros q Hq; pose proof (PreH61 q Hq); lia) ltac:(lia) r Hr) as H1.
    pose proof (maxbitinsert_bound__dp_body_branches_k4 mX_2 retval_6
                  (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)
                  (-1000000000) n_pre nvals HmXL ltac:(lia)
                  ltac:(intros q Hq; pose proof (PreH61 q Hq); lia) ltac:(lia) r Hr) as H2.
    lia. }
  assert (Hbb : forall k_3, 0 <= k_3 < nvals + 1 ->
     (((-1000000000 <= Znth k_3 bit_l1 0 <= 1000000000 /\
        -1000000000 <= Znth k_3 bit_l1_2 0) /\
       Znth k_3 bit_l1_2 0 <= 1000000000) /\ -1000000000 <= Znth k_3 bit_l1_3 0) /\
      Znth k_3 bit_l1_3 0 <= 1000000000).
  { intros k3 Hk3. pose proof (PreH14 k3 Hk3). pose proof (PreH10 k3 Hk3).
    pose proof (PreH3 k3 Hk3). lia. }
  Exists (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_3 (retval + 1))
         (MaxBitInsert m0_2 retval_2 (0 + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (0 + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - do 12 cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed.

Lemma proof_of_solver_entail_wit_12_45 : solver_entail_wit_12_45.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hsi : StrictIncPrefix vals_l_2 nvals) by (destruct PreH53 as [HH _]; exact HH).
  assert (Hci : Znth i c_l_2 0 = KeyAt values i) by (apply PreH50; lia).
  assert (Hci1 : Znth (i - 1) c_l_2 0 = KeyAt values (i - 1)) by (apply PreH50; lia).
  rewrite Hci in PreH31, PreH34. rewrite Hci1 in PreH5.
  assert (HdpL : Zlength (replace_Znth i (retval_4 + 1) dp0_l_2) = n_pre).
  { rewrite Zlength_replace_Znth__dp_body_branches_k4. exact PreH49. }
  assert (Hkeep : forall j, 0 <= j < i ->
            Znth j (replace_Znth i (retval_4 + 1) dp0_l_2) 0 = Znth j dp0_l_2 0).
  { intros j Hj. apply Znth_replace_Znth_Diff; lia. }
  assert (Hnew : Znth i (replace_Znth i (retval_4 + 1) dp0_l_2) 0 = retval_4 + 1).
  { apply Znth_replace_Znth_Same. lia. }
  assert (Hkeep1 : Znth (i - 1) (replace_Znth i (retval_4 + 1) dp0_l_2) 0
                   = Znth (i - 1) dp0_l_2 0) by (apply Hkeep; lia).
  assert (Hbest0 : Best0EndingAt values i (retval_4 + 1)).
  { apply (best0_step_val__dp_body_branches_k4 values vals_l_2 dp0_l_2 m0_2 nvals i
             retval_2 retval_4 (retval_4 + 1));
      [lia | exact PreH53 | exact PreH62 | exact PreH64 | exact PreH34 | exact PreH28 | lia]. }
  assert (Hbest1 : Best1EndingAt values i (retval + 1)).
  { apply (best1_step__dp_body_branches_k4 values vals_l_2 dp0_l_2 m1_2 mX_2 nvals i
             retval_3 retval retval_5 retval);
      [lia | exact PreH53 | exact PreH62 | exact PreH65 | exact PreH66 | exact PreH31
      | exact PreH23 | exact PreH19 | lia]. }
  assert (Hd0b : retval_4 + 1 <= n_pre).
  { pose proof (best0_value_bound__dp_body_branches_k4 values i (retval_4 + 1) ltac:(lia) Hbest0).
    lia. }
  assert (Hd1b : retval + 1 <= n_pre).
  { pose proof (best1_value_bound__dp_body_branches_k4 values i (retval + 1) ltac:(lia) Hbest1).
    lia. }
  assert (HDP : DP0Prefix values (replace_Znth i (retval_4 + 1) dp0_l_2) (i + 1)).
  { apply (dp0prefix_step__dp_body_branches_k4 values dp0_l_2
             (replace_Znth i (retval_4 + 1) dp0_l_2) i (retval_4 + 1));
      [exact PreH62 | lia | exact Hkeep | exact Hnew | exact Hbest0]. }
  assert (Hdpb : forall k_4, 0 <= k_4 < i + 1 ->
            1 <= Znth k_4 (replace_Znth i (retval_4 + 1) dp0_l_2) 0 <= n_pre).
  { intros k4 Hk4. destruct (Z.eq_dec k4 i) as [He | Hne].
    - subst k4. rewrite Hnew. lia.
    - rewrite (Hkeep k4 ltac:(lia)). apply PreH63. lia. }
  assert (HB0 : Bit0Model values vals_l_2 (replace_Znth i (retval_4 + 1) dp0_l_2)
                  (MaxBitInsert m0_2 retval_2 (retval_4 + 1)) (i + 1) nvals).
  { apply (bit_model_insert__dp_body_branches_k4 values vals_l_2 dp0_l_2
             (replace_Znth i (retval_4 + 1) dp0_l_2) m0_2 nvals i retval_2 (retval_4 + 1));
      [lia | exact Hsi | exact PreH64 | exact PreH34 | exact Hkeep | exact Hnew]. }
  assert (HB1 : Bit1Model values vals_l_2 (MaxBitInsert m1_2 retval_3 (retval + 1))
                  (i + 1) nvals).
  { apply (bit1_model_insert__dp_body_branches_k4 values vals_l_2 m1_2 nvals i retval_3
             (retval + 1));
      [lia | exact Hsi | exact PreH65 | exact PreH31 | exact Hbest1]. }
  assert (HBX : Bit0Model values vals_l_2 (replace_Znth i (retval_4 + 1) dp0_l_2)
                  (MaxBitInsert mX_2 retval_6
                     (Znth (i - 1) (replace_Znth i (retval_4 + 1) dp0_l_2) 0)) (i + 1 - 1) nvals).
  { replace (i + 1 - 1) with (i - 1 + 1) by lia.
    apply (bit_model_insert__dp_body_branches_k4 values vals_l_2 dp0_l_2
             (replace_Znth i (retval_4 + 1) dp0_l_2) mX_2 nvals (i - 1) retval_6
             (Znth (i - 1) (replace_Znth i (retval_4 + 1) dp0_l_2) 0));
      [lia | exact Hsi | exact PreH66 | exact PreH5 | | reflexivity].
    intros j Hj. apply Hkeep. lia. }
  assert (HCP : ClampedPrefixMax (replace_Znth i (retval_4 + 1) dp0_l_2) (i + 1) best0).
  { apply (clamped_step__dp_body_branches_k4 dp0_l_2 (replace_Znth i (retval_4 + 1) dp0_l_2)
             i best0 (retval_4 + 1) best0);
      [lia | exact PreH67 | exact Hkeep | exact Hnew | lia | lia]. }
  assert (HCB : ClampedBest1Upto values (i + 1) (retval + 1)).
  { apply (clamped_best1_step__dp_body_branches_k4 values i best1 (retval + 1) (retval + 1));
      [lia | exact PreH68 | exact Hbest1 | lia | lia]. }
  assert (HCPp : ClampedPrefixMax (replace_Znth i (retval_4 + 1) dp0_l_2) (i + 1 - 1) best0_prefix).
  { replace (i + 1 - 1) with (i - 1 + 1) by lia.
    apply (clamped_keep_step__dp_body_branches_k4 dp0_l_2 (replace_Znth i (retval_4 + 1) dp0_l_2)
             (i - 1) best0_prefix);
      [lia | exact PreH69 | | exact PreH1].
    intros j Hj. apply Hkeep. lia. }
  assert (Hm0L : Zlength m0_2 = nvals + 1) by (destruct PreH64 as [HH _]; exact HH).
  assert (Hm1L : Zlength m1_2 = nvals + 1) by (destruct PreH65 as [HH _]; exact HH).
  assert (HmXL : Zlength mX_2 = nvals + 1) by (destruct PreH66 as [HH _]; exact HH).
  assert (HmXv : 1 <= Znth (i - 1) (replace_Znth i (retval_4 + 1) dp0_l_2) 0 <= n_pre).
  { rewrite Hkeep1. apply PreH63. lia. }
  assert (Hmb : forall r, 0 <= r <= nvals ->
     (((-1000000000 <= Znth r (MaxBitInsert m0_2 retval_2 (retval_4 + 1)) 0 <= n_pre /\
        -1000000000 <= Znth r (MaxBitInsert m1_2 retval_3 (retval + 1)) 0) /\
       Znth r (MaxBitInsert m1_2 retval_3 (retval + 1)) 0 <= n_pre) /\
      -1000000000 <= Znth r (MaxBitInsert mX_2 retval_6
        (Znth (i - 1) (replace_Znth i (retval_4 + 1) dp0_l_2) 0)) 0) /\
     Znth r (MaxBitInsert mX_2 retval_6
        (Znth (i - 1) (replace_Znth i (retval_4 + 1) dp0_l_2) 0)) 0 <= n_pre).
  { intros r Hr.
    pose proof (maxbitinsert_bound__dp_body_branches_k4 m0_2 retval_2 (retval_4 + 1)
                  (-1000000000) n_pre nvals Hm0L ltac:(lia)
                  ltac:(intros q Hq; pose proof (PreH61 q Hq); lia) ltac:(lia) r Hr) as H0.
    pose proof (maxbitinsert_bound__dp_body_branches_k4 m1_2 retval_3 (retval + 1)
                  (-1000000000) n_pre nvals Hm1L ltac:(lia)
                  ltac:(intros q Hq; pose proof (PreH61 q Hq); lia) ltac:(lia) r Hr) as H1.
    pose proof (maxbitinsert_bound__dp_body_branches_k4 mX_2 retval_6
                  (Znth (i - 1) (replace_Znth i (retval_4 + 1) dp0_l_2) 0)
                  (-1000000000) n_pre nvals HmXL ltac:(lia)
                  ltac:(intros q Hq; pose proof (PreH61 q Hq); lia) ltac:(lia) r Hr) as H2.
    lia. }
  assert (Hbb : forall k_3, 0 <= k_3 < nvals + 1 ->
     (((-1000000000 <= Znth k_3 bit_l1 0 <= 1000000000 /\
        -1000000000 <= Znth k_3 bit_l1_2 0) /\
       Znth k_3 bit_l1_2 0 <= 1000000000) /\ -1000000000 <= Znth k_3 bit_l1_3 0) /\
      Znth k_3 bit_l1_3 0 <= 1000000000).
  { intros k3 Hk3. pose proof (PreH14 k3 Hk3). pose proof (PreH10 k3 Hk3).
    pose proof (PreH3 k3 Hk3). lia. }
  Exists (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (retval_4 + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_3 (retval + 1))
         (MaxBitInsert m0_2 retval_2 (retval_4 + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (retval_4 + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - do 12 cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed.

Lemma proof_of_solver_entail_wit_12_46 : solver_entail_wit_12_46.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hsi : StrictIncPrefix vals_l_2 nvals) by (destruct PreH53 as [HH _]; exact HH).
  assert (Hci : Znth i c_l_2 0 = KeyAt values i) by (apply PreH50; lia).
  assert (Hci1 : Znth (i - 1) c_l_2 0 = KeyAt values (i - 1)) by (apply PreH50; lia).
  rewrite Hci in PreH31, PreH34. rewrite Hci1 in PreH5.
  assert (HdpL : Zlength (replace_Znth i (0 + 1) dp0_l_2) = n_pre).
  { rewrite Zlength_replace_Znth__dp_body_branches_k4. exact PreH49. }
  assert (Hkeep : forall j, 0 <= j < i ->
            Znth j (replace_Znth i (0 + 1) dp0_l_2) 0 = Znth j dp0_l_2 0).
  { intros j Hj. apply Znth_replace_Znth_Diff; lia. }
  assert (Hnew : Znth i (replace_Znth i (0 + 1) dp0_l_2) 0 = 0 + 1).
  { apply Znth_replace_Znth_Same. lia. }
  assert (Hkeep1 : Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0
                   = Znth (i - 1) dp0_l_2 0) by (apply Hkeep; lia).
  assert (Hbest0 : Best0EndingAt values i (0 + 1)).
  { apply (best0_step_val__dp_body_branches_k4 values vals_l_2 dp0_l_2 m0_2 nvals i
             retval_2 retval_4 (0 + 1));
      [lia | exact PreH53 | exact PreH62 | exact PreH64 | exact PreH34 | exact PreH28 | lia]. }
  assert (Hbest1 : Best1EndingAt values i (retval + 1)).
  { apply (best1_step__dp_body_branches_k4 values vals_l_2 dp0_l_2 m1_2 mX_2 nvals i
             retval_3 retval retval_5 retval);
      [lia | exact PreH53 | exact PreH62 | exact PreH65 | exact PreH66 | exact PreH31
      | exact PreH23 | exact PreH19 | lia]. }
  assert (Hd0b : 0 + 1 <= n_pre).
  { pose proof (best0_value_bound__dp_body_branches_k4 values i (0 + 1) ltac:(lia) Hbest0).
    lia. }
  assert (Hd1b : retval + 1 <= n_pre).
  { pose proof (best1_value_bound__dp_body_branches_k4 values i (retval + 1) ltac:(lia) Hbest1).
    lia. }
  assert (HDP : DP0Prefix values (replace_Znth i (0 + 1) dp0_l_2) (i + 1)).
  { apply (dp0prefix_step__dp_body_branches_k4 values dp0_l_2
             (replace_Znth i (0 + 1) dp0_l_2) i (0 + 1));
      [exact PreH62 | lia | exact Hkeep | exact Hnew | exact Hbest0]. }
  assert (Hdpb : forall k_4, 0 <= k_4 < i + 1 ->
            1 <= Znth k_4 (replace_Znth i (0 + 1) dp0_l_2) 0 <= n_pre).
  { intros k4 Hk4. destruct (Z.eq_dec k4 i) as [He | Hne].
    - subst k4. rewrite Hnew. lia.
    - rewrite (Hkeep k4 ltac:(lia)). apply PreH63. lia. }
  assert (HB0 : Bit0Model values vals_l_2 (replace_Znth i (0 + 1) dp0_l_2)
                  (MaxBitInsert m0_2 retval_2 (0 + 1)) (i + 1) nvals).
  { apply (bit_model_insert__dp_body_branches_k4 values vals_l_2 dp0_l_2
             (replace_Znth i (0 + 1) dp0_l_2) m0_2 nvals i retval_2 (0 + 1));
      [lia | exact Hsi | exact PreH64 | exact PreH34 | exact Hkeep | exact Hnew]. }
  assert (HB1 : Bit1Model values vals_l_2 (MaxBitInsert m1_2 retval_3 (retval + 1))
                  (i + 1) nvals).
  { apply (bit1_model_insert__dp_body_branches_k4 values vals_l_2 m1_2 nvals i retval_3
             (retval + 1));
      [lia | exact Hsi | exact PreH65 | exact PreH31 | exact Hbest1]. }
  assert (HBX : Bit0Model values vals_l_2 (replace_Znth i (0 + 1) dp0_l_2)
                  (MaxBitInsert mX_2 retval_6
                     (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)) (i + 1 - 1) nvals).
  { replace (i + 1 - 1) with (i - 1 + 1) by lia.
    apply (bit_model_insert__dp_body_branches_k4 values vals_l_2 dp0_l_2
             (replace_Znth i (0 + 1) dp0_l_2) mX_2 nvals (i - 1) retval_6
             (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0));
      [lia | exact Hsi | exact PreH66 | exact PreH5 | | reflexivity].
    intros j Hj. apply Hkeep. lia. }
  assert (HCP : ClampedPrefixMax (replace_Znth i (0 + 1) dp0_l_2) (i + 1) best0).
  { apply (clamped_step__dp_body_branches_k4 dp0_l_2 (replace_Znth i (0 + 1) dp0_l_2)
             i best0 (0 + 1) best0);
      [lia | exact PreH67 | exact Hkeep | exact Hnew | lia | lia]. }
  assert (HCB : ClampedBest1Upto values (i + 1) (retval + 1)).
  { apply (clamped_best1_step__dp_body_branches_k4 values i best1 (retval + 1) (retval + 1));
      [lia | exact PreH68 | exact Hbest1 | lia | lia]. }
  assert (HCPp : ClampedPrefixMax (replace_Znth i (0 + 1) dp0_l_2) (i + 1 - 1) best0_prefix).
  { replace (i + 1 - 1) with (i - 1 + 1) by lia.
    apply (clamped_keep_step__dp_body_branches_k4 dp0_l_2 (replace_Znth i (0 + 1) dp0_l_2)
             (i - 1) best0_prefix);
      [lia | exact PreH69 | | exact PreH1].
    intros j Hj. apply Hkeep. lia. }
  assert (Hm0L : Zlength m0_2 = nvals + 1) by (destruct PreH64 as [HH _]; exact HH).
  assert (Hm1L : Zlength m1_2 = nvals + 1) by (destruct PreH65 as [HH _]; exact HH).
  assert (HmXL : Zlength mX_2 = nvals + 1) by (destruct PreH66 as [HH _]; exact HH).
  assert (HmXv : 1 <= Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0 <= n_pre).
  { rewrite Hkeep1. apply PreH63. lia. }
  assert (Hmb : forall r, 0 <= r <= nvals ->
     (((-1000000000 <= Znth r (MaxBitInsert m0_2 retval_2 (0 + 1)) 0 <= n_pre /\
        -1000000000 <= Znth r (MaxBitInsert m1_2 retval_3 (retval + 1)) 0) /\
       Znth r (MaxBitInsert m1_2 retval_3 (retval + 1)) 0 <= n_pre) /\
      -1000000000 <= Znth r (MaxBitInsert mX_2 retval_6
        (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)) 0) /\
     Znth r (MaxBitInsert mX_2 retval_6
        (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)) 0 <= n_pre).
  { intros r Hr.
    pose proof (maxbitinsert_bound__dp_body_branches_k4 m0_2 retval_2 (0 + 1)
                  (-1000000000) n_pre nvals Hm0L ltac:(lia)
                  ltac:(intros q Hq; pose proof (PreH61 q Hq); lia) ltac:(lia) r Hr) as H0.
    pose proof (maxbitinsert_bound__dp_body_branches_k4 m1_2 retval_3 (retval + 1)
                  (-1000000000) n_pre nvals Hm1L ltac:(lia)
                  ltac:(intros q Hq; pose proof (PreH61 q Hq); lia) ltac:(lia) r Hr) as H1.
    pose proof (maxbitinsert_bound__dp_body_branches_k4 mX_2 retval_6
                  (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)
                  (-1000000000) n_pre nvals HmXL ltac:(lia)
                  ltac:(intros q Hq; pose proof (PreH61 q Hq); lia) ltac:(lia) r Hr) as H2.
    lia. }
  assert (Hbb : forall k_3, 0 <= k_3 < nvals + 1 ->
     (((-1000000000 <= Znth k_3 bit_l1 0 <= 1000000000 /\
        -1000000000 <= Znth k_3 bit_l1_2 0) /\
       Znth k_3 bit_l1_2 0 <= 1000000000) /\ -1000000000 <= Znth k_3 bit_l1_3 0) /\
      Znth k_3 bit_l1_3 0 <= 1000000000).
  { intros k3 Hk3. pose proof (PreH14 k3 Hk3). pose proof (PreH10 k3 Hk3).
    pose proof (PreH3 k3 Hk3). lia. }
  Exists (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_3 (retval + 1))
         (MaxBitInsert m0_2 retval_2 (0 + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (0 + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - do 12 cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed.

Lemma proof_of_solver_entail_wit_12_47 : solver_entail_wit_12_47.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hsi : StrictIncPrefix vals_l_2 nvals) by (destruct PreH53 as [HH _]; exact HH).
  assert (Hci : Znth i c_l_2 0 = KeyAt values i) by (apply PreH50; lia).
  assert (Hci1 : Znth (i - 1) c_l_2 0 = KeyAt values (i - 1)) by (apply PreH50; lia).
  rewrite Hci in PreH31, PreH34. rewrite Hci1 in PreH5.
  assert (HdpL : Zlength (replace_Znth i (retval_3 + 1) dp0_l_2) = n_pre).
  { rewrite Zlength_replace_Znth__dp_body_branches_k4. exact PreH49. }
  assert (Hkeep : forall j, 0 <= j < i ->
            Znth j (replace_Znth i (retval_3 + 1) dp0_l_2) 0 = Znth j dp0_l_2 0).
  { intros j Hj. apply Znth_replace_Znth_Diff; lia. }
  assert (Hnew : Znth i (replace_Znth i (retval_3 + 1) dp0_l_2) 0 = retval_3 + 1).
  { apply Znth_replace_Znth_Same. lia. }
  assert (Hkeep1 : Znth (i - 1) (replace_Znth i (retval_3 + 1) dp0_l_2) 0
                   = Znth (i - 1) dp0_l_2 0) by (apply Hkeep; lia).
  assert (Hbest0 : Best0EndingAt values i (retval_3 + 1)).
  { apply (best0_step_val__dp_body_branches_k4 values vals_l_2 dp0_l_2 m0_2 nvals i
             retval retval_3 (retval_3 + 1));
      [lia | exact PreH53 | exact PreH62 | exact PreH64 | exact PreH34 | exact PreH28 | lia]. }
  assert (Hbest1 : Best1EndingAt values i (0 + 1)).
  { apply (best1_step__dp_body_branches_k4 values vals_l_2 dp0_l_2 m1_2 mX_2 nvals i
             retval_2 retval_4 retval_5 0);
      [lia | exact PreH53 | exact PreH62 | exact PreH65 | exact PreH66 | exact PreH31
      | exact PreH23 | exact PreH19 | lia]. }
  assert (Hd0b : retval_3 + 1 <= n_pre).
  { pose proof (best0_value_bound__dp_body_branches_k4 values i (retval_3 + 1) ltac:(lia) Hbest0).
    lia. }
  assert (Hd1b : 0 + 1 <= n_pre).
  { pose proof (best1_value_bound__dp_body_branches_k4 values i (0 + 1) ltac:(lia) Hbest1).
    lia. }
  assert (HDP : DP0Prefix values (replace_Znth i (retval_3 + 1) dp0_l_2) (i + 1)).
  { apply (dp0prefix_step__dp_body_branches_k4 values dp0_l_2
             (replace_Znth i (retval_3 + 1) dp0_l_2) i (retval_3 + 1));
      [exact PreH62 | lia | exact Hkeep | exact Hnew | exact Hbest0]. }
  assert (Hdpb : forall k_4, 0 <= k_4 < i + 1 ->
            1 <= Znth k_4 (replace_Znth i (retval_3 + 1) dp0_l_2) 0 <= n_pre).
  { intros k4 Hk4. destruct (Z.eq_dec k4 i) as [He | Hne].
    - subst k4. rewrite Hnew. lia.
    - rewrite (Hkeep k4 ltac:(lia)). apply PreH63. lia. }
  assert (HB0 : Bit0Model values vals_l_2 (replace_Znth i (retval_3 + 1) dp0_l_2)
                  (MaxBitInsert m0_2 retval (retval_3 + 1)) (i + 1) nvals).
  { apply (bit_model_insert__dp_body_branches_k4 values vals_l_2 dp0_l_2
             (replace_Znth i (retval_3 + 1) dp0_l_2) m0_2 nvals i retval (retval_3 + 1));
      [lia | exact Hsi | exact PreH64 | exact PreH34 | exact Hkeep | exact Hnew]. }
  assert (HB1 : Bit1Model values vals_l_2 (MaxBitInsert m1_2 retval_2 (0 + 1))
                  (i + 1) nvals).
  { apply (bit1_model_insert__dp_body_branches_k4 values vals_l_2 m1_2 nvals i retval_2
             (0 + 1));
      [lia | exact Hsi | exact PreH65 | exact PreH31 | exact Hbest1]. }
  assert (HBX : Bit0Model values vals_l_2 (replace_Znth i (retval_3 + 1) dp0_l_2)
                  (MaxBitInsert mX_2 retval_6
                     (Znth (i - 1) (replace_Znth i (retval_3 + 1) dp0_l_2) 0)) (i + 1 - 1) nvals).
  { replace (i + 1 - 1) with (i - 1 + 1) by lia.
    apply (bit_model_insert__dp_body_branches_k4 values vals_l_2 dp0_l_2
             (replace_Znth i (retval_3 + 1) dp0_l_2) mX_2 nvals (i - 1) retval_6
             (Znth (i - 1) (replace_Znth i (retval_3 + 1) dp0_l_2) 0));
      [lia | exact Hsi | exact PreH66 | exact PreH5 | | reflexivity].
    intros j Hj. apply Hkeep. lia. }
  assert (HCP : ClampedPrefixMax (replace_Znth i (retval_3 + 1) dp0_l_2) (i + 1) best0).
  { apply (clamped_step__dp_body_branches_k4 dp0_l_2 (replace_Znth i (retval_3 + 1) dp0_l_2)
             i best0 (retval_3 + 1) best0);
      [lia | exact PreH67 | exact Hkeep | exact Hnew | lia | lia]. }
  assert (HCB : ClampedBest1Upto values (i + 1) (0 + 1)).
  { apply (clamped_best1_step__dp_body_branches_k4 values i best1 (0 + 1) (0 + 1));
      [lia | exact PreH68 | exact Hbest1 | lia | lia]. }
  assert (HCPp : ClampedPrefixMax (replace_Znth i (retval_3 + 1) dp0_l_2) (i + 1 - 1) best0_prefix).
  { replace (i + 1 - 1) with (i - 1 + 1) by lia.
    apply (clamped_keep_step__dp_body_branches_k4 dp0_l_2 (replace_Znth i (retval_3 + 1) dp0_l_2)
             (i - 1) best0_prefix);
      [lia | exact PreH69 | | exact PreH1].
    intros j Hj. apply Hkeep. lia. }
  assert (Hm0L : Zlength m0_2 = nvals + 1) by (destruct PreH64 as [HH _]; exact HH).
  assert (Hm1L : Zlength m1_2 = nvals + 1) by (destruct PreH65 as [HH _]; exact HH).
  assert (HmXL : Zlength mX_2 = nvals + 1) by (destruct PreH66 as [HH _]; exact HH).
  assert (HmXv : 1 <= Znth (i - 1) (replace_Znth i (retval_3 + 1) dp0_l_2) 0 <= n_pre).
  { rewrite Hkeep1. apply PreH63. lia. }
  assert (Hmb : forall r, 0 <= r <= nvals ->
     (((-1000000000 <= Znth r (MaxBitInsert m0_2 retval (retval_3 + 1)) 0 <= n_pre /\
        -1000000000 <= Znth r (MaxBitInsert m1_2 retval_2 (0 + 1)) 0) /\
       Znth r (MaxBitInsert m1_2 retval_2 (0 + 1)) 0 <= n_pre) /\
      -1000000000 <= Znth r (MaxBitInsert mX_2 retval_6
        (Znth (i - 1) (replace_Znth i (retval_3 + 1) dp0_l_2) 0)) 0) /\
     Znth r (MaxBitInsert mX_2 retval_6
        (Znth (i - 1) (replace_Znth i (retval_3 + 1) dp0_l_2) 0)) 0 <= n_pre).
  { intros r Hr.
    pose proof (maxbitinsert_bound__dp_body_branches_k4 m0_2 retval (retval_3 + 1)
                  (-1000000000) n_pre nvals Hm0L ltac:(lia)
                  ltac:(intros q Hq; pose proof (PreH61 q Hq); lia) ltac:(lia) r Hr) as H0.
    pose proof (maxbitinsert_bound__dp_body_branches_k4 m1_2 retval_2 (0 + 1)
                  (-1000000000) n_pre nvals Hm1L ltac:(lia)
                  ltac:(intros q Hq; pose proof (PreH61 q Hq); lia) ltac:(lia) r Hr) as H1.
    pose proof (maxbitinsert_bound__dp_body_branches_k4 mX_2 retval_6
                  (Znth (i - 1) (replace_Znth i (retval_3 + 1) dp0_l_2) 0)
                  (-1000000000) n_pre nvals HmXL ltac:(lia)
                  ltac:(intros q Hq; pose proof (PreH61 q Hq); lia) ltac:(lia) r Hr) as H2.
    lia. }
  assert (Hbb : forall k_3, 0 <= k_3 < nvals + 1 ->
     (((-1000000000 <= Znth k_3 bit_l1 0 <= 1000000000 /\
        -1000000000 <= Znth k_3 bit_l1_2 0) /\
       Znth k_3 bit_l1_2 0 <= 1000000000) /\ -1000000000 <= Znth k_3 bit_l1_3 0) /\
      Znth k_3 bit_l1_3 0 <= 1000000000).
  { intros k3 Hk3. pose proof (PreH14 k3 Hk3). pose proof (PreH10 k3 Hk3).
    pose proof (PreH3 k3 Hk3). lia. }
  Exists (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (retval_3 + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_2 (0 + 1))
         (MaxBitInsert m0_2 retval (retval_3 + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (retval_3 + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - do 12 cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed.

Lemma proof_of_solver_entail_wit_12_48 : solver_entail_wit_12_48.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hsi : StrictIncPrefix vals_l_2 nvals) by (destruct PreH53 as [HH _]; exact HH).
  assert (Hci : Znth i c_l_2 0 = KeyAt values i) by (apply PreH50; lia).
  assert (Hci1 : Znth (i - 1) c_l_2 0 = KeyAt values (i - 1)) by (apply PreH50; lia).
  rewrite Hci in PreH31, PreH34. rewrite Hci1 in PreH5.
  assert (HdpL : Zlength (replace_Znth i (0 + 1) dp0_l_2) = n_pre).
  { rewrite Zlength_replace_Znth__dp_body_branches_k4. exact PreH49. }
  assert (Hkeep : forall j, 0 <= j < i ->
            Znth j (replace_Znth i (0 + 1) dp0_l_2) 0 = Znth j dp0_l_2 0).
  { intros j Hj. apply Znth_replace_Znth_Diff; lia. }
  assert (Hnew : Znth i (replace_Znth i (0 + 1) dp0_l_2) 0 = 0 + 1).
  { apply Znth_replace_Znth_Same. lia. }
  assert (Hkeep1 : Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0
                   = Znth (i - 1) dp0_l_2 0) by (apply Hkeep; lia).
  assert (Hbest0 : Best0EndingAt values i (0 + 1)).
  { apply (best0_step_val__dp_body_branches_k4 values vals_l_2 dp0_l_2 m0_2 nvals i
             retval retval_3 (0 + 1));
      [lia | exact PreH53 | exact PreH62 | exact PreH64 | exact PreH34 | exact PreH28 | lia]. }
  assert (Hbest1 : Best1EndingAt values i (0 + 1)).
  { apply (best1_step__dp_body_branches_k4 values vals_l_2 dp0_l_2 m1_2 mX_2 nvals i
             retval_2 retval_4 retval_5 0);
      [lia | exact PreH53 | exact PreH62 | exact PreH65 | exact PreH66 | exact PreH31
      | exact PreH23 | exact PreH19 | lia]. }
  assert (Hd0b : 0 + 1 <= n_pre).
  { pose proof (best0_value_bound__dp_body_branches_k4 values i (0 + 1) ltac:(lia) Hbest0).
    lia. }
  assert (Hd1b : 0 + 1 <= n_pre).
  { pose proof (best1_value_bound__dp_body_branches_k4 values i (0 + 1) ltac:(lia) Hbest1).
    lia. }
  assert (HDP : DP0Prefix values (replace_Znth i (0 + 1) dp0_l_2) (i + 1)).
  { apply (dp0prefix_step__dp_body_branches_k4 values dp0_l_2
             (replace_Znth i (0 + 1) dp0_l_2) i (0 + 1));
      [exact PreH62 | lia | exact Hkeep | exact Hnew | exact Hbest0]. }
  assert (Hdpb : forall k_4, 0 <= k_4 < i + 1 ->
            1 <= Znth k_4 (replace_Znth i (0 + 1) dp0_l_2) 0 <= n_pre).
  { intros k4 Hk4. destruct (Z.eq_dec k4 i) as [He | Hne].
    - subst k4. rewrite Hnew. lia.
    - rewrite (Hkeep k4 ltac:(lia)). apply PreH63. lia. }
  assert (HB0 : Bit0Model values vals_l_2 (replace_Znth i (0 + 1) dp0_l_2)
                  (MaxBitInsert m0_2 retval (0 + 1)) (i + 1) nvals).
  { apply (bit_model_insert__dp_body_branches_k4 values vals_l_2 dp0_l_2
             (replace_Znth i (0 + 1) dp0_l_2) m0_2 nvals i retval (0 + 1));
      [lia | exact Hsi | exact PreH64 | exact PreH34 | exact Hkeep | exact Hnew]. }
  assert (HB1 : Bit1Model values vals_l_2 (MaxBitInsert m1_2 retval_2 (0 + 1))
                  (i + 1) nvals).
  { apply (bit1_model_insert__dp_body_branches_k4 values vals_l_2 m1_2 nvals i retval_2
             (0 + 1));
      [lia | exact Hsi | exact PreH65 | exact PreH31 | exact Hbest1]. }
  assert (HBX : Bit0Model values vals_l_2 (replace_Znth i (0 + 1) dp0_l_2)
                  (MaxBitInsert mX_2 retval_6
                     (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)) (i + 1 - 1) nvals).
  { replace (i + 1 - 1) with (i - 1 + 1) by lia.
    apply (bit_model_insert__dp_body_branches_k4 values vals_l_2 dp0_l_2
             (replace_Znth i (0 + 1) dp0_l_2) mX_2 nvals (i - 1) retval_6
             (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0));
      [lia | exact Hsi | exact PreH66 | exact PreH5 | | reflexivity].
    intros j Hj. apply Hkeep. lia. }
  assert (HCP : ClampedPrefixMax (replace_Znth i (0 + 1) dp0_l_2) (i + 1) best0).
  { apply (clamped_step__dp_body_branches_k4 dp0_l_2 (replace_Znth i (0 + 1) dp0_l_2)
             i best0 (0 + 1) best0);
      [lia | exact PreH67 | exact Hkeep | exact Hnew | lia | lia]. }
  assert (HCB : ClampedBest1Upto values (i + 1) (0 + 1)).
  { apply (clamped_best1_step__dp_body_branches_k4 values i best1 (0 + 1) (0 + 1));
      [lia | exact PreH68 | exact Hbest1 | lia | lia]. }
  assert (HCPp : ClampedPrefixMax (replace_Znth i (0 + 1) dp0_l_2) (i + 1 - 1) best0_prefix).
  { replace (i + 1 - 1) with (i - 1 + 1) by lia.
    apply (clamped_keep_step__dp_body_branches_k4 dp0_l_2 (replace_Znth i (0 + 1) dp0_l_2)
             (i - 1) best0_prefix);
      [lia | exact PreH69 | | exact PreH1].
    intros j Hj. apply Hkeep. lia. }
  assert (Hm0L : Zlength m0_2 = nvals + 1) by (destruct PreH64 as [HH _]; exact HH).
  assert (Hm1L : Zlength m1_2 = nvals + 1) by (destruct PreH65 as [HH _]; exact HH).
  assert (HmXL : Zlength mX_2 = nvals + 1) by (destruct PreH66 as [HH _]; exact HH).
  assert (HmXv : 1 <= Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0 <= n_pre).
  { rewrite Hkeep1. apply PreH63. lia. }
  assert (Hmb : forall r, 0 <= r <= nvals ->
     (((-1000000000 <= Znth r (MaxBitInsert m0_2 retval (0 + 1)) 0 <= n_pre /\
        -1000000000 <= Znth r (MaxBitInsert m1_2 retval_2 (0 + 1)) 0) /\
       Znth r (MaxBitInsert m1_2 retval_2 (0 + 1)) 0 <= n_pre) /\
      -1000000000 <= Znth r (MaxBitInsert mX_2 retval_6
        (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)) 0) /\
     Znth r (MaxBitInsert mX_2 retval_6
        (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)) 0 <= n_pre).
  { intros r Hr.
    pose proof (maxbitinsert_bound__dp_body_branches_k4 m0_2 retval (0 + 1)
                  (-1000000000) n_pre nvals Hm0L ltac:(lia)
                  ltac:(intros q Hq; pose proof (PreH61 q Hq); lia) ltac:(lia) r Hr) as H0.
    pose proof (maxbitinsert_bound__dp_body_branches_k4 m1_2 retval_2 (0 + 1)
                  (-1000000000) n_pre nvals Hm1L ltac:(lia)
                  ltac:(intros q Hq; pose proof (PreH61 q Hq); lia) ltac:(lia) r Hr) as H1.
    pose proof (maxbitinsert_bound__dp_body_branches_k4 mX_2 retval_6
                  (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)
                  (-1000000000) n_pre nvals HmXL ltac:(lia)
                  ltac:(intros q Hq; pose proof (PreH61 q Hq); lia) ltac:(lia) r Hr) as H2.
    lia. }
  assert (Hbb : forall k_3, 0 <= k_3 < nvals + 1 ->
     (((-1000000000 <= Znth k_3 bit_l1 0 <= 1000000000 /\
        -1000000000 <= Znth k_3 bit_l1_2 0) /\
       Znth k_3 bit_l1_2 0 <= 1000000000) /\ -1000000000 <= Znth k_3 bit_l1_3 0) /\
      Znth k_3 bit_l1_3 0 <= 1000000000).
  { intros k3 Hk3. pose proof (PreH14 k3 Hk3). pose proof (PreH10 k3 Hk3).
    pose proof (PreH3 k3 Hk3). lia. }
  Exists (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_2 (0 + 1))
         (MaxBitInsert m0_2 retval (0 + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (0 + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - do 12 cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed.

Lemma proof_of_solver_entail_wit_12_49 : solver_entail_wit_12_49.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hlm0 : Zlength m0_2 = nvals + 1) by exact (proj1 PreH64).
  assert (Hlm1 : Zlength m1_2 = nvals + 1) by exact (proj1 PreH65).
  assert (HlmX : Zlength mX_2 = nvals + 1) by exact (proj1 PreH66).
  pose proof (dp_step_core__dp_body_branches_k5
                values vals_l_2 c_l_2 dp0_l_2 m0_2 m1_2 mX_2 nvals i
                retval_2 retval_3 retval_6 retval retval_4 retval_5
                (retval + 1) (retval_5 + 1)
                (replace_Znth i (retval + 1) dp0_l_2)
                ltac:(lia) ltac:(lia) PreH53
                ltac:(rewrite <- PreH40; exact PreH50)
                PreH62 PreH64 PreH65 PreH66 PreH34 PreH31 PreH5
                ltac:(lia) ltac:(lia) ltac:(lia)
                PreH28 PreH23 PreH19 ltac:(lia) ltac:(lia) eq_refl) as Hcore.
  destruct Hcore as [Hbest0 [Hbest1 [Hd0b [Hd1b [Hnew [Hagree [Hlen'
                    [Hdp' [Hm0' [Hm1' HmX']]]]]]]]]].
  assert (HdXv : Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0
                 = Znth (i - 1) dp0_l_2 0) by (apply Hagree; lia).
  assert (HdXb : 1 <= Znth (i - 1) dp0_l_2 0 <= n_pre) by (apply PreH63; lia).
  assert (HdpB : forall k_4 : Z, 0 <= k_4 < i + 1 ->
            1 <= Znth k_4 (replace_Znth i (retval + 1) dp0_l_2) 0 <= n_pre).
  { intros k Hk. destruct (Z.eq_dec k i) as [-> | Hne].
    - rewrite Hnew. lia.
    - rewrite Hagree by lia. apply PreH63; lia. }
  assert (Hbitb : forall k_3 : Z, 0 <= k_3 < nvals + 1 ->
            (((-1000000000 <= Znth k_3 bit_l1 0 <= 1000000000 /\
               -1000000000 <= Znth k_3 bit_l1_2 0) /\
              Znth k_3 bit_l1_2 0 <= 1000000000) /\
             -1000000000 <= Znth k_3 bit_l1_3 0) /\
            Znth k_3 bit_l1_3 0 <= 1000000000).
  { intros k Hk. pose proof (PreH14 k Hk). pose proof (PreH10 k Hk).
    pose proof (PreH3 k Hk). lia. }
  assert (Hmb : forall r : Z, 0 <= r <= nvals ->
            (((-1000000000 <=
               Znth r (MaxBitInsert m0_2 retval_2 (retval + 1)) 0 <= n_pre /\
               -1000000000 <=
               Znth r (MaxBitInsert m1_2 retval_3 (retval_5 + 1)) 0) /\
              Znth r (MaxBitInsert m1_2 retval_3 (retval_5 + 1)) 0 <= n_pre) /\
             -1000000000 <=
             Znth r (MaxBitInsert mX_2 retval_6
                       (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0)) 0) /\
            Znth r (MaxBitInsert mX_2 retval_6
                      (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0)) 0
            <= n_pre).
  { intros r Hr. pose proof (PreH61 r Hr) as Hb.
    pose proof (maxbitinsert_bounds__dp_body_branches_k5 m0_2 retval_2 (retval + 1) r
                  (-1000000000) n_pre ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as B0.
    pose proof (maxbitinsert_bounds__dp_body_branches_k5 m1_2 retval_3 (retval_5 + 1) r
                  (-1000000000) n_pre ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as B1.
    pose proof (maxbitinsert_bounds__dp_body_branches_k5 mX_2 retval_6
                  (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0) r
                  (-1000000000) n_pre ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as BX.
    lia. }
  assert (HmX2 : Bit0Model values vals_l_2 (replace_Znth i (retval + 1) dp0_l_2)
                   (MaxBitInsert mX_2 retval_6
                      (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0))
                   (i + 1 - 1) nvals).
  { replace (i + 1 - 1) with i by lia. exact HmX'. }
  assert (Hcp1 : ClampedPrefixMax (replace_Znth i (retval + 1) dp0_l_2)
                   (i + 1) (retval + 1)).
  { apply (clamped_step__dp_body_branches_k5 dp0_l_2
             (replace_Znth i (retval + 1) dp0_l_2) i best0 (retval + 1) (retval + 1)
             PreH67 Hagree Hnew ltac:(lia) ltac:(lia)).
    left. split; [reflexivity | lia]. }
  assert (Hcb1 : ClampedBest1Upto values (i + 1) best1).
  { apply (clamped_best1_step__dp_body_branches_k5 values i best1 (retval_5 + 1) best1
             PreH68 Hbest1 ltac:(lia) ltac:(lia)).
    right. split; [reflexivity | lia]. }
  assert (Hcp2 : ClampedPrefixMax (replace_Znth i (retval + 1) dp0_l_2)
                   (i + 1 - 1) best0_prefix).
  { replace (i + 1 - 1) with (i - 1 + 1) by lia.
    apply (clamped_step__dp_body_branches_k5 dp0_l_2
             (replace_Znth i (retval + 1) dp0_l_2) (i - 1) best0_prefix
             (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0) best0_prefix
             PreH69 ltac:(intros j Hj; apply Hagree; lia) eq_refl ltac:(lia) ltac:(lia)).
    right. split; [reflexivity | exact PreH1]. }
  assert (Hdpl : Zlength (replace_Znth i (retval + 1) dp0_l_2) = n_pre) by lia.
  Exists (MaxBitInsert mX_2 retval_6
            (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_3 (retval_5 + 1))
         (MaxBitInsert m0_2 retval_2 (retval + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (retval + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed.

Lemma proof_of_solver_entail_wit_12_50 : solver_entail_wit_12_50.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hlm0 : Zlength m0_2 = nvals + 1) by exact (proj1 PreH64).
  assert (Hlm1 : Zlength m1_2 = nvals + 1) by exact (proj1 PreH65).
  assert (HlmX : Zlength mX_2 = nvals + 1) by exact (proj1 PreH66).
  pose proof (dp_step_core__dp_body_branches_k5
                values vals_l_2 c_l_2 dp0_l_2 m0_2 m1_2 mX_2 nvals i
                retval retval_2 retval_6 retval_3 retval_4 retval_5
                (0 + 1) (retval_5 + 1)
                (replace_Znth i (0 + 1) dp0_l_2)
                ltac:(lia) ltac:(lia) PreH53
                ltac:(rewrite <- PreH40; exact PreH50)
                PreH62 PreH64 PreH65 PreH66 PreH34 PreH31 PreH5
                ltac:(lia) ltac:(lia) ltac:(lia)
                PreH28 PreH23 PreH19 ltac:(lia) ltac:(lia) eq_refl) as Hcore.
  destruct Hcore as [Hbest0 [Hbest1 [Hd0b [Hd1b [Hnew [Hagree [Hlen'
                    [Hdp' [Hm0' [Hm1' HmX']]]]]]]]]].
  assert (HdXv : Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0
                 = Znth (i - 1) dp0_l_2 0) by (apply Hagree; lia).
  assert (HdXb : 1 <= Znth (i - 1) dp0_l_2 0 <= n_pre) by (apply PreH63; lia).
  assert (HdpB : forall k_4 : Z, 0 <= k_4 < i + 1 ->
            1 <= Znth k_4 (replace_Znth i (0 + 1) dp0_l_2) 0 <= n_pre).
  { intros k Hk. destruct (Z.eq_dec k i) as [-> | Hne].
    - rewrite Hnew. lia.
    - rewrite Hagree by lia. apply PreH63; lia. }
  assert (Hbitb : forall k_3 : Z, 0 <= k_3 < nvals + 1 ->
            (((-1000000000 <= Znth k_3 bit_l1 0 <= 1000000000 /\
               -1000000000 <= Znth k_3 bit_l1_2 0) /\
              Znth k_3 bit_l1_2 0 <= 1000000000) /\
             -1000000000 <= Znth k_3 bit_l1_3 0) /\
            Znth k_3 bit_l1_3 0 <= 1000000000).
  { intros k Hk. pose proof (PreH14 k Hk). pose proof (PreH10 k Hk).
    pose proof (PreH3 k Hk). lia. }
  assert (Hmb : forall r : Z, 0 <= r <= nvals ->
            (((-1000000000 <=
               Znth r (MaxBitInsert m0_2 retval (0 + 1)) 0 <= n_pre /\
               -1000000000 <=
               Znth r (MaxBitInsert m1_2 retval_2 (retval_5 + 1)) 0) /\
              Znth r (MaxBitInsert m1_2 retval_2 (retval_5 + 1)) 0 <= n_pre) /\
             -1000000000 <=
             Znth r (MaxBitInsert mX_2 retval_6
                       (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)) 0) /\
            Znth r (MaxBitInsert mX_2 retval_6
                      (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)) 0
            <= n_pre).
  { intros r Hr. pose proof (PreH61 r Hr) as Hb.
    pose proof (maxbitinsert_bounds__dp_body_branches_k5 m0_2 retval (0 + 1) r
                  (-1000000000) n_pre ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as B0.
    pose proof (maxbitinsert_bounds__dp_body_branches_k5 m1_2 retval_2 (retval_5 + 1) r
                  (-1000000000) n_pre ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as B1.
    pose proof (maxbitinsert_bounds__dp_body_branches_k5 mX_2 retval_6
                  (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0) r
                  (-1000000000) n_pre ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as BX.
    lia. }
  assert (HmX2 : Bit0Model values vals_l_2 (replace_Znth i (0 + 1) dp0_l_2)
                   (MaxBitInsert mX_2 retval_6
                      (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0))
                   (i + 1 - 1) nvals).
  { replace (i + 1 - 1) with i by lia. exact HmX'. }
  assert (Hcp1 : ClampedPrefixMax (replace_Znth i (0 + 1) dp0_l_2)
                   (i + 1) (0 + 1)).
  { apply (clamped_step__dp_body_branches_k5 dp0_l_2
             (replace_Znth i (0 + 1) dp0_l_2) i best0 (0 + 1) (0 + 1)
             PreH67 Hagree Hnew ltac:(lia) ltac:(lia)).
    left. split; [reflexivity | lia]. }
  assert (Hcb1 : ClampedBest1Upto values (i + 1) best1).
  { apply (clamped_best1_step__dp_body_branches_k5 values i best1 (retval_5 + 1) best1
             PreH68 Hbest1 ltac:(lia) ltac:(lia)).
    right. split; [reflexivity | lia]. }
  assert (Hcp2 : ClampedPrefixMax (replace_Znth i (0 + 1) dp0_l_2)
                   (i + 1 - 1) best0_prefix).
  { replace (i + 1 - 1) with (i - 1 + 1) by lia.
    apply (clamped_step__dp_body_branches_k5 dp0_l_2
             (replace_Znth i (0 + 1) dp0_l_2) (i - 1) best0_prefix
             (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0) best0_prefix
             PreH69 ltac:(intros j Hj; apply Hagree; lia) eq_refl ltac:(lia) ltac:(lia)).
    right. split; [reflexivity | exact PreH1]. }
  assert (Hdpl : Zlength (replace_Znth i (0 + 1) dp0_l_2) = n_pre) by lia.
  Exists (MaxBitInsert mX_2 retval_6
            (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_2 (retval_5 + 1))
         (MaxBitInsert m0_2 retval (0 + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (0 + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed.

Lemma proof_of_solver_entail_wit_12_51 : solver_entail_wit_12_51.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hlm0 : Zlength m0_2 = nvals + 1) by exact (proj1 PreH64).
  assert (Hlm1 : Zlength m1_2 = nvals + 1) by exact (proj1 PreH65).
  assert (HlmX : Zlength mX_2 = nvals + 1) by exact (proj1 PreH66).
  pose proof (dp_step_core__dp_body_branches_k5
                values vals_l_2 c_l_2 dp0_l_2 m0_2 m1_2 mX_2 nvals i
                retval_2 retval_3 retval_6 retval retval_4 retval_5
                (retval + 1) (retval_5 + 1)
                (replace_Znth i (retval + 1) dp0_l_2)
                ltac:(lia) ltac:(lia) PreH53
                ltac:(rewrite <- PreH40; exact PreH50)
                PreH62 PreH64 PreH65 PreH66 PreH34 PreH31 PreH5
                ltac:(lia) ltac:(lia) ltac:(lia)
                PreH28 PreH23 PreH19 ltac:(lia) ltac:(lia) eq_refl) as Hcore.
  destruct Hcore as [Hbest0 [Hbest1 [Hd0b [Hd1b [Hnew [Hagree [Hlen'
                    [Hdp' [Hm0' [Hm1' HmX']]]]]]]]]].
  assert (HdXv : Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0
                 = Znth (i - 1) dp0_l_2 0) by (apply Hagree; lia).
  assert (HdXb : 1 <= Znth (i - 1) dp0_l_2 0 <= n_pre) by (apply PreH63; lia).
  assert (HdpB : forall k_4 : Z, 0 <= k_4 < i + 1 ->
            1 <= Znth k_4 (replace_Znth i (retval + 1) dp0_l_2) 0 <= n_pre).
  { intros k Hk. destruct (Z.eq_dec k i) as [-> | Hne].
    - rewrite Hnew. lia.
    - rewrite Hagree by lia. apply PreH63; lia. }
  assert (Hbitb : forall k_3 : Z, 0 <= k_3 < nvals + 1 ->
            (((-1000000000 <= Znth k_3 bit_l1 0 <= 1000000000 /\
               -1000000000 <= Znth k_3 bit_l1_2 0) /\
              Znth k_3 bit_l1_2 0 <= 1000000000) /\
             -1000000000 <= Znth k_3 bit_l1_3 0) /\
            Znth k_3 bit_l1_3 0 <= 1000000000).
  { intros k Hk. pose proof (PreH14 k Hk). pose proof (PreH10 k Hk).
    pose proof (PreH3 k Hk). lia. }
  assert (Hmb : forall r : Z, 0 <= r <= nvals ->
            (((-1000000000 <=
               Znth r (MaxBitInsert m0_2 retval_2 (retval + 1)) 0 <= n_pre /\
               -1000000000 <=
               Znth r (MaxBitInsert m1_2 retval_3 (retval_5 + 1)) 0) /\
              Znth r (MaxBitInsert m1_2 retval_3 (retval_5 + 1)) 0 <= n_pre) /\
             -1000000000 <=
             Znth r (MaxBitInsert mX_2 retval_6
                       (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0)) 0) /\
            Znth r (MaxBitInsert mX_2 retval_6
                      (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0)) 0
            <= n_pre).
  { intros r Hr. pose proof (PreH61 r Hr) as Hb.
    pose proof (maxbitinsert_bounds__dp_body_branches_k5 m0_2 retval_2 (retval + 1) r
                  (-1000000000) n_pre ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as B0.
    pose proof (maxbitinsert_bounds__dp_body_branches_k5 m1_2 retval_3 (retval_5 + 1) r
                  (-1000000000) n_pre ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as B1.
    pose proof (maxbitinsert_bounds__dp_body_branches_k5 mX_2 retval_6
                  (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0) r
                  (-1000000000) n_pre ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as BX.
    lia. }
  assert (HmX2 : Bit0Model values vals_l_2 (replace_Znth i (retval + 1) dp0_l_2)
                   (MaxBitInsert mX_2 retval_6
                      (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0))
                   (i + 1 - 1) nvals).
  { replace (i + 1 - 1) with i by lia. exact HmX'. }
  assert (Hcp1 : ClampedPrefixMax (replace_Znth i (retval + 1) dp0_l_2)
                   (i + 1) (retval + 1)).
  { apply (clamped_step__dp_body_branches_k5 dp0_l_2
             (replace_Znth i (retval + 1) dp0_l_2) i best0 (retval + 1) (retval + 1)
             PreH67 Hagree Hnew ltac:(lia) ltac:(lia)).
    left. split; [reflexivity | lia]. }
  assert (Hcb1 : ClampedBest1Upto values (i + 1) best1).
  { apply (clamped_best1_step__dp_body_branches_k5 values i best1 (retval_5 + 1) best1
             PreH68 Hbest1 ltac:(lia) ltac:(lia)).
    right. split; [reflexivity | lia]. }
  assert (Hcp2 : ClampedPrefixMax (replace_Znth i (retval + 1) dp0_l_2)
                   (i + 1 - 1) best0_prefix).
  { replace (i + 1 - 1) with (i - 1 + 1) by lia.
    apply (clamped_step__dp_body_branches_k5 dp0_l_2
             (replace_Znth i (retval + 1) dp0_l_2) (i - 1) best0_prefix
             (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0) best0_prefix
             PreH69 ltac:(intros j Hj; apply Hagree; lia) eq_refl ltac:(lia) ltac:(lia)).
    right. split; [reflexivity | exact PreH1]. }
  assert (Hdpl : Zlength (replace_Znth i (retval + 1) dp0_l_2) = n_pre) by lia.
  Exists (MaxBitInsert mX_2 retval_6
            (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_3 (retval_5 + 1))
         (MaxBitInsert m0_2 retval_2 (retval + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (retval + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed.

Lemma proof_of_solver_entail_wit_12_52 : solver_entail_wit_12_52.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hlm0 : Zlength m0_2 = nvals + 1) by exact (proj1 PreH64).
  assert (Hlm1 : Zlength m1_2 = nvals + 1) by exact (proj1 PreH65).
  assert (HlmX : Zlength mX_2 = nvals + 1) by exact (proj1 PreH66).
  pose proof (dp_step_core__dp_body_branches_k5
                values vals_l_2 c_l_2 dp0_l_2 m0_2 m1_2 mX_2 nvals i
                retval retval_2 retval_6 retval_3 retval_4 retval_5
                (0 + 1) (retval_5 + 1)
                (replace_Znth i (0 + 1) dp0_l_2)
                ltac:(lia) ltac:(lia) PreH53
                ltac:(rewrite <- PreH40; exact PreH50)
                PreH62 PreH64 PreH65 PreH66 PreH34 PreH31 PreH5
                ltac:(lia) ltac:(lia) ltac:(lia)
                PreH28 PreH23 PreH19 ltac:(lia) ltac:(lia) eq_refl) as Hcore.
  destruct Hcore as [Hbest0 [Hbest1 [Hd0b [Hd1b [Hnew [Hagree [Hlen'
                    [Hdp' [Hm0' [Hm1' HmX']]]]]]]]]].
  assert (HdXv : Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0
                 = Znth (i - 1) dp0_l_2 0) by (apply Hagree; lia).
  assert (HdXb : 1 <= Znth (i - 1) dp0_l_2 0 <= n_pre) by (apply PreH63; lia).
  assert (HdpB : forall k_4 : Z, 0 <= k_4 < i + 1 ->
            1 <= Znth k_4 (replace_Znth i (0 + 1) dp0_l_2) 0 <= n_pre).
  { intros k Hk. destruct (Z.eq_dec k i) as [-> | Hne].
    - rewrite Hnew. lia.
    - rewrite Hagree by lia. apply PreH63; lia. }
  assert (Hbitb : forall k_3 : Z, 0 <= k_3 < nvals + 1 ->
            (((-1000000000 <= Znth k_3 bit_l1 0 <= 1000000000 /\
               -1000000000 <= Znth k_3 bit_l1_2 0) /\
              Znth k_3 bit_l1_2 0 <= 1000000000) /\
             -1000000000 <= Znth k_3 bit_l1_3 0) /\
            Znth k_3 bit_l1_3 0 <= 1000000000).
  { intros k Hk. pose proof (PreH14 k Hk). pose proof (PreH10 k Hk).
    pose proof (PreH3 k Hk). lia. }
  assert (Hmb : forall r : Z, 0 <= r <= nvals ->
            (((-1000000000 <=
               Znth r (MaxBitInsert m0_2 retval (0 + 1)) 0 <= n_pre /\
               -1000000000 <=
               Znth r (MaxBitInsert m1_2 retval_2 (retval_5 + 1)) 0) /\
              Znth r (MaxBitInsert m1_2 retval_2 (retval_5 + 1)) 0 <= n_pre) /\
             -1000000000 <=
             Znth r (MaxBitInsert mX_2 retval_6
                       (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)) 0) /\
            Znth r (MaxBitInsert mX_2 retval_6
                      (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)) 0
            <= n_pre).
  { intros r Hr. pose proof (PreH61 r Hr) as Hb.
    pose proof (maxbitinsert_bounds__dp_body_branches_k5 m0_2 retval (0 + 1) r
                  (-1000000000) n_pre ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as B0.
    pose proof (maxbitinsert_bounds__dp_body_branches_k5 m1_2 retval_2 (retval_5 + 1) r
                  (-1000000000) n_pre ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as B1.
    pose proof (maxbitinsert_bounds__dp_body_branches_k5 mX_2 retval_6
                  (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0) r
                  (-1000000000) n_pre ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as BX.
    lia. }
  assert (HmX2 : Bit0Model values vals_l_2 (replace_Znth i (0 + 1) dp0_l_2)
                   (MaxBitInsert mX_2 retval_6
                      (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0))
                   (i + 1 - 1) nvals).
  { replace (i + 1 - 1) with i by lia. exact HmX'. }
  assert (Hcp1 : ClampedPrefixMax (replace_Znth i (0 + 1) dp0_l_2)
                   (i + 1) (0 + 1)).
  { apply (clamped_step__dp_body_branches_k5 dp0_l_2
             (replace_Znth i (0 + 1) dp0_l_2) i best0 (0 + 1) (0 + 1)
             PreH67 Hagree Hnew ltac:(lia) ltac:(lia)).
    left. split; [reflexivity | lia]. }
  assert (Hcb1 : ClampedBest1Upto values (i + 1) best1).
  { apply (clamped_best1_step__dp_body_branches_k5 values i best1 (retval_5 + 1) best1
             PreH68 Hbest1 ltac:(lia) ltac:(lia)).
    right. split; [reflexivity | lia]. }
  assert (Hcp2 : ClampedPrefixMax (replace_Znth i (0 + 1) dp0_l_2)
                   (i + 1 - 1) best0_prefix).
  { replace (i + 1 - 1) with (i - 1 + 1) by lia.
    apply (clamped_step__dp_body_branches_k5 dp0_l_2
             (replace_Znth i (0 + 1) dp0_l_2) (i - 1) best0_prefix
             (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0) best0_prefix
             PreH69 ltac:(intros j Hj; apply Hagree; lia) eq_refl ltac:(lia) ltac:(lia)).
    right. split; [reflexivity | exact PreH1]. }
  assert (Hdpl : Zlength (replace_Znth i (0 + 1) dp0_l_2) = n_pre) by lia.
  Exists (MaxBitInsert mX_2 retval_6
            (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_2 (retval_5 + 1))
         (MaxBitInsert m0_2 retval (0 + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (0 + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed.

Lemma proof_of_solver_entail_wit_12_53 : solver_entail_wit_12_53.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hlm0 : Zlength m0_2 = nvals + 1) by exact (proj1 PreH64).
  assert (Hlm1 : Zlength m1_2 = nvals + 1) by exact (proj1 PreH65).
  assert (HlmX : Zlength mX_2 = nvals + 1) by exact (proj1 PreH66).
  pose proof (dp_step_core__dp_body_branches_k5
                values vals_l_2 c_l_2 dp0_l_2 m0_2 m1_2 mX_2 nvals i
                retval_2 retval_3 retval_6 retval retval_4 retval_5
                (retval + 1) (retval_4 + 1)
                (replace_Znth i (retval + 1) dp0_l_2)
                ltac:(lia) ltac:(lia) PreH53
                ltac:(rewrite <- PreH40; exact PreH50)
                PreH62 PreH64 PreH65 PreH66 PreH34 PreH31 PreH5
                ltac:(lia) ltac:(lia) ltac:(lia)
                PreH28 PreH23 PreH19 ltac:(lia) ltac:(lia) eq_refl) as Hcore.
  destruct Hcore as [Hbest0 [Hbest1 [Hd0b [Hd1b [Hnew [Hagree [Hlen'
                    [Hdp' [Hm0' [Hm1' HmX']]]]]]]]]].
  assert (HdXv : Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0
                 = Znth (i - 1) dp0_l_2 0) by (apply Hagree; lia).
  assert (HdXb : 1 <= Znth (i - 1) dp0_l_2 0 <= n_pre) by (apply PreH63; lia).
  assert (HdpB : forall k_4 : Z, 0 <= k_4 < i + 1 ->
            1 <= Znth k_4 (replace_Znth i (retval + 1) dp0_l_2) 0 <= n_pre).
  { intros k Hk. destruct (Z.eq_dec k i) as [-> | Hne].
    - rewrite Hnew. lia.
    - rewrite Hagree by lia. apply PreH63; lia. }
  assert (Hbitb : forall k_3 : Z, 0 <= k_3 < nvals + 1 ->
            (((-1000000000 <= Znth k_3 bit_l1 0 <= 1000000000 /\
               -1000000000 <= Znth k_3 bit_l1_2 0) /\
              Znth k_3 bit_l1_2 0 <= 1000000000) /\
             -1000000000 <= Znth k_3 bit_l1_3 0) /\
            Znth k_3 bit_l1_3 0 <= 1000000000).
  { intros k Hk. pose proof (PreH14 k Hk). pose proof (PreH10 k Hk).
    pose proof (PreH3 k Hk). lia. }
  assert (Hmb : forall r : Z, 0 <= r <= nvals ->
            (((-1000000000 <=
               Znth r (MaxBitInsert m0_2 retval_2 (retval + 1)) 0 <= n_pre /\
               -1000000000 <=
               Znth r (MaxBitInsert m1_2 retval_3 (retval_4 + 1)) 0) /\
              Znth r (MaxBitInsert m1_2 retval_3 (retval_4 + 1)) 0 <= n_pre) /\
             -1000000000 <=
             Znth r (MaxBitInsert mX_2 retval_6
                       (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0)) 0) /\
            Znth r (MaxBitInsert mX_2 retval_6
                      (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0)) 0
            <= n_pre).
  { intros r Hr. pose proof (PreH61 r Hr) as Hb.
    pose proof (maxbitinsert_bounds__dp_body_branches_k5 m0_2 retval_2 (retval + 1) r
                  (-1000000000) n_pre ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as B0.
    pose proof (maxbitinsert_bounds__dp_body_branches_k5 m1_2 retval_3 (retval_4 + 1) r
                  (-1000000000) n_pre ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as B1.
    pose proof (maxbitinsert_bounds__dp_body_branches_k5 mX_2 retval_6
                  (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0) r
                  (-1000000000) n_pre ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as BX.
    lia. }
  assert (HmX2 : Bit0Model values vals_l_2 (replace_Znth i (retval + 1) dp0_l_2)
                   (MaxBitInsert mX_2 retval_6
                      (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0))
                   (i + 1 - 1) nvals).
  { replace (i + 1 - 1) with i by lia. exact HmX'. }
  assert (Hcp1 : ClampedPrefixMax (replace_Znth i (retval + 1) dp0_l_2)
                   (i + 1) (retval + 1)).
  { apply (clamped_step__dp_body_branches_k5 dp0_l_2
             (replace_Znth i (retval + 1) dp0_l_2) i best0 (retval + 1) (retval + 1)
             PreH67 Hagree Hnew ltac:(lia) ltac:(lia)).
    left. split; [reflexivity | lia]. }
  assert (Hcb1 : ClampedBest1Upto values (i + 1) best1).
  { apply (clamped_best1_step__dp_body_branches_k5 values i best1 (retval_4 + 1) best1
             PreH68 Hbest1 ltac:(lia) ltac:(lia)).
    right. split; [reflexivity | lia]. }
  assert (Hcp2 : ClampedPrefixMax (replace_Znth i (retval + 1) dp0_l_2)
                   (i + 1 - 1) best0_prefix).
  { replace (i + 1 - 1) with (i - 1 + 1) by lia.
    apply (clamped_step__dp_body_branches_k5 dp0_l_2
             (replace_Znth i (retval + 1) dp0_l_2) (i - 1) best0_prefix
             (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0) best0_prefix
             PreH69 ltac:(intros j Hj; apply Hagree; lia) eq_refl ltac:(lia) ltac:(lia)).
    right. split; [reflexivity | exact PreH1]. }
  assert (Hdpl : Zlength (replace_Znth i (retval + 1) dp0_l_2) = n_pre) by lia.
  Exists (MaxBitInsert mX_2 retval_6
            (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_3 (retval_4 + 1))
         (MaxBitInsert m0_2 retval_2 (retval + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (retval + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed.

Lemma proof_of_solver_entail_wit_12_54 : solver_entail_wit_12_54.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hlm0 : Zlength m0_2 = nvals + 1) by exact (proj1 PreH64).
  assert (Hlm1 : Zlength m1_2 = nvals + 1) by exact (proj1 PreH65).
  assert (HlmX : Zlength mX_2 = nvals + 1) by exact (proj1 PreH66).
  pose proof (dp_step_core__dp_body_branches_k5
                values vals_l_2 c_l_2 dp0_l_2 m0_2 m1_2 mX_2 nvals i
                retval retval_2 retval_6 retval_3 retval_4 retval_5
                (0 + 1) (retval_4 + 1)
                (replace_Znth i (0 + 1) dp0_l_2)
                ltac:(lia) ltac:(lia) PreH53
                ltac:(rewrite <- PreH40; exact PreH50)
                PreH62 PreH64 PreH65 PreH66 PreH34 PreH31 PreH5
                ltac:(lia) ltac:(lia) ltac:(lia)
                PreH28 PreH23 PreH19 ltac:(lia) ltac:(lia) eq_refl) as Hcore.
  destruct Hcore as [Hbest0 [Hbest1 [Hd0b [Hd1b [Hnew [Hagree [Hlen'
                    [Hdp' [Hm0' [Hm1' HmX']]]]]]]]]].
  assert (HdXv : Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0
                 = Znth (i - 1) dp0_l_2 0) by (apply Hagree; lia).
  assert (HdXb : 1 <= Znth (i - 1) dp0_l_2 0 <= n_pre) by (apply PreH63; lia).
  assert (HdpB : forall k_4 : Z, 0 <= k_4 < i + 1 ->
            1 <= Znth k_4 (replace_Znth i (0 + 1) dp0_l_2) 0 <= n_pre).
  { intros k Hk. destruct (Z.eq_dec k i) as [-> | Hne].
    - rewrite Hnew. lia.
    - rewrite Hagree by lia. apply PreH63; lia. }
  assert (Hbitb : forall k_3 : Z, 0 <= k_3 < nvals + 1 ->
            (((-1000000000 <= Znth k_3 bit_l1 0 <= 1000000000 /\
               -1000000000 <= Znth k_3 bit_l1_2 0) /\
              Znth k_3 bit_l1_2 0 <= 1000000000) /\
             -1000000000 <= Znth k_3 bit_l1_3 0) /\
            Znth k_3 bit_l1_3 0 <= 1000000000).
  { intros k Hk. pose proof (PreH14 k Hk). pose proof (PreH10 k Hk).
    pose proof (PreH3 k Hk). lia. }
  assert (Hmb : forall r : Z, 0 <= r <= nvals ->
            (((-1000000000 <=
               Znth r (MaxBitInsert m0_2 retval (0 + 1)) 0 <= n_pre /\
               -1000000000 <=
               Znth r (MaxBitInsert m1_2 retval_2 (retval_4 + 1)) 0) /\
              Znth r (MaxBitInsert m1_2 retval_2 (retval_4 + 1)) 0 <= n_pre) /\
             -1000000000 <=
             Znth r (MaxBitInsert mX_2 retval_6
                       (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)) 0) /\
            Znth r (MaxBitInsert mX_2 retval_6
                      (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)) 0
            <= n_pre).
  { intros r Hr. pose proof (PreH61 r Hr) as Hb.
    pose proof (maxbitinsert_bounds__dp_body_branches_k5 m0_2 retval (0 + 1) r
                  (-1000000000) n_pre ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as B0.
    pose proof (maxbitinsert_bounds__dp_body_branches_k5 m1_2 retval_2 (retval_4 + 1) r
                  (-1000000000) n_pre ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as B1.
    pose proof (maxbitinsert_bounds__dp_body_branches_k5 mX_2 retval_6
                  (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0) r
                  (-1000000000) n_pre ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as BX.
    lia. }
  assert (HmX2 : Bit0Model values vals_l_2 (replace_Znth i (0 + 1) dp0_l_2)
                   (MaxBitInsert mX_2 retval_6
                      (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0))
                   (i + 1 - 1) nvals).
  { replace (i + 1 - 1) with i by lia. exact HmX'. }
  assert (Hcp1 : ClampedPrefixMax (replace_Znth i (0 + 1) dp0_l_2)
                   (i + 1) (0 + 1)).
  { apply (clamped_step__dp_body_branches_k5 dp0_l_2
             (replace_Znth i (0 + 1) dp0_l_2) i best0 (0 + 1) (0 + 1)
             PreH67 Hagree Hnew ltac:(lia) ltac:(lia)).
    left. split; [reflexivity | lia]. }
  assert (Hcb1 : ClampedBest1Upto values (i + 1) best1).
  { apply (clamped_best1_step__dp_body_branches_k5 values i best1 (retval_4 + 1) best1
             PreH68 Hbest1 ltac:(lia) ltac:(lia)).
    right. split; [reflexivity | lia]. }
  assert (Hcp2 : ClampedPrefixMax (replace_Znth i (0 + 1) dp0_l_2)
                   (i + 1 - 1) best0_prefix).
  { replace (i + 1 - 1) with (i - 1 + 1) by lia.
    apply (clamped_step__dp_body_branches_k5 dp0_l_2
             (replace_Znth i (0 + 1) dp0_l_2) (i - 1) best0_prefix
             (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0) best0_prefix
             PreH69 ltac:(intros j Hj; apply Hagree; lia) eq_refl ltac:(lia) ltac:(lia)).
    right. split; [reflexivity | exact PreH1]. }
  assert (Hdpl : Zlength (replace_Znth i (0 + 1) dp0_l_2) = n_pre) by lia.
  Exists (MaxBitInsert mX_2 retval_6
            (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_2 (retval_4 + 1))
         (MaxBitInsert m0_2 retval (0 + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (0 + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed.

Lemma proof_of_solver_entail_wit_12_55 : solver_entail_wit_12_55.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hlm0 : Zlength m0_2 = nvals + 1) by exact (proj1 PreH64).
  assert (Hlm1 : Zlength m1_2 = nvals + 1) by exact (proj1 PreH65).
  assert (HlmX : Zlength mX_2 = nvals + 1) by exact (proj1 PreH66).
  pose proof (dp_step_core__dp_body_branches_k5
                values vals_l_2 c_l_2 dp0_l_2 m0_2 m1_2 mX_2 nvals i
                retval_2 retval_3 retval_6 retval retval_4 retval_5
                (retval + 1) (0 + 1)
                (replace_Znth i (retval + 1) dp0_l_2)
                ltac:(lia) ltac:(lia) PreH53
                ltac:(rewrite <- PreH40; exact PreH50)
                PreH62 PreH64 PreH65 PreH66 PreH34 PreH31 PreH5
                ltac:(lia) ltac:(lia) ltac:(lia)
                PreH28 PreH23 PreH19 ltac:(lia) ltac:(lia) eq_refl) as Hcore.
  destruct Hcore as [Hbest0 [Hbest1 [Hd0b [Hd1b [Hnew [Hagree [Hlen'
                    [Hdp' [Hm0' [Hm1' HmX']]]]]]]]]].
  assert (HdXv : Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0
                 = Znth (i - 1) dp0_l_2 0) by (apply Hagree; lia).
  assert (HdXb : 1 <= Znth (i - 1) dp0_l_2 0 <= n_pre) by (apply PreH63; lia).
  assert (HdpB : forall k_4 : Z, 0 <= k_4 < i + 1 ->
            1 <= Znth k_4 (replace_Znth i (retval + 1) dp0_l_2) 0 <= n_pre).
  { intros k Hk. destruct (Z.eq_dec k i) as [-> | Hne].
    - rewrite Hnew. lia.
    - rewrite Hagree by lia. apply PreH63; lia. }
  assert (Hbitb : forall k_3 : Z, 0 <= k_3 < nvals + 1 ->
            (((-1000000000 <= Znth k_3 bit_l1 0 <= 1000000000 /\
               -1000000000 <= Znth k_3 bit_l1_2 0) /\
              Znth k_3 bit_l1_2 0 <= 1000000000) /\
             -1000000000 <= Znth k_3 bit_l1_3 0) /\
            Znth k_3 bit_l1_3 0 <= 1000000000).
  { intros k Hk. pose proof (PreH14 k Hk). pose proof (PreH10 k Hk).
    pose proof (PreH3 k Hk). lia. }
  assert (Hmb : forall r : Z, 0 <= r <= nvals ->
            (((-1000000000 <=
               Znth r (MaxBitInsert m0_2 retval_2 (retval + 1)) 0 <= n_pre /\
               -1000000000 <=
               Znth r (MaxBitInsert m1_2 retval_3 (0 + 1)) 0) /\
              Znth r (MaxBitInsert m1_2 retval_3 (0 + 1)) 0 <= n_pre) /\
             -1000000000 <=
             Znth r (MaxBitInsert mX_2 retval_6
                       (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0)) 0) /\
            Znth r (MaxBitInsert mX_2 retval_6
                      (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0)) 0
            <= n_pre).
  { intros r Hr. pose proof (PreH61 r Hr) as Hb.
    pose proof (maxbitinsert_bounds__dp_body_branches_k5 m0_2 retval_2 (retval + 1) r
                  (-1000000000) n_pre ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as B0.
    pose proof (maxbitinsert_bounds__dp_body_branches_k5 m1_2 retval_3 (0 + 1) r
                  (-1000000000) n_pre ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as B1.
    pose proof (maxbitinsert_bounds__dp_body_branches_k5 mX_2 retval_6
                  (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0) r
                  (-1000000000) n_pre ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as BX.
    lia. }
  assert (HmX2 : Bit0Model values vals_l_2 (replace_Znth i (retval + 1) dp0_l_2)
                   (MaxBitInsert mX_2 retval_6
                      (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0))
                   (i + 1 - 1) nvals).
  { replace (i + 1 - 1) with i by lia. exact HmX'. }
  assert (Hcp1 : ClampedPrefixMax (replace_Znth i (retval + 1) dp0_l_2)
                   (i + 1) (retval + 1)).
  { apply (clamped_step__dp_body_branches_k5 dp0_l_2
             (replace_Znth i (retval + 1) dp0_l_2) i best0 (retval + 1) (retval + 1)
             PreH67 Hagree Hnew ltac:(lia) ltac:(lia)).
    left. split; [reflexivity | lia]. }
  assert (Hcb1 : ClampedBest1Upto values (i + 1) best1).
  { apply (clamped_best1_step__dp_body_branches_k5 values i best1 (0 + 1) best1
             PreH68 Hbest1 ltac:(lia) ltac:(lia)).
    right. split; [reflexivity | lia]. }
  assert (Hcp2 : ClampedPrefixMax (replace_Znth i (retval + 1) dp0_l_2)
                   (i + 1 - 1) best0_prefix).
  { replace (i + 1 - 1) with (i - 1 + 1) by lia.
    apply (clamped_step__dp_body_branches_k5 dp0_l_2
             (replace_Znth i (retval + 1) dp0_l_2) (i - 1) best0_prefix
             (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0) best0_prefix
             PreH69 ltac:(intros j Hj; apply Hagree; lia) eq_refl ltac:(lia) ltac:(lia)).
    right. split; [reflexivity | exact PreH1]. }
  assert (Hdpl : Zlength (replace_Znth i (retval + 1) dp0_l_2) = n_pre) by lia.
  Exists (MaxBitInsert mX_2 retval_6
            (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_3 (0 + 1))
         (MaxBitInsert m0_2 retval_2 (retval + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (retval + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed.
