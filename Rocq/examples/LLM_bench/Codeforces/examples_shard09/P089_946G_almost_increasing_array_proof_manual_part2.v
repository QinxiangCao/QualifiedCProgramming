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



Lemma proof_of_solver_entail_wit_12_8 : solver_entail_wit_12_8.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hci : Znth i c_l_2 0 = KeyAt values i) by (apply PreH50; lia).
  assert (Hcim : Znth (i - 1) c_l_2 0 = KeyAt values (i - 1)) by (apply PreH50; lia).
  rewrite Hci in PreH34, PreH31.
  rewrite Hcim in PreH5.
  assert (Hsi : StrictIncPrefix vals_l_2 nvals) by (destruct PreH53 as [Hs _]; exact Hs).
  assert (Hlm0 : Zlength m0_2 = nvals + 1) by (destruct PreH64 as [Hz _]; exact Hz).
  assert (Hlm1 : Zlength m1_2 = nvals + 1) by (destruct PreH65 as [Hz _]; exact Hz).
  assert (HlmX : Zlength mX_2 = nvals + 1) by (destruct PreH66 as [Hz _]; exact Hz).
  assert (Hdpi : Znth i (replace_Znth i (0 + 1) dp0_l_2) 0 = 0 + 1)
    by (apply Znth_replace_Znth_Same; lia).
  assert (Hdpj : forall j, 0 <= j < n_pre -> j <> i ->
                 Znth j (replace_Znth i (0 + 1) dp0_l_2) 0 = Znth j dp0_l_2 0)
    by (intros j Hj Hne; apply Znth_replace_Znth_Diff; lia).
  assert (Hdpim : Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0
                  = Znth (i - 1) dp0_l_2 0) by (apply Hdpj; lia).
  assert (Hdpimb : 1 <= Znth (i - 1) dp0_l_2 0 <= n_pre) by (apply PreH63; lia).
  assert (HB0 : Best0EndingAt values i (0 + 1)).
  { replace (0 + 1) with (Z.max retval_3 0 + 1) by lia.
    apply (best0_step__dp_body_branches_k1 values vals_l_2 dp0_l_2 m0_2 i nvals retval retval_3);
      [lia | exact PreH53 | exact PreH62 | exact PreH64 | exact PreH34 | lia | exact PreH28]. }
  assert (HB1v : Best1EndingAt values i (0 + 1)).
  { replace (0 + 1) with (Z.max (Z.max retval_4 retval_5) 0 + 1) by lia.
    apply (best1_step__dp_body_branches_k1 values vals_l_2 dp0_l_2 m1_2 mX_2 i nvals retval_2 retval_4 retval_5);
      [lia | exact PreH53 | exact PreH62 | exact PreH65 | exact PreH66 | exact PreH31 | lia
      | exact PreH23 | exact PreH19]. }
  pose proof (best0_val_bound__dp_body_branches_k1 values i (0 + 1) HB0 ltac:(lia)) as Hb0b.
  pose proof (best1_val_bound__dp_body_branches_k1 values i (0 + 1) HB1v ltac:(lia)) as Hb1b.
  Exists (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_2 (0 + 1))
         (MaxBitInsert m0_2 retval (0 + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (0 + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    + lia.
    + lia.
    + lia.
    + exact PreH41.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + rewrite zlength_replace__dp_body_branches_k1. lia.
    + exact PreH50.
    + exact PreH51.
    + exact PreH52.
    + exact PreH53.
    + intros k3 Hk3. pose proof (PreH14 k3 Hk3). pose proof (PreH10 k3 Hk3).
      pose proof (PreH3 k3 Hk3). lia.
    + lia.
    + lia.
    + lia.
    + exact PreH15.
    + exact PreH11.
    + exact PreH4.
    + intros r Hr.
      assert (H0 : Znth r (MaxBitInsert m0_2 retval (0 + 1)) 0
                     = Z.max (Znth r m0_2 0) (0 + 1)
                   \/ Znth r (MaxBitInsert m0_2 retval (0 + 1)) 0 = Znth r m0_2 0).
      { destruct (Z.eq_dec r retval) as [He | Hne].
        - left. rewrite He. apply maxbitinsert_same__dp_body_branches_k1. lia.
        - right. apply maxbitinsert_diff__dp_body_branches_k1; lia. }
      assert (H1 : Znth r (MaxBitInsert m1_2 retval_2 (0 + 1)) 0
                     = Z.max (Znth r m1_2 0) (0 + 1)
                   \/ Znth r (MaxBitInsert m1_2 retval_2 (0 + 1)) 0 = Znth r m1_2 0).
      { destruct (Z.eq_dec r retval_2) as [He | Hne].
        - left. rewrite He. apply maxbitinsert_same__dp_body_branches_k1. lia.
        - right. apply maxbitinsert_diff__dp_body_branches_k1; lia. }
      assert (HX : Znth r (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)) 0
                     = Z.max (Znth r mX_2 0) (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)
                   \/ Znth r (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)) 0
                     = Znth r mX_2 0).
      { destruct (Z.eq_dec r retval_6) as [He | Hne].
        - left. rewrite He. apply maxbitinsert_same__dp_body_branches_k1. lia.
        - right. apply maxbitinsert_diff__dp_body_branches_k1; lia. }
      pose proof (PreH61 r Hr). lia.
    + intros j Hj. destruct (Z.eq_dec j i) as [He | Hne].
      * rewrite He. rewrite Hdpi. exact HB0.
      * rewrite Hdpj by lia. apply PreH62; lia.
    + intros k4 Hk4. destruct (Z.eq_dec k4 i) as [He | Hne].
      * rewrite He. rewrite Hdpi. lia.
      * rewrite Hdpj by lia. apply PreH63; lia.
    + apply (bit0_model_insert__dp_body_branches_k1 values vals_l_2 dp0_l_2
               (replace_Znth i (0 + 1) dp0_l_2) m0_2 i nvals retval (0 + 1));
        [exact PreH64 | exact Hsi | lia | intros j Hj; apply Hdpj; lia | exact Hdpi
        | exact PreH34 | lia | unfold MaxBitNeg; lia].
    + apply (bit1_model_insert__dp_body_branches_k1 values vals_l_2 m1_2 i nvals retval_2 (0 + 1));
        [exact PreH65 | exact Hsi | lia | exact PreH31 | lia | exact HB1v
        | unfold MaxBitNeg; lia].
    + replace (i + 1 - 1) with (i - 1 + 1) by lia.
      apply (bit0_model_insert__dp_body_branches_k1 values vals_l_2 dp0_l_2
               (replace_Znth i (0 + 1) dp0_l_2) mX_2 (i - 1) nvals retval_6
               (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0));
        [exact PreH66 | exact Hsi | lia | intros j Hj; apply Hdpj; lia | reflexivity
        | exact PreH5 | lia | unfold MaxBitNeg; lia].
    + apply (clamped_step_up__dp_body_branches_k1 dp0_l_2
               (replace_Znth i (0 + 1) dp0_l_2) i best0 (0 + 1));
        [exact PreH67 | lia | intros j Hj; apply Hdpj; lia | exact Hdpi | lia].
    + apply (clamped_best1_step__dp_body_branches_k1 values i best1 (0 + 1));
        [exact PreH68 | lia | exact HB1v | lia].
    + replace (i + 1 - 1) with (i - 1 + 1) by lia.
      apply (clamped_step_up__dp_body_branches_k1 dp0_l_2
               (replace_Znth i (0 + 1) dp0_l_2) (i - 1) best0_prefix
               (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0));
        [exact PreH69 | lia | intros j Hj; apply Hdpj; lia | reflexivity | lia].
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
Qed.

Lemma proof_of_solver_entail_wit_12_9 : solver_entail_wit_12_9.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hci : Znth i c_l_2 0 = KeyAt values i) by (apply PreH50; lia).
  assert (Hcim : Znth (i - 1) c_l_2 0 = KeyAt values (i - 1)) by (apply PreH50; lia).
  rewrite Hci in PreH34, PreH31.
  rewrite Hcim in PreH5.
  assert (Hsi : StrictIncPrefix vals_l_2 nvals) by (destruct PreH53 as [Hs _]; exact Hs).
  assert (Hlm0 : Zlength m0_2 = nvals + 1) by (destruct PreH64 as [Hz _]; exact Hz).
  assert (Hlm1 : Zlength m1_2 = nvals + 1) by (destruct PreH65 as [Hz _]; exact Hz).
  assert (HlmX : Zlength mX_2 = nvals + 1) by (destruct PreH66 as [Hz _]; exact Hz).
  assert (Hdpi : Znth i (replace_Znth i (retval + 1) dp0_l_2) 0 = retval + 1)
    by (apply Znth_replace_Znth_Same; lia).
  assert (Hdpj : forall j, 0 <= j < n_pre -> j <> i ->
                 Znth j (replace_Znth i (retval + 1) dp0_l_2) 0 = Znth j dp0_l_2 0)
    by (intros j Hj Hne; apply Znth_replace_Znth_Diff; lia).
  assert (Hdpim : Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0
                  = Znth (i - 1) dp0_l_2 0) by (apply Hdpj; lia).
  assert (Hdpimb : 1 <= Znth (i - 1) dp0_l_2 0 <= n_pre) by (apply PreH63; lia).
  assert (HB0 : Best0EndingAt values i (retval + 1)).
  { replace (retval + 1) with (Z.max retval 0 + 1) by lia.
    apply (best0_step__dp_body_branches_k1 values vals_l_2 dp0_l_2 m0_2 i nvals retval_3 retval);
      [lia | exact PreH53 | exact PreH62 | exact PreH64 | exact PreH34 | lia | exact PreH28]. }
  assert (HB1v : Best1EndingAt values i (retval_2 + 1)).
  { replace (retval_2 + 1) with (Z.max (Z.max retval_5 retval_2) 0 + 1) by lia.
    apply (best1_step__dp_body_branches_k1 values vals_l_2 dp0_l_2 m1_2 mX_2 i nvals retval_4 retval_5 retval_2);
      [lia | exact PreH53 | exact PreH62 | exact PreH65 | exact PreH66 | exact PreH31 | lia
      | exact PreH23 | exact PreH19]. }
  pose proof (best0_val_bound__dp_body_branches_k1 values i (retval + 1) HB0 ltac:(lia)) as Hb0b.
  pose proof (best1_val_bound__dp_body_branches_k1 values i (retval_2 + 1) HB1v ltac:(lia)) as Hb1b.
  Exists (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_4 (retval_2 + 1))
         (MaxBitInsert m0_2 retval_3 (retval + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (retval + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    + lia.
    + lia.
    + lia.
    + exact PreH41.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + rewrite zlength_replace__dp_body_branches_k1. lia.
    + exact PreH50.
    + exact PreH51.
    + exact PreH52.
    + exact PreH53.
    + intros k3 Hk3. pose proof (PreH14 k3 Hk3). pose proof (PreH10 k3 Hk3).
      pose proof (PreH3 k3 Hk3). lia.
    + lia.
    + lia.
    + lia.
    + exact PreH15.
    + exact PreH11.
    + exact PreH4.
    + intros r Hr.
      assert (H0 : Znth r (MaxBitInsert m0_2 retval_3 (retval + 1)) 0
                     = Z.max (Znth r m0_2 0) (retval + 1)
                   \/ Znth r (MaxBitInsert m0_2 retval_3 (retval + 1)) 0 = Znth r m0_2 0).
      { destruct (Z.eq_dec r retval_3) as [He | Hne].
        - left. rewrite He. apply maxbitinsert_same__dp_body_branches_k1. lia.
        - right. apply maxbitinsert_diff__dp_body_branches_k1; lia. }
      assert (H1 : Znth r (MaxBitInsert m1_2 retval_4 (retval_2 + 1)) 0
                     = Z.max (Znth r m1_2 0) (retval_2 + 1)
                   \/ Znth r (MaxBitInsert m1_2 retval_4 (retval_2 + 1)) 0 = Znth r m1_2 0).
      { destruct (Z.eq_dec r retval_4) as [He | Hne].
        - left. rewrite He. apply maxbitinsert_same__dp_body_branches_k1. lia.
        - right. apply maxbitinsert_diff__dp_body_branches_k1; lia. }
      assert (HX : Znth r (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0)) 0
                     = Z.max (Znth r mX_2 0) (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0)
                   \/ Znth r (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0)) 0
                     = Znth r mX_2 0).
      { destruct (Z.eq_dec r retval_6) as [He | Hne].
        - left. rewrite He. apply maxbitinsert_same__dp_body_branches_k1. lia.
        - right. apply maxbitinsert_diff__dp_body_branches_k1; lia. }
      pose proof (PreH61 r Hr). lia.
    + intros j Hj. destruct (Z.eq_dec j i) as [He | Hne].
      * rewrite He. rewrite Hdpi. exact HB0.
      * rewrite Hdpj by lia. apply PreH62; lia.
    + intros k4 Hk4. destruct (Z.eq_dec k4 i) as [He | Hne].
      * rewrite He. rewrite Hdpi. lia.
      * rewrite Hdpj by lia. apply PreH63; lia.
    + apply (bit0_model_insert__dp_body_branches_k1 values vals_l_2 dp0_l_2
               (replace_Znth i (retval + 1) dp0_l_2) m0_2 i nvals retval_3 (retval + 1));
        [exact PreH64 | exact Hsi | lia | intros j Hj; apply Hdpj; lia | exact Hdpi
        | exact PreH34 | lia | unfold MaxBitNeg; lia].
    + apply (bit1_model_insert__dp_body_branches_k1 values vals_l_2 m1_2 i nvals retval_4 (retval_2 + 1));
        [exact PreH65 | exact Hsi | lia | exact PreH31 | lia | exact HB1v
        | unfold MaxBitNeg; lia].
    + replace (i + 1 - 1) with (i - 1 + 1) by lia.
      apply (bit0_model_insert__dp_body_branches_k1 values vals_l_2 dp0_l_2
               (replace_Znth i (retval + 1) dp0_l_2) mX_2 (i - 1) nvals retval_6
               (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0));
        [exact PreH66 | exact Hsi | lia | intros j Hj; apply Hdpj; lia | reflexivity
        | exact PreH5 | lia | unfold MaxBitNeg; lia].
    + apply (clamped_step_keep__dp_body_branches_k1 dp0_l_2
               (replace_Znth i (retval + 1) dp0_l_2) i best0 (retval + 1));
        [exact PreH67 | lia | intros j Hj; apply Hdpj; lia | exact Hdpi | lia].
    + apply (clamped_best1_step__dp_body_branches_k1 values i best1 (retval_2 + 1));
        [exact PreH68 | lia | exact HB1v | lia].
    + replace (i + 1 - 1) with (i - 1 + 1) by lia.
      apply (clamped_step_up__dp_body_branches_k1 dp0_l_2
               (replace_Znth i (retval + 1) dp0_l_2) (i - 1) best0_prefix
               (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0));
        [exact PreH69 | lia | intros j Hj; apply Hdpj; lia | reflexivity | lia].
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
Qed.

Lemma proof_of_solver_entail_wit_12_10 : solver_entail_wit_12_10.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hci : Znth i c_l_2 0 = KeyAt values i) by (apply PreH50; lia).
  assert (Hcim : Znth (i - 1) c_l_2 0 = KeyAt values (i - 1)) by (apply PreH50; lia).
  rewrite Hci in PreH34, PreH31.
  rewrite Hcim in PreH5.
  assert (Hsi : StrictIncPrefix vals_l_2 nvals) by (destruct PreH53 as [Hs _]; exact Hs).
  assert (Hlm0 : Zlength m0_2 = nvals + 1) by (destruct PreH64 as [Hz _]; exact Hz).
  assert (Hlm1 : Zlength m1_2 = nvals + 1) by (destruct PreH65 as [Hz _]; exact Hz).
  assert (HlmX : Zlength mX_2 = nvals + 1) by (destruct PreH66 as [Hz _]; exact Hz).
  assert (Hdpi : Znth i (replace_Znth i (0 + 1) dp0_l_2) 0 = 0 + 1)
    by (apply Znth_replace_Znth_Same; lia).
  assert (Hdpj : forall j, 0 <= j < n_pre -> j <> i ->
                 Znth j (replace_Znth i (0 + 1) dp0_l_2) 0 = Znth j dp0_l_2 0)
    by (intros j Hj Hne; apply Znth_replace_Znth_Diff; lia).
  assert (Hdpim : Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0
                  = Znth (i - 1) dp0_l_2 0) by (apply Hdpj; lia).
  assert (Hdpimb : 1 <= Znth (i - 1) dp0_l_2 0 <= n_pre) by (apply PreH63; lia).
  assert (HB0 : Best0EndingAt values i (0 + 1)).
  { replace (0 + 1) with (Z.max retval_4 0 + 1) by lia.
    apply (best0_step__dp_body_branches_k1 values vals_l_2 dp0_l_2 m0_2 i nvals retval_2 retval_4);
      [lia | exact PreH53 | exact PreH62 | exact PreH64 | exact PreH34 | lia | exact PreH28]. }
  assert (HB1v : Best1EndingAt values i (retval + 1)).
  { replace (retval + 1) with (Z.max (Z.max retval_5 retval) 0 + 1) by lia.
    apply (best1_step__dp_body_branches_k1 values vals_l_2 dp0_l_2 m1_2 mX_2 i nvals retval_3 retval_5 retval);
      [lia | exact PreH53 | exact PreH62 | exact PreH65 | exact PreH66 | exact PreH31 | lia
      | exact PreH23 | exact PreH19]. }
  pose proof (best0_val_bound__dp_body_branches_k1 values i (0 + 1) HB0 ltac:(lia)) as Hb0b.
  pose proof (best1_val_bound__dp_body_branches_k1 values i (retval + 1) HB1v ltac:(lia)) as Hb1b.
  Exists (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_3 (retval + 1))
         (MaxBitInsert m0_2 retval_2 (0 + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (0 + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    + lia.
    + lia.
    + lia.
    + exact PreH41.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + rewrite zlength_replace__dp_body_branches_k1. lia.
    + exact PreH50.
    + exact PreH51.
    + exact PreH52.
    + exact PreH53.
    + intros k3 Hk3. pose proof (PreH14 k3 Hk3). pose proof (PreH10 k3 Hk3).
      pose proof (PreH3 k3 Hk3). lia.
    + lia.
    + lia.
    + lia.
    + exact PreH15.
    + exact PreH11.
    + exact PreH4.
    + intros r Hr.
      assert (H0 : Znth r (MaxBitInsert m0_2 retval_2 (0 + 1)) 0
                     = Z.max (Znth r m0_2 0) (0 + 1)
                   \/ Znth r (MaxBitInsert m0_2 retval_2 (0 + 1)) 0 = Znth r m0_2 0).
      { destruct (Z.eq_dec r retval_2) as [He | Hne].
        - left. rewrite He. apply maxbitinsert_same__dp_body_branches_k1. lia.
        - right. apply maxbitinsert_diff__dp_body_branches_k1; lia. }
      assert (H1 : Znth r (MaxBitInsert m1_2 retval_3 (retval + 1)) 0
                     = Z.max (Znth r m1_2 0) (retval + 1)
                   \/ Znth r (MaxBitInsert m1_2 retval_3 (retval + 1)) 0 = Znth r m1_2 0).
      { destruct (Z.eq_dec r retval_3) as [He | Hne].
        - left. rewrite He. apply maxbitinsert_same__dp_body_branches_k1. lia.
        - right. apply maxbitinsert_diff__dp_body_branches_k1; lia. }
      assert (HX : Znth r (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)) 0
                     = Z.max (Znth r mX_2 0) (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)
                   \/ Znth r (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)) 0
                     = Znth r mX_2 0).
      { destruct (Z.eq_dec r retval_6) as [He | Hne].
        - left. rewrite He. apply maxbitinsert_same__dp_body_branches_k1. lia.
        - right. apply maxbitinsert_diff__dp_body_branches_k1; lia. }
      pose proof (PreH61 r Hr). lia.
    + intros j Hj. destruct (Z.eq_dec j i) as [He | Hne].
      * rewrite He. rewrite Hdpi. exact HB0.
      * rewrite Hdpj by lia. apply PreH62; lia.
    + intros k4 Hk4. destruct (Z.eq_dec k4 i) as [He | Hne].
      * rewrite He. rewrite Hdpi. lia.
      * rewrite Hdpj by lia. apply PreH63; lia.
    + apply (bit0_model_insert__dp_body_branches_k1 values vals_l_2 dp0_l_2
               (replace_Znth i (0 + 1) dp0_l_2) m0_2 i nvals retval_2 (0 + 1));
        [exact PreH64 | exact Hsi | lia | intros j Hj; apply Hdpj; lia | exact Hdpi
        | exact PreH34 | lia | unfold MaxBitNeg; lia].
    + apply (bit1_model_insert__dp_body_branches_k1 values vals_l_2 m1_2 i nvals retval_3 (retval + 1));
        [exact PreH65 | exact Hsi | lia | exact PreH31 | lia | exact HB1v
        | unfold MaxBitNeg; lia].
    + replace (i + 1 - 1) with (i - 1 + 1) by lia.
      apply (bit0_model_insert__dp_body_branches_k1 values vals_l_2 dp0_l_2
               (replace_Znth i (0 + 1) dp0_l_2) mX_2 (i - 1) nvals retval_6
               (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0));
        [exact PreH66 | exact Hsi | lia | intros j Hj; apply Hdpj; lia | reflexivity
        | exact PreH5 | lia | unfold MaxBitNeg; lia].
    + apply (clamped_step_keep__dp_body_branches_k1 dp0_l_2
               (replace_Znth i (0 + 1) dp0_l_2) i best0 (0 + 1));
        [exact PreH67 | lia | intros j Hj; apply Hdpj; lia | exact Hdpi | lia].
    + apply (clamped_best1_step__dp_body_branches_k1 values i best1 (retval + 1));
        [exact PreH68 | lia | exact HB1v | lia].
    + replace (i + 1 - 1) with (i - 1 + 1) by lia.
      apply (clamped_step_up__dp_body_branches_k1 dp0_l_2
               (replace_Znth i (0 + 1) dp0_l_2) (i - 1) best0_prefix
               (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0));
        [exact PreH69 | lia | intros j Hj; apply Hdpj; lia | reflexivity | lia].
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
Qed.

Lemma proof_of_solver_entail_wit_12_11 : solver_entail_wit_12_11.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hci : Znth i c_l_2 0 = KeyAt values i) by (apply PreH50; lia).
  assert (Hcim : Znth (i - 1) c_l_2 0 = KeyAt values (i - 1)) by (apply PreH50; lia).
  rewrite Hci in PreH34, PreH31.
  rewrite Hcim in PreH5.
  assert (Hsi : StrictIncPrefix vals_l_2 nvals) by (destruct PreH53 as [Hs _]; exact Hs).
  assert (Hlm0 : Zlength m0_2 = nvals + 1) by (destruct PreH64 as [Hz _]; exact Hz).
  assert (Hlm1 : Zlength m1_2 = nvals + 1) by (destruct PreH65 as [Hz _]; exact Hz).
  assert (HlmX : Zlength mX_2 = nvals + 1) by (destruct PreH66 as [Hz _]; exact Hz).
  assert (Hdpi : Znth i (replace_Znth i (retval + 1) dp0_l_2) 0 = retval + 1)
    by (apply Znth_replace_Znth_Same; lia).
  assert (Hdpj : forall j, 0 <= j < n_pre -> j <> i ->
                 Znth j (replace_Znth i (retval + 1) dp0_l_2) 0 = Znth j dp0_l_2 0)
    by (intros j Hj Hne; apply Znth_replace_Znth_Diff; lia).
  assert (Hdpim : Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0
                  = Znth (i - 1) dp0_l_2 0) by (apply Hdpj; lia).
  assert (Hdpimb : 1 <= Znth (i - 1) dp0_l_2 0 <= n_pre) by (apply PreH63; lia).
  assert (HB0 : Best0EndingAt values i (retval + 1)).
  { replace (retval + 1) with (Z.max retval 0 + 1) by lia.
    apply (best0_step__dp_body_branches_k1 values vals_l_2 dp0_l_2 m0_2 i nvals retval_3 retval);
      [lia | exact PreH53 | exact PreH62 | exact PreH64 | exact PreH34 | lia | exact PreH28]. }
  assert (HB1v : Best1EndingAt values i (retval_2 + 1)).
  { replace (retval_2 + 1) with (Z.max (Z.max retval_5 retval_2) 0 + 1) by lia.
    apply (best1_step__dp_body_branches_k1 values vals_l_2 dp0_l_2 m1_2 mX_2 i nvals retval_4 retval_5 retval_2);
      [lia | exact PreH53 | exact PreH62 | exact PreH65 | exact PreH66 | exact PreH31 | lia
      | exact PreH23 | exact PreH19]. }
  pose proof (best0_val_bound__dp_body_branches_k1 values i (retval + 1) HB0 ltac:(lia)) as Hb0b.
  pose proof (best1_val_bound__dp_body_branches_k1 values i (retval_2 + 1) HB1v ltac:(lia)) as Hb1b.
  Exists (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_4 (retval_2 + 1))
         (MaxBitInsert m0_2 retval_3 (retval + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (retval + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    + lia.
    + lia.
    + lia.
    + exact PreH41.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + rewrite zlength_replace__dp_body_branches_k1. lia.
    + exact PreH50.
    + exact PreH51.
    + exact PreH52.
    + exact PreH53.
    + intros k3 Hk3. pose proof (PreH14 k3 Hk3). pose proof (PreH10 k3 Hk3).
      pose proof (PreH3 k3 Hk3). lia.
    + lia.
    + lia.
    + lia.
    + exact PreH15.
    + exact PreH11.
    + exact PreH4.
    + intros r Hr.
      assert (H0 : Znth r (MaxBitInsert m0_2 retval_3 (retval + 1)) 0
                     = Z.max (Znth r m0_2 0) (retval + 1)
                   \/ Znth r (MaxBitInsert m0_2 retval_3 (retval + 1)) 0 = Znth r m0_2 0).
      { destruct (Z.eq_dec r retval_3) as [He | Hne].
        - left. rewrite He. apply maxbitinsert_same__dp_body_branches_k1. lia.
        - right. apply maxbitinsert_diff__dp_body_branches_k1; lia. }
      assert (H1 : Znth r (MaxBitInsert m1_2 retval_4 (retval_2 + 1)) 0
                     = Z.max (Znth r m1_2 0) (retval_2 + 1)
                   \/ Znth r (MaxBitInsert m1_2 retval_4 (retval_2 + 1)) 0 = Znth r m1_2 0).
      { destruct (Z.eq_dec r retval_4) as [He | Hne].
        - left. rewrite He. apply maxbitinsert_same__dp_body_branches_k1. lia.
        - right. apply maxbitinsert_diff__dp_body_branches_k1; lia. }
      assert (HX : Znth r (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0)) 0
                     = Z.max (Znth r mX_2 0) (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0)
                   \/ Znth r (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0)) 0
                     = Znth r mX_2 0).
      { destruct (Z.eq_dec r retval_6) as [He | Hne].
        - left. rewrite He. apply maxbitinsert_same__dp_body_branches_k1. lia.
        - right. apply maxbitinsert_diff__dp_body_branches_k1; lia. }
      pose proof (PreH61 r Hr). lia.
    + intros j Hj. destruct (Z.eq_dec j i) as [He | Hne].
      * rewrite He. rewrite Hdpi. exact HB0.
      * rewrite Hdpj by lia. apply PreH62; lia.
    + intros k4 Hk4. destruct (Z.eq_dec k4 i) as [He | Hne].
      * rewrite He. rewrite Hdpi. lia.
      * rewrite Hdpj by lia. apply PreH63; lia.
    + apply (bit0_model_insert__dp_body_branches_k1 values vals_l_2 dp0_l_2
               (replace_Znth i (retval + 1) dp0_l_2) m0_2 i nvals retval_3 (retval + 1));
        [exact PreH64 | exact Hsi | lia | intros j Hj; apply Hdpj; lia | exact Hdpi
        | exact PreH34 | lia | unfold MaxBitNeg; lia].
    + apply (bit1_model_insert__dp_body_branches_k1 values vals_l_2 m1_2 i nvals retval_4 (retval_2 + 1));
        [exact PreH65 | exact Hsi | lia | exact PreH31 | lia | exact HB1v
        | unfold MaxBitNeg; lia].
    + replace (i + 1 - 1) with (i - 1 + 1) by lia.
      apply (bit0_model_insert__dp_body_branches_k1 values vals_l_2 dp0_l_2
               (replace_Znth i (retval + 1) dp0_l_2) mX_2 (i - 1) nvals retval_6
               (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0));
        [exact PreH66 | exact Hsi | lia | intros j Hj; apply Hdpj; lia | reflexivity
        | exact PreH5 | lia | unfold MaxBitNeg; lia].
    + apply (clamped_step_keep__dp_body_branches_k1 dp0_l_2
               (replace_Znth i (retval + 1) dp0_l_2) i best0 (retval + 1));
        [exact PreH67 | lia | intros j Hj; apply Hdpj; lia | exact Hdpi | lia].
    + apply (clamped_best1_step__dp_body_branches_k1 values i best1 (retval_2 + 1));
        [exact PreH68 | lia | exact HB1v | lia].
    + replace (i + 1 - 1) with (i - 1 + 1) by lia.
      apply (clamped_step_up__dp_body_branches_k1 dp0_l_2
               (replace_Znth i (retval + 1) dp0_l_2) (i - 1) best0_prefix
               (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0));
        [exact PreH69 | lia | intros j Hj; apply Hdpj; lia | reflexivity | lia].
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
Qed.

Lemma proof_of_solver_entail_wit_12_12 : solver_entail_wit_12_12.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hci : Znth i c_l_2 0 = KeyAt values i) by (apply PreH50; lia).
  assert (Hcim : Znth (i - 1) c_l_2 0 = KeyAt values (i - 1)) by (apply PreH50; lia).
  rewrite Hci in PreH34, PreH31.
  rewrite Hcim in PreH5.
  assert (Hsi : StrictIncPrefix vals_l_2 nvals) by (destruct PreH53 as [Hs _]; exact Hs).
  assert (Hlm0 : Zlength m0_2 = nvals + 1) by (destruct PreH64 as [Hz _]; exact Hz).
  assert (Hlm1 : Zlength m1_2 = nvals + 1) by (destruct PreH65 as [Hz _]; exact Hz).
  assert (HlmX : Zlength mX_2 = nvals + 1) by (destruct PreH66 as [Hz _]; exact Hz).
  assert (Hdpi : Znth i (replace_Znth i (0 + 1) dp0_l_2) 0 = 0 + 1)
    by (apply Znth_replace_Znth_Same; lia).
  assert (Hdpj : forall j, 0 <= j < n_pre -> j <> i ->
                 Znth j (replace_Znth i (0 + 1) dp0_l_2) 0 = Znth j dp0_l_2 0)
    by (intros j Hj Hne; apply Znth_replace_Znth_Diff; lia).
  assert (Hdpim : Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0
                  = Znth (i - 1) dp0_l_2 0) by (apply Hdpj; lia).
  assert (Hdpimb : 1 <= Znth (i - 1) dp0_l_2 0 <= n_pre) by (apply PreH63; lia).
  assert (HB0 : Best0EndingAt values i (0 + 1)).
  { replace (0 + 1) with (Z.max retval_4 0 + 1) by lia.
    apply (best0_step__dp_body_branches_k1 values vals_l_2 dp0_l_2 m0_2 i nvals retval_2 retval_4);
      [lia | exact PreH53 | exact PreH62 | exact PreH64 | exact PreH34 | lia | exact PreH28]. }
  assert (HB1v : Best1EndingAt values i (retval + 1)).
  { replace (retval + 1) with (Z.max (Z.max retval_5 retval) 0 + 1) by lia.
    apply (best1_step__dp_body_branches_k1 values vals_l_2 dp0_l_2 m1_2 mX_2 i nvals retval_3 retval_5 retval);
      [lia | exact PreH53 | exact PreH62 | exact PreH65 | exact PreH66 | exact PreH31 | lia
      | exact PreH23 | exact PreH19]. }
  pose proof (best0_val_bound__dp_body_branches_k1 values i (0 + 1) HB0 ltac:(lia)) as Hb0b.
  pose proof (best1_val_bound__dp_body_branches_k1 values i (retval + 1) HB1v ltac:(lia)) as Hb1b.
  Exists (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_3 (retval + 1))
         (MaxBitInsert m0_2 retval_2 (0 + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (0 + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures.
    all: dump_pre_spatial.
    + lia.
    + lia.
    + lia.
    + exact PreH41.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + rewrite zlength_replace__dp_body_branches_k1. lia.
    + exact PreH50.
    + exact PreH51.
    + exact PreH52.
    + exact PreH53.
    + intros k3 Hk3. pose proof (PreH14 k3 Hk3). pose proof (PreH10 k3 Hk3).
      pose proof (PreH3 k3 Hk3). lia.
    + lia.
    + lia.
    + lia.
    + exact PreH15.
    + exact PreH11.
    + exact PreH4.
    + intros r Hr.
      assert (H0 : Znth r (MaxBitInsert m0_2 retval_2 (0 + 1)) 0
                     = Z.max (Znth r m0_2 0) (0 + 1)
                   \/ Znth r (MaxBitInsert m0_2 retval_2 (0 + 1)) 0 = Znth r m0_2 0).
      { destruct (Z.eq_dec r retval_2) as [He | Hne].
        - left. rewrite He. apply maxbitinsert_same__dp_body_branches_k1. lia.
        - right. apply maxbitinsert_diff__dp_body_branches_k1; lia. }
      assert (H1 : Znth r (MaxBitInsert m1_2 retval_3 (retval + 1)) 0
                     = Z.max (Znth r m1_2 0) (retval + 1)
                   \/ Znth r (MaxBitInsert m1_2 retval_3 (retval + 1)) 0 = Znth r m1_2 0).
      { destruct (Z.eq_dec r retval_3) as [He | Hne].
        - left. rewrite He. apply maxbitinsert_same__dp_body_branches_k1. lia.
        - right. apply maxbitinsert_diff__dp_body_branches_k1; lia. }
      assert (HX : Znth r (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)) 0
                     = Z.max (Znth r mX_2 0) (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)
                   \/ Znth r (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)) 0
                     = Znth r mX_2 0).
      { destruct (Z.eq_dec r retval_6) as [He | Hne].
        - left. rewrite He. apply maxbitinsert_same__dp_body_branches_k1. lia.
        - right. apply maxbitinsert_diff__dp_body_branches_k1; lia. }
      pose proof (PreH61 r Hr). lia.
    + intros j Hj. destruct (Z.eq_dec j i) as [He | Hne].
      * rewrite He. rewrite Hdpi. exact HB0.
      * rewrite Hdpj by lia. apply PreH62; lia.
    + intros k4 Hk4. destruct (Z.eq_dec k4 i) as [He | Hne].
      * rewrite He. rewrite Hdpi. lia.
      * rewrite Hdpj by lia. apply PreH63; lia.
    + apply (bit0_model_insert__dp_body_branches_k1 values vals_l_2 dp0_l_2
               (replace_Znth i (0 + 1) dp0_l_2) m0_2 i nvals retval_2 (0 + 1));
        [exact PreH64 | exact Hsi | lia | intros j Hj; apply Hdpj; lia | exact Hdpi
        | exact PreH34 | lia | unfold MaxBitNeg; lia].
    + apply (bit1_model_insert__dp_body_branches_k1 values vals_l_2 m1_2 i nvals retval_3 (retval + 1));
        [exact PreH65 | exact Hsi | lia | exact PreH31 | lia | exact HB1v
        | unfold MaxBitNeg; lia].
    + replace (i + 1 - 1) with (i - 1 + 1) by lia.
      apply (bit0_model_insert__dp_body_branches_k1 values vals_l_2 dp0_l_2
               (replace_Znth i (0 + 1) dp0_l_2) mX_2 (i - 1) nvals retval_6
               (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0));
        [exact PreH66 | exact Hsi | lia | intros j Hj; apply Hdpj; lia | reflexivity
        | exact PreH5 | lia | unfold MaxBitNeg; lia].
    + apply (clamped_step_keep__dp_body_branches_k1 dp0_l_2
               (replace_Znth i (0 + 1) dp0_l_2) i best0 (0 + 1));
        [exact PreH67 | lia | intros j Hj; apply Hdpj; lia | exact Hdpi | lia].
    + apply (clamped_best1_step__dp_body_branches_k1 values i best1 (retval + 1));
        [exact PreH68 | lia | exact HB1v | lia].
    + replace (i + 1 - 1) with (i - 1 + 1) by lia.
      apply (clamped_step_up__dp_body_branches_k1 dp0_l_2
               (replace_Znth i (0 + 1) dp0_l_2) (i - 1) best0_prefix
               (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0));
        [exact PreH69 | lia | intros j Hj; apply Hdpj; lia | reflexivity | lia].
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
    + lia.
Qed.

Lemma proof_of_solver_entail_wit_12_13 : solver_entail_wit_12_13.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (dp_body_master__dp_body_branches_k2 values vals_l_2 c_l_2 dp0_l_2
     (replace_Znth i (retval + 1) dp0_l_2) m0_2 m1_2 mX_2
     i n_pre nvals retval_3 retval_4 retval_6 retval retval_2 retval_5
     (retval + 1) (retval_2 + 1) best0 best1 best0_prefix (best0) (retval_2 + 1)
     PreH38 PreH40 PreH43 PreH50 PreH47 PreH49 PreH53
     PreH34 ltac:(lia) PreH31 ltac:(lia) PreH5 ltac:(lia)
     PreH28 PreH23 PreH19 ltac:(lia) PreH62 PreH63 PreH64 PreH65 PreH66
     PreH67 PreH68 PreH69
     ltac:(intros r Hr; specialize (PreH61 r Hr); lia)
     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia)
     ltac:(lia) ltac:(lia)) as HM.
  Exists (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_4 (retval_2 + 1))
         (MaxBitInsert m0_2 retval_3 (retval + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (retval + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; try (dump_pre_spatial; first [tauto | lia]).
    dump_pre_spatial. intros k3 Hk3.
    pose proof (PreH3 k3 Hk3). pose proof (PreH10 k3 Hk3). pose proof (PreH14 k3 Hk3).
    lia.
Qed.

Lemma proof_of_solver_entail_wit_12_14 : solver_entail_wit_12_14.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (dp_body_master__dp_body_branches_k2 values vals_l_2 c_l_2 dp0_l_2
     (replace_Znth i (0 + 1) dp0_l_2) m0_2 m1_2 mX_2
     i n_pre nvals retval_2 retval_3 retval_6 retval_4 retval retval_5
     (0 + 1) (retval + 1) best0 best1 best0_prefix (best0) (retval + 1)
     PreH38 PreH40 PreH43 PreH50 PreH47 PreH49 PreH53
     PreH34 ltac:(lia) PreH31 ltac:(lia) PreH5 ltac:(lia)
     PreH28 PreH23 PreH19 ltac:(lia) PreH62 PreH63 PreH64 PreH65 PreH66
     PreH67 PreH68 PreH69
     ltac:(intros r Hr; specialize (PreH61 r Hr); lia)
     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia)
     ltac:(lia) ltac:(lia)) as HM.
  Exists (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_3 (retval + 1))
         (MaxBitInsert m0_2 retval_2 (0 + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (0 + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; try (dump_pre_spatial; first [tauto | lia]).
    dump_pre_spatial. intros k3 Hk3.
    pose proof (PreH3 k3 Hk3). pose proof (PreH10 k3 Hk3). pose proof (PreH14 k3 Hk3).
    lia.
Qed.

Lemma proof_of_solver_entail_wit_12_15 : solver_entail_wit_12_15.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (dp_body_master__dp_body_branches_k2 values vals_l_2 c_l_2 dp0_l_2
     (replace_Znth i (retval + 1) dp0_l_2) m0_2 m1_2 mX_2
     i n_pre nvals retval_2 retval_3 retval_6 retval retval_4 retval_5
     (retval + 1) (0 + 1) best0 best1 best0_prefix (best0) (0 + 1)
     PreH38 PreH40 PreH43 PreH50 PreH47 PreH49 PreH53
     PreH34 ltac:(lia) PreH31 ltac:(lia) PreH5 ltac:(lia)
     PreH28 PreH23 PreH19 ltac:(lia) PreH62 PreH63 PreH64 PreH65 PreH66
     PreH67 PreH68 PreH69
     ltac:(intros r Hr; specialize (PreH61 r Hr); lia)
     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia)
     ltac:(lia) ltac:(lia)) as HM.
  Exists (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_3 (0 + 1))
         (MaxBitInsert m0_2 retval_2 (retval + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (retval + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; try (dump_pre_spatial; first [tauto | lia]).
    dump_pre_spatial. intros k3 Hk3.
    pose proof (PreH3 k3 Hk3). pose proof (PreH10 k3 Hk3). pose proof (PreH14 k3 Hk3).
    lia.
Qed.

Lemma proof_of_solver_entail_wit_12_16 : solver_entail_wit_12_16.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (dp_body_master__dp_body_branches_k2 values vals_l_2 c_l_2 dp0_l_2
     (replace_Znth i (0 + 1) dp0_l_2) m0_2 m1_2 mX_2
     i n_pre nvals retval retval_2 retval_6 retval_3 retval_4 retval_5
     (0 + 1) (0 + 1) best0 best1 best0_prefix (best0) (0 + 1)
     PreH38 PreH40 PreH43 PreH50 PreH47 PreH49 PreH53
     PreH34 ltac:(lia) PreH31 ltac:(lia) PreH5 ltac:(lia)
     PreH28 PreH23 PreH19 ltac:(lia) PreH62 PreH63 PreH64 PreH65 PreH66
     PreH67 PreH68 PreH69
     ltac:(intros r Hr; specialize (PreH61 r Hr); lia)
     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia)
     ltac:(lia) ltac:(lia)) as HM.
  Exists (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_2 (0 + 1))
         (MaxBitInsert m0_2 retval (0 + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (0 + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; try (dump_pre_spatial; first [tauto | lia]).
    dump_pre_spatial. intros k3 Hk3.
    pose proof (PreH3 k3 Hk3). pose proof (PreH10 k3 Hk3). pose proof (PreH14 k3 Hk3).
    lia.
Qed.

Lemma proof_of_solver_entail_wit_12_17 : solver_entail_wit_12_17.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (dp_body_master__dp_body_branches_k2 values vals_l_2 c_l_2 dp0_l_2
     (replace_Znth i (retval + 1) dp0_l_2) m0_2 m1_2 mX_2
     i n_pre nvals retval_2 retval_3 retval_6 retval retval_4 retval_5
     (retval + 1) (retval_5 + 1) best0 best1 best0_prefix (retval + 1) (best1)
     PreH38 PreH40 PreH43 PreH50 PreH47 PreH49 PreH53
     PreH34 ltac:(lia) PreH31 ltac:(lia) PreH5 ltac:(lia)
     PreH28 PreH23 PreH19 ltac:(lia) PreH62 PreH63 PreH64 PreH65 PreH66
     PreH67 PreH68 PreH69
     ltac:(intros r Hr; specialize (PreH61 r Hr); lia)
     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia)
     ltac:(lia) ltac:(lia)) as HM.
  Exists (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_3 (retval_5 + 1))
         (MaxBitInsert m0_2 retval_2 (retval + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (retval + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; try (dump_pre_spatial; first [tauto | lia]).
    dump_pre_spatial. intros k3 Hk3.
    pose proof (PreH3 k3 Hk3). pose proof (PreH10 k3 Hk3). pose proof (PreH14 k3 Hk3).
    lia.
Qed.

Lemma proof_of_solver_entail_wit_12_18 : solver_entail_wit_12_18.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (dp_body_master__dp_body_branches_k2 values vals_l_2 c_l_2 dp0_l_2
     (replace_Znth i (0 + 1) dp0_l_2) m0_2 m1_2 mX_2
     i n_pre nvals retval retval_2 retval_6 retval_3 retval_4 retval_5
     (0 + 1) (retval_5 + 1) best0 best1 best0_prefix (0 + 1) (best1)
     PreH38 PreH40 PreH43 PreH50 PreH47 PreH49 PreH53
     PreH34 ltac:(lia) PreH31 ltac:(lia) PreH5 ltac:(lia)
     PreH28 PreH23 PreH19 ltac:(lia) PreH62 PreH63 PreH64 PreH65 PreH66
     PreH67 PreH68 PreH69
     ltac:(intros r Hr; specialize (PreH61 r Hr); lia)
     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia)
     ltac:(lia) ltac:(lia)) as HM.
  Exists (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_2 (retval_5 + 1))
         (MaxBitInsert m0_2 retval (0 + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (0 + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; try (dump_pre_spatial; first [tauto | lia]).
    dump_pre_spatial. intros k3 Hk3.
    pose proof (PreH3 k3 Hk3). pose proof (PreH10 k3 Hk3). pose proof (PreH14 k3 Hk3).
    lia.
Qed.

Lemma proof_of_solver_entail_wit_12_19 : solver_entail_wit_12_19.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (dp_body_master__dp_body_branches_k2 values vals_l_2 c_l_2 dp0_l_2
     (replace_Znth i (retval + 1) dp0_l_2) m0_2 m1_2 mX_2
     i n_pre nvals retval_2 retval_3 retval_6 retval retval_4 retval_5
     (retval + 1) (retval_5 + 1) best0 best1 best0_prefix (retval + 1) (best1)
     PreH38 PreH40 PreH43 PreH50 PreH47 PreH49 PreH53
     PreH34 ltac:(lia) PreH31 ltac:(lia) PreH5 ltac:(lia)
     PreH28 PreH23 PreH19 ltac:(lia) PreH62 PreH63 PreH64 PreH65 PreH66
     PreH67 PreH68 PreH69
     ltac:(intros r Hr; specialize (PreH61 r Hr); lia)
     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia)
     ltac:(lia) ltac:(lia)) as HM.
  Exists (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_3 (retval_5 + 1))
         (MaxBitInsert m0_2 retval_2 (retval + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (retval + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; try (dump_pre_spatial; first [tauto | lia]).
    dump_pre_spatial. intros k3 Hk3.
    pose proof (PreH3 k3 Hk3). pose proof (PreH10 k3 Hk3). pose proof (PreH14 k3 Hk3).
    lia.
Qed.

Lemma proof_of_solver_entail_wit_12_20 : solver_entail_wit_12_20.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (dp_body_master__dp_body_branches_k2 values vals_l_2 c_l_2 dp0_l_2
     (replace_Znth i (0 + 1) dp0_l_2) m0_2 m1_2 mX_2
     i n_pre nvals retval retval_2 retval_6 retval_3 retval_4 retval_5
     (0 + 1) (retval_5 + 1) best0 best1 best0_prefix (0 + 1) (best1)
     PreH38 PreH40 PreH43 PreH50 PreH47 PreH49 PreH53
     PreH34 ltac:(lia) PreH31 ltac:(lia) PreH5 ltac:(lia)
     PreH28 PreH23 PreH19 ltac:(lia) PreH62 PreH63 PreH64 PreH65 PreH66
     PreH67 PreH68 PreH69
     ltac:(intros r Hr; specialize (PreH61 r Hr); lia)
     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia)
     ltac:(lia) ltac:(lia)) as HM.
  Exists (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_2 (retval_5 + 1))
         (MaxBitInsert m0_2 retval (0 + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (0 + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; try (dump_pre_spatial; first [tauto | lia]).
    dump_pre_spatial. intros k3 Hk3.
    pose proof (PreH3 k3 Hk3). pose proof (PreH10 k3 Hk3). pose proof (PreH14 k3 Hk3).
    lia.
Qed.

Lemma proof_of_solver_entail_wit_12_21 : solver_entail_wit_12_21.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (dp_body_master__dp_body_branches_k2 values vals_l_2 c_l_2 dp0_l_2
     (replace_Znth i (retval + 1) dp0_l_2) m0_2 m1_2 mX_2
     i n_pre nvals retval_2 retval_3 retval_6 retval retval_4 retval_5
     (retval + 1) (retval_4 + 1) best0 best1 best0_prefix (retval + 1) (best1)
     PreH38 PreH40 PreH43 PreH50 PreH47 PreH49 PreH53
     PreH34 ltac:(lia) PreH31 ltac:(lia) PreH5 ltac:(lia)
     PreH28 PreH23 PreH19 ltac:(lia) PreH62 PreH63 PreH64 PreH65 PreH66
     PreH67 PreH68 PreH69
     ltac:(intros r Hr; specialize (PreH61 r Hr); lia)
     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia)
     ltac:(lia) ltac:(lia)) as HM.
  Exists (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_3 (retval_4 + 1))
         (MaxBitInsert m0_2 retval_2 (retval + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (retval + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; try (dump_pre_spatial; first [tauto | lia]).
    dump_pre_spatial. intros k3 Hk3.
    pose proof (PreH3 k3 Hk3). pose proof (PreH10 k3 Hk3). pose proof (PreH14 k3 Hk3).
    lia.
Qed.

Lemma proof_of_solver_entail_wit_12_22 : solver_entail_wit_12_22.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (dp_body_master__dp_body_branches_k2 values vals_l_2 c_l_2 dp0_l_2
     (replace_Znth i (0 + 1) dp0_l_2) m0_2 m1_2 mX_2
     i n_pre nvals retval retval_2 retval_6 retval_3 retval_4 retval_5
     (0 + 1) (retval_4 + 1) best0 best1 best0_prefix (0 + 1) (best1)
     PreH38 PreH40 PreH43 PreH50 PreH47 PreH49 PreH53
     PreH34 ltac:(lia) PreH31 ltac:(lia) PreH5 ltac:(lia)
     PreH28 PreH23 PreH19 ltac:(lia) PreH62 PreH63 PreH64 PreH65 PreH66
     PreH67 PreH68 PreH69
     ltac:(intros r Hr; specialize (PreH61 r Hr); lia)
     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia)
     ltac:(lia) ltac:(lia)) as HM.
  Exists (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_2 (retval_4 + 1))
         (MaxBitInsert m0_2 retval (0 + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (0 + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; try (dump_pre_spatial; first [tauto | lia]).
    dump_pre_spatial. intros k3 Hk3.
    pose proof (PreH3 k3 Hk3). pose proof (PreH10 k3 Hk3). pose proof (PreH14 k3 Hk3).
    lia.
Qed.

Lemma proof_of_solver_entail_wit_12_23 : solver_entail_wit_12_23.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (dp_body_master__dp_body_branches_k2 values vals_l_2 c_l_2 dp0_l_2
     (replace_Znth i (retval + 1) dp0_l_2) m0_2 m1_2 mX_2
     i n_pre nvals retval_2 retval_3 retval_6 retval retval_4 retval_5
     (retval + 1) (0 + 1) best0 best1 best0_prefix (retval + 1) (best1)
     PreH38 PreH40 PreH43 PreH50 PreH47 PreH49 PreH53
     PreH34 ltac:(lia) PreH31 ltac:(lia) PreH5 ltac:(lia)
     PreH28 PreH23 PreH19 ltac:(lia) PreH62 PreH63 PreH64 PreH65 PreH66
     PreH67 PreH68 PreH69
     ltac:(intros r Hr; specialize (PreH61 r Hr); lia)
     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia)
     ltac:(lia) ltac:(lia)) as HM.
  Exists (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_3 (0 + 1))
         (MaxBitInsert m0_2 retval_2 (retval + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (retval + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; try (dump_pre_spatial; first [tauto | lia]).
    dump_pre_spatial. intros k3 Hk3.
    pose proof (PreH3 k3 Hk3). pose proof (PreH10 k3 Hk3). pose proof (PreH14 k3 Hk3).
    lia.
Qed.

Lemma proof_of_solver_entail_wit_12_24 : solver_entail_wit_12_24.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (dp_body_master__dp_body_branches_k2 values vals_l_2 c_l_2 dp0_l_2
     (replace_Znth i (0 + 1) dp0_l_2) m0_2 m1_2 mX_2
     i n_pre nvals retval retval_2 retval_6 retval_3 retval_4 retval_5
     (0 + 1) (0 + 1) best0 best1 best0_prefix (0 + 1) (best1)
     PreH38 PreH40 PreH43 PreH50 PreH47 PreH49 PreH53
     PreH34 ltac:(lia) PreH31 ltac:(lia) PreH5 ltac:(lia)
     PreH28 PreH23 PreH19 ltac:(lia) PreH62 PreH63 PreH64 PreH65 PreH66
     PreH67 PreH68 PreH69
     ltac:(intros r Hr; specialize (PreH61 r Hr); lia)
     ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) eq_refl ltac:(lia)
     ltac:(lia) ltac:(lia)) as HM.
  Exists (MaxBitInsert mX_2 retval_6 (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_2 (0 + 1))
         (MaxBitInsert m0_2 retval (0 + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (0 + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; try (dump_pre_spatial; first [tauto | lia]).
    dump_pre_spatial. intros k3 Hk3.
    pose proof (PreH3 k3 Hk3). pose proof (PreH10 k3 Hk3). pose proof (PreH14 k3 Hk3).
    lia.
Qed.

Lemma proof_of_solver_entail_wit_12_25 : solver_entail_wit_12_25.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (dp_core__dp_body_branches_k3 values vals_l_2 c_l_2 dp0_l_2
              m0_2 m1_2 mX_2 (replace_Znth i (retval + 1) dp0_l_2)
              n_pre nvals i retval_2 retval_3 retval_6 (retval + 1) (retval_5 + 1)
              ltac:(lia) ltac:(lia) PreH40 PreH47 PreH49 PreH50 PreH53
              PreH34 ltac:(lia) PreH31 ltac:(lia) PreH5 ltac:(lia)
              PreH62 PreH64 PreH65 PreH66
              ltac:(rewrite <- PreH28; lia)
              ltac:(rewrite <- PreH23, <- PreH19; lia)
              eq_refl)
    as [Hbest0 [Hbest1 [Hd0r [Hd1r [Hdiff [Hsame
       [Hlen' [Hdp' [Hm0' [Hm1' HmX']]]]]]]]]].
  assert (Hl0 : Zlength m0_2 = nvals + 1) by (apply (proj1 PreH64)).
  assert (Hl1 : Zlength m1_2 = nvals + 1) by (apply (proj1 PreH65)).
  assert (HlX : Zlength mX_2 = nvals + 1) by (apply (proj1 PreH66)).
  assert (HX : Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0
               = Znth (i - 1) dp0_l_2 0) by (apply Hdiff; lia).
  pose proof (PreH63 (i - 1) ltac:(lia)) as HdpX.
  Exists (MaxBitInsert mX_2 retval_6
            (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0)).
  Exists (MaxBitInsert m1_2 retval_3 (retval_5 + 1)).
  Exists (MaxBitInsert m0_2 retval_2 (retval + 1)).
  Exists bit_l1_3 bit_l1_2 bit_l1.
  Exists (replace_Znth i (retval + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - do 12 (try cancel).
  - split_pures; dump_pre_spatial.
    all: try (exact PreH38 || exact PreH39 || exact PreH40 || exact PreH41
              || exact PreH42 || exact PreH43 || exact PreH44 || exact PreH47
              || exact PreH48 || exact PreH50 || exact PreH51 || exact PreH52
              || exact PreH53 || exact PreH70 || exact PreH71 || exact PreH72
              || exact PreH73 || lia
              || exact PreH15 || exact PreH11 || exact PreH4
              || exact Hdp' || exact Hm0' || exact Hm1').
    + intros k3 Hk3.
      pose proof (PreH14 k3 ltac:(lia)). pose proof (PreH10 k3 ltac:(lia)).
      pose proof (PreH3 k3 ltac:(lia)). repeat split; lia.
    + intros r Hr. rewrite HX. repeat split;
        [ apply (maxbitinsert_bound__dp_body_branches_k3 m0_2 retval_2
                   (retval + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 m0_2 retval_2
                   (retval + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 m1_2 retval_3
                   (retval_5 + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 m1_2 retval_3
                   (retval_5 + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 mX_2 retval_6
                   (Znth (i - 1) dp0_l_2 0) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 mX_2 retval_6
                   (Znth (i - 1) dp0_l_2 0) r (-1000000000) n_pre) ];
        try lia;
        try (intros q Hq; pose proof (PreH61 q ltac:(lia)); lia).
    + intros k4 Hk4. destruct (Z.eq_dec k4 i) as [Heq | Hne].
      * subst k4. rewrite Hsame. lia.
      * rewrite (Hdiff k4 ltac:(lia) Hne). apply PreH63; lia.
    + replace (i + 1 - 1) with i by lia. rewrite HX. exact HmX'.
    + apply (clamped_keep__dp_body_branches_k3 dp0_l_2
               (replace_Znth i (retval + 1) dp0_l_2) i best0 (retval + 1));
        try lia; auto.
      intros j Hj. apply Hdiff; lia.
    + apply (clamped_best1_keep__dp_body_branches_k3 values i best1 (retval_5 + 1));
        try lia; auto.
    + replace (i + 1 - 1) with (i - 1 + 1) by lia.
      apply (clamped_update__dp_body_branches_k3 dp0_l_2
               (replace_Znth i (retval + 1) dp0_l_2) (i - 1) best0_prefix
               (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0));
        try lia; auto.
      intros j Hj. apply Hdiff; lia.
Qed.

Lemma proof_of_solver_entail_wit_12_26 : solver_entail_wit_12_26.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (dp_core__dp_body_branches_k3 values vals_l_2 c_l_2 dp0_l_2
              m0_2 m1_2 mX_2 (replace_Znth i (0 + 1) dp0_l_2)
              n_pre nvals i retval retval_2 retval_6 (0 + 1) (retval_5 + 1)
              ltac:(lia) ltac:(lia) PreH40 PreH47 PreH49 PreH50 PreH53
              PreH34 ltac:(lia) PreH31 ltac:(lia) PreH5 ltac:(lia)
              PreH62 PreH64 PreH65 PreH66
              ltac:(rewrite <- PreH28; lia)
              ltac:(rewrite <- PreH23, <- PreH19; lia)
              eq_refl)
    as [Hbest0 [Hbest1 [Hd0r [Hd1r [Hdiff [Hsame
       [Hlen' [Hdp' [Hm0' [Hm1' HmX']]]]]]]]]].
  assert (Hl0 : Zlength m0_2 = nvals + 1) by (apply (proj1 PreH64)).
  assert (Hl1 : Zlength m1_2 = nvals + 1) by (apply (proj1 PreH65)).
  assert (HlX : Zlength mX_2 = nvals + 1) by (apply (proj1 PreH66)).
  assert (HX : Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0
               = Znth (i - 1) dp0_l_2 0) by (apply Hdiff; lia).
  pose proof (PreH63 (i - 1) ltac:(lia)) as HdpX.
  Exists (MaxBitInsert mX_2 retval_6
            (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)).
  Exists (MaxBitInsert m1_2 retval_2 (retval_5 + 1)).
  Exists (MaxBitInsert m0_2 retval (0 + 1)).
  Exists bit_l1_3 bit_l1_2 bit_l1.
  Exists (replace_Znth i (0 + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - do 12 (try cancel).
  - split_pures; dump_pre_spatial.
    all: try (exact PreH38 || exact PreH39 || exact PreH40 || exact PreH41
              || exact PreH42 || exact PreH43 || exact PreH44 || exact PreH47
              || exact PreH48 || exact PreH50 || exact PreH51 || exact PreH52
              || exact PreH53 || exact PreH70 || exact PreH71 || exact PreH72
              || exact PreH73 || lia
              || exact PreH15 || exact PreH11 || exact PreH4
              || exact Hdp' || exact Hm0' || exact Hm1').
    + intros k3 Hk3.
      pose proof (PreH14 k3 ltac:(lia)). pose proof (PreH10 k3 ltac:(lia)).
      pose proof (PreH3 k3 ltac:(lia)). repeat split; lia.
    + intros r Hr. rewrite HX. repeat split;
        [ apply (maxbitinsert_bound__dp_body_branches_k3 m0_2 retval
                   (0 + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 m0_2 retval
                   (0 + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 m1_2 retval_2
                   (retval_5 + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 m1_2 retval_2
                   (retval_5 + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 mX_2 retval_6
                   (Znth (i - 1) dp0_l_2 0) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 mX_2 retval_6
                   (Znth (i - 1) dp0_l_2 0) r (-1000000000) n_pre) ];
        try lia;
        try (intros q Hq; pose proof (PreH61 q ltac:(lia)); lia).
    + intros k4 Hk4. destruct (Z.eq_dec k4 i) as [Heq | Hne].
      * subst k4. rewrite Hsame. lia.
      * rewrite (Hdiff k4 ltac:(lia) Hne). apply PreH63; lia.
    + replace (i + 1 - 1) with i by lia. rewrite HX. exact HmX'.
    + apply (clamped_keep__dp_body_branches_k3 dp0_l_2
               (replace_Znth i (0 + 1) dp0_l_2) i best0 (0 + 1));
        try lia; auto.
      intros j Hj. apply Hdiff; lia.
    + apply (clamped_best1_keep__dp_body_branches_k3 values i best1 (retval_5 + 1));
        try lia; auto.
    + replace (i + 1 - 1) with (i - 1 + 1) by lia.
      apply (clamped_update__dp_body_branches_k3 dp0_l_2
               (replace_Znth i (0 + 1) dp0_l_2) (i - 1) best0_prefix
               (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0));
        try lia; auto.
      intros j Hj. apply Hdiff; lia.
Qed.

Lemma proof_of_solver_entail_wit_12_27 : solver_entail_wit_12_27.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (dp_core__dp_body_branches_k3 values vals_l_2 c_l_2 dp0_l_2
              m0_2 m1_2 mX_2 (replace_Znth i (retval + 1) dp0_l_2)
              n_pre nvals i retval_2 retval_3 retval_6 (retval + 1) (retval_5 + 1)
              ltac:(lia) ltac:(lia) PreH40 PreH47 PreH49 PreH50 PreH53
              PreH34 ltac:(lia) PreH31 ltac:(lia) PreH5 ltac:(lia)
              PreH62 PreH64 PreH65 PreH66
              ltac:(rewrite <- PreH28; lia)
              ltac:(rewrite <- PreH23, <- PreH19; lia)
              eq_refl)
    as [Hbest0 [Hbest1 [Hd0r [Hd1r [Hdiff [Hsame
       [Hlen' [Hdp' [Hm0' [Hm1' HmX']]]]]]]]]].
  assert (Hl0 : Zlength m0_2 = nvals + 1) by (apply (proj1 PreH64)).
  assert (Hl1 : Zlength m1_2 = nvals + 1) by (apply (proj1 PreH65)).
  assert (HlX : Zlength mX_2 = nvals + 1) by (apply (proj1 PreH66)).
  assert (HX : Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0
               = Znth (i - 1) dp0_l_2 0) by (apply Hdiff; lia).
  pose proof (PreH63 (i - 1) ltac:(lia)) as HdpX.
  Exists (MaxBitInsert mX_2 retval_6
            (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0)).
  Exists (MaxBitInsert m1_2 retval_3 (retval_5 + 1)).
  Exists (MaxBitInsert m0_2 retval_2 (retval + 1)).
  Exists bit_l1_3 bit_l1_2 bit_l1.
  Exists (replace_Znth i (retval + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - do 12 (try cancel).
  - split_pures; dump_pre_spatial.
    all: try (exact PreH38 || exact PreH39 || exact PreH40 || exact PreH41
              || exact PreH42 || exact PreH43 || exact PreH44 || exact PreH47
              || exact PreH48 || exact PreH50 || exact PreH51 || exact PreH52
              || exact PreH53 || exact PreH70 || exact PreH71 || exact PreH72
              || exact PreH73 || lia
              || exact PreH15 || exact PreH11 || exact PreH4
              || exact Hdp' || exact Hm0' || exact Hm1').
    + intros k3 Hk3.
      pose proof (PreH14 k3 ltac:(lia)). pose proof (PreH10 k3 ltac:(lia)).
      pose proof (PreH3 k3 ltac:(lia)). repeat split; lia.
    + intros r Hr. rewrite HX. repeat split;
        [ apply (maxbitinsert_bound__dp_body_branches_k3 m0_2 retval_2
                   (retval + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 m0_2 retval_2
                   (retval + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 m1_2 retval_3
                   (retval_5 + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 m1_2 retval_3
                   (retval_5 + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 mX_2 retval_6
                   (Znth (i - 1) dp0_l_2 0) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 mX_2 retval_6
                   (Znth (i - 1) dp0_l_2 0) r (-1000000000) n_pre) ];
        try lia;
        try (intros q Hq; pose proof (PreH61 q ltac:(lia)); lia).
    + intros k4 Hk4. destruct (Z.eq_dec k4 i) as [Heq | Hne].
      * subst k4. rewrite Hsame. lia.
      * rewrite (Hdiff k4 ltac:(lia) Hne). apply PreH63; lia.
    + replace (i + 1 - 1) with i by lia. rewrite HX. exact HmX'.
    + apply (clamped_keep__dp_body_branches_k3 dp0_l_2
               (replace_Znth i (retval + 1) dp0_l_2) i best0 (retval + 1));
        try lia; auto.
      intros j Hj. apply Hdiff; lia.
    + apply (clamped_best1_keep__dp_body_branches_k3 values i best1 (retval_5 + 1));
        try lia; auto.
    + replace (i + 1 - 1) with (i - 1 + 1) by lia.
      apply (clamped_update__dp_body_branches_k3 dp0_l_2
               (replace_Znth i (retval + 1) dp0_l_2) (i - 1) best0_prefix
               (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0));
        try lia; auto.
      intros j Hj. apply Hdiff; lia.
Qed.

Lemma proof_of_solver_entail_wit_12_28 : solver_entail_wit_12_28.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (dp_core__dp_body_branches_k3 values vals_l_2 c_l_2 dp0_l_2
              m0_2 m1_2 mX_2 (replace_Znth i (0 + 1) dp0_l_2)
              n_pre nvals i retval retval_2 retval_6 (0 + 1) (retval_5 + 1)
              ltac:(lia) ltac:(lia) PreH40 PreH47 PreH49 PreH50 PreH53
              PreH34 ltac:(lia) PreH31 ltac:(lia) PreH5 ltac:(lia)
              PreH62 PreH64 PreH65 PreH66
              ltac:(rewrite <- PreH28; lia)
              ltac:(rewrite <- PreH23, <- PreH19; lia)
              eq_refl)
    as [Hbest0 [Hbest1 [Hd0r [Hd1r [Hdiff [Hsame
       [Hlen' [Hdp' [Hm0' [Hm1' HmX']]]]]]]]]].
  assert (Hl0 : Zlength m0_2 = nvals + 1) by (apply (proj1 PreH64)).
  assert (Hl1 : Zlength m1_2 = nvals + 1) by (apply (proj1 PreH65)).
  assert (HlX : Zlength mX_2 = nvals + 1) by (apply (proj1 PreH66)).
  assert (HX : Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0
               = Znth (i - 1) dp0_l_2 0) by (apply Hdiff; lia).
  pose proof (PreH63 (i - 1) ltac:(lia)) as HdpX.
  Exists (MaxBitInsert mX_2 retval_6
            (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)).
  Exists (MaxBitInsert m1_2 retval_2 (retval_5 + 1)).
  Exists (MaxBitInsert m0_2 retval (0 + 1)).
  Exists bit_l1_3 bit_l1_2 bit_l1.
  Exists (replace_Znth i (0 + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - do 12 (try cancel).
  - split_pures; dump_pre_spatial.
    all: try (exact PreH38 || exact PreH39 || exact PreH40 || exact PreH41
              || exact PreH42 || exact PreH43 || exact PreH44 || exact PreH47
              || exact PreH48 || exact PreH50 || exact PreH51 || exact PreH52
              || exact PreH53 || exact PreH70 || exact PreH71 || exact PreH72
              || exact PreH73 || lia
              || exact PreH15 || exact PreH11 || exact PreH4
              || exact Hdp' || exact Hm0' || exact Hm1').
    + intros k3 Hk3.
      pose proof (PreH14 k3 ltac:(lia)). pose proof (PreH10 k3 ltac:(lia)).
      pose proof (PreH3 k3 ltac:(lia)). repeat split; lia.
    + intros r Hr. rewrite HX. repeat split;
        [ apply (maxbitinsert_bound__dp_body_branches_k3 m0_2 retval
                   (0 + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 m0_2 retval
                   (0 + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 m1_2 retval_2
                   (retval_5 + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 m1_2 retval_2
                   (retval_5 + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 mX_2 retval_6
                   (Znth (i - 1) dp0_l_2 0) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 mX_2 retval_6
                   (Znth (i - 1) dp0_l_2 0) r (-1000000000) n_pre) ];
        try lia;
        try (intros q Hq; pose proof (PreH61 q ltac:(lia)); lia).
    + intros k4 Hk4. destruct (Z.eq_dec k4 i) as [Heq | Hne].
      * subst k4. rewrite Hsame. lia.
      * rewrite (Hdiff k4 ltac:(lia) Hne). apply PreH63; lia.
    + replace (i + 1 - 1) with i by lia. rewrite HX. exact HmX'.
    + apply (clamped_keep__dp_body_branches_k3 dp0_l_2
               (replace_Znth i (0 + 1) dp0_l_2) i best0 (0 + 1));
        try lia; auto.
      intros j Hj. apply Hdiff; lia.
    + apply (clamped_best1_keep__dp_body_branches_k3 values i best1 (retval_5 + 1));
        try lia; auto.
    + replace (i + 1 - 1) with (i - 1 + 1) by lia.
      apply (clamped_update__dp_body_branches_k3 dp0_l_2
               (replace_Znth i (0 + 1) dp0_l_2) (i - 1) best0_prefix
               (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0));
        try lia; auto.
      intros j Hj. apply Hdiff; lia.
Qed.

Lemma proof_of_solver_entail_wit_12_29 : solver_entail_wit_12_29.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (dp_core__dp_body_branches_k3 values vals_l_2 c_l_2 dp0_l_2
              m0_2 m1_2 mX_2 (replace_Znth i (retval + 1) dp0_l_2)
              n_pre nvals i retval_2 retval_3 retval_6 (retval + 1) (retval_4 + 1)
              ltac:(lia) ltac:(lia) PreH40 PreH47 PreH49 PreH50 PreH53
              PreH34 ltac:(lia) PreH31 ltac:(lia) PreH5 ltac:(lia)
              PreH62 PreH64 PreH65 PreH66
              ltac:(rewrite <- PreH28; lia)
              ltac:(rewrite <- PreH23, <- PreH19; lia)
              eq_refl)
    as [Hbest0 [Hbest1 [Hd0r [Hd1r [Hdiff [Hsame
       [Hlen' [Hdp' [Hm0' [Hm1' HmX']]]]]]]]]].
  assert (Hl0 : Zlength m0_2 = nvals + 1) by (apply (proj1 PreH64)).
  assert (Hl1 : Zlength m1_2 = nvals + 1) by (apply (proj1 PreH65)).
  assert (HlX : Zlength mX_2 = nvals + 1) by (apply (proj1 PreH66)).
  assert (HX : Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0
               = Znth (i - 1) dp0_l_2 0) by (apply Hdiff; lia).
  pose proof (PreH63 (i - 1) ltac:(lia)) as HdpX.
  Exists (MaxBitInsert mX_2 retval_6
            (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0)).
  Exists (MaxBitInsert m1_2 retval_3 (retval_4 + 1)).
  Exists (MaxBitInsert m0_2 retval_2 (retval + 1)).
  Exists bit_l1_3 bit_l1_2 bit_l1.
  Exists (replace_Znth i (retval + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - do 12 (try cancel).
  - split_pures; dump_pre_spatial.
    all: try (exact PreH38 || exact PreH39 || exact PreH40 || exact PreH41
              || exact PreH42 || exact PreH43 || exact PreH44 || exact PreH47
              || exact PreH48 || exact PreH50 || exact PreH51 || exact PreH52
              || exact PreH53 || exact PreH70 || exact PreH71 || exact PreH72
              || exact PreH73 || lia
              || exact PreH15 || exact PreH11 || exact PreH4
              || exact Hdp' || exact Hm0' || exact Hm1').
    + intros k3 Hk3.
      pose proof (PreH14 k3 ltac:(lia)). pose proof (PreH10 k3 ltac:(lia)).
      pose proof (PreH3 k3 ltac:(lia)). repeat split; lia.
    + intros r Hr. rewrite HX. repeat split;
        [ apply (maxbitinsert_bound__dp_body_branches_k3 m0_2 retval_2
                   (retval + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 m0_2 retval_2
                   (retval + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 m1_2 retval_3
                   (retval_4 + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 m1_2 retval_3
                   (retval_4 + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 mX_2 retval_6
                   (Znth (i - 1) dp0_l_2 0) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 mX_2 retval_6
                   (Znth (i - 1) dp0_l_2 0) r (-1000000000) n_pre) ];
        try lia;
        try (intros q Hq; pose proof (PreH61 q ltac:(lia)); lia).
    + intros k4 Hk4. destruct (Z.eq_dec k4 i) as [Heq | Hne].
      * subst k4. rewrite Hsame. lia.
      * rewrite (Hdiff k4 ltac:(lia) Hne). apply PreH63; lia.
    + replace (i + 1 - 1) with i by lia. rewrite HX. exact HmX'.
    + apply (clamped_keep__dp_body_branches_k3 dp0_l_2
               (replace_Znth i (retval + 1) dp0_l_2) i best0 (retval + 1));
        try lia; auto.
      intros j Hj. apply Hdiff; lia.
    + apply (clamped_best1_keep__dp_body_branches_k3 values i best1 (retval_4 + 1));
        try lia; auto.
    + replace (i + 1 - 1) with (i - 1 + 1) by lia.
      apply (clamped_update__dp_body_branches_k3 dp0_l_2
               (replace_Znth i (retval + 1) dp0_l_2) (i - 1) best0_prefix
               (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0));
        try lia; auto.
      intros j Hj. apply Hdiff; lia.
Qed.

Lemma proof_of_solver_entail_wit_12_30 : solver_entail_wit_12_30.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (dp_core__dp_body_branches_k3 values vals_l_2 c_l_2 dp0_l_2
              m0_2 m1_2 mX_2 (replace_Znth i (0 + 1) dp0_l_2)
              n_pre nvals i retval retval_2 retval_6 (0 + 1) (retval_4 + 1)
              ltac:(lia) ltac:(lia) PreH40 PreH47 PreH49 PreH50 PreH53
              PreH34 ltac:(lia) PreH31 ltac:(lia) PreH5 ltac:(lia)
              PreH62 PreH64 PreH65 PreH66
              ltac:(rewrite <- PreH28; lia)
              ltac:(rewrite <- PreH23, <- PreH19; lia)
              eq_refl)
    as [Hbest0 [Hbest1 [Hd0r [Hd1r [Hdiff [Hsame
       [Hlen' [Hdp' [Hm0' [Hm1' HmX']]]]]]]]]].
  assert (Hl0 : Zlength m0_2 = nvals + 1) by (apply (proj1 PreH64)).
  assert (Hl1 : Zlength m1_2 = nvals + 1) by (apply (proj1 PreH65)).
  assert (HlX : Zlength mX_2 = nvals + 1) by (apply (proj1 PreH66)).
  assert (HX : Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0
               = Znth (i - 1) dp0_l_2 0) by (apply Hdiff; lia).
  pose proof (PreH63 (i - 1) ltac:(lia)) as HdpX.
  Exists (MaxBitInsert mX_2 retval_6
            (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)).
  Exists (MaxBitInsert m1_2 retval_2 (retval_4 + 1)).
  Exists (MaxBitInsert m0_2 retval (0 + 1)).
  Exists bit_l1_3 bit_l1_2 bit_l1.
  Exists (replace_Znth i (0 + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - do 12 (try cancel).
  - split_pures; dump_pre_spatial.
    all: try (exact PreH38 || exact PreH39 || exact PreH40 || exact PreH41
              || exact PreH42 || exact PreH43 || exact PreH44 || exact PreH47
              || exact PreH48 || exact PreH50 || exact PreH51 || exact PreH52
              || exact PreH53 || exact PreH70 || exact PreH71 || exact PreH72
              || exact PreH73 || lia
              || exact PreH15 || exact PreH11 || exact PreH4
              || exact Hdp' || exact Hm0' || exact Hm1').
    + intros k3 Hk3.
      pose proof (PreH14 k3 ltac:(lia)). pose proof (PreH10 k3 ltac:(lia)).
      pose proof (PreH3 k3 ltac:(lia)). repeat split; lia.
    + intros r Hr. rewrite HX. repeat split;
        [ apply (maxbitinsert_bound__dp_body_branches_k3 m0_2 retval
                   (0 + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 m0_2 retval
                   (0 + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 m1_2 retval_2
                   (retval_4 + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 m1_2 retval_2
                   (retval_4 + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 mX_2 retval_6
                   (Znth (i - 1) dp0_l_2 0) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 mX_2 retval_6
                   (Znth (i - 1) dp0_l_2 0) r (-1000000000) n_pre) ];
        try lia;
        try (intros q Hq; pose proof (PreH61 q ltac:(lia)); lia).
    + intros k4 Hk4. destruct (Z.eq_dec k4 i) as [Heq | Hne].
      * subst k4. rewrite Hsame. lia.
      * rewrite (Hdiff k4 ltac:(lia) Hne). apply PreH63; lia.
    + replace (i + 1 - 1) with i by lia. rewrite HX. exact HmX'.
    + apply (clamped_keep__dp_body_branches_k3 dp0_l_2
               (replace_Znth i (0 + 1) dp0_l_2) i best0 (0 + 1));
        try lia; auto.
      intros j Hj. apply Hdiff; lia.
    + apply (clamped_best1_keep__dp_body_branches_k3 values i best1 (retval_4 + 1));
        try lia; auto.
    + replace (i + 1 - 1) with (i - 1 + 1) by lia.
      apply (clamped_update__dp_body_branches_k3 dp0_l_2
               (replace_Znth i (0 + 1) dp0_l_2) (i - 1) best0_prefix
               (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0));
        try lia; auto.
      intros j Hj. apply Hdiff; lia.
Qed.

Lemma proof_of_solver_entail_wit_12_31 : solver_entail_wit_12_31.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (dp_core__dp_body_branches_k3 values vals_l_2 c_l_2 dp0_l_2
              m0_2 m1_2 mX_2 (replace_Znth i (retval + 1) dp0_l_2)
              n_pre nvals i retval_2 retval_3 retval_6 (retval + 1) (0 + 1)
              ltac:(lia) ltac:(lia) PreH40 PreH47 PreH49 PreH50 PreH53
              PreH34 ltac:(lia) PreH31 ltac:(lia) PreH5 ltac:(lia)
              PreH62 PreH64 PreH65 PreH66
              ltac:(rewrite <- PreH28; lia)
              ltac:(rewrite <- PreH23, <- PreH19; lia)
              eq_refl)
    as [Hbest0 [Hbest1 [Hd0r [Hd1r [Hdiff [Hsame
       [Hlen' [Hdp' [Hm0' [Hm1' HmX']]]]]]]]]].
  assert (Hl0 : Zlength m0_2 = nvals + 1) by (apply (proj1 PreH64)).
  assert (Hl1 : Zlength m1_2 = nvals + 1) by (apply (proj1 PreH65)).
  assert (HlX : Zlength mX_2 = nvals + 1) by (apply (proj1 PreH66)).
  assert (HX : Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0
               = Znth (i - 1) dp0_l_2 0) by (apply Hdiff; lia).
  pose proof (PreH63 (i - 1) ltac:(lia)) as HdpX.
  Exists (MaxBitInsert mX_2 retval_6
            (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0)).
  Exists (MaxBitInsert m1_2 retval_3 (0 + 1)).
  Exists (MaxBitInsert m0_2 retval_2 (retval + 1)).
  Exists bit_l1_3 bit_l1_2 bit_l1.
  Exists (replace_Znth i (retval + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - do 12 (try cancel).
  - split_pures; dump_pre_spatial.
    all: try (exact PreH38 || exact PreH39 || exact PreH40 || exact PreH41
              || exact PreH42 || exact PreH43 || exact PreH44 || exact PreH47
              || exact PreH48 || exact PreH50 || exact PreH51 || exact PreH52
              || exact PreH53 || exact PreH70 || exact PreH71 || exact PreH72
              || exact PreH73 || lia
              || exact PreH15 || exact PreH11 || exact PreH4
              || exact Hdp' || exact Hm0' || exact Hm1').
    + intros k3 Hk3.
      pose proof (PreH14 k3 ltac:(lia)). pose proof (PreH10 k3 ltac:(lia)).
      pose proof (PreH3 k3 ltac:(lia)). repeat split; lia.
    + intros r Hr. rewrite HX. repeat split;
        [ apply (maxbitinsert_bound__dp_body_branches_k3 m0_2 retval_2
                   (retval + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 m0_2 retval_2
                   (retval + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 m1_2 retval_3
                   (0 + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 m1_2 retval_3
                   (0 + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 mX_2 retval_6
                   (Znth (i - 1) dp0_l_2 0) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 mX_2 retval_6
                   (Znth (i - 1) dp0_l_2 0) r (-1000000000) n_pre) ];
        try lia;
        try (intros q Hq; pose proof (PreH61 q ltac:(lia)); lia).
    + intros k4 Hk4. destruct (Z.eq_dec k4 i) as [Heq | Hne].
      * subst k4. rewrite Hsame. lia.
      * rewrite (Hdiff k4 ltac:(lia) Hne). apply PreH63; lia.
    + replace (i + 1 - 1) with i by lia. rewrite HX. exact HmX'.
    + apply (clamped_keep__dp_body_branches_k3 dp0_l_2
               (replace_Znth i (retval + 1) dp0_l_2) i best0 (retval + 1));
        try lia; auto.
      intros j Hj. apply Hdiff; lia.
    + apply (clamped_best1_keep__dp_body_branches_k3 values i best1 (0 + 1));
        try lia; auto.
    + replace (i + 1 - 1) with (i - 1 + 1) by lia.
      apply (clamped_update__dp_body_branches_k3 dp0_l_2
               (replace_Znth i (retval + 1) dp0_l_2) (i - 1) best0_prefix
               (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0));
        try lia; auto.
      intros j Hj. apply Hdiff; lia.
Qed.

Lemma proof_of_solver_entail_wit_12_32 : solver_entail_wit_12_32.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (dp_core__dp_body_branches_k3 values vals_l_2 c_l_2 dp0_l_2
              m0_2 m1_2 mX_2 (replace_Znth i (0 + 1) dp0_l_2)
              n_pre nvals i retval retval_2 retval_6 (0 + 1) (0 + 1)
              ltac:(lia) ltac:(lia) PreH40 PreH47 PreH49 PreH50 PreH53
              PreH34 ltac:(lia) PreH31 ltac:(lia) PreH5 ltac:(lia)
              PreH62 PreH64 PreH65 PreH66
              ltac:(rewrite <- PreH28; lia)
              ltac:(rewrite <- PreH23, <- PreH19; lia)
              eq_refl)
    as [Hbest0 [Hbest1 [Hd0r [Hd1r [Hdiff [Hsame
       [Hlen' [Hdp' [Hm0' [Hm1' HmX']]]]]]]]]].
  assert (Hl0 : Zlength m0_2 = nvals + 1) by (apply (proj1 PreH64)).
  assert (Hl1 : Zlength m1_2 = nvals + 1) by (apply (proj1 PreH65)).
  assert (HlX : Zlength mX_2 = nvals + 1) by (apply (proj1 PreH66)).
  assert (HX : Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0
               = Znth (i - 1) dp0_l_2 0) by (apply Hdiff; lia).
  pose proof (PreH63 (i - 1) ltac:(lia)) as HdpX.
  Exists (MaxBitInsert mX_2 retval_6
            (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)).
  Exists (MaxBitInsert m1_2 retval_2 (0 + 1)).
  Exists (MaxBitInsert m0_2 retval (0 + 1)).
  Exists bit_l1_3 bit_l1_2 bit_l1.
  Exists (replace_Znth i (0 + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - do 12 (try cancel).
  - split_pures; dump_pre_spatial.
    all: try (exact PreH38 || exact PreH39 || exact PreH40 || exact PreH41
              || exact PreH42 || exact PreH43 || exact PreH44 || exact PreH47
              || exact PreH48 || exact PreH50 || exact PreH51 || exact PreH52
              || exact PreH53 || exact PreH70 || exact PreH71 || exact PreH72
              || exact PreH73 || lia
              || exact PreH15 || exact PreH11 || exact PreH4
              || exact Hdp' || exact Hm0' || exact Hm1').
    + intros k3 Hk3.
      pose proof (PreH14 k3 ltac:(lia)). pose proof (PreH10 k3 ltac:(lia)).
      pose proof (PreH3 k3 ltac:(lia)). repeat split; lia.
    + intros r Hr. rewrite HX. repeat split;
        [ apply (maxbitinsert_bound__dp_body_branches_k3 m0_2 retval
                   (0 + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 m0_2 retval
                   (0 + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 m1_2 retval_2
                   (0 + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 m1_2 retval_2
                   (0 + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 mX_2 retval_6
                   (Znth (i - 1) dp0_l_2 0) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 mX_2 retval_6
                   (Znth (i - 1) dp0_l_2 0) r (-1000000000) n_pre) ];
        try lia;
        try (intros q Hq; pose proof (PreH61 q ltac:(lia)); lia).
    + intros k4 Hk4. destruct (Z.eq_dec k4 i) as [Heq | Hne].
      * subst k4. rewrite Hsame. lia.
      * rewrite (Hdiff k4 ltac:(lia) Hne). apply PreH63; lia.
    + replace (i + 1 - 1) with i by lia. rewrite HX. exact HmX'.
    + apply (clamped_keep__dp_body_branches_k3 dp0_l_2
               (replace_Znth i (0 + 1) dp0_l_2) i best0 (0 + 1));
        try lia; auto.
      intros j Hj. apply Hdiff; lia.
    + apply (clamped_best1_keep__dp_body_branches_k3 values i best1 (0 + 1));
        try lia; auto.
    + replace (i + 1 - 1) with (i - 1 + 1) by lia.
      apply (clamped_update__dp_body_branches_k3 dp0_l_2
               (replace_Znth i (0 + 1) dp0_l_2) (i - 1) best0_prefix
               (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0));
        try lia; auto.
      intros j Hj. apply Hdiff; lia.
Qed.

Lemma proof_of_solver_entail_wit_12_33 : solver_entail_wit_12_33.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (dp_core__dp_body_branches_k3 values vals_l_2 c_l_2 dp0_l_2
              m0_2 m1_2 mX_2 (replace_Znth i (retval + 1) dp0_l_2)
              n_pre nvals i retval_3 retval_4 retval_6 (retval + 1) (retval_2 + 1)
              ltac:(lia) ltac:(lia) PreH40 PreH47 PreH49 PreH50 PreH53
              PreH34 ltac:(lia) PreH31 ltac:(lia) PreH5 ltac:(lia)
              PreH62 PreH64 PreH65 PreH66
              ltac:(rewrite <- PreH28; lia)
              ltac:(rewrite <- PreH23, <- PreH19; lia)
              eq_refl)
    as [Hbest0 [Hbest1 [Hd0r [Hd1r [Hdiff [Hsame
       [Hlen' [Hdp' [Hm0' [Hm1' HmX']]]]]]]]]].
  assert (Hl0 : Zlength m0_2 = nvals + 1) by (apply (proj1 PreH64)).
  assert (Hl1 : Zlength m1_2 = nvals + 1) by (apply (proj1 PreH65)).
  assert (HlX : Zlength mX_2 = nvals + 1) by (apply (proj1 PreH66)).
  assert (HX : Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0
               = Znth (i - 1) dp0_l_2 0) by (apply Hdiff; lia).
  pose proof (PreH63 (i - 1) ltac:(lia)) as HdpX.
  Exists (MaxBitInsert mX_2 retval_6
            (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0)).
  Exists (MaxBitInsert m1_2 retval_4 (retval_2 + 1)).
  Exists (MaxBitInsert m0_2 retval_3 (retval + 1)).
  Exists bit_l1_3 bit_l1_2 bit_l1.
  Exists (replace_Znth i (retval + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - do 12 (try cancel).
  - split_pures; dump_pre_spatial.
    all: try (exact PreH38 || exact PreH39 || exact PreH40 || exact PreH41
              || exact PreH42 || exact PreH43 || exact PreH44 || exact PreH47
              || exact PreH48 || exact PreH50 || exact PreH51 || exact PreH52
              || exact PreH53 || exact PreH70 || exact PreH71 || exact PreH72
              || exact PreH73 || lia
              || exact PreH15 || exact PreH11 || exact PreH4
              || exact Hdp' || exact Hm0' || exact Hm1').
    + intros k3 Hk3.
      pose proof (PreH14 k3 ltac:(lia)). pose proof (PreH10 k3 ltac:(lia)).
      pose proof (PreH3 k3 ltac:(lia)). repeat split; lia.
    + intros r Hr. rewrite HX. repeat split;
        [ apply (maxbitinsert_bound__dp_body_branches_k3 m0_2 retval_3
                   (retval + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 m0_2 retval_3
                   (retval + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 m1_2 retval_4
                   (retval_2 + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 m1_2 retval_4
                   (retval_2 + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 mX_2 retval_6
                   (Znth (i - 1) dp0_l_2 0) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 mX_2 retval_6
                   (Znth (i - 1) dp0_l_2 0) r (-1000000000) n_pre) ];
        try lia;
        try (intros q Hq; pose proof (PreH61 q ltac:(lia)); lia).
    + intros k4 Hk4. destruct (Z.eq_dec k4 i) as [Heq | Hne].
      * subst k4. rewrite Hsame. lia.
      * rewrite (Hdiff k4 ltac:(lia) Hne). apply PreH63; lia.
    + replace (i + 1 - 1) with i by lia. rewrite HX. exact HmX'.
    + apply (clamped_update__dp_body_branches_k3 dp0_l_2
               (replace_Znth i (retval + 1) dp0_l_2) i best0 (retval + 1));
        try lia; auto.
      intros j Hj. apply Hdiff; lia.
    + apply (clamped_best1_update__dp_body_branches_k3 values i best1 (retval_2 + 1));
        try lia; auto.
    + replace (i + 1 - 1) with (i - 1 + 1) by lia.
      apply (clamped_keep__dp_body_branches_k3 dp0_l_2
               (replace_Znth i (retval + 1) dp0_l_2) (i - 1) best0_prefix
               (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0));
        try lia; auto.
      intros j Hj. apply Hdiff; lia.
Qed.

Lemma proof_of_solver_entail_wit_12_34 : solver_entail_wit_12_34.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (dp_core__dp_body_branches_k3 values vals_l_2 c_l_2 dp0_l_2
              m0_2 m1_2 mX_2 (replace_Znth i (0 + 1) dp0_l_2)
              n_pre nvals i retval_2 retval_3 retval_6 (0 + 1) (retval + 1)
              ltac:(lia) ltac:(lia) PreH40 PreH47 PreH49 PreH50 PreH53
              PreH34 ltac:(lia) PreH31 ltac:(lia) PreH5 ltac:(lia)
              PreH62 PreH64 PreH65 PreH66
              ltac:(rewrite <- PreH28; lia)
              ltac:(rewrite <- PreH23, <- PreH19; lia)
              eq_refl)
    as [Hbest0 [Hbest1 [Hd0r [Hd1r [Hdiff [Hsame
       [Hlen' [Hdp' [Hm0' [Hm1' HmX']]]]]]]]]].
  assert (Hl0 : Zlength m0_2 = nvals + 1) by (apply (proj1 PreH64)).
  assert (Hl1 : Zlength m1_2 = nvals + 1) by (apply (proj1 PreH65)).
  assert (HlX : Zlength mX_2 = nvals + 1) by (apply (proj1 PreH66)).
  assert (HX : Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0
               = Znth (i - 1) dp0_l_2 0) by (apply Hdiff; lia).
  pose proof (PreH63 (i - 1) ltac:(lia)) as HdpX.
  Exists (MaxBitInsert mX_2 retval_6
            (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)).
  Exists (MaxBitInsert m1_2 retval_3 (retval + 1)).
  Exists (MaxBitInsert m0_2 retval_2 (0 + 1)).
  Exists bit_l1_3 bit_l1_2 bit_l1.
  Exists (replace_Znth i (0 + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - do 12 (try cancel).
  - split_pures; dump_pre_spatial.
    all: try (exact PreH38 || exact PreH39 || exact PreH40 || exact PreH41
              || exact PreH42 || exact PreH43 || exact PreH44 || exact PreH47
              || exact PreH48 || exact PreH50 || exact PreH51 || exact PreH52
              || exact PreH53 || exact PreH70 || exact PreH71 || exact PreH72
              || exact PreH73 || lia
              || exact PreH15 || exact PreH11 || exact PreH4
              || exact Hdp' || exact Hm0' || exact Hm1').
    + intros k3 Hk3.
      pose proof (PreH14 k3 ltac:(lia)). pose proof (PreH10 k3 ltac:(lia)).
      pose proof (PreH3 k3 ltac:(lia)). repeat split; lia.
    + intros r Hr. rewrite HX. repeat split;
        [ apply (maxbitinsert_bound__dp_body_branches_k3 m0_2 retval_2
                   (0 + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 m0_2 retval_2
                   (0 + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 m1_2 retval_3
                   (retval + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 m1_2 retval_3
                   (retval + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 mX_2 retval_6
                   (Znth (i - 1) dp0_l_2 0) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 mX_2 retval_6
                   (Znth (i - 1) dp0_l_2 0) r (-1000000000) n_pre) ];
        try lia;
        try (intros q Hq; pose proof (PreH61 q ltac:(lia)); lia).
    + intros k4 Hk4. destruct (Z.eq_dec k4 i) as [Heq | Hne].
      * subst k4. rewrite Hsame. lia.
      * rewrite (Hdiff k4 ltac:(lia) Hne). apply PreH63; lia.
    + replace (i + 1 - 1) with i by lia. rewrite HX. exact HmX'.
    + apply (clamped_update__dp_body_branches_k3 dp0_l_2
               (replace_Znth i (0 + 1) dp0_l_2) i best0 (0 + 1));
        try lia; auto.
      intros j Hj. apply Hdiff; lia.
    + apply (clamped_best1_update__dp_body_branches_k3 values i best1 (retval + 1));
        try lia; auto.
    + replace (i + 1 - 1) with (i - 1 + 1) by lia.
      apply (clamped_keep__dp_body_branches_k3 dp0_l_2
               (replace_Znth i (0 + 1) dp0_l_2) (i - 1) best0_prefix
               (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0));
        try lia; auto.
      intros j Hj. apply Hdiff; lia.
Qed.

Lemma proof_of_solver_entail_wit_12_35 : solver_entail_wit_12_35.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (dp_core__dp_body_branches_k3 values vals_l_2 c_l_2 dp0_l_2
              m0_2 m1_2 mX_2 (replace_Znth i (retval + 1) dp0_l_2)
              n_pre nvals i retval_3 retval_4 retval_6 (retval + 1) (retval_2 + 1)
              ltac:(lia) ltac:(lia) PreH40 PreH47 PreH49 PreH50 PreH53
              PreH34 ltac:(lia) PreH31 ltac:(lia) PreH5 ltac:(lia)
              PreH62 PreH64 PreH65 PreH66
              ltac:(rewrite <- PreH28; lia)
              ltac:(rewrite <- PreH23, <- PreH19; lia)
              eq_refl)
    as [Hbest0 [Hbest1 [Hd0r [Hd1r [Hdiff [Hsame
       [Hlen' [Hdp' [Hm0' [Hm1' HmX']]]]]]]]]].
  assert (Hl0 : Zlength m0_2 = nvals + 1) by (apply (proj1 PreH64)).
  assert (Hl1 : Zlength m1_2 = nvals + 1) by (apply (proj1 PreH65)).
  assert (HlX : Zlength mX_2 = nvals + 1) by (apply (proj1 PreH66)).
  assert (HX : Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0
               = Znth (i - 1) dp0_l_2 0) by (apply Hdiff; lia).
  pose proof (PreH63 (i - 1) ltac:(lia)) as HdpX.
  Exists (MaxBitInsert mX_2 retval_6
            (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0)).
  Exists (MaxBitInsert m1_2 retval_4 (retval_2 + 1)).
  Exists (MaxBitInsert m0_2 retval_3 (retval + 1)).
  Exists bit_l1_3 bit_l1_2 bit_l1.
  Exists (replace_Znth i (retval + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - do 12 (try cancel).
  - split_pures; dump_pre_spatial.
    all: try (exact PreH38 || exact PreH39 || exact PreH40 || exact PreH41
              || exact PreH42 || exact PreH43 || exact PreH44 || exact PreH47
              || exact PreH48 || exact PreH50 || exact PreH51 || exact PreH52
              || exact PreH53 || exact PreH70 || exact PreH71 || exact PreH72
              || exact PreH73 || lia
              || exact PreH15 || exact PreH11 || exact PreH4
              || exact Hdp' || exact Hm0' || exact Hm1').
    + intros k3 Hk3.
      pose proof (PreH14 k3 ltac:(lia)). pose proof (PreH10 k3 ltac:(lia)).
      pose proof (PreH3 k3 ltac:(lia)). repeat split; lia.
    + intros r Hr. rewrite HX. repeat split;
        [ apply (maxbitinsert_bound__dp_body_branches_k3 m0_2 retval_3
                   (retval + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 m0_2 retval_3
                   (retval + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 m1_2 retval_4
                   (retval_2 + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 m1_2 retval_4
                   (retval_2 + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 mX_2 retval_6
                   (Znth (i - 1) dp0_l_2 0) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 mX_2 retval_6
                   (Znth (i - 1) dp0_l_2 0) r (-1000000000) n_pre) ];
        try lia;
        try (intros q Hq; pose proof (PreH61 q ltac:(lia)); lia).
    + intros k4 Hk4. destruct (Z.eq_dec k4 i) as [Heq | Hne].
      * subst k4. rewrite Hsame. lia.
      * rewrite (Hdiff k4 ltac:(lia) Hne). apply PreH63; lia.
    + replace (i + 1 - 1) with i by lia. rewrite HX. exact HmX'.
    + apply (clamped_update__dp_body_branches_k3 dp0_l_2
               (replace_Znth i (retval + 1) dp0_l_2) i best0 (retval + 1));
        try lia; auto.
      intros j Hj. apply Hdiff; lia.
    + apply (clamped_best1_update__dp_body_branches_k3 values i best1 (retval_2 + 1));
        try lia; auto.
    + replace (i + 1 - 1) with (i - 1 + 1) by lia.
      apply (clamped_keep__dp_body_branches_k3 dp0_l_2
               (replace_Znth i (retval + 1) dp0_l_2) (i - 1) best0_prefix
               (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0));
        try lia; auto.
      intros j Hj. apply Hdiff; lia.
Qed.

Lemma proof_of_solver_entail_wit_12_36 : solver_entail_wit_12_36.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (dp_core__dp_body_branches_k3 values vals_l_2 c_l_2 dp0_l_2
              m0_2 m1_2 mX_2 (replace_Znth i (0 + 1) dp0_l_2)
              n_pre nvals i retval_2 retval_3 retval_6 (0 + 1) (retval + 1)
              ltac:(lia) ltac:(lia) PreH40 PreH47 PreH49 PreH50 PreH53
              PreH34 ltac:(lia) PreH31 ltac:(lia) PreH5 ltac:(lia)
              PreH62 PreH64 PreH65 PreH66
              ltac:(rewrite <- PreH28; lia)
              ltac:(rewrite <- PreH23, <- PreH19; lia)
              eq_refl)
    as [Hbest0 [Hbest1 [Hd0r [Hd1r [Hdiff [Hsame
       [Hlen' [Hdp' [Hm0' [Hm1' HmX']]]]]]]]]].
  assert (Hl0 : Zlength m0_2 = nvals + 1) by (apply (proj1 PreH64)).
  assert (Hl1 : Zlength m1_2 = nvals + 1) by (apply (proj1 PreH65)).
  assert (HlX : Zlength mX_2 = nvals + 1) by (apply (proj1 PreH66)).
  assert (HX : Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0
               = Znth (i - 1) dp0_l_2 0) by (apply Hdiff; lia).
  pose proof (PreH63 (i - 1) ltac:(lia)) as HdpX.
  Exists (MaxBitInsert mX_2 retval_6
            (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)).
  Exists (MaxBitInsert m1_2 retval_3 (retval + 1)).
  Exists (MaxBitInsert m0_2 retval_2 (0 + 1)).
  Exists bit_l1_3 bit_l1_2 bit_l1.
  Exists (replace_Znth i (0 + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - do 12 (try cancel).
  - split_pures; dump_pre_spatial.
    all: try (exact PreH38 || exact PreH39 || exact PreH40 || exact PreH41
              || exact PreH42 || exact PreH43 || exact PreH44 || exact PreH47
              || exact PreH48 || exact PreH50 || exact PreH51 || exact PreH52
              || exact PreH53 || exact PreH70 || exact PreH71 || exact PreH72
              || exact PreH73 || lia
              || exact PreH15 || exact PreH11 || exact PreH4
              || exact Hdp' || exact Hm0' || exact Hm1').
    + intros k3 Hk3.
      pose proof (PreH14 k3 ltac:(lia)). pose proof (PreH10 k3 ltac:(lia)).
      pose proof (PreH3 k3 ltac:(lia)). repeat split; lia.
    + intros r Hr. rewrite HX. repeat split;
        [ apply (maxbitinsert_bound__dp_body_branches_k3 m0_2 retval_2
                   (0 + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 m0_2 retval_2
                   (0 + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 m1_2 retval_3
                   (retval + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 m1_2 retval_3
                   (retval + 1) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 mX_2 retval_6
                   (Znth (i - 1) dp0_l_2 0) r (-1000000000) n_pre)
        | apply (maxbitinsert_bound__dp_body_branches_k3 mX_2 retval_6
                   (Znth (i - 1) dp0_l_2 0) r (-1000000000) n_pre) ];
        try lia;
        try (intros q Hq; pose proof (PreH61 q ltac:(lia)); lia).
    + intros k4 Hk4. destruct (Z.eq_dec k4 i) as [Heq | Hne].
      * subst k4. rewrite Hsame. lia.
      * rewrite (Hdiff k4 ltac:(lia) Hne). apply PreH63; lia.
    + replace (i + 1 - 1) with i by lia. rewrite HX. exact HmX'.
    + apply (clamped_update__dp_body_branches_k3 dp0_l_2
               (replace_Znth i (0 + 1) dp0_l_2) i best0 (0 + 1));
        try lia; auto.
      intros j Hj. apply Hdiff; lia.
    + apply (clamped_best1_update__dp_body_branches_k3 values i best1 (retval + 1));
        try lia; auto.
    + replace (i + 1 - 1) with (i - 1 + 1) by lia.
      apply (clamped_keep__dp_body_branches_k3 dp0_l_2
               (replace_Znth i (0 + 1) dp0_l_2) (i - 1) best0_prefix
               (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0));
        try lia; auto.
      intros j Hj. apply Hdiff; lia.
Qed.

Lemma proof_of_solver_entail_wit_12_37 : solver_entail_wit_12_37.
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
             retval_3 retval (retval + 1));
      [lia | exact PreH53 | exact PreH62 | exact PreH64 | exact PreH34 | exact PreH28 | lia]. }
  assert (Hbest1 : Best1EndingAt values i (retval_2 + 1)).
  { apply (best1_step__dp_body_branches_k4 values vals_l_2 dp0_l_2 m1_2 mX_2 nvals i
             retval_4 retval_2 retval_5 retval_2);
      [lia | exact PreH53 | exact PreH62 | exact PreH65 | exact PreH66 | exact PreH31
      | exact PreH23 | exact PreH19 | lia]. }
  assert (Hd0b : retval + 1 <= n_pre).
  { pose proof (best0_value_bound__dp_body_branches_k4 values i (retval + 1) ltac:(lia) Hbest0).
    lia. }
  assert (Hd1b : retval_2 + 1 <= n_pre).
  { pose proof (best1_value_bound__dp_body_branches_k4 values i (retval_2 + 1) ltac:(lia) Hbest1).
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
                  (MaxBitInsert m0_2 retval_3 (retval + 1)) (i + 1) nvals).
  { apply (bit_model_insert__dp_body_branches_k4 values vals_l_2 dp0_l_2
             (replace_Znth i (retval + 1) dp0_l_2) m0_2 nvals i retval_3 (retval + 1));
      [lia | exact Hsi | exact PreH64 | exact PreH34 | exact Hkeep | exact Hnew]. }
  assert (HB1 : Bit1Model values vals_l_2 (MaxBitInsert m1_2 retval_4 (retval_2 + 1))
                  (i + 1) nvals).
  { apply (bit1_model_insert__dp_body_branches_k4 values vals_l_2 m1_2 nvals i retval_4
             (retval_2 + 1));
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
  assert (HCB : ClampedBest1Upto values (i + 1) (retval_2 + 1)).
  { apply (clamped_best1_step__dp_body_branches_k4 values i best1 (retval_2 + 1) (retval_2 + 1));
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
     (((-1000000000 <= Znth r (MaxBitInsert m0_2 retval_3 (retval + 1)) 0 <= n_pre /\
        -1000000000 <= Znth r (MaxBitInsert m1_2 retval_4 (retval_2 + 1)) 0) /\
       Znth r (MaxBitInsert m1_2 retval_4 (retval_2 + 1)) 0 <= n_pre) /\
      -1000000000 <= Znth r (MaxBitInsert mX_2 retval_6
        (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0)) 0) /\
     Znth r (MaxBitInsert mX_2 retval_6
        (Znth (i - 1) (replace_Znth i (retval + 1) dp0_l_2) 0)) 0 <= n_pre).
  { intros r Hr.
    pose proof (maxbitinsert_bound__dp_body_branches_k4 m0_2 retval_3 (retval + 1)
                  (-1000000000) n_pre nvals Hm0L ltac:(lia)
                  ltac:(intros q Hq; pose proof (PreH61 q Hq); lia) ltac:(lia) r Hr) as H0.
    pose proof (maxbitinsert_bound__dp_body_branches_k4 m1_2 retval_4 (retval_2 + 1)
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
         (MaxBitInsert m1_2 retval_4 (retval_2 + 1))
         (MaxBitInsert m0_2 retval_3 (retval + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (retval + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - do 12 cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed.
