From SimpleC.Verification Require Import VCPrelude.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P089_946G_almost_increasing_array_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P089_946G_almost_increasing_array_proof_auto.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P089_946G_almost_increasing_array_lib.
Local Open Scope sac.



Lemma proof_of_solver_entail_wit_12_56 : solver_entail_wit_12_56.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hlm0 : Zlength m0_2 = nvals + 1) by exact (proj1 PreH64).
  assert (Hlm1 : Zlength m1_2 = nvals + 1) by exact (proj1 PreH65).
  assert (HlmX : Zlength mX_2 = nvals + 1) by exact (proj1 PreH66).
  pose proof (dp_step_core__dp_body_branches_k5
                values vals_l_2 c_l_2 dp0_l_2 m0_2 m1_2 mX_2 nvals i
                retval retval_2 retval_6 retval_3 retval_4 retval_5
                (0 + 1) (0 + 1)
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
               Znth r (MaxBitInsert m1_2 retval_2 (0 + 1)) 0) /\
              Znth r (MaxBitInsert m1_2 retval_2 (0 + 1)) 0 <= n_pre) /\
             -1000000000 <=
             Znth r (MaxBitInsert mX_2 retval_6
                       (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)) 0) /\
            Znth r (MaxBitInsert mX_2 retval_6
                      (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)) 0
            <= n_pre).
  { intros r Hr. pose proof (PreH61 r Hr) as Hb.
    pose proof (maxbitinsert_bounds__dp_body_branches_k5 m0_2 retval (0 + 1) r
                  (-1000000000) n_pre ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as B0.
    pose proof (maxbitinsert_bounds__dp_body_branches_k5 m1_2 retval_2 (0 + 1) r
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
  { apply (clamped_best1_step__dp_body_branches_k5 values i best1 (0 + 1) best1
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
         (MaxBitInsert m1_2 retval_2 (0 + 1))
         (MaxBitInsert m0_2 retval (0 + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (0 + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed.

Lemma proof_of_solver_entail_wit_12_57 : solver_entail_wit_12_57.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hlm0 : Zlength m0_2 = nvals + 1) by exact (proj1 PreH64).
  assert (Hlm1 : Zlength m1_2 = nvals + 1) by exact (proj1 PreH65).
  assert (HlmX : Zlength mX_2 = nvals + 1) by exact (proj1 PreH66).
  pose proof (dp_step_core__dp_body_branches_k5
                values vals_l_2 c_l_2 dp0_l_2 m0_2 m1_2 mX_2 nvals i
                retval retval_2 retval_6 retval_3 retval_4 retval_5
                (retval_3 + 1) (retval_5 + 1)
                (replace_Znth i (retval_3 + 1) dp0_l_2)
                ltac:(lia) ltac:(lia) PreH53
                ltac:(rewrite <- PreH40; exact PreH50)
                PreH62 PreH64 PreH65 PreH66 PreH34 PreH31 PreH5
                ltac:(lia) ltac:(lia) ltac:(lia)
                PreH28 PreH23 PreH19 ltac:(lia) ltac:(lia) eq_refl) as Hcore.
  destruct Hcore as [Hbest0 [Hbest1 [Hd0b [Hd1b [Hnew [Hagree [Hlen'
                    [Hdp' [Hm0' [Hm1' HmX']]]]]]]]]].
  assert (HdXv : Znth (i - 1) (replace_Znth i (retval_3 + 1) dp0_l_2) 0
                 = Znth (i - 1) dp0_l_2 0) by (apply Hagree; lia).
  assert (HdXb : 1 <= Znth (i - 1) dp0_l_2 0 <= n_pre) by (apply PreH63; lia).
  assert (HdpB : forall k_4 : Z, 0 <= k_4 < i + 1 ->
            1 <= Znth k_4 (replace_Znth i (retval_3 + 1) dp0_l_2) 0 <= n_pre).
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
               Znth r (MaxBitInsert m0_2 retval (retval_3 + 1)) 0 <= n_pre /\
               -1000000000 <=
               Znth r (MaxBitInsert m1_2 retval_2 (retval_5 + 1)) 0) /\
              Znth r (MaxBitInsert m1_2 retval_2 (retval_5 + 1)) 0 <= n_pre) /\
             -1000000000 <=
             Znth r (MaxBitInsert mX_2 retval_6
                       (Znth (i - 1) (replace_Znth i (retval_3 + 1) dp0_l_2) 0)) 0) /\
            Znth r (MaxBitInsert mX_2 retval_6
                      (Znth (i - 1) (replace_Znth i (retval_3 + 1) dp0_l_2) 0)) 0
            <= n_pre).
  { intros r Hr. pose proof (PreH61 r Hr) as Hb.
    pose proof (maxbitinsert_bounds__dp_body_branches_k5 m0_2 retval (retval_3 + 1) r
                  (-1000000000) n_pre ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as B0.
    pose proof (maxbitinsert_bounds__dp_body_branches_k5 m1_2 retval_2 (retval_5 + 1) r
                  (-1000000000) n_pre ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as B1.
    pose proof (maxbitinsert_bounds__dp_body_branches_k5 mX_2 retval_6
                  (Znth (i - 1) (replace_Znth i (retval_3 + 1) dp0_l_2) 0) r
                  (-1000000000) n_pre ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as BX.
    lia. }
  assert (HmX2 : Bit0Model values vals_l_2 (replace_Znth i (retval_3 + 1) dp0_l_2)
                   (MaxBitInsert mX_2 retval_6
                      (Znth (i - 1) (replace_Znth i (retval_3 + 1) dp0_l_2) 0))
                   (i + 1 - 1) nvals).
  { replace (i + 1 - 1) with i by lia. exact HmX'. }
  assert (Hcp1 : ClampedPrefixMax (replace_Znth i (retval_3 + 1) dp0_l_2)
                   (i + 1) (best0)).
  { apply (clamped_step__dp_body_branches_k5 dp0_l_2
             (replace_Znth i (retval_3 + 1) dp0_l_2) i best0 (retval_3 + 1) (best0)
             PreH67 Hagree Hnew ltac:(lia) ltac:(lia)).
    right. split; [reflexivity | lia]. }
  assert (Hcb1 : ClampedBest1Upto values (i + 1) best1).
  { apply (clamped_best1_step__dp_body_branches_k5 values i best1 (retval_5 + 1) best1
             PreH68 Hbest1 ltac:(lia) ltac:(lia)).
    right. split; [reflexivity | lia]. }
  assert (Hcp2 : ClampedPrefixMax (replace_Znth i (retval_3 + 1) dp0_l_2)
                   (i + 1 - 1) best0_prefix).
  { replace (i + 1 - 1) with (i - 1 + 1) by lia.
    apply (clamped_step__dp_body_branches_k5 dp0_l_2
             (replace_Znth i (retval_3 + 1) dp0_l_2) (i - 1) best0_prefix
             (Znth (i - 1) (replace_Znth i (retval_3 + 1) dp0_l_2) 0) best0_prefix
             PreH69 ltac:(intros j Hj; apply Hagree; lia) eq_refl ltac:(lia) ltac:(lia)).
    right. split; [reflexivity | exact PreH1]. }
  assert (Hdpl : Zlength (replace_Znth i (retval_3 + 1) dp0_l_2) = n_pre) by lia.
  Exists (MaxBitInsert mX_2 retval_6
            (Znth (i - 1) (replace_Znth i (retval_3 + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_2 (retval_5 + 1))
         (MaxBitInsert m0_2 retval (retval_3 + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (retval_3 + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed.

Lemma proof_of_solver_entail_wit_12_58 : solver_entail_wit_12_58.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
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
                   (i + 1) (best0)).
  { apply (clamped_step__dp_body_branches_k5 dp0_l_2
             (replace_Znth i (0 + 1) dp0_l_2) i best0 (0 + 1) (best0)
             PreH67 Hagree Hnew ltac:(lia) ltac:(lia)).
    right. split; [reflexivity | lia]. }
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

Lemma proof_of_solver_entail_wit_12_59 : solver_entail_wit_12_59.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hlm0 : Zlength m0_2 = nvals + 1) by exact (proj1 PreH64).
  assert (Hlm1 : Zlength m1_2 = nvals + 1) by exact (proj1 PreH65).
  assert (HlmX : Zlength mX_2 = nvals + 1) by exact (proj1 PreH66).
  pose proof (dp_step_core__dp_body_branches_k5
                values vals_l_2 c_l_2 dp0_l_2 m0_2 m1_2 mX_2 nvals i
                retval retval_2 retval_6 retval_3 retval_4 retval_5
                (retval_3 + 1) (retval_5 + 1)
                (replace_Znth i (retval_3 + 1) dp0_l_2)
                ltac:(lia) ltac:(lia) PreH53
                ltac:(rewrite <- PreH40; exact PreH50)
                PreH62 PreH64 PreH65 PreH66 PreH34 PreH31 PreH5
                ltac:(lia) ltac:(lia) ltac:(lia)
                PreH28 PreH23 PreH19 ltac:(lia) ltac:(lia) eq_refl) as Hcore.
  destruct Hcore as [Hbest0 [Hbest1 [Hd0b [Hd1b [Hnew [Hagree [Hlen'
                    [Hdp' [Hm0' [Hm1' HmX']]]]]]]]]].
  assert (HdXv : Znth (i - 1) (replace_Znth i (retval_3 + 1) dp0_l_2) 0
                 = Znth (i - 1) dp0_l_2 0) by (apply Hagree; lia).
  assert (HdXb : 1 <= Znth (i - 1) dp0_l_2 0 <= n_pre) by (apply PreH63; lia).
  assert (HdpB : forall k_4 : Z, 0 <= k_4 < i + 1 ->
            1 <= Znth k_4 (replace_Znth i (retval_3 + 1) dp0_l_2) 0 <= n_pre).
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
               Znth r (MaxBitInsert m0_2 retval (retval_3 + 1)) 0 <= n_pre /\
               -1000000000 <=
               Znth r (MaxBitInsert m1_2 retval_2 (retval_5 + 1)) 0) /\
              Znth r (MaxBitInsert m1_2 retval_2 (retval_5 + 1)) 0 <= n_pre) /\
             -1000000000 <=
             Znth r (MaxBitInsert mX_2 retval_6
                       (Znth (i - 1) (replace_Znth i (retval_3 + 1) dp0_l_2) 0)) 0) /\
            Znth r (MaxBitInsert mX_2 retval_6
                      (Znth (i - 1) (replace_Znth i (retval_3 + 1) dp0_l_2) 0)) 0
            <= n_pre).
  { intros r Hr. pose proof (PreH61 r Hr) as Hb.
    pose proof (maxbitinsert_bounds__dp_body_branches_k5 m0_2 retval (retval_3 + 1) r
                  (-1000000000) n_pre ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as B0.
    pose proof (maxbitinsert_bounds__dp_body_branches_k5 m1_2 retval_2 (retval_5 + 1) r
                  (-1000000000) n_pre ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as B1.
    pose proof (maxbitinsert_bounds__dp_body_branches_k5 mX_2 retval_6
                  (Znth (i - 1) (replace_Znth i (retval_3 + 1) dp0_l_2) 0) r
                  (-1000000000) n_pre ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as BX.
    lia. }
  assert (HmX2 : Bit0Model values vals_l_2 (replace_Znth i (retval_3 + 1) dp0_l_2)
                   (MaxBitInsert mX_2 retval_6
                      (Znth (i - 1) (replace_Znth i (retval_3 + 1) dp0_l_2) 0))
                   (i + 1 - 1) nvals).
  { replace (i + 1 - 1) with i by lia. exact HmX'. }
  assert (Hcp1 : ClampedPrefixMax (replace_Znth i (retval_3 + 1) dp0_l_2)
                   (i + 1) (best0)).
  { apply (clamped_step__dp_body_branches_k5 dp0_l_2
             (replace_Znth i (retval_3 + 1) dp0_l_2) i best0 (retval_3 + 1) (best0)
             PreH67 Hagree Hnew ltac:(lia) ltac:(lia)).
    right. split; [reflexivity | lia]. }
  assert (Hcb1 : ClampedBest1Upto values (i + 1) best1).
  { apply (clamped_best1_step__dp_body_branches_k5 values i best1 (retval_5 + 1) best1
             PreH68 Hbest1 ltac:(lia) ltac:(lia)).
    right. split; [reflexivity | lia]. }
  assert (Hcp2 : ClampedPrefixMax (replace_Znth i (retval_3 + 1) dp0_l_2)
                   (i + 1 - 1) best0_prefix).
  { replace (i + 1 - 1) with (i - 1 + 1) by lia.
    apply (clamped_step__dp_body_branches_k5 dp0_l_2
             (replace_Znth i (retval_3 + 1) dp0_l_2) (i - 1) best0_prefix
             (Znth (i - 1) (replace_Znth i (retval_3 + 1) dp0_l_2) 0) best0_prefix
             PreH69 ltac:(intros j Hj; apply Hagree; lia) eq_refl ltac:(lia) ltac:(lia)).
    right. split; [reflexivity | exact PreH1]. }
  assert (Hdpl : Zlength (replace_Znth i (retval_3 + 1) dp0_l_2) = n_pre) by lia.
  Exists (MaxBitInsert mX_2 retval_6
            (Znth (i - 1) (replace_Znth i (retval_3 + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_2 (retval_5 + 1))
         (MaxBitInsert m0_2 retval (retval_3 + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (retval_3 + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  - repeat cancel.
  - split_pures; dump_pre_spatial; first [assumption | lia].
Qed.

Lemma proof_of_solver_entail_wit_12_60 : solver_entail_wit_12_60.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
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
                   (i + 1) (best0)).
  { apply (clamped_step__dp_body_branches_k5 dp0_l_2
             (replace_Znth i (0 + 1) dp0_l_2) i best0 (0 + 1) (best0)
             PreH67 Hagree Hnew ltac:(lia) ltac:(lia)).
    right. split; [reflexivity | lia]. }
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

Lemma proof_of_solver_entail_wit_12_61 : solver_entail_wit_12_61.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hn : n_pre = Zlength values) by exact PreH40.
  assert (HkeyC : Znth i c_l_2 0 = KeyAt values i) by (apply PreH50; lia).
  assert (HkeyC1 : Znth (i - 1) c_l_2 0 = KeyAt values (i - 1)) by (apply PreH50; lia).
  rewrite HkeyC in PreH34, PreH31.
  rewrite HkeyC1 in PreH5.
  assert (Hlm0 : Zlength m0_2 = nvals + 1) by (apply (proj1 PreH64)).
  assert (Hlm1 : Zlength m1_2 = nvals + 1) by (apply (proj1 PreH65)).
  assert (HlmX : Zlength mX_2 = nvals + 1) by (apply (proj1 PreH66)).
  assert (Hdplen : Zlength (replace_Znth i (retval_3 + 1) dp0_l_2) = n_pre)
    by (rewrite Zlength_replace_Znth__dp_body_branches_k6; exact PreH49).
  assert (Hnew_i : Znth i (replace_Znth i (retval_3 + 1) dp0_l_2) 0 = retval_3 + 1)
    by (apply Znth_replace_Znth_Same; lia).
  assert (Hnew_j : forall j, 0 <= j < i ->
            Znth j (replace_Znth i (retval_3 + 1) dp0_l_2) 0 = Znth j dp0_l_2 0)
    by (intros j Hj; apply Znth_replace_Znth_Diff; lia).
  assert (HB0 : Best0EndingAt values i (retval_3 + 1)).
  { pose proof (best0_step__dp_body_branches_k6 values vals_l_2 dp0_l_2 m0_2 i nvals retval
                  ltac:(lia) PreH53 PreH62 PreH64 PreH34) as HB.
    replace (Z.max (RangeMax m0_2 1 (retval + 1)) 0 + 1) with (retval_3 + 1) in HB by lia.
    exact HB. }
  assert (HB1 : Best1EndingAt values i (retval_4 + 1)).
  { pose proof (best1_step__dp_body_branches_k6 values vals_l_2 dp0_l_2 m1_2 mX_2 i nvals
                  retval_2 ltac:(lia) PreH53 PreH62 PreH65 PreH66 PreH31) as HB.
    replace (Z.max (Z.max (RangeMax m1_2 1 (retval_2 + 1))
                          (RangeMax mX_2 1 (retval_2 + 1))) 0 + 1)
      with (retval_4 + 1) in HB by lia.
    exact HB. }
  assert (Hd0b : 1 <= retval_3 + 1 <= n_pre).
  { pose proof (best0_bounds__dp_body_branches_k6 values i (retval_3 + 1) HB0 ltac:(lia)). lia. }
  assert (Hd1b : 1 <= retval_4 + 1 <= n_pre).
  { pose proof (best1_bounds__dp_body_branches_k6 values i (retval_4 + 1) HB1). lia. }
  assert (HdpXb : 1 <= Znth (i - 1) (replace_Znth i (retval_3 + 1) dp0_l_2) 0 <= n_pre).
  { rewrite Hnew_j by lia. apply PreH63; lia. }
  assert (HDPnew : DP0Prefix values (replace_Znth i (retval_3 + 1) dp0_l_2) (i + 1)).
  { intros j Hj. destruct (Z.eq_dec j i) as [He | Hne].
    - subst j. rewrite Hnew_i. exact HB0.
    - rewrite Hnew_j by lia. apply PreH62; lia. }
  assert (Hdpb : forall k_4 : Z, 0 <= k_4 < i + 1 ->
            1 <= Znth k_4 (replace_Znth i (retval_3 + 1) dp0_l_2) 0 <= n_pre).
  { intros k4 Hk4. destruct (Z.eq_dec k4 i) as [He | Hne].
    - subst k4. rewrite Hnew_i. lia.
    - rewrite Hnew_j by lia. apply PreH63; lia. }
  assert (HBit0 : Bit0Model values vals_l_2 (replace_Znth i (retval_3 + 1) dp0_l_2)
                    (MaxBitInsert m0_2 retval (retval_3 + 1)) (i + 1) nvals).
  { apply (bit0_model_insert__dp_body_branches_k6 values vals_l_2 dp0_l_2
             (replace_Znth i (retval_3 + 1) dp0_l_2) m0_2 i nvals retval (retval_3 + 1));
      [lia | apply (proj1 PreH53) | exact PreH64 | exact Hnew_j | exact Hnew_i | exact PreH34]. }
  assert (HBit1 : Bit1Model values vals_l_2
                    (MaxBitInsert m1_2 retval_2 (retval_4 + 1)) (i + 1) nvals).
  { apply (bit1_model_insert__dp_body_branches_k6 values vals_l_2 m1_2 i nvals retval_2
             (retval_4 + 1));
      [lia | apply (proj1 PreH53) | exact PreH65 | exact HB1 | exact PreH31]. }
  assert (HBitX : Bit0Model values vals_l_2 (replace_Znth i (retval_3 + 1) dp0_l_2)
                    (MaxBitInsert mX_2 retval_6
                       (Znth (i - 1) (replace_Znth i (retval_3 + 1) dp0_l_2) 0))
                    (i + 1 - 1) nvals).
  { replace (i + 1 - 1) with ((i - 1) + 1) by lia.
    apply (bit0_model_insert__dp_body_branches_k6 values vals_l_2 dp0_l_2
             (replace_Znth i (retval_3 + 1) dp0_l_2) mX_2 (i - 1) nvals retval_6
             (Znth (i - 1) (replace_Znth i (retval_3 + 1) dp0_l_2) 0));
      [lia | apply (proj1 PreH53) | exact PreH66 | | reflexivity | exact PreH5].
    intros j Hj. apply Hnew_j; lia. }
  assert (HCP : ClampedPrefixMax (replace_Znth i (retval_3 + 1) dp0_l_2) (i + 1) best0).
  { apply (clamped_prefix_step_keep__dp_body_branches_k6
             (replace_Znth i (retval_3 + 1) dp0_l_2) i best0 (retval_3 + 1));
      [ | lia | exact Hnew_i | lia].
    apply (clamped_prefix_ext__dp_body_branches_k6 dp0_l_2); [exact PreH67 | exact Hnew_j]. }
  assert (HCB1 : ClampedBest1Upto values (i + 1) best1).
  { apply (clamped_best1_step_keep__dp_body_branches_k6 values i best1 (retval_4 + 1));
      [exact PreH68 | lia | exact HB1 | lia]. }
  assert (HCP0 : ClampedPrefixMax (replace_Znth i (retval_3 + 1) dp0_l_2)
                   (i + 1 - 1) best0_prefix).
  { replace (i + 1 - 1) with ((i - 1) + 1) by lia.
    apply (clamped_prefix_step_keep__dp_body_branches_k6
             (replace_Znth i (retval_3 + 1) dp0_l_2) (i - 1) best0_prefix
             (Znth (i - 1) (replace_Znth i (retval_3 + 1) dp0_l_2) 0));
      [ | lia | reflexivity | exact PreH1].
    apply (clamped_prefix_ext__dp_body_branches_k6 dp0_l_2); [exact PreH69 |].
    intros j Hj. apply Hnew_j; lia. }
  assert (Hmb : forall r : Z, 0 <= r <= nvals ->
    (((-1000000000 <= Znth r (MaxBitInsert m0_2 retval (retval_3 + 1)) 0 <= n_pre /\
       -1000000000 <= Znth r (MaxBitInsert m1_2 retval_2 (retval_4 + 1)) 0) /\
      Znth r (MaxBitInsert m1_2 retval_2 (retval_4 + 1)) 0 <= n_pre) /\
     -1000000000 <= Znth r (MaxBitInsert mX_2 retval_6
        (Znth (i - 1) (replace_Znth i (retval_3 + 1) dp0_l_2) 0)) 0) /\
     Znth r (MaxBitInsert mX_2 retval_6
        (Znth (i - 1) (replace_Znth i (retval_3 + 1) dp0_l_2) 0)) 0 <= n_pre).
  { intros r Hr.
    assert (Hb0 : -1000000000 <=
                  Znth r (MaxBitInsert m0_2 retval (retval_3 + 1)) 0 <= n_pre).
    { apply (Znth_maxbitinsert_bound__dp_body_branches_k6 m0_2 retval (retval_3 + 1) r
               (-1000000000) n_pre); [lia | lia | | lia | lia].
      intros t Ht. pose proof (PreH61 t ltac:(lia)). lia. }
    assert (Hb1 : -1000000000 <=
                  Znth r (MaxBitInsert m1_2 retval_2 (retval_4 + 1)) 0 <= n_pre).
    { apply (Znth_maxbitinsert_bound__dp_body_branches_k6 m1_2 retval_2 (retval_4 + 1) r
               (-1000000000) n_pre); [lia | lia | | lia | lia].
      intros t Ht. pose proof (PreH61 t ltac:(lia)). lia. }
    assert (HbX : -1000000000 <= Znth r (MaxBitInsert mX_2 retval_6
        (Znth (i - 1) (replace_Znth i (retval_3 + 1) dp0_l_2) 0)) 0 <= n_pre).
    { apply (Znth_maxbitinsert_bound__dp_body_branches_k6 mX_2 retval_6
               (Znth (i - 1) (replace_Znth i (retval_3 + 1) dp0_l_2) 0) r
               (-1000000000) n_pre); [lia | lia | | lia | lia].
      intros t Ht. pose proof (PreH61 t ltac:(lia)). lia. }
    lia. }
  assert (Hbb : forall k_3 : Z, 0 <= k_3 < nvals + 1 ->
    (((-1000000000 <= Znth k_3 bit_l1 0 <= 1000000000 /\
       -1000000000 <= Znth k_3 bit_l1_2 0) /\ Znth k_3 bit_l1_2 0 <= 1000000000) /\
     -1000000000 <= Znth k_3 bit_l1_3 0) /\ Znth k_3 bit_l1_3 0 <= 1000000000).
  { intros k3 Hk3. pose proof (PreH14 k3 Hk3). pose proof (PreH10 k3 Hk3).
    pose proof (PreH3 k3 Hk3). lia. }
  Exists (MaxBitInsert mX_2 retval_6
            (Znth (i - 1) (replace_Znth i (retval_3 + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_2 (retval_4 + 1))
         (MaxBitInsert m0_2 retval (retval_3 + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (retval_3 + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  { repeat sepcon_cancel. }
  split_pures; dump_pre_spatial.
  all: first [assumption | lia].
Qed.

Lemma proof_of_solver_entail_wit_12_62 : solver_entail_wit_12_62.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hn : n_pre = Zlength values) by exact PreH40.
  assert (HkeyC : Znth i c_l_2 0 = KeyAt values i) by (apply PreH50; lia).
  assert (HkeyC1 : Znth (i - 1) c_l_2 0 = KeyAt values (i - 1)) by (apply PreH50; lia).
  rewrite HkeyC in PreH34, PreH31.
  rewrite HkeyC1 in PreH5.
  assert (Hlm0 : Zlength m0_2 = nvals + 1) by (apply (proj1 PreH64)).
  assert (Hlm1 : Zlength m1_2 = nvals + 1) by (apply (proj1 PreH65)).
  assert (HlmX : Zlength mX_2 = nvals + 1) by (apply (proj1 PreH66)).
  assert (Hdplen : Zlength (replace_Znth i (0 + 1) dp0_l_2) = n_pre)
    by (rewrite Zlength_replace_Znth__dp_body_branches_k6; exact PreH49).
  assert (Hnew_i : Znth i (replace_Znth i (0 + 1) dp0_l_2) 0 = 0 + 1)
    by (apply Znth_replace_Znth_Same; lia).
  assert (Hnew_j : forall j, 0 <= j < i ->
            Znth j (replace_Znth i (0 + 1) dp0_l_2) 0 = Znth j dp0_l_2 0)
    by (intros j Hj; apply Znth_replace_Znth_Diff; lia).
  assert (HB0 : Best0EndingAt values i (0 + 1)).
  { pose proof (best0_step__dp_body_branches_k6 values vals_l_2 dp0_l_2 m0_2 i nvals retval
                  ltac:(lia) PreH53 PreH62 PreH64 PreH34) as HB.
    replace (Z.max (RangeMax m0_2 1 (retval + 1)) 0 + 1) with (0 + 1) in HB by lia.
    exact HB. }
  assert (HB1 : Best1EndingAt values i (retval_4 + 1)).
  { pose proof (best1_step__dp_body_branches_k6 values vals_l_2 dp0_l_2 m1_2 mX_2 i nvals
                  retval_2 ltac:(lia) PreH53 PreH62 PreH65 PreH66 PreH31) as HB.
    replace (Z.max (Z.max (RangeMax m1_2 1 (retval_2 + 1))
                          (RangeMax mX_2 1 (retval_2 + 1))) 0 + 1)
      with (retval_4 + 1) in HB by lia.
    exact HB. }
  assert (Hd0b : 1 <= 0 + 1 <= n_pre).
  { pose proof (best0_bounds__dp_body_branches_k6 values i (0 + 1) HB0 ltac:(lia)). lia. }
  assert (Hd1b : 1 <= retval_4 + 1 <= n_pre).
  { pose proof (best1_bounds__dp_body_branches_k6 values i (retval_4 + 1) HB1). lia. }
  assert (HdpXb : 1 <= Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0 <= n_pre).
  { rewrite Hnew_j by lia. apply PreH63; lia. }
  assert (HDPnew : DP0Prefix values (replace_Znth i (0 + 1) dp0_l_2) (i + 1)).
  { intros j Hj. destruct (Z.eq_dec j i) as [He | Hne].
    - subst j. rewrite Hnew_i. exact HB0.
    - rewrite Hnew_j by lia. apply PreH62; lia. }
  assert (Hdpb : forall k_4 : Z, 0 <= k_4 < i + 1 ->
            1 <= Znth k_4 (replace_Znth i (0 + 1) dp0_l_2) 0 <= n_pre).
  { intros k4 Hk4. destruct (Z.eq_dec k4 i) as [He | Hne].
    - subst k4. rewrite Hnew_i. lia.
    - rewrite Hnew_j by lia. apply PreH63; lia. }
  assert (HBit0 : Bit0Model values vals_l_2 (replace_Znth i (0 + 1) dp0_l_2)
                    (MaxBitInsert m0_2 retval (0 + 1)) (i + 1) nvals).
  { apply (bit0_model_insert__dp_body_branches_k6 values vals_l_2 dp0_l_2
             (replace_Znth i (0 + 1) dp0_l_2) m0_2 i nvals retval (0 + 1));
      [lia | apply (proj1 PreH53) | exact PreH64 | exact Hnew_j | exact Hnew_i | exact PreH34]. }
  assert (HBit1 : Bit1Model values vals_l_2
                    (MaxBitInsert m1_2 retval_2 (retval_4 + 1)) (i + 1) nvals).
  { apply (bit1_model_insert__dp_body_branches_k6 values vals_l_2 m1_2 i nvals retval_2
             (retval_4 + 1));
      [lia | apply (proj1 PreH53) | exact PreH65 | exact HB1 | exact PreH31]. }
  assert (HBitX : Bit0Model values vals_l_2 (replace_Znth i (0 + 1) dp0_l_2)
                    (MaxBitInsert mX_2 retval_6
                       (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0))
                    (i + 1 - 1) nvals).
  { replace (i + 1 - 1) with ((i - 1) + 1) by lia.
    apply (bit0_model_insert__dp_body_branches_k6 values vals_l_2 dp0_l_2
             (replace_Znth i (0 + 1) dp0_l_2) mX_2 (i - 1) nvals retval_6
             (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0));
      [lia | apply (proj1 PreH53) | exact PreH66 | | reflexivity | exact PreH5].
    intros j Hj. apply Hnew_j; lia. }
  assert (HCP : ClampedPrefixMax (replace_Znth i (0 + 1) dp0_l_2) (i + 1) best0).
  { apply (clamped_prefix_step_keep__dp_body_branches_k6
             (replace_Znth i (0 + 1) dp0_l_2) i best0 (0 + 1));
      [ | lia | exact Hnew_i | lia].
    apply (clamped_prefix_ext__dp_body_branches_k6 dp0_l_2); [exact PreH67 | exact Hnew_j]. }
  assert (HCB1 : ClampedBest1Upto values (i + 1) best1).
  { apply (clamped_best1_step_keep__dp_body_branches_k6 values i best1 (retval_4 + 1));
      [exact PreH68 | lia | exact HB1 | lia]. }
  assert (HCP0 : ClampedPrefixMax (replace_Znth i (0 + 1) dp0_l_2)
                   (i + 1 - 1) best0_prefix).
  { replace (i + 1 - 1) with ((i - 1) + 1) by lia.
    apply (clamped_prefix_step_keep__dp_body_branches_k6
             (replace_Znth i (0 + 1) dp0_l_2) (i - 1) best0_prefix
             (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0));
      [ | lia | reflexivity | exact PreH1].
    apply (clamped_prefix_ext__dp_body_branches_k6 dp0_l_2); [exact PreH69 |].
    intros j Hj. apply Hnew_j; lia. }
  assert (Hmb : forall r : Z, 0 <= r <= nvals ->
    (((-1000000000 <= Znth r (MaxBitInsert m0_2 retval (0 + 1)) 0 <= n_pre /\
       -1000000000 <= Znth r (MaxBitInsert m1_2 retval_2 (retval_4 + 1)) 0) /\
      Znth r (MaxBitInsert m1_2 retval_2 (retval_4 + 1)) 0 <= n_pre) /\
     -1000000000 <= Znth r (MaxBitInsert mX_2 retval_6
        (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)) 0) /\
     Znth r (MaxBitInsert mX_2 retval_6
        (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)) 0 <= n_pre).
  { intros r Hr.
    assert (Hb0 : -1000000000 <=
                  Znth r (MaxBitInsert m0_2 retval (0 + 1)) 0 <= n_pre).
    { apply (Znth_maxbitinsert_bound__dp_body_branches_k6 m0_2 retval (0 + 1) r
               (-1000000000) n_pre); [lia | lia | | lia | lia].
      intros t Ht. pose proof (PreH61 t ltac:(lia)). lia. }
    assert (Hb1 : -1000000000 <=
                  Znth r (MaxBitInsert m1_2 retval_2 (retval_4 + 1)) 0 <= n_pre).
    { apply (Znth_maxbitinsert_bound__dp_body_branches_k6 m1_2 retval_2 (retval_4 + 1) r
               (-1000000000) n_pre); [lia | lia | | lia | lia].
      intros t Ht. pose proof (PreH61 t ltac:(lia)). lia. }
    assert (HbX : -1000000000 <= Znth r (MaxBitInsert mX_2 retval_6
        (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)) 0 <= n_pre).
    { apply (Znth_maxbitinsert_bound__dp_body_branches_k6 mX_2 retval_6
               (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0) r
               (-1000000000) n_pre); [lia | lia | | lia | lia].
      intros t Ht. pose proof (PreH61 t ltac:(lia)). lia. }
    lia. }
  assert (Hbb : forall k_3 : Z, 0 <= k_3 < nvals + 1 ->
    (((-1000000000 <= Znth k_3 bit_l1 0 <= 1000000000 /\
       -1000000000 <= Znth k_3 bit_l1_2 0) /\ Znth k_3 bit_l1_2 0 <= 1000000000) /\
     -1000000000 <= Znth k_3 bit_l1_3 0) /\ Znth k_3 bit_l1_3 0 <= 1000000000).
  { intros k3 Hk3. pose proof (PreH14 k3 Hk3). pose proof (PreH10 k3 Hk3).
    pose proof (PreH3 k3 Hk3). lia. }
  Exists (MaxBitInsert mX_2 retval_6
            (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_2 (retval_4 + 1))
         (MaxBitInsert m0_2 retval (0 + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (0 + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  { repeat sepcon_cancel. }
  split_pures; dump_pre_spatial.
  all: first [assumption | lia].
Qed.

Lemma proof_of_solver_entail_wit_12_63 : solver_entail_wit_12_63.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hn : n_pre = Zlength values) by exact PreH40.
  assert (HkeyC : Znth i c_l_2 0 = KeyAt values i) by (apply PreH50; lia).
  assert (HkeyC1 : Znth (i - 1) c_l_2 0 = KeyAt values (i - 1)) by (apply PreH50; lia).
  rewrite HkeyC in PreH34, PreH31.
  rewrite HkeyC1 in PreH5.
  assert (Hlm0 : Zlength m0_2 = nvals + 1) by (apply (proj1 PreH64)).
  assert (Hlm1 : Zlength m1_2 = nvals + 1) by (apply (proj1 PreH65)).
  assert (HlmX : Zlength mX_2 = nvals + 1) by (apply (proj1 PreH66)).
  assert (Hdplen : Zlength (replace_Znth i (retval_3 + 1) dp0_l_2) = n_pre)
    by (rewrite Zlength_replace_Znth__dp_body_branches_k6; exact PreH49).
  assert (Hnew_i : Znth i (replace_Znth i (retval_3 + 1) dp0_l_2) 0 = retval_3 + 1)
    by (apply Znth_replace_Znth_Same; lia).
  assert (Hnew_j : forall j, 0 <= j < i ->
            Znth j (replace_Znth i (retval_3 + 1) dp0_l_2) 0 = Znth j dp0_l_2 0)
    by (intros j Hj; apply Znth_replace_Znth_Diff; lia).
  assert (HB0 : Best0EndingAt values i (retval_3 + 1)).
  { pose proof (best0_step__dp_body_branches_k6 values vals_l_2 dp0_l_2 m0_2 i nvals retval
                  ltac:(lia) PreH53 PreH62 PreH64 PreH34) as HB.
    replace (Z.max (RangeMax m0_2 1 (retval + 1)) 0 + 1) with (retval_3 + 1) in HB by lia.
    exact HB. }
  assert (HB1 : Best1EndingAt values i (0 + 1)).
  { pose proof (best1_step__dp_body_branches_k6 values vals_l_2 dp0_l_2 m1_2 mX_2 i nvals
                  retval_2 ltac:(lia) PreH53 PreH62 PreH65 PreH66 PreH31) as HB.
    replace (Z.max (Z.max (RangeMax m1_2 1 (retval_2 + 1))
                          (RangeMax mX_2 1 (retval_2 + 1))) 0 + 1)
      with (0 + 1) in HB by lia.
    exact HB. }
  assert (Hd0b : 1 <= retval_3 + 1 <= n_pre).
  { pose proof (best0_bounds__dp_body_branches_k6 values i (retval_3 + 1) HB0 ltac:(lia)). lia. }
  assert (Hd1b : 1 <= 0 + 1 <= n_pre).
  { pose proof (best1_bounds__dp_body_branches_k6 values i (0 + 1) HB1). lia. }
  assert (HdpXb : 1 <= Znth (i - 1) (replace_Znth i (retval_3 + 1) dp0_l_2) 0 <= n_pre).
  { rewrite Hnew_j by lia. apply PreH63; lia. }
  assert (HDPnew : DP0Prefix values (replace_Znth i (retval_3 + 1) dp0_l_2) (i + 1)).
  { intros j Hj. destruct (Z.eq_dec j i) as [He | Hne].
    - subst j. rewrite Hnew_i. exact HB0.
    - rewrite Hnew_j by lia. apply PreH62; lia. }
  assert (Hdpb : forall k_4 : Z, 0 <= k_4 < i + 1 ->
            1 <= Znth k_4 (replace_Znth i (retval_3 + 1) dp0_l_2) 0 <= n_pre).
  { intros k4 Hk4. destruct (Z.eq_dec k4 i) as [He | Hne].
    - subst k4. rewrite Hnew_i. lia.
    - rewrite Hnew_j by lia. apply PreH63; lia. }
  assert (HBit0 : Bit0Model values vals_l_2 (replace_Znth i (retval_3 + 1) dp0_l_2)
                    (MaxBitInsert m0_2 retval (retval_3 + 1)) (i + 1) nvals).
  { apply (bit0_model_insert__dp_body_branches_k6 values vals_l_2 dp0_l_2
             (replace_Znth i (retval_3 + 1) dp0_l_2) m0_2 i nvals retval (retval_3 + 1));
      [lia | apply (proj1 PreH53) | exact PreH64 | exact Hnew_j | exact Hnew_i | exact PreH34]. }
  assert (HBit1 : Bit1Model values vals_l_2
                    (MaxBitInsert m1_2 retval_2 (0 + 1)) (i + 1) nvals).
  { apply (bit1_model_insert__dp_body_branches_k6 values vals_l_2 m1_2 i nvals retval_2
             (0 + 1));
      [lia | apply (proj1 PreH53) | exact PreH65 | exact HB1 | exact PreH31]. }
  assert (HBitX : Bit0Model values vals_l_2 (replace_Znth i (retval_3 + 1) dp0_l_2)
                    (MaxBitInsert mX_2 retval_6
                       (Znth (i - 1) (replace_Znth i (retval_3 + 1) dp0_l_2) 0))
                    (i + 1 - 1) nvals).
  { replace (i + 1 - 1) with ((i - 1) + 1) by lia.
    apply (bit0_model_insert__dp_body_branches_k6 values vals_l_2 dp0_l_2
             (replace_Znth i (retval_3 + 1) dp0_l_2) mX_2 (i - 1) nvals retval_6
             (Znth (i - 1) (replace_Znth i (retval_3 + 1) dp0_l_2) 0));
      [lia | apply (proj1 PreH53) | exact PreH66 | | reflexivity | exact PreH5].
    intros j Hj. apply Hnew_j; lia. }
  assert (HCP : ClampedPrefixMax (replace_Znth i (retval_3 + 1) dp0_l_2) (i + 1) best0).
  { apply (clamped_prefix_step_keep__dp_body_branches_k6
             (replace_Znth i (retval_3 + 1) dp0_l_2) i best0 (retval_3 + 1));
      [ | lia | exact Hnew_i | lia].
    apply (clamped_prefix_ext__dp_body_branches_k6 dp0_l_2); [exact PreH67 | exact Hnew_j]. }
  assert (HCB1 : ClampedBest1Upto values (i + 1) best1).
  { apply (clamped_best1_step_keep__dp_body_branches_k6 values i best1 (0 + 1));
      [exact PreH68 | lia | exact HB1 | lia]. }
  assert (HCP0 : ClampedPrefixMax (replace_Znth i (retval_3 + 1) dp0_l_2)
                   (i + 1 - 1) best0_prefix).
  { replace (i + 1 - 1) with ((i - 1) + 1) by lia.
    apply (clamped_prefix_step_keep__dp_body_branches_k6
             (replace_Znth i (retval_3 + 1) dp0_l_2) (i - 1) best0_prefix
             (Znth (i - 1) (replace_Znth i (retval_3 + 1) dp0_l_2) 0));
      [ | lia | reflexivity | exact PreH1].
    apply (clamped_prefix_ext__dp_body_branches_k6 dp0_l_2); [exact PreH69 |].
    intros j Hj. apply Hnew_j; lia. }
  assert (Hmb : forall r : Z, 0 <= r <= nvals ->
    (((-1000000000 <= Znth r (MaxBitInsert m0_2 retval (retval_3 + 1)) 0 <= n_pre /\
       -1000000000 <= Znth r (MaxBitInsert m1_2 retval_2 (0 + 1)) 0) /\
      Znth r (MaxBitInsert m1_2 retval_2 (0 + 1)) 0 <= n_pre) /\
     -1000000000 <= Znth r (MaxBitInsert mX_2 retval_6
        (Znth (i - 1) (replace_Znth i (retval_3 + 1) dp0_l_2) 0)) 0) /\
     Znth r (MaxBitInsert mX_2 retval_6
        (Znth (i - 1) (replace_Znth i (retval_3 + 1) dp0_l_2) 0)) 0 <= n_pre).
  { intros r Hr.
    assert (Hb0 : -1000000000 <=
                  Znth r (MaxBitInsert m0_2 retval (retval_3 + 1)) 0 <= n_pre).
    { apply (Znth_maxbitinsert_bound__dp_body_branches_k6 m0_2 retval (retval_3 + 1) r
               (-1000000000) n_pre); [lia | lia | | lia | lia].
      intros t Ht. pose proof (PreH61 t ltac:(lia)). lia. }
    assert (Hb1 : -1000000000 <=
                  Znth r (MaxBitInsert m1_2 retval_2 (0 + 1)) 0 <= n_pre).
    { apply (Znth_maxbitinsert_bound__dp_body_branches_k6 m1_2 retval_2 (0 + 1) r
               (-1000000000) n_pre); [lia | lia | | lia | lia].
      intros t Ht. pose proof (PreH61 t ltac:(lia)). lia. }
    assert (HbX : -1000000000 <= Znth r (MaxBitInsert mX_2 retval_6
        (Znth (i - 1) (replace_Znth i (retval_3 + 1) dp0_l_2) 0)) 0 <= n_pre).
    { apply (Znth_maxbitinsert_bound__dp_body_branches_k6 mX_2 retval_6
               (Znth (i - 1) (replace_Znth i (retval_3 + 1) dp0_l_2) 0) r
               (-1000000000) n_pre); [lia | lia | | lia | lia].
      intros t Ht. pose proof (PreH61 t ltac:(lia)). lia. }
    lia. }
  assert (Hbb : forall k_3 : Z, 0 <= k_3 < nvals + 1 ->
    (((-1000000000 <= Znth k_3 bit_l1 0 <= 1000000000 /\
       -1000000000 <= Znth k_3 bit_l1_2 0) /\ Znth k_3 bit_l1_2 0 <= 1000000000) /\
     -1000000000 <= Znth k_3 bit_l1_3 0) /\ Znth k_3 bit_l1_3 0 <= 1000000000).
  { intros k3 Hk3. pose proof (PreH14 k3 Hk3). pose proof (PreH10 k3 Hk3).
    pose proof (PreH3 k3 Hk3). lia. }
  Exists (MaxBitInsert mX_2 retval_6
            (Znth (i - 1) (replace_Znth i (retval_3 + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_2 (0 + 1))
         (MaxBitInsert m0_2 retval (retval_3 + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (retval_3 + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  { repeat sepcon_cancel. }
  split_pures; dump_pre_spatial.
  all: first [assumption | lia].
Qed.

Lemma proof_of_solver_entail_wit_12_64 : solver_entail_wit_12_64.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hn : n_pre = Zlength values) by exact PreH40.
  assert (HkeyC : Znth i c_l_2 0 = KeyAt values i) by (apply PreH50; lia).
  assert (HkeyC1 : Znth (i - 1) c_l_2 0 = KeyAt values (i - 1)) by (apply PreH50; lia).
  rewrite HkeyC in PreH34, PreH31.
  rewrite HkeyC1 in PreH5.
  assert (Hlm0 : Zlength m0_2 = nvals + 1) by (apply (proj1 PreH64)).
  assert (Hlm1 : Zlength m1_2 = nvals + 1) by (apply (proj1 PreH65)).
  assert (HlmX : Zlength mX_2 = nvals + 1) by (apply (proj1 PreH66)).
  assert (Hdplen : Zlength (replace_Znth i (0 + 1) dp0_l_2) = n_pre)
    by (rewrite Zlength_replace_Znth__dp_body_branches_k6; exact PreH49).
  assert (Hnew_i : Znth i (replace_Znth i (0 + 1) dp0_l_2) 0 = 0 + 1)
    by (apply Znth_replace_Znth_Same; lia).
  assert (Hnew_j : forall j, 0 <= j < i ->
            Znth j (replace_Znth i (0 + 1) dp0_l_2) 0 = Znth j dp0_l_2 0)
    by (intros j Hj; apply Znth_replace_Znth_Diff; lia).
  assert (HB0 : Best0EndingAt values i (0 + 1)).
  { pose proof (best0_step__dp_body_branches_k6 values vals_l_2 dp0_l_2 m0_2 i nvals retval
                  ltac:(lia) PreH53 PreH62 PreH64 PreH34) as HB.
    replace (Z.max (RangeMax m0_2 1 (retval + 1)) 0 + 1) with (0 + 1) in HB by lia.
    exact HB. }
  assert (HB1 : Best1EndingAt values i (0 + 1)).
  { pose proof (best1_step__dp_body_branches_k6 values vals_l_2 dp0_l_2 m1_2 mX_2 i nvals
                  retval_2 ltac:(lia) PreH53 PreH62 PreH65 PreH66 PreH31) as HB.
    replace (Z.max (Z.max (RangeMax m1_2 1 (retval_2 + 1))
                          (RangeMax mX_2 1 (retval_2 + 1))) 0 + 1)
      with (0 + 1) in HB by lia.
    exact HB. }
  assert (Hd0b : 1 <= 0 + 1 <= n_pre).
  { pose proof (best0_bounds__dp_body_branches_k6 values i (0 + 1) HB0 ltac:(lia)). lia. }
  assert (Hd1b : 1 <= 0 + 1 <= n_pre).
  { pose proof (best1_bounds__dp_body_branches_k6 values i (0 + 1) HB1). lia. }
  assert (HdpXb : 1 <= Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0 <= n_pre).
  { rewrite Hnew_j by lia. apply PreH63; lia. }
  assert (HDPnew : DP0Prefix values (replace_Znth i (0 + 1) dp0_l_2) (i + 1)).
  { intros j Hj. destruct (Z.eq_dec j i) as [He | Hne].
    - subst j. rewrite Hnew_i. exact HB0.
    - rewrite Hnew_j by lia. apply PreH62; lia. }
  assert (Hdpb : forall k_4 : Z, 0 <= k_4 < i + 1 ->
            1 <= Znth k_4 (replace_Znth i (0 + 1) dp0_l_2) 0 <= n_pre).
  { intros k4 Hk4. destruct (Z.eq_dec k4 i) as [He | Hne].
    - subst k4. rewrite Hnew_i. lia.
    - rewrite Hnew_j by lia. apply PreH63; lia. }
  assert (HBit0 : Bit0Model values vals_l_2 (replace_Znth i (0 + 1) dp0_l_2)
                    (MaxBitInsert m0_2 retval (0 + 1)) (i + 1) nvals).
  { apply (bit0_model_insert__dp_body_branches_k6 values vals_l_2 dp0_l_2
             (replace_Znth i (0 + 1) dp0_l_2) m0_2 i nvals retval (0 + 1));
      [lia | apply (proj1 PreH53) | exact PreH64 | exact Hnew_j | exact Hnew_i | exact PreH34]. }
  assert (HBit1 : Bit1Model values vals_l_2
                    (MaxBitInsert m1_2 retval_2 (0 + 1)) (i + 1) nvals).
  { apply (bit1_model_insert__dp_body_branches_k6 values vals_l_2 m1_2 i nvals retval_2
             (0 + 1));
      [lia | apply (proj1 PreH53) | exact PreH65 | exact HB1 | exact PreH31]. }
  assert (HBitX : Bit0Model values vals_l_2 (replace_Znth i (0 + 1) dp0_l_2)
                    (MaxBitInsert mX_2 retval_6
                       (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0))
                    (i + 1 - 1) nvals).
  { replace (i + 1 - 1) with ((i - 1) + 1) by lia.
    apply (bit0_model_insert__dp_body_branches_k6 values vals_l_2 dp0_l_2
             (replace_Znth i (0 + 1) dp0_l_2) mX_2 (i - 1) nvals retval_6
             (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0));
      [lia | apply (proj1 PreH53) | exact PreH66 | | reflexivity | exact PreH5].
    intros j Hj. apply Hnew_j; lia. }
  assert (HCP : ClampedPrefixMax (replace_Znth i (0 + 1) dp0_l_2) (i + 1) best0).
  { apply (clamped_prefix_step_keep__dp_body_branches_k6
             (replace_Znth i (0 + 1) dp0_l_2) i best0 (0 + 1));
      [ | lia | exact Hnew_i | lia].
    apply (clamped_prefix_ext__dp_body_branches_k6 dp0_l_2); [exact PreH67 | exact Hnew_j]. }
  assert (HCB1 : ClampedBest1Upto values (i + 1) best1).
  { apply (clamped_best1_step_keep__dp_body_branches_k6 values i best1 (0 + 1));
      [exact PreH68 | lia | exact HB1 | lia]. }
  assert (HCP0 : ClampedPrefixMax (replace_Znth i (0 + 1) dp0_l_2)
                   (i + 1 - 1) best0_prefix).
  { replace (i + 1 - 1) with ((i - 1) + 1) by lia.
    apply (clamped_prefix_step_keep__dp_body_branches_k6
             (replace_Znth i (0 + 1) dp0_l_2) (i - 1) best0_prefix
             (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0));
      [ | lia | reflexivity | exact PreH1].
    apply (clamped_prefix_ext__dp_body_branches_k6 dp0_l_2); [exact PreH69 |].
    intros j Hj. apply Hnew_j; lia. }
  assert (Hmb : forall r : Z, 0 <= r <= nvals ->
    (((-1000000000 <= Znth r (MaxBitInsert m0_2 retval (0 + 1)) 0 <= n_pre /\
       -1000000000 <= Znth r (MaxBitInsert m1_2 retval_2 (0 + 1)) 0) /\
      Znth r (MaxBitInsert m1_2 retval_2 (0 + 1)) 0 <= n_pre) /\
     -1000000000 <= Znth r (MaxBitInsert mX_2 retval_6
        (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)) 0) /\
     Znth r (MaxBitInsert mX_2 retval_6
        (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)) 0 <= n_pre).
  { intros r Hr.
    assert (Hb0 : -1000000000 <=
                  Znth r (MaxBitInsert m0_2 retval (0 + 1)) 0 <= n_pre).
    { apply (Znth_maxbitinsert_bound__dp_body_branches_k6 m0_2 retval (0 + 1) r
               (-1000000000) n_pre); [lia | lia | | lia | lia].
      intros t Ht. pose proof (PreH61 t ltac:(lia)). lia. }
    assert (Hb1 : -1000000000 <=
                  Znth r (MaxBitInsert m1_2 retval_2 (0 + 1)) 0 <= n_pre).
    { apply (Znth_maxbitinsert_bound__dp_body_branches_k6 m1_2 retval_2 (0 + 1) r
               (-1000000000) n_pre); [lia | lia | | lia | lia].
      intros t Ht. pose proof (PreH61 t ltac:(lia)). lia. }
    assert (HbX : -1000000000 <= Znth r (MaxBitInsert mX_2 retval_6
        (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0)) 0 <= n_pre).
    { apply (Znth_maxbitinsert_bound__dp_body_branches_k6 mX_2 retval_6
               (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0) r
               (-1000000000) n_pre); [lia | lia | | lia | lia].
      intros t Ht. pose proof (PreH61 t ltac:(lia)). lia. }
    lia. }
  assert (Hbb : forall k_3 : Z, 0 <= k_3 < nvals + 1 ->
    (((-1000000000 <= Znth k_3 bit_l1 0 <= 1000000000 /\
       -1000000000 <= Znth k_3 bit_l1_2 0) /\ Znth k_3 bit_l1_2 0 <= 1000000000) /\
     -1000000000 <= Znth k_3 bit_l1_3 0) /\ Znth k_3 bit_l1_3 0 <= 1000000000).
  { intros k3 Hk3. pose proof (PreH14 k3 Hk3). pose proof (PreH10 k3 Hk3).
    pose proof (PreH3 k3 Hk3). lia. }
  Exists (MaxBitInsert mX_2 retval_6
            (Znth (i - 1) (replace_Znth i (0 + 1) dp0_l_2) 0))
         (MaxBitInsert m1_2 retval_2 (0 + 1))
         (MaxBitInsert m0_2 retval (0 + 1))
         bit_l1_3 bit_l1_2 bit_l1
         (replace_Znth i (0 + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  { repeat sepcon_cancel. }
  split_pures; dump_pre_spatial.
  all: first [assumption | lia].
Qed.

Lemma proof_of_solver_entail_wit_12_65 : solver_entail_wit_12_65.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exfalso.
  pose proof (bit0_query_empty__dp_body_branches_k6 values vals_l_2 dp0_l_2 m0_2 i nvals
                retval_2 PreH46 ltac:(lia) ltac:(lia)) as Hq.
  unfold MaxBitNeg in Hq. lia.
Qed.

Lemma proof_of_solver_entail_wit_12_66 : solver_entail_wit_12_66.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  assert (Hi0 : i = 0) by lia. subst i.
  assert (Hlm0 : Zlength m0_2 = nvals + 1) by (apply (proj1 PreH46)).
  assert (HkeyC : Znth 0 c_l_2 0 = KeyAt values 0) by (apply PreH32; lia).
  rewrite HkeyC in PreH16.
  assert (Hdplen : Zlength (replace_Znth 0 (0 + 1) dp0_l_2) = n_pre)
    by (rewrite Zlength_replace_Znth__dp_body_branches_k6; exact PreH31).
  assert (Hnew_i : Znth 0 (replace_Znth 0 (0 + 1) dp0_l_2) 0 = 0 + 1)
    by (apply Znth_replace_Znth_Same; lia).
  assert (Hnew_j : forall j, 0 <= j < 0 ->
                   Znth j (replace_Znth 0 (0 + 1) dp0_l_2) 0 = Znth j dp0_l_2 0)
    by (intros j Hj; lia).
  assert (HB0 : Best0EndingAt values 0 (0 + 1)).
  { pose proof (best0_step__dp_body_branches_k6 values vals_l_2 dp0_l_2 m0_2 0 nvals retval
                  ltac:(lia) PreH35 PreH44 PreH46 PreH16) as HB.
    replace (Z.max (RangeMax m0_2 1 (retval + 1)) 0 + 1) with (0 + 1) in HB by lia.
    exact HB. }
  assert (HDPnew : DP0Prefix values (replace_Znth 0 (0 + 1) dp0_l_2) (0 + 1)).
  { intros j Hj. replace j with 0 by lia. rewrite Hnew_i. exact HB0. }
  assert (Hdpb : forall k_4 : Z, 0 <= k_4 < 0 + 1 ->
                 1 <= Znth k_4 (replace_Znth 0 (0 + 1) dp0_l_2) 0 <= n_pre).
  { intros k4 Hk4. replace k4 with 0 by lia. rewrite Hnew_i. lia. }
  assert (HBit0 : Bit0Model values vals_l_2 (replace_Znth 0 (0 + 1) dp0_l_2)
                    (MaxBitInsert m0_2 retval (0 + 1)) (0 + 1) nvals).
  { apply (bit0_model_insert__dp_body_branches_k6 values vals_l_2 dp0_l_2
             (replace_Znth 0 (0 + 1) dp0_l_2) m0_2 0 nvals retval (0 + 1));
      [lia | apply (proj1 PreH35) | exact PreH46 | exact Hnew_j | exact Hnew_i | exact PreH16]. }
  assert (HBitX : Bit0Model values vals_l_2 (replace_Znth 0 (0 + 1) dp0_l_2) mX_2
                    (0 + 1 - 1) nvals).
  { replace (0 + 1 - 1) with 0 by lia.
    apply (bit0_model_neg__dp_body_branches_k6 values vals_l_2 dp0_l_2
             (replace_Znth 0 (0 + 1) dp0_l_2) mX_2 (0 - 1) nvals PreH48). lia. }
  assert (HBit1 : Bit1Model values vals_l_2 m1_2 (0 + 1) nvals).
  { replace (0 + 1) with 1 by lia.
    apply (bit1_model_step_zero__dp_body_branches_k6 values vals_l_2 m1_2 0 nvals PreH47). lia. }
  assert (HCP : ClampedPrefixMax (replace_Znth 0 (0 + 1) dp0_l_2) (0 + 1) (0 + 1)).
  { apply (clamped_prefix_step_up__dp_body_branches_k6
             (replace_Znth 0 (0 + 1) dp0_l_2) 0 best0 (0 + 1));
      [ | lia | exact Hnew_i | lia | lia].
    apply (clamped_prefix_ext__dp_body_branches_k6 dp0_l_2); [exact PreH49 | exact Hnew_j]. }
  assert (HCB1 : ClampedBest1Upto values (0 + 1) best1).
  { replace (0 + 1) with 1 by lia.
    apply clamped_best1_zero_step__dp_body_branches_k6. exact PreH50. }
  assert (HCP0 : ClampedPrefixMax (replace_Znth 0 (0 + 1) dp0_l_2) (0 + 1 - 1) best0_prefix).
  { apply (clamped_prefix_neg__dp_body_branches_k6 dp0_l_2
             (replace_Znth 0 (0 + 1) dp0_l_2) (0 - 1) (0 + 1 - 1) best0_prefix PreH51); lia. }
  assert (Hmb : forall r : Z, 0 <= r <= nvals ->
    (((-1000000000 <= Znth r (MaxBitInsert m0_2 retval (0 + 1)) 0 <= n_pre /\
       -1000000000 <= Znth r m1_2 0) /\ Znth r m1_2 0 <= n_pre) /\
     -1000000000 <= Znth r mX_2 0) /\ Znth r mX_2 0 <= n_pre).
  { intros r Hr.
    assert (Hb0 : -1000000000 <= Znth r (MaxBitInsert m0_2 retval (0 + 1)) 0 <= n_pre).
    { apply (Znth_maxbitinsert_bound__dp_body_branches_k6 m0_2 retval (0 + 1) r
               (-1000000000) n_pre); [lia | lia | | lia | lia].
      intros t Ht. pose proof (PreH43 t ltac:(lia)). lia. }
    pose proof (PreH43 r Hr). lia. }
  assert (Hbb : forall k_3 : Z, 0 <= k_3 < nvals + 1 ->
    (((-1000000000 <= Znth k_3 bit_l1 0 <= 1000000000 /\
       -1000000000 <= Znth k_3 bit1_l_2 0) /\ Znth k_3 bit1_l_2 0 <= 1000000000) /\
     -1000000000 <= Znth k_3 bitX_l_2 0) /\ Znth k_3 bitX_l_2 0 <= 1000000000).
  { intros k3 Hk3. pose proof (PreH4 k3 Hk3). pose proof (PreH36 k3 Hk3). lia. }
  Exists mX_2 m1_2 (MaxBitInsert m0_2 retval (0 + 1)) bitX_l_2 bit1_l_2 bit_l1
         (replace_Znth 0 (0 + 1) dp0_l_2) vals_l_2 c_l_2.
  split_pure_spatial.
  { repeat sepcon_cancel. }
  split_pures; dump_pre_spatial.
  all: first [assumption | lia].
Qed.

Lemma proof_of_solver_entail_wit_12_67 : solver_entail_wit_12_67.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exfalso.
  pose proof (bit0_query_empty__dp_body_branches_k6 values vals_l_2 dp0_l_2 m0_2 i nvals
                retval PreH46 ltac:(lia) ltac:(lia)) as Hq.
  unfold MaxBitNeg in Hq. lia.
Qed.

Lemma proof_of_solver_entail_wit_12_68 : solver_entail_wit_12_68.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  exfalso.
  pose proof (clamped_prefix_zero__dp_body_branches_k6 dp0_l_2 i best0 PreH49 ltac:(lia)) as Hz.
  lia.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Hieq : i = n_pre) by lia. subst i.
  apply (solver_spec_from_invariant__solver_result_spec values dp0_l n_pre best0 best1
           best0_prefix); try assumption; lia.
Qed.

Lemma proof_of_solver_return_wit_1_split_goal_spatial : solver_return_wit_1_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply (Int64Array.full_to_full_shape c_pre n_pre c_l).
  sep_apply (IntArray.full_to_full_shape vals_pre (2 * n_pre) vals_l).
  sep_apply (IntArray.full_to_full_shape dp0_pre n_pre dp0_l).
  sep_apply (IntArray.full_to_seg bit0_pre (nvals + 1)).
  sep_apply (IntArray.seg_to_seg_shape bit0_pre 0 (nvals + 1)).
  sep_apply (IntArray.seg_shape_merge_to_full_shape bit0_pre 0 (nvals + 1) (2 * n_pre + 1)); [ | lia ].
  replace (bit0_pre + 0 * sizeof ( INT )) with bit0_pre by lia.
  replace (2 * n_pre + 1 - 0) with (2 * n_pre + 1) by lia.
  sep_apply (IntArray.full_to_seg bit1_pre (nvals + 1)).
  sep_apply (IntArray.seg_to_seg_shape bit1_pre 0 (nvals + 1)).
  sep_apply (IntArray.seg_shape_merge_to_full_shape bit1_pre 0 (nvals + 1) (2 * n_pre + 1)); [ | lia ].
  replace (bit1_pre + 0 * sizeof ( INT )) with bit1_pre by lia.
  replace (2 * n_pre + 1 - 0) with (2 * n_pre + 1) by lia.
  sep_apply (IntArray.full_to_seg bitX_pre (nvals + 1)).
  sep_apply (IntArray.seg_to_seg_shape bitX_pre 0 (nvals + 1)).
  sep_apply (IntArray.seg_shape_merge_to_full_shape bitX_pre 0 (nvals + 1) (2 * n_pre + 1)); [ | lia ].
  replace (bitX_pre + 0 * sizeof ( INT )) with bitX_pre by lia.
  replace (2 * n_pre + 1 - 0) with (2 * n_pre + 1) by lia.
  cancel.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_return_wit_1_split_goal_spatial.
  - Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_2_split_goal_1 : solver_return_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Hieq : i = n_pre) by lia. subst i.
  apply (solver_spec_from_invariant__solver_result_spec values dp0_l n_pre best0 best1
           best0_prefix); try assumption; lia.
Qed.

Lemma proof_of_solver_return_wit_2_split_goal_spatial : solver_return_wit_2_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply (Int64Array.full_to_full_shape c_pre n_pre c_l).
  sep_apply (IntArray.full_to_full_shape vals_pre (2 * n_pre) vals_l).
  sep_apply (IntArray.full_to_full_shape dp0_pre n_pre dp0_l).
  sep_apply (IntArray.full_to_seg bit0_pre (nvals + 1)).
  sep_apply (IntArray.seg_to_seg_shape bit0_pre 0 (nvals + 1)).
  sep_apply (IntArray.seg_shape_merge_to_full_shape bit0_pre 0 (nvals + 1) (2 * n_pre + 1)); [ | lia ].
  replace (bit0_pre + 0 * sizeof ( INT )) with bit0_pre by lia.
  replace (2 * n_pre + 1 - 0) with (2 * n_pre + 1) by lia.
  sep_apply (IntArray.full_to_seg bit1_pre (nvals + 1)).
  sep_apply (IntArray.seg_to_seg_shape bit1_pre 0 (nvals + 1)).
  sep_apply (IntArray.seg_shape_merge_to_full_shape bit1_pre 0 (nvals + 1) (2 * n_pre + 1)); [ | lia ].
  replace (bit1_pre + 0 * sizeof ( INT )) with bit1_pre by lia.
  replace (2 * n_pre + 1 - 0) with (2 * n_pre + 1) by lia.
  sep_apply (IntArray.full_to_seg bitX_pre (nvals + 1)).
  sep_apply (IntArray.seg_to_seg_shape bitX_pre 0 (nvals + 1)).
  sep_apply (IntArray.seg_shape_merge_to_full_shape bitX_pre 0 (nvals + 1) (2 * n_pre + 1)); [ | lia ].
  replace (bitX_pre + 0 * sizeof ( INT )) with bitX_pre by lia.
  replace (2 * n_pre + 1 - 0) with (2 * n_pre + 1) by lia.
  cancel.
Qed.

Lemma proof_of_solver_return_wit_2 : solver_return_wit_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_return_wit_2_split_goal_spatial.
  - Goal_apply proof_of_solver_return_wit_2_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_3_split_goal_1 : solver_return_wit_3_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Hieq : i = n_pre) by lia. subst i.
  apply (solver_spec_from_invariant__solver_result_spec values dp0_l n_pre best0 best1
           best0_prefix); try assumption; lia.
Qed.

Lemma proof_of_solver_return_wit_3_split_goal_spatial : solver_return_wit_3_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply (Int64Array.full_to_full_shape c_pre n_pre c_l).
  sep_apply (IntArray.full_to_full_shape vals_pre (2 * n_pre) vals_l).
  sep_apply (IntArray.full_to_full_shape dp0_pre n_pre dp0_l).
  sep_apply (IntArray.full_to_seg bit0_pre (nvals + 1)).
  sep_apply (IntArray.seg_to_seg_shape bit0_pre 0 (nvals + 1)).
  sep_apply (IntArray.seg_shape_merge_to_full_shape bit0_pre 0 (nvals + 1) (2 * n_pre + 1)); [ | lia ].
  replace (bit0_pre + 0 * sizeof ( INT )) with bit0_pre by lia.
  replace (2 * n_pre + 1 - 0) with (2 * n_pre + 1) by lia.
  sep_apply (IntArray.full_to_seg bit1_pre (nvals + 1)).
  sep_apply (IntArray.seg_to_seg_shape bit1_pre 0 (nvals + 1)).
  sep_apply (IntArray.seg_shape_merge_to_full_shape bit1_pre 0 (nvals + 1) (2 * n_pre + 1)); [ | lia ].
  replace (bit1_pre + 0 * sizeof ( INT )) with bit1_pre by lia.
  replace (2 * n_pre + 1 - 0) with (2 * n_pre + 1) by lia.
  sep_apply (IntArray.full_to_seg bitX_pre (nvals + 1)).
  sep_apply (IntArray.seg_to_seg_shape bitX_pre 0 (nvals + 1)).
  sep_apply (IntArray.seg_shape_merge_to_full_shape bitX_pre 0 (nvals + 1) (2 * n_pre + 1)); [ | lia ].
  replace (bitX_pre + 0 * sizeof ( INT )) with bitX_pre by lia.
  replace (2 * n_pre + 1 - 0) with (2 * n_pre + 1) by lia.
  cancel.
Qed.

Lemma proof_of_solver_return_wit_3 : solver_return_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_return_wit_3_split_goal_spatial.
  - Goal_apply proof_of_solver_return_wit_3_split_goal_1.
Qed.

Lemma proof_of_solver_return_wit_4_split_goal_1 : solver_return_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Hieq : i = n_pre) by lia. subst i.
  apply (solver_spec_from_invariant__solver_result_spec values dp0_l n_pre best0 best1
           best0_prefix); try assumption; lia.
Qed.

Lemma proof_of_solver_return_wit_4_split_goal_spatial : solver_return_wit_4_split_goal_spatial.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  sep_apply (Int64Array.full_to_full_shape c_pre n_pre c_l).
  sep_apply (IntArray.full_to_full_shape vals_pre (2 * n_pre) vals_l).
  sep_apply (IntArray.full_to_full_shape dp0_pre n_pre dp0_l).
  sep_apply (IntArray.full_to_seg bit0_pre (nvals + 1)).
  sep_apply (IntArray.seg_to_seg_shape bit0_pre 0 (nvals + 1)).
  sep_apply (IntArray.seg_shape_merge_to_full_shape bit0_pre 0 (nvals + 1) (2 * n_pre + 1)); [ | lia ].
  replace (bit0_pre + 0 * sizeof ( INT )) with bit0_pre by lia.
  replace (2 * n_pre + 1 - 0) with (2 * n_pre + 1) by lia.
  sep_apply (IntArray.full_to_seg bit1_pre (nvals + 1)).
  sep_apply (IntArray.seg_to_seg_shape bit1_pre 0 (nvals + 1)).
  sep_apply (IntArray.seg_shape_merge_to_full_shape bit1_pre 0 (nvals + 1) (2 * n_pre + 1)); [ | lia ].
  replace (bit1_pre + 0 * sizeof ( INT )) with bit1_pre by lia.
  replace (2 * n_pre + 1 - 0) with (2 * n_pre + 1) by lia.
  sep_apply (IntArray.full_to_seg bitX_pre (nvals + 1)).
  sep_apply (IntArray.seg_to_seg_shape bitX_pre 0 (nvals + 1)).
  sep_apply (IntArray.seg_shape_merge_to_full_shape bitX_pre 0 (nvals + 1) (2 * n_pre + 1)); [ | lia ].
  replace (bitX_pre + 0 * sizeof ( INT )) with bitX_pre by lia.
  replace (2 * n_pre + 1 - 0) with (2 * n_pre + 1) by lia.
  cancel.
Qed.

Lemma proof_of_solver_return_wit_4 : solver_return_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_return_wit_4_split_goal_spatial.
  - Goal_apply proof_of_solver_return_wit_4_split_goal_1.
Qed.

Lemma proof_of_solver_partial_solve_wit_20_pure_split_goal_1 : solver_partial_solve_wit_20_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact HSI.
Qed.

Lemma proof_of_solver_partial_solve_wit_20_pure_split_goal_2 : solver_partial_solve_wit_20_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
  match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H i) by lia end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact (proj1 (HMEM i ltac:(lia))).
Qed.

Lemma proof_of_solver_partial_solve_wit_20_pure_split_goal_3 : solver_partial_solve_wit_20_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_20_pure_split_goal_4 : solver_partial_solve_wit_20_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
  match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H i) by lia end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact (proj1 (HMEM i ltac:(lia))).
Qed.

Lemma proof_of_solver_partial_solve_wit_20_pure_split_goal_5 : solver_partial_solve_wit_20_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact HSI.
Qed.

Lemma proof_of_solver_partial_solve_wit_20_pure : solver_partial_solve_wit_20_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_20_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_20_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_20_pure_split_goal_3.
  - Goal_apply proof_of_solver_partial_solve_wit_20_pure_split_goal_4.
  - Goal_apply proof_of_solver_partial_solve_wit_20_pure_split_goal_5.
Qed.

Lemma proof_of_solver_partial_solve_wit_22_pure_split_goal_1 : solver_partial_solve_wit_22_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact HSI.
Qed.

Lemma proof_of_solver_partial_solve_wit_22_pure_split_goal_2 : solver_partial_solve_wit_22_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
  match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H i) by lia end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact (proj2 (HMEM i ltac:(lia))).
Qed.

Lemma proof_of_solver_partial_solve_wit_22_pure_split_goal_3 : solver_partial_solve_wit_22_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
Qed.

Lemma proof_of_solver_partial_solve_wit_22_pure_split_goal_4 : solver_partial_solve_wit_22_pure_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [_ [HMEM _]] end.
  match goal with H : KeyPrefix _ _ _ |- _ => unfold KeyPrefix in H; rewrite (H i) by lia end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact (proj2 (HMEM i ltac:(lia))).
Qed.

Lemma proof_of_solver_partial_solve_wit_22_pure_split_goal_5 : solver_partial_solve_wit_22_pure_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : CompressedKeys _ _ _ |- _ => unfold CompressedKeys in H; destruct H as [HSI _] end.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  exact HSI.
Qed.

Lemma proof_of_solver_partial_solve_wit_22_pure : solver_partial_solve_wit_22_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_22_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_22_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_22_pure_split_goal_3.
  - Goal_apply proof_of_solver_partial_solve_wit_22_pure_split_goal_4.
  - Goal_apply proof_of_solver_partial_solve_wit_22_pure_split_goal_5.
Qed.

Lemma proof_of_solver_partial_solve_wit_23_pure_split_goal_1 : solver_partial_solve_wit_23_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH42 k ltac:(lia)). lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_23_pure_split_goal_2 : solver_partial_solve_wit_23_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH42 k ltac:(lia)). lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_23_pure : solver_partial_solve_wit_23_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_23_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_23_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_24_pure_split_goal_1 : solver_partial_solve_wit_24_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH55 k ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_24_pure_split_goal_2 : solver_partial_solve_wit_24_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH55 k ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_24_pure : solver_partial_solve_wit_24_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_24_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_24_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_25_pure_split_goal_1 : solver_partial_solve_wit_25_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH55 k ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_25_pure_split_goal_2 : solver_partial_solve_wit_25_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH55 k ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_25_pure : solver_partial_solve_wit_25_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_25_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_25_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_26_pure_split_goal_1 : solver_partial_solve_wit_26_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  intros k Hk.
  match goal with
  | H : forall _ : Z, _ -> (_ /\ (Znth _ bitX_l 0 <= 1000000000)) |- _ =>
      pose proof (H k Hk) as HB
  end.
  split; [ exact (proj2 (proj1 HB)) | exact (proj2 HB) ].
Qed.

Lemma proof_of_solver_partial_solve_wit_26_pure_split_goal_2 : solver_partial_solve_wit_26_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  match goal with
  | H : forall _ : Z, _ -> (_ /\ (Znth _ bitX_l 0 <= 1000000000)) |- _ =>
      pose proof (H k Hk) as HB
  end.
  split; [ exact (proj2 (proj1 HB)) | exact (proj2 HB) ].
Qed.

Lemma proof_of_solver_partial_solve_wit_26_pure : solver_partial_solve_wit_26_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_26_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_26_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_27_pure_split_goal_1 : solver_partial_solve_wit_27_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  intros k Hk.
  match goal with
  | H : forall _ : Z, _ -> (_ /\ (Znth _ bitX_l 0 <= 1000000000)) |- _ =>
      pose proof (H k Hk) as HB
  end.
  split; [ exact (proj2 (proj1 HB)) | exact (proj2 HB) ].
Qed.

Lemma proof_of_solver_partial_solve_wit_27_pure_split_goal_2 : solver_partial_solve_wit_27_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  match goal with
  | H : forall _ : Z, _ -> (_ /\ (Znth _ bitX_l 0 <= 1000000000)) |- _ =>
      pose proof (H k Hk) as HB
  end.
  split; [ exact (proj2 (proj1 HB)) | exact (proj2 HB) ].
Qed.

Lemma proof_of_solver_partial_solve_wit_27_pure : solver_partial_solve_wit_27_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_27_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_27_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_28_pure_split_goal_1 : solver_partial_solve_wit_28_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  intros k Hk.
  match goal with
  | H : forall _ : Z, _ -> (_ /\ (Znth _ bitX_l 0 <= 1000000000)) |- _ =>
      pose proof (H k Hk) as HB
  end.
  split; [ exact (proj2 (proj1 HB)) | exact (proj2 HB) ].
Qed.

Lemma proof_of_solver_partial_solve_wit_28_pure_split_goal_2 : solver_partial_solve_wit_28_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  match goal with
  | H : forall _ : Z, _ -> (_ /\ (Znth _ bitX_l 0 <= 1000000000)) |- _ =>
      pose proof (H k Hk) as HB
  end.
  split; [ exact (proj2 (proj1 HB)) | exact (proj2 HB) ].
Qed.

Lemma proof_of_solver_partial_solve_wit_28_pure : solver_partial_solve_wit_28_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_28_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_28_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_29_pure_split_goal_1 : solver_partial_solve_wit_29_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  match goal with H : nvals = uniq |- _ => rewrite <- H end.
  intros k Hk.
  match goal with
  | H : forall _ : Z, _ -> (_ /\ (Znth _ bitX_l 0 <= 1000000000)) |- _ =>
      pose proof (H k Hk) as HB
  end.
  split; [ exact (proj2 (proj1 HB)) | exact (proj2 HB) ].
Qed.

Lemma proof_of_solver_partial_solve_wit_29_pure_split_goal_2 : solver_partial_solve_wit_29_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  match goal with
  | H : forall _ : Z, _ -> (_ /\ (Znth _ bitX_l 0 <= 1000000000)) |- _ =>
      pose proof (H k Hk) as HB
  end.
  split; [ exact (proj2 (proj1 HB)) | exact (proj2 HB) ].
Qed.

Lemma proof_of_solver_partial_solve_wit_29_pure : solver_partial_solve_wit_29_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_29_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_29_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_40_pure_split_goal_1 : solver_partial_solve_wit_40_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Hb : RangeMax m0 1 (retval + 1) <= n_pre).
  { apply rangemax_le_bound__pure_d1_bound_bit0.
    - unfold MaxBitNeg. lia.
    - intros r Hr. specialize (PreH66 r ltac:(lia)). lia. }
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_40_pure_split_goal_2 : solver_partial_solve_wit_40_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH59 k ltac:(lia)). lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_40_pure_split_goal_3 : solver_partial_solve_wit_40_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH59 k ltac:(lia)). lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_40_pure : solver_partial_solve_wit_40_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_40_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_40_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_40_pure_split_goal_3.
Qed. 

Lemma proof_of_solver_partial_solve_wit_41_pure_split_goal_1 : solver_partial_solve_wit_41_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH59 k ltac:(lia)). lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_41_pure_split_goal_2 : solver_partial_solve_wit_41_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH59 k ltac:(lia)). lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_41_pure : solver_partial_solve_wit_41_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_41_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_41_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_42_pure_split_goal_1 : solver_partial_solve_wit_42_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Hb : RangeMax m0 1 (retval + 1) <= n_pre).
  { apply rangemax_le_bound__pure_d1_bound_bit0.
    - unfold MaxBitNeg. lia.
    - intros r Hr. specialize (PreH66 r ltac:(lia)). lia. }
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_42_pure_split_goal_2 : solver_partial_solve_wit_42_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH59 k ltac:(lia)). lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_42_pure_split_goal_3 : solver_partial_solve_wit_42_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH59 k ltac:(lia)). lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_42_pure : solver_partial_solve_wit_42_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_42_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_42_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_42_pure_split_goal_3.
Qed. 

Lemma proof_of_solver_partial_solve_wit_43_pure_split_goal_1 : solver_partial_solve_wit_43_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH59 k ltac:(lia)). lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_43_pure_split_goal_2 : solver_partial_solve_wit_43_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH59 k ltac:(lia)). lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_43_pure : solver_partial_solve_wit_43_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_43_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_43_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_44_pure_split_goal_1 : solver_partial_solve_wit_44_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Hb : RangeMax m0 1 (retval + 1) <= n_pre).
  { apply rangemax_le_bound__pure_d1_bound_bit0.
    - unfold MaxBitNeg. lia.
    - intros r Hr. specialize (PreH66 r ltac:(lia)). lia. }
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_44_pure_split_goal_2 : solver_partial_solve_wit_44_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH59 k ltac:(lia)). lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_44_pure_split_goal_3 : solver_partial_solve_wit_44_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH59 k ltac:(lia)). lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_44_pure : solver_partial_solve_wit_44_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_44_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_44_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_44_pure_split_goal_3.
Qed. 

Lemma proof_of_solver_partial_solve_wit_45_pure_split_goal_1 : solver_partial_solve_wit_45_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH59 k ltac:(lia)). lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_45_pure_split_goal_2 : solver_partial_solve_wit_45_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH59 k ltac:(lia)). lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_45_pure : solver_partial_solve_wit_45_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_45_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_45_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_46_pure_split_goal_1 : solver_partial_solve_wit_46_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  assert (Hb : RangeMax m0 1 (retval + 1) <= n_pre).
  { apply rangemax_le_bound__pure_d1_bound_bit0.
    - unfold MaxBitNeg. lia.
    - intros r Hr. specialize (PreH66 r ltac:(lia)). lia. }
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_46_pure_split_goal_2 : solver_partial_solve_wit_46_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH59 k ltac:(lia)). lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_46_pure_split_goal_3 : solver_partial_solve_wit_46_pure_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH59 k ltac:(lia)). lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_46_pure : solver_partial_solve_wit_46_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_46_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_46_pure_split_goal_2.
  - Goal_apply proof_of_solver_partial_solve_wit_46_pure_split_goal_3.
Qed. 

Lemma proof_of_solver_partial_solve_wit_47_pure_split_goal_1 : solver_partial_solve_wit_47_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH57 k ltac:(lia)). lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_47_pure_split_goal_2 : solver_partial_solve_wit_47_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || int_auto).
  dump_pre_spatial.
  intros k Hk.
  specialize (PreH57 k ltac:(lia)). lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_47_pure : solver_partial_solve_wit_47_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_47_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_47_pure_split_goal_2.
Qed.

Lemma proof_of_solver_partial_solve_wit_48_pure_split_goal_1 : solver_partial_solve_wit_48_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  intros k Hk.
  assert (Hk' : 0 <= k /\ k < nvals + 1) by lia.
  specialize (PreH61 k Hk').
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_48_pure_split_goal_2 : solver_partial_solve_wit_48_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  intros k Hk.
  assert (Hk' : 0 <= k /\ k < nvals + 1) by lia.
  specialize (PreH61 k Hk').
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_48_pure : solver_partial_solve_wit_48_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_partial_solve_wit_48_pure_split_goal_1.
  Goal_apply proof_of_solver_partial_solve_wit_48_pure_split_goal_2.
Qed. 

Lemma proof_of_solver_partial_solve_wit_49_pure_split_goal_1 : solver_partial_solve_wit_49_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  intros k Hk.
  assert (Hk' : 0 <= k /\ k < nvals + 1) by lia.
  specialize (PreH61 k Hk').
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_49_pure_split_goal_2 : solver_partial_solve_wit_49_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  intros k Hk.
  assert (Hk' : 0 <= k /\ k < nvals + 1) by lia.
  specialize (PreH61 k Hk').
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_49_pure : solver_partial_solve_wit_49_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_partial_solve_wit_49_pure_split_goal_1.
  Goal_apply proof_of_solver_partial_solve_wit_49_pure_split_goal_2.
Qed. 

Lemma proof_of_solver_partial_solve_wit_50_pure_split_goal_1 : solver_partial_solve_wit_50_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  intros k Hk.
  assert (Hk' : 0 <= k /\ k < nvals + 1) by lia.
  specialize (PreH61 k Hk').
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_50_pure_split_goal_2 : solver_partial_solve_wit_50_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  intros k Hk.
  assert (Hk' : 0 <= k /\ k < nvals + 1) by lia.
  specialize (PreH61 k Hk').
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_50_pure : solver_partial_solve_wit_50_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_partial_solve_wit_50_pure_split_goal_1.
  Goal_apply proof_of_solver_partial_solve_wit_50_pure_split_goal_2.
Qed. 

Lemma proof_of_solver_partial_solve_wit_51_pure_split_goal_1 : solver_partial_solve_wit_51_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  intros k Hk.
  assert (Hk' : 0 <= k /\ k < nvals + 1) by lia.
  specialize (PreH61 k Hk').
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_51_pure_split_goal_2 : solver_partial_solve_wit_51_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  intros k Hk.
  assert (Hk' : 0 <= k /\ k < nvals + 1) by lia.
  specialize (PreH61 k Hk').
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_51_pure : solver_partial_solve_wit_51_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_partial_solve_wit_51_pure_split_goal_1.
  Goal_apply proof_of_solver_partial_solve_wit_51_pure_split_goal_2.
Qed. 

Lemma proof_of_solver_partial_solve_wit_52_pure_split_goal_1 : solver_partial_solve_wit_52_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  intros k Hk.
  assert (Hk' : 0 <= k /\ k < nvals + 1) by lia.
  specialize (PreH61 k Hk').
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_52_pure_split_goal_2 : solver_partial_solve_wit_52_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(idtac).
  dump_pre_spatial.
  intros k Hk.
  assert (Hk' : 0 <= k /\ k < nvals + 1) by lia.
  specialize (PreH61 k Hk').
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_52_pure : solver_partial_solve_wit_52_pure.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_partial_solve_wit_52_pure_split_goal_1.
  Goal_apply proof_of_solver_partial_solve_wit_52_pure_split_goal_2.
Qed. 
