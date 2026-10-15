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
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P083_938E_max_history_goal.
From SimpleC.EE.LLM_bench.Codeforces.examples_shard09 Require Import P083_938E_max_history_proof_auto.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import AUXLib.MonotonicList.
Require Import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P083_938E_max_history_lib.
Local Open Scope sac.

Lemma proof_of_power_entail_wit_1_split_goal_1 : power_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold PowerLoopState.
  destruct (rem_eq_mod_nonneg__power_modexp b_pre 1000000007 ltac:(lia) ltac:(lia)) as [Hrb Hbnd].
  rewrite Hrb.
  rewrite (Z.mod_small b_pre 1000000007) by lia.
  rewrite Z.mul_1_l.
  reflexivity.
Qed.

Lemma proof_of_power_entail_wit_1_split_goal_2 : power_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (rem_eq_mod_nonneg__power_modexp b_pre 1000000007 ltac:(lia) ltac:(lia)) as [Hrb Hbnd].
  lia.
Qed.

Lemma proof_of_power_entail_wit_1_split_goal_3 : power_entail_wit_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (rem_eq_mod_nonneg__power_modexp b_pre 1000000007 ltac:(lia) ltac:(lia)) as [Hrb Hbnd].
  lia.
Qed.

Lemma proof_of_power_entail_wit_1 : power_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_power_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_power_entail_wit_1_split_goal_2.
  - Goal_apply proof_of_power_entail_wit_1_split_goal_3.
Qed.

Lemma proof_of_power_entail_wit_2_1_split_goal_1 : power_entail_wit_2_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold PowerLoopState in PreH11 |- *.
  destruct (shiftr_land1_decompose__power_modexp e ltac:(lia)) as [Hs [[Hq0 Hqe] [Hdec Hcase]]].
  assert (He : e = 2 * Z.shiftr e 1 + 1) by lia.
  remember (Z.shiftr e 1) as q eqn:Hqdef.
  clear Hqdef Hs Hdec Hcase.
  destruct (rem_eq_mod_nonneg__power_modexp (r * b) 1000000007 ltac:(nia) ltac:(lia)) as [Hrb _].
  destruct (rem_eq_mod_nonneg__power_modexp (b * b) 1000000007 ltac:(nia) ltac:(lia)) as [Hbb _].
  rewrite Hrb, Hbb.
  rewrite (Zmult_mod ((r * b) mod 1000000007) (((b * b) mod 1000000007) ^ q) 1000000007).
  rewrite (Zmod_mod (r * b) 1000000007).
  rewrite (pow_mod_square_step__power_modexp b 1000000007 q ltac:(lia) ltac:(lia)).
  rewrite <- (Zmult_mod (r * b) (b ^ (2 * q)) 1000000007).
  rewrite <- PreH11.
  f_equal.
  rewrite He.
  rewrite Z.pow_add_r by lia.
  rewrite Z.pow_1_r.
  ring.
Qed.

Lemma proof_of_power_entail_wit_2_1_split_goal_2 : power_entail_wit_2_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (shiftr_land1_decompose__power_modexp e ltac:(lia)) as [Hs [[Hq0 Hqe] [Hdec Hcase]]].
  lia.
Qed.

Lemma proof_of_power_entail_wit_2_1_split_goal_3 : power_entail_wit_2_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (shiftr_land1_decompose__power_modexp e ltac:(lia)) as [Hs [[Hq0 Hqe] [Hdec Hcase]]].
  lia.
Qed.

Lemma proof_of_power_entail_wit_2_1_split_goal_4 : power_entail_wit_2_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (rem_eq_mod_nonneg__power_modexp (r * b) 1000000007 ltac:(nia) ltac:(lia)) as [_ Hbnd].
  lia.
Qed.

Lemma proof_of_power_entail_wit_2_1_split_goal_5 : power_entail_wit_2_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (rem_eq_mod_nonneg__power_modexp (r * b) 1000000007 ltac:(nia) ltac:(lia)) as [_ Hbnd].
  lia.
Qed.

Lemma proof_of_power_entail_wit_2_1_split_goal_6 : power_entail_wit_2_1_split_goal_6.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (rem_eq_mod_nonneg__power_modexp (b * b) 1000000007 ltac:(nia) ltac:(lia)) as [_ Hbnd].
  lia.
Qed.

Lemma proof_of_power_entail_wit_2_1_split_goal_7 : power_entail_wit_2_1_split_goal_7.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (rem_eq_mod_nonneg__power_modexp (b * b) 1000000007 ltac:(nia) ltac:(lia)) as [_ Hbnd].
  lia.
Qed.

Lemma proof_of_power_entail_wit_2_1 : power_entail_wit_2_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_power_entail_wit_2_1_split_goal_1.
  - Goal_apply proof_of_power_entail_wit_2_1_split_goal_2.
  - Goal_apply proof_of_power_entail_wit_2_1_split_goal_3.
  - Goal_apply proof_of_power_entail_wit_2_1_split_goal_4.
  - Goal_apply proof_of_power_entail_wit_2_1_split_goal_5.
  - Goal_apply proof_of_power_entail_wit_2_1_split_goal_6.
  - Goal_apply proof_of_power_entail_wit_2_1_split_goal_7.
Qed.

Lemma proof_of_power_entail_wit_2_2_split_goal_1 : power_entail_wit_2_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold PowerLoopState in PreH11 |- *.
  destruct (shiftr_land1_decompose__power_modexp e ltac:(lia)) as [Hs [[Hq0 Hqe] [Hdec Hcase]]].
  assert (He : e = 2 * Z.shiftr e 1) by lia.
  remember (Z.shiftr e 1) as q eqn:Hqdef.
  clear Hqdef Hs Hdec Hcase.
  destruct (rem_eq_mod_nonneg__power_modexp (b * b) 1000000007 ltac:(nia) ltac:(lia)) as [Hbb _].
  rewrite Hbb.
  rewrite (Zmult_mod r (((b * b) mod 1000000007) ^ q) 1000000007).
  rewrite (pow_mod_square_step__power_modexp b 1000000007 q ltac:(lia) ltac:(lia)).
  rewrite <- (Zmult_mod r (b ^ (2 * q)) 1000000007).
  rewrite <- PreH11.
  f_equal.
  rewrite He.
  reflexivity.
Qed.

Lemma proof_of_power_entail_wit_2_2_split_goal_2 : power_entail_wit_2_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (shiftr_land1_decompose__power_modexp e ltac:(lia)) as [Hs [[Hq0 Hqe] [Hdec Hcase]]].
  lia.
Qed.

Lemma proof_of_power_entail_wit_2_2_split_goal_3 : power_entail_wit_2_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (shiftr_land1_decompose__power_modexp e ltac:(lia)) as [Hs [[Hq0 Hqe] [Hdec Hcase]]].
  lia.
Qed.

Lemma proof_of_power_entail_wit_2_2_split_goal_4 : power_entail_wit_2_2_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (rem_eq_mod_nonneg__power_modexp (b * b) 1000000007 ltac:(nia) ltac:(lia)) as [_ Hbnd].
  lia.
Qed.

Lemma proof_of_power_entail_wit_2_2_split_goal_5 : power_entail_wit_2_2_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  destruct (rem_eq_mod_nonneg__power_modexp (b * b) 1000000007 ltac:(nia) ltac:(lia)) as [_ Hbnd].
  lia.
Qed.

Lemma proof_of_power_entail_wit_2_2 : power_entail_wit_2_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_power_entail_wit_2_2_split_goal_1.
  - Goal_apply proof_of_power_entail_wit_2_2_split_goal_2.
  - Goal_apply proof_of_power_entail_wit_2_2_split_goal_3.
  - Goal_apply proof_of_power_entail_wit_2_2_split_goal_4.
  - Goal_apply proof_of_power_entail_wit_2_2_split_goal_5.
Qed.

Lemma proof_of_power_return_wit_1_split_goal_1 : power_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold ModPower.
  unfold PowerLoopState in PreH11.
  rewrite PreH12 in PreH11.
  rewrite Z.pow_0_r in PreH11.
  rewrite Z.mul_1_r in PreH11.
  rewrite (Z.mod_small r 1000000007) in PreH11 by lia.
  exact PreH11.
Qed.

Lemma proof_of_power_return_wit_1 : power_return_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_power_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_safety_wit_14_split_goal_1 : solver_safety_wit_14_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (rem_nonneg_bound__solver_arith_safety fact 1000000007 ltac:(lia) ltac:(lia)) as Hf.
  assert (Z.rem fact 1000000007 * retval <= 1000000006 * 1000000006) as Hb.
  { apply Z.mul_le_mono_nonneg; lia. }
  lia.
Qed.

Lemma proof_of_solver_safety_wit_14_split_goal_2 : solver_safety_wit_14_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (rem_nonneg_bound__solver_arith_safety fact 1000000007 ltac:(lia) ltac:(lia)) as Hf.
  assert (0 <= Z.rem fact 1000000007 * retval) as Hb.
  { apply Z.mul_nonneg_nonneg; lia. }
  lia.
Qed.

Lemma proof_of_solver_safety_wit_14 : solver_safety_wit_14.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_14_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_14_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_25_split_goal_1 : solver_safety_wit_25_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (PreH11 i ltac:(lia)) as Hi.
  pose proof (rem_nonneg_bound__solver_arith_safety (j - i) 1000000007 ltac:(lia) ltac:(lia)) as H1.
  pose proof (rem_nonneg_bound__solver_arith_safety (Znth i l1 0) 1000000007 ltac:(lia) ltac:(lia)) as H2.
  pose proof (rem_nonneg_bound__solver_arith_safety fact 1000000007 ltac:(lia) ltac:(lia)) as H3.
  assert (0 <= Z.rem (j - i) 1000000007 * Z.rem (Znth i l1 0) 1000000007) as Hp1.
  { apply Z.mul_nonneg_nonneg; lia. }
  assert (0 <= Z.rem fact 1000000007 * retval) as Hp2.
  { apply Z.mul_nonneg_nonneg; lia. }
  pose proof (rem_nonneg_bound__solver_arith_safety (Z.rem (j - i) 1000000007 * Z.rem (Znth i l1 0) 1000000007) 1000000007 ltac:(lia) ltac:(lia)) as HA.
  pose proof (rem_nonneg_bound__solver_arith_safety (Z.rem fact 1000000007 * retval) 1000000007 ltac:(lia) ltac:(lia)) as HB.
  assert (Z.rem (Z.rem (j - i) 1000000007 * Z.rem (Znth i l1 0) 1000000007) 1000000007
          * Z.rem (Z.rem fact 1000000007 * retval) 1000000007
          <= 1000000006 * 1000000006) as Hub.
  { apply Z.mul_le_mono_nonneg; lia. }
  lia.
Qed.

Lemma proof_of_solver_safety_wit_25_split_goal_2 : solver_safety_wit_25_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (PreH11 i ltac:(lia)) as Hi.
  pose proof (rem_nonneg_bound__solver_arith_safety (j - i) 1000000007 ltac:(lia) ltac:(lia)) as H1.
  pose proof (rem_nonneg_bound__solver_arith_safety (Znth i l1 0) 1000000007 ltac:(lia) ltac:(lia)) as H2.
  pose proof (rem_nonneg_bound__solver_arith_safety fact 1000000007 ltac:(lia) ltac:(lia)) as H3.
  assert (0 <= Z.rem (j - i) 1000000007 * Z.rem (Znth i l1 0) 1000000007) as Hp1.
  { apply Z.mul_nonneg_nonneg; lia. }
  assert (0 <= Z.rem fact 1000000007 * retval) as Hp2.
  { apply Z.mul_nonneg_nonneg; lia. }
  pose proof (rem_nonneg_bound__solver_arith_safety (Z.rem (j - i) 1000000007 * Z.rem (Znth i l1 0) 1000000007) 1000000007 ltac:(lia) ltac:(lia)) as HA.
  pose proof (rem_nonneg_bound__solver_arith_safety (Z.rem fact 1000000007 * retval) 1000000007 ltac:(lia) ltac:(lia)) as HB.
  assert (0 <= Z.rem (Z.rem (j - i) 1000000007 * Z.rem (Znth i l1 0) 1000000007) 1000000007
               * Z.rem (Z.rem fact 1000000007 * retval) 1000000007) as Hlb.
  { apply Z.mul_nonneg_nonneg; lia. }
  lia.
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
  dump_pre_spatial.
  pose proof (PreH11 i ltac:(lia)) as Hi.
  pose proof (rem_nonneg_bound__solver_arith_safety (j - i) 1000000007 ltac:(lia) ltac:(lia)) as H1.
  pose proof (rem_nonneg_bound__solver_arith_safety (Znth i l1 0) 1000000007 ltac:(lia) ltac:(lia)) as H2.
  pose proof (rem_nonneg_bound__solver_arith_safety fact 1000000007 ltac:(lia) ltac:(lia)) as H3.
  assert (0 <= Z.rem (j - i) 1000000007 * Z.rem (Znth i l1 0) 1000000007) as Hp1.
  { apply Z.mul_nonneg_nonneg; lia. }
  assert (0 <= Z.rem fact 1000000007 * retval) as Hp2.
  { apply Z.mul_nonneg_nonneg; lia. }
  pose proof (rem_nonneg_bound__solver_arith_safety (Z.rem (j - i) 1000000007 * Z.rem (Znth i l1 0) 1000000007) 1000000007 ltac:(lia) ltac:(lia)) as HA.
  pose proof (rem_nonneg_bound__solver_arith_safety (Z.rem fact 1000000007 * retval) 1000000007 ltac:(lia) ltac:(lia)) as HB.
  assert (Z.rem (Z.rem (j - i) 1000000007 * Z.rem (Znth i l1 0) 1000000007) 1000000007
          * Z.rem (Z.rem fact 1000000007 * retval) 1000000007
          <= 1000000006 * 1000000006) as Hub.
  { apply Z.mul_le_mono_nonneg; lia. }
  lia.
Qed.

Lemma proof_of_solver_safety_wit_26_split_goal_2 : solver_safety_wit_26_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (PreH11 i ltac:(lia)) as Hi.
  pose proof (rem_nonneg_bound__solver_arith_safety (j - i) 1000000007 ltac:(lia) ltac:(lia)) as H1.
  pose proof (rem_nonneg_bound__solver_arith_safety (Znth i l1 0) 1000000007 ltac:(lia) ltac:(lia)) as H2.
  pose proof (rem_nonneg_bound__solver_arith_safety fact 1000000007 ltac:(lia) ltac:(lia)) as H3.
  assert (0 <= Z.rem (j - i) 1000000007 * Z.rem (Znth i l1 0) 1000000007) as Hp1.
  { apply Z.mul_nonneg_nonneg; lia. }
  assert (0 <= Z.rem fact 1000000007 * retval) as Hp2.
  { apply Z.mul_nonneg_nonneg; lia. }
  pose proof (rem_nonneg_bound__solver_arith_safety (Z.rem (j - i) 1000000007 * Z.rem (Znth i l1 0) 1000000007) 1000000007 ltac:(lia) ltac:(lia)) as HA.
  pose proof (rem_nonneg_bound__solver_arith_safety (Z.rem fact 1000000007 * retval) 1000000007 ltac:(lia) ltac:(lia)) as HB.
  assert (0 <= Z.rem (Z.rem (j - i) 1000000007 * Z.rem (Znth i l1 0) 1000000007) 1000000007
               * Z.rem (Z.rem fact 1000000007 * retval) 1000000007) as Hlb.
  { apply Z.mul_nonneg_nonneg; lia. }
  lia.
Qed.

Lemma proof_of_solver_safety_wit_26 : solver_safety_wit_26.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_26_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_26_split_goal_2.
Qed.

Lemma proof_of_solver_safety_wit_28_split_goal_1 : solver_safety_wit_28_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (PreH11 i ltac:(lia)) as Hi.
  pose proof (rem_nonneg_bound__solver_arith_safety (j - i) 1000000007 ltac:(lia) ltac:(lia)) as H1.
  pose proof (rem_nonneg_bound__solver_arith_safety (Znth i l1 0) 1000000007 ltac:(lia) ltac:(lia)) as H2.
  assert (Z.rem (j - i) 1000000007 * Z.rem (Znth i l1 0) 1000000007
          <= 1000000006 * 1000000006) as Hub.
  { apply Z.mul_le_mono_nonneg; lia. }
  lia.
Qed.

Lemma proof_of_solver_safety_wit_28_split_goal_2 : solver_safety_wit_28_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (PreH11 i ltac:(lia)) as Hi.
  pose proof (rem_nonneg_bound__solver_arith_safety (j - i) 1000000007 ltac:(lia) ltac:(lia)) as H1.
  pose proof (rem_nonneg_bound__solver_arith_safety (Znth i l1 0) 1000000007 ltac:(lia) ltac:(lia)) as H2.
  assert (0 <= Z.rem (j - i) 1000000007 * Z.rem (Znth i l1 0) 1000000007) as Hlb.
  { apply Z.mul_nonneg_nonneg; lia. }
  lia.
Qed.

Lemma proof_of_solver_safety_wit_28 : solver_safety_wit_28.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_safety_wit_28_split_goal_1.
  - Goal_apply proof_of_solver_safety_wit_28_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (znth_bounds_perm_transfer__solver_loop_setup values l1_2 n_pre 1 1000000000
                PreH1 (eq_sym PreH6) PreH5) as [Hlen Hb].
  apply Hb. exact H.
Qed.

Lemma proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  pose proof (znth_bounds_perm_transfer__solver_loop_setup values l1_2 n_pre 1 1000000000
                PreH1 (eq_sym PreH6) PreH5) as [Hlen Hb].
  exact Hlen.
Qed.

Lemma proof_of_solver_entail_wit_1 : solver_entail_wit_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_1_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH5. exact H.
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
  unfold FactorialModState in *.
  rewrite rem_eq_mod_nonneg__solver_loop_setup by nia.
  replace (i + 1 - 1) with i by lia.
  rewrite PreH13.
  rewrite Zmult_mod_idemp_l.
  rewrite (zfact_succ_step__solver_loop_setup i) by lia.
  f_equal. lia.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_2 : solver_entail_wit_3_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite rem_eq_mod_nonneg__solver_loop_setup by nia.
  pose proof (Z.mod_pos_bound (fact * i) 1000000007 ltac:(lia)) as Hb.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_3_split_goal_3 : solver_entail_wit_3_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  rewrite rem_eq_mod_nonneg__solver_loop_setup by nia.
  pose proof (Z.mod_pos_bound (fact * i) 1000000007 ltac:(lia)) as Hb.
  lia.
Qed.

Lemma proof_of_solver_entail_wit_3 : solver_entail_wit_3.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_3_split_goal_3.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_2 : solver_entail_wit_4_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold GroupBoundary. left. reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_3 : solver_entail_wit_4_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (n_pre + 1) with i by lia. exact PreH13.
Qed.

Lemma proof_of_solver_entail_wit_4_split_goal_4 : solver_entail_wit_4_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH6. exact H.
Qed.

Lemma proof_of_solver_entail_wit_4 : solver_entail_wit_4.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_4_split_goal_4.
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
Qed.

Lemma proof_of_solver_entail_wit_5_split_goal_2 : solver_entail_wit_5_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH6. exact H.
Qed.

Lemma proof_of_solver_entail_wit_5 : solver_entail_wit_5.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_5_split_goal_2.
Qed.

Lemma proof_of_solver_entail_wit_7_1_split_goal_1 : solver_entail_wit_7_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold ContribPrefixSum in *.
  unfold FactorialModState in PreH21.
  replace (n_pre + 1 - 1) with n_pre in PreH21 by lia.
  replace (j - 1 + 1) with j by lia.
  assert (Hv : 1 <= Znth i l1_2 0 <= 1000000000) by (apply PreH11; lia).
  assert (Hij : i < j).
  { assert (i <> j) by (intro Heq; apply PreH5; rewrite Heq; reflexivity). lia. }
  assert (Hle : Znth i l1_2 0 <= Znth j l1_2 0) by (apply PreH13; lia).
  assert (Hguard : existsb (fun w => Z.ltb (Znth i l1_2 0) w) l1_2 = true).
  { apply existsb_exists. exists (Znth j l1_2 0). split.
    - apply Znth_In__group_contribution_step. lia.
    - apply Z.ltb_lt. lia. }
  assert (Hcount : count_ge l1_2 (Znth i l1_2 0) = n_pre - i).
  { pose proof (count_ge_sorted_group__group_contribution_step l1_2 i
                  PreH13 PreH24 ltac:(lia)) as Hc. lia. }
  assert (Hcontrib : contrib l1_2 (Znth i l1_2 0)
                   = Znth i l1_2 0 * (Zfact n_pre / (n_pre - i))).
  { unfold contrib. rewrite Hguard, Hcount, PreH10. reflexivity. }
  assert (Hext : fold_right Z.add 0 (sublist 0 j (contrib_list l1_2))
               = fold_right Z.add 0 (sublist 0 i (contrib_list l1_2))
                 + (j - i) * contrib l1_2 (Znth i l1_2 0)).
  { apply contrib_prefix_extend__group_contribution_step;
      [ lia | lia | exact PreH18 ]. }
  assert (Hquot : (Zfact n_pre / (n_pre - i)) mod 1000000007
                = (fact * retval) mod 1000000007).
  { assert (Hrem1 : Z.rem (n_pre - i) 1000000007 = n_pre - i)
      by (rewrite Z.rem_mod_nonneg by lia; apply Z.mod_small; lia).
    assert (Hb1 : 0 < n_pre - i <= n_pre) by lia.
    assert (Hb2 : n_pre <= 1000000) by lia.
    unfold ModPower in PreH3.
    rewrite Hrem1 in PreH3.
    pose proof (exact_quotient_mod_inverse__group_contribution_step
                  n_pre (n_pre - i) Hb1 Hb2) as [_ Heq].
    rewrite Heq, <- PreH21, <- PreH3. reflexivity. }
  assert (Rji : Z.rem (j - i) 1000000007 = j - i)
    by (rewrite Z.rem_mod_nonneg by lia; apply Z.mod_small; lia).
  assert (Rv : Z.rem (Znth i l1_2 0) 1000000007 = Znth i l1_2 0)
    by (rewrite Z.rem_mod_nonneg by lia; apply Z.mod_small; lia).
  assert (Rf : Z.rem fact 1000000007 = fact)
    by (rewrite Z.rem_mod_nonneg by lia; apply Z.mod_small; lia).
  rewrite Rji, Rv, Rf.
  assert (RA : Z.rem ((j - i) * Znth i l1_2 0) 1000000007
             = ((j - i) * Znth i l1_2 0) mod 1000000007)
    by (apply Z.rem_mod_nonneg; [nia | lia]).
  assert (RB : Z.rem (fact * retval) 1000000007
             = (fact * retval) mod 1000000007)
    by (apply Z.rem_mod_nonneg; [nia | lia]).
  rewrite RA, RB.
  assert (RO : Z.rem (total + ((j - i) * Znth i l1_2 0) mod 1000000007
                              * ((fact * retval) mod 1000000007)) 1000000007
             = (total + ((j - i) * Znth i l1_2 0) mod 1000000007
                              * ((fact * retval) mod 1000000007))
               mod 1000000007).
  { apply Z.rem_mod_nonneg; [| lia].
    pose proof (Z.mod_pos_bound ((j - i) * Znth i l1_2 0) 1000000007
                  ltac:(lia)).
    pose proof (Z.mod_pos_bound (fact * retval) 1000000007 ltac:(lia)).
    nia. }
  rewrite RO.
  rewrite Hext, Hcontrib, PreH25.
  rewrite Zplus_mod_idemp_l.
  assert (Hcore : (((j - i) * Znth i l1_2 0) mod 1000000007
                   * ((fact * retval) mod 1000000007)) mod 1000000007
                = ((j - i) * (Znth i l1_2 0 * (Zfact n_pre / (n_pre - i))))
                  mod 1000000007).
  { rewrite <- Hquot, <- Zmult_mod. f_equal. symmetry. apply Z.mul_assoc. }
  rewrite Zplus_mod, Hcore, <- Zplus_mod.
  reflexivity.
Qed.

Lemma proof_of_solver_entail_wit_7_1_split_goal_2 : solver_entail_wit_7_1_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (j - 1 + 1) with j by lia.
  assert (Hij : i < j).
  { assert (i <> j) by (intro Heq; apply PreH5; rewrite Heq; reflexivity). lia. }
  assert (Hprev : Znth (j - 1) l1_2 0 = Znth i l1_2 0) by (apply PreH18; lia).
  assert (Hle : Znth i l1_2 0 <= Znth j l1_2 0) by (apply PreH13; lia).
  unfold GroupBoundary. right. right.
  split; [lia | rewrite Hprev; lia].
Qed.

Lemma proof_of_solver_entail_wit_7_1_split_goal_3 : solver_entail_wit_7_1_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hv : 1 <= Znth i l1_2 0 <= 1000000000) by (apply PreH11; lia).
  pose proof (rem_eq_mod_nonneg__group_contribution_step (j - i) 1000000007
                ltac:(lia) ltac:(lia)) as [_ R1].
  pose proof (rem_eq_mod_nonneg__group_contribution_step (Znth i l1_2 0) 1000000007
                ltac:(lia) ltac:(lia)) as [_ R2].
  pose proof (rem_eq_mod_nonneg__group_contribution_step
                (Z.rem (j - i) 1000000007 * Z.rem (Znth i l1_2 0) 1000000007)
                1000000007 ltac:(nia) ltac:(lia)) as [_ R3].
  pose proof (rem_eq_mod_nonneg__group_contribution_step fact 1000000007
                ltac:(lia) ltac:(lia)) as [_ R4].
  pose proof (rem_eq_mod_nonneg__group_contribution_step
                (Z.rem fact 1000000007 * retval)
                1000000007 ltac:(nia) ltac:(lia)) as [_ R5].
  pose proof (rem_eq_mod_nonneg__group_contribution_step
                (total
                 + Z.rem (Z.rem (j - i) 1000000007
                          * Z.rem (Znth i l1_2 0) 1000000007) 1000000007
                   * Z.rem (Z.rem fact 1000000007 * retval) 1000000007)
                1000000007 ltac:(nia) ltac:(lia)) as [_ R6].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_7_1_split_goal_4 : solver_entail_wit_7_1_split_goal_4.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  assert (Hv : 1 <= Znth i l1_2 0 <= 1000000000) by (apply PreH11; lia).
  pose proof (rem_eq_mod_nonneg__group_contribution_step (j - i) 1000000007
                ltac:(lia) ltac:(lia)) as [_ R1].
  pose proof (rem_eq_mod_nonneg__group_contribution_step (Znth i l1_2 0) 1000000007
                ltac:(lia) ltac:(lia)) as [_ R2].
  pose proof (rem_eq_mod_nonneg__group_contribution_step
                (Z.rem (j - i) 1000000007 * Z.rem (Znth i l1_2 0) 1000000007)
                1000000007 ltac:(nia) ltac:(lia)) as [_ R3].
  pose proof (rem_eq_mod_nonneg__group_contribution_step fact 1000000007
                ltac:(lia) ltac:(lia)) as [_ R4].
  pose proof (rem_eq_mod_nonneg__group_contribution_step
                (Z.rem fact 1000000007 * retval)
                1000000007 ltac:(nia) ltac:(lia)) as [_ R5].
  pose proof (rem_eq_mod_nonneg__group_contribution_step
                (total
                 + Z.rem (Z.rem (j - i) 1000000007
                          * Z.rem (Znth i l1_2 0) 1000000007) 1000000007
                   * Z.rem (Z.rem fact 1000000007 * retval) 1000000007)
                1000000007 ltac:(nia) ltac:(lia)) as [_ R6].
  lia.
Qed.

Lemma proof_of_solver_entail_wit_7_1_split_goal_5 : solver_entail_wit_7_1_split_goal_5.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH11. exact H.
Qed.

Lemma proof_of_solver_entail_wit_7_1 : solver_entail_wit_7_1.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_7_1_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_7_1_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_7_1_split_goal_3.
  - Goal_apply proof_of_solver_entail_wit_7_1_split_goal_4.
  - Goal_apply proof_of_solver_entail_wit_7_1_split_goal_5.
Qed. 

Lemma proof_of_solver_entail_wit_7_2_split_goal_1 : solver_entail_wit_7_2_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  unfold ContribPrefixSum in *.
  replace (j - 1 + 1) with j by lia.
  assert (Hzero : contrib l1_2 (Znth i l1_2 0) = 0).
  { apply contrib_zero_on_max_group__group_contribution_step;
      [ exact PreH9 | lia | ].
    intros q Hq. apply PreH14. lia. }
  rewrite (contrib_prefix_extend__group_contribution_step l1_2 i j
             ltac:(lia) ltac:(lia) PreH14).
  rewrite Hzero, Z.mul_0_r, Z.add_0_r.
  exact PreH21.
Qed.

Lemma proof_of_solver_entail_wit_7_2_split_goal_2 : solver_entail_wit_7_2_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  replace (j - 1 + 1) with j by lia.
  unfold GroupBoundary. right. left. lia.
Qed.

Lemma proof_of_solver_entail_wit_7_2_split_goal_3 : solver_entail_wit_7_2_split_goal_3.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply PreH7. exact H.
Qed.

Lemma proof_of_solver_entail_wit_7_2 : solver_entail_wit_7_2.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_entail_wit_7_2_split_goal_1.
  - Goal_apply proof_of_solver_entail_wit_7_2_split_goal_2.
  - Goal_apply proof_of_solver_entail_wit_7_2_split_goal_3.
Qed. 

Lemma proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  apply (spec_of_contrib_prefix__spec_final_result values l1 i total).
  - lia.
  - assumption.
  - lia.
  - assumption.
Qed.

Lemma proof_of_solver_return_wit_1 : solver_return_wit_1.
Proof.
  aggressive_pre_process.
  Goal_apply proof_of_solver_return_wit_1_split_goal_1.
Qed.

Lemma proof_of_solver_partial_solve_wit_4_pure_split_goal_1 : solver_partial_solve_wit_4_pure_split_goal_1.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (rem_nonneg_bound__solver_arith_safety (n_pre - i) 1000000007 ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_4_pure_split_goal_2 : solver_partial_solve_wit_4_pure_split_goal_2.
Proof.
  LLM_pre_process ltac:(lia || nia || int_auto).
  dump_pre_spatial.
  pose proof (rem_nonneg_bound__solver_arith_safety (n_pre - i) 1000000007 ltac:(lia) ltac:(lia)).
  lia.
Qed.

Lemma proof_of_solver_partial_solve_wit_4_pure : solver_partial_solve_wit_4_pure.
Proof.
  aggressive_pre_process.
  - Goal_apply proof_of_solver_partial_solve_wit_4_pure_split_goal_1.
  - Goal_apply proof_of_solver_partial_solve_wit_4_pure_split_goal_2.
Qed.

