import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_manual_powmod_gcd
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_goal SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
local infixl:70 " /ᶻ " => Z.div
local infixl:70 " mod " => Z.modulo

theorem p090_rem_mod (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) : Z.rem a b = a mod b :=
  (Int.fmod_eq_tmod_of_nonneg ha hb).symm

theorem p090_quot_div (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) : Z.quot a b = a /ᶻ b := by
  change a.tdiv b = a.fdiv b
  rw [Int.tdiv_eq_ediv_of_nonneg ha,Int.fdiv_eq_ediv_of_nonneg a hb]

theorem proof_of_order_entail_wit_1_split_goal_1 : order_entail_wit_1_split_goal_1 := by
  intro phi_pre modulus_pre x_pre phi0 modulus0 x0 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  apply order_trial_init_ex
  simpa only [PreH2,PreH3,PreH4] using PreH6

theorem proof_of_order_entail_wit_1_split_goal_2 : order_entail_wit_1_split_goal_2 := by
  intro phi_pre modulus_pre x_pre phi0 modulus0 x0 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  have h := PreH6.2.2.2.1
  have hm := PreH6.1
  omega

theorem proof_of_order_entail_wit_1_split_goal_3 : order_entail_wit_1_split_goal_3 := by
  intro phi_pre modulus_pre x_pre phi0 modulus0 x0 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  have h := PreH6.2.2.2.1
  have hm := PreH6.1
  omega

theorem proof_of_order_entail_wit_1_split_goal_4 : order_entail_wit_1_split_goal_4 := by
  intro phi_pre modulus_pre x_pre phi0 modulus0 x0 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  have h := PreH6.2.2.2.1
  have hm := PreH6.1
  omega

theorem proof_of_order_entail_wit_1 : order_entail_wit_1 := by
  unfold order_entail_wit_1
  right
  intro phi_pre modulus_pre x_pre phi0 modulus0 x0 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_order_entail_wit_1_split_goal_1 phi_pre modulus_pre x_pre phi0 modulus0 x0 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
    | exact proof_of_order_entail_wit_1_split_goal_2 phi_pre modulus_pre x_pre phi0 modulus0 x0 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
    | exact proof_of_order_entail_wit_1_split_goal_3 phi_pre modulus_pre x_pre phi0 modulus0 x0 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
    | exact proof_of_order_entail_wit_1_split_goal_4 phi_pre modulus_pre x_pre phi0 modulus0 x0 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6

theorem proof_of_order_entail_wit_2_split_goal_1 : order_entail_wit_2_split_goal_1 := by
  intro phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  exact order_trial_enter_factor_ex x_pre modulus_pre phi_pre q t ord (by omega) PreH14
    (by rw [← p090_rem_mod t q (by omega) (by omega)]; exact PreH1)

theorem proof_of_order_entail_wit_2_split_goal_2 : order_entail_wit_2_split_goal_2 := by
  intro phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  have hphi := PreH14.1.2.2.2.1.2
  nlinarith

theorem proof_of_order_entail_wit_2 : order_entail_wit_2 := by
  unfold order_entail_wit_2
  right
  intro phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_order_entail_wit_2_split_goal_1 phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
    | exact proof_of_order_entail_wit_2_split_goal_2 phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14

theorem proof_of_order_entail_wit_3_split_goal_1 : order_entail_wit_3_split_goal_1 := by
  intro phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  rw [p090_quot_div t q (by omega) (by omega)]
  exact order_factor_step_div_ex x_pre modulus_pre phi_pre q t ord PreH13
    (by rw [← p090_rem_mod t q (by omega) (by omega)]; exact PreH1)

theorem proof_of_order_entail_wit_3_split_goal_2 : order_entail_wit_3_split_goal_2 := by
  intro phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hs := proof_of_order_entail_wit_3_split_goal_1 phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  exact hs.2.2.2.1

theorem proof_of_order_entail_wit_3_split_goal_3 : order_entail_wit_3_split_goal_3 := by
  intro phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have hs := proof_of_order_entail_wit_3_split_goal_1 phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  exact hs.2.2.1

theorem proof_of_order_entail_wit_3 : order_entail_wit_3 := by
  unfold order_entail_wit_3
  right
  intro phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_order_entail_wit_3_split_goal_1 phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
    | exact proof_of_order_entail_wit_3_split_goal_2 phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
    | exact proof_of_order_entail_wit_3_split_goal_3 phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13

theorem proof_of_order_entail_wit_4_split_goal_1 : order_entail_wit_4_split_goal_1 := by
  intro phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  apply order_factor_completed_ex
  · assumption
  · rw [← p090_rem_mod t q (by omega) (by omega)]
    exact PreH1

theorem proof_of_order_entail_wit_4 : order_entail_wit_4 := by
  unfold order_entail_wit_4
  right
  intro phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_order_entail_wit_4_split_goal_1 phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13

theorem proof_of_order_entail_wit_5_split_goal_1 : order_entail_wit_5_split_goal_1 := by
  intro phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hquot := p090_quot_div ord q (by omega) (by omega)
  rw [hquot] at PreH2 ⊢
  have hmod : ord mod q = 0 := by rw [← p090_rem_mod ord q (by omega) (by omega)]; exact PreH5
  have hpow : Z.pow x_pre (ord /ᶻ q) mod modulus_pre = 1 :=
    rem_one_implies_mod_one__order_entry_and_factorization _ _ (by omega) (PreH2.symm.trans PreH1)
  exact order_strip_step_div_ex x_pre modulus_pre phi_pre q t ord PreH17 hmod hpow

theorem proof_of_order_entail_wit_5_split_goal_2 : order_entail_wit_5_split_goal_2 := by
  intro phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hs := proof_of_order_entail_wit_5_split_goal_1 phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  obtain ⟨excess,hcore,_⟩ := hs.1.2.2.2.2.2.2
  exact hcore.2.2.1

theorem proof_of_order_entail_wit_5_split_goal_3 : order_entail_wit_5_split_goal_3 := by
  intro phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hs := proof_of_order_entail_wit_5_split_goal_1 phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  obtain ⟨excess,hcore,_⟩ := hs.1.2.2.2.2.2.2
  exact hcore.2.1

theorem proof_of_order_entail_wit_5 : order_entail_wit_5 := by
  unfold order_entail_wit_5
  right
  intro phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_order_entail_wit_5_split_goal_1 phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
    | exact proof_of_order_entail_wit_5_split_goal_2 phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
    | exact proof_of_order_entail_wit_5_split_goal_3 phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17

theorem proof_of_order_entail_wit_6_1_split_goal_1 : order_entail_wit_6_1_split_goal_1 := by
  intro phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  apply order_strip_exit_mod_ex
  · assumption
  · rw [← p090_rem_mod ord q (by omega) (by omega)]
    exact PreH1

theorem proof_of_order_entail_wit_6_1 : order_entail_wit_6_1 := by
  unfold order_entail_wit_6_1
  right
  intro phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_order_entail_wit_6_1_split_goal_1 phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13

theorem proof_of_order_entail_wit_6_2_split_goal_1 : order_entail_wit_6_2_split_goal_1 := by
  intro phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have hquot := p090_quot_div ord q (by omega) (by omega)
  rw [hquot] at PreH2
  have hmod : ord mod q = 0 := by rw [← p090_rem_mod ord q (by omega) (by omega)]; exact PreH5
  have hpowrem : Z.rem (Z.pow x_pre (ord /ᶻ q)) modulus_pre = Z.pow x_pre (ord /ᶻ q) mod modulus_pre :=
    rem_eq_mod_of_nonnegative_remainder__order_strip_and_exits _ _ (by omega) (by exact PreH2 ▸ PreH3)
  exact order_strip_exit_power_ex x_pre modulus_pre phi_pre q t ord retval PreH17 hmod (PreH2.trans hpowrem) PreH1

theorem proof_of_order_entail_wit_6_2 : order_entail_wit_6_2 := by
  unfold order_entail_wit_6_2
  right
  intro phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_order_entail_wit_6_2_split_goal_1 phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17

theorem proof_of_order_entail_wit_6_3_split_goal_1 : order_entail_wit_6_3_split_goal_1 := by
  intro phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  apply order_trial_skip_ex
  · assumption
  · rw [← p090_rem_mod t q (by omega) (by omega)]
    exact PreH1

theorem proof_of_order_entail_wit_6_3_split_goal_2 : order_entail_wit_6_3_split_goal_2 := by
  intro phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  have hphi := PreH14.1.2.2.2.1.2
  nlinarith

theorem proof_of_order_entail_wit_6_3 : order_entail_wit_6_3 := by
  unfold order_entail_wit_6_3
  right
  intro phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_order_entail_wit_6_3_split_goal_1 phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
    | exact proof_of_order_entail_wit_6_3_split_goal_2 phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14

theorem proof_of_order_entail_wit_7_split_goal_1 : order_entail_wit_7_split_goal_1 := by
  intro phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  exact order_trial_enter_final_ex x_pre modulus_pre phi_pre q t ord (by omega) (by omega) (by omega) PreH14

theorem proof_of_order_entail_wit_7 : order_entail_wit_7 := by
  unfold order_entail_wit_7
  right
  intro phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_order_entail_wit_7_split_goal_1 phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14

theorem proof_of_order_entail_wit_8_split_goal_1 : order_entail_wit_8_split_goal_1 := by
  intro phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have hquot := p090_quot_div ord t (by omega) (by omega)
  rw [hquot] at PreH2 ⊢
  have hmod : ord mod t = 0 := by rw [← p090_rem_mod ord t (by omega) (by omega)]; exact PreH5
  have hpow : Z.pow x_pre (ord /ᶻ t) mod modulus_pre = 1 :=
    rem_one_implies_mod_one__order_entry_and_factorization _ _ (by omega) (PreH2.symm.trans PreH1)
  exact order_final_step_div_ex x_pre modulus_pre phi_pre t ord PreH15 hmod hpow

theorem proof_of_order_entail_wit_8_split_goal_2 : order_entail_wit_8_split_goal_2 := by
  intro phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have hs := proof_of_order_entail_wit_8_split_goal_1 phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  obtain ⟨excess,hcore,_⟩ := hs.2.2
  exact hcore.2.2.1

theorem proof_of_order_entail_wit_8_split_goal_3 : order_entail_wit_8_split_goal_3 := by
  intro phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have hs := proof_of_order_entail_wit_8_split_goal_1 phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  obtain ⟨excess,hcore,_⟩ := hs.2.2
  exact hcore.2.1

theorem proof_of_order_entail_wit_8 : order_entail_wit_8 := by
  unfold order_entail_wit_8
  right
  intro phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_order_entail_wit_8_split_goal_1 phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
    | exact proof_of_order_entail_wit_8_split_goal_2 phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
    | exact proof_of_order_entail_wit_8_split_goal_3 phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15

theorem proof_of_order_return_wit_1_split_goal_1 : order_return_wit_1_split_goal_1 := by
  intro phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  exact order_final_exit_mod_ex x_pre modulus_pre phi_pre t ord PreH11
    (by rw [← p090_rem_mod ord t (by omega) (by omega)]; exact PreH1)

theorem proof_of_order_return_wit_1 : order_return_wit_1 := by
  unfold order_return_wit_1
  right
  intro phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_order_return_wit_1_split_goal_1 phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11

theorem proof_of_order_return_wit_2_split_goal_1 : order_return_wit_2_split_goal_1 := by
  intro phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have hquot := p090_quot_div ord t (by omega) (by omega)
  rw [hquot] at PreH2
  have hmod : ord mod t = 0 := by rw [← p090_rem_mod ord t (by omega) (by omega)]; exact PreH5
  have hpowrem : Z.rem (Z.pow x_pre (ord /ᶻ t)) modulus_pre = Z.pow x_pre (ord /ᶻ t) mod modulus_pre :=
    rem_eq_mod_of_nonnegative_remainder__order_strip_and_exits _ _ (by omega) (by exact PreH2 ▸ PreH3)
  exact order_final_exit_power_guard_ex x_pre modulus_pre phi_pre t ord retval PreH15 hmod (PreH2.trans hpowrem) PreH1

theorem proof_of_order_return_wit_2 : order_return_wit_2 := by
  unfold order_return_wit_2
  right
  intro phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_order_return_wit_2_split_goal_1 phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15

theorem proof_of_order_return_wit_3_split_goal_1 : order_return_wit_3_split_goal_1 := by
  intro phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  exact order_trial_exit_bounded_ex x_pre modulus_pre phi_pre q t ord PreH14 (by omega) (by omega)

theorem proof_of_order_return_wit_3 : order_return_wit_3 := by
  unfold order_return_wit_3
  right
  intro phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_order_return_wit_3_split_goal_1 phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14

theorem proof_of_order_return_wit_4_split_goal_1 : order_return_wit_4_split_goal_1 := by
  intro phi_pre modulus_pre x_pre phi0 modulus0 x0 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  have hm := PreH6.1
  omega

theorem proof_of_order_return_wit_4 : order_return_wit_4 := by
  unfold order_return_wit_4
  right
  intro phi_pre modulus_pre x_pre phi0 modulus0 x0 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_order_return_wit_4_split_goal_1 phi_pre modulus_pre x_pre phi0 modulus0 x0 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6

theorem proof_of_order_partial_solve_wit_1_pure_split_goal_1 : order_partial_solve_wit_1_pure_split_goal_1 := by
  intro phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  dump_pre_spatial
  rw [p090_quot_div ord q (by omega) (by omega)]
  have hq0 : 0 ≤ ord /ᶻ q := Int.fdiv_nonneg (by omega) (by omega)
  have hqle : ord /ᶻ q ≤ ord := by
    change ord.fdiv q ≤ ord
    rw [Int.fdiv_eq_ediv_of_nonneg ord (by omega)]
    exact Int.ediv_le_self q (by omega)
  have hphi := PreH25.1.1.2.2.2.1.2
  omega

theorem proof_of_order_partial_solve_wit_1_pure_split_goal_2 : order_partial_solve_wit_1_pure_split_goal_2 := by
  intro phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  dump_pre_spatial
  rw [p090_quot_div ord q (by omega) (by omega)]
  have hq0 : 0 ≤ ord /ᶻ q := Int.fdiv_nonneg (by omega) (by omega)
  have hqle : ord /ᶻ q ≤ ord := by
    change ord.fdiv q ≤ ord
    rw [Int.fdiv_eq_ediv_of_nonneg ord (by omega)]
    exact Int.ediv_le_self q (by omega)
  have hphi := PreH25.1.1.2.2.2.1.2
  omega

theorem proof_of_order_partial_solve_wit_1_pure : order_partial_solve_wit_1_pure := by
  unfold order_partial_solve_wit_1_pure
  right
  intro phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pures <;> first
    | exact proof_of_order_partial_solve_wit_1_pure_split_goal_1 phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
    | exact proof_of_order_partial_solve_wit_1_pure_split_goal_2 phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t q PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_order_partial_solve_wit_2_pure_split_goal_1 : order_partial_solve_wit_2_pure_split_goal_1 := by
  intro phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  dump_pre_spatial
  rw [p090_quot_div ord t (by omega) (by omega)]
  have hq0 : 0 ≤ ord /ᶻ t := Int.fdiv_nonneg (by omega) (by omega)
  have hqle : ord /ᶻ t ≤ ord := by
    change ord.fdiv t ≤ ord
    rw [Int.fdiv_eq_ediv_of_nonneg ord (by omega)]
    exact Int.ediv_le_self t (by omega)
  have hphi := PreH21.1.2.2.2.1.2
  omega

theorem proof_of_order_partial_solve_wit_2_pure_split_goal_2 : order_partial_solve_wit_2_pure_split_goal_2 := by
  intro phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  dump_pre_spatial
  rw [p090_quot_div ord t (by omega) (by omega)]
  have hq0 : 0 ≤ ord /ᶻ t := Int.fdiv_nonneg (by omega) (by omega)
  have hqle : ord /ᶻ t ≤ ord := by
    change ord.fdiv t ≤ ord
    rw [Int.fdiv_eq_ediv_of_nonneg ord (by omega)]
    exact Int.ediv_le_self t (by omega)
  have hphi := PreH21.1.2.2.2.1.2
  omega

theorem proof_of_order_partial_solve_wit_2_pure : order_partial_solve_wit_2_pure := by
  unfold order_partial_solve_wit_2_pure
  right
  intro phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  split_pures <;> first
    | exact proof_of_order_partial_solve_wit_2_pure_split_goal_1 phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
    | exact proof_of_order_partial_solve_wit_2_pure_split_goal_2 phi_pre modulus_pre x_pre phi0 modulus0 x0 ord t PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_proof_manual
