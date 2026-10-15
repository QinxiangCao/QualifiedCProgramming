import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_manual_order
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

theorem p090_exponent_lt_pow (p e : Int) (hp : 2 ≤ p) (he : 0 ≤ e) : e < Z.pow p e := by
  have hpn : (p.toNat : Int) = p := Int.toNat_of_nonneg (by omega)
  have hen : (e.toNat : Int) = e := Int.toNat_of_nonneg he
  have h := Nat.lt_pow_self (n := e.toNat) (a := p.toNat) (by omega)
  have hcast : (e.toNat : Int) < (p.toNat : Int)^e.toNat := by exact_mod_cast h
  simpa only [hpn,hen,coq_pow_nat p e he] using hcast

theorem proof_of_walk_safety_wit_10_split_goal_1 : walk_safety_wit_10_split_goal_1 := by
  intro ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current e p ph pk PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  dump_pre_spatial
  have h := PreH8.2.2.1
  omega

theorem proof_of_walk_safety_wit_10 : walk_safety_wit_10 := by
  unfold walk_safety_wit_10
  right
  intro ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current e p ph pk PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  split_pures <;> first
  | exact proof_of_walk_safety_wit_10_split_goal_1 ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current e p ph pk PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15


theorem proof_of_walk_entail_wit_1_split_goal_1 : walk_entail_wit_1_split_goal_1 := by
  intro ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  exact incoming_walk_suffix_zero_call_budget m pr_values pe_values x_value i_pre d_pre before PreH9 (by omega) PreH11

theorem proof_of_walk_entail_wit_1_split_goal_2 : walk_entail_wit_1_split_goal_2 := by
  intro ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  exact prefix_choice_zero_extend m pr_values pe_values x_value i_pre d_pre phi_pre ord_pre PreH9 PreH10 (by omega)

theorem proof_of_walk_entail_wit_1 : walk_entail_wit_1 := by
  unfold walk_entail_wit_1
  right
  intro ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_walk_entail_wit_1_split_goal_1 ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
    | exact proof_of_walk_entail_wit_1_split_goal_2 ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11


theorem proof_of_walk_entail_wit_2_split_goal_1 : walk_entail_wit_2_split_goal_1 := by
  intro ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  exact walk_pending_after_zero m pr_values pe_values x_value i_pre d_pre before _ PreH8 (by omega) PreH11 rfl

theorem proof_of_walk_entail_wit_2 : walk_entail_wit_2 := by
  unfold walk_entail_wit_2
  right
  intro ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_walk_entail_wit_2_split_goal_1 ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12


theorem proof_of_walk_entail_wit_3_split_goal_1 : walk_entail_wit_3_split_goal_1 := by
  intro ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  simp only [sub_zero]
  exact walk_exponent_init_from_table m (Znth i_pre pr_values 0) pr_values pe_values i_pre PreH5.1.1 PreH8 (by omega) rfl

theorem proof_of_walk_entail_wit_3_split_goal_2 : walk_entail_wit_3_split_goal_2 := by
  intro ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  simp only [sub_zero]

theorem proof_of_walk_entail_wit_3_split_goal_3 : walk_entail_wit_3_split_goal_3 := by
  intro ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have h := valid_table_exponent_positive m pr_values pe_values i_pre PreH8 (by omega)
  omega

theorem proof_of_walk_entail_wit_3 : walk_entail_wit_3 := by
  unfold walk_entail_wit_3
  right
  intro ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_walk_entail_wit_3_split_goal_1 ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
    | exact proof_of_walk_entail_wit_3_split_goal_2 ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
    | exact proof_of_walk_entail_wit_3_split_goal_3 ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11


theorem proof_of_walk_entail_wit_4_1_split_goal_1 : walk_entail_wit_4_1_split_goal_1 := by
  intro ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current_2 pk ph p e PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  subst e
  simp only [sub_zero] at PreH2
  obtain ⟨Hstate,Hpk,Hph,Hpkb,Hphb⟩ := walk_exponent_step_first_from_table m p (Znth i_pre pe_values 0) pk ph pr_values pe_values i_pre PreH11.1.2 PreH14 (by omega) PreH9 rfl PreH10
  rw [p090_uint64 (pk*p) (by omega) (by omega),p090_uint64 (p - 1) (by omega) (by omega)]
  have hpkb := Hstate.2.2.1
  have hx := PreH11.2.1
  rw [p090_rem_mod x_value (pk*p) (by omega) (by omega)]
  exact prime_power_consumer_order_input m x_value p 1 (pk*p) (p - 1) d_pre pr_values pe_values i_pre PreH14 (prefix_choice_selected _ _ _ _ _ _ _ PreH15) (by omega) PreH9 (by omega) PreH11 Hpk Hph

theorem proof_of_walk_entail_wit_4_1_split_goal_2 : walk_entail_wit_4_1_split_goal_2 := by
  intro ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current_2 pk ph p e PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  subst e
  simp only [sub_zero] at PreH2
  obtain ⟨Hstate,Hpk,Hph,Hpkb,Hphb⟩ := walk_exponent_step_first_from_table m p (Znth i_pre pe_values 0) pk ph pr_values pe_values i_pre PreH11.1.2 PreH14 (by omega) PreH9 rfl PreH10
  rw [p090_uint64 (pk*p) (by omega) (by omega),p090_uint64 (p - 1) (by omega) (by omega)]
  exact Hstate

theorem proof_of_walk_entail_wit_4_1_split_goal_3 : walk_entail_wit_4_1_split_goal_3 := by
  intro ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current_2 pk ph p e PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  exact valid_table_exponent_positive m pr_values pe_values i_pre PreH14 (by omega)

theorem proof_of_walk_entail_wit_4_1 : walk_entail_wit_4_1 := by
  unfold walk_entail_wit_4_1
  right
  intro ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current_2 pk ph p e PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_walk_entail_wit_4_1_split_goal_1 ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current_2 pk ph p e PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
    | exact proof_of_walk_entail_wit_4_1_split_goal_2 ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current_2 pk ph p e PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
    | exact proof_of_walk_entail_wit_4_1_split_goal_3 ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current_2 pk ph p e PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16


theorem proof_of_walk_entail_wit_4_2_split_goal_1 : walk_entail_wit_4_2_split_goal_1 := by
  intro ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current_2 pk ph p e PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  simp only [sub_zero] at PreH2
  obtain ⟨Hstate,Hpk,Hph,Hpkb,Hphb⟩ := walk_exponent_step_later_from_table m p e (Znth i_pre pe_values 0) pk ph pr_values pe_values i_pre PreH11.1.2 PreH14 (by omega) PreH9 rfl (by omega) PreH2 PreH10
  rw [p090_uint64 (pk*p) (by omega) (by omega),p090_uint64 (ph * p) (by omega) (by omega)]
  have hpkb := Hstate.2.2.1
  have hx := PreH11.2.1
  rw [p090_rem_mod x_value (pk*p) (by omega) (by omega)]
  exact prime_power_consumer_order_input m x_value p e (pk*p) (ph * p) d_pre pr_values pe_values i_pre PreH14 (prefix_choice_selected _ _ _ _ _ _ _ PreH15) (by omega) PreH9 (by omega) PreH11 Hpk Hph

theorem proof_of_walk_entail_wit_4_2_split_goal_2 : walk_entail_wit_4_2_split_goal_2 := by
  intro ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current_2 pk ph p e PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  simp only [sub_zero] at PreH2
  obtain ⟨Hstate,Hpk,Hph,Hpkb,Hphb⟩ := walk_exponent_step_later_from_table m p e (Znth i_pre pe_values 0) pk ph pr_values pe_values i_pre PreH11.1.2 PreH14 (by omega) PreH9 rfl (by omega) PreH2 PreH10
  rw [p090_uint64 (pk*p) (by omega) (by omega),p090_uint64 (ph * p) (by omega) (by omega)]
  exact Hstate

theorem proof_of_walk_entail_wit_4_2_split_goal_3 : walk_entail_wit_4_2_split_goal_3 := by
  intro ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current_2 pk ph p e PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  simpa only [sub_zero] using PreH2

theorem proof_of_walk_entail_wit_4_2 : walk_entail_wit_4_2 := by
  unfold walk_entail_wit_4_2
  right
  intro ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current_2 pk ph p e PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_walk_entail_wit_4_2_split_goal_1 ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current_2 pk ph p e PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
    | exact proof_of_walk_entail_wit_4_2_split_goal_2 ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current_2 pk ph p e PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
    | exact proof_of_walk_entail_wit_4_2_split_goal_3 ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current_2 pk ph p e PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16


theorem proof_of_walk_entail_wit_5_split_goal_1 : walk_entail_wit_5_split_goal_1 := by
  intro ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current_2 e p ph pk retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  obtain ⟨Hpk,Hph,_⟩ := walk_exponent_ready_for_transition m p e (Znth i_pre pe_values 0) pk ph (by omega) PreH12
  rw [Hpk,PreH11]
  exact walk_pending_recursive_call_budget pr_values pe_values m x_value i_pre d_pre before current_2 e (by omega) PreH19

theorem proof_of_walk_entail_wit_5_split_goal_2 : walk_entail_wit_5_split_goal_2 := by
  intro ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current_2 e p ph pk retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  obtain ⟨Ho,Hretval,_⟩ := PreH4
  have hx := PreH14.2.1
  have hpk := PreH12.2.2.1
  rw [p090_rem_mod x_value pk (by omega) (by omega)] at Ho
  obtain ⟨Hinput,Hprime,Hprefix,Hbounds⟩ := walk_exponent_state_consumer_transition m x_value p e pk ph retval retval_2 d_pre phi_pre ord_pre pr_values pe_values i_pre PreH17 PreH18 (by omega) PreH11 (by omega) PreH14 PreH12 Ho PreH1
  have hg : 0 < retval_2 := by
    rw [PreH1]
    have h := Int.gcd_pos_of_ne_zero_right ord_pre (show retval ≠ 0 from by omega)
    change (0 : Int) < (Int.gcd ord_pre retval : Int)
    exact_mod_cast h
  rw [p090_quot_div ord_pre retval_2 (by omega) (by omega)]
  exact Hprefix

theorem proof_of_walk_entail_wit_5_split_goal_3 : walk_entail_wit_5_split_goal_3 := by
  intro ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current_2 e p ph pk retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  obtain ⟨Ho,Hretval,_⟩ := PreH4
  have hx := PreH14.2.1
  have hpk := PreH12.2.2.1
  rw [p090_rem_mod x_value pk (by omega) (by omega)] at Ho
  obtain ⟨Hinput,Hprime,Hprefix,Hbounds⟩ := walk_exponent_state_consumer_transition m x_value p e pk ph retval retval_2 d_pre phi_pre ord_pre pr_values pe_values i_pre PreH17 PreH18 (by omega) PreH11 (by omega) PreH14 PreH12 Ho PreH1
  have hg : 0 < retval_2 := by
    rw [PreH1]
    have h := Int.gcd_pos_of_ne_zero_right ord_pre (show retval ≠ 0 from by omega)
    change (0 : Int) < (Int.gcd ord_pre retval : Int)
    exact_mod_cast h
  rw [p090_quot_div ord_pre retval_2 (by omega) (by omega)]
  exact Hprime

theorem proof_of_walk_entail_wit_5_split_goal_4 : walk_entail_wit_5_split_goal_4 := by
  intro ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current_2 e p ph pk retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  obtain ⟨Ho,Hretval,_⟩ := PreH4
  have hx := PreH14.2.1
  have hpk := PreH12.2.2.1
  rw [p090_rem_mod x_value pk (by omega) (by omega)] at Ho
  obtain ⟨Hinput,Hprime,Hprefix,Hbounds⟩ := walk_exponent_state_consumer_transition m x_value p e pk ph retval retval_2 d_pre phi_pre ord_pre pr_values pe_values i_pre PreH17 PreH18 (by omega) PreH11 (by omega) PreH14 PreH12 Ho PreH1
  have hg : 0 < retval_2 := by
    rw [PreH1]
    have h := Int.gcd_pos_of_ne_zero_right ord_pre (show retval ≠ 0 from by omega)
    change (0 : Int) < (Int.gcd ord_pre retval : Int)
    exact_mod_cast h
  rw [p090_quot_div ord_pre retval_2 (by omega) (by omega)]
  exact Hbounds

theorem proof_of_walk_entail_wit_5_split_goal_5 : walk_entail_wit_5_split_goal_5 := by
  intro ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current_2 e p ph pk retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  rw [PreH1]
  have h := Int.gcd_pos_of_ne_zero_right ord_pre (show retval ≠ 0 from by have := PreH4.2.1; omega)
  change (0 : Int) < (Int.gcd ord_pre retval : Int)
  exact_mod_cast h

theorem proof_of_walk_entail_wit_5 : walk_entail_wit_5 := by
  unfold walk_entail_wit_5
  right
  intro ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current_2 e p ph pk retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_walk_entail_wit_5_split_goal_1 ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current_2 e p ph pk retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
    | exact proof_of_walk_entail_wit_5_split_goal_2 ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current_2 e p ph pk retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
    | exact proof_of_walk_entail_wit_5_split_goal_3 ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current_2 e p ph pk retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
    | exact proof_of_walk_entail_wit_5_split_goal_4 ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current_2 e p ph pk retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
    | exact proof_of_walk_entail_wit_5_split_goal_5 ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current_2 e p ph pk retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19


theorem proof_of_walk_entail_wit_6_split_goal_1 : walk_entail_wit_6_split_goal_1 := by
  intro ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current_2 e p g ph pk o PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have Hstate := PreH14
  obtain ⟨Hp,He,Hpkb,Hphb,Hpk,Hph⟩ := PreH14
  simp only [add_sub_cancel_right] at Hpk
  have hm := PreH9.1.2
  have hep := p090_exponent_lt_pow p e (by omega) (by omega)
  have hewrap : unsigned_last_nbits (e+1) 64 = e+1 := p090_uint64 _ (by omega) (by omega)
  have hdpk := PreH15.1
  rw [p090_uint64 (d_pre*pk) (by omega) (by omega),hewrap,Hpk,PreH7]
  exact walk_recursive_return_continuation pr_values pe_values m x_value i_pre d_pre before current_2 e _ (by omega) PreH19 rfl

theorem proof_of_walk_entail_wit_6_split_goal_2 : walk_entail_wit_6_split_goal_2 := by
  intro ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current_2 e p g ph pk o PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have Hstate := PreH14
  obtain ⟨Hp,He,Hpkb,Hphb,Hpk,Hph⟩ := PreH14
  simp only [add_sub_cancel_right] at Hpk
  have hm := PreH9.1.2
  have hep := p090_exponent_lt_pow p e (by omega) (by omega)
  have hewrap : unsigned_last_nbits (e+1) 64 = e+1 := p090_uint64 _ (by omega) (by omega)
  rw [hewrap]
  exact Hstate

theorem proof_of_walk_entail_wit_6_split_goal_3 : walk_entail_wit_6_split_goal_3 := by
  intro ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current_2 e p g ph pk o PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have Hstate := PreH14
  obtain ⟨Hp,He,Hpkb,Hphb,Hpk,Hph⟩ := PreH14
  simp only [add_sub_cancel_right] at Hpk
  have hm := PreH9.1.2
  have hep := p090_exponent_lt_pow p e (by omega) (by omega)
  have hewrap : unsigned_last_nbits (e+1) 64 = e+1 := p090_uint64 _ (by omega) (by omega)
  rw [hewrap]
  omega

theorem proof_of_walk_entail_wit_6_split_goal_4 : walk_entail_wit_6_split_goal_4 := by
  intro ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current_2 e p g ph pk o PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have Hstate := PreH14
  obtain ⟨Hp,He,Hpkb,Hphb,Hpk,Hph⟩ := PreH14
  simp only [add_sub_cancel_right] at Hpk
  have hm := PreH9.1.2
  have hep := p090_exponent_lt_pow p e (by omega) (by omega)
  have hewrap : unsigned_last_nbits (e+1) 64 = e+1 := p090_uint64 _ (by omega) (by omega)
  rw [hewrap]
  omega

theorem proof_of_walk_entail_wit_6 : walk_entail_wit_6 := by
  unfold walk_entail_wit_6
  right
  intro ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current_2 e p g ph pk o PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_walk_entail_wit_6_split_goal_1 ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current_2 e p g ph pk o PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
    | exact proof_of_walk_entail_wit_6_split_goal_2 ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current_2 e p g ph pk o PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
    | exact proof_of_walk_entail_wit_6_split_goal_3 ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current_2 e p g ph pk o PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
    | exact proof_of_walk_entail_wit_6_split_goal_4 ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current_2 e p g ph pk o PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19


theorem proof_of_walk_return_wit_1_split_goal_1 : walk_return_wit_1_split_goal_1 := by
  intro ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hleaf := prefix_choice_terminal_walk_value pr_values pe_values x_value i_pre d_pre phi_pre ord_pre PreH11 (by omega) (by omega)
  rw [hleaf] at PreH12 ⊢
  have hb := PreH12
  unfold WalkBudget at hb
  have hm := PreH7.1.2
  have hp := PreH8.2.1.1
  rw [p090_quot_div phi_pre ord_pre (by omega) (by omega)]
  exact p090_uint64 _ (by omega) (by omega)

theorem proof_of_walk_return_wit_1 : walk_return_wit_1 := by
  unfold walk_return_wit_1
  right
  intro ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_walk_return_wit_1_split_goal_1 ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12


theorem proof_of_walk_return_wit_2_split_goal_1 : walk_return_wit_2_split_goal_1 := by
  intro ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hd := (prefix_choice_positive pr_values pe_values x_value i_pre d_pre phi_pre ord_pre PreH11).1
  have hd1 : d_pre = 1 := by omega
  rw [walk_suffix_at_terminal pr_values pe_values x_value i_pre d_pre (by omega) (by omega),hd1]
  simp [CycleTerm]

theorem proof_of_walk_return_wit_2 : walk_return_wit_2 := by
  unfold walk_return_wit_2
  right
  intro ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_walk_return_wit_2_split_goal_1 ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12


theorem proof_of_walk_return_wit_3_split_goal_1 : walk_return_wit_3_split_goal_1 := by
  intro ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current pk ph p e PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  apply walk_pending_terminal pr_values pe_values m x_value i_pre d_pre before current e PreH15
  simpa only [sub_zero] using PreH1

theorem proof_of_walk_return_wit_3 : walk_return_wit_3 := by
  unfold walk_return_wit_3
  right
  intro ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current pk ph p e PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_walk_return_wit_3_split_goal_1 ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current pk ph p e PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15


theorem proof_of_walk_partial_solve_wit_4_pure_split_goal_1 : walk_partial_solve_wit_4_pure_split_goal_1 := by
  intro ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current e p ph pk PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37
  dump_pre_spatial
  have hpk := PreH30.2.2.1
  have hm := PreH32.1
  omega

theorem proof_of_walk_partial_solve_wit_4_pure : walk_partial_solve_wit_4_pure := by
  unfold walk_partial_solve_wit_4_pure
  right
  intro ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current e p ph pk PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37
  split_pures <;> first
  | exact proof_of_walk_partial_solve_wit_4_pure_split_goal_1 ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current e p ph pk PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37


theorem proof_of_walk_partial_solve_wit_5_pure_split_goal_1 : walk_partial_solve_wit_5_pure_split_goal_1 := by
  intro ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current e p ph pk retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  dump_pre_spatial
  have ho := PreH36.2.2
  have hm := PreH35.1
  omega

theorem proof_of_walk_partial_solve_wit_5_pure_split_goal_2 : walk_partial_solve_wit_5_pure_split_goal_2 := by
  intro ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current e p ph pk retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  dump_pre_spatial
  have hret := PreH25.1
  have hdvd := PreH34.2.2.2.2.2.1
  have hphi := PreH34.2.2.2.1
  have hle := Int.le_of_dvd hphi.1 ((Z.divide_iff_dvd _ _).mp hdvd)
  have hpk := PreH33.2.2.1
  have hm := PreH35.1
  omega

theorem proof_of_walk_partial_solve_wit_5_pure : walk_partial_solve_wit_5_pure := by
  unfold walk_partial_solve_wit_5_pure
  right
  intro ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current e p ph pk retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  split_pures <;> first
  | exact proof_of_walk_partial_solve_wit_5_pure_split_goal_1 ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current e p ph pk retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  | exact proof_of_walk_partial_solve_wit_5_pure_split_goal_2 ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current e p ph pk retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40


theorem proof_of_walk_partial_solve_wit_6_pure_split_goal_1 : walk_partial_solve_wit_6_pure_split_goal_1 := by
  intro ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current e p g ph pk o PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
  dump_pre_spatial
  obtain ⟨Hd,Hphi,Hord⟩ := PreH41
  have hm := PreH35.1.2
  rw [p090_uint64 (d_pre*pk) (by omega) (by omega), p090_uint64 (phi_pre*ph) (by omega) (by omega), p090_uint64 ((Z.quot ord_pre g)*o) (by omega) (by omega)]
  exact ⟨Hd,Hphi,Hord⟩

theorem proof_of_walk_partial_solve_wit_6_pure_split_goal_2 : walk_partial_solve_wit_6_pure_split_goal_2 := by
  intro ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current e p g ph pk o PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
  dump_pre_spatial
  obtain ⟨Hd,Hphi,Hord⟩ := PreH41
  have hm := PreH35.1.2
  rw [p090_uint64 ((Z.quot ord_pre g)*o) (by omega) (by omega)]
  omega

theorem proof_of_walk_partial_solve_wit_6_pure_split_goal_3 : walk_partial_solve_wit_6_pure_split_goal_3 := by
  intro ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current e p g ph pk o PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
  dump_pre_spatial
  obtain ⟨Hd,Hphi,Hord⟩ := PreH41
  have hm := PreH35.1.2
  rw [p090_uint64 (d_pre*pk) (by omega) (by omega), p090_uint64 (phi_pre*ph) (by omega) (by omega), p090_uint64 ((Z.quot ord_pre g)*o) (by omega) (by omega)]
  exact PreH43

theorem proof_of_walk_partial_solve_wit_6_pure_split_goal_4 : walk_partial_solve_wit_6_pure_split_goal_4 := by
  intro ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current e p g ph pk o PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
  dump_pre_spatial
  obtain ⟨Hd,Hphi,Hord⟩ := PreH41
  have hm := PreH35.1.2
  rw [p090_uint64 (d_pre*pk) (by omega) (by omega)]
  exact PreH44

theorem proof_of_walk_partial_solve_wit_6_pure : walk_partial_solve_wit_6_pure := by
  unfold walk_partial_solve_wit_6_pure
  right
  intro ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current e p g ph pk o PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
  split_pures <;> first
  | exact proof_of_walk_partial_solve_wit_6_pure_split_goal_1 ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current e p g ph pk o PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
  | exact proof_of_walk_partial_solve_wit_6_pure_split_goal_2 ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current e p g ph pk o PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
  | exact proof_of_walk_partial_solve_wit_6_pure_split_goal_3 ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current e p g ph pk o PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45
  | exact proof_of_walk_partial_solve_wit_6_pure_split_goal_4 ord_pre phi_pre d_pre i_pre pe_values pr_values before factor_count x_value m current e p g ph pk o PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45


end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_proof_manual
