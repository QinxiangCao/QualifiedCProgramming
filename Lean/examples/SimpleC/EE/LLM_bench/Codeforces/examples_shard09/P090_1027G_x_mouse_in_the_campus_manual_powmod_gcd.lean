import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_manual_mulmod
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

theorem proof_of_powmod_entail_wit_1_split_goal_1 : powmod_entail_wit_1_split_goal_1 := by
  intro modulus_pre e_pre b_pre modulus0 exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  unfold PowLoopState Z.rem
  rw [← Int.fmod_eq_tmod_of_nonneg (by omega : 0 ≤ b_pre) (by omega : 0 ≤ modulus_pre),
    ← Int.fmod_eq_tmod_of_nonneg (by omega : (0:Int) ≤ 1) (by omega : 0 ≤ modulus_pre)]
  by_cases hm1 : modulus_pre = 1
  · simp [hm1,Z.modulo]
  · have h1 : (1:Int).fmod modulus_pre = 1 := Int.fmod_eq_of_lt (by omega) (by omega)
    rw [h1,one_mul]
    exact pow_mod_base__powmod_loop b_pre modulus_pre e_pre (by omega) (by omega)

theorem proof_of_powmod_entail_wit_1_split_goal_2 : powmod_entail_wit_1_split_goal_2 := by
  intro modulus_pre e_pre b_pre modulus0 exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  first
    | exact Int.tmod_lt_of_pos _ (by omega)
    | exact Int.tmod_nonneg _ (by omega)

theorem proof_of_powmod_entail_wit_1_split_goal_3 : powmod_entail_wit_1_split_goal_3 := by
  intro modulus_pre e_pre b_pre modulus0 exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  first
    | exact Int.tmod_lt_of_pos _ (by omega)
    | exact Int.tmod_nonneg _ (by omega)

theorem proof_of_powmod_entail_wit_1_split_goal_4 : powmod_entail_wit_1_split_goal_4 := by
  intro modulus_pre e_pre b_pre modulus0 exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  first
    | exact Int.tmod_lt_of_pos _ (by omega)
    | exact Int.tmod_nonneg _ (by omega)

theorem proof_of_powmod_entail_wit_1_split_goal_5 : powmod_entail_wit_1_split_goal_5 := by
  intro modulus_pre e_pre b_pre modulus0 exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  first
    | exact Int.tmod_lt_of_pos _ (by omega)
    | exact Int.tmod_nonneg _ (by omega)

theorem proof_of_powmod_entail_wit_1 : powmod_entail_wit_1 := by
  unfold powmod_entail_wit_1
  right
  intro modulus_pre e_pre b_pre modulus0 exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_powmod_entail_wit_1_split_goal_1 modulus_pre e_pre b_pre modulus0 exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
    | exact proof_of_powmod_entail_wit_1_split_goal_2 modulus_pre e_pre b_pre modulus0 exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
    | exact proof_of_powmod_entail_wit_1_split_goal_3 modulus_pre e_pre b_pre modulus0 exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
    | exact proof_of_powmod_entail_wit_1_split_goal_4 modulus_pre e_pre b_pre modulus0 exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
    | exact proof_of_powmod_entail_wit_1_split_goal_5 modulus_pre e_pre b_pre modulus0 exponent base PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9

theorem proof_of_powmod_entail_wit_2_1_split_goal_1 : powmod_entail_wit_2_1_split_goal_1 := by
  intro modulus_pre e_pre b_pre modulus0 exponent base r e b retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have hbb : Z.rem (b*b) modulus_pre = (b*b) mod modulus_pre :=
    (Int.fmod_eq_tmod_of_nonneg (mul_self_nonneg b) (by omega)).symm
  rw [hbb]
  have hrb : Z.rem (r*b) modulus_pre = (r*b) mod modulus_pre :=
    (Int.fmod_eq_tmod_of_nonneg (mul_nonneg (by omega) (by omega)) (by omega)).symm
  rw [hrb]
  have hp : PowLoopState b_pre e_pre modulus_pre b e r := by simpa only [PreH7,PreH8] using PreH19
  exact pow_loop_odd_step__powmod_loop b_pre e_pre modulus_pre b e r (by omega) (by omega) PreH21 hp

theorem proof_of_powmod_entail_wit_2_1_split_goal_2 : powmod_entail_wit_2_1_split_goal_2 := by
  intro modulus_pre e_pre b_pre modulus0 exponent base r e b retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  rw [p090_shiftr_one]
  have hq0 : 0 ≤ e /ᶻ 2 := Int.fdiv_nonneg (by omega) (by omega)
  have hqle : e /ᶻ 2 ≤ e := by
    change e.fdiv 2 ≤ e
    rw [Int.fdiv_eq_ediv_of_nonneg e (by omega)]
    exact Int.ediv_le_self 2 (by omega)
  omega

theorem proof_of_powmod_entail_wit_2_1_split_goal_3 : powmod_entail_wit_2_1_split_goal_3 := by
  intro modulus_pre e_pre b_pre modulus0 exponent base r e b retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  rw [p090_shiftr_one]
  have hq0 : 0 ≤ e /ᶻ 2 := Int.fdiv_nonneg (by omega) (by omega)
  have hqle : e /ᶻ 2 ≤ e := by
    change e.fdiv 2 ≤ e
    rw [Int.fdiv_eq_ediv_of_nonneg e (by omega)]
    exact Int.ediv_le_self 2 (by omega)
  omega

theorem proof_of_powmod_entail_wit_2_1 : powmod_entail_wit_2_1 := by
  unfold powmod_entail_wit_2_1
  right
  intro modulus_pre e_pre b_pre modulus0 exponent base r e b retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_powmod_entail_wit_2_1_split_goal_1 modulus_pre e_pre b_pre modulus0 exponent base r e b retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
    | exact proof_of_powmod_entail_wit_2_1_split_goal_2 modulus_pre e_pre b_pre modulus0 exponent base r e b retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
    | exact proof_of_powmod_entail_wit_2_1_split_goal_3 modulus_pre e_pre b_pre modulus0 exponent base r e b retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21

theorem proof_of_powmod_entail_wit_2_2_split_goal_1 : powmod_entail_wit_2_2_split_goal_1 := by
  intro modulus_pre e_pre b_pre modulus0 exponent base r e b retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hbb : Z.rem (b*b) modulus_pre = (b*b) mod modulus_pre :=
    (Int.fmod_eq_tmod_of_nonneg (mul_self_nonneg b) (by omega)).symm
  rw [hbb]
  have hp : PowLoopState b_pre e_pre modulus_pre b e r := by simpa only [PreH4,PreH5] using PreH16
  exact pow_loop_even_step__powmod_loop b_pre e_pre modulus_pre b e r (by omega) (by omega) PreH18 hp

theorem proof_of_powmod_entail_wit_2_2_split_goal_2 : powmod_entail_wit_2_2_split_goal_2 := by
  intro modulus_pre e_pre b_pre modulus0 exponent base r e b retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  rw [p090_shiftr_one]
  have hq0 : 0 ≤ e /ᶻ 2 := Int.fdiv_nonneg (by omega) (by omega)
  have hqle : e /ᶻ 2 ≤ e := by
    change e.fdiv 2 ≤ e
    rw [Int.fdiv_eq_ediv_of_nonneg e (by omega)]
    exact Int.ediv_le_self 2 (by omega)
  omega

theorem proof_of_powmod_entail_wit_2_2_split_goal_3 : powmod_entail_wit_2_2_split_goal_3 := by
  intro modulus_pre e_pre b_pre modulus0 exponent base r e b retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  rw [p090_shiftr_one]
  have hq0 : 0 ≤ e /ᶻ 2 := Int.fdiv_nonneg (by omega) (by omega)
  have hqle : e /ᶻ 2 ≤ e := by
    change e.fdiv 2 ≤ e
    rw [Int.fdiv_eq_ediv_of_nonneg e (by omega)]
    exact Int.ediv_le_self 2 (by omega)
  omega

theorem proof_of_powmod_entail_wit_2_2 : powmod_entail_wit_2_2 := by
  unfold powmod_entail_wit_2_2
  right
  intro modulus_pre e_pre b_pre modulus0 exponent base r e b retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_powmod_entail_wit_2_2_split_goal_1 modulus_pre e_pre b_pre modulus0 exponent base r e b retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
    | exact proof_of_powmod_entail_wit_2_2_split_goal_2 modulus_pre e_pre b_pre modulus0 exponent base r e b retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
    | exact proof_of_powmod_entail_wit_2_2_split_goal_3 modulus_pre e_pre b_pre modulus0 exponent base r e b retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18

theorem proof_of_powmod_return_wit_1_split_goal_1 : powmod_return_wit_1_split_goal_1 := by
  intro modulus_pre e_pre b_pre modulus0 exponent base r e b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  unfold PowLoopState at PreH13
  rw [PreH1,PreH2,PreH14] at PreH13
  rw [show Z.pow b 0 = 1 from rfl,mul_one] at PreH13
  have hr : r mod modulus_pre = r := Int.fmod_eq_of_lt (by omega) (by omega)
  rw [hr] at PreH13
  have hp : 0 ≤ Z.pow b_pre e_pre := by
    rw [coq_pow_nat b_pre e_pre (by omega)]
    exact pow_nonneg (by omega) _
  change r = Z.rem (Z.pow b_pre e_pre) modulus_pre
  rw [show Z.rem (Z.pow b_pre e_pre) modulus_pre = Z.pow b_pre e_pre mod modulus_pre from
    (Int.fmod_eq_tmod_of_nonneg hp (by omega)).symm]
  exact PreH13

theorem proof_of_powmod_return_wit_1 : powmod_return_wit_1 := by
  unfold powmod_return_wit_1
  right
  intro modulus_pre e_pre b_pre modulus0 exponent base r e b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_powmod_return_wit_1_split_goal_1 modulus_pre e_pre b_pre modulus0 exponent base r e b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14

theorem proof_of_gcd__entail_wit_1_split_goal_1 : gcd__entail_wit_1_split_goal_1 := by
  intro b_pre a_pre b0 a0 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  rfl

theorem proof_of_gcd__entail_wit_1 : gcd__entail_wit_1 := by
  unfold gcd__entail_wit_1
  right
  intro b_pre a_pre b0 a0 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_gcd__entail_wit_1_split_goal_1 b_pre a_pre b0 a0 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6

theorem proof_of_gcd__entail_wit_2_split_goal_1 : gcd__entail_wit_2_split_goal_1 := by
  intro b_pre a_pre b0 a0 b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  unfold GcdLoopState at *
  rw [show Z.rem a b = a mod b from (Int.fmod_eq_tmod_of_nonneg (by omega) (by omega)).symm]
  rw [show Z.gcd b (a mod b) = Z.gcd (a mod b) b by simp [Z.gcd,Int.gcd_comm],coq_gcd_mod]
  simpa only [PreH1,PreH2] using PreH9

theorem proof_of_gcd__entail_wit_2_split_goal_2 : gcd__entail_wit_2_split_goal_2 := by
  intro b_pre a_pre b0 a0 b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hn : 0 ≤ Z.rem a b := Int.tmod_nonneg b (by omega)
  have hl : Z.rem a b < b := Int.tmod_lt_of_pos a (by omega)
  omega

theorem proof_of_gcd__entail_wit_2_split_goal_3 : gcd__entail_wit_2_split_goal_3 := by
  intro b_pre a_pre b0 a0 b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hn : 0 ≤ Z.rem a b := Int.tmod_nonneg b (by omega)
  have hl : Z.rem a b < b := Int.tmod_lt_of_pos a (by omega)
  omega

theorem proof_of_gcd__entail_wit_2 : gcd__entail_wit_2 := by
  unfold gcd__entail_wit_2
  right
  intro b_pre a_pre b0 a0 b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_gcd__entail_wit_2_split_goal_1 b_pre a_pre b0 a0 b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
    | exact proof_of_gcd__entail_wit_2_split_goal_2 b_pre a_pre b0 a0 b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
    | exact proof_of_gcd__entail_wit_2_split_goal_3 b_pre a_pre b0 a0 b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10

theorem proof_of_gcd__return_wit_1_split_goal_1 : gcd__return_wit_1_split_goal_1 := by
  intro b_pre a_pre b0 a0 b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  unfold GcdLoopState at PreH9
  rw [PreH10] at PreH9
  have hga : Z.gcd a 0 = a := by simp [Z.gcd,Int.natAbs_of_nonneg (by omega : 0 ≤ a)]
  rw [hga,PreH1,PreH2] at PreH9
  have hd : (Z.gcd a_pre b_pre : Int) ∣ a_pre+b_pre := dvd_add (Int.gcd_dvd_left _ _) (Int.gcd_dvd_right _ _)
  by_cases hz : a_pre+b_pre = 0
  · have ha0 : a_pre = 0 := by omega
    have hb0 : b_pre = 0 := by omega
    simp [ha0,hb0,Z.gcd] at PreH9
    omega
  · have hle := Int.le_of_dvd (by omega : 0 < a_pre+b_pre) hd
    omega

theorem proof_of_gcd__return_wit_1_split_goal_2 : gcd__return_wit_1_split_goal_2 := by
  intro b_pre a_pre b0 a0 b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  unfold GcdLoopState at PreH9
  rw [PreH10] at PreH9
  have hga : Z.gcd a 0 = a := by simp [Z.gcd,Int.natAbs_of_nonneg (by omega : 0 ≤ a)]
  rw [hga,PreH1,PreH2] at PreH9
  exact PreH9

theorem proof_of_gcd__return_wit_1 : gcd__return_wit_1 := by
  unfold gcd__return_wit_1
  right
  intro b_pre a_pre b0 a0 b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_gcd__return_wit_1_split_goal_1 b_pre a_pre b0 a0 b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
    | exact proof_of_gcd__return_wit_1_split_goal_2 b_pre a_pre b0 a0 b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_proof_manual
