import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_goal
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

theorem p090_shiftr_one (e : Int) : Z.shiftr e 1 = e /ᶻ 2 := by
  change e >>> 1 = e.fdiv 2
  rw [Int.shiftRight_eq_div_pow]
  simpa using (Int.fdiv_eq_ediv_of_nonneg e (by omega : (0:Int) ≤ 2)).symm

theorem p090_shiftl_one (a : Int) : Z.shiftl a 1 = a*2 := by
  change a <<< 1 = a*2
  simp [Int.shiftLeft_eq]

theorem p090_uint64 (a : Int) (ha : 0 ≤ a) (hb : a < 18446744073709551616) : unsigned_last_nbits a 64 = a :=
  unsigned_last_nbits_eq a 64 ⟨ha,hb⟩

theorem p090_mul_step (a0 b0 m a b r a' b' r' k : Int) :
    MulLoopState a0 b0 m a b r → r'+a'*b' = (r+a*b)-m*k → MulLoopState a0 b0 m a' b' r' := by
  intro hs he
  unfold MulLoopState Z.modulo at *
  rw [he,Int.sub_mul_fmod_self_left]
  exact hs

theorem proof_of_mulmod_entail_wit_1_split_goal_1 : mulmod_entail_wit_1_split_goal_1 := by
  intro modulus_pre b_pre a_pre modulus0 b0 a0 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  unfold MulLoopState Z.rem Z.modulo
  rw [← Int.fmod_eq_tmod_of_nonneg (by omega : 0 ≤ a_pre) (by omega : 0 ≤ modulus_pre),
    ← Int.fmod_eq_tmod_of_nonneg (by omega : 0 ≤ b_pre) (by omega : 0 ≤ modulus_pre)]
  simp only [zero_add,← Int.mul_fmod]

theorem proof_of_mulmod_entail_wit_1_split_goal_2 : mulmod_entail_wit_1_split_goal_2 := by
  intro modulus_pre b_pre a_pre modulus0 b0 a0 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  first
    | exact Int.tmod_lt_of_pos _ (by omega)
    | exact Int.tmod_nonneg _ (by omega)

theorem proof_of_mulmod_entail_wit_1_split_goal_3 : mulmod_entail_wit_1_split_goal_3 := by
  intro modulus_pre b_pre a_pre modulus0 b0 a0 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  first
    | exact Int.tmod_lt_of_pos _ (by omega)
    | exact Int.tmod_nonneg _ (by omega)

theorem proof_of_mulmod_entail_wit_1_split_goal_4 : mulmod_entail_wit_1_split_goal_4 := by
  intro modulus_pre b_pre a_pre modulus0 b0 a0 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  first
    | exact Int.tmod_lt_of_pos _ (by omega)
    | exact Int.tmod_nonneg _ (by omega)

theorem proof_of_mulmod_entail_wit_1_split_goal_5 : mulmod_entail_wit_1_split_goal_5 := by
  intro modulus_pre b_pre a_pre modulus0 b0 a0 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  first
    | exact Int.tmod_lt_of_pos _ (by omega)
    | exact Int.tmod_nonneg _ (by omega)

theorem proof_of_mulmod_entail_wit_1 : mulmod_entail_wit_1 := by
  unfold mulmod_entail_wit_1
  right
  intro modulus_pre b_pre a_pre modulus0 b0 a0 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_mulmod_entail_wit_1_split_goal_1 modulus_pre b_pre a_pre modulus0 b0 a0 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
    | exact proof_of_mulmod_entail_wit_1_split_goal_2 modulus_pre b_pre a_pre modulus0 b0 a0 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
    | exact proof_of_mulmod_entail_wit_1_split_goal_3 modulus_pre b_pre a_pre modulus0 b0 a0 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
    | exact proof_of_mulmod_entail_wit_1_split_goal_4 modulus_pre b_pre a_pre modulus0 b0 a0 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
    | exact proof_of_mulmod_entail_wit_1_split_goal_5 modulus_pre b_pre a_pre modulus0 b0 a0 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9

theorem proof_of_mulmod_entail_wit_2_1_split_goal_1 : mulmod_entail_wit_2_1_split_goal_1 := by
  intro modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  simp only [p090_shiftl_one,p090_shiftr_one] at *
  have hw : unsigned_last_nbits (a*2) 64 = a*2 := p090_uint64 _ (by omega) (by omega)
  simp only [hw] at *
  simp only [land_one_mod_two__powmod_loop] at *
  have hmod0 := Int.fmod_nonneg_of_pos b (by omega : (0:Int) < 2)
  have hmod2 := Int.fmod_lt_of_pos b (by omega : (0:Int) < 2)
  have hdiv := Int.fmod_add_mul_fdiv b 2
  change b.fmod 2 + 2*(b /ᶻ 2) = b at hdiv
  unfold Z.modulo at *
  have hbit : b.fmod 2 = 1 := by omega
  rw [hbit] at hdiv
  apply p090_mul_step _ _ _ a b r _ _ _ (1+b /ᶻ 2)
  · assumption
  · nlinarith

theorem proof_of_mulmod_entail_wit_2_1_split_goal_2 : mulmod_entail_wit_2_1_split_goal_2 := by
  intro modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  simp only [p090_shiftl_one,p090_shiftr_one] at *
  have hw : unsigned_last_nbits (a*2) 64 = a*2 := p090_uint64 _ (by omega) (by omega)
  simp only [hw] at *
  have hq0 : 0 ≤ b /ᶻ 2 := Int.fdiv_nonneg (by omega) (by omega)
  have hqle : b /ᶻ 2 ≤ b := by
    change b.fdiv 2 ≤ b
    rw [Int.fdiv_eq_ediv_of_nonneg b (by omega)]
    exact Int.ediv_le_self 2 (by omega)
  omega

theorem proof_of_mulmod_entail_wit_2_1_split_goal_3 : mulmod_entail_wit_2_1_split_goal_3 := by
  intro modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  simp only [p090_shiftl_one,p090_shiftr_one] at *
  have hw : unsigned_last_nbits (a*2) 64 = a*2 := p090_uint64 _ (by omega) (by omega)
  simp only [hw] at *
  have hq0 : 0 ≤ b /ᶻ 2 := Int.fdiv_nonneg (by omega) (by omega)
  have hqle : b /ᶻ 2 ≤ b := by
    change b.fdiv 2 ≤ b
    rw [Int.fdiv_eq_ediv_of_nonneg b (by omega)]
    exact Int.ediv_le_self 2 (by omega)
  omega

theorem proof_of_mulmod_entail_wit_2_1_split_goal_4 : mulmod_entail_wit_2_1_split_goal_4 := by
  intro modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  simp only [p090_shiftl_one,p090_shiftr_one] at *
  have hw : unsigned_last_nbits (a*2) 64 = a*2 := p090_uint64 _ (by omega) (by omega)
  simp only [hw] at *
  have hq0 : 0 ≤ b /ᶻ 2 := Int.fdiv_nonneg (by omega) (by omega)
  have hqle : b /ᶻ 2 ≤ b := by
    change b.fdiv 2 ≤ b
    rw [Int.fdiv_eq_ediv_of_nonneg b (by omega)]
    exact Int.ediv_le_self 2 (by omega)
  omega

theorem proof_of_mulmod_entail_wit_2_1 : mulmod_entail_wit_2_1 := by
  unfold mulmod_entail_wit_2_1
  right
  intro modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_mulmod_entail_wit_2_1_split_goal_1 modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
    | exact proof_of_mulmod_entail_wit_2_1_split_goal_2 modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
    | exact proof_of_mulmod_entail_wit_2_1_split_goal_3 modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
    | exact proof_of_mulmod_entail_wit_2_1_split_goal_4 modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18

theorem proof_of_mulmod_entail_wit_2_2_split_goal_1 : mulmod_entail_wit_2_2_split_goal_1 := by
  intro modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  simp only [p090_shiftl_one,p090_shiftr_one] at *
  have hw : unsigned_last_nbits (a*2) 64 = a*2 := p090_uint64 _ (by omega) (by omega)
  simp only [hw] at *
  simp only [land_one_mod_two__powmod_loop] at *
  have hmod0 := Int.fmod_nonneg_of_pos b (by omega : (0:Int) < 2)
  have hmod2 := Int.fmod_lt_of_pos b (by omega : (0:Int) < 2)
  have hdiv := Int.fmod_add_mul_fdiv b 2
  change b.fmod 2 + 2*(b /ᶻ 2) = b at hdiv
  unfold Z.modulo at *
  have hbit : b.fmod 2 = 1 := by omega
  rw [hbit] at hdiv
  apply p090_mul_step _ _ _ a b r _ _ _ (b /ᶻ 2)
  · assumption
  · nlinarith

theorem proof_of_mulmod_entail_wit_2_2_split_goal_2 : mulmod_entail_wit_2_2_split_goal_2 := by
  intro modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  simp only [p090_shiftl_one,p090_shiftr_one] at *
  have hw : unsigned_last_nbits (a*2) 64 = a*2 := p090_uint64 _ (by omega) (by omega)
  simp only [hw] at *
  have hq0 : 0 ≤ b /ᶻ 2 := Int.fdiv_nonneg (by omega) (by omega)
  have hqle : b /ᶻ 2 ≤ b := by
    change b.fdiv 2 ≤ b
    rw [Int.fdiv_eq_ediv_of_nonneg b (by omega)]
    exact Int.ediv_le_self 2 (by omega)
  omega

theorem proof_of_mulmod_entail_wit_2_2_split_goal_3 : mulmod_entail_wit_2_2_split_goal_3 := by
  intro modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  simp only [p090_shiftl_one,p090_shiftr_one] at *
  have hw : unsigned_last_nbits (a*2) 64 = a*2 := p090_uint64 _ (by omega) (by omega)
  simp only [hw] at *
  have hq0 : 0 ≤ b /ᶻ 2 := Int.fdiv_nonneg (by omega) (by omega)
  have hqle : b /ᶻ 2 ≤ b := by
    change b.fdiv 2 ≤ b
    rw [Int.fdiv_eq_ediv_of_nonneg b (by omega)]
    exact Int.ediv_le_self 2 (by omega)
  omega

theorem proof_of_mulmod_entail_wit_2_2_split_goal_4 : mulmod_entail_wit_2_2_split_goal_4 := by
  intro modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  simp only [p090_shiftl_one,p090_shiftr_one] at *
  have hw : unsigned_last_nbits (a*2) 64 = a*2 := p090_uint64 _ (by omega) (by omega)
  simp only [hw] at *
  have hq0 : 0 ≤ b /ᶻ 2 := Int.fdiv_nonneg (by omega) (by omega)
  have hqle : b /ᶻ 2 ≤ b := by
    change b.fdiv 2 ≤ b
    rw [Int.fdiv_eq_ediv_of_nonneg b (by omega)]
    exact Int.ediv_le_self 2 (by omega)
  omega

theorem proof_of_mulmod_entail_wit_2_2 : mulmod_entail_wit_2_2 := by
  unfold mulmod_entail_wit_2_2
  right
  intro modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_mulmod_entail_wit_2_2_split_goal_1 modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
    | exact proof_of_mulmod_entail_wit_2_2_split_goal_2 modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
    | exact proof_of_mulmod_entail_wit_2_2_split_goal_3 modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
    | exact proof_of_mulmod_entail_wit_2_2_split_goal_4 modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18

theorem proof_of_mulmod_entail_wit_2_3_split_goal_1 : mulmod_entail_wit_2_3_split_goal_1 := by
  intro modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  simp only [p090_shiftl_one,p090_shiftr_one] at *
  have hw : unsigned_last_nbits (a*2) 64 = a*2 := p090_uint64 _ (by omega) (by omega)
  simp only [hw] at *
  simp only [land_one_mod_two__powmod_loop] at *
  have hmod0 := Int.fmod_nonneg_of_pos b (by omega : (0:Int) < 2)
  have hmod2 := Int.fmod_lt_of_pos b (by omega : (0:Int) < 2)
  have hdiv := Int.fmod_add_mul_fdiv b 2
  change b.fmod 2 + 2*(b /ᶻ 2) = b at hdiv
  unfold Z.modulo at *
  have hbit : b.fmod 2 = 0 := by omega
  rw [hbit] at hdiv
  apply p090_mul_step _ _ _ a b r _ _ _ (b /ᶻ 2)
  · assumption
  · nlinarith

theorem proof_of_mulmod_entail_wit_2_3_split_goal_2 : mulmod_entail_wit_2_3_split_goal_2 := by
  intro modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  simp only [p090_shiftl_one,p090_shiftr_one] at *
  have hw : unsigned_last_nbits (a*2) 64 = a*2 := p090_uint64 _ (by omega) (by omega)
  simp only [hw] at *
  have hq0 : 0 ≤ b /ᶻ 2 := Int.fdiv_nonneg (by omega) (by omega)
  have hqle : b /ᶻ 2 ≤ b := by
    change b.fdiv 2 ≤ b
    rw [Int.fdiv_eq_ediv_of_nonneg b (by omega)]
    exact Int.ediv_le_self 2 (by omega)
  omega

theorem proof_of_mulmod_entail_wit_2_3_split_goal_3 : mulmod_entail_wit_2_3_split_goal_3 := by
  intro modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  simp only [p090_shiftl_one,p090_shiftr_one] at *
  have hw : unsigned_last_nbits (a*2) 64 = a*2 := p090_uint64 _ (by omega) (by omega)
  simp only [hw] at *
  have hq0 : 0 ≤ b /ᶻ 2 := Int.fdiv_nonneg (by omega) (by omega)
  have hqle : b /ᶻ 2 ≤ b := by
    change b.fdiv 2 ≤ b
    rw [Int.fdiv_eq_ediv_of_nonneg b (by omega)]
    exact Int.ediv_le_self 2 (by omega)
  omega

theorem proof_of_mulmod_entail_wit_2_3_split_goal_4 : mulmod_entail_wit_2_3_split_goal_4 := by
  intro modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  simp only [p090_shiftl_one,p090_shiftr_one] at *
  have hw : unsigned_last_nbits (a*2) 64 = a*2 := p090_uint64 _ (by omega) (by omega)
  simp only [hw] at *
  have hq0 : 0 ≤ b /ᶻ 2 := Int.fdiv_nonneg (by omega) (by omega)
  have hqle : b /ᶻ 2 ≤ b := by
    change b.fdiv 2 ≤ b
    rw [Int.fdiv_eq_ediv_of_nonneg b (by omega)]
    exact Int.ediv_le_self 2 (by omega)
  omega

theorem proof_of_mulmod_entail_wit_2_3 : mulmod_entail_wit_2_3 := by
  unfold mulmod_entail_wit_2_3
  right
  intro modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_mulmod_entail_wit_2_3_split_goal_1 modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
    | exact proof_of_mulmod_entail_wit_2_3_split_goal_2 modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
    | exact proof_of_mulmod_entail_wit_2_3_split_goal_3 modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
    | exact proof_of_mulmod_entail_wit_2_3_split_goal_4 modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17

theorem proof_of_mulmod_entail_wit_2_4_split_goal_1 : mulmod_entail_wit_2_4_split_goal_1 := by
  intro modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  simp only [p090_shiftl_one,p090_shiftr_one] at *
  have hw : unsigned_last_nbits (a*2) 64 = a*2 := p090_uint64 _ (by omega) (by omega)
  simp only [hw] at *
  simp only [land_one_mod_two__powmod_loop] at *
  have hmod0 := Int.fmod_nonneg_of_pos b (by omega : (0:Int) < 2)
  have hmod2 := Int.fmod_lt_of_pos b (by omega : (0:Int) < 2)
  have hdiv := Int.fmod_add_mul_fdiv b 2
  change b.fmod 2 + 2*(b /ᶻ 2) = b at hdiv
  unfold Z.modulo at *
  have hbit : b.fmod 2 = 1 := by omega
  rw [hbit] at hdiv
  apply p090_mul_step _ _ _ a b r _ _ _ (1)
  · assumption
  · nlinarith

theorem proof_of_mulmod_entail_wit_2_4_split_goal_2 : mulmod_entail_wit_2_4_split_goal_2 := by
  intro modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  simp only [p090_shiftl_one,p090_shiftr_one] at *
  have hw : unsigned_last_nbits (a*2) 64 = a*2 := p090_uint64 _ (by omega) (by omega)
  simp only [hw] at *
  have hq0 : 0 ≤ b /ᶻ 2 := Int.fdiv_nonneg (by omega) (by omega)
  have hqle : b /ᶻ 2 ≤ b := by
    change b.fdiv 2 ≤ b
    rw [Int.fdiv_eq_ediv_of_nonneg b (by omega)]
    exact Int.ediv_le_self 2 (by omega)
  omega

theorem proof_of_mulmod_entail_wit_2_4_split_goal_3 : mulmod_entail_wit_2_4_split_goal_3 := by
  intro modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  simp only [p090_shiftl_one,p090_shiftr_one] at *
  have hw : unsigned_last_nbits (a*2) 64 = a*2 := p090_uint64 _ (by omega) (by omega)
  simp only [hw] at *
  have hq0 : 0 ≤ b /ᶻ 2 := Int.fdiv_nonneg (by omega) (by omega)
  have hqle : b /ᶻ 2 ≤ b := by
    change b.fdiv 2 ≤ b
    rw [Int.fdiv_eq_ediv_of_nonneg b (by omega)]
    exact Int.ediv_le_self 2 (by omega)
  omega

theorem proof_of_mulmod_entail_wit_2_4_split_goal_4 : mulmod_entail_wit_2_4_split_goal_4 := by
  intro modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  simp only [p090_shiftl_one,p090_shiftr_one] at *
  have hw : unsigned_last_nbits (a*2) 64 = a*2 := p090_uint64 _ (by omega) (by omega)
  simp only [hw] at *
  have hq0 : 0 ≤ b /ᶻ 2 := Int.fdiv_nonneg (by omega) (by omega)
  have hqle : b /ᶻ 2 ≤ b := by
    change b.fdiv 2 ≤ b
    rw [Int.fdiv_eq_ediv_of_nonneg b (by omega)]
    exact Int.ediv_le_self 2 (by omega)
  omega

theorem proof_of_mulmod_entail_wit_2_4 : mulmod_entail_wit_2_4 := by
  unfold mulmod_entail_wit_2_4
  right
  intro modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_mulmod_entail_wit_2_4_split_goal_1 modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
    | exact proof_of_mulmod_entail_wit_2_4_split_goal_2 modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
    | exact proof_of_mulmod_entail_wit_2_4_split_goal_3 modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
    | exact proof_of_mulmod_entail_wit_2_4_split_goal_4 modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18

theorem proof_of_mulmod_entail_wit_2_5_split_goal_1 : mulmod_entail_wit_2_5_split_goal_1 := by
  intro modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  simp only [p090_shiftl_one,p090_shiftr_one] at *
  have hw : unsigned_last_nbits (a*2) 64 = a*2 := p090_uint64 _ (by omega) (by omega)
  simp only [hw] at *
  simp only [land_one_mod_two__powmod_loop] at *
  have hmod0 := Int.fmod_nonneg_of_pos b (by omega : (0:Int) < 2)
  have hmod2 := Int.fmod_lt_of_pos b (by omega : (0:Int) < 2)
  have hdiv := Int.fmod_add_mul_fdiv b 2
  change b.fmod 2 + 2*(b /ᶻ 2) = b at hdiv
  unfold Z.modulo at *
  have hbit : b.fmod 2 = 1 := by omega
  rw [hbit] at hdiv
  apply p090_mul_step _ _ _ a b r _ _ _ (0)
  · assumption
  · nlinarith

theorem proof_of_mulmod_entail_wit_2_5_split_goal_2 : mulmod_entail_wit_2_5_split_goal_2 := by
  intro modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  simp only [p090_shiftl_one,p090_shiftr_one] at *
  have hw : unsigned_last_nbits (a*2) 64 = a*2 := p090_uint64 _ (by omega) (by omega)
  simp only [hw] at *
  have hq0 : 0 ≤ b /ᶻ 2 := Int.fdiv_nonneg (by omega) (by omega)
  have hqle : b /ᶻ 2 ≤ b := by
    change b.fdiv 2 ≤ b
    rw [Int.fdiv_eq_ediv_of_nonneg b (by omega)]
    exact Int.ediv_le_self 2 (by omega)
  omega

theorem proof_of_mulmod_entail_wit_2_5_split_goal_3 : mulmod_entail_wit_2_5_split_goal_3 := by
  intro modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  simp only [p090_shiftl_one,p090_shiftr_one] at *
  have hw : unsigned_last_nbits (a*2) 64 = a*2 := p090_uint64 _ (by omega) (by omega)
  simp only [hw] at *
  have hq0 : 0 ≤ b /ᶻ 2 := Int.fdiv_nonneg (by omega) (by omega)
  have hqle : b /ᶻ 2 ≤ b := by
    change b.fdiv 2 ≤ b
    rw [Int.fdiv_eq_ediv_of_nonneg b (by omega)]
    exact Int.ediv_le_self 2 (by omega)
  omega

theorem proof_of_mulmod_entail_wit_2_5_split_goal_4 : mulmod_entail_wit_2_5_split_goal_4 := by
  intro modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  simp only [p090_shiftl_one,p090_shiftr_one] at *
  have hw : unsigned_last_nbits (a*2) 64 = a*2 := p090_uint64 _ (by omega) (by omega)
  simp only [hw] at *
  have hq0 : 0 ≤ b /ᶻ 2 := Int.fdiv_nonneg (by omega) (by omega)
  have hqle : b /ᶻ 2 ≤ b := by
    change b.fdiv 2 ≤ b
    rw [Int.fdiv_eq_ediv_of_nonneg b (by omega)]
    exact Int.ediv_le_self 2 (by omega)
  omega

theorem proof_of_mulmod_entail_wit_2_5 : mulmod_entail_wit_2_5 := by
  unfold mulmod_entail_wit_2_5
  right
  intro modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_mulmod_entail_wit_2_5_split_goal_1 modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
    | exact proof_of_mulmod_entail_wit_2_5_split_goal_2 modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
    | exact proof_of_mulmod_entail_wit_2_5_split_goal_3 modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
    | exact proof_of_mulmod_entail_wit_2_5_split_goal_4 modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18

theorem proof_of_mulmod_entail_wit_2_6_split_goal_1 : mulmod_entail_wit_2_6_split_goal_1 := by
  intro modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  simp only [p090_shiftl_one,p090_shiftr_one] at *
  have hw : unsigned_last_nbits (a*2) 64 = a*2 := p090_uint64 _ (by omega) (by omega)
  simp only [hw] at *
  simp only [land_one_mod_two__powmod_loop] at *
  have hmod0 := Int.fmod_nonneg_of_pos b (by omega : (0:Int) < 2)
  have hmod2 := Int.fmod_lt_of_pos b (by omega : (0:Int) < 2)
  have hdiv := Int.fmod_add_mul_fdiv b 2
  change b.fmod 2 + 2*(b /ᶻ 2) = b at hdiv
  unfold Z.modulo at *
  have hbit : b.fmod 2 = 0 := by omega
  rw [hbit] at hdiv
  apply p090_mul_step _ _ _ a b r _ _ _ (0)
  · assumption
  · nlinarith

theorem proof_of_mulmod_entail_wit_2_6_split_goal_2 : mulmod_entail_wit_2_6_split_goal_2 := by
  intro modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  simp only [p090_shiftl_one,p090_shiftr_one] at *
  have hw : unsigned_last_nbits (a*2) 64 = a*2 := p090_uint64 _ (by omega) (by omega)
  simp only [hw] at *
  have hq0 : 0 ≤ b /ᶻ 2 := Int.fdiv_nonneg (by omega) (by omega)
  have hqle : b /ᶻ 2 ≤ b := by
    change b.fdiv 2 ≤ b
    rw [Int.fdiv_eq_ediv_of_nonneg b (by omega)]
    exact Int.ediv_le_self 2 (by omega)
  omega

theorem proof_of_mulmod_entail_wit_2_6_split_goal_3 : mulmod_entail_wit_2_6_split_goal_3 := by
  intro modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  simp only [p090_shiftl_one,p090_shiftr_one] at *
  have hw : unsigned_last_nbits (a*2) 64 = a*2 := p090_uint64 _ (by omega) (by omega)
  simp only [hw] at *
  have hq0 : 0 ≤ b /ᶻ 2 := Int.fdiv_nonneg (by omega) (by omega)
  have hqle : b /ᶻ 2 ≤ b := by
    change b.fdiv 2 ≤ b
    rw [Int.fdiv_eq_ediv_of_nonneg b (by omega)]
    exact Int.ediv_le_self 2 (by omega)
  omega

theorem proof_of_mulmod_entail_wit_2_6_split_goal_4 : mulmod_entail_wit_2_6_split_goal_4 := by
  intro modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  simp only [p090_shiftl_one,p090_shiftr_one] at *
  have hw : unsigned_last_nbits (a*2) 64 = a*2 := p090_uint64 _ (by omega) (by omega)
  simp only [hw] at *
  have hq0 : 0 ≤ b /ᶻ 2 := Int.fdiv_nonneg (by omega) (by omega)
  have hqle : b /ᶻ 2 ≤ b := by
    change b.fdiv 2 ≤ b
    rw [Int.fdiv_eq_ediv_of_nonneg b (by omega)]
    exact Int.ediv_le_self 2 (by omega)
  omega

theorem proof_of_mulmod_entail_wit_2_6 : mulmod_entail_wit_2_6 := by
  unfold mulmod_entail_wit_2_6
  right
  intro modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_mulmod_entail_wit_2_6_split_goal_1 modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
    | exact proof_of_mulmod_entail_wit_2_6_split_goal_2 modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
    | exact proof_of_mulmod_entail_wit_2_6_split_goal_3 modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
    | exact proof_of_mulmod_entail_wit_2_6_split_goal_4 modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17

theorem proof_of_mulmod_return_wit_1_split_goal_1 : mulmod_return_wit_1_split_goal_1 := by
  intro modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have hb : b = 0 := by omega
  unfold MulLoopState at PreH14
  rw [hb,mul_zero,add_zero] at PreH14
  have hr : r mod modulus_pre = r := Int.fmod_eq_of_lt (by omega) (by omega)
  rw [hr] at PreH14
  have hprod : 0 ≤ a_pre*b_pre := mul_nonneg (by omega) (by omega)
  rw [show Z.rem (a_pre*b_pre) modulus_pre = (a_pre*b_pre) mod modulus_pre from
    (Int.fmod_eq_tmod_of_nonneg hprod (by omega)).symm]
  exact PreH14

theorem proof_of_mulmod_return_wit_1 : mulmod_return_wit_1 := by
  unfold mulmod_return_wit_1
  right
  intro modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_mulmod_return_wit_1_split_goal_1 modulus_pre b_pre a_pre modulus0 b0 a0 r b a PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_proof_manual
