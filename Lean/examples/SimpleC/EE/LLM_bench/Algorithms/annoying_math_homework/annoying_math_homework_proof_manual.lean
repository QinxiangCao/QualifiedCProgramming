import SimpleC.EE.LLM_bench.Algorithms.annoying_math_homework.annoying_math_homework_goal
import SimpleC.EE.LLM_bench.Algorithms.annoying_math_homework.annoying_math_homework_proof_auto

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.annoying_math_homework.annoying_math_homework_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open SimpleC.EE.LLM_bench
open annoying_math_homework_goal annoying_math_homework_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray

private theorem mod_bounds (x : Int) :
    0 ≤ Z.modulo x digit_sum_modulus ∧ Z.modulo x digit_sum_modulus < digit_sum_modulus :=
  ⟨Int.fmod_nonneg_of_pos _ (by decide), Int.fmod_lt_of_pos _ (by decide)⟩
private theorem dp_bounds (p d : Int) : 0 ≤ DigitDPValue p d ∧ DigitDPValue p d < digit_sum_modulus := by
  unfold DigitDPValue
  split <;> exact mod_bounds _
private theorem signed_mod (x : Int) : signed_last_nbits (Z.modulo x 1000000007) 32 = Z.modulo x 1000000007 := by
  apply signed_last_nbits_small _ 32 (by decide)
  have hb := mod_bounds x
  change 0 ≤ _ ∧ _ < 2147483648
  unfold digit_sum_modulus at hb
  omega
private theorem pow_step (a n : Int) (hn : 0 ≤ n) : Z.pow a (n+1) = Z.pow a n * a := by
  cases n with
  | ofNat n => exact Int.pow_succ a n
  | negSucc n => omega
private theorem pow10_pos (n : Int) (hn : 0 ≤ n) : 0 < Z.pow 10 n := by
  cases n with
  | ofNat n => exact Int.pow_pos (by decide : (0 : Int) < 10)
  | negSucc n => omega

private theorem pow10_bound (n : Int) (k : Nat) (hn : 0 ≤ n) (hk : n ≤ (k : Int)) : Z.pow 10 n ≤ Z.pow 10 (k : Int) := by
  cases n with
  | ofNat n =>
    simp only [Int.ofNat_eq_coe] at hk
    have h := Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide : 0 < 10) (show n ≤ k by omega))
    simpa only [Int.natCast_pow] using h
  | negSucc n => omega
private theorem outer_power_pos (i p : Int) (hi : 1 ≤ i) (hp : OuterDigitPositionPower i p) : 0 < p := by
  rcases hp with ⟨hz, _⟩ | ⟨hr, he⟩
  · omega
  · rw [he]; exact pow10_pos (i-1) (by omega)
private theorem digit_sum_program_answer (x p ans before choice digit : Int)
    (hx : 0 ≤ x) (hp : 0 < p) (ha : 0 ≤ ans)
    (hd : digit = Z.modulo (Z.div x p) 10)
    (he : ans = Z.modulo (before+choice) digit_sum_modulus) :
    signed_last_nbits (Z.rem (ans+Z.rem (Z.rem (Z.rem x p+1) 1000000007 * Z.rem (Z.quot x p) 10) 1000000007) 1000000007) 32 =
      Z.modulo (before+choice+Z.modulo (Z.modulo x p+1) digit_sum_modulus * digit) digit_sum_modulus := by
  have hquot : Z.quot x p = Z.div x p := (Int.fdiv_eq_tdiv_of_nonneg hx (by omega)).symm
  have hdiv : 0 ≤ Z.div x p := Int.fdiv_nonneg hx (by omega)
  have hmod : 0 ≤ Z.modulo x p := Int.fmod_nonneg_of_pos _ hp
  have hlow := mod_bounds (Z.modulo x p+1)
  have hd0 : 0 ≤ digit := by rw [hd]; exact Int.fmod_nonneg_of_pos _ (by decide)
  rw [rem_eq_mod x p hx hp, hquot, rem_eq_mod _ 10 hdiv (by decide),
    rem_eq_mod (Z.modulo x p+1) 1000000007 (by omega) (by decide), ← hd]
  have hprod : 0 ≤ Z.modulo (Z.modulo x p+1) 1000000007 * digit := Int.mul_nonneg hlow.1 hd0
  rw [rem_eq_mod _ 1000000007 hprod (by decide)]
  have hm := mod_bounds (Z.modulo (Z.modulo x p+1) 1000000007 * digit)
  rw [rem_eq_mod _ 1000000007 (by unfold digit_sum_modulus at hm; omega) (by decide), signed_mod, he]
  unfold digit_sum_modulus Z.modulo
  rw [Int.fmod_add_fmod, Int.add_fmod_fmod]

-- Previously proved auxiliary statements retained for proof audits.
private theorem zero_annotation (l : List Int) (hi total : Int)
    (hlen : Zlength l = hi) (hb : 0 ≤ hi ∧ hi ≤ total)
    (hz : Forall (Eq (0 : Int)) l) : ZeroSegment l hi total := by
  refine ⟨hlen, hb, ?_⟩
  intro k hk
  have hn : k.toNat < l.length := by
    change (l.length : Int) = hi at hlen
    omega
  have hh := hz.mem (List.getElem_mem (l := l) hn)
  have he : 0 = Znth k l 0 := by
    simpa only [Znth, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some] using hh
  exact he.symm

private theorem zero_annotation_back (l : List Int) (hi total : Int)
    (hz : ZeroSegment l hi total) : Forall (Eq (0 : Int)) l := by
  apply Forall.iff_forall_mem.mpr
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx
  have hr : 0 ≤ (k : Int) ∧ (k : Int) < hi := by
    have he : (l.length : Int) = hi := hz.1
    omega
  have hh := (hz.2.2 k hr).symm
  simpa only [Znth, Int.toNat_natCast, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some] using hh

theorem proof_of_digits_sum_init_safety_wit_8_split_goal_1 : digits_sum_init_safety_wit_8_split_goal_1 := by
  unfold digits_sum_init_safety_wit_8_split_goal_1
  intro dp_pre power_pre power_l i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH4 : (PowerPrefix power_l i) := NewPreH5
    dump_pre_spatial
    have hv := PreH4.2.2 (i-1-0) (by omega)
    have hb := mod_bounds (Z.pow 10 (i-1-0))
    unfold digit_sum_modulus at *
    omega

theorem proof_of_digits_sum_init_safety_wit_8_split_goal_2 : digits_sum_init_safety_wit_8_split_goal_2 := by
  unfold digits_sum_init_safety_wit_8_split_goal_2
  intro dp_pre power_pre power_l i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH4 : (PowerPrefix power_l i) := NewPreH5
    dump_pre_spatial
    have hv := PreH4.2.2 (i-1-0) (by omega)
    have hb := mod_bounds (Z.pow 10 (i-1-0))
    unfold digit_sum_modulus at *
    omega

theorem proof_of_digits_sum_init_safety_wit_8 : digits_sum_init_safety_wit_8 := by
  unfold digits_sum_init_safety_wit_8
  right
  intro dp_pre power_pre power_l i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5
  have PreH1 : (i < 20) := NewPreH1
  have PreH2 : (1 <= i) := NewPreH2
  have PreH3 : (i <= 20) := NewPreH3
  have PreH4 : (PowerPrefix power_l i) := NewPreH5
  split_pures
  all_goals first
    | assumption
    | omega
    | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
    | exact proof_of_digits_sum_init_safety_wit_8_split_goal_1 dp_pre power_pre power_l i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5
    | exact proof_of_digits_sum_init_safety_wit_8_split_goal_2 dp_pre power_pre power_l i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5


theorem proof_of_digits_sum_init_safety_wit_36_split_goal_1 : digits_sum_init_safety_wit_36_split_goal_1 := by
  unfold digits_sum_init_safety_wit_36_split_goal_1
  intro dp_pre power_pre power_l dp_l k j i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH1 : (k < 10) := NewPreH1
    have PreH2 : (2 <= i) := NewPreH2
    have PreH3 : (i < 20) := NewPreH3
    have PreH4 : ((0 : Int) <= j) := NewPreH4
    have PreH5 : (j < 10) := NewPreH5
    have PreH6 : ((0 : Int) <= k) := NewPreH6
    have PreH7 : (k <= 10) := NewPreH7
    have PreH8 : (DigitDPCellProgress dp_l i j k) := NewPreH9
    have dp_length := PreH8.1
    have PreH9 : (PowerTable power_l) := NewPreH10
    dump_pre_spatial
    have hb := digits_dp_previous_term_bounds__digits_dp_cell power_l dp_l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
    omega

theorem proof_of_digits_sum_init_safety_wit_36_split_goal_2 : digits_sum_init_safety_wit_36_split_goal_2 := by
  unfold digits_sum_init_safety_wit_36_split_goal_2
  intro dp_pre power_pre power_l dp_l k j i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH1 : (k < 10) := NewPreH1
    have PreH2 : (2 <= i) := NewPreH2
    have PreH3 : (i < 20) := NewPreH3
    have PreH4 : ((0 : Int) <= j) := NewPreH4
    have PreH5 : (j < 10) := NewPreH5
    have PreH6 : ((0 : Int) <= k) := NewPreH6
    have PreH7 : (k <= 10) := NewPreH7
    have PreH8 : (DigitDPCellProgress dp_l i j k) := NewPreH9
    have dp_length := PreH8.1
    have PreH9 : (PowerTable power_l) := NewPreH10
    dump_pre_spatial
    have hb := digits_dp_previous_term_bounds__digits_dp_cell power_l dp_l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
    omega

theorem proof_of_digits_sum_init_safety_wit_36 : digits_sum_init_safety_wit_36 := by
  unfold digits_sum_init_safety_wit_36
  right
  intro dp_pre power_pre power_l dp_l k j i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10
  have PreH1 : (k < 10) := NewPreH1
  have PreH2 : (2 <= i) := NewPreH2
  have PreH3 : (i < 20) := NewPreH3
  have PreH4 : ((0 : Int) <= j) := NewPreH4
  have PreH5 : (j < 10) := NewPreH5
  have PreH6 : ((0 : Int) <= k) := NewPreH6
  have PreH7 : (k <= 10) := NewPreH7
  have PreH8 : (DigitDPCellProgress dp_l i j k) := NewPreH9
  have dp_length := PreH8.1
  have PreH9 : (PowerTable power_l) := NewPreH10
  split_pures
  all_goals first
    | assumption
    | omega
    | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
    | exact proof_of_digits_sum_init_safety_wit_36_split_goal_1 dp_pre power_pre power_l dp_l k j i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10
    | exact proof_of_digits_sum_init_safety_wit_36_split_goal_2 dp_pre power_pre power_l dp_l k j i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10


theorem proof_of_digits_sum_init_safety_wit_38_split_goal_1 : digits_sum_init_safety_wit_38_split_goal_1 := by
  unfold digits_sum_init_safety_wit_38_split_goal_1
  intro dp_pre power_pre power_l dp_l k j i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH4 : ((0 : Int) <= j) := NewPreH4
    have PreH9 : (PowerTable power_l) := NewPreH10
    dump_pre_spatial
    have hv := PreH9.2 (i-2) (by omega)
    have hb := mod_bounds (Z.pow 10 (i-2))
    have hp0 := Int.mul_nonneg (show 0 ≤ Znth (i-2) power_l 0 by omega) PreH4
    have hp1 := Int.mul_le_mul_of_nonneg_left (show j ≤ 10 by omega) (show 0 ≤ Znth (i-2) power_l 0 by omega)
    unfold digit_sum_modulus at *
    omega

theorem proof_of_digits_sum_init_safety_wit_38_split_goal_2 : digits_sum_init_safety_wit_38_split_goal_2 := by
  unfold digits_sum_init_safety_wit_38_split_goal_2
  intro dp_pre power_pre power_l dp_l k j i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH4 : ((0 : Int) <= j) := NewPreH4
    have PreH9 : (PowerTable power_l) := NewPreH10
    dump_pre_spatial
    have hv := PreH9.2 (i-2) (by omega)
    have hb := mod_bounds (Z.pow 10 (i-2))
    have hp0 := Int.mul_nonneg (show 0 ≤ Znth (i-2) power_l 0 by omega) PreH4
    have hp1 := Int.mul_le_mul_of_nonneg_left (show j ≤ 10 by omega) (show 0 ≤ Znth (i-2) power_l 0 by omega)
    unfold digit_sum_modulus at *
    omega

theorem proof_of_digits_sum_init_safety_wit_38 : digits_sum_init_safety_wit_38 := by
  unfold digits_sum_init_safety_wit_38
  right
  intro dp_pre power_pre power_l dp_l k j i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10
  have PreH1 : (k < 10) := NewPreH1
  have PreH2 : (2 <= i) := NewPreH2
  have PreH3 : (i < 20) := NewPreH3
  have PreH4 : ((0 : Int) <= j) := NewPreH4
  have PreH5 : (j < 10) := NewPreH5
  have PreH6 : ((0 : Int) <= k) := NewPreH6
  have PreH7 : (k <= 10) := NewPreH7
  have PreH8 : (DigitDPCellProgress dp_l i j k) := NewPreH9
  have dp_length := PreH8.1
  have PreH9 : (PowerTable power_l) := NewPreH10
  split_pures
  all_goals first
    | assumption
    | omega
    | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
    | exact proof_of_digits_sum_init_safety_wit_38_split_goal_1 dp_pre power_pre power_l dp_l k j i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10
    | exact proof_of_digits_sum_init_safety_wit_38_split_goal_2 dp_pre power_pre power_l dp_l k j i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10


theorem proof_of_digits_sum_init_safety_wit_47_split_goal_1 : digits_sum_init_safety_wit_47_split_goal_1 := by
  unfold digits_sum_init_safety_wit_47_split_goal_1
  intro dp_pre power_pre power_l dp_l k j i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH1 : (k < 10) := NewPreH1
    have PreH2 : (2 <= i) := NewPreH2
    have PreH3 : (i < 20) := NewPreH3
    have PreH4 : ((0 : Int) <= j) := NewPreH4
    have PreH5 : (j < 10) := NewPreH5
    have PreH6 : ((0 : Int) <= k) := NewPreH6
    have PreH7 : (k <= 10) := NewPreH7
    have PreH8 : (DigitDPCellProgress dp_l i j k) := NewPreH9
    have dp_length := PreH8.1
    have PreH9 : (PowerTable power_l) := NewPreH10
    dump_pre_spatial
    have hb := digits_dp_current_plus_moving_bounds__digits_dp_cell power_l dp_l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
    omega

theorem proof_of_digits_sum_init_safety_wit_47_split_goal_2 : digits_sum_init_safety_wit_47_split_goal_2 := by
  unfold digits_sum_init_safety_wit_47_split_goal_2
  intro dp_pre power_pre power_l dp_l k j i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH1 : (k < 10) := NewPreH1
    have PreH2 : (2 <= i) := NewPreH2
    have PreH3 : (i < 20) := NewPreH3
    have PreH4 : ((0 : Int) <= j) := NewPreH4
    have PreH5 : (j < 10) := NewPreH5
    have PreH6 : ((0 : Int) <= k) := NewPreH6
    have PreH7 : (k <= 10) := NewPreH7
    have PreH8 : (DigitDPCellProgress dp_l i j k) := NewPreH9
    have dp_length := PreH8.1
    have PreH9 : (PowerTable power_l) := NewPreH10
    dump_pre_spatial
    have hb := digits_dp_current_plus_moving_bounds__digits_dp_cell power_l dp_l k j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
    omega

theorem proof_of_digits_sum_init_safety_wit_47 : digits_sum_init_safety_wit_47 := by
  unfold digits_sum_init_safety_wit_47
  right
  intro dp_pre power_pre power_l dp_l k j i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10
  have PreH1 : (k < 10) := NewPreH1
  have PreH2 : (2 <= i) := NewPreH2
  have PreH3 : (i < 20) := NewPreH3
  have PreH4 : ((0 : Int) <= j) := NewPreH4
  have PreH5 : (j < 10) := NewPreH5
  have PreH6 : ((0 : Int) <= k) := NewPreH6
  have PreH7 : (k <= 10) := NewPreH7
  have PreH8 : (DigitDPCellProgress dp_l i j k) := NewPreH9
  have dp_length := PreH8.1
  have PreH9 : (PowerTable power_l) := NewPreH10
  split_pures
  all_goals first
    | assumption
    | omega
    | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
    | exact proof_of_digits_sum_init_safety_wit_47_split_goal_1 dp_pre power_pre power_l dp_l k j i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10
    | exact proof_of_digits_sum_init_safety_wit_47_split_goal_2 dp_pre power_pre power_l dp_l k j i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10


theorem proof_of_digits_sum_init_entail_wit_1 : digits_sum_init_entail_wit_1 := by
  unfold digits_sum_init_entail_wit_1
  right
  intro power_pre NewPreH1 NewPreH2
  have hp : PowerPrefix [1] 1 := by
    refine ⟨rfl, by decide, ?_⟩
    intro idx hi
    have he : idx = 0 := by omega
    subst idx
    rfl
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ([1] : List Int) ?_
  split_pure_spatial
  · exact intArray.seg_single power_pre 0 (1 : Int)
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | exact Forall.nil | omega | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega)) | assumption | omega


theorem proof_of_digits_sum_init_entail_wit_2_split_goal_1 : digits_sum_init_entail_wit_2_split_goal_1 := by
  unfold digits_sum_init_entail_wit_2_split_goal_1
  intro power_l_2 i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH4 : (PowerPrefix power_l_2 i) := NewPreH5
    simp only [Int.sub_zero]
    obtain ⟨hlen, hr, hp⟩ := PreH4
    have hb := mod_bounds (Z.pow 10 (i-1))
    have hn : 0 ≤ Znth (i-1) power_l_2 0 := by rw [hp _ (by omega)]; exact hb.1
    rw [rem_eq_mod _ 1000000007 (Int.mul_nonneg hn (by decide)) (by decide), signed_mod]
    refine ⟨by rw [Zlength_app, Zlength_cons, Zlength_nil, hlen]; omega, by omega, ?_⟩
    intro idx hi
    by_cases hlt : idx < i
    · rw [Znth_app_left__digits_power_and_zero_init power_l_2 _ 0 idx (by omega)]
      exact hp idx (by omega)
    · have he : idx = i := by omega
      subst idx
      have hh : Znth i (power_l_2 ++ [Z.modulo (Znth (i-1) power_l_2 0 * 10) 1000000007]) 0 = Z.modulo (Znth (i-1) power_l_2 0 * 10) 1000000007 := by
        rw [← hlen]
        exact Znth_app_last__digits_power_and_zero_init power_l_2 0 _
      rw [hh, hp _ (by omega)]
      have he : i = (i-1)+1 := by omega
      have hpow : Z.pow 10 i = Z.pow 10 (i-1)*10 := by simpa only [Int.sub_add_cancel] using pow_step 10 (i-1) (by omega)
      rw [hpow]
      unfold digit_sum_modulus Z.modulo
      rw [Int.mul_fmod, Int.fmod_fmod, ← Int.mul_fmod]

theorem proof_of_digits_sum_init_entail_wit_2 : digits_sum_init_entail_wit_2 := by
  unfold digits_sum_init_entail_wit_2
  right
  intro power_l_2 i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5
  have PreH1 : (i < 20) := NewPreH1
  have PreH2 : (1 <= i) := NewPreH2
  have PreH3 : (i <= 20) := NewPreH3
  have PreH4 : (PowerPrefix power_l_2 i) := NewPreH5
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | (solve | simp only [Zlength_replace_Znth]; omega)
      | omega
      | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
      | exact proof_of_digits_sum_init_entail_wit_2_split_goal_1 power_l_2 i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5


theorem proof_of_digits_sum_init_entail_wit_3 : digits_sum_init_entail_wit_3 := by
  unfold digits_sum_init_entail_wit_3
  right
  intro dp_pre power_l_2 i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5
  have PreH4 : (PowerPrefix power_l_2 i) := NewPreH5
  have hz : ZeroSegment [] 0 200 := ⟨rfl, by omega, fun k hk => by omega⟩
  have hp : PowerTable power_l_2 := ⟨by have := PreH4.1; omega, fun idx hi => PreH4.2.2 idx (by omega)⟩
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ([] : List Int) ?_
  simp only [Int.zero_mul]
  split_pure_spatial
  · have hemp : emp |-- intArray.seg dp_pre 0 0 [] := by
      refine naive_C_Rules.toContext.derivable1_trans _ ( “ ((0 : Int) = 0) ” && emp) _ ?_ (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp (intArray.seg_empty dp_pre 0 0)).2)
      split_pure_spatial
      · cancel
      · dump_pre_spatial; rfl
    refine naive_C_Rules.toContext.derivable1_trans _ (emp ** intArray.undef_seg dp_pre 0 200) _ ?_ ?_
    · change intArray.undef_seg dp_pre 0 200 |-- emp ** intArray.undef_seg dp_pre 0 200
      cancel
    · exact naive_C_Rules.toContext.derivable1_sepcon_mono _ _ _ _ hemp (naive_C_Rules.toContext.derivable1_refl _)
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | exact Forall.nil | omega | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega)) | assumption | omega


theorem proof_of_digits_sum_init_entail_wit_4 : digits_sum_init_entail_wit_4 := by
  unfold digits_sum_init_entail_wit_4
  right
  intro dp_pre power_l_2 dp_l_2 i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6
  simp only [Int.add_zero]
  Exists dp_l_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | exact Forall.nil | omega | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega)) | assumption | omega


theorem proof_of_digits_sum_init_entail_wit_5 : digits_sum_init_entail_wit_5 := by
  unfold digits_sum_init_entail_wit_5
  right
  intro dp_pre power_l_2 dp_l_2 j i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8
  have PreH6 : (ZeroSegment dp_l_2 ((i * 10) + j) 200) := zero_annotation dp_l_2 ((i * 10) + j) 200 NewPreH6 (by omega) NewPreH7
  rw [show i*10+(j+1) = i*10+j+1 by omega]
  have hz := ZeroSegment_app_zero__digits_power_and_zero_init dp_l_2 (i*10+j) 200 PreH6 (by omega)
  have zeros_forall := zero_annotation_back _ _ _ hz
  Exists (dp_l_2 ++ [0])
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | exact Forall.nil | omega | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega)) | assumption | omega


theorem proof_of_digits_sum_init_entail_wit_6 : digits_sum_init_entail_wit_6 := by
  unfold digits_sum_init_entail_wit_6
  right
  intro dp_pre power_l_2 dp_l_2 j i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8
  have he : (i+1)*10 = i*10+j := by omega
  rw [he]
  Exists dp_l_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | exact Forall.nil | omega | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega)) | assumption | omega


theorem proof_of_digits_sum_init_entail_wit_7_split_goal_1 : digits_sum_init_entail_wit_7_split_goal_1 := by
  unfold digits_sum_init_entail_wit_7_split_goal_1
  intro power_l_2 dp_l_2 i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH4 : (ZeroSegment dp_l_2 (i * 10) 200) := zero_annotation dp_l_2 (i * 10) 200 NewPreH4 (by omega) NewPreH5
    obtain ⟨hlen, hr, hz⟩ := PreH4
    exact ⟨by omega, by omega, (fun j hj => by omega), fun k hk _ => hz k (by omega)⟩

theorem proof_of_digits_sum_init_entail_wit_7 : digits_sum_init_entail_wit_7 := by
  unfold digits_sum_init_entail_wit_7
  right
  intro power_l_2 dp_l_2 i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6
  have PreH1 : (i >= 20) := NewPreH1
  have PreH2 : ((0 : Int) <= i) := NewPreH2
  have PreH3 : (i <= 20) := NewPreH3
  have PreH4 : (ZeroSegment dp_l_2 (i * 10) 200) := zero_annotation dp_l_2 (i * 10) 200 NewPreH4 (by omega) NewPreH5
  have PreH5 : (PowerTable power_l_2) := NewPreH6
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | (solve | simp only [Zlength_replace_Znth]; omega)
      | omega
      | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
      | exact proof_of_digits_sum_init_entail_wit_7_split_goal_1 power_l_2 dp_l_2 i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6


theorem proof_of_digits_sum_init_entail_wit_8_split_goal_1 : digits_sum_init_entail_wit_8_split_goal_1 := by
  unfold digits_sum_init_entail_wit_8_split_goal_1
  intro power_l_2 dp_l_2 j NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH4 : (DigitDPBaseProgress dp_l_2 j) := NewPreH5
    have dp_length := PreH4.1
    obtain ⟨hlen, hr, hold, hzero⟩ := PreH4
    refine ⟨by simpa only [Zlength_replace_Znth] using hlen, by omega, ?_, ?_⟩
    · intro d hd
      by_cases he : d = j
      · subst d; exact Znth_replace_Znth_Same 0 dp_l_2 _ _ (by omega)
      · rw [Znth_replace_Znth_Diff 0 dp_l_2 (10+j) (10+d) j (by omega) (by omega) (by omega)]
        exact hold d (by omega)
    · intro idx hi hz
      rw [Znth_replace_Znth_Diff 0 dp_l_2 (10+j) idx j (by omega) (by omega) (by omega)]
      exact hzero idx hi (by omega)

theorem proof_of_digits_sum_init_entail_wit_8 : digits_sum_init_entail_wit_8 := by
  unfold digits_sum_init_entail_wit_8
  right
  intro power_l_2 dp_l_2 j NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6
  have PreH1 : (j < 10) := NewPreH1
  have PreH2 : ((0 : Int) <= j) := NewPreH2
  have PreH3 : (j <= 10) := NewPreH3
  have PreH4 : (DigitDPBaseProgress dp_l_2 j) := NewPreH5
  have dp_length := PreH4.1
  have PreH5 : (PowerTable power_l_2) := NewPreH6
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | (solve | simp only [Zlength_replace_Znth]; omega)
      | omega
      | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
      | exact proof_of_digits_sum_init_entail_wit_8_split_goal_1 power_l_2 dp_l_2 j NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6


theorem proof_of_digits_sum_init_entail_wit_9_split_goal_1 : digits_sum_init_entail_wit_9_split_goal_1 := by
  unfold digits_sum_init_entail_wit_9_split_goal_1
  intro power_l_2 dp_l_2 j NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH4 : (DigitDPBaseProgress dp_l_2 j) := NewPreH5
    have dp_length := PreH4.1
    obtain ⟨hlen, hr, hold, hz⟩ := PreH4
    refine ⟨hlen, by decide, (fun d hd => hz d (by omega) (by omega)), ?_, ?_⟩
    · intro p d hp hd
      have he : p = 1 := by omega
      subst p
      change Znth (10+d) dp_l_2 0 = DigitDPValue 1 d
      rw [hold d (by omega)]
      change d = Z.modulo d digit_sum_modulus
      exact (Int.fmod_eq_of_lt hd.1 (by unfold digit_sum_modulus; omega)).symm
    · intro p d hp hd
      exact hz (p*10+d) (by omega) (by omega)

theorem proof_of_digits_sum_init_entail_wit_9 : digits_sum_init_entail_wit_9 := by
  unfold digits_sum_init_entail_wit_9
  right
  intro power_l_2 dp_l_2 j NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6
  have PreH1 : (j >= 10) := NewPreH1
  have PreH2 : ((0 : Int) <= j) := NewPreH2
  have PreH3 : (j <= 10) := NewPreH3
  have PreH4 : (DigitDPBaseProgress dp_l_2 j) := NewPreH5
  have dp_length := PreH4.1
  have PreH5 : (PowerTable power_l_2) := NewPreH6
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | (solve | simp only [Zlength_replace_Znth]; omega)
      | omega
      | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
      | exact proof_of_digits_sum_init_entail_wit_9_split_goal_1 power_l_2 dp_l_2 j NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6


theorem proof_of_digits_sum_init_entail_wit_10_split_goal_1 : digits_sum_init_entail_wit_10_split_goal_1 := by
  unfold digits_sum_init_entail_wit_10_split_goal_1
  intro power_l_2 dp_l_2 i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH4 : (DigitDPOuterProgress dp_l_2 i) := NewPreH5
    obtain ⟨hlen, hr, hbase, hprev, hz⟩ := PreH4
    exact ⟨hlen, by omega, by omega, hbase, hprev, (fun d hd => by omega), (fun d hd => hz i d (by omega) hd), fun p d hp hd => hz p d (by omega) hd⟩

theorem proof_of_digits_sum_init_entail_wit_10 : digits_sum_init_entail_wit_10 := by
  unfold digits_sum_init_entail_wit_10
  right
  intro power_l_2 dp_l_2 i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6
  have PreH1 : (i < 20) := NewPreH1
  have PreH2 : (2 <= i) := NewPreH2
  have PreH3 : (i <= 20) := NewPreH3
  have PreH4 : (DigitDPOuterProgress dp_l_2 i) := NewPreH5
  have PreH5 : (PowerTable power_l_2) := NewPreH6
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | (solve | simp only [Zlength_replace_Znth]; omega)
      | omega
      | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
      | exact proof_of_digits_sum_init_entail_wit_10_split_goal_1 power_l_2 dp_l_2 i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6


theorem proof_of_digits_sum_init_entail_wit_11_split_goal_1 : digits_sum_init_entail_wit_11_split_goal_1 := by
  unfold digits_sum_init_entail_wit_11_split_goal_1
  intro power_l_2 dp_l_2 j i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH6 : (DigitDPRowProgress dp_l_2 i j) := NewPreH7
    obtain ⟨hlen, hr, hj, hbase, hprev, hdone, hz, hlater⟩ := PreH6
    refine ⟨hlen, hr, by omega, by decide, hbase, hprev, hdone, (fun d hd => hz d (by omega)), hlater, 0, InnerCandidateDigitSum_zero dp_l_2 (i-1), ?_⟩
    simp only [Int.zero_mul, Int.add_zero, Z.modulo, Int.zero_fmod]
    exact hz j (by omega)

theorem proof_of_digits_sum_init_entail_wit_11 : digits_sum_init_entail_wit_11 := by
  unfold digits_sum_init_entail_wit_11
  right
  intro power_l_2 dp_l_2 j i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8
  have PreH1 : (j < 10) := NewPreH1
  have PreH2 : (2 <= i) := NewPreH2
  have PreH3 : (i < 20) := NewPreH3
  have PreH4 : ((0 : Int) <= j) := NewPreH4
  have PreH5 : (j <= 10) := NewPreH5
  have PreH6 : (DigitDPRowProgress dp_l_2 i j) := NewPreH7
  have PreH7 : (PowerTable power_l_2) := NewPreH8
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | (solve | simp only [Zlength_replace_Znth]; omega)
      | omega
      | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
      | exact proof_of_digits_sum_init_entail_wit_11_split_goal_1 power_l_2 dp_l_2 j i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8


theorem proof_of_digits_sum_init_entail_wit_12_split_goal_1 : digits_sum_init_entail_wit_12_split_goal_1 := by
  unfold digits_sum_init_entail_wit_12_split_goal_1
  intro power_l_2 dp_l_2 k j i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH4 : ((0 : Int) <= j) := NewPreH4
    have PreH6 : ((0 : Int) <= k) := NewPreH6
    have PreH8 : (DigitDPCellProgress dp_l_2 i j k) := NewPreH9
    have dp_length := PreH8.1
    have PreH9 : (PowerTable power_l_2) := NewPreH10
    obtain ⟨hlen, hp, hj, hk, hbase, hprev, hdone, hz, hlater, part, hinner, hcell⟩ := PreH8
    have hpower := PreH9.2 (i-2) (by omega)
    have hbpower := mod_bounds (Z.pow 10 (i-2))
    have hbprev := dp_bounds (i-1) k
    have hbcell := mod_bounds (part + k * Z.pow 10 (i-2) * j)
    have hprevEq := hprev (i-1) k (by omega) (by omega)
    have hprod : 0 ≤ Znth (i-2) power_l_2 0 * j := Int.mul_nonneg (by omega) PreH4
    rw [rem_eq_mod _ 1000000007 hprod (by decide)]
    have hinnerMod := mod_bounds (Znth (i-2) power_l_2 0 * j)
    rw [rem_eq_mod (Znth ((i-1)*10+k) dp_l_2 0 + Z.modulo (Znth (i-2) power_l_2 0*j) 1000000007) 1000000007 (by unfold digit_sum_modulus at *; omega) (by decide)]
    have hmiddle := mod_bounds (Znth ((i-1)*10+k) dp_l_2 0 + Z.modulo (Znth (i-2) power_l_2 0*j) 1000000007)
    rw [rem_eq_mod _ 1000000007 (by unfold digit_sum_modulus at *; omega) (by decide), signed_mod]
    let cell := Z.modulo (Znth (i*10+j) dp_l_2 0 + Z.modulo (Znth ((i-1)*10+k) dp_l_2 0 + Z.modulo (Znth (i-2) power_l_2 0*j) 1000000007) 1000000007) 1000000007
    change DigitDPCellProgress (replace_Znth (i*10+j) cell dp_l_2) i j (k+1)
    refine ⟨by simpa only [Zlength_replace_Znth] using hlen, hp, hj, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro d hd
      rw [Znth_replace_Znth_Diff 0 dp_l_2 (i*10+j) d cell (by omega) (by omega) (by omega)]
      exact hbase d hd
    · intro p d hpr hd
      rw [Znth_replace_Znth_Diff 0 dp_l_2 (i*10+j) (p*10+d) cell (by omega) (by omega) (by omega)]
      exact hprev p d hpr hd
    · intro d hd
      rw [Znth_replace_Znth_Diff 0 dp_l_2 (i*10+j) (i*10+d) cell (by omega) (by omega) (by omega)]
      exact hdone d hd
    · intro d hd
      rw [Znth_replace_Znth_Diff 0 dp_l_2 (i*10+j) (i*10+d) cell (by omega) (by omega) (by omega)]
      exact hz d hd
    · intro p d hpr hd
      rw [Znth_replace_Znth_Diff 0 dp_l_2 (i*10+j) (p*10+d) cell (by omega) (by omega) (by omega)]
      exact hlater p d hpr hd
    · refine ⟨Z.modulo (part+Znth ((i-1)*10+k) dp_l_2 0) digit_sum_modulus, ?_, ?_⟩
      · rw [← Znth_replace_Znth_Diff 0 dp_l_2 (i*10+j) ((i-1)*10+k) cell (by omega) (by omega) (by omega)]
        apply InnerCandidateDigitSum_step _ _ _ _ PreH6
        exact InnerCandidateDigitSum_replace_other__digits_dp_cell dp_l_2 (i-1) k part (i*10+j) cell (by omega) (by intro d hd; constructor <;> omega) hinner
      · rw [Znth_replace_Znth_Same 0 dp_l_2 (i*10+j) cell (by omega)]
        dsimp only [cell]
        rw [hcell, hpower]
        exact digit_dp_cell_mod_update__digits_dp_cell part _ (Z.pow 10 (i-2)) k j digit_sum_modulus (by decide)

theorem proof_of_digits_sum_init_entail_wit_12 : digits_sum_init_entail_wit_12 := by
  unfold digits_sum_init_entail_wit_12
  right
  intro power_l_2 dp_l_2 k j i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10
  have PreH1 : (k < 10) := NewPreH1
  have PreH2 : (2 <= i) := NewPreH2
  have PreH3 : (i < 20) := NewPreH3
  have PreH4 : ((0 : Int) <= j) := NewPreH4
  have PreH5 : (j < 10) := NewPreH5
  have PreH6 : ((0 : Int) <= k) := NewPreH6
  have PreH7 : (k <= 10) := NewPreH7
  have PreH8 : (DigitDPCellProgress dp_l_2 i j k) := NewPreH9
  have dp_length := PreH8.1
  have PreH9 : (PowerTable power_l_2) := NewPreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | (solve | simp only [Zlength_replace_Znth]; omega)
      | omega
      | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
      | exact proof_of_digits_sum_init_entail_wit_12_split_goal_1 power_l_2 dp_l_2 k j i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10


theorem proof_of_digits_sum_init_entail_wit_13_split_goal_1 : digits_sum_init_entail_wit_13_split_goal_1 := by
  unfold digits_sum_init_entail_wit_13_split_goal_1
  intro power_l_2 dp_l_2 k j i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH8 : (DigitDPCellProgress dp_l_2 i j k) := NewPreH9
    have dp_length := PreH8.1
    have he : k = 10 := by omega
    rw [he] at PreH8
    obtain ⟨hlen, hp, hj, hk, hbase, hprev, hdone, hz, hlater, part, hinner, hcell⟩ := PreH8
    refine ⟨hlen, hp, by omega, hbase, hprev, ?_, (fun d hd => hz d (by omega)), hlater⟩
    intro d hd
    by_cases hlt : d < j
    · exact hdone d (by omega)
    · have he : d = j := by omega
      subst d
      rw [hcell, InnerCandidateDigitSum_ten__digits_dp_row dp_l_2 (i-1) part (by omega) (fun d hd => hprev (i-1) d (by omega) hd) hinner]
      rw [DigitDPValue, if_neg (by omega)]
      have hpow : Z.pow 10 (i-1) = Z.pow 10 (i-2)*10 := by rw [show i-1 = (i-2)+1 by omega, pow_step 10 (i-2) (by omega)]
      simp only [Z.modulo, Int.fmod_add_fmod]
      congr 1
      rw [hpow, show i-1-1 = i-2 by omega]
      grind

theorem proof_of_digits_sum_init_entail_wit_13 : digits_sum_init_entail_wit_13 := by
  unfold digits_sum_init_entail_wit_13
  right
  intro power_l_2 dp_l_2 k j i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10
  have PreH1 : (k >= 10) := NewPreH1
  have PreH2 : (2 <= i) := NewPreH2
  have PreH3 : (i < 20) := NewPreH3
  have PreH4 : ((0 : Int) <= j) := NewPreH4
  have PreH5 : (j < 10) := NewPreH5
  have PreH6 : ((0 : Int) <= k) := NewPreH6
  have PreH7 : (k <= 10) := NewPreH7
  have PreH8 : (DigitDPCellProgress dp_l_2 i j k) := NewPreH9
  have dp_length := PreH8.1
  have PreH9 : (PowerTable power_l_2) := NewPreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | (solve | simp only [Zlength_replace_Znth]; omega)
      | omega
      | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
      | exact proof_of_digits_sum_init_entail_wit_13_split_goal_1 power_l_2 dp_l_2 k j i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10


theorem proof_of_digits_sum_init_entail_wit_14_split_goal_1 : digits_sum_init_entail_wit_14_split_goal_1 := by
  unfold digits_sum_init_entail_wit_14_split_goal_1
  intro power_l_2 dp_l_2 j i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH6 : (DigitDPRowProgress dp_l_2 i j) := NewPreH7
    obtain ⟨hlen, hp, hj, hbase, hprev, hdone, hz, hlater⟩ := PreH6
    refine ⟨hlen, by omega, hbase, ?_, ?_⟩
    · intro p d hpr hd
      by_cases he : p = i
      · subst p; exact hdone d (by omega)
      · exact hprev p d (by omega) hd
    · intro p d hpr hd
      exact hlater p d (by omega) hd

theorem proof_of_digits_sum_init_entail_wit_14 : digits_sum_init_entail_wit_14 := by
  unfold digits_sum_init_entail_wit_14
  right
  intro power_l_2 dp_l_2 j i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8
  have PreH1 : (j >= 10) := NewPreH1
  have PreH2 : (2 <= i) := NewPreH2
  have PreH3 : (i < 20) := NewPreH3
  have PreH4 : ((0 : Int) <= j) := NewPreH4
  have PreH5 : (j <= 10) := NewPreH5
  have PreH6 : (DigitDPRowProgress dp_l_2 i j) := NewPreH7
  have PreH7 : (PowerTable power_l_2) := NewPreH8
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | (solve | simp only [Zlength_replace_Znth]; omega)
      | omega
      | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
      | exact proof_of_digits_sum_init_entail_wit_14_split_goal_1 power_l_2 dp_l_2 j i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8


theorem proof_of_digits_sum_init_return_wit_1_split_goal_1 : digits_sum_init_return_wit_1_split_goal_1 := by
  unfold digits_sum_init_return_wit_1_split_goal_1
  intro power_l_2 dp_l_2 i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH4 : (DigitDPOuterProgress dp_l_2 i) := NewPreH5
    obtain ⟨hlen, hr, hbase, hprev, hlater⟩ := PreH4
    exact ⟨hlen, hbase, fun p d hp hd => hprev p d (by omega) hd⟩

theorem proof_of_digits_sum_init_return_wit_1 : digits_sum_init_return_wit_1 := by
  unfold digits_sum_init_return_wit_1
  right
  intro power_l_2 dp_l_2 i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6
  have PreH1 : (i >= 20) := NewPreH1
  have PreH2 : (2 <= i) := NewPreH2
  have PreH3 : (i <= 20) := NewPreH3
  have PreH4 : (DigitDPOuterProgress dp_l_2 i) := NewPreH5
  have PreH5 : (PowerTable power_l_2) := NewPreH6
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | (solve | simp only [Zlength_replace_Znth]; omega)
      | omega
      | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
      | exact proof_of_digits_sum_init_return_wit_1_split_goal_1 power_l_2 dp_l_2 i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6


theorem proof_of_prefix_digits_sum_safety_wit_17_split_goal_1 : prefix_digits_sum_safety_wit_17_split_goal_1 := by
  unfold prefix_digits_sum_safety_wit_17_split_goal_1
  intro dp_l x_pre dp_pre digits_pre power_ll digits_l m i tmpx ans NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH11 : (DigitPositionPower i power_ll) := NewPreH12
    dump_pre_spatial
    have hp := pow10_pos (i-1) (by omega)
    have hb := pow10_bound (i-1) 17 (by omega) (by change i-1 ≤ 17; omega)
    change Z.pow 10 (i-1) ≤ 100000000000000000 at hb
    have he := PreH11.2
    omega

theorem proof_of_prefix_digits_sum_safety_wit_17_split_goal_2 : prefix_digits_sum_safety_wit_17_split_goal_2 := by
  unfold prefix_digits_sum_safety_wit_17_split_goal_2
  intro dp_l x_pre dp_pre digits_pre power_ll digits_l m i tmpx ans NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH11 : (DigitPositionPower i power_ll) := NewPreH12
    dump_pre_spatial
    have hp := pow10_pos (i-1) (by omega)
    have hb := pow10_bound (i-1) 17 (by omega) (by change i-1 ≤ 17; omega)
    change Z.pow 10 (i-1) ≤ 100000000000000000 at hb
    have he := PreH11.2
    omega

theorem proof_of_prefix_digits_sum_safety_wit_17 : prefix_digits_sum_safety_wit_17 := by
  unfold prefix_digits_sum_safety_wit_17
  right
  intro dp_l x_pre dp_pre digits_pre power_ll digits_l m i tmpx ans NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14
  have PreH1 : (i < m) := NewPreH1
  have PreH2 : (1 <= x_pre) := NewPreH2
  have PreH3 : (x_pre <= 1000000000000000000) := NewPreH3
  have PreH4 : (ans = (0 : Int)) := NewPreH4
  have PreH5 : (tmpx = (0 : Int)) := NewPreH5
  have PreH6 : (1 <= i) := NewPreH6
  have PreH7 : (i <= m) := NewPreH7
  have PreH8 : (m <= 19) := NewPreH8
  have PreH9 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int)) := NewPreH10
  have PreH10 : (ExtractedDigitCount x_pre m) := NewPreH11
  have PreH11 : (DigitPositionPower i power_ll) := NewPreH12
  have PreH13 : (AccumulatedDigitSumCorrect x_pre m ans) := NewPreH13
  have PreH14 : (DigitDPTable dp_l) := NewPreH14
  split_pures
  all_goals first
    | assumption
    | omega
    | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
    | exact proof_of_prefix_digits_sum_safety_wit_17_split_goal_1 dp_l x_pre dp_pre digits_pre power_ll digits_l m i tmpx ans NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14
    | exact proof_of_prefix_digits_sum_safety_wit_17_split_goal_2 dp_l x_pre dp_pre digits_pre power_ll digits_l m i tmpx ans NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14


theorem proof_of_prefix_digits_sum_safety_wit_23_split_goal_1 : prefix_digits_sum_safety_wit_23_split_goal_1 := by
  unfold prefix_digits_sum_safety_wit_23_split_goal_1
  intro dp_l x_pre dp_pre digits_pre power_ll answer_before ans j digits_l m i tmpx NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH19 : (DigitDPTable dp_l) := NewPreH20
    dump_pre_spatial
    have hv := PreH19.2.2 i j (by omega) (by omega)
    have hb := dp_bounds i j
    simp only [digit_sum_modulus, INT_MAX, INT_MIN] at *
    omega

theorem proof_of_prefix_digits_sum_safety_wit_23_split_goal_2 : prefix_digits_sum_safety_wit_23_split_goal_2 := by
  unfold prefix_digits_sum_safety_wit_23_split_goal_2
  intro dp_l x_pre dp_pre digits_pre power_ll answer_before ans j digits_l m i tmpx NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH19 : (DigitDPTable dp_l) := NewPreH20
    dump_pre_spatial
    have hv := PreH19.2.2 i j (by omega) (by omega)
    have hb := dp_bounds i j
    simp only [digit_sum_modulus, INT_MAX, INT_MIN] at *
    omega

theorem proof_of_prefix_digits_sum_safety_wit_23 : prefix_digits_sum_safety_wit_23 := by
  unfold prefix_digits_sum_safety_wit_23
  right
  intro dp_l x_pre dp_pre digits_pre power_ll answer_before ans j digits_l m i tmpx NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20
  have PreH1 : (j < (Znth i digits_l (0 : Int))) := NewPreH1
  have PreH2 : (1 <= x_pre) := NewPreH2
  have PreH3 : (x_pre <= 1000000000000000000) := NewPreH3
  have PreH4 : (tmpx = (0 : Int)) := NewPreH4
  have PreH5 : (1 <= i) := NewPreH5
  have PreH6 : (i <= m) := NewPreH6
  have PreH7 : (m <= 19) := NewPreH7
  have PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int))) := NewPreH8
  have PreH9 : ((Znth i digits_l (0 : Int)) < 10) := NewPreH9
  have PreH10 : ((0 : Int) <= j) := NewPreH10
  have PreH11 : (j <= (Znth i digits_l (0 : Int))) := NewPreH11
  have PreH12 : ((0 : Int) <= ans) := NewPreH12
  have PreH13 : (ans < 1000000007) := NewPreH13
  have PreH14 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int)) := NewPreH15
  have PreH15 : (ExtractedDigitCount x_pre m) := NewPreH16
  have PreH17 : (AccumulatedDigitSumCorrect x_pre i answer_before) := NewPreH18
  have PreH18 : (OuterDigitPositionPower i power_ll) := NewPreH19
  have PreH19 : (DigitDPTable dp_l) := NewPreH20
  split_pures
  all_goals first
    | assumption
    | omega
    | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
    | exact proof_of_prefix_digits_sum_safety_wit_23_split_goal_1 dp_l x_pre dp_pre digits_pre power_ll answer_before ans j digits_l m i tmpx NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20
    | exact proof_of_prefix_digits_sum_safety_wit_23_split_goal_2 dp_l x_pre dp_pre digits_pre power_ll answer_before ans j digits_l m i tmpx NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20


theorem proof_of_prefix_digits_sum_safety_wit_30_split_goal_1 : prefix_digits_sum_safety_wit_30_split_goal_1 := by
  unfold prefix_digits_sum_safety_wit_30_split_goal_1
  intro dp_l x_pre dp_pre digits_pre power_ll answer_before ans j digits_l m i tmpx NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    dump_pre_spatial
    left
    omega

theorem proof_of_prefix_digits_sum_safety_wit_30_split_goal_2 : prefix_digits_sum_safety_wit_30_split_goal_2 := by
  unfold prefix_digits_sum_safety_wit_30_split_goal_2
  intro dp_l x_pre dp_pre digits_pre power_ll answer_before ans j digits_l m i tmpx NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH5 : (1 <= i) := NewPreH5
    have PreH18 : (OuterDigitPositionPower i power_ll) := NewPreH19
    dump_pre_spatial
    have hp := outer_power_pos i power_ll PreH5 PreH18
    omega

theorem proof_of_prefix_digits_sum_safety_wit_30 : prefix_digits_sum_safety_wit_30 := by
  unfold prefix_digits_sum_safety_wit_30
  right
  intro dp_l x_pre dp_pre digits_pre power_ll answer_before ans j digits_l m i tmpx NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20
  have PreH1 : (j >= (Znth i digits_l (0 : Int))) := NewPreH1
  have PreH2 : (1 <= x_pre) := NewPreH2
  have PreH3 : (x_pre <= 1000000000000000000) := NewPreH3
  have PreH4 : (tmpx = (0 : Int)) := NewPreH4
  have PreH5 : (1 <= i) := NewPreH5
  have PreH6 : (i <= m) := NewPreH6
  have PreH7 : (m <= 19) := NewPreH7
  have PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int))) := NewPreH8
  have PreH9 : ((Znth i digits_l (0 : Int)) < 10) := NewPreH9
  have PreH10 : ((0 : Int) <= j) := NewPreH10
  have PreH11 : (j <= (Znth i digits_l (0 : Int))) := NewPreH11
  have PreH12 : ((0 : Int) <= ans) := NewPreH12
  have PreH13 : (ans < 1000000007) := NewPreH13
  have PreH14 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int)) := NewPreH15
  have PreH15 : (ExtractedDigitCount x_pre m) := NewPreH16
  have PreH17 : (AccumulatedDigitSumCorrect x_pre i answer_before) := NewPreH18
  have PreH18 : (OuterDigitPositionPower i power_ll) := NewPreH19
  have PreH19 : (DigitDPTable dp_l) := NewPreH20
  split_pures
  all_goals first
    | assumption
    | omega
    | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
    | exact proof_of_prefix_digits_sum_safety_wit_30_split_goal_1 dp_l x_pre dp_pre digits_pre power_ll answer_before ans j digits_l m i tmpx NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20
    | exact proof_of_prefix_digits_sum_safety_wit_30_split_goal_2 dp_l x_pre dp_pre digits_pre power_ll answer_before ans j digits_l m i tmpx NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20


theorem proof_of_prefix_digits_sum_safety_wit_33_split_goal_1 : prefix_digits_sum_safety_wit_33_split_goal_1 := by
  unfold prefix_digits_sum_safety_wit_33_split_goal_1
  intro dp_l x_pre dp_pre digits_pre power_ll answer_before ans j digits_l m i tmpx NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH5 : (1 <= i) := NewPreH5
    have PreH18 : (OuterDigitPositionPower i power_ll) := NewPreH19
    dump_pre_spatial
    have hp := outer_power_pos i power_ll PreH5 PreH18
    have hb : power_ll ≤ 1000000000000000000 := by
      rcases PreH18 with ⟨hz, _⟩ | ⟨hr, he⟩
      · omega
      · rw [he]
        exact pow10_bound (i-1) 18 (by omega) (by change i-1 ≤ 18; omega)
    have hr := rem_nonneg_bounds x_pre power_ll (by omega) hp
    omega

theorem proof_of_prefix_digits_sum_safety_wit_33_split_goal_2 : prefix_digits_sum_safety_wit_33_split_goal_2 := by
  unfold prefix_digits_sum_safety_wit_33_split_goal_2
  intro dp_l x_pre dp_pre digits_pre power_ll answer_before ans j digits_l m i tmpx NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH5 : (1 <= i) := NewPreH5
    have PreH18 : (OuterDigitPositionPower i power_ll) := NewPreH19
    dump_pre_spatial
    have hp := outer_power_pos i power_ll PreH5 PreH18
    have hb : power_ll ≤ 1000000000000000000 := by
      rcases PreH18 with ⟨hz, _⟩ | ⟨hr, he⟩
      · omega
      · rw [he]
        exact pow10_bound (i-1) 18 (by omega) (by change i-1 ≤ 18; omega)
    have hr := rem_nonneg_bounds x_pre power_ll (by omega) hp
    omega

theorem proof_of_prefix_digits_sum_safety_wit_33 : prefix_digits_sum_safety_wit_33 := by
  unfold prefix_digits_sum_safety_wit_33
  right
  intro dp_l x_pre dp_pre digits_pre power_ll answer_before ans j digits_l m i tmpx NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20
  have PreH1 : (j >= (Znth i digits_l (0 : Int))) := NewPreH1
  have PreH2 : (1 <= x_pre) := NewPreH2
  have PreH3 : (x_pre <= 1000000000000000000) := NewPreH3
  have PreH4 : (tmpx = (0 : Int)) := NewPreH4
  have PreH5 : (1 <= i) := NewPreH5
  have PreH6 : (i <= m) := NewPreH6
  have PreH7 : (m <= 19) := NewPreH7
  have PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int))) := NewPreH8
  have PreH9 : ((Znth i digits_l (0 : Int)) < 10) := NewPreH9
  have PreH10 : ((0 : Int) <= j) := NewPreH10
  have PreH11 : (j <= (Znth i digits_l (0 : Int))) := NewPreH11
  have PreH12 : ((0 : Int) <= ans) := NewPreH12
  have PreH13 : (ans < 1000000007) := NewPreH13
  have PreH14 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int)) := NewPreH15
  have PreH15 : (ExtractedDigitCount x_pre m) := NewPreH16
  have PreH17 : (AccumulatedDigitSumCorrect x_pre i answer_before) := NewPreH18
  have PreH18 : (OuterDigitPositionPower i power_ll) := NewPreH19
  have PreH19 : (DigitDPTable dp_l) := NewPreH20
  split_pures
  all_goals first
    | assumption
    | omega
    | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
    | exact proof_of_prefix_digits_sum_safety_wit_33_split_goal_1 dp_l x_pre dp_pre digits_pre power_ll answer_before ans j digits_l m i tmpx NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20
    | exact proof_of_prefix_digits_sum_safety_wit_33_split_goal_2 dp_l x_pre dp_pre digits_pre power_ll answer_before ans j digits_l m i tmpx NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20


theorem proof_of_prefix_digits_sum_safety_wit_34_split_goal_1 : prefix_digits_sum_safety_wit_34_split_goal_1 := by
  unfold prefix_digits_sum_safety_wit_34_split_goal_1
  intro dp_l x_pre dp_pre digits_pre power_ll answer_before ans j digits_l m i tmpx NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    dump_pre_spatial
    left
    omega

theorem proof_of_prefix_digits_sum_safety_wit_34_split_goal_2 : prefix_digits_sum_safety_wit_34_split_goal_2 := by
  unfold prefix_digits_sum_safety_wit_34_split_goal_2
  intro dp_l x_pre dp_pre digits_pre power_ll answer_before ans j digits_l m i tmpx NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH5 : (1 <= i) := NewPreH5
    have PreH18 : (OuterDigitPositionPower i power_ll) := NewPreH19
    dump_pre_spatial
    have hp := outer_power_pos i power_ll PreH5 PreH18
    omega

theorem proof_of_prefix_digits_sum_safety_wit_34 : prefix_digits_sum_safety_wit_34 := by
  unfold prefix_digits_sum_safety_wit_34
  right
  intro dp_l x_pre dp_pre digits_pre power_ll answer_before ans j digits_l m i tmpx NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20
  have PreH1 : (j >= (Znth i digits_l (0 : Int))) := NewPreH1
  have PreH2 : (1 <= x_pre) := NewPreH2
  have PreH3 : (x_pre <= 1000000000000000000) := NewPreH3
  have PreH4 : (tmpx = (0 : Int)) := NewPreH4
  have PreH5 : (1 <= i) := NewPreH5
  have PreH6 : (i <= m) := NewPreH6
  have PreH7 : (m <= 19) := NewPreH7
  have PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int))) := NewPreH8
  have PreH9 : ((Znth i digits_l (0 : Int)) < 10) := NewPreH9
  have PreH10 : ((0 : Int) <= j) := NewPreH10
  have PreH11 : (j <= (Znth i digits_l (0 : Int))) := NewPreH11
  have PreH12 : ((0 : Int) <= ans) := NewPreH12
  have PreH13 : (ans < 1000000007) := NewPreH13
  have PreH14 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int)) := NewPreH15
  have PreH15 : (ExtractedDigitCount x_pre m) := NewPreH16
  have PreH17 : (AccumulatedDigitSumCorrect x_pre i answer_before) := NewPreH18
  have PreH18 : (OuterDigitPositionPower i power_ll) := NewPreH19
  have PreH19 : (DigitDPTable dp_l) := NewPreH20
  split_pures
  all_goals first
    | assumption
    | omega
    | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
    | exact proof_of_prefix_digits_sum_safety_wit_34_split_goal_1 dp_l x_pre dp_pre digits_pre power_ll answer_before ans j digits_l m i tmpx NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20
    | exact proof_of_prefix_digits_sum_safety_wit_34_split_goal_2 dp_l x_pre dp_pre digits_pre power_ll answer_before ans j digits_l m i tmpx NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20


theorem proof_of_prefix_digits_sum_safety_wit_38_split_goal_1 : prefix_digits_sum_safety_wit_38_split_goal_1 := by
  unfold prefix_digits_sum_safety_wit_38_split_goal_1
  intro dp_l x_pre dp_pre digits_pre power_ll answer_before ans j digits_l m i tmpx NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH5 : (1 <= i) := NewPreH5
    have PreH18 : (OuterDigitPositionPower i power_ll) := NewPreH19
    dump_pre_spatial
    have hp := outer_power_pos i power_ll PreH5 PreH18
    have hr := rem_nonneg_bounds x_pre power_ll (by omega) hp
    have hl := rem_nonneg_bounds (Z.rem x_pre power_ll+1) 1000000007 (by omega) (by decide)
    have hq : 0 ≤ Z.quot x_pre power_ll := Int.tdiv_nonneg (by omega) (by omega)
    have hd := rem_nonneg_bounds (Z.quot x_pre power_ll) 10 hq (by decide)
    have hp0 := Int.mul_nonneg hl.1 hd.1
    have hp1 := Int.mul_le_mul_of_nonneg_left (show Z.rem (Z.quot x_pre power_ll) 10 ≤ 10 by omega) hl.1
    have hm := rem_nonneg_bounds (Z.rem (Z.rem x_pre power_ll+1) 1000000007 * Z.rem (Z.quot x_pre power_ll) 10) 1000000007 hp0 (by decide)
    omega

theorem proof_of_prefix_digits_sum_safety_wit_38_split_goal_2 : prefix_digits_sum_safety_wit_38_split_goal_2 := by
  unfold prefix_digits_sum_safety_wit_38_split_goal_2
  intro dp_l x_pre dp_pre digits_pre power_ll answer_before ans j digits_l m i tmpx NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH5 : (1 <= i) := NewPreH5
    have PreH18 : (OuterDigitPositionPower i power_ll) := NewPreH19
    dump_pre_spatial
    have hp := outer_power_pos i power_ll PreH5 PreH18
    have hr := rem_nonneg_bounds x_pre power_ll (by omega) hp
    have hl := rem_nonneg_bounds (Z.rem x_pre power_ll+1) 1000000007 (by omega) (by decide)
    have hq : 0 ≤ Z.quot x_pre power_ll := Int.tdiv_nonneg (by omega) (by omega)
    have hd := rem_nonneg_bounds (Z.quot x_pre power_ll) 10 hq (by decide)
    have hp0 := Int.mul_nonneg hl.1 hd.1
    have hp1 := Int.mul_le_mul_of_nonneg_left (show Z.rem (Z.quot x_pre power_ll) 10 ≤ 10 by omega) hl.1
    have hm := rem_nonneg_bounds (Z.rem (Z.rem x_pre power_ll+1) 1000000007 * Z.rem (Z.quot x_pre power_ll) 10) 1000000007 hp0 (by decide)
    omega

theorem proof_of_prefix_digits_sum_safety_wit_38 : prefix_digits_sum_safety_wit_38 := by
  unfold prefix_digits_sum_safety_wit_38
  right
  intro dp_l x_pre dp_pre digits_pre power_ll answer_before ans j digits_l m i tmpx NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20
  have PreH1 : (j >= (Znth i digits_l (0 : Int))) := NewPreH1
  have PreH2 : (1 <= x_pre) := NewPreH2
  have PreH3 : (x_pre <= 1000000000000000000) := NewPreH3
  have PreH4 : (tmpx = (0 : Int)) := NewPreH4
  have PreH5 : (1 <= i) := NewPreH5
  have PreH6 : (i <= m) := NewPreH6
  have PreH7 : (m <= 19) := NewPreH7
  have PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int))) := NewPreH8
  have PreH9 : ((Znth i digits_l (0 : Int)) < 10) := NewPreH9
  have PreH10 : ((0 : Int) <= j) := NewPreH10
  have PreH11 : (j <= (Znth i digits_l (0 : Int))) := NewPreH11
  have PreH12 : ((0 : Int) <= ans) := NewPreH12
  have PreH13 : (ans < 1000000007) := NewPreH13
  have PreH14 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int)) := NewPreH15
  have PreH15 : (ExtractedDigitCount x_pre m) := NewPreH16
  have PreH17 : (AccumulatedDigitSumCorrect x_pre i answer_before) := NewPreH18
  have PreH18 : (OuterDigitPositionPower i power_ll) := NewPreH19
  have PreH19 : (DigitDPTable dp_l) := NewPreH20
  split_pures
  all_goals first
    | assumption
    | omega
    | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
    | exact proof_of_prefix_digits_sum_safety_wit_38_split_goal_1 dp_l x_pre dp_pre digits_pre power_ll answer_before ans j digits_l m i tmpx NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20
    | exact proof_of_prefix_digits_sum_safety_wit_38_split_goal_2 dp_l x_pre dp_pre digits_pre power_ll answer_before ans j digits_l m i tmpx NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20


theorem proof_of_prefix_digits_sum_safety_wit_41_split_goal_1 : prefix_digits_sum_safety_wit_41_split_goal_1 := by
  unfold prefix_digits_sum_safety_wit_41_split_goal_1
  intro dp_l x_pre dp_pre digits_pre power_ll answer_before ans j digits_l m i tmpx NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH5 : (1 <= i) := NewPreH5
    have PreH18 : (OuterDigitPositionPower i power_ll) := NewPreH19
    dump_pre_spatial
    have hp := outer_power_pos i power_ll PreH5 PreH18
    have hr := rem_nonneg_bounds x_pre power_ll (by omega) hp
    have hl := rem_nonneg_bounds (Z.rem x_pre power_ll+1) 1000000007 (by omega) (by decide)
    have hq : 0 ≤ Z.quot x_pre power_ll := Int.tdiv_nonneg (by omega) (by omega)
    have hd := rem_nonneg_bounds (Z.quot x_pre power_ll) 10 hq (by decide)
    have hp0 := Int.mul_nonneg hl.1 hd.1
    have hp1 := Int.mul_le_mul_of_nonneg_left (show Z.rem (Z.quot x_pre power_ll) 10 ≤ 10 by omega) hl.1
    have hm := rem_nonneg_bounds (Z.rem (Z.rem x_pre power_ll+1) 1000000007 * Z.rem (Z.quot x_pre power_ll) 10) 1000000007 hp0 (by decide)
    omega

theorem proof_of_prefix_digits_sum_safety_wit_41_split_goal_2 : prefix_digits_sum_safety_wit_41_split_goal_2 := by
  unfold prefix_digits_sum_safety_wit_41_split_goal_2
  intro dp_l x_pre dp_pre digits_pre power_ll answer_before ans j digits_l m i tmpx NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH5 : (1 <= i) := NewPreH5
    have PreH18 : (OuterDigitPositionPower i power_ll) := NewPreH19
    dump_pre_spatial
    have hp := outer_power_pos i power_ll PreH5 PreH18
    have hr := rem_nonneg_bounds x_pre power_ll (by omega) hp
    have hl := rem_nonneg_bounds (Z.rem x_pre power_ll+1) 1000000007 (by omega) (by decide)
    have hq : 0 ≤ Z.quot x_pre power_ll := Int.tdiv_nonneg (by omega) (by omega)
    have hd := rem_nonneg_bounds (Z.quot x_pre power_ll) 10 hq (by decide)
    have hp0 := Int.mul_nonneg hl.1 hd.1
    have hp1 := Int.mul_le_mul_of_nonneg_left (show Z.rem (Z.quot x_pre power_ll) 10 ≤ 10 by omega) hl.1
    have hm := rem_nonneg_bounds (Z.rem (Z.rem x_pre power_ll+1) 1000000007 * Z.rem (Z.quot x_pre power_ll) 10) 1000000007 hp0 (by decide)
    omega

theorem proof_of_prefix_digits_sum_safety_wit_41 : prefix_digits_sum_safety_wit_41 := by
  unfold prefix_digits_sum_safety_wit_41
  right
  intro dp_l x_pre dp_pre digits_pre power_ll answer_before ans j digits_l m i tmpx NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20
  have PreH1 : (j >= (Znth i digits_l (0 : Int))) := NewPreH1
  have PreH2 : (1 <= x_pre) := NewPreH2
  have PreH3 : (x_pre <= 1000000000000000000) := NewPreH3
  have PreH4 : (tmpx = (0 : Int)) := NewPreH4
  have PreH5 : (1 <= i) := NewPreH5
  have PreH6 : (i <= m) := NewPreH6
  have PreH7 : (m <= 19) := NewPreH7
  have PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int))) := NewPreH8
  have PreH9 : ((Znth i digits_l (0 : Int)) < 10) := NewPreH9
  have PreH10 : ((0 : Int) <= j) := NewPreH10
  have PreH11 : (j <= (Znth i digits_l (0 : Int))) := NewPreH11
  have PreH12 : ((0 : Int) <= ans) := NewPreH12
  have PreH13 : (ans < 1000000007) := NewPreH13
  have PreH14 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int)) := NewPreH15
  have PreH15 : (ExtractedDigitCount x_pre m) := NewPreH16
  have PreH17 : (AccumulatedDigitSumCorrect x_pre i answer_before) := NewPreH18
  have PreH18 : (OuterDigitPositionPower i power_ll) := NewPreH19
  have PreH19 : (DigitDPTable dp_l) := NewPreH20
  split_pures
  all_goals first
    | assumption
    | omega
    | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
    | exact proof_of_prefix_digits_sum_safety_wit_41_split_goal_1 dp_l x_pre dp_pre digits_pre power_ll answer_before ans j digits_l m i tmpx NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20
    | exact proof_of_prefix_digits_sum_safety_wit_41_split_goal_2 dp_l x_pre dp_pre digits_pre power_ll answer_before ans j digits_l m i tmpx NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20


theorem proof_of_prefix_digits_sum_entail_wit_1 : prefix_digits_sum_entail_wit_1 := by
  unfold prefix_digits_sum_entail_wit_1
  right
  intro dp_l x_pre NewPreH1 NewPreH2 NewPreH3 NewPreH4
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    · exact .nil
    · rfl

theorem aux_prefix_digits_sum_entail_wit_2_split_goal_1 : (forall (x_pre : Int) (dp_l : (List Int)) (digits_l_2 : (List Int)) (i : Int) (power_ll : Int) (ans : Int) (m : Int) (PreH1 : (i < 20)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (m = (0 : Int))) (PreH5 : (ans = (0 : Int))) (PreH6 : (power_ll = 1)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= 20)) (PreH9 : (ZeroSegment digits_l_2 i 20)) (PreH10 : (DigitDPTable dp_l)) ,
  (ZeroSegment (digits_l_2 ++ ((0 : Int) :: (@List.nil Int))) (i + 1) 20)) := by

  intro x_pre dp_l digits_l_2 i power_ll ans m PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    exact ZeroSegment_app_zero__digits_power_and_zero_init digits_l_2 i 20 PreH9 PreH1

theorem proof_of_prefix_digits_sum_entail_wit_2 : prefix_digits_sum_entail_wit_2 := by
  unfold prefix_digits_sum_entail_wit_2
  right
  intro dp_l x_pre digits_l_2 i power_ll ans m NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11
  have PreH1 : (i < 20) := NewPreH1
  have PreH2 : (1 <= x_pre) := NewPreH2
  have PreH3 : (x_pre <= 1000000000000000000) := NewPreH3
  have PreH4 : (m = (0 : Int)) := NewPreH4
  have PreH5 : (ans = (0 : Int)) := NewPreH5
  have PreH6 : (power_ll = 1) := NewPreH6
  have PreH7 : ((0 : Int) <= i) := NewPreH7
  have PreH8 : (i <= 20) := NewPreH8
  have PreH9 : (ZeroSegment digits_l_2 i 20) := zero_annotation digits_l_2 i 20 NewPreH9 (by omega) NewPreH10
  have PreH10 : (DigitDPTable dp_l) := NewPreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | (solve | simp only [Zlength_replace_Znth]; omega)
      | omega
      | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
      | exact zero_annotation_back _ _ _ (aux_prefix_digits_sum_entail_wit_2_split_goal_1 x_pre dp_l digits_l_2 i power_ll ans m PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10)


theorem proof_of_prefix_digits_sum_entail_wit_3_split_goal_1 : prefix_digits_sum_entail_wit_3_split_goal_1 := by
  unfold prefix_digits_sum_entail_wit_3_split_goal_1
  intro dp_l x_pre digits_l_2 i power_ll ans m NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH9 : (ZeroSegment digits_l_2 i 20) := zero_annotation digits_l_2 i 20 NewPreH9 (by omega) NewPreH10
    obtain ⟨hlen, hr, hz⟩ := PreH9
    refine ⟨by omega, by decide, ?_, (fun k hk => by omega), fun k hk => hz k (by omega)⟩
    change x_pre = Int.fdiv x_pre 1
    simp

theorem proof_of_prefix_digits_sum_entail_wit_3 : prefix_digits_sum_entail_wit_3 := by
  unfold prefix_digits_sum_entail_wit_3
  right
  intro dp_l x_pre digits_l_2 i power_ll ans m NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11
  have PreH1 : (i >= 20) := NewPreH1
  have PreH2 : (1 <= x_pre) := NewPreH2
  have PreH3 : (x_pre <= 1000000000000000000) := NewPreH3
  have PreH4 : (m = (0 : Int)) := NewPreH4
  have PreH5 : (ans = (0 : Int)) := NewPreH5
  have PreH6 : (power_ll = 1) := NewPreH6
  have PreH7 : ((0 : Int) <= i) := NewPreH7
  have PreH8 : (i <= 20) := NewPreH8
  have PreH9 : (ZeroSegment digits_l_2 i 20) := zero_annotation digits_l_2 i 20 NewPreH9 (by omega) NewPreH10
  have PreH10 : (DigitDPTable dp_l) := NewPreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | (solve | simp only [Zlength_replace_Znth]; omega)
      | omega
      | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
      | exact proof_of_prefix_digits_sum_entail_wit_3_split_goal_1 dp_l x_pre digits_l_2 i power_ll ans m NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11


theorem proof_of_prefix_digits_sum_entail_wit_4_split_goal_1 : prefix_digits_sum_entail_wit_4_split_goal_1 := by
  unfold prefix_digits_sum_entail_wit_4_split_goal_1
  intro dp_l x_pre digits_l_2 tmpx m power_ll ans NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH5 : ((0 : Int) <= m) := NewPreH5
    have PreH7 : (tmpx >= (0 : Int)) := NewPreH7
    have PreH8 : ((tmpx ≠ (0 : Int)) -> (m < 19)) := NewPreH8
    have PreH11 : (ExtractedDigitBuffer x_pre digits_l_2 m tmpx) := NewPreH12
    have PreH13 : (tmpx ≠ (0 : Int)) := NewPreH14
    obtain ⟨hlen, hm, htmp, hd, hz⟩ := PreH11
    have hm18 := PreH8 PreH13
    have hp := pow10_pos m PreH5
    have hr := rem_nonneg_bounds tmpx 10 PreH7 (by decide)
    have hs : signed_last_nbits (Z.rem tmpx 10) 32 = Z.rem tmpx 10 := signed_last_nbits_small _ 32 (by decide) (by change 0 ≤ _ ∧ _ < 2147483648; omega)
    rw [hs]
    refine ⟨by simpa only [Zlength_replace_Znth] using hlen, by omega, ?_, ?_, ?_⟩
    · rw [htmp, pow_step 10 m PreH5]
      have hdiv : 0 ≤ Z.div x_pre (Z.pow 10 m) := Int.fdiv_nonneg (by omega) (by omega)
      rw [show Z.quot (Z.div x_pre (Z.pow 10 m)) 10 = Z.div (Z.div x_pre (Z.pow 10 m)) 10 from (Int.fdiv_eq_tdiv_of_nonneg hdiv (by decide)).symm]
      simp only [Z.div, Int.fdiv_eq_ediv, show 0 ≤ Z.pow 10 m by omega, show 0 ≤ Z.pow 10 m * 10 from Int.mul_nonneg (by omega) (by decide), show (0 : Int) ≤ 10 by decide, true_or, ↓reduceIte, Int.sub_zero]
      exact Int.ediv_ediv (by omega)
    · intro idx hi
      by_cases he : idx = m+1
      · subst idx
        rw [Znth_replace_Znth_Same 0 digits_l_2 (m+1) _ (by omega), show m+1-1 = m by omega, ← htmp]
        exact rem_eq_mod tmpx 10 PreH7 (by decide)
      · rw [Znth_replace_Znth_Diff 0 digits_l_2 (m+1) idx _ (by omega) (by omega) (Ne.symm he)]
        exact hd idx (by omega)
    · intro idx hi
      rw [Znth_replace_Znth_Diff 0 digits_l_2 (m+1) idx _ (by omega) (by omega) (by omega)]
      exact hz idx (by omega)

theorem proof_of_prefix_digits_sum_entail_wit_4_split_goal_3 : prefix_digits_sum_entail_wit_4_split_goal_3 := by
  unfold prefix_digits_sum_entail_wit_4_split_goal_3
  intro dp_l x_pre digits_l_2 tmpx m power_ll ans NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH5 : ((0 : Int) <= m) := NewPreH5
    have PreH7 : (tmpx >= (0 : Int)) := NewPreH7
    have PreH8 : ((tmpx ≠ (0 : Int)) -> (m < 19)) := NewPreH8
    have PreH11 : (ExtractedDigitBuffer x_pre digits_l_2 m tmpx) := NewPreH12
    have PreH13 : (tmpx ≠ (0 : Int)) := NewPreH14
    intro hzero
    have hm18 := PreH8 PreH13
    have hp := pow10_pos m PreH5
    have htmp := PreH11.2.2.1
    have hd := Int.tmod_add_tdiv_mul tmpx 10
    have hr := rem_nonneg_bounds tmpx 10 PreH7 (by decide)
    change Z.rem tmpx 10 + Z.quot tmpx 10 * 10 = tmpx at hd
    have hsmall : 1 ≤ tmpx ∧ tmpx < 10 := by omega
    have hx := Int.fmod_add_fdiv_mul x_pre (Z.pow 10 m)
    change Z.modulo x_pre (Z.pow 10 m) + Z.div x_pre (Z.pow 10 m) * Z.pow 10 m = x_pre at hx
    have hrx : 0 ≤ Z.modulo x_pre (Z.pow 10 m) ∧ Z.modulo x_pre (Z.pow 10 m) < Z.pow 10 m := ⟨Int.fmod_nonneg_of_pos _ hp, Int.fmod_lt_of_pos _ hp⟩
    have hlo := Int.mul_le_mul_of_nonneg_right hsmall.1 (show 0 ≤ Z.pow 10 m by omega)
    have hhi := Int.mul_le_mul_of_nonneg_right (show tmpx ≤ 9 by omega) (show 0 ≤ Z.pow 10 m by omega)
    rw [htmp] at hlo hhi
    unfold ExtractedDigitCount
    rw [show m+1-1 = m by omega, pow_step 10 m PreH5]
    omega

theorem proof_of_prefix_digits_sum_entail_wit_4_split_goal_4 : prefix_digits_sum_entail_wit_4_split_goal_4 := by
  unfold prefix_digits_sum_entail_wit_4_split_goal_4
  intro dp_l x_pre digits_l_2 tmpx m power_ll ans NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH7 : (tmpx >= (0 : Int)) := NewPreH7
    have PreH8 : ((tmpx ≠ (0 : Int)) -> (m < 19)) := NewPreH8
    have PreH11 : (ExtractedDigitBuffer x_pre digits_l_2 m tmpx) := NewPreH12
    have PreH13 : (tmpx ≠ (0 : Int)) := NewPreH14
    intro hnonzero
    have hm18 := PreH8 PreH13
    by_cases hm : m < 18
    · omega
    · have he : m = 18 := by omega
      have htmp := PreH11.2.2.1
      rw [he] at htmp
      change tmpx = Z.div x_pre 1000000000000000000 at htmp
      have hdiv : Z.div x_pre 1000000000000000000 ≤ 1 := by
        have hrem := Int.fmod_add_fdiv_mul x_pre 1000000000000000000
        have hb : 0 ≤ Int.fmod x_pre 1000000000000000000 := Int.fmod_nonneg_of_pos _ (by decide)
        change Int.fdiv x_pre 1000000000000000000 ≤ 1
        omega
      have hz : Z.quot tmpx 10 = 0 := Int.tdiv_eq_zero_of_lt PreH7 (by omega)
      exact False.elim (hnonzero hz)

theorem proof_of_prefix_digits_sum_entail_wit_4_split_goal_5 : prefix_digits_sum_entail_wit_4_split_goal_5 := by
  unfold prefix_digits_sum_entail_wit_4_split_goal_5
  intro dp_l x_pre digits_l_2 tmpx m power_ll ans NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH7 : (tmpx >= (0 : Int)) := NewPreH7
    exact Int.tdiv_nonneg PreH7 (by decide)

theorem proof_of_prefix_digits_sum_entail_wit_4 : prefix_digits_sum_entail_wit_4 := by
  unfold prefix_digits_sum_entail_wit_4
  right
  intro dp_l x_pre digits_l_2 tmpx m power_ll ans NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14
  have PreH1 : (1 <= x_pre) := NewPreH1
  have PreH2 : (x_pre <= 1000000000000000000) := NewPreH2
  have PreH3 : (ans = (0 : Int)) := NewPreH3
  have PreH4 : (power_ll = 1) := NewPreH4
  have PreH5 : ((0 : Int) <= m) := NewPreH5
  have PreH6 : (m <= 19) := NewPreH6
  have PreH7 : (tmpx >= (0 : Int)) := NewPreH7
  have PreH8 : ((tmpx ≠ (0 : Int)) -> (m < 19)) := NewPreH8
  have PreH9 : ((tmpx = (0 : Int)) -> (1 <= m)) := NewPreH9
  have PreH10 : ((tmpx = (0 : Int)) -> (ExtractedDigitCount x_pre m)) := NewPreH10
  have PreH11 : (ExtractedDigitBuffer x_pre digits_l_2 m tmpx) := NewPreH12
  have PreH12 : (DigitDPTable dp_l) := NewPreH13
  have PreH13 : (tmpx ≠ (0 : Int)) := NewPreH14
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | (solve | simp only [Zlength_replace_Znth]; omega)
      | omega
      | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
      | exact proof_of_prefix_digits_sum_entail_wit_4_split_goal_1 dp_l x_pre digits_l_2 tmpx m power_ll ans NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14
      | exact proof_of_prefix_digits_sum_entail_wit_4_split_goal_3 dp_l x_pre digits_l_2 tmpx m power_ll ans NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14
      | exact proof_of_prefix_digits_sum_entail_wit_4_split_goal_4 dp_l x_pre digits_l_2 tmpx m power_ll ans NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14
      | exact proof_of_prefix_digits_sum_entail_wit_4_split_goal_5 dp_l x_pre digits_l_2 tmpx m power_ll ans NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14


theorem proof_of_prefix_digits_sum_entail_wit_5_split_goal_1 : prefix_digits_sum_entail_wit_5_split_goal_1 := by
  unfold prefix_digits_sum_entail_wit_5_split_goal_1
  intro dp_l x_pre digits_l_2 tmpx m power_ll ans NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH1 : (1 <= x_pre) := NewPreH1
    have PreH10 : ((tmpx = (0 : Int)) -> (ExtractedDigitCount x_pre m)) := NewPreH10
    have PreH13 : (tmpx = (0 : Int)) := NewPreH14
    exact AccumulatedDigitSumCorrect_initial x_pre m PreH1 (PreH10 PreH13)

theorem aux_prefix_digits_sum_entail_wit_5_split_goal_2 : (forall (x_pre : Int) (dp_l : (List Int)) (digits_l_2 : (List Int)) (tmpx : Int) (m : Int) (power_ll : Int) (ans : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (ans = (0 : Int))) (PreH4 : (power_ll = 1)) (PreH5 : ((0 : Int) <= m)) (PreH6 : (m <= 19)) (PreH7 : (tmpx >= (0 : Int))) (PreH8 : ((tmpx ≠ (0 : Int)) -> (m < 19))) (PreH9 : ((tmpx = (0 : Int)) -> (1 <= m))) (PreH10 : ((tmpx = (0 : Int)) -> (ExtractedDigitCount x_pre m))) (PreH11 : (ExtractedDigitBuffer x_pre digits_l_2 m tmpx)) (PreH12 : (DigitDPTable dp_l)) (PreH13 : (tmpx = (0 : Int))) ,
  (OuterDigitPositionProgress x_pre dp_l digits_l_2 m (0 : Int))) := by

  intro x_pre dp_l digits_l_2 tmpx m power_ll ans PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    exact DigitPositionAccumulation_start x_pre dp_l digits_l_2 m (by simpa only [PreH13] using PreH11) (PreH10 PreH13)

theorem proof_of_prefix_digits_sum_entail_wit_5_split_goal_2 : prefix_digits_sum_entail_wit_5_split_goal_2 := by
  unfold prefix_digits_sum_entail_wit_5_split_goal_2
  intro dp_l x_pre digits_l_2 tmpx m power_ll ans NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    exact ⟨by decide, rfl⟩

theorem proof_of_prefix_digits_sum_entail_wit_5 : prefix_digits_sum_entail_wit_5 := by
  unfold prefix_digits_sum_entail_wit_5
  right
  intro dp_l x_pre digits_l_2 tmpx m power_ll ans NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14
  have PreH1 : (1 <= x_pre) := NewPreH1
  have PreH2 : (x_pre <= 1000000000000000000) := NewPreH2
  have PreH3 : (ans = (0 : Int)) := NewPreH3
  have PreH4 : (power_ll = 1) := NewPreH4
  have PreH5 : ((0 : Int) <= m) := NewPreH5
  have PreH6 : (m <= 19) := NewPreH6
  have PreH7 : (tmpx >= (0 : Int)) := NewPreH7
  have PreH8 : ((tmpx ≠ (0 : Int)) -> (m < 19)) := NewPreH8
  have PreH9 : ((tmpx = (0 : Int)) -> (1 <= m)) := NewPreH9
  have PreH10 : ((tmpx = (0 : Int)) -> (ExtractedDigitCount x_pre m)) := NewPreH10
  have PreH11 : (ExtractedDigitBuffer x_pre digits_l_2 m tmpx) := NewPreH12
  have PreH12 : (DigitDPTable dp_l) := NewPreH13
  have PreH13 : (tmpx = (0 : Int)) := NewPreH14
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | (solve | simp only [Zlength_replace_Znth]; omega)
      | omega
      | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
      | exact proof_of_prefix_digits_sum_entail_wit_5_split_goal_1 dp_l x_pre digits_l_2 tmpx m power_ll ans NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14
      | exact aux_prefix_digits_sum_entail_wit_5_split_goal_2 x_pre dp_l digits_l_2 tmpx m power_ll ans PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
      | exact proof_of_prefix_digits_sum_entail_wit_5_split_goal_2 dp_l x_pre digits_l_2 tmpx m power_ll ans NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14


theorem proof_of_prefix_digits_sum_entail_wit_6_split_goal_1 : prefix_digits_sum_entail_wit_6_split_goal_1 := by
  unfold prefix_digits_sum_entail_wit_6_split_goal_1
  intro dp_l x_pre power_ll digits_l_2 m i tmpx ans NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH11 : (DigitPositionPower i power_ll) := NewPreH12
    refine ⟨by omega, ?_⟩
    rw [PreH11.2, show i+1-1 = (i-1)+1 by omega, pow_step 10 (i-1) (by omega)]

theorem proof_of_prefix_digits_sum_entail_wit_6 : prefix_digits_sum_entail_wit_6 := by
  unfold prefix_digits_sum_entail_wit_6
  right
  intro dp_l x_pre power_ll digits_l_2 m i tmpx ans NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14
  have PreH1 : (i < m) := NewPreH1
  have PreH2 : (1 <= x_pre) := NewPreH2
  have PreH3 : (x_pre <= 1000000000000000000) := NewPreH3
  have PreH4 : (ans = (0 : Int)) := NewPreH4
  have PreH5 : (tmpx = (0 : Int)) := NewPreH5
  have PreH6 : (1 <= i) := NewPreH6
  have PreH7 : (i <= m) := NewPreH7
  have PreH8 : (m <= 19) := NewPreH8
  have PreH9 : (ExtractedDigitBuffer x_pre digits_l_2 m (0 : Int)) := NewPreH10
  have PreH10 : (ExtractedDigitCount x_pre m) := NewPreH11
  have PreH11 : (DigitPositionPower i power_ll) := NewPreH12
  have PreH13 : (AccumulatedDigitSumCorrect x_pre m ans) := NewPreH13
  have PreH14 : (DigitDPTable dp_l) := NewPreH14
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | (solve | simp only [Zlength_replace_Znth]; omega)
      | omega
      | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
      | exact proof_of_prefix_digits_sum_entail_wit_6_split_goal_1 dp_l x_pre power_ll digits_l_2 m i tmpx ans NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14


theorem proof_of_prefix_digits_sum_entail_wit_7_split_goal_1 : prefix_digits_sum_entail_wit_7_split_goal_1 := by
  unfold prefix_digits_sum_entail_wit_7_split_goal_1
  intro dp_l x_pre power_ll digits_l_2 m i tmpx ans NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH11 : (DigitPositionPower i power_ll) := NewPreH12
    right
    have he : i = m := by omega
    simpa only [he] using PreH11

theorem proof_of_prefix_digits_sum_entail_wit_7 : prefix_digits_sum_entail_wit_7 := by
  unfold prefix_digits_sum_entail_wit_7
  right
  intro dp_l x_pre power_ll digits_l_2 m i tmpx ans NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14
  have PreH1 : (i >= m) := NewPreH1
  have PreH2 : (1 <= x_pre) := NewPreH2
  have PreH3 : (x_pre <= 1000000000000000000) := NewPreH3
  have PreH4 : (ans = (0 : Int)) := NewPreH4
  have PreH5 : (tmpx = (0 : Int)) := NewPreH5
  have PreH6 : (1 <= i) := NewPreH6
  have PreH7 : (i <= m) := NewPreH7
  have PreH8 : (m <= 19) := NewPreH8
  have PreH9 : (ExtractedDigitBuffer x_pre digits_l_2 m (0 : Int)) := NewPreH10
  have PreH10 : (ExtractedDigitCount x_pre m) := NewPreH11
  have PreH11 : (DigitPositionPower i power_ll) := NewPreH12
  have PreH13 : (AccumulatedDigitSumCorrect x_pre m ans) := NewPreH13
  have PreH14 : (DigitDPTable dp_l) := NewPreH14
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | (solve | simp only [Zlength_replace_Znth]; omega)
      | omega
      | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
      | exact proof_of_prefix_digits_sum_entail_wit_7_split_goal_1 dp_l x_pre power_ll digits_l_2 m i tmpx ans NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14


theorem proof_of_prefix_digits_sum_entail_wit_8 : prefix_digits_sum_entail_wit_8 := by
  unfold prefix_digits_sum_entail_wit_8
  right
  intro dp_l x_pre power_ll digits_l_2 ans m i tmpx NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15
  have PreH8 : ((0 : Int) <= ans) := NewPreH8
  have PreH9 : (ans < 1000000007) := NewPreH9
  have PreH10 : (ExtractedDigitBuffer x_pre digits_l_2 m (0 : Int)) := NewPreH11
  have hd := PreH10.2.2.2.1 i (by omega)
  have hr : 0 ≤ Znth i digits_l_2 0 ∧ Znth i digits_l_2 0 < 10 := by
    rw [hd]
    exact ⟨Int.fmod_nonneg_of_pos _ (by decide), Int.fmod_lt_of_pos _ (by decide)⟩
  have hi : InnerCandidateDigitProgress dp_l i 0 ans ans := by
    refine ⟨0, InnerCandidateDigitSum_zero dp_l i, ?_⟩
    simp only [Int.add_zero]
    exact (Int.fmod_eq_of_lt PreH8 PreH9).symm
  Exists ans
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | exact Forall.nil | omega | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega)) | assumption | omega


theorem proof_of_prefix_digits_sum_entail_wit_9 : prefix_digits_sum_entail_wit_9 := by
  unfold prefix_digits_sum_entail_wit_9
  right
  intro dp_l x_pre power_ll answer_before_2 ans j digits_l_2 m i tmpx NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20
  have PreH10 : ((0 : Int) <= j) := NewPreH10
  have PreH16 : (InnerCandidateDigitProgress dp_l i j answer_before_2 ans) := NewPreH17
  have PreH19 : (DigitDPTable dp_l) := NewPreH20
  have hv := PreH19.2.2 i j (by omega) (by omega)
  have hb := dp_bounds i j
  have hn : 0 ≤ ans + Znth (i*10+j) dp_l 0 := by omega
  rw [rem_eq_mod _ 1000000007 hn (by decide)]
  have hr := mod_bounds (ans + Znth (i*10+j) dp_l 0)
  have hnext : InnerCandidateDigitProgress dp_l i (j+1) answer_before_2 (Z.modulo (ans + Znth (i*10+j) dp_l 0) 1000000007) := by
    obtain ⟨choice, hchoice, hans⟩ := PreH16
    refine ⟨Z.modulo (choice+Znth (i*10+j) dp_l 0) digit_sum_modulus, InnerCandidateDigitSum_step dp_l i j choice PreH10 hchoice, ?_⟩
    rw [hans]
    unfold digit_sum_modulus Z.modulo
    rw [Int.fmod_add_fmod, Int.add_fmod_fmod]
    congr 1
    omega
  Exists answer_before_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | exact Forall.nil | omega | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega)) | assumption | (unfold digit_sum_modulus at hr; omega)


theorem proof_of_prefix_digits_sum_entail_wit_10_split_goal_1 : prefix_digits_sum_entail_wit_10_split_goal_1 := by
  unfold prefix_digits_sum_entail_wit_10_split_goal_1
  intro dp_l x_pre power_ll answer_before ans j digits_l_2 m i tmpx NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH5 : (1 <= i) := NewPreH5
    have PreH18 : (OuterDigitPositionPower i power_ll) := NewPreH19
    exact outer_power_predecessor__prefix_inner_outer_scan i power_ll PreH5 PreH18

theorem proof_of_prefix_digits_sum_entail_wit_10_split_goal_2 : prefix_digits_sum_entail_wit_10_split_goal_2 := by
  unfold prefix_digits_sum_entail_wit_10_split_goal_2
  intro dp_l x_pre power_ll answer_before ans j digits_l_2 m i tmpx NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH2 : (1 <= x_pre) := NewPreH2
    have PreH5 : (1 <= i) := NewPreH5
    have PreH6 : (i <= m) := NewPreH6
    have PreH7 : (m <= 19) := NewPreH7
    have PreH12 : ((0 : Int) <= ans) := NewPreH12
    have PreH14 : (ExtractedDigitBuffer x_pre digits_l_2 m (0 : Int)) := NewPreH15
    have PreH16 : (InnerCandidateDigitProgress dp_l i j answer_before ans) := NewPreH17
    have PreH17 : (AccumulatedDigitSumCorrect x_pre i answer_before) := NewPreH18
    have PreH18 : (OuterDigitPositionPower i power_ll) := NewPreH19
    have PreH19 : (DigitDPTable dp_l) := NewPreH20
    have hj : j = Znth i digits_l_2 0 := by omega
    obtain ⟨choice, hchoice, hans⟩ := PreH16
    have hsem := AccumulatedDigitSumCorrect_step x_pre dp_l digits_l_2 m i answer_before choice PreH2 ⟨PreH5, PreH6⟩ PreH7 PreH14 PreH19 (hj ▸ hchoice) PreH17
    have hpower : power_ll = Z.pow 10 (i-1) := by
      rcases PreH18 with ⟨hz, _⟩ | ⟨_, he⟩
      · omega
      · exact he
    have hd : Znth i digits_l_2 0 = Z.modulo (Z.div x_pre power_ll) 10 := by
      rw [hpower]
      exact PreH14.2.2.2.1 i (by omega)
    rw [digit_sum_program_answer x_pre power_ll ans answer_before choice (Znth i digits_l_2 0) (by omega) (outer_power_pos i power_ll PreH5 PreH18) PreH12 hd hans, hpower]
    exact hsem

theorem aux_prefix_digits_sum_entail_wit_10_split_goal_3 : (forall (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l_2 : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j >= (Znth i digits_l_2 (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l_2 (0 : Int)))) (PreH9 : ((Znth i digits_l_2 (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l_2 (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : (ExtractedDigitBuffer x_pre digits_l_2 m (0 : Int))) (PreH15 : (ExtractedDigitCount x_pre m)) (PreH16 : (InnerCandidateDigitProgressLegacy x_pre dp_l digits_l_2 i j answer_before ans)) (PreH17 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH18 : (OuterDigitPositionPower i power_ll)) (PreH19 : (DigitDPTable dp_l)) ,
  (OuterDigitPositionProgress x_pre dp_l digits_l_2 (i - 1) (signed_last_nbits ((Z.rem (ans + (Z.rem ((Z.rem ((Z.rem x_pre power_ll) + 1) 1000000007) * (Z.rem (Z.quot x_pre power_ll) 10)) 1000000007)) 1000000007)) (32)))) := by

  intro x_pre dp_l power_ll answer_before ans j digits_l_2 m i tmpx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    exact outer_progress_predecessor__prefix_inner_outer_scan x_pre dp_l digits_l_2 power_ll answer_before ans j m i PreH1 PreH2 PreH5 PreH6 PreH7 ⟨PreH8, PreH9⟩ PreH10 PreH11 ⟨PreH12, PreH13⟩ PreH14 PreH15 PreH16 PreH18

theorem proof_of_prefix_digits_sum_entail_wit_10_split_goal_3 : prefix_digits_sum_entail_wit_10_split_goal_3 := by
  unfold prefix_digits_sum_entail_wit_10_split_goal_3
  intro dp_l x_pre power_ll answer_before ans j digits_l_2 m i tmpx NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH5 : (1 <= i) := NewPreH5
    have PreH18 : (OuterDigitPositionPower i power_ll) := NewPreH19
    have hp := outer_power_pos i power_ll PreH5 PreH18
    have hr := rem_nonneg_bounds x_pre power_ll (by omega) hp
    have hl := rem_nonneg_bounds (Z.rem x_pre power_ll+1) 1000000007 (by omega) (by decide)
    have hq : 0 ≤ Z.quot x_pre power_ll := Int.tdiv_nonneg (by omega) (by omega)
    have hd := rem_nonneg_bounds (Z.quot x_pre power_ll) 10 hq (by decide)
    have hm := rem_nonneg_bounds (Z.rem (Z.rem x_pre power_ll+1) 1000000007 * Z.rem (Z.quot x_pre power_ll) 10) 1000000007 (Int.mul_nonneg hl.1 hd.1) (by decide)
    rw [rem_eq_mod (ans + Z.rem (Z.rem (Z.rem x_pre power_ll+1) 1000000007 * Z.rem (Z.quot x_pre power_ll) 10) 1000000007) 1000000007 (by omega) (by decide)]
    exact (signed_modulus_range__prefix_inner_outer_scan _).2

theorem proof_of_prefix_digits_sum_entail_wit_10_split_goal_4 : prefix_digits_sum_entail_wit_10_split_goal_4 := by
  unfold prefix_digits_sum_entail_wit_10_split_goal_4
  intro dp_l x_pre power_ll answer_before ans j digits_l_2 m i tmpx NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH5 : (1 <= i) := NewPreH5
    have PreH18 : (OuterDigitPositionPower i power_ll) := NewPreH19
    have hp := outer_power_pos i power_ll PreH5 PreH18
    have hr := rem_nonneg_bounds x_pre power_ll (by omega) hp
    have hl := rem_nonneg_bounds (Z.rem x_pre power_ll+1) 1000000007 (by omega) (by decide)
    have hq : 0 ≤ Z.quot x_pre power_ll := Int.tdiv_nonneg (by omega) (by omega)
    have hd := rem_nonneg_bounds (Z.quot x_pre power_ll) 10 hq (by decide)
    have hm := rem_nonneg_bounds (Z.rem (Z.rem x_pre power_ll+1) 1000000007 * Z.rem (Z.quot x_pre power_ll) 10) 1000000007 (Int.mul_nonneg hl.1 hd.1) (by decide)
    rw [rem_eq_mod (ans + Z.rem (Z.rem (Z.rem x_pre power_ll+1) 1000000007 * Z.rem (Z.quot x_pre power_ll) 10) 1000000007) 1000000007 (by omega) (by decide)]
    exact (signed_modulus_range__prefix_inner_outer_scan _).1

theorem proof_of_prefix_digits_sum_entail_wit_10 : prefix_digits_sum_entail_wit_10 := by
  unfold prefix_digits_sum_entail_wit_10
  right
  intro dp_l x_pre power_ll answer_before ans j digits_l_2 m i tmpx NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20
  have PreH1 : (j >= (Znth i digits_l_2 (0 : Int))) := NewPreH1
  have PreH2 : (1 <= x_pre) := NewPreH2
  have PreH3 : (x_pre <= 1000000000000000000) := NewPreH3
  have PreH4 : (tmpx = (0 : Int)) := NewPreH4
  have PreH5 : (1 <= i) := NewPreH5
  have PreH6 : (i <= m) := NewPreH6
  have PreH7 : (m <= 19) := NewPreH7
  have PreH8 : ((0 : Int) <= (Znth i digits_l_2 (0 : Int))) := NewPreH8
  have PreH9 : ((Znth i digits_l_2 (0 : Int)) < 10) := NewPreH9
  have PreH10 : ((0 : Int) <= j) := NewPreH10
  have PreH11 : (j <= (Znth i digits_l_2 (0 : Int))) := NewPreH11
  have PreH12 : ((0 : Int) <= ans) := NewPreH12
  have PreH13 : (ans < 1000000007) := NewPreH13
  have PreH14 : (ExtractedDigitBuffer x_pre digits_l_2 m (0 : Int)) := NewPreH15
  have PreH15 : (ExtractedDigitCount x_pre m) := NewPreH16
  have PreH16 : (InnerCandidateDigitProgress dp_l i j answer_before ans) := NewPreH17
  have PreH17 : (AccumulatedDigitSumCorrect x_pre i answer_before) := NewPreH18
  have PreH18 : (OuterDigitPositionPower i power_ll) := NewPreH19
  have PreH19 : (DigitDPTable dp_l) := NewPreH20
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | (solve | simp only [Zlength_replace_Znth]; omega)
      | omega
      | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
      | exact proof_of_prefix_digits_sum_entail_wit_10_split_goal_1 dp_l x_pre power_ll answer_before ans j digits_l_2 m i tmpx NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20
      | exact proof_of_prefix_digits_sum_entail_wit_10_split_goal_2 dp_l x_pre power_ll answer_before ans j digits_l_2 m i tmpx NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20
      | exact aux_prefix_digits_sum_entail_wit_10_split_goal_3 x_pre dp_l power_ll answer_before ans j digits_l_2 m i tmpx PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
      | exact proof_of_prefix_digits_sum_entail_wit_10_split_goal_3 dp_l x_pre power_ll answer_before ans j digits_l_2 m i tmpx NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20
      | exact proof_of_prefix_digits_sum_entail_wit_10_split_goal_4 dp_l x_pre power_ll answer_before ans j digits_l_2 m i tmpx NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15 NewPreH16 NewPreH17 NewPreH18 NewPreH19 NewPreH20


theorem proof_of_prefix_digits_sum_return_wit_1_split_goal_1 : prefix_digits_sum_return_wit_1_split_goal_1 := by
  unfold prefix_digits_sum_return_wit_1_split_goal_1
  intro dp_l x_pre digits_pre power_ll digits_l ans m i tmpx NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH13 : (AccumulatedDigitSumCorrect x_pre i ans) := NewPreH13
    dump_pre_spatial
    rcases PreH13 with ⟨_, hs⟩ | ⟨hi, _⟩
    · exact hs
    · omega

theorem proof_of_prefix_digits_sum_return_wit_1_split_goal_spatial : prefix_digits_sum_return_wit_1_split_goal_spatial := by
  unfold prefix_digits_sum_return_wit_1_split_goal_spatial
  intro dp_l x_pre digits_pre power_ll digits_l ans m i tmpx NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15
  exact intArray.full_to_undef_full digits_pre 20 digits_l


theorem proof_of_prefix_digits_sum_return_wit_1 : prefix_digits_sum_return_wit_1 := by
  unfold prefix_digits_sum_return_wit_1
  right
  intro dp_l x_pre digits_pre power_ll digits_l ans m i tmpx NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15
  have PreH1 : (i <= (0 : Int)) := NewPreH1
  have PreH2 : (1 <= x_pre) := NewPreH2
  have PreH3 : (x_pre <= 1000000000000000000) := NewPreH3
  have PreH4 : (tmpx = (0 : Int)) := NewPreH4
  have PreH5 : ((0 : Int) <= i) := NewPreH5
  have PreH6 : (i <= m) := NewPreH6
  have PreH7 : (m <= 19) := NewPreH7
  have PreH8 : ((0 : Int) <= ans) := NewPreH8
  have PreH9 : (ans < 1000000007) := NewPreH9
  have PreH10 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int)) := NewPreH11
  have PreH11 : (ExtractedDigitCount x_pre m) := NewPreH12
  have PreH13 : (AccumulatedDigitSumCorrect x_pre i ans) := NewPreH13
  have PreH14 : (OuterDigitPositionPower i power_ll) := NewPreH14
  have PreH15 : (DigitDPTable dp_l) := NewPreH15
  split_pure_spatial
  · exact proof_of_prefix_digits_sum_return_wit_1_split_goal_spatial dp_l x_pre digits_pre power_ll digits_l ans m i tmpx NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15
  · exact proof_of_prefix_digits_sum_return_wit_1_split_goal_1 dp_l x_pre digits_pre power_ll digits_l ans m i tmpx NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15


theorem proof_of_prefix_digits_sum_return_wit_2_split_goal_1 : prefix_digits_sum_return_wit_2_split_goal_1 := by
  unfold prefix_digits_sum_return_wit_2_split_goal_1
  intro dp_l x_pre NewPreH1 NewPreH2 NewPreH3 NewPreH4
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    exact PrefixDigitSum_nonpositive x_pre (by omega)

theorem proof_of_prefix_digits_sum_return_wit_2 : prefix_digits_sum_return_wit_2 := by
  unfold prefix_digits_sum_return_wit_2
  right
  intro dp_l x_pre NewPreH1 NewPreH2 NewPreH3 NewPreH4
  have PreH1 : (x_pre < 1) := NewPreH1
  have PreH2 : ((0 : Int) <= x_pre) := NewPreH2
  have PreH3 : (x_pre <= 1000000000000000000) := NewPreH3
  have PreH4 : (DigitDPTable dp_l) := NewPreH4
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | assumption
      | (solve | simp only [Zlength_replace_Znth]; omega)
      | omega
      | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
      | exact proof_of_prefix_digits_sum_return_wit_2_split_goal_1 dp_l x_pre NewPreH1 NewPreH2 NewPreH3 NewPreH4


theorem proof_of_interval_digits_sum_return_wit_1 : interval_digits_sum_return_wit_1 := by
  unfold interval_digits_sum_return_wit_1
  right
  intro x_pre y_pre ans1 ans2 PreH1 PreH2 PreH3 PreH4 PreH5
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    have he := normalized_outer_rem__interval_bridge (ans1-ans2)
    simp only [digit_sum_modulus] at he
    rw [he]
    exact IntervalDigitSum_from_prefixes__interval_bridge x_pre y_pre ans2 ans1 PreH1 PreH2 PreH5 PreH4

theorem proof_of_interval_digits_sum_safety_wit_10 : interval_digits_sum_safety_wit_10 := by
  unfold interval_digits_sum_safety_wit_10
  right
  intro x_pre y_pre ans1 ans2 PreH1 PreH2 PreH3 PreH4 PreH5
  have hr := rem_bounds (ans1-ans2) 1000000007 (by decide)
  split_pures <;> dump_pre_spatial <;> simp only [INT_MIN, INT_MAX] <;> omega

theorem proof_of_interval_digits_sum_safety_wit_12 : interval_digits_sum_safety_wit_12 := by
  unfold interval_digits_sum_safety_wit_12
  right
  intro x_pre y_pre ans1 ans2 PreH1 PreH2 PreH3 PreH4 PreH5
  have h1 := PrefixDigitSum_range y_pre ans1 PreH4
  have h2 := PrefixDigitSum_range (x_pre-1) ans2 PreH5
  simp only [digit_sum_modulus] at h1 h2
  split_pures <;> dump_pre_spatial <;> simp only [INT_MIN, INT_MAX] <;> omega

theorem proof_of_interval_digits_sum_entail_wit_1 : interval_digits_sum_entail_wit_1 := by
  unfold interval_digits_sum_entail_wit_1
  right
  intro x_pre y_pre PreH1 PreH2 PreH3
  simp only [Int.zero_mul, Int.add_zero]
  cancel

theorem proof_of_interval_digits_sum_entail_wit_2 : interval_digits_sum_entail_wit_2 := by
  unfold interval_digits_sum_entail_wit_2
  right
  intro x_pre y_pre power_l dp_l retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7
  simp only [Int.zero_mul, Int.add_zero]
  change (intArray.full (&("dp")) 200 dp_l ** intArray.undef_full (&("digits")) 20) **
      intArray.full (&("power")) 20 power_l
    |-- (intArray.undef_full (&("dp")) 200 ** intArray.undef_full (&("power")) 20) **
      intArray.undef_full (&("digits")) 20
  refine naive_C_Rules.toContext.derivable1_trans _
    ((intArray.undef_full (&("dp")) 200 ** intArray.undef_full (&("digits")) 20) **
      intArray.undef_full (&("power")) 20) _ ?_ ?_
  · exact naive_C_Rules.toContext.derivable1_sepcon_mono _ _ _ _
      (naive_C_Rules.toContext.derivable1_sepcon_mono _ _ _ _
        (intArray.full_to_undef_full (&("dp")) 200 dp_l)
        (naive_C_Rules.toContext.derivable1_refl _))
      (intArray.full_to_undef_full (&("power")) 20 power_l)
  · cancel

end SimpleC.EE.LLM_bench.Algorithms.annoying_math_homework.annoying_math_homework_proof_manual
