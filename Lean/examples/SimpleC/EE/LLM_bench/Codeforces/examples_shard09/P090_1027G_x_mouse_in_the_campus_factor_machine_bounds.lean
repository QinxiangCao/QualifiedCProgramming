import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_factor_consumer
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
open AUXLib AUXLib.Prime MaxMinLib
local infixl:70 " mod " => Z.modulo
namespace P090_FactorMachineBounds

theorem strict_trial_numeric_components (m candidate remainder : Int) (pr pe : List Int) :
    StrictTrialState m candidate remainder pr pe → 2 ≤ candidate ∧ 0 < remainder ∧ remainder ≤ m := by
  intro h
  exact ⟨h.1.2.2.1,h.1.2.2.2.1⟩

theorem strict_trial_candidate_bound_under_guard (m candidate remainder : Int) (pr pe : List Int) :
    StrictTrialState m candidate remainder pr pe → m ≤ FactorInputLimit → candidate*candidate ≤ remainder →
    candidate ≤ FactorCandidateGuardLimit := by
  intro h hm hg
  obtain ⟨hc,hr,hrm⟩ := strict_trial_numeric_components m candidate remainder pr pe h
  unfold FactorInputLimit FactorCandidateGuardLimit at *
  nlinarith

theorem strict_trial_guard_square_range (m candidate remainder : Int) (pr pe : List Int) :
    StrictTrialState m candidate remainder pr pe → m ≤ FactorInputLimit → candidate*candidate ≤ remainder →
    0 ≤ candidate*candidate ∧ candidate*candidate ≤ FactorInputLimit := by
  intro h hm hg
  obtain ⟨hc,hr,hrm⟩ := strict_trial_numeric_components m candidate remainder pr pe h
  constructor <;> nlinarith

theorem strict_factor_exponent_cap (m candidate original remainder exponent : Int) (pr pe : List Int) :
    StrictFactorAtPrime m candidate original remainder exponent pr pe → m ≤ FactorInputLimit → exponent < 47 := by
  rintro ⟨hs,hp,hm,he,hd,hb⟩ hlimit
  obtain ⟨hc,ho,hom⟩ := strict_trial_numeric_components m candidate original pr pe hs
  have hpow := coq_pow_pos candidate exponent (by omega) he
  have hmono : Z.pow 2 exponent ≤ Z.pow candidate exponent := by
    rw [coq_pow_nat 2 exponent he,coq_pow_nat candidate exponent he]
    exact pow_le_pow_left₀ (by omega) hc _
  by_contra hn
  have hlarge := coq_pow_mono 2 47 exponent (by omega) (by omega) (by omega)
  have h47 : Z.pow 2 47 = 140737488355328 := by decide
  unfold FactorInputLimit at hlimit
  rw [h47] at hlarge
  nlinarith

theorem strict_factor_exponent_nonnegative_bounded (m candidate original remainder exponent : Int) (pr pe : List Int) :
    StrictFactorAtPrime m candidate original remainder exponent pr pe → m ≤ FactorInputLimit → 0 ≤ exponent ∧ exponent ≤ 46 := by
  intro h hm
  have hc := strict_factor_exponent_cap m candidate original remainder exponent pr pe h hm
  exact ⟨h.2.2.2.1,by omega⟩

theorem factor_machine_trial_init (m : Int) :
    0 < m → m ≤ FactorInputLimit → FactorMachineTrialState m 2 m [] [] := by
  intro hm hl
  exact ⟨strict_trial_init m hm,hl,by decide⟩

theorem factor_machine_trial_skip (m candidate remainder : Int) (pr pe : List Int) :
    FactorMachineTrialState m candidate remainder pr pe → candidate*candidate ≤ remainder → remainder mod candidate ≠ 0 →
    FactorMachineTrialState m (candidate+1) remainder pr pe := by
  rintro ⟨h,hm,hc⟩ hg hn
  have hb := strict_trial_candidate_bound_under_guard m candidate remainder pr pe h hm hg
  refine ⟨strict_trial_skip m candidate remainder pr pe h hn,hm,?_⟩
  unfold FactorCandidateGuardLimit FactorCandidateStateLimit at *
  omega

theorem factor_machine_enter_prime (m candidate remainder : Int) (pr pe : List Int) :
    FactorMachineTrialState m candidate remainder pr pe → candidate*candidate ≤ remainder → remainder mod candidate = 0 →
    FactorMachineAtPrime m candidate remainder remainder 0 pr pe := by
  rintro ⟨h,hm,hc⟩ hg hd
  exact ⟨strict_trial_enter_factor m candidate remainder pr pe (strict_trial_numeric_components m candidate remainder pr pe h).1 h hd,
    hm,strict_trial_candidate_bound_under_guard m candidate remainder pr pe h hm hg⟩

theorem factor_machine_divide_step (m candidate original remainder remainder' exponent : Int) (pr pe : List Int) :
    FactorMachineAtPrime m candidate original remainder exponent pr pe → remainder = candidate*remainder' →
    FactorMachineAtPrime m candidate original remainder' (exponent+1) pr pe := by
  rintro ⟨h,hm,hc⟩ hd
  exact ⟨strict_factor_divide_step m candidate original remainder remainder' exponent pr pe h hd,hm,hc⟩

theorem factor_machine_active_exponent_bounds (m candidate original remainder exponent : Int) (pr pe : List Int) :
    FactorMachineAtPrime m candidate original remainder exponent pr pe → 0 ≤ exponent ∧ exponent ≤ 46 := by
  rintro ⟨h,hm,hc⟩
  exact strict_factor_exponent_nonnegative_bounded m candidate original remainder exponent pr pe h hm

theorem factor_machine_finish_prime (m candidate original remainder exponent : Int) (pr pe : List Int) :
    FactorMachineAtPrime m candidate original remainder exponent pr pe → remainder mod candidate ≠ 0 → Zlength pr < 64 →
    FactorMachineTrialState m (candidate+1) remainder (pr++[candidate]) (pe++[exponent]) := by
  rintro ⟨h,hm,hc⟩ hn hr
  refine ⟨strict_factor_finish_prime m candidate original remainder exponent pr pe h hn hr,hm,?_⟩
  unfold FactorCandidateGuardLimit FactorCandidateStateLimit at *
  omega

theorem factor_machine_candidate_square_signed64 (m candidate remainder : Int) (pr pe : List Int) :
    FactorMachineTrialState m candidate remainder pr pe → 0 ≤ candidate*candidate ∧ candidate*candidate ≤ Signed64Max := by
  rintro ⟨h,hm,hc⟩
  have hl := (strict_trial_numeric_components m candidate remainder pr pe h).1
  unfold FactorCandidateStateLimit Signed64Max at *
  constructor <;> nlinarith

theorem factor_machine_candidate_increment_signed64 (m candidate remainder : Int) (pr pe : List Int) :
    FactorMachineTrialState m candidate remainder pr pe → 0 ≤ candidate+1 ∧ candidate+1 ≤ Signed64Max := by
  rintro ⟨h,hm,hc⟩
  have hl := (strict_trial_numeric_components m candidate remainder pr pe h).1
  unfold FactorCandidateStateLimit Signed64Max at *
  omega

theorem factor_machine_square_guard_no_wrap (m candidate remainder : Int) (pr pe : List Int) (square : Int) :
    FactorMachineTrialState m candidate remainder pr pe → square = candidate*candidate →
    (0 ≤ square ∧ square ≤ Signed64Max) ∧ (square ≤ remainder ↔ candidate*candidate ≤ remainder) := by
  intro h hs
  subst square
  exact ⟨factor_machine_candidate_square_signed64 m candidate remainder pr pe h,Iff.rfl⟩

theorem factor_machine_finalize_from_failed_square_guard (m candidate remainder : Int) (pr pe : List Int) (square : Int) :
    FactorMachineTrialState m candidate remainder pr pe → square = candidate*candidate → ¬square ≤ remainder →
    (0 ≤ square ∧ square ≤ Signed64Max) ∧ square > remainder ∧ ∃ final_pr final_pe, ValidFactorTable m final_pr final_pe := by
  intro h hs hn
  subst square
  exact ⟨factor_machine_candidate_square_signed64 m candidate remainder pr pe h,by omega,
    strict_trial_finalize_from_failed_guard m candidate remainder pr pe h.1 h.2.1 hn⟩
end P090_FactorMachineBounds
export P090_FactorMachineBounds (strict_trial_numeric_components strict_trial_candidate_bound_under_guard
  strict_trial_guard_square_range strict_factor_exponent_cap strict_factor_exponent_nonnegative_bounded
  factor_machine_trial_init factor_machine_trial_skip factor_machine_enter_prime factor_machine_divide_step
  factor_machine_active_exponent_bounds factor_machine_finish_prime factor_machine_candidate_square_signed64
  factor_machine_candidate_increment_signed64 factor_machine_square_guard_no_wrap factor_machine_finalize_from_failed_square_guard)
end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
