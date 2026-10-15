import SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_goal
import SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_proof_auto

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open euler_theorem_inverse_goal euler_theorem_inverse_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

-- Previously proved auxiliary statements retained for proof audits.
theorem proof_of_euler_phi_entail_wit_1_split_goal_1 : euler_phi_entail_wit_1_split_goal_1 := by
  unfold euler_phi_entail_wit_1_split_goal_1
  intro value_pre NewPreH1 NewPreH2
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    refine ⟨⟨⟨1,by simp⟩,?_⟩,?_⟩
    · intro op rp ho hr
      unfold EulerPhi at ho hr
      rw [ho,hr]
      grind
    · intro p hp hl _
      have := hp.1
      omega

theorem proof_of_euler_phi_entail_wit_1 : euler_phi_entail_wit_1 := by
  unfold euler_phi_entail_wit_1
  right
  intro value_pre NewPreH1 NewPreH2
  have PreH1 : (2 <= value_pre) := NewPreH1
  have PreH2 : (value_pre <= 46341) := NewPreH2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | assumption
    | omega
    | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
    | (solve | Goal_apply (proof_of_euler_phi_entail_wit_1_split_goal_1 value_pre NewPreH1 NewPreH2))
    | exact (proof_of_euler_phi_entail_wit_1_split_goal_1 value_pre NewPreH1 NewPreH2)
    | trivial

theorem proof_of_euler_phi_entail_wit_2_split_goal_1 : euler_phi_entail_wit_2_split_goal_1 := by
  unfold euler_phi_entail_wit_2_split_goal_1
  intro value_pre factor result value NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH1 : ((Z.rem value factor) = (0 : Int)) := NewPreH1
    have PreH3 : (2 <= value_pre) := NewPreH3
    have PreH5 : (1 <= value) := NewPreH5
    have PreH7 : (1 <= result) := NewPreH7
    have PreH9 : (2 <= factor) := NewPreH9
    have PreH13 : (EulerPhiProgress value_pre factor value result) := NewPreH11
    have hm : Z.modulo value factor=0 := Int.fmod_eq_zero_of_dvd ((Z.divide_iff_dvd _ _).1 ((Z.rem_divide value factor (by omega)).1 PreH1))
    exact euler_phi_removal_start__euler_phi_setup_removal value_pre factor value result PreH3 PreH5 PreH7 PreH9 hm PreH13

theorem proof_of_euler_phi_entail_wit_2 : euler_phi_entail_wit_2 := by
  unfold euler_phi_entail_wit_2
  right
  intro value_pre factor result value NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11
  have PreH1 : ((Z.rem value factor) = (0 : Int)) := NewPreH1
  have PreH2 : ((factor * factor) <= value) := NewPreH2
  have PreH3 : (2 <= value_pre) := NewPreH3
  have PreH4 : (value_pre <= 46341) := NewPreH4
  have PreH5 : (1 <= value) := NewPreH5
  have PreH6 : (value <= value_pre) := NewPreH6
  have PreH7 : (1 <= result) := NewPreH7
  have PreH8 : (result <= value_pre) := NewPreH8
  have PreH9 : (2 <= factor) := NewPreH9
  have PreH10 : (factor <= 216) := NewPreH10
  have PreH11 : ((0 : Int) <= (factor * factor)) := Int.mul_nonneg (by omega) (by omega)
  have PreH12 : ((factor * factor) <= INT_MAX) := by simp only [INT_MAX, INT_MIN]; omega
  have PreH13 : (EulerPhiProgress value_pre factor value result) := NewPreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | assumption
    | omega
    | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
    | (solve | Goal_apply (proof_of_euler_phi_entail_wit_2_split_goal_1 value_pre factor result value NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11))
    | exact (proof_of_euler_phi_entail_wit_2_split_goal_1 value_pre factor result value NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11)
    | trivial

theorem proof_of_euler_phi_entail_wit_3_split_goal_1 : euler_phi_entail_wit_3_split_goal_1 := by
  unfold euler_phi_entail_wit_3_split_goal_1
  intro value_pre factor result value NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH1 : ((Z.rem value factor) = (0 : Int)) := NewPreH1
    have PreH10 : (EulerPhiRemovalProgress value_pre factor value result) := NewPreH10
    have hm : Z.modulo value factor=0 := Int.fmod_eq_zero_of_dvd ((Z.divide_iff_dvd _ _).1 ((Z.rem_divide value factor (by omega)).1 PreH1))
    rewrite [show Z.quot value factor=Z.div value factor from (Int.fdiv_eq_tdiv_of_nonneg (by omega) (by omega)).symm]
    rcases PreH10 with ⟨before,removed,hr,hbefore,hfb,hfr,hprogress,hcompletion⟩
    have hs : Z.pow factor (removed+1)=Z.pow factor removed*factor := by
      cases removed with
      | ofNat m => exact Int.pow_succ factor m
      | negSucc m => omega
    have hdiv := Int.fmod_add_mul_fdiv value factor
    change value.fmod factor=0 at hm
    rw [hm] at hdiv
    refine ⟨before,removed+1,by omega,?_,hfb,hfr,hprogress,?_⟩
    · rw [hs]
      change before=value.fdiv factor*(Z.pow factor removed*factor)
      grind
    · exact EulerPhiFactorCompletion_divide value_pre factor value result (by omega) hm hcompletion

theorem proof_of_euler_phi_entail_wit_3_split_goal_2 : euler_phi_entail_wit_3_split_goal_2 := by
  unfold euler_phi_entail_wit_3_split_goal_2
  intro value_pre factor result value NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    apply Z.quot_le_upper_bound value factor value_pre (by omega)
    have hm := Int.mul_le_mul_of_nonneg_right (by omega : 1≤factor) (by omega : 0≤value_pre)
    omega

theorem proof_of_euler_phi_entail_wit_3_split_goal_3 : euler_phi_entail_wit_3_split_goal_3 := by
  unfold euler_phi_entail_wit_3_split_goal_3
  intro value_pre factor result value NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH1 : ((Z.rem value factor) = (0 : Int)) := NewPreH1
    have PreH4 : (1 <= value) := NewPreH4
    have PreH8 : (2 <= factor) := NewPreH8
    have hd := (Z.rem_divide value factor (by omega)).1 PreH1
    exact (euler_exact_positive_quotient_bounds__euler_phi_factor_completion value factor PreH4 PreH8 hd).1

theorem proof_of_euler_phi_entail_wit_3 : euler_phi_entail_wit_3 := by
  unfold euler_phi_entail_wit_3
  right
  intro value_pre factor result value NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10
  have PreH1 : ((Z.rem value factor) = (0 : Int)) := NewPreH1
  have PreH2 : (2 <= value_pre) := NewPreH2
  have PreH3 : (value_pre <= 46341) := NewPreH3
  have PreH4 : (1 <= value) := NewPreH4
  have PreH5 : (value <= value_pre) := NewPreH5
  have PreH6 : (1 <= result) := NewPreH6
  have PreH7 : (result <= value_pre) := NewPreH7
  have PreH8 : (2 <= factor) := NewPreH8
  have PreH9 : (factor <= 216) := NewPreH9
  have PreH10 : (EulerPhiRemovalProgress value_pre factor value result) := NewPreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | assumption
    | omega
    | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
    | (solve | Goal_apply (proof_of_euler_phi_entail_wit_3_split_goal_1 value_pre factor result value NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10))
    | exact (proof_of_euler_phi_entail_wit_3_split_goal_1 value_pre factor result value NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10)
    | (solve | Goal_apply (proof_of_euler_phi_entail_wit_3_split_goal_2 value_pre factor result value NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10))
    | exact (proof_of_euler_phi_entail_wit_3_split_goal_2 value_pre factor result value NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10)
    | (solve | Goal_apply (proof_of_euler_phi_entail_wit_3_split_goal_3 value_pre factor result value NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10))
    | exact (proof_of_euler_phi_entail_wit_3_split_goal_3 value_pre factor result value NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10)
    | trivial

theorem aux_euler_phi_entail_wit_4_split_goal_1 : (forall (value_pre : Int) (factor : Int) (result : Int) (value : Int) (PreH1 : ((Z.rem value factor) ≠ (0 : Int))) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= factor)) (PreH9 : (factor <= 216)) (PreH10 : (EulerPhiRemovalProgress value_pre factor value result)) ,
  (((Z.quot result factor) * (factor - 1)) <= INT_MAX)) := by

  intro value_pre factor result value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    rcases PreH10 with ⟨before,removed,hr,hbefore,hfb,hfr,hprogress,hcompletion⟩
    have hb := euler_exact_positive_quotient_bounds__euler_phi_factor_completion result factor PreH6 PreH8 hfr
    change _≤2147483647
    omega

theorem proof_of_euler_phi_entail_wit_4_1_split_goal_3 : euler_phi_entail_wit_4_1_split_goal_3 := by
  unfold euler_phi_entail_wit_4_1_split_goal_3
  intro value_pre factor result value NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH6 : (1 <= result) := NewPreH6
    have PreH8 : (2 <= factor) := NewPreH8
    have PreH10 : (EulerPhiRemovalProgress value_pre factor value result) := NewPreH10
    rcases PreH10 with ⟨before,removed,hr,hbefore,hfb,hfr,hprogress,hcompletion⟩
    have hb := euler_exact_positive_quotient_bounds__euler_phi_factor_completion result factor PreH6 PreH8 hfr
    omega

theorem aux_euler_phi_entail_wit_4_split_goal_3 : (forall (value_pre : Int) (factor : Int) (result : Int) (value : Int) (PreH1 : ((Z.rem value factor) ≠ (0 : Int))) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= factor)) (PreH9 : (factor <= 216)) (PreH10 : (EulerPhiRemovalProgress value_pre factor value result)) ,
  ((0 : Int) <= ((Z.quot result factor) * (factor - 1)))) := by

  intro value_pre factor result value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    rcases PreH10 with ⟨before,removed,hr,hbefore,hfb,hfr,hprogress,hcompletion⟩
    have hb := euler_exact_positive_quotient_bounds__euler_phi_factor_completion result factor PreH6 PreH8 hfr
    exact hb.2.1

theorem proof_of_euler_phi_entail_wit_4_1 : euler_phi_entail_wit_4_1 := by
  unfold euler_phi_entail_wit_4_1
  right
  intro original factor result value hrem ho0 ho hv0 hv hr0 hr hf0 hf hs
  have hnext := euler_completed_progress__euler_phi_factor_completion original factor value result hv0 hr0 hf0 hrem hs
  have hfrontier := euler_active_frontier_bound__euler_phi_factor_completion original factor value result hf0 hf hs
  obtain ⟨before,removed,hremoved,hbefore,hvalue,hresult,hprogress,hcompletion⟩ := hs
  have hb := euler_exact_positive_quotient_bounds__euler_phi_factor_completion result factor hr0 hf0 hresult
  have hmul := Int.mul_le_mul_of_nonneg_left (show (1 : Int) ≤ factor-1 by omega)
    (show 0 ≤ Z.quot result factor by omega)
  simp only [Int.mul_one] at hmul
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_euler_phi_entail_wit_4_1_split_goal_1 : euler_phi_entail_wit_4_1_split_goal_1 := by
  unfold euler_phi_entail_wit_4_1_split_goal_1
  intro value_pre factor result value NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH3 : (1 <= value) := NewPreH4
    have PreH5 : (1 <= result) := NewPreH6
    have PreH7 : (2 <= factor) := NewPreH8
    have PreH9 : ((Z.rem value factor) ≠ (0 : Int)) := NewPreH1
    have PreH15 : (EulerPhiRemovalProgress value_pre factor value result) := NewPreH10
    exact euler_completed_progress__euler_phi_factor_completion value_pre factor value result PreH3 PreH5 PreH7 PreH9 PreH15

theorem proof_of_euler_phi_entail_wit_4_1_split_goal_2 : euler_phi_entail_wit_4_1_split_goal_2 := by
  unfold euler_phi_entail_wit_4_1_split_goal_2
  intro value_pre factor result value NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH7 : (2 <= factor) := NewPreH8
    have PreH8 : (factor <= 216) := NewPreH9
    have PreH15 : (EulerPhiRemovalProgress value_pre factor value result) := NewPreH10
    exact euler_active_frontier_bound__euler_phi_factor_completion value_pre factor value result PreH7 PreH8 PreH15


theorem proof_of_euler_phi_entail_wit_4_2_split_goal_1 : euler_phi_entail_wit_4_2_split_goal_1 := by
  unfold euler_phi_entail_wit_4_2_split_goal_1
  intro value_pre factor result value NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH1 : ((Z.rem value factor) ≠ (0 : Int)) := NewPreH1
    have PreH9 : (2 <= factor) := NewPreH9
    have PreH13 : (EulerPhiProgress value_pre factor value result) := NewPreH11
    exact euler_progress_advance_nondivisor__euler_phi_factor_completion value_pre factor value result PreH9 PreH1 PreH13

theorem proof_of_euler_phi_entail_wit_4_2 : euler_phi_entail_wit_4_2 := by
  unfold euler_phi_entail_wit_4_2
  right
  intro original factor result value hrem hsq ho0 ho hv0 hv hr0 hr hf0 hf hs
  have hnext := euler_progress_advance_nondivisor__euler_phi_factor_completion original factor value result hf0 hrem hs
  have hfrontier : factor+1 ≤ 216 := by nlinarith
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_euler_phi_return_wit_1_split_goal_1 : euler_phi_return_wit_1_split_goal_1 := by
  unfold euler_phi_return_wit_1_split_goal_1
  intro value_pre frontier value result NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH8 : (2 <= frontier) := NewPreH8
    have PreH12 : ((frontier * frontier) > value) := NewPreH10
    have PreH18 : (EulerPhiProgress value_pre frontier value result) := NewPreH15
    exact euler_progress_terminal_prime__euler_phi_final_results value_pre frontier value result (by omega) PreH8 PreH12 PreH18

theorem proof_of_euler_phi_return_wit_1 : euler_phi_return_wit_1 := by
  unfold euler_phi_return_wit_1
  right
  intro value_pre frontier value result NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15
  have PreH1 : (value ≠ 1) := NewPreH1
  have PreH2 : (2 <= value_pre) := NewPreH2
  have PreH3 : (value_pre <= 46341) := NewPreH3
  have PreH4 : (1 <= value) := NewPreH4
  have PreH5 : (value <= value_pre) := NewPreH5
  have PreH6 : (1 <= result) := NewPreH6
  have PreH7 : (result <= value_pre) := NewPreH7
  have PreH8 : (2 <= frontier) := NewPreH8
  have PreH9 : (frontier <= 216) := NewPreH9
  have PreH10 : ((0 : Int) <= (frontier * frontier)) := by first | assumption | (simp only [INT_MAX, INT_MIN] <;> omega) | positivity | nlinarith
  have PreH11 : ((frontier * frontier) <= INT_MAX) := by simp only [INT_MAX, INT_MIN]; nlinarith
  have PreH12 : ((frontier * frontier) > value) := NewPreH10
  have PreH13 : ((Z.rem result value) = (0 : Int)) := NewPreH11
  have PreH14 : (1 <= (Z.quot result value)) := NewPreH12
  have PreH15 : ((0 : Int) <= ((Z.quot result value) * (value - 1))) := NewPreH13
  have PreH16 : (((Z.quot result value) * (value - 1)) <= value_pre) := NewPreH14
  have PreH17 : (((Z.quot result value) * (value - 1)) <= INT_MAX) := by simp only [INT_MAX, INT_MIN]; omega
  have PreH18 : (EulerPhiProgress value_pre frontier value result) := NewPreH15
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | assumption
    | omega
    | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
    | (solve | Goal_apply (proof_of_euler_phi_return_wit_1_split_goal_1 value_pre frontier value result NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15))
    | exact (proof_of_euler_phi_return_wit_1_split_goal_1 value_pre frontier value result NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15)
    | trivial

theorem proof_of_euler_phi_return_wit_2_split_goal_1 : euler_phi_return_wit_2_split_goal_1 := by
  unfold euler_phi_return_wit_2_split_goal_1
  intro value_pre frontier value result NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH1 : (value = 1) := NewPreH1
    have PreH18 : (EulerPhiProgress value_pre frontier value result) := NewPreH15
    exact euler_progress_terminal_one__euler_phi_final_results value_pre frontier value result PreH1 PreH18

theorem proof_of_euler_phi_return_wit_2 : euler_phi_return_wit_2 := by
  unfold euler_phi_return_wit_2
  right
  intro value_pre frontier value result NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15
  have PreH1 : (value = 1) := NewPreH1
  have PreH2 : (2 <= value_pre) := NewPreH2
  have PreH3 : (value_pre <= 46341) := NewPreH3
  have PreH4 : (1 <= value) := NewPreH4
  have PreH5 : (value <= value_pre) := NewPreH5
  have PreH6 : (1 <= result) := NewPreH6
  have PreH7 : (result <= value_pre) := NewPreH7
  have PreH8 : (2 <= frontier) := NewPreH8
  have PreH9 : (frontier <= 216) := NewPreH9
  have PreH10 : ((0 : Int) <= (frontier * frontier)) := by first | assumption | (simp only [INT_MAX, INT_MIN] <;> omega) | positivity | nlinarith
  have PreH11 : ((frontier * frontier) <= INT_MAX) := by simp only [INT_MAX, INT_MIN]; nlinarith
  have PreH12 : ((frontier * frontier) > value) := NewPreH10
  have PreH13 : ((Z.rem result value) = (0 : Int)) := NewPreH11
  have PreH14 : (1 <= (Z.quot result value)) := NewPreH12
  have PreH15 : ((0 : Int) <= ((Z.quot result value) * (value - 1))) := NewPreH13
  have PreH16 : (((Z.quot result value) * (value - 1)) <= value_pre) := NewPreH14
  have PreH17 : (((Z.quot result value) * (value - 1)) <= INT_MAX) := by simp only [INT_MAX, INT_MIN]; omega
  have PreH18 : (EulerPhiProgress value_pre frontier value result) := NewPreH15
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | assumption
    | omega
    | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
    | (solve | Goal_apply (proof_of_euler_phi_return_wit_2_split_goal_1 value_pre frontier value result NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15))
    | exact (proof_of_euler_phi_return_wit_2_split_goal_1 value_pre frontier value result NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13 NewPreH14 NewPreH15)
    | trivial

theorem proof_of_euler_phi_return_wit_3_split_goal_1 : euler_phi_return_wit_3_split_goal_1 := by
  unfold euler_phi_return_wit_3_split_goal_1
  intro value_pre frontier value result NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH1 : (value = 1) := NewPreH1
    have PreH14 : (EulerPhiProgress value_pre frontier value result) := NewPreH12
    exact euler_progress_terminal_one__euler_phi_final_results value_pre frontier value result PreH1 PreH14

theorem proof_of_euler_phi_return_wit_3 : euler_phi_return_wit_3 := by
  unfold euler_phi_return_wit_3
  right
  intro value_pre frontier value result NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12
  have PreH1 : (value = 1) := NewPreH1
  have PreH2 : (2 <= value_pre) := NewPreH2
  have PreH3 : (value_pre <= 46341) := NewPreH3
  have PreH4 : (1 <= value) := NewPreH4
  have PreH5 : (value <= value_pre) := NewPreH5
  have PreH6 : (1 <= result) := NewPreH6
  have PreH7 : (result <= value_pre) := NewPreH7
  have PreH8 : (2 <= frontier) := NewPreH8
  have PreH9 : (frontier <= 216) := NewPreH9
  have PreH10 : ((0 : Int) <= (frontier * frontier)) := by first | assumption | (simp only [INT_MAX, INT_MIN] <;> omega) | positivity | nlinarith
  have PreH11 : ((frontier * frontier) <= INT_MAX) := by simp only [INT_MAX, INT_MIN]; nlinarith
  have PreH12 : ((frontier * frontier) > value) := NewPreH10
  have PreH13 : (value = 1) := NewPreH1
  have PreH14 : (EulerPhiProgress value_pre frontier value result) := NewPreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | assumption
    | omega
    | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
    | (solve | Goal_apply (proof_of_euler_phi_return_wit_3_split_goal_1 value_pre frontier value result NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12))
    | exact (proof_of_euler_phi_return_wit_3_split_goal_1 value_pre frontier value result NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12)
    | trivial

theorem proof_of_modular_power_entail_wit_1_split_goal_1 : modular_power_entail_wit_1_split_goal_1 := by
  unfold modular_power_entail_wit_1_split_goal_1
  intro modulus_pre exponent_pre base_pre NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    unfold EulerModularPowerProgress
    simp

theorem proof_of_modular_power_entail_wit_1 : modular_power_entail_wit_1 := by
  unfold modular_power_entail_wit_1
  right
  intro modulus_pre exponent_pre base_pre NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5
  have PreH1 : ((0 : Int) <= base_pre) := NewPreH1
  have PreH2 : (base_pre < modulus_pre) := NewPreH2
  have PreH3 : ((0 : Int) <= exponent_pre) := NewPreH3
  have PreH4 : (2 <= modulus_pre) := NewPreH4
  have PreH5 : (modulus_pre <= 46341) := NewPreH5
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | assumption
    | omega
    | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
    | (solve | Goal_apply (proof_of_modular_power_entail_wit_1_split_goal_1 modulus_pre exponent_pre base_pre NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5))
    | exact (proof_of_modular_power_entail_wit_1_split_goal_1 modulus_pre exponent_pre base_pre NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5)
    | trivial

theorem proof_of_modular_power_entail_wit_2_1_split_goal_1 : modular_power_entail_wit_2_1_split_goal_1 := by
  unfold modular_power_entail_wit_2_1_split_goal_1
  intro modulus_pre exponent_pre base_pre result exponent base NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH1 : ((Z.rem exponent 2) = 1) := NewPreH1
    have PreH2 : (exponent > (0 : Int)) := NewPreH2
    have PreH10 : ((0 : Int) <= exponent) := NewPreH7
    have PreH14 : ((0 : Int) <= (base * base)) := by first | assumption | (simp only [INT_MAX, INT_MIN] <;> omega) | positivity | nlinarith
    have PreH16 : ((0 : Int) <= (result * base)) := by first | assumption | (simp only [INT_MAX, INT_MIN] <;> omega) | positivity | nlinarith
    have PreH18 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result) := NewPreH10
    rw [AUXLib.rem_eq_mod exponent 2 PreH10 (by omega)] at PreH1
    rw [AUXLib.rem_eq_mod (base*base) modulus_pre PreH14 (by omega)]
    rw [show Z.quot exponent 2=Z.div exponent 2 from (Int.fdiv_eq_tdiv_of_nonneg PreH10 (by omega)).symm]
    rw [AUXLib.rem_eq_mod (result*base) modulus_pre PreH16 (by omega)]
    exact euler_modular_progress_odd_step__modular_power_loop base_pre exponent_pre modulus_pre base exponent result (by omega) PreH2 PreH1 PreH18

theorem proof_of_modular_power_entail_wit_2_1_split_goal_2 : modular_power_entail_wit_2_1_split_goal_2 := by
  unfold modular_power_entail_wit_2_1_split_goal_2
  intro modulus_pre exponent_pre base_pre result exponent base NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH7 : (modulus_pre <= 46341) := NewPreH4
    have PreH10 : ((0 : Int) <= exponent) := NewPreH7
    have PreH14 : ((0 : Int) <= (base * base)) := by first | assumption | (simp only [INT_MAX, INT_MIN] <;> omega) | positivity | nlinarith
    have PreH16 : ((0 : Int) <= (result * base)) := by first | assumption | (simp only [INT_MAX, INT_MIN] <;> omega) | positivity | nlinarith
    have hs := AUXLib.rem_nonneg_bounds (base*base) modulus_pre PreH14 (by omega)
    have hr := AUXLib.rem_nonneg_bounds (result*base) modulus_pre PreH16 (by omega)
    have hp := AUXLib.bounded_product (Z.rem (result*base) modulus_pre) (Z.rem (base*base) modulus_pre) modulus_pre PreH7 hr hs
    have hsq := AUXLib.bounded_product (Z.rem (base*base) modulus_pre) (Z.rem (base*base) modulus_pre) modulus_pre PreH7 hs hs
    have hql := Z.quot_pos exponent 2 PreH10 (by omega)
    omega

theorem proof_of_modular_power_entail_wit_2_1_split_goal_3 : modular_power_entail_wit_2_1_split_goal_3 := by
  unfold modular_power_entail_wit_2_1_split_goal_3
  intro modulus_pre exponent_pre base_pre result exponent base NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH7 : (modulus_pre <= 46341) := NewPreH4
    have PreH10 : ((0 : Int) <= exponent) := NewPreH7
    have PreH14 : ((0 : Int) <= (base * base)) := by first | assumption | (simp only [INT_MAX, INT_MIN] <;> omega) | positivity | nlinarith
    have PreH16 : ((0 : Int) <= (result * base)) := by first | assumption | (simp only [INT_MAX, INT_MIN] <;> omega) | positivity | nlinarith
    have hs := AUXLib.rem_nonneg_bounds (base*base) modulus_pre PreH14 (by omega)
    have hr := AUXLib.rem_nonneg_bounds (result*base) modulus_pre PreH16 (by omega)
    have hp := AUXLib.bounded_product (Z.rem (result*base) modulus_pre) (Z.rem (base*base) modulus_pre) modulus_pre PreH7 hr hs
    have hsq := AUXLib.bounded_product (Z.rem (base*base) modulus_pre) (Z.rem (base*base) modulus_pre) modulus_pre PreH7 hs hs
    have hql := Z.quot_pos exponent 2 PreH10 (by omega)
    omega

theorem proof_of_modular_power_entail_wit_2_1_split_goal_4 : modular_power_entail_wit_2_1_split_goal_4 := by
  unfold modular_power_entail_wit_2_1_split_goal_4
  intro modulus_pre exponent_pre base_pre result exponent base NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH7 : (modulus_pre <= 46341) := NewPreH4
    have PreH10 : ((0 : Int) <= exponent) := NewPreH7
    have PreH14 : ((0 : Int) <= (base * base)) := by first | assumption | (simp only [INT_MAX, INT_MIN] <;> omega) | positivity | nlinarith
    have PreH16 : ((0 : Int) <= (result * base)) := by first | assumption | (simp only [INT_MAX, INT_MIN] <;> omega) | positivity | nlinarith
    have hs := AUXLib.rem_nonneg_bounds (base*base) modulus_pre PreH14 (by omega)
    have hr := AUXLib.rem_nonneg_bounds (result*base) modulus_pre PreH16 (by omega)
    have hp := AUXLib.bounded_product (Z.rem (result*base) modulus_pre) (Z.rem (base*base) modulus_pre) modulus_pre PreH7 hr hs
    have hsq := AUXLib.bounded_product (Z.rem (base*base) modulus_pre) (Z.rem (base*base) modulus_pre) modulus_pre PreH7 hs hs
    have hql := Z.quot_pos exponent 2 PreH10 (by omega)
    omega

theorem proof_of_modular_power_entail_wit_2_1_split_goal_5 : modular_power_entail_wit_2_1_split_goal_5 := by
  unfold modular_power_entail_wit_2_1_split_goal_5
  intro modulus_pre exponent_pre base_pre result exponent base NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH7 : (modulus_pre <= 46341) := NewPreH4
    have PreH10 : ((0 : Int) <= exponent) := NewPreH7
    have PreH14 : ((0 : Int) <= (base * base)) := by first | assumption | (simp only [INT_MAX, INT_MIN] <;> omega) | positivity | nlinarith
    have PreH16 : ((0 : Int) <= (result * base)) := by first | assumption | (simp only [INT_MAX, INT_MIN] <;> omega) | positivity | nlinarith
    have hs := AUXLib.rem_nonneg_bounds (base*base) modulus_pre PreH14 (by omega)
    have hr := AUXLib.rem_nonneg_bounds (result*base) modulus_pre PreH16 (by omega)
    have hp := AUXLib.bounded_product (Z.rem (result*base) modulus_pre) (Z.rem (base*base) modulus_pre) modulus_pre PreH7 hr hs
    have hsq := AUXLib.bounded_product (Z.rem (base*base) modulus_pre) (Z.rem (base*base) modulus_pre) modulus_pre PreH7 hs hs
    have hql := Z.quot_pos exponent 2 PreH10 (by omega)
    omega

theorem proof_of_modular_power_entail_wit_2_1_split_goal_6 : modular_power_entail_wit_2_1_split_goal_6 := by
  unfold modular_power_entail_wit_2_1_split_goal_6
  intro modulus_pre exponent_pre base_pre result exponent base NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH7 : (modulus_pre <= 46341) := NewPreH4
    have PreH10 : ((0 : Int) <= exponent) := NewPreH7
    have PreH14 : ((0 : Int) <= (base * base)) := by first | assumption | (simp only [INT_MAX, INT_MIN] <;> omega) | positivity | nlinarith
    have PreH16 : ((0 : Int) <= (result * base)) := by first | assumption | (simp only [INT_MAX, INT_MIN] <;> omega) | positivity | nlinarith
    have hs := AUXLib.rem_nonneg_bounds (base*base) modulus_pre PreH14 (by omega)
    have hr := AUXLib.rem_nonneg_bounds (result*base) modulus_pre PreH16 (by omega)
    have hp := AUXLib.bounded_product (Z.rem (result*base) modulus_pre) (Z.rem (base*base) modulus_pre) modulus_pre PreH7 hr hs
    have hsq := AUXLib.bounded_product (Z.rem (base*base) modulus_pre) (Z.rem (base*base) modulus_pre) modulus_pre PreH7 hs hs
    have hql := Z.quot_pos exponent 2 PreH10 (by omega)
    omega

theorem proof_of_modular_power_entail_wit_2_1 : modular_power_entail_wit_2_1 := by
  unfold modular_power_entail_wit_2_1
  right
  intro modulus_pre exponent_pre base_pre result exponent base NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | assumption
    | omega
    | exact (proof_of_modular_power_entail_wit_2_1_split_goal_1 modulus_pre exponent_pre base_pre result exponent base NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10)
    | exact (proof_of_modular_power_entail_wit_2_1_split_goal_2 modulus_pre exponent_pre base_pre result exponent base NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10)
    | exact (proof_of_modular_power_entail_wit_2_1_split_goal_3 modulus_pre exponent_pre base_pre result exponent base NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10)
    | exact (proof_of_modular_power_entail_wit_2_1_split_goal_4 modulus_pre exponent_pre base_pre result exponent base NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10)
    | exact (proof_of_modular_power_entail_wit_2_1_split_goal_5 modulus_pre exponent_pre base_pre result exponent base NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10)
    | exact (proof_of_modular_power_entail_wit_2_1_split_goal_6 modulus_pre exponent_pre base_pre result exponent base NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10)
    | trivial

theorem proof_of_modular_power_entail_wit_2_2_split_goal_1 : modular_power_entail_wit_2_2_split_goal_1 := by
  unfold modular_power_entail_wit_2_2_split_goal_1
  intro modulus_pre exponent_pre base_pre result exponent base NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH1 : ((Z.rem exponent 2) ≠ 1) := NewPreH1
    have PreH2 : (exponent > (0 : Int)) := NewPreH2
    have PreH10 : ((0 : Int) <= exponent) := NewPreH7
    have PreH14 : ((0 : Int) <= (base * base)) := by first | assumption | (simp only [INT_MAX, INT_MIN] <;> omega) | positivity | nlinarith
    have PreH18 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result) := NewPreH10
    rw [AUXLib.rem_eq_mod exponent 2 PreH10 (by omega)] at PreH1
    rw [AUXLib.rem_eq_mod (base*base) modulus_pre PreH14 (by omega)]
    rw [show Z.quot exponent 2=Z.div exponent 2 from (Int.fdiv_eq_tdiv_of_nonneg PreH10 (by omega)).symm]
    exact euler_modular_progress_even_step__modular_power_loop base_pre exponent_pre modulus_pre base exponent result (by omega) PreH2 PreH1 PreH18

theorem proof_of_modular_power_entail_wit_2_2_split_goal_2 : modular_power_entail_wit_2_2_split_goal_2 := by
  unfold modular_power_entail_wit_2_2_split_goal_2
  intro modulus_pre exponent_pre base_pre result exponent base NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH7 : (modulus_pre <= 46341) := NewPreH4
    have PreH10 : ((0 : Int) <= exponent) := NewPreH7
    have PreH12 : ((0 : Int) <= result) := NewPreH8
    have PreH13 : (result < modulus_pre) := NewPreH9
    have PreH14 : ((0 : Int) <= (base * base)) := by first | assumption | (simp only [INT_MAX, INT_MIN] <;> omega) | positivity | nlinarith
    have PreH16 : ((0 : Int) <= (result * base)) := by first | assumption | (simp only [INT_MAX, INT_MIN] <;> omega) | positivity | nlinarith
    have hs := AUXLib.rem_nonneg_bounds (base*base) modulus_pre PreH14 (by omega)
    have hr := AUXLib.rem_nonneg_bounds (result*base) modulus_pre PreH16 (by omega)
    have hp := AUXLib.bounded_product result (Z.rem (base*base) modulus_pre) modulus_pre PreH7 ⟨PreH12,PreH13⟩ hs
    have hsq := AUXLib.bounded_product (Z.rem (base*base) modulus_pre) (Z.rem (base*base) modulus_pre) modulus_pre PreH7 hs hs
    have hql := Z.quot_pos exponent 2 PreH10 (by omega)
    omega

theorem proof_of_modular_power_entail_wit_2_2_split_goal_3 : modular_power_entail_wit_2_2_split_goal_3 := by
  unfold modular_power_entail_wit_2_2_split_goal_3
  intro modulus_pre exponent_pre base_pre result exponent base NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH7 : (modulus_pre <= 46341) := NewPreH4
    have PreH10 : ((0 : Int) <= exponent) := NewPreH7
    have PreH12 : ((0 : Int) <= result) := NewPreH8
    have PreH13 : (result < modulus_pre) := NewPreH9
    have PreH14 : ((0 : Int) <= (base * base)) := by first | assumption | (simp only [INT_MAX, INT_MIN] <;> omega) | positivity | nlinarith
    have PreH16 : ((0 : Int) <= (result * base)) := by first | assumption | (simp only [INT_MAX, INT_MIN] <;> omega) | positivity | nlinarith
    have hs := AUXLib.rem_nonneg_bounds (base*base) modulus_pre PreH14 (by omega)
    have hr := AUXLib.rem_nonneg_bounds (result*base) modulus_pre PreH16 (by omega)
    have hp := AUXLib.bounded_product result (Z.rem (base*base) modulus_pre) modulus_pre PreH7 ⟨PreH12,PreH13⟩ hs
    have hsq := AUXLib.bounded_product (Z.rem (base*base) modulus_pre) (Z.rem (base*base) modulus_pre) modulus_pre PreH7 hs hs
    have hql := Z.quot_pos exponent 2 PreH10 (by omega)
    omega

theorem proof_of_modular_power_entail_wit_2_2_split_goal_4 : modular_power_entail_wit_2_2_split_goal_4 := by
  unfold modular_power_entail_wit_2_2_split_goal_4
  intro modulus_pre exponent_pre base_pre result exponent base NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH7 : (modulus_pre <= 46341) := NewPreH4
    have PreH10 : ((0 : Int) <= exponent) := NewPreH7
    have PreH12 : ((0 : Int) <= result) := NewPreH8
    have PreH13 : (result < modulus_pre) := NewPreH9
    have PreH14 : ((0 : Int) <= (base * base)) := by first | assumption | (simp only [INT_MAX, INT_MIN] <;> omega) | positivity | nlinarith
    have PreH16 : ((0 : Int) <= (result * base)) := by first | assumption | (simp only [INT_MAX, INT_MIN] <;> omega) | positivity | nlinarith
    have hs := AUXLib.rem_nonneg_bounds (base*base) modulus_pre PreH14 (by omega)
    have hr := AUXLib.rem_nonneg_bounds (result*base) modulus_pre PreH16 (by omega)
    have hp := AUXLib.bounded_product result (Z.rem (base*base) modulus_pre) modulus_pre PreH7 ⟨PreH12,PreH13⟩ hs
    have hsq := AUXLib.bounded_product (Z.rem (base*base) modulus_pre) (Z.rem (base*base) modulus_pre) modulus_pre PreH7 hs hs
    have hql := Z.quot_pos exponent 2 PreH10 (by omega)
    omega

theorem proof_of_modular_power_entail_wit_2_2 : modular_power_entail_wit_2_2 := by
  unfold modular_power_entail_wit_2_2
  right
  intro modulus_pre exponent_pre base_pre result exponent base NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | assumption
    | omega
    | exact (proof_of_modular_power_entail_wit_2_2_split_goal_1 modulus_pre exponent_pre base_pre result exponent base NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10)
    | exact (proof_of_modular_power_entail_wit_2_2_split_goal_2 modulus_pre exponent_pre base_pre result exponent base NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10)
    | exact (proof_of_modular_power_entail_wit_2_2_split_goal_3 modulus_pre exponent_pre base_pre result exponent base NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10)
    | exact (proof_of_modular_power_entail_wit_2_2_split_goal_4 modulus_pre exponent_pre base_pre result exponent base NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10)
    | trivial

theorem proof_of_modular_power_return_wit_1_split_goal_1 : modular_power_return_wit_1_split_goal_1 := by
  unfold modular_power_return_wit_1_split_goal_1
  intro modulus_pre exponent_pre base_pre result exponent base NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9
  first
  | assumption
  | omega
  | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega))
  |
    have PreH11 : ((0 : Int) <= result) := NewPreH7
    have PreH12 : (result < modulus_pre) := NewPreH8
    have PreH17 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result) := NewPreH9
    have he : exponent=0 := by omega
    subst exponent
    exact euler_modular_progress_zero_finish__modular_power_final base_pre exponent_pre modulus_pre base result PreH11 PreH12 PreH17

theorem proof_of_modular_power_return_wit_1 : modular_power_return_wit_1 := by
  unfold modular_power_return_wit_1
  right
  intro modulus_pre exponent_pre base_pre result exponent base NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | assumption
    | omega
    | exact (proof_of_modular_power_return_wit_1_split_goal_1 modulus_pre exponent_pre base_pre result exponent base NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9)
    | trivial

theorem proof_of_euler_theorem_inverse_return_wit_1_split_goal_1 : euler_theorem_inverse_return_wit_1_split_goal_1 := by
  unfold euler_theorem_inverse_return_wit_1_split_goal_1
  intro modulus_pre value_pre retval_2 retval NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11
  exact (euler_totient_inverse_theorem__inverse_final_result value_pre modulus_pre retval_2 retval
    NewPreH7 NewPreH8 NewPreH9 NewPreH11 NewPreH6 NewPreH3).2

theorem proof_of_euler_theorem_inverse_return_wit_1 : euler_theorem_inverse_return_wit_1 := by
  unfold euler_theorem_inverse_return_wit_1
  right
  intro modulus_pre value_pre retval_2 retval NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
    | assumption
    | omega
    | exact (proof_of_euler_theorem_inverse_return_wit_1_split_goal_1 modulus_pre value_pre retval_2 retval NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11)
    | trivial

theorem proof_of_euler_phi_entail_wit_5 : euler_phi_entail_wit_5 := by
  unfold euler_phi_entail_wit_5
  intro value_pre factor result value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hd := PreH10.1.1
  have hr := (Z.rem_divide result value (by omega)).2 hd
  by_cases he : value=1
  · Right
    Exists factor
    split_pure_spatial
    · cancel
    · split_pures <;> dump_pre_spatial
      all_goals first | assumption | omega | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega)) | exact PreH10 | (change _≤2147483647; omega) | omega | trivial
  · have hb := euler_exact_positive_quotient_bounds__euler_phi_factor_completion result value PreH6 (by omega) hd
    Left
    Exists factor
    split_pure_spatial
    · cancel
    · split_pures <;> dump_pre_spatial
      all_goals first | assumption | omega | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega)) | exact PreH10 | (change _≤2147483647; omega) | omega | trivial

theorem proof_of_euler_phi_safety_wit_8 : euler_phi_safety_wit_8 := by
  unfold euler_phi_safety_wit_8
  right
  intro value_pre factor result value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hi := aux_euler_phi_entail_wit_4_split_goal_1 value_pre factor result value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hlo := aux_euler_phi_entail_wit_4_split_goal_3 value_pre factor result value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pures <;> dump_pre_spatial
  all_goals simp only [INT_MAX, INT_MIN] at * <;> omega

end SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_proof_manual
