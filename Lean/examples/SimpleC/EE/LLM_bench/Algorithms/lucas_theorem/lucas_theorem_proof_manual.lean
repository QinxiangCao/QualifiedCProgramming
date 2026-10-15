import SimpleC.EE.LLM_bench.Algorithms.lucas_theorem.lucas_theorem_goal
import SimpleC.EE.LLM_bench.Algorithms.lucas_theorem.lucas_theorem_proof_auto

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.lucas_theorem.lucas_theorem_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open lucas_theorem_goal lucas_theorem_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

private theorem cast_rem (x p : Int) (hx : 0 ≤ x) (hp : 0 < p) (hb : p ≤ 100000) :
    signed_last_nbits (Z.rem x p) 32 = Z.rem x p := by
  have h := AUXLib.rem_nonneg_bounds x p hx hp
  apply signed_last_nbits_eq _ 32 (by decide)
  change -2147483648 ≤ _ ∧ _ < 2147483648
  omega

private theorem initial_product (upper lower p : Int) (hp : 2 ≤ p) :
    DigitProductProgress upper lower p 1 1 1 := by
  simp only [DigitProductProgress, DigitNumeratorPrefix, DigitDenominatorPrefix,
    LucasRangeProduct, Int.sub_self, Int.toNat_zero, List.range'_zero,
    List.map_nil, List.foldr_nil, Z.modulo, Int.fmod_eq_of_lt (show 0 ≤ (1:Int) by decide) (show 1 < p by omega)]
  trivial

theorem proof_of_binomial_digit_mod_prime_entail_wit_1_1 : binomial_digit_mod_prime_entail_wit_1_1 := by
  pre_process
  have hp := initial_product upper_pre (upper_pre-lower_pre) prime_pre PreH7
  have hm : upper_pre-lower_pre = min lower_pre (upper_pre-lower_pre) := (min_eq_right (by omega)).symm
  entailer!

theorem proof_of_binomial_digit_mod_prime_entail_wit_1_2 : binomial_digit_mod_prime_entail_wit_1_2 := by
  pre_process
  have hp := initial_product upper_pre lower_pre prime_pre PreH7
  have hm : lower_pre = min lower_pre (upper_pre-lower_pre) := (min_eq_left PreH1).symm
  entailer!

theorem proof_of_binomial_digit_mod_prime_entail_wit_2 : binomial_digit_mod_prime_entail_wit_2 := by
  pre_process
  have hn := Int.mul_nonneg PreH13 (show 0 ≤ upper_pre-lower+i by omega)
  have hd := Int.mul_nonneg PreH15 (show 0 ≤ i by omega)
  have cn := cast_rem (numerator*(upper_pre-lower+i)) prime_pre hn (by omega) PreH7
  have cd := cast_rem (denominator*i) prime_pre hd (by omega) PreH7
  have bn := AUXLib.rem_nonneg_bounds (numerator*(upper_pre-lower+i)) prime_pre hn (by omega)
  have bd := AUXLib.rem_nonneg_bounds (denominator*i) prime_pre hd (by omega)
  have hp := digit_product_progress_step__digit_product_progress upper_pre lower prime_pre i numerator denominator (by omega) PreH11 PreH17
  have hnrem := AUXLib.rem_eq_mod (numerator*(upper_pre-lower+i)) prime_pre hn (by omega)
  have hdrem := AUXLib.rem_eq_mod (denominator*i) prime_pre hd (by omega)
  rw [← hnrem, ← hdrem] at hp
  entailer!
  all_goals first | (simpa only [cn,cd] using hp) | (simp only [cn,cd]; omega)

theorem proof_of_binomial_digit_mod_prime_return_wit_1 : binomial_digit_mod_prime_return_wit_1 := by
  pre_process
  have hi : i = lower+1 := by omega
  subst i
  have hb : 0 ≤ lower ∧ lower ≤ upper_pre := by omega
  have hm := digit_multiplicative_residue__digit_final_residue upper_pre lower prime_pre numerator denominator retval hb PreH6 PreH3 PreH18 PreH1
  have hsym : LucasBinomialCoefficient upper_pre lower = LucasBinomialCoefficient upper_pre lower_pre := by
    rw [PreH9]
    by_cases he : lower_pre ≤ upper_pre-lower_pre
    · rw [min_eq_left he]
    · rw [min_eq_right (by omega)]
      exact (lucas_binomial_symmetry_z__digit_final_residue upper_pre lower_pre (by omega)).symm
  rw [hsym] at hm
  have hv : 0 ≤ retval := by
    rw [PreH1]
    exact Int.fmod_nonneg_of_pos _ (by omega)
  have hn := Int.mul_nonneg PreH14 hv
  have hc := cast_rem (numerator*retval) prime_pre hn (by omega) PreH8
  have hr := AUXLib.rem_eq_mod (numerator*retval) prime_pre hn (by omega)
  have hp : BinomialDigitResidue upper_pre lower_pre prime_pre (signed_last_nbits (Z.rem (numerator*retval) prime_pre) 32) := by
    unfold BinomialDigitResidue
    rw [hc,hr,hm]
  entailer!

theorem proof_of_lucas_theorem_entail_wit_1 : lucas_theorem_entail_wit_1 := by
  pre_process
  have hp : LucasProgress (n_pre+m_pre) n_pre prime_pre (n_pre+m_pre) n_pre 1 := by
    refine ⟨0,?_,?_,?_,?_⟩
    · simp [Z.div,Z.pow]
    · simp [Z.div,Z.pow]
    · change 1=Z.modulo 1 prime_pre
      symm
      exact Int.fmod_eq_of_lt (by omega) (by omega)
    · simp
  entailer!

theorem proof_of_lucas_theorem_entail_wit_2 : lucas_theorem_entail_wit_2 := by
  pre_process
  have hv : 0 ≤ retval := by
    rw [PreH1]
    exact Int.fmod_nonneg_of_pos _ (by omega)
  have hn := Int.mul_nonneg PreH11 hv
  have hc := cast_rem (result*retval) prime_pre hn (by omega) PreH7
  have hr := AUXLib.rem_nonneg_bounds (result*retval) prime_pre hn (by omega)
  have hp := lucas_progress_advance__lucas_digit_transition (n_pre+m_pre) n_pre prime_pre upper lower result retval
    (by omega) PreH4 (by omega) PreH9 PreH11 hv PreH8 PreH1 PreH13
  have hlq := Z.quot_pos lower prime_pre PreH9 (by omega)
  have hlu : Z.quot lower prime_pre ≤ Z.quot upper prime_pre := by
    exact Int.tdiv_le_tdiv (by omega) PreH10
  entailer!
  all_goals first | (simpa only [hc] using hp) | (simp only [hc]; omega)

theorem proof_of_lucas_theorem_return_wit_1 : lucas_theorem_return_wit_1 := by
  pre_process
  have hu : upper=0 := by omega
  have hl : lower=0 := by omega
  subst upper lower
  have hp := lucas_progress_terminal_residue__lucas_terminal_return (n_pre+m_pre) n_pre prime_pre result (by omega) ⟨PreH10,PreH11⟩ PreH12
  entailer!

theorem proof_of_lucas_theorem_return_wit_2 : lucas_theorem_return_wit_2 := by
  pre_process
  have hp : LucasBinomialResidue n_pre m_pre prime_pre 0 := by
    unfold LucasBinomialResidue
    obtain ⟨processed,hu,hl,hr,hres⟩ := PreH12
    rw [hres]
    have hz := lucas_binomial_zero_from_low_digit__lucas_digit_transition upper lower prime_pre (by omega) PreH8 PreH7 PreH1
    unfold Z.modulo at hz ⊢
    rw [Int.mul_fmod,hz,Int.mul_zero,Int.zero_fmod]
  entailer!

theorem proof_of_lucas_theorem_partial_solve_wit_1_pure : lucas_theorem_partial_solve_wit_1_pure := by
  pre_process
  have hl := AUXLib.rem_nonneg_bounds lower prime_pre (by omega) (by omega)
  have hu := AUXLib.rem_nonneg_bounds upper prime_pre (by omega) (by omega)
  entailer!

end SimpleC.EE.LLM_bench.Algorithms.lucas_theorem.lucas_theorem_proof_manual
