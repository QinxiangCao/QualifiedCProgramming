import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
namespace SimpleC.EE.LLM_bench.Algorithms.modular_mul.modular_mul_lib

def ModularMul (multiplicand multiplier modulus result : Int) : Prop :=
  (-modulus < result ∧ result < modulus) ∧
  ∃ quotient, multiplicand * multiplier = result + modulus * quotient

def ModularMulProgress (original_multiplicand original_multiplier modulus
    current_multiplicand remaining_multiplier accumulator sign : Int) : Prop :=
  ∃ quotient, original_multiplicand * original_multiplier =
    sign * (accumulator + current_multiplicand * remaining_multiplier) + modulus * quotient

theorem modular_mul_progress_odd_step__odd_transition (oa ob m a b r s : Int)
    (hodd : Z.modulo b 2 = 1) (hm : m ≠ 0)
    (hp : ModularMulProgress oa ob m a b r s) :
    ModularMulProgress oa ob m (Z.rem (a + a) m) (Z.div b 2)
      (Z.rem (r + a) m) s := by
  obtain ⟨q, hq⟩ := hp
  refine ⟨q + s * (Z.quot (r + a) m + Z.quot (a + a) m * Z.div b 2), ?_⟩
  have hr := Z.quot_rem (r + a) m hm
  have ha := Z.quot_rem (a + a) m hm
  have hb : b = 2 * Z.div b 2 + 1 := by
    have := Int.fmod_add_mul_fdiv b 2
    change b.fmod 2 = 1 at hodd
    change b = 2 * b.fdiv 2 + 1
    omega
  grind

theorem modular_mul_progress_even_step__even_transition (oa ob m a b r s : Int)
    (heven : Z.rem b 2 = 0) (hm : m ≠ 0)
    (hp : ModularMulProgress oa ob m a b r s) :
    ModularMulProgress oa ob m (Z.rem (a + a) m) (Z.quot b 2) r s := by
  obtain ⟨q, hq⟩ := hp
  refine ⟨q + s * (Z.quot (a + a) m * Z.quot b 2), ?_⟩
  have hb := Z.quot_rem b 2 (by decide)
  have ha := Z.quot_rem (a + a) m hm
  grind

theorem z_rem_strict_bounds__even_transition (value modulus : Int)
    (hm : 0 < modulus) : -modulus < Z.rem value modulus ∧ Z.rem value modulus < modulus :=
  AUXLib.rem_bounds value modulus hm

theorem modular_mul_progress_finish__final_result (oa ob m a b r s : Int)
    (hb : b = 0) (hs : s = 1 ∨ s = -1) (hr : -m < r ∧ r < m)
    (hp : ModularMulProgress oa ob m a b r s) : ModularMul oa ob m (r * s) := by
  obtain ⟨q, hq⟩ := hp
  constructor
  · rcases hs with hs | hs <;> subst s <;> omega
  · exact ⟨q, by subst b; grind⟩

end SimpleC.EE.LLM_bench.Algorithms.modular_mul.modular_mul_lib

namespace SimpleC.EE.LLM_bench.Algorithms.modular_mul
export modular_mul_lib (ModularMul ModularMulProgress)
end SimpleC.EE.LLM_bench.Algorithms.modular_mul
