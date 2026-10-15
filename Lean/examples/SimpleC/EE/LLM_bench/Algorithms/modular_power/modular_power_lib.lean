import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic

namespace SimpleC.EE.LLM_bench.Algorithms.modular_power.modular_power_lib

def ModularPower (base exponent modulus result : Int) : Prop :=
  result = Z.modulo (Z.pow base exponent) modulus

def ModularPowerProgress (original_base original_exponent modulus
    current_base remaining_exponent accumulator : Int) : Prop :=
  Z.modulo (accumulator * Z.pow current_base remaining_exponent) modulus =
    Z.modulo (Z.pow original_base original_exponent) modulus

private theorem pow_fmod (x m : Int) (n : Nat) :
    ((x.fmod m)^n).fmod m = (x^n).fmod m := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Int.pow_succ]
    rw [Int.mul_fmod, ih, Int.fmod_fmod, ← Int.mul_fmod]

theorem pow_mod_base__loop_transitions (x m n : Int) (_hm : m ≠ 0) (hn : 0 ≤ n) :
    Z.modulo (Z.pow (Z.modulo x m) n) m = Z.modulo (Z.pow x n) m := by
  cases n with
  | ofNat n => exact pow_fmod x m n
  | negSucc n => omega

private theorem pow_twice (a n : Int) (hn : 0 ≤ n) :
    Z.pow (a * a) n = Z.pow a (2 * n) := by
  cases n with
  | ofNat n =>
    change (a * a) ^ n = a ^ (2 * n)
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Nat.mul_succ, Int.pow_add, Int.pow_succ, ih (Int.ofNat_zero_le n)]
      simp [Int.pow_succ, Int.mul_assoc]
  | negSucc n => omega

private theorem pow_succ (a n : Int) (hn : 0 ≤ n) :
    Z.pow a (n + 1) = Z.pow a n * a := by
  cases n with
  | ofNat n => exact Int.pow_succ a n
  | negSucc n => omega

theorem modular_power_progress_odd_step__loop_transitions (ob oe m a b r : Int)
    (hm : 0 < m) (hb : 0 ≤ b) (hodd : Z.modulo b 2 = 1)
    (hp : ModularPowerProgress ob oe m a b r) :
    ModularPowerProgress ob oe m (Z.modulo (a*a) m) (Z.div b 2) (Z.modulo (r*a) m) := by
  have hq : 0 ≤ Z.div b 2 := Int.fdiv_nonneg hb (by decide)
  have hdecomp : b = 2 * Z.div b 2 + 1 := by
    have := Int.fmod_add_mul_fdiv b 2
    change b.fmod 2 = 1 at hodd
    change b = 2 * b.fdiv 2 + 1
    omega
  unfold ModularPowerProgress at *
  rw [show Z.modulo (Z.modulo (r*a) m * Z.pow (Z.modulo (a*a) m) (Z.div b 2)) m =
    Z.modulo (r*a * Z.pow (a*a) (Z.div b 2)) m by
      unfold Z.modulo
      rw [Int.mul_fmod, Int.fmod_fmod]
      have hpow := pow_mod_base__loop_transitions (a*a) m (Z.div b 2) (by omega) hq
      simp only [Z.modulo] at hpow
      rw [hpow]
      rw [← Int.mul_fmod]]
  rw [pow_twice a _ hq]
  have heq : r*a * Z.pow a (2 * Z.div b 2) = r * Z.pow a b := by
    conv => rhs; rw [hdecomp, pow_succ a _ (by omega)]
    grind
  rw [heq]
  exact hp

theorem modular_power_progress_even_step__loop_transitions (ob oe m a b r : Int)
    (hm : 0 < m) (hb : 0 ≤ b) (heven : Z.modulo b 2 = 0)
    (hp : ModularPowerProgress ob oe m a b r) :
    ModularPowerProgress ob oe m (Z.modulo (a*a) m) (Z.div b 2) r := by
  have hq : 0 ≤ Z.div b 2 := Int.fdiv_nonneg hb (by decide)
  have hdecomp : b = 2 * Z.div b 2 := by
    have := Int.fmod_add_mul_fdiv b 2
    change b.fmod 2 = 0 at heven
    change b = 2 * b.fdiv 2
    omega
  unfold ModularPowerProgress at *
  calc
    _ = Z.modulo (r * Z.pow (a*a) (Z.div b 2)) m := by
      unfold Z.modulo
      rw [Int.mul_fmod]
      have hpow := pow_mod_base__loop_transitions (a*a) m (Z.div b 2) (by omega) hq
      simp only [Z.modulo] at hpow
      rw [hpow]
      rw [← Int.mul_fmod]
    _ = _ := by rw [pow_twice a _ hq, ← hdecomp]; exact hp

end SimpleC.EE.LLM_bench.Algorithms.modular_power.modular_power_lib
namespace SimpleC.EE.LLM_bench.Algorithms.modular_power
export modular_power_lib (ModularPower ModularPowerProgress)
end SimpleC.EE.LLM_bench.Algorithms.modular_power
