import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic

namespace SimpleC.EE.LLM_bench.Algorithms.linear_modular_inverse.linear_modular_inverse_lib
open AUXLib

def PrimeForLinearInverse (p : Int) : Prop :=
  2 ≤ p ∧ ∀ divisor, (2 ≤ divisor ∧ divisor < p) → Z.modulo p divisor ≠ 0

def CanonicalModularInverse (p index value : Int) : Prop :=
  (1 ≤ index ∧ index < p) ∧ (0 < value ∧ value < p) ∧
    ∃ coefficient, index * value + p * coefficient = 1

def ModularInversePrefix (p next : Int) (values : List Int) : Prop :=
  Zlength values = next - 1 ∧ ∀ index, (1 ≤ index ∧ index < next) →
    CanonicalModularInverse p index (Znth (index - 1) values 0)

theorem linear_inverse_division_facts__recurrence_core (p i : Int)
    (hp : PrimeForLinearInverse p) (hi : 2 ≤ i ∧ i < p) :
    p = Z.div p i * i + Z.modulo p i ∧ 1 ≤ Z.div p i ∧
    (1 ≤ Z.modulo p i ∧ Z.modulo p i < i) ∧ (0 < p - Z.div p i ∧ p - Z.div p i < p) := by
  have hd := Int.fdiv_mul_add_fmod p i
  have hr0 := Int.fmod_nonneg_of_pos p (show 0 < i by omega)
  have hr1 := Int.fmod_lt_of_pos p (show 0 < i by omega)
  have hrn := hp.2 i hi
  have hq0 := Int.fdiv_nonneg (show 0 ≤ p by have := hp.1; omega) (show 0 ≤ i by omega)
  unfold Z.div Z.modulo at *
  have hq1 : 1 ≤ p.fdiv i := by
    by_cases h : 1 ≤ p.fdiv i
    · exact h
    · have hzero : p.fdiv i = 0 := by omega
      simp [hzero] at hd
      omega
  have hqp : p.fdiv i < p := by
    have hmul := Int.mul_le_mul_of_nonneg_left (show 1 ≤ i by omega) hq0
    simp only [Int.mul_one] at hmul
    omega
  exact ⟨hd.symm, hq1, by omega, by omega⟩

theorem linear_inverse_product_bound__recurrence_core (p a b : Int)
    (hp : 2 ≤ p ∧ p ≤ 46340) (ha : 0 < a ∧ a < p) (hb : 0 < b ∧ b < p) :
    a * b ≤ 2147483647 := by
  have h1 := Int.mul_le_mul_of_nonneg_right (show a ≤ 46340 by omega) (show 0 ≤ b by omega)
  have h2 := Int.mul_le_mul_of_nonneg_left (show b ≤ 46340 by omega) (show (0 : Int) ≤ 46340 by decide)
  omega

theorem linear_inverse_prefix_extend__recurrence_core (p i q r : Int) (values : List Int)
    (hp : PrimeForLinearInverse p) (hi : 2 ≤ i ∧ i < p)
    (hq : q = Z.div p i) (hr : r = Z.modulo p i) (hpre : ModularInversePrefix p i values) :
    ModularInversePrefix p (i + 1)
      (values ++ [Z.modulo ((p-q) * Znth (r-1) values 0) p]) := by
  subst q r
  obtain ⟨hd, hq1, hrem, hdiff⟩ := linear_inverse_division_facts__recurrence_core p i hp hi
  obtain ⟨hlen, hpre⟩ := hpre
  obtain ⟨_, hv, c, hc⟩ := hpre (Z.modulo p i) hrem
  constructor
  · rw [Zlength_app, hlen]
    simp [Zlength]
  · intro index hindex
    by_cases hlt : index < i
    · have hi0 : 0 ≤ index - 1 := by omega
      have hin : (index-1).toNat < values.length := by
        have := (Int.toNat_lt_toNat (show 0 < Zlength values by omega)).2 (show index-1 < Zlength values by omega)
        simpa [Zlength] using this
      have heq : Znth (index-1) (values ++ [Z.modulo ((p-Z.div p i) * Znth (Z.modulo p i-1) values 0) p]) 0 =
          Znth (index-1) values 0 := by
        simp only [Znth, List.getD_eq_getElem?_getD, List.getElem?_append_left hin]
      rw [heq]
      exact hpre index ⟨hindex.1, hlt⟩
    · have hieq : index = i := by omega
      subst index
      rw [app_Znth2 0 values _ (i-1) (by omega), hlen]
      simp only [Int.sub_self, Znth0_cons]
      let value := Znth (Z.modulo p i - 1) values 0
      let raw := (p - Z.div p i) * value
      have hp0 : 0 < p := by have := hp.1; omega
      have hraw : raw = p * Z.div raw p + Z.modulo raw p := (Int.mul_fdiv_add_fmod raw p).symm
      have hm0 : 0 ≤ Z.modulo raw p := Int.fmod_nonneg_of_pos raw hp0
      have hm1 : Z.modulo raw p < p := Int.fmod_lt_of_pos raw hp0
      have hinv : i * Z.modulo raw p + p * (c - i*value + value + i*Z.div raw p) = 1 := by
        change Z.modulo p i * value + p*c = 1 at hc
        have hbez : i*raw + p*(c-i*value+value) = 1 := by dsimp [raw]; grind
        grind
      have hnz : Z.modulo raw p ≠ 0 := by
        intro hz
        have hmult : p * (c-i*value+value+i*Z.div raw p) = 1 := by rw [hz, Int.mul_zero, Int.zero_add] at hinv; exact hinv
        have hmod := congrArg (fun x : Int => x.fmod p) hmult
        simp only [Int.mul_fmod_right, Int.fmod_eq_of_lt (show (0 : Int) ≤ 1 by decide) (show 1 < p by have := hp.1; omega)] at hmod
        contradiction
      change CanonicalModularInverse p i (Z.modulo raw p)
      exact ⟨by omega, ⟨by omega, hm1⟩, _, hinv⟩

end SimpleC.EE.LLM_bench.Algorithms.linear_modular_inverse.linear_modular_inverse_lib
namespace SimpleC.EE.LLM_bench.Algorithms.linear_modular_inverse
export linear_modular_inverse_lib (PrimeForLinearInverse CanonicalModularInverse ModularInversePrefix)
end SimpleC.EE.LLM_bench.Algorithms.linear_modular_inverse
