import AUXLib.NiaCompat
import compcert.lib.ZArithCompat

namespace SimpleC.EE.QCP_demos_LLM.simple_arith.test_prime_lib

def HasFactorBetween (x lo hi : Int) : Prop :=
  exists k, lo <= k ∧ k < hi ∧ Z.divide k x

def prime (p : Int) : Prop :=
  1 < p ∧ forall n, 1 < n ∧ n < p -> ¬Z.divide n p

theorem prime_alt (p : Int) :
    (1 < p ∧ forall n, 1 < n ∧ n < p -> ¬Z.divide n p) ↔ prime p :=
  Iff.rfl

theorem prime_ge_2 (p : Int) (hprime : prime p) : 2 <= p := by
  exact hprime.1

theorem no_factor_between_empty (x lo hi : Int) (hle : hi <= lo) :
    ¬HasFactorBetween x lo hi := by
  rintro ⟨k, hklo, hkhi, _⟩
  omega

theorem has_factor_between_hit (x lo hi d : Int) (hd : 2 <= d)
    (hlo : lo <= d) (hlt : d < x) (hmod : Z.rem x d = 0)
    (hhi : hi = d + 1) : HasFactorBetween x lo hi := by
  refine ⟨d, hlo, ?_, ?_⟩
  · omega
  · exact (Z.rem_divide x d (by omega)).1 hmod

theorem no_factor_between_snoc (x lo d : Int) (hd : 2 <= d)
    (hlo : lo <= d) (hmod : Z.rem x d ≠ 0)
    (hnone : ¬HasFactorBetween x lo d) :
    ¬HasFactorBetween x lo (d + 1) := by
  rintro ⟨k, hklo, hkd, hkdiv⟩
  by_cases hkeq : k = d
  · subst k
    apply hmod
    exact (Z.rem_divide x d (by omega)).2 hkdiv
  · apply hnone
    exact ⟨k, hklo, by omega, hkdiv⟩

theorem prime_of_no_factor_from_2 (x : Int) (hx : 2 <= x)
    (hnone : ¬HasFactorBetween x 2 x) : prime x := by
  rw [← prime_alt]
  constructor
  · omega
  · intro n hn hdiv
    apply hnone
    exact ⟨n, by omega, hn.2, hdiv⟩

theorem not_prime_of_factor_between_2 (x : Int)
    (hfactor : HasFactorBetween x 2 x) : ¬prime x := by
  intro hprime
  rw [← prime_alt] at hprime
  rcases hfactor with ⟨k, hlo, hhi, hdiv⟩
  exact hprime.2 k (by omega) hdiv

theorem not_prime_of_mod_factor (x d : Int) (hd : 2 <= d) (hdx : d < x)
    (hmod : Z.rem x d = 0) : ¬prime x := by
  apply not_prime_of_factor_between_2
  exact ⟨d, hd, hdx, (Z.rem_divide x d (by omega)).1 hmod⟩

theorem not_prime_lt_2 (x : Int) (hlt : x < 2) : ¬prime x := by
  intro hprime
  have := prime_ge_2 x hprime
  omega

theorem prime_of_no_factor_before_square (x d : Int) (hx : 2 <= x)
    (hd : 2 <= d) (hsquare : x < d * d)
    (hnone : ¬HasFactorBetween x 2 d) : prime x := by
  rw [← prime_alt]
  constructor
  · omega
  · intro n hn hdiv
    by_cases hnd : n < d
    · apply hnone
      exact ⟨n, by omega, hnd, hdiv⟩
    · rcases hdiv with ⟨q, hq⟩
      have hqpos : 0 < q := by
        by_cases hqle : q <= 0
        · have hmul : q * n <= 0 := by nia
          omega
        · omega
      have hqne : q ≠ 1 := by
        intro hqone
        subst q
        omega
      have hq2 : 2 <= q := by omega
      have hqd : q < d := by
        by_cases hqd : q < d
        · exact hqd
        · have hmul : d * d <= q * n := by nia
          omega
      apply hnone
      refine ⟨q, hq2, hqd, ?_⟩
      exact ⟨n, by simpa [Int.mul_comm] using hq⟩

end SimpleC.EE.QCP_demos_LLM.simple_arith.test_prime_lib

namespace SimpleC.EE.QCP_demos_LLM.simple_arith

export SimpleC.EE.QCP_demos_LLM.simple_arith.test_prime_lib (HasFactorBetween prime)

end SimpleC.EE.QCP_demos_LLM.simple_arith

namespace SimpleC.EE.QCP_demos_LLM

export SimpleC.EE.QCP_demos_LLM.simple_arith.test_prime_lib (HasFactorBetween prime)

end SimpleC.EE.QCP_demos_LLM
