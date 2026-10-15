import ListLib.General.Length
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_order_modules

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
open AUXLib AUXLib.Prime MaxMinLib
local infixl:70 " /ᶻ " => Z.div
local infixl:70 " mod " => Z.modulo
local infix:50 " ∣ᶻ " => Z.divide

namespace P090_FactorTable

private theorem app_Znth1 (d : Int) (pr ps : List Int) (i : Int) (hi : 0 ≤ i ∧ i < Zlength pr) :
    Znth i (pr++ps) d = Znth i pr d := ListLib.app_Znth1 d pr ps i hi

theorem strict_factor_prefix_base (m : Int) : 0 < m → StrictFactorPrefix m 2 m [] [] := by
  intro hm
  refine ⟨⟨rfl, by simp [Zlength], by omega, ⟨hm, le_refl _⟩, by simp [factor_product], ?_, ?_⟩, ?_⟩
  · intro k hk; simp [Zlength] at hk; omega
  · rintro p ⟨hp, _⟩ hl; omega
  · intro j k hk; simp [Zlength] at hk; omega

theorem strict_factor_prefix_forgets_order (m candidate remainder : Int) (pr pe : List Int) :
    StrictFactorPrefix m candidate remainder pr pe → FactorPrefix m candidate remainder pr pe := fun h => h.1

theorem strict_factor_prefix_has_order (m candidate remainder : Int) (pr pe : List Int) :
    StrictFactorPrefix m candidate remainder pr pe → StrictPrimePrefix pr := fun h => h.2

theorem strict_prime_prefix_lt (pr : List Int) (j k : Int) :
    StrictPrimePrefix pr → 0 ≤ j → j < k → k < Zlength pr → Znth j pr 0 < Znth k pr 0 := by
  intro h hj hjk hk
  exact h j k ⟨hj, hjk, hk⟩

theorem strict_prime_prefix_distinct_indices (pr : List Int) (j k : Int) :
    StrictPrimePrefix pr → (0 ≤ j ∧ j < Zlength pr) → (0 ≤ k ∧ k < Zlength pr) → j ≠ k →
    Znth j pr 0 ≠ Znth k pr 0 := by
  intro h hj hk hn he
  by_cases hl : j < k
  · have := h j k ⟨hj.1, hl, hk.2⟩; omega
  · have := h k j ⟨hk.1, by omega, hj.2⟩; omega

theorem strict_prime_prefix_snoc (pr : List Int) (p : Int) :
    StrictPrimePrefix pr → (∀ k, (0 ≤ k ∧ k < Zlength pr) → Znth k pr 0 < p) →
    StrictPrimePrefix (pr ++ [p]) := by
  intro h hb j k hjk
  have hlen : Zlength (pr++[p]) = Zlength pr + 1 := by simp [Zlength]
  by_cases hk : k < Zlength pr
  · rw [app_Znth1 0 pr [p] j (by omega), app_Znth1 0 pr [p] k (by omega)]
    exact h j k ⟨hjk.1, hjk.2.1, hk⟩
  · have he : k = Zlength pr := by omega
    subst k
    rw [app_Znth1 0 pr [p] j (by omega), app_Znth2 0 pr [p] (Zlength pr) (by omega)]
    simpa [Znth] using hb j ⟨hjk.1, by omega⟩

theorem factor_product_snoc (pr pe : List Int) (p e : Int) :
    Zlength pr = Zlength pe → factor_product (pr++[p]) (pe++[e]) = factor_product pr pe * Z.pow p e := by
  induction pr generalizing pe with
  | nil =>
    intro h
    cases pe with
    | nil => simp [factor_product]
    | cons q pe => simp [Zlength] at h <;> omega
  | cons q pr ih =>
    intro h
    cases pe with
    | nil => simp [Zlength] at h <;> omega
    | cons f pe =>
      have hlen : Zlength pr = Zlength pe := by simp only [Zlength_cons] at h; omega
      simp only [List.cons_append, factor_product]
      rw [ih pe hlen]
      ring

theorem strict_factor_prefix_length_bounds (m candidate remainder : Int) (pr pe : List Int) :
    StrictFactorPrefix m candidate remainder pr pe → (0 ≤ Zlength pr ∧ Zlength pr ≤ 64) := fun h => h.1.2.1

theorem strict_factor_prefix_snoc_capacity (m candidate remainder : Int) (pr pe : List Int) (p : Int) :
    StrictFactorPrefix m candidate remainder pr pe → Zlength pr < 64 →
    (0 ≤ Zlength (pr++[p]) ∧ Zlength (pr++[p]) ≤ 64) := by
  intro h hr
  have hb := strict_factor_prefix_length_bounds m candidate remainder pr pe h
  have hl : Zlength (pr++[p]) = Zlength pr+1 := by simp [Zlength]
  omega

theorem factor_prefix_smaller_prime_survives_division (m candidate original remainder : Int)
    (pr pe : List Int) (p exponent : Int) :
    FactorPrefix m candidate original pr pe → original = Z.pow p exponent*remainder →
    ∀ q, IsPrime q → q < candidate → remainder mod q ≠ 0 := by
  intro h he q hq hl hm
  have hd : q ∣ remainder := (Int.dvd_iff_fmod_eq_zero).mpr hm
  apply h.2.2.2.2.2.2 q hq hl
  apply (Int.dvd_iff_fmod_eq_zero).mp
  rw [he]
  exact dvd_mul_of_dvd_right hd _

theorem coq_pow_ge_one (a e : Int) (ha : 1 ≤ a) (he : 0 ≤ e) : 1 ≤ Z.pow a e := by
  have := coq_pow_pos a e (by omega) he
  omega

theorem strict_factor_prefix_append_completed_prime (m candidate original remainder exponent : Int) (pr pe : List Int) :
    StrictFactorPrefix m candidate original pr pe → IsPrime candidate → 1 ≤ exponent →
    original = Z.pow candidate exponent*remainder → 0 < remainder → remainder mod candidate ≠ 0 →
    Zlength pr < 64 → StrictFactorPrefix m (candidate+1) remainder (pr++[candidate]) (pe++[exponent]) := by
  rintro ⟨hf, ho⟩ hp he hd hr hn hroom
  have hf_before := hf
  obtain ⟨hl, hc, hcan, hori, hprod, hentries, hexclude⟩ := hf
  have hprlen : Zlength (pr++[candidate]) = Zlength pr+1 := by simp [Zlength]
  have hpelen : Zlength (pe++[exponent]) = Zlength pe+1 := by simp [Zlength]
  have hpower := coq_pow_ge_one candidate exponent (by omega) (by omega)
  refine ⟨⟨by omega, ⟨by omega, by omega⟩, by omega, ⟨hr, by nlinarith⟩, ?_, ?_, ?_⟩, ?_⟩
  · rw [factor_product_snoc pr pe candidate exponent hl, hprod, hd]
    ring
  · intro k hk
    by_cases hkin : k < Zlength pr
    · rw [app_Znth1 0 pr [candidate] k (by omega), app_Znth1 0 pe [exponent] k (by omega)]
      have hh := hentries k ⟨hk.1, hkin⟩
      exact ⟨hh.1, hh.2.1, by omega⟩
    · have heq : k = Zlength pr := by omega
      subst k
      rw [app_Znth2 0 pr [candidate] (Zlength pr) (by omega), app_Znth2 0 pe [exponent] (Zlength pr) (by omega), hl]
      simpa [Znth] using (show IsPrime candidate ∧ 1 ≤ exponent ∧ candidate < candidate+1 from ⟨hp, he, by omega⟩)
  · intro q hq hbelow
    by_cases hlt : q < candidate
    · exact factor_prefix_smaller_prime_survives_division m candidate original remainder pr pe candidate exponent hf_before hd q hq hlt
    · have heq : q = candidate := by omega
      simpa [heq] using hn
  · apply strict_prime_prefix_snoc pr candidate ho
    intro k hk
    exact (hentries k hk).2.2

theorem strict_factor_prefix_residual_ge_candidate (m candidate remainder : Int) (pr pe : List Int) :
    StrictFactorPrefix m candidate remainder pr pe → IsPrime remainder → candidate ≤ remainder := by
  intro h hp
  by_contra hn
  have he := h.1.2.2.2.2.2.2 remainder hp (by omega)
  exact he Int.fmod_self

theorem strict_factor_prefix_finalize_one (m candidate : Int) (pr pe : List Int) :
    StrictFactorPrefix m candidate 1 pr pe → ValidFactorTable m pr pe := by
  rintro ⟨⟨hl, hc, hcan, hr, hp, he, hn⟩, ho⟩
  refine ⟨hl, hc, by simpa using hp, ?_, ho⟩
  intro k hk
  exact ⟨(he k hk).1, (he k hk).2.1⟩

theorem strict_factor_prefix_finalize_prime_residual (m candidate remainder : Int) (pr pe : List Int) :
    StrictFactorPrefix m candidate remainder pr pe → IsPrime remainder → Zlength pr < 64 →
    ValidFactorTable m (pr++[remainder]) (pe++[1]) := by
  intro hs hp hroom
  have hg := strict_factor_prefix_residual_ge_candidate m candidate remainder pr pe hs hp
  obtain ⟨⟨hl, hc, hcan, hr, hprod, he, hn⟩, ho⟩ := hs
  have hprlen : Zlength (pr++[remainder]) = Zlength pr+1 := by simp [Zlength]
  have hpelen : Zlength (pe++[1]) = Zlength pe+1 := by simp [Zlength]
  refine ⟨by omega, ⟨by omega, by omega⟩, ?_, ?_, ?_⟩
  · rw [factor_product_snoc pr pe remainder 1 hl]
    simpa [Z.pow] using hprod
  · intro k hk
    by_cases hkin : k < Zlength pr
    · rw [app_Znth1 0 pr [remainder] k (by omega), app_Znth1 0 pe [1] k (by omega)]
      exact ⟨(he k ⟨hk.1, hkin⟩).1, (he k ⟨hk.1, hkin⟩).2.1⟩
    · have heq : k = Zlength pr := by omega
      subst k
      rw [app_Znth2 0 pr [remainder] (Zlength pr) (by omega), app_Znth2 0 pe [1] (Zlength pr) (by omega), hl]
      simpa [Znth] using (show IsPrime remainder ∧ (1:Int) ≤ 1 from ⟨hp, le_refl _⟩)
  · apply strict_prime_prefix_snoc pr remainder ho
    intro k hk
    have := (he k hk).2.2
    omega

theorem duplicated_prefix_is_rejected : ¬StrictFactorPrefix 60 4 5 [2,2,3] [1,1,1] := by
  rintro ⟨_, ho⟩
  have h := ho 0 1 (by decide)
  change (2:Int) < 2 at h
  omega

theorem duplicated_complete_prefix_is_rejected : ¬StrictFactorPrefix 12 4 1 [2,2,3] [1,1,1] := by
  rintro ⟨_, ho⟩
  have h := ho 0 1 (by decide)
  change (2:Int) < 2 at h
  omega

end P090_FactorTable
export P090_FactorTable (strict_factor_prefix_base strict_factor_prefix_forgets_order strict_factor_prefix_has_order strict_prime_prefix_lt strict_prime_prefix_distinct_indices strict_prime_prefix_snoc factor_product_snoc strict_factor_prefix_length_bounds strict_factor_prefix_snoc_capacity factor_prefix_smaller_prime_survives_division strict_factor_prefix_append_completed_prime strict_factor_prefix_residual_ge_candidate strict_factor_prefix_finalize_one strict_factor_prefix_finalize_prime_residual duplicated_prefix_is_rejected duplicated_complete_prefix_is_rejected)

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
