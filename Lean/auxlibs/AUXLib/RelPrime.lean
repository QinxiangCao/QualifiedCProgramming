import AUXLib.Arithmetic

-- Reached source interfaces of Coq 8.20.1 ZArith/Znumtheory.v.
namespace AUXLib.RelPrime

inductive Zis_gcd (a b g : Int) : Prop where
  | Zis_gcd_intro : Z.divide g a → Z.divide g b →
      (∀ x, Z.divide x a → Z.divide x b → Z.divide x g) → Zis_gcd a b g

-- Coq exposes the three parameters explicitly at this constructor.
@[match_pattern] abbrev Zis_gcd_intro (a b g : Int) (ha : Z.divide g a) (hb : Z.divide g b)
    (h : ∀ x, Z.divide x a → Z.divide x b → Z.divide x g) : Zis_gcd a b g :=
  Zis_gcd.Zis_gcd_intro ha hb h

def rel_prime (a b : Int) : Prop := Zis_gcd a b 1

theorem Zgcd_1_rel_prime (a b : Int) : Z.gcd a b = 1 ↔ rel_prime a b := by
  constructor
  · intro hg
    have hnat : Int.gcd a b = 1 := by
      simp only [Z.gcd, Int.ofNat_eq_coe] at hg
      omega
    refine .Zis_gcd_intro ⟨a, by simp⟩ ⟨b, by simp⟩ ?_
    intro x ha hb
    exact (Z.divide_iff_dvd x 1).mpr ((Int.gcd_eq_one_iff.mp hnat) x
      ((Z.divide_iff_dvd x a).mp ha) ((Z.divide_iff_dvd x b).mp hb))
  · intro h
    cases h with
    | Zis_gcd_intro ha hb hl =>
      have hg : Int.gcd a b = 1 := Int.gcd_eq_one_iff.mpr (by
        intro x hxa hxb
        exact (Z.divide_iff_dvd x 1).mp (hl x
          ((Z.divide_iff_dvd x a).mpr hxa) ((Z.divide_iff_dvd x b).mpr hxb)))
      simp only [Z.gcd, hg]
      rfl

private theorem bezout_nat_right (n : Nat) :
    ∀ a : Int, ∃ u v : Int, u*a+v*(n : Int) = (Int.gcd a n : Int) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro a
    by_cases hn : n = 0
    · subst n
      by_cases ha : 0 ≤ a
      · refine ⟨1, 0, ?_⟩
        simpa only [Int.natCast_zero, Int.one_mul, Int.zero_mul, Int.add_zero, Int.gcd_zero] using Int.eq_natAbs_of_nonneg ha
      · refine ⟨-1, 0, ?_⟩
        simpa only [Int.natCast_zero, Int.neg_one_mul, Int.zero_mul, Int.add_zero, Int.gcd_zero] using
          (Int.ofNat_natAbs_of_nonpos (show a ≤ 0 by omega)).symm
    · have hnp : 0 < (n : Int) := by omega
      let r := a % (n : Int)
      have hr0 : 0 ≤ r := Int.emod_nonneg _ (by omega)
      have hrlt : r < (n : Int) := Int.emod_lt_of_pos _ hnp
      have hrt : r.toNat < n := by omega
      have hrnat : (r.toNat : Int) = r := by omega
      obtain ⟨u, v, huv⟩ := ih r.toNat hrt (n : Int)
      rw [hrnat] at huv
      have he : r + (a / (n : Int)) * (n : Int) = a := Int.emod_add_ediv_mul _ _
      have hg : Int.gcd (n : Int) r = Int.gcd a (n : Int) := by
        rw [Int.gcd_comm (n : Int) r, ← Int.gcd_add_mul_right_left (n : Int) r (a / (n : Int)), he]
      rw [hg] at huv
      refine ⟨v, u-v*(a / (n : Int)), ?_⟩
      grind

-- New proof helper, not a redefinition of Coq's unqualified inductive Bezout.
theorem gcd_eq_one_bezout (a b : Int) (hg : Z.gcd a b = 1) :
    ∃ u v : Int, u*a+v*b=1 := by
  have hnat : (Int.gcd a b : Int) = 1 := hg
  by_cases hb : 0 ≤ b
  · obtain ⟨u, v, huv⟩ := bezout_nat_right b.toNat a
    have hbn : (b.toNat : Int) = b := by omega
    rw [hbn, hnat] at huv
    exact ⟨u,v,huv⟩
  · obtain ⟨u, v, huv⟩ := bezout_nat_right (-b).toNat a
    have hbn : ((-b).toNat : Int) = -b := by omega
    rw [hbn, Int.gcd_neg, hnat] at huv
    exact ⟨u,-v,by grind⟩

end AUXLib.RelPrime
