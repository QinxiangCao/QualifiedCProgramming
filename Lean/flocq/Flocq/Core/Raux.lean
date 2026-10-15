import Flocq.Core.Zaux
import Mathlib.Data.Int.Log
import Mathlib.Data.Real.Archimedean

namespace Flocq.Core.Raux

open Flocq.Core.Zaux

/-! Lean migration of the real helpers reached from `flocq/src/Core/Raux.v`. -/

noncomputable def bpow (beta : radix) (e : Int) : Real :=
  (beta.radix_val : Real) ^ e

noncomputable def Zfloor (x : Real) : Int :=
  Int.floor x

noncomputable def Zceil (x : Real) : Int :=
  Int.ceil x

noncomputable def Ztrunc (x : Real) : Int :=
  if x < 0 then Int.ceil x else Int.floor x

structure mag_prop (beta : radix) (x : Real) where
  mag_val : Int
  mag_bound : x ≠ 0 ->
    bpow beta (mag_val - 1) <= |x| /\ |x| < bpow beta mag_val

abbrev Build_mag_prop {beta : radix} {x : Real} (mag_val : Int)
    (h : x ≠ 0 ->
      bpow beta (mag_val - 1) <= |x| /\ |x| < bpow beta mag_val) :
    mag_prop beta x :=
  ⟨mag_val, h⟩

namespace mag_prop

instance : CoeOut (mag_prop beta x) Int := ⟨mag_val⟩

end mag_prop

noncomputable def mag (beta : radix) (x : Real) : mag_prop beta x := by
  by_cases hx : x = 0
  · exact ⟨0, fun h => (h hx).elim⟩
  · let value := Int.log beta.radix_val.toNat |x| + 1
    refine ⟨value, ?_⟩
    intro _
    have hbase : 1 < beta.radix_val.toNat := by
      have hnonneg : 0 <= beta.radix_val := le_of_lt (radix_gt_0 beta)
      rw [← Int.ofNat_lt]
      simpa [Int.toNat_of_nonneg hnonneg] using radix_gt_1 beta
    have habs : 0 < |x| := abs_pos.mpr hx
    have hbase_cast : (beta.radix_val.toNat : Int) = beta.radix_val :=
      Int.toNat_of_nonneg (le_of_lt (radix_gt_0 beta))
    constructor
    · have hlog := (Int.zpow_le_iff_le_log (R := Real) hbase habs).2
          (le_refl (Int.log beta.radix_val.toNat |x|))
      simp only [value, bpow]
      rw [show Int.log beta.radix_val.toNat |x| + 1 - 1 =
        Int.log beta.radix_val.toNat |x| by omega]
      change (beta.radix_val : Real) ^ Int.log beta.radix_val.toNat |x| <= |x|
      rw [← hbase_cast]
      norm_cast at hlog ⊢
    · have hlog := (Int.lt_zpow_iff_log_lt (R := Real) hbase habs).2
          (Int.lt_add_one_iff.mpr (le_refl _))
      simp only [value, bpow]
      change |x| < (beta.radix_val : Real) ^
        (Int.log beta.radix_val.toNat |x| + 1)
      rw [← hbase_cast]
      norm_cast at hlog ⊢

end Flocq.Core.Raux

namespace Flocq.Core
export Raux (bpow Zfloor Zceil Ztrunc mag_prop Build_mag_prop mag)
end Flocq.Core
