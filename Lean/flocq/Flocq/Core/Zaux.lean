namespace Flocq.Core.Zaux

/-! Lean migration of the radix slice from `flocq/src/Core/Zaux.v`. -/

structure radix where
  radix_val : Int
  radix_prop : decide (2 <= radix_val) = true

abbrev Build_radix (radix_val : Int)
    (radix_prop : decide (2 <= radix_val) = true) : radix :=
  ⟨radix_val, radix_prop⟩

instance : Coe radix Int := ⟨radix.radix_val⟩

theorem radix_val_inj (r1 r2 : radix)
    (h : r1.radix_val = r2.radix_val) : r1 = r2 := by
  cases r1 with
  | mk v1 h1 =>
      cases r2 with
      | mk v2 h2 =>
          simp only at h
          subst v2
          rfl

def radix2 : radix :=
  ⟨2, by decide⟩

theorem radix_gt_0 (r : radix) : 0 < r.radix_val := by
  have : 2 <= r.radix_val := of_decide_eq_true r.radix_prop
  omega

theorem radix_gt_1 (r : radix) : 1 < r.radix_val := by
  exact of_decide_eq_true r.radix_prop

end Flocq.Core.Zaux

namespace Flocq.Core
export Zaux (radix Build_radix radix_val_inj radix2 radix_gt_0 radix_gt_1)
end Flocq.Core
