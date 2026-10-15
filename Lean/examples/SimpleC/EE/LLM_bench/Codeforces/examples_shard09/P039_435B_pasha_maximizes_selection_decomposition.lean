import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P039_435B_pasha_maximizes_lexicographic

set_option linter.unusedVariables false
set_option maxRecDepth 1000
set_option maxHeartbeats 4000000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P039_435B_pasha_maximizes_lib
open AUXLib

theorem ReachableFirstMaximum_decompose (current : List Int) (pos remaining best : Int)
    (hm : ReachableFirstMaximum current pos remaining best) :
    ∃ pref middle x suffix,
      current = pref ++ middle ++ x :: suffix ∧ Zlength pref = pos ∧ Zlength middle = best - pos ∧
      Forall (fun y => y < x) middle ∧ best - pos ≤ remaining ∧
      FirstRemove x (middle ++ x :: suffix) middle.length (middle ++ suffix) ∧
      move_left current best pos = pref ++ x :: middle ++ suffix := by
  rcases hm with ⟨hpos, hhi, hb, hmax, hfirst⟩
  let pref := sublist 0 pos current
  let middle := sublist pos best current
  let x := Znth best current 0
  let suffix := sublist (best + 1) (Zlength current) current
  have hpl : Zlength pref = pos := by simpa [pref] using p039_Zlength_sublist 0 pos current ⟨by omega, hpos.1⟩ (by omega)
  have hml : Zlength middle = best - pos := p039_Zlength_sublist pos best current ⟨hpos.1, hb.1⟩ (by omega)
  have hd : current = pref ++ middle ++ x :: suffix := by
    have hs := sublist_self current (Zlength current) rfl
    rw [sublist_split 0 (Zlength current) pos current ⟨by omega, hpos.1⟩ ⟨by omega, le_rfl⟩,
      sublist_split pos (Zlength current) best current ⟨hpos.1, hb.1⟩ ⟨by omega, le_rfl⟩,
      sublist_split best (Zlength current) (best + 1) current ⟨by omega, by omega⟩ ⟨by omega, le_rfl⟩,
      sublist_single 0 best current ⟨by omega, by omega⟩] at hs
    simpa only [pref, middle, x, suffix, List.singleton_append, List.append_assoc] using hs.symm
  have hsmall : Forall (fun y => y < x) middle := by
    apply Forall.iff_forall_mem.mpr
    intro y hy
    obtain ⟨n, hn, he⟩ := List.getElem_of_mem hy
    have hn' : 0 ≤ (n : Int) ∧ (n : Int) < Zlength middle := by simp only [Zlength, Int.ofNat_eq_coe]; omega
    have hf := hfirst (pos + n) ⟨by omega, by omega⟩
    have hv : Znth (n : Int) middle 0 = y := by simp [Znth, List.getD, List.getElem?_eq_getElem hn, he]
    rw [Znth_sublist 0 pos n best current hpos.1 (by omega)] at hv
    change Znth (pos + n) current 0 < x at hf
    rw [show pos + (n : Int) = n + pos by omega, hv] at hf
    exact hf
  have hr : FirstRemove x (middle ++ x :: suffix) middle.length (middle ++ suffix) := by
    apply FirstRemove_app_absent
    apply Forall.iff_forall_mem.mpr
    intro y hy
    have hs := Forall.iff_forall_mem.mp hsmall y hy
    omega
  refine ⟨pref, middle, x, suffix, hd, hpl, hml, hsmall, by omega, hr, ?_⟩
  rw [hd, ← hpl, show best = Zlength pref + Zlength middle by omega]
  exact move_left_app_middle _ _ _ _

theorem app_cancel_equal_Zlength (left_prefix left_tail right_prefix right_tail : List Int)
    (hl : Zlength left_prefix = Zlength right_prefix)
    (ha : left_prefix ++ left_tail = right_prefix ++ right_tail) :
    left_prefix = right_prefix ∧ left_tail = right_tail :=
  List.append_inj ha (by simp only [Zlength, Int.ofNat_eq_coe] at hl; omega)

theorem FirstRemove_Znth (x : Int) (source : List Int) (position : Nat) (rest : List Int)
    (hr : FirstRemove x source position rest) : Znth (position : Int) source 0 = x := by
  obtain ⟨pref, suffix, hs, ht, hl, ha⟩ := FirstRemove_decompose _ _ _ _ hr
  have hpl : Zlength pref = (position : Int) := by simp only [Zlength, hl, Int.ofNat_eq_coe]
  rw [hs, app_Znth2 0 pref (x :: suffix) _ (by omega), hpl, sub_self, Znth0_cons]

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P039_435B_pasha_maximizes_lib
