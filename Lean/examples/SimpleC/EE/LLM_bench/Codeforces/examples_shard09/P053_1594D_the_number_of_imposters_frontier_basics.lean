import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_initialization

set_option linter.unusedVariables false
set_option linter.style.nameCheck false
set_option maxRecDepth 1000
set_option maxHeartbeats 4000000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_lib
open AUXLib MaxMinLib

theorem singleton_component_frontier_strong__outer_loop_entry (n : Int) (comments : List Comment)
    (before ks : List Int) (s : Int) (hn : 1 ≤ n) (hs : 1 ≤ s ∧ s ≤ n)
    (hbl : Zlength before = n + 1) (hkl : Zlength ks = n + 1) (hcv : ColourValues n before)
    (hneg : Znth s before 0 < 0) :
    ComponentFrontierStrong n comments before (replace_Znth s 0 before) []
      (sublist 0 1 (replace_Znth 0 s ks)) 0 0 := by
  have hbefore : Znth s before 0 = -1 := by have := hcv.2 s hs; omega
  have hafter : Znth s (replace_Znth s 0 before) 0 = 0 := Znth_replace_Znth_Same 0 before s 0 ⟨by omega, by omega⟩
  have hp : sublist 0 1 (replace_Znth 0 s ks) = [s] := by
    cases ks with
    | nil => simp only [Zlength_nil] at hkl; omega
    | cons k ks => rfl
  rw [hp]
  have hcv' : ColourValues n (replace_Znth s 0 before) := by
    refine ⟨by rw [Zlength_replace_Znth]; exact hbl, ?_⟩
    intro v hv
    by_cases he : v = s
    · subst v; exact Or.inr (Or.inl hafter)
    · rw [Znth_replace_Znth_Diff 0 before s v 0 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (Ne.symm he)]
      exact hcv.2 v hv
  have hnew : NewColourSet n before (replace_Znth s 0 before) [s] := by
    refine ⟨by simp, Forall.cons hs Forall.nil, ?_, ?_⟩
    · intro v hv
      constructor
      · intro hm
        have he : v = s := by simpa using hm
        subst v
        exact ⟨hbefore, by rw [hafter]; omega⟩
      · intro hh
        by_cases he : v = s
        · simp [he]
        · rw [Znth_replace_Znth_Diff 0 before s v 0 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (Ne.symm he)] at hh
          exact False.elim (hh.2 hh.1)
    · intro v hv hn
      have he : s ≠ v := by intro he; exact hn (by simp only [List.mem_singleton]; exact he.symm)
      exact Znth_replace_Znth_Diff 0 before s v 0 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ he
  have htwo : ComponentTwoChoices n comments (replace_Znth s 0 before) [s] := by
    intro roles hr
    have hrole : Znth (s - 1) roles 0 = 0 ∨ Znth (s - 1) roles 0 = 1 :=
      Forall.iff_forall_mem.mp hr.2.1 _ (Znth_In__scan_conflict Int roles 0 (s - 1) ⟨by omega, by rw [hr.1]; omega⟩)
    refine ⟨Znth (s - 1) roles 0, hrole, ?_⟩
    intro v hv
    have he : v = s := by simpa using hv
    subst v
    rw [hafter]
    rcases hrole with hz | ho
    · rw [hz]; rfl
    · rw [ho]; rfl
  have hlocal : ComponentTwoChoicesLocal n comments (replace_Znth s 0 before) [s] := by
    intro roles hr
    have hb := hr.2.1 s (by simp)
    refine ⟨Znth (s - 1) roles 0, hb, ?_⟩
    intro v hv
    have he : v = s := by simpa using hv
    subst v
    rw [hafter]
    rcases hb with hz | ho
    · rw [hz]; rfl
    · rw [ho]; rfl
  refine ⟨⟨hcv', hnew, htwo, ?_, rfl, rfl⟩, hlocal⟩
  intro e he hm
  contradiction

theorem sublist_pop_permutation__frontier_pop_to_scan (ks : List Int) (top : Int)
    (ht : 0 < top ∧ top ≤ Zlength ks) :
    Permutation (sublist 0 top ks) (Znth (top - 1) ks 0 :: sublist 0 (top - 1) ks) := by
  rw [sublist_split 0 top (top - 1) ks ⟨by omega, by omega⟩ ⟨by omega, ht.2⟩]
  have hs := sublist_single 0 (top - 1) ks ⟨by omega, by omega⟩
  rw [show top - 1 + 1 = top by omega] at hs
  rw [hs]
  exact List.perm_append_comm

theorem nodup_app_keep_head__frontier_pop_to_scan (pref tail : List Int) (x : Int)
    (hn : (pref ++ x :: tail).Nodup) : (pref ++ [x]).Nodup := by
  have hs : (pref ++ [x]).Sublist (pref ++ x :: tail) :=
    List.Sublist.append (List.Sublist.refl pref) (List.Sublist.cons_cons x (List.nil_sublist _))
  exact List.Sublist.nodup hs hn

theorem nodup_bounded_Zlength__frontier_pop_to_scan (xs : List Int) (n : Int)
    (hn : 0 ≤ n) (hnd : xs.Nodup) (hall : Forall (fun x => 1 ≤ x ∧ x ≤ n) xs) : Zlength xs ≤ n := by
  have hsub : xs ⊆ (List.range' 1 n.toNat).map (fun k : Nat => (k : Int)) := by
    intro x hx
    have hb := Forall.iff_forall_mem.mp hall x hx
    apply List.mem_map.mpr
    refine ⟨x.toNat, ?_, by omega⟩
    apply List.mem_range'.mpr
    exact ⟨(x - 1).toNat, by omega, by omega⟩
  have hl := (List.subperm_of_subset hnd hsub).length_le
  simp only [List.length_map, List.length_range'] at hl
  simp only [Zlength, Int.ofNat_eq_coe]
  omega

theorem colour_counts_cover__frontier_pop_to_scan (n : Int) (cs vertices : List Int)
    (hcv : ColourValues n cs) (hall : Forall (fun v => 1 ≤ v ∧ v ≤ n) vertices)
    (hcol : ∀ v, v ∈ vertices → Znth v cs 0 ≠ -1) :
    ((vertices.map (fun v => Znth v cs 0)).count 0 +
      (vertices.map (fun v => Znth v cs 0)).count 1) = vertices.length := by
  induction hall with
  | nil => rfl
  | @cons v vs hv ht ih =>
    have hvn := hcol v (by simp)
    have hb := hcv.2 v hv
    have hh := ih (by intro x hx; exact hcol x (List.mem_cons_of_mem _ hx))
    rcases hb with hm | hz | ho
    · exact False.elim (hvn hm)
    · simp only [List.map_cons, List.length_cons, hz, List.count_cons, beq_self_eq_true, ite_true,
        show ((0 : Int) == 1) = false by decide, Bool.false_eq_true, ↓reduceIte]
      omega
    · simp only [List.map_cons, List.length_cons, ho, List.count_cons, beq_self_eq_true, ite_true,
        show ((1 : Int) == 0) = false by decide, Bool.false_eq_true, ↓reduceIte]
      omega

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_lib
