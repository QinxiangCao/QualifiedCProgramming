import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_scan_basics

set_option linter.unusedVariables false
set_option linter.style.nameCheck false
set_option maxRecDepth 1000
set_option maxHeartbeats 4000000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_lib
open AUXLib MaxMinLib

theorem component_two_choices_extend__scan_edge_transitions (n : Int) (comments : List Comment)
    (before cs oldvs : List Int) (u v w x : Int) (hcv : ColourValues n cs)
    (hnew : NewColourSet n before cs oldvs) (htwo : ComponentTwoChoices n comments cs oldvs)
    (hu : u ∈ oldvs) (hv : 1 ≤ v ∧ v ≤ n) (hneg : Znth v cs 0 < 0)
    (hw : w = 0 ∨ w = 1) (hx : x = Z.lxor (Znth u cs 0) w)
    (hedge : ∀ roles, RolesConsistent n comments roles →
      Znth (v - 1) roles 0 = Z.lxor (Znth (u - 1) roles 0) w) :
    ComponentTwoChoices n comments (replace_Znth v x cs) (oldvs ++ [v]) := by
  have hvm : Znth v cs 0 = -1 := by have := hcv.2 v hv; omega
  have hnot : v ∉ oldvs := by intro hm; exact ((hnew.2.2.1 v hv).mp hm).2 hvm
  have hub := Forall.iff_forall_mem.mp hnew.2.1 u hu
  have hubit : Znth u cs 0 = 0 ∨ Znth u cs 0 = 1 := by
    have := hcv.2 u hub
    have := ((hnew.2.2.1 u hub).mp hu).2
    omega
  intro roles hr
  obtain ⟨flip, hf, he⟩ := htwo roles hr
  refine ⟨flip, hf, ?_⟩
  intro z hz
  rcases List.mem_append.mp hz with hz | hz
  · have hzb := Forall.iff_forall_mem.mp hnew.2.1 z hz
    have hne : v ≠ z := by intro hh; exact hnot (hh ▸ hz)
    rw [Znth_replace_Znth_Diff 0 cs v z x ⟨by omega, by rw [hcv.1]; omega⟩
      ⟨by omega, by rw [hcv.1]; omega⟩ hne]
    exact he z hz
  · have hez : z = v := by simpa only [List.mem_singleton] using hz
    subst z
    rw [Znth_replace_Znth_Same 0 cs v x ⟨by omega, by rw [hcv.1]; omega⟩, hx, hedge roles hr, he u hu]
    exact xor_extend_flip__scan_edge_transitions _ _ _ hubit hw hf

theorem component_two_choices_local_extend__scan_edge_transitions (n : Int) (comments : List Comment)
    (before cs oldvs : List Int) (u v w x : Int) (hcv : ColourValues n cs)
    (hnew : NewColourSet n before cs oldvs) (htwo : ComponentTwoChoicesLocal n comments cs oldvs)
    (hu : u ∈ oldvs) (hv : 1 ≤ v ∧ v ≤ n) (hneg : Znth v cs 0 < 0)
    (hw : w = 0 ∨ w = 1) (hx : x = Z.lxor (Znth u cs 0) w)
    (hedge : ∀ roles, RolesConsistentOnVertices n comments (oldvs ++ [v]) roles →
      Znth (v - 1) roles 0 = Z.lxor (Znth (u - 1) roles 0) w) :
    ComponentTwoChoicesLocal n comments (replace_Znth v x cs) (oldvs ++ [v]) := by
  have hvm : Znth v cs 0 = -1 := by have := hcv.2 v hv; omega
  have hnot : v ∉ oldvs := by intro hm; exact ((hnew.2.2.1 v hv).mp hm).2 hvm
  have hub := Forall.iff_forall_mem.mp hnew.2.1 u hu
  have hubit : Znth u cs 0 = 0 ∨ Znth u cs 0 = 1 := by
    have := hcv.2 u hub
    have := ((hnew.2.2.1 u hub).mp hu).2
    omega
  intro roles hr
  have hrold : RolesConsistentOnVertices n comments oldvs roles := by
    refine ⟨hr.1, ?_, ?_⟩
    · intro z hz
      exact hr.2.1 z (List.mem_append.mpr (Or.inl hz))
    · intro i hi
      dsimp
      intro ha hb
      exact hr.2.2 i hi (List.mem_append.mpr (Or.inl ha)) (List.mem_append.mpr (Or.inl hb))
  obtain ⟨flip, hf, he⟩ := htwo roles hrold
  refine ⟨flip, hf, ?_⟩
  intro z hz
  rcases List.mem_append.mp hz with hz | hz
  · have hzb := Forall.iff_forall_mem.mp hnew.2.1 z hz
    have hne : v ≠ z := by intro hh; exact hnot (hh ▸ hz)
    rw [Znth_replace_Znth_Diff 0 cs v z x ⟨by omega, by rw [hcv.1]; omega⟩
      ⟨by omega, by rw [hcv.1]; omega⟩ hne]
    exact he z hz
  · have hez : z = v := by simpa only [List.mem_singleton] using hz
    subst z
    rw [Znth_replace_Znth_Same 0 cs v x ⟨by omega, by rw [hcv.1]; omega⟩, hx, hedge roles hr, he u hu]
    exact xor_extend_flip__scan_edge_transitions _ _ _ hubit hw hf

theorem new_colour_set_extend__scan_edge_transitions (n : Int) (before cs oldvs : List Int) (v x : Int)
    (hv : 1 ≤ v ∧ v ≤ n) (hx : x = 0 ∨ x = 1) (hneg : Znth v cs 0 < 0)
    (hcv : ColourValues n cs) (hnew : NewColourSet n before cs oldvs) :
    NewColourSet n before (replace_Znth v x cs) (oldvs ++ [v]) := by
  have hvm : Znth v cs 0 = -1 := by have := hcv.2 v hv; omega
  have hnot : v ∉ oldvs := by intro hm; exact ((hnew.2.2.1 v hv).mp hm).2 hvm
  have hb : Znth v before 0 = -1 := (hnew.2.2.2 v hv hnot).symm.trans hvm
  have hvr : 0 ≤ v ∧ v < Zlength cs := ⟨by omega, by rw [hcv.1]; omega⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply List.nodup_append.mpr
    refine ⟨hnew.1, by simp, ?_⟩
    intro a ha b hb he
    have hb' : b = v := by simpa only [List.mem_singleton] using hb
    exact hnot ((he.trans hb') ▸ ha)
  · apply Forall.iff_forall_mem.mpr
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact Forall.iff_forall_mem.mp hnew.2.1 z hz
    · have he : z = v := by simpa only [List.mem_singleton] using hz
      rwa [he]
  · intro z hz
    constructor
    · intro hm
      rcases List.mem_append.mp hm with hm | hm
      · have hne : v ≠ z := by intro hh; exact hnot (hh ▸ hm)
        rw [Znth_replace_Znth_Diff 0 cs v z x hvr ⟨by omega, by rw [hcv.1]; omega⟩ hne]
        exact (hnew.2.2.1 z hz).mp hm
      · have he : z = v := by simpa only [List.mem_singleton] using hm
        subst z
        rw [Znth_replace_Znth_Same 0 cs v x hvr]
        exact ⟨hb, by omega⟩
    · intro hh
      by_cases he : z = v
      · exact List.mem_append.mpr (Or.inr (by simp [he]))
      · apply List.mem_append.mpr
        left
        rw [Znth_replace_Znth_Diff 0 cs v z x hvr ⟨by omega, by rw [hcv.1]; omega⟩ (Ne.symm he)] at hh
        exact (hnew.2.2.1 z hz).mpr hh
  · intro z hz hm
    have he : v ≠ z := by intro he; apply hm; exact List.mem_append.mpr (Or.inr (by simp only [List.mem_singleton]; exact he.symm))
    rw [Znth_replace_Znth_Diff 0 cs v z x hvr ⟨by omega, by rw [hcv.1]; omega⟩ he]
    exact hnew.2.2.2 z hz (fun hz => hm (List.mem_append.mpr (Or.inl hz)))

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_lib
