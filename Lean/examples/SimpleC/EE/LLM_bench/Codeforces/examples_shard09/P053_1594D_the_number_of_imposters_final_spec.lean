import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_optimality

set_option linter.unusedVariables false
set_option linter.style.nameCheck false
set_option maxRecDepth 1000
set_option maxHeartbeats 4000000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_lib
open AUXLib MaxMinLib

theorem xor_roles_equiv__final_specification (ru rv c : Int)
    (hu : ru = 0 ∨ ru = 1) (hv : rv = 0 ∨ rv = 1) (hc : c = 0 ∨ c = 1) :
    ((ru = 0 ∧ rv = c) ∨ (ru = 1 ∧ rv ≠ c) ↔ rv = Z.lxor ru c) := by
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> rcases hc with rfl | rfl <;> decide

private theorem p053_mem_index {A : Type} (xs : List A) (x d : A) (hx : x ∈ xs) :
    ∃ i : Int, (0 ≤ i ∧ i < Zlength xs) ∧ Znth i xs d = x := by
  obtain ⟨k,hk,he⟩ := List.getElem_of_mem hx
  refine ⟨(k:Int),⟨by omega,by simp only [Zlength,Int.ofNat_eq_coe]; omega⟩,?_⟩
  simp [Znth,List.getD,List.getElem?_eq_getElem hk,he]

theorem roles_consistent_iff_consistent_on_total__final_specification (n : Int) (comments : List Comment)
    (cs roles : List Int) (ht : ∀ v, (1 ≤ v ∧ v ≤ n) → Znth v cs 0 ≠ -1)
    (hv : ∀ i, (0 ≤ i ∧ i < Zlength comments) → let ((u,v),w) := comment_at comments i;
      (1 ≤ u ∧ u ≤ n) ∧ (1 ≤ v ∧ v ≤ n) ∧ (w = 0 ∨ w = 1)) :
    ConsistentOn n comments cs roles ↔ RolesConsistent n comments roles := by
  constructor
  · rintro ⟨⟨hlen,hbits,hzero⟩,hp⟩
    refine ⟨hlen,?_,?_⟩
    · apply Forall.iff_forall_mem.mpr
      intro x hx
      obtain ⟨i,hi,he⟩ := p053_mem_index roles x 0 hx
      have hb : 1 ≤ i+1 ∧ i+1 ≤ n := by omega
      have hh := hbits (i+1) hb (ht _ hb)
      simpa only [Int.add_sub_cancel,he] using hh
    · rintro ⟨⟨u,v⟩,w⟩ hm
      obtain ⟨i,hi,hq⟩ := p053_mem_index comments ((u,v),w) ((0,0),0) hm
      change comment_at comments i = ((u,v),w) at hq
      have hvalid := hv i hi
      have hpar := hp i hi
      rw [hq] at hvalid hpar
      obtain ⟨hu,hv,hw⟩ := hvalid
      exact (xor_roles_equiv__final_specification _ _ _ (hbits u hu (ht _ hu)) (hbits v hv (ht _ hv)) hw).mpr
        (hpar (ht u hu) (ht v hv))
  · rintro ⟨hlen,hbits,hcomments⟩
    have hbit (v : Int) (hv : 1 ≤ v ∧ v ≤ n) : Znth (v-1) roles 0 = 0 ∨ Znth (v-1) roles 0 = 1 :=
      Forall.iff_forall_mem.mp hbits _ (Znth_In__scan_conflict Int roles 0 (v-1) ⟨by omega,by omega⟩)
    refine ⟨⟨hlen,fun v hv _ => hbit v hv,fun v hv hm => False.elim (ht v hv hm)⟩,?_⟩
    intro i hi
    rcases hq : comment_at comments i with ⟨⟨u,v⟩,w⟩
    dsimp
    intro _ _
    have hm := Znth_In__scan_conflict Comment comments ((0,0),0) i hi
    change comment_at comments i ∈ comments at hm
    rw [hq] at hm
    have hc := hcomments ((u,v),w) hm
    have hvalid := hv i hi
    rw [hq] at hvalid
    obtain ⟨hu,hv,hw⟩ := hvalid
    exact (xor_roles_equiv__final_specification _ _ _ (hbit u hu) (hbit v hv) hw).mp hc

theorem max_imposters_on_total_implies_spec__final_specification (n : Int) (comments : List Comment)
    (cs : List Int) (total : Int) (h0 : 0 ≤ total) (ht : ∀ v, (1 ≤ v ∧ v ≤ n) → Znth v cs 0 ≠ -1)
    (hv : ∀ i, (0 ≤ i ∧ i < Zlength comments) → let ((u,v),w) := comment_at comments i;
      (1 ≤ u ∧ u ≤ n) ∧ (1 ≤ v ∧ v ≤ n) ∧ (w = 0 ∨ w = 1))
    (hmax : MaxImpostersOn n comments cs total) : Spec n comments total := by
  refine Or.inr ⟨h0,?_⟩
  rcases hmax with ⟨x,⟨⟨roles,hr,hx⟩,hu⟩,hxt⟩
  refine ⟨x,⟨⟨roles,?_,hx⟩,?_⟩,hxt⟩
  · exact (roles_consistent_iff_consistent_on_total__final_specification _ _ _ _ ht hv).mp hr
  · rintro b ⟨roles,hr,hb⟩
    exact hu b ⟨roles,(roles_consistent_iff_consistent_on_total__final_specification _ _ _ _ ht hv).mpr hr,hb⟩

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_lib
