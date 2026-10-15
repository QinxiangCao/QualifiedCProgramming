import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_frontier_basics

set_option linter.unusedVariables false
set_option linter.style.nameCheck false
set_option maxRecDepth 1000
set_option maxHeartbeats 4000000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_lib
open AUXLib MaxMinLib

theorem Znth_In_bounds__scan_edge_transitions (A : Type) (l : List A) (d : A) (i : Int)
    (hi : 0 ≤ i ∧ i < Zlength l) : Znth i l d ∈ l := Znth_In__scan_conflict A l d i hi

theorem xor_relation_sym__scan_edge_transitions (a b w : Int)
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (hw : w = 0 ∨ w = 1)
    (he : b = Z.lxor a w) : a = Z.lxor b w := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hw with rfl | rfl <;>
    first | rfl | (norm_num only [show Z.lxor 0 0 = 0 by rfl, show Z.lxor 0 1 = 1 by rfl, show Z.lxor 1 0 = 1 by rfl, show Z.lxor 1 1 = 0 by rfl] at he)

theorem xor_extend_flip__scan_edge_transitions (a w f : Int)
    (ha : a = 0 ∨ a = 1) (hw : w = 0 ∨ w = 1) (hf : f = 0 ∨ f = 1) :
    Z.lxor (Z.lxor a f) w = Z.lxor (Z.lxor a w) f := by
  rcases ha with rfl | rfl <;> rcases hw with rfl | rfl <;> rcases hf with rfl | rfl <;> rfl

theorem contract_disj_xor__scan_edge_transitions (ru rv c : Int)
    (hv : rv = 0 ∨ rv = 1) (hc : c = 0 ∨ c = 1)
    (hh : (ru = 0 ∧ rv = c) ∨ (ru = 1 ∧ rv ≠ c)) : rv = Z.lxor ru c := by
  rcases hh with ⟨rfl, he⟩ | ⟨rfl, he⟩ <;> rcases hv with rfl | rfl <;> rcases hc with rfl | rfl <;>
    first | rfl | (norm_num only [show Z.lxor 0 0 = 0 by rfl, show Z.lxor 0 1 = 1 by rfl, show Z.lxor 1 0 = 1 by rfl, show Z.lxor 1 1 = 0 by rfl] at he)

theorem p053_edge_index_range (comments : List Comment) (e : Int)
    (he : 0 ≤ e ∧ e < 2 * Zlength comments) :
    0 ≤ Z.div e 2 ∧ Z.div e 2 < Zlength comments := by
  simp only [Z.div, Int.fdiv_eq_ediv_of_nonneg _ (by decide : (0 : Int) ≤ 2)]
  omega

theorem roles_consistent_edge__scan_edge_transitions (n : Int) (comments : List Comment)
    (roles : List Int) (e : Int) (he : 0 ≤ e ∧ e < 2 * Zlength comments)
    (hs : 1 ≤ edge_src comments e ∧ edge_src comments e ≤ n)
    (hd : 1 ≤ edge_dst comments e ∧ edge_dst comments e ≤ n)
    (hw : edge_wt comments e = 0 ∨ edge_wt comments e = 1)
    (hr : RolesConsistent n comments roles) :
    Znth (edge_dst comments e - 1) roles 0 =
      Z.lxor (Znth (edge_src comments e - 1) roles 0) (edge_wt comments e) := by
  have hi := p053_edge_index_range comments e he
  rcases hr with ⟨hl, hbits, hc⟩
  have hcomment := hc (comment_at comments (Z.div e 2))
    (Znth_In_bounds__scan_edge_transitions Comment comments ((0, 0), 0) _ hi)
  have hsb := Forall.iff_forall_mem.mp hbits _
    (Znth_In_bounds__scan_edge_transitions Int roles 0 (edge_src comments e - 1) ⟨by omega, by omega⟩)
  have hdb := Forall.iff_forall_mem.mp hbits _
    (Znth_In_bounds__scan_edge_transitions Int roles 0 (edge_dst comments e - 1) ⟨by omega, by omega⟩)
  unfold edge_src edge_dst edge_wt at *
  rcases hq : comment_at comments (Z.div e 2) with ⟨⟨a, b⟩, w⟩
  rw [hq] at hcomment hsb hdb hw
  cases hv : Z.even e <;> simp only [hv, Bool.false_eq_true, Bool.true_eq, ↓reduceIte] at hcomment hsb hdb hw ⊢
  · exact xor_relation_sym__scan_edge_transitions _ _ _ hdb hsb hw
      (contract_disj_xor__scan_edge_transitions _ _ _ hsb hw hcomment)
  · exact contract_disj_xor__scan_edge_transitions _ _ _ hdb hw hcomment

theorem roles_consistent_local_edge__scan_edge_transitions (n : Int) (comments : List Comment)
    (vertices roles : List Int) (e : Int) (he : 0 ≤ e ∧ e < 2 * Zlength comments)
    (hs : edge_src comments e ∈ vertices) (hd : edge_dst comments e ∈ vertices)
    (hw : edge_wt comments e = 0 ∨ edge_wt comments e = 1)
    (hr : RolesConsistentOnVertices n comments vertices roles) :
    Znth (edge_dst comments e - 1) roles 0 =
      Z.lxor (Znth (edge_src comments e - 1) roles 0) (edge_wt comments e) := by
  have hi := p053_edge_index_range comments e he
  rcases hr with ⟨hl, hbits, hc⟩
  have hcomment := hc (Z.div e 2) hi
  have hsb := hbits _ hs
  have hdb := hbits _ hd
  unfold edge_src edge_dst edge_wt at *
  rcases hq : comment_at comments (Z.div e 2) with ⟨⟨a, b⟩, w⟩
  rw [hq] at hcomment hsb hdb hw hs hd
  cases hv : Z.even e <;> simp only [hv, Bool.false_eq_true, Bool.true_eq, ↓reduceIte] at hcomment hsb hdb hw hs hd ⊢
  · exact xor_relation_sym__scan_edge_transitions _ _ _ hdb hsb hw (hcomment hd hs)
  · exact hcomment hs hd

theorem lxor_bit__scan_and_component_closure (a b : Int)
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) : Z.lxor a b = 0 ∨ Z.lxor a b = 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

theorem lxor_shuffle__scan_and_component_closure (a b c : Int) :
    Z.lxor (Z.lxor a b) c = Z.lxor (Z.lxor a c) b := by
  have hn (a b c : Nat) : Nat.xor (Nat.xor a b) c = Nat.xor (Nat.xor a c) b := by
    change (a ^^^ b) ^^^ c = (a ^^^ c) ^^^ b
    rw [Nat.xor_assoc, Nat.xor_assoc, Nat.xor_comm b c]
  cases a <;> cases b <;> cases c <;> simp only [Z.lxor]
  all_goals congr 1; exact hn _ _ _

theorem edge_forward__scan_and_component_closure (comments : List Comment) (i u v w : Int)
    (hc : comment_at comments i = ((u, v), w)) :
    edge_src comments (2 * i) = u ∧ edge_dst comments (2 * i) = v ∧ edge_wt comments (2 * i) = w := by
  have hd : Z.div (2 * i) 2 = i := by
    simp only [Z.div, Int.fdiv_eq_ediv_of_nonneg _ (by decide : (0 : Int) ≤ 2)]
    omega
  have he : Z.even (2 * i) = true := by simp only [Z.even, decide_eq_true_eq]; omega
  simp only [edge_src, edge_dst, edge_wt, hd, hc, he, ↓reduceIte]
  trivial

theorem edge_reverse__scan_and_component_closure (comments : List Comment) (i u v w : Int)
    (hc : comment_at comments i = ((u, v), w)) :
    edge_src comments (2 * i + 1) = v ∧ edge_dst comments (2 * i + 1) = u ∧ edge_wt comments (2 * i + 1) = w := by
  have hd : Z.div (2 * i + 1) 2 = i := by
    simp only [Z.div, Int.fdiv_eq_ediv_of_nonneg _ (by decide : (0 : Int) ≤ 2)]
    omega
  have he : Z.even (2 * i + 1) = false := by simp only [Z.even, decide_eq_false_iff_not]; omega
  simp only [edge_src, edge_dst, edge_wt, hd, hc, he, Bool.false_eq_true, ↓reduceIte]
  trivial

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P053_1594D_the_number_of_imposters_lib
