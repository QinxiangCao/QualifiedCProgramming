import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import ListLib.General.Length
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface

set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.rod_cutting.rod_cutting_lib
open AUXLib

def RodCutPlan (rod_len : Int) (pieces : List Int) : Prop :=
  0 ≤ rod_len ∧ Forall (fun piece => 1 ≤ piece ∧ piece ≤ rod_len) pieces ∧ sum pieces = rod_len

def RodCutPlanRevenue (price pieces : List Int) : Int :=
  sum (pieces.map (fun piece => Znth piece price 0))

def RodCutOptimalRevenue (price : List Int) (rod_len answer : Int) : Prop :=
  MaxMinLib.max_value_of_subset (· ≤ ·) (fun pieces : List Int => RodCutPlan rod_len pieces)
    (fun pieces => RodCutPlanRevenue price pieces) answer

def RodCutRevenueTable (price revenue : List Int) (upto : Int) : Prop :=
  ∀ rod_len : Int, (0 ≤ rod_len ∧ rod_len < upto) →
    RodCutOptimalRevenue price rod_len (Znth rod_len revenue 0)

def RodCutScanBest (price revenue : List Int) (rod_len next_piece best : Int) : Prop :=
  MaxMinLib.max_value_of_subset_with_default (· ≤ ·)
    (fun piece : Int => 1 ≤ piece ∧ piece < next_piece)
    (fun piece => Znth piece price 0 + Znth (rod_len - piece) revenue 0) 0 best

theorem rod_cut_scan_best_step__scan_transitions
    (f : Int → Int) (i best next_best : Int) (hi : 1 ≤ i)
    (hold : MaxMinLib.max_value_of_subset_with_default (· ≤ ·)
      (fun piece : Int => 1 ≤ piece ∧ piece < i) f 0 best)
    (hnext : (best ≤ f i ∧ next_best = f i) ∨ (f i ≤ best ∧ next_best = best)) :
    MaxMinLib.max_value_of_subset_with_default (· ≤ ·)
      (fun piece : Int => 1 ≤ piece ∧ piece < i + 1) f 0 next_best := by
  have hzero : 0 ≤ best := by
    rcases hold with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  have hbound : ∀ b, 1 ≤ b ∧ b < i → f b ≤ best := by
    intro b hb
    rcases hold with ⟨⟨a, ⟨ha, hm⟩, heq⟩, _⟩ | ⟨hm, heq⟩
    · have := hm b hb; omega
    · have := hm b hb; omega
  rcases hnext with ⟨hle, rfl⟩ | ⟨hle, rfl⟩
  · left
    refine ⟨⟨i, ⟨⟨hi, by omega⟩, ?_⟩, rfl⟩, by omega⟩
    intro b hb
    by_cases hbi : b < i
    · have := hbound b ⟨hb.1, hbi⟩; omega
    · have : b = i := by omega
      subst b; exact Int.le_refl _
  · rcases hold with ⟨⟨a, ⟨ha, hm⟩, heq⟩, hz⟩ | ⟨hm, heq⟩
    · left
      refine ⟨⟨a, ⟨⟨ha.1, by omega⟩, ?_⟩, heq⟩, hz⟩
      intro b hb
      by_cases hbi : b < i
      · exact hm b ⟨hb.1, hbi⟩
      · have : b = i := by omega
        subst b; omega
    · right
      refine ⟨?_, heq⟩
      intro b hb
      by_cases hbi : b < i
      · exact hm b ⟨hb.1, hbi⟩
      · have : b = i := by omega
        subst b; omega

theorem rod_cut_positive_sum_nonnegative__table_extension
    (parts : List Int) (hparts : Forall (fun piece => 1 ≤ piece) parts) : 0 ≤ sum parts := by
  induction hparts with
  | nil => exact Int.le_refl 0
  | @cons p parts hp hparts ih => change 0 ≤ p + sum parts; omega

theorem rod_cut_positive_sum_member_bound__table_extension
    (parts : List Int) (piece : Int) (hparts : Forall (fun p => 1 ≤ p) parts)
    (hin : In piece parts) : piece ≤ sum parts := by
  induction hparts with
  | nil => simp at hin
  | @cons p parts hp hparts ih =>
    change piece ≤ p + sum parts
    rcases List.mem_cons.mp hin with rfl | hmem
    · have := rod_cut_positive_sum_nonnegative__table_extension parts hparts; omega
    · have := ih hmem; omega

theorem rod_cut_plan_tail__table_extension
    (rod_len piece : Int) (tail : List Int) (hplan : RodCutPlan rod_len (piece :: tail)) :
    RodCutPlan (rod_len - piece) tail := by
  rcases hplan with ⟨hn, hparts, hsum⟩
  cases hparts with
  | cons hp ht =>
    change piece + sum tail = rod_len at hsum
    have htpos : Forall (fun p => 1 ≤ p) tail :=
      Forall.iff_forall_mem.mpr (fun q hq => (ht.mem hq).1)
    refine ⟨by omega, Forall.iff_forall_mem.mpr ?_, by omega⟩
    intro q hq
    have := ht.mem hq
    have := rod_cut_positive_sum_member_bound__table_extension tail q htpos hq
    omega

private theorem plan_zero_nil (pieces : List Int) (hp : RodCutPlan 0 pieces) : pieces = [] := by
  cases pieces with
  | nil => rfl
  | cons p ps =>
    have h := hp.2.1.mem (List.mem_cons_self (a := p) (l := ps))
    omega

private theorem plan_cons (n p : Int) (tail : List Int)
    (hp : 1 ≤ p ∧ p ≤ n) (ht : RodCutPlan (n - p) tail) : RodCutPlan n (p :: tail) := by
  refine ⟨by omega, Forall.cons hp ?_, ?_⟩
  · exact Forall.iff_forall_mem.mpr (fun q hq => by have := ht.2.1.mem hq; omega)
  · change p + sum tail = n
    have := ht.2.2; omega

private theorem revenue_cons (price : List Int) (p : Int) (tail : List Int) :
    RodCutPlanRevenue price (p :: tail) = Znth p price 0 + RodCutPlanRevenue price tail := rfl

theorem rod_cut_optimal_revenue_step__table_extension
    (price revenue : List Int) (rod_len best : Int)
    (hlen : 1 ≤ rod_len) (hprice : 0 ≤ Znth rod_len price 0)
    (htable : RodCutRevenueTable price revenue rod_len)
    (hscan : RodCutScanBest price revenue rod_len (rod_len + 1) best) :
    RodCutOptimalRevenue price rod_len best := by
  have hrzero : Znth 0 revenue 0 = 0 := by
    rcases htable 0 (by omega) with ⟨parts, ⟨hp, _⟩, hv⟩
    have he := plan_zero_nil parts hp
    subst parts
    exact hv.symm
  have hscanbound : ∀ p, 1 ≤ p ∧ p ≤ rod_len →
      Znth p price 0 + Znth (rod_len - p) revenue 0 ≤ best := by
    intro p hp
    rcases hscan with ⟨⟨q, ⟨_, hm⟩, hv⟩, _⟩ | ⟨hm, hv⟩
    · have := hm p (by omega); dsimp only at this hv; omega
    · have := hm p (by omega); dsimp only at this hv; omega
  have hupper : ∀ parts, RodCutPlan rod_len parts → RodCutPlanRevenue price parts ≤ best := by
    intro parts hp
    cases parts with
    | nil => have := hp.2.2; change 0 = rod_len at this; omega
    | cons p ps =>
      have hpbound := hp.2.1.mem (List.mem_cons_self (a := p) (l := ps))
      have ht := rod_cut_plan_tail__table_extension rod_len p ps hp
      rcases htable (rod_len - p) (by omega) with ⟨opt, ⟨_, hm⟩, hv⟩
      have hrest := hm ps ht
      have hb := hscanbound p hpbound
      rw [revenue_cons]
      dsimp only at hrest hv
      omega
  rcases hscan with ⟨⟨p, ⟨hp, _⟩, hv⟩, _⟩ | ⟨hm, hv⟩
  · rcases htable (rod_len - p) (by omega) with ⟨tail, ⟨ht, _⟩, htv⟩
    have heq : RodCutPlanRevenue price (p :: tail) = best := by rw [revenue_cons]; dsimp only at hv htv; omega
    exact ⟨p :: tail, ⟨plan_cons rod_len p tail (by omega) ht,
      fun parts hparts => by have := hupper parts hparts; dsimp only; omega⟩, heq⟩
  · have hc := hm rod_len (by omega)
    simp only [Int.sub_self, hrzero, Int.add_zero] at hc
    have heq : RodCutPlanRevenue price [rod_len] = best := by
      change Znth rod_len price 0 + 0 = best
      omega
    refine ⟨[rod_len], ⟨?_, fun parts hp => ?_⟩, heq⟩
    · exact ⟨by omega, Forall.cons ⟨hlen, Int.le_refl _⟩ Forall.nil, by change rod_len + 0 = rod_len; omega⟩
    · have := hupper parts hp; dsimp only; omega

theorem rod_cut_revenue_table_snoc__table_extension
    (price revenue : List Int) (rod_len best : Int)
    (hlen : 1 ≤ rod_len) (hrevenue_len : Zlength revenue = rod_len)
    (hprice : 0 ≤ Znth rod_len price 0)
    (htable : RodCutRevenueTable price revenue rod_len)
    (hscan : RodCutScanBest price revenue rod_len (rod_len + 1) best) :
    RodCutRevenueTable price (revenue ++ [best]) (rod_len + 1) := by
  intro q hq
  by_cases hlt : q < rod_len
  · have hn : Znth q (revenue ++ [best]) 0 = Znth q revenue 0 :=
      ListLib.app_Znth1 0 revenue [best] q ⟨hq.1, by change q < Zlength revenue; omega⟩
    rw [hn]
    exact htable q (by omega)
  · have he : q = rod_len := by omega
    subst q
    rw [app_Znth2 0 revenue [best] rod_len (by omega), hrevenue_len, Int.sub_self]
    change RodCutOptimalRevenue price rod_len best
    exact rod_cut_optimal_revenue_step__table_extension price revenue rod_len best hlen hprice htable hscan

theorem rod_cut_optimal_revenue_zero__boundary_states (price : List Int) :
    RodCutOptimalRevenue price 0 0 := by
  refine ⟨[], ⟨⟨Int.le_refl _, Forall.nil, rfl⟩, ?_⟩, rfl⟩
  intro parts hp
  rw [plan_zero_nil parts hp]

end SimpleC.EE.LLM_bench.Algorithms.rod_cutting.rod_cutting_lib
