import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface

set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.matrix_chain_multiplication.matrix_chain_multiplication_lib
open AUXLib

def MatrixChainDimensionsBounded (dimensions : List Int) (matrix_count : Int) : Prop :=
  Zlength dimensions = matrix_count + 1 ∧
    ∀ i : Int, (0 ≤ i ∧ i ≤ matrix_count) → (1 ≤ Znth i dimensions 0 ∧ Znth i dimensions 0 ≤ 100)

inductive MatrixChainPlan (dimensions : List Int) : Int → Int → Int → Prop where
  | MatrixChainPlan_single (left : Int) : 0 ≤ left → left + 1 < Zlength dimensions →
      MatrixChainPlan dimensions left left 0
  | MatrixChainPlan_join (left split right left_cost right_cost : Int) :
      0 ≤ left → (left ≤ split ∧ split < right) → right + 1 < Zlength dimensions →
      MatrixChainPlan dimensions left split left_cost →
      MatrixChainPlan dimensions (split + 1) right right_cost →
      MatrixChainPlan dimensions left right (left_cost + right_cost +
        Znth left dimensions 0 * Znth (split + 1) dimensions 0 * Znth (right + 1) dimensions 0)
export MatrixChainPlan (MatrixChainPlan_single MatrixChainPlan_join)

def MatrixChainIntervalMinimum (dimensions : List Int) (left right answer : Int) : Prop :=
  MaxMinLib.min_value_of_subset (· ≤ ·)
    (fun scalar_cost => MatrixChainPlan dimensions left right scalar_cost)
    (fun scalar_cost => scalar_cost) answer

def MatrixChainMinimumCost (dimensions : List Int) (matrix_count answer : Int) : Prop :=
  Zlength dimensions = matrix_count + 1 ∧ MatrixChainIntervalMinimum dimensions 0 (matrix_count - 1) answer

def MatrixChainTableResult (dimensions table : List Int) (matrix_count : Int) : Prop :=
  Zlength table = matrix_count * matrix_count ∧
  ∀ left right : Int, (0 ≤ left ∧ left ≤ right ∧ right < matrix_count) →
    MatrixChainIntervalMinimum dimensions left right (Znth (left * matrix_count + right) table 0)

def MatrixChainZeroPrefix (table : List Int) (done : Int) : Prop :=
  Zlength table = done ∧ ∀ index : Int, (0 ≤ index ∧ index < done) → Znth index table 0 = 0

def MatrixChainTableValuesBounded (table : List Int) : Prop :=
  ∀ index : Int, (0 ≤ index ∧ index < Zlength table) →
    (0 ≤ Znth index table 0 ∧ Znth index table 0 ≤ 7000000)

def MatrixChainLengthsDone (dimensions table : List Int) (matrix_count next_length : Int) : Prop :=
  1 ≤ next_length ∧ ∀ length left right : Int,
    (1 ≤ length ∧ length < next_length) → right = left + length - 1 → 0 ≤ left →
    left + length ≤ matrix_count →
    MatrixChainIntervalMinimum dimensions left right (Znth (left * matrix_count + right) table 0)

def MatrixChainLeftProgress (dimensions table : List Int) (matrix_count length next_left : Int) : Prop :=
  MatrixChainLengthsDone dimensions table matrix_count length ∧ ∀ left right : Int,
    (0 ≤ left ∧ left < next_left) → right = left + length - 1 → left + length ≤ matrix_count →
    MatrixChainIntervalMinimum dimensions left right (Znth (left * matrix_count + right) table 0)

def MatrixChainSplitCandidate (dimensions table : List Int) (width left right split candidate : Int) : Prop :=
  candidate = Znth (left * width + split) table 0 + Znth ((split + 1) * width + right) table 0 +
    Znth left dimensions 0 * Znth (split + 1) dimensions 0 * Znth (right + 1) dimensions 0

def MatrixChainSplitProgress (dimensions table : List Int)
    (matrix_count width length left next_split best : Int) : Prop :=
  MatrixChainLeftProgress dimensions table matrix_count length left ∧
  let right := left + length - 1
  MaxMinLib.min_value_of_subset (· ≤ ·)
    (fun candidate => ∃ split : Int, (left ≤ split ∧ split < next_split) ∧
      MatrixChainSplitCandidate dimensions table width left right split candidate)
    (fun candidate => candidate) best

set_option maxHeartbeats 4000000

private theorem minimum_iff (P : Int → Prop) (v : Int) :
    MaxMinLib.min_value_of_subset (· ≤ ·) P id v ↔ P v ∧ ∀ x, P x → v ≤ x := by
  constructor
  · rintro ⟨x, ⟨hx, hleast⟩, rfl⟩
    exact ⟨hx, hleast⟩
  · rintro ⟨hv, hleast⟩
    exact ⟨v, ⟨hv, hleast⟩, rfl⟩

theorem matrix_chain_index_bounds (n i j : Int) (hn : 1 ≤ n)
    (hi : 0 ≤ i ∧ i < n) (hj : 0 ≤ j ∧ j < n) : 0 ≤ i*n+j ∧ i*n+j < n*n := by
  constructor
  · exact add_nonneg (mul_nonneg hi.1 (by omega)) hj.1
  · nlinarith

theorem matrix_chain_dimensions_product_bound (a b c : Int)
    (ha : 1 ≤ a ∧ a ≤ 100) (hb : 1 ≤ b ∧ b ≤ 100) (hc : 1 ≤ c ∧ c ≤ 100) :
    a*b*c ≤ 1000000 := by
  have hab : a*b ≤ 10000 := by nlinarith
  have ht := mul_le_mul_of_nonneg_right hab (show 0 ≤ c by omega)
  nlinarith

theorem matrix_chain_zero_table_lengths_done__initialization
    (dimensions table : List Int) (matrix_count : Int)
    (hcount : 1 ≤ matrix_count) (hdims : Zlength dimensions = matrix_count + 1)
    (hzero : MatrixChainZeroPrefix table (matrix_count * matrix_count)) :
    MatrixChainLengthsDone dimensions table matrix_count 2 := by
  refine ⟨by omega, ?_⟩
  intro length left right hl hr hleft hfits
  have he : length = 1 := by omega
  have her : right = left := by omega
  subst length right
  have hind := matrix_chain_index_bounds matrix_count left left hcount
    ⟨hleft, by omega⟩ ⟨hleft, by omega⟩
  rw [hzero.2 _ hind]
  apply (minimum_iff _ 0).mpr
  refine ⟨MatrixChainPlan_single left hleft (by omega), ?_⟩
  intro c hc
  cases hc with
  | MatrixChainPlan_single => omega
  | MatrixChainPlan_join l k r lc rc hleft hsplit => omega

theorem matrix_chain_plan_linear_upper_bound__candidate_progress
    (dimensions : List Int) (matrix_count left right : Int)
    (hdims : MatrixChainDimensionsBounded dimensions matrix_count)
    (hleft : 0 ≤ left) (horder : left ≤ right) (hright : right < matrix_count) :
    ∃ cost, MatrixChainPlan dimensions left right cost ∧ cost ≤ (right-left)*1000000 := by
  generalize hs : (right-left).toNat = span
  induction span generalizing left right with
  | zero =>
    have he : right = left := by omega
    subst right
    exact ⟨0, MatrixChainPlan_single left hleft (by have := hdims.1; omega), by omega⟩
  | succ span ih =>
    have hstrict : left < right := by omega
    obtain ⟨rc, hplan, hbound⟩ := ih (left+1) right (by omega) (by omega) hright (by omega)
    refine ⟨0+rc+Znth left dimensions 0*Znth (left+1) dimensions 0*Znth (right+1) dimensions 0, ?_, ?_⟩
    · exact MatrixChainPlan_join left left right 0 rc hleft ⟨le_refl _, hstrict⟩
        (by have := hdims.1; omega)
        (MatrixChainPlan_single left hleft (by have := hdims.1; omega)) hplan
    · have hb := matrix_chain_dimensions_product_bound _ _ _
        (hdims.2 left ⟨hleft, by omega⟩)
        (hdims.2 (left+1) ⟨by omega, by omega⟩)
        (hdims.2 (right+1) ⟨by omega, by omega⟩)
      omega

theorem matrix_chain_interval_minimum_upper_bound__candidate_progress
    (dimensions : List Int) (matrix_count left right answer : Int)
    (hdims : MatrixChainDimensionsBounded dimensions matrix_count)
    (hleft : 0 ≤ left) (horder : left ≤ right) (hright : right < matrix_count)
    (hmin : MatrixChainIntervalMinimum dimensions left right answer) :
    answer ≤ (right-left)*1000000 := by
  obtain ⟨cost, hp, hb⟩ := matrix_chain_plan_linear_upper_bound__candidate_progress
    dimensions matrix_count left right hdims hleft horder hright
  have hm := (minimum_iff _ answer).mp hmin
  exact le_trans (hm.2 cost hp) hb

theorem matrix_chain_split_progress_initial__candidate_progress
    (dimensions table : List Int) (matrix_count width length left : Int)
    (hp : MatrixChainLeftProgress dimensions table matrix_count length left) :
    MatrixChainSplitProgress dimensions table matrix_count width length left (left+1)
      (Znth (left*width+left) table 0 + Znth ((left+1)*width+(left+length-1)) table 0 +
       Znth left dimensions 0*Znth (left+1) dimensions 0*Znth ((left+length-1)+1) dimensions 0) := by
  refine ⟨hp, ?_⟩
  apply (minimum_iff _ _).mpr
  refine ⟨⟨left, ⟨by omega, by omega⟩, rfl⟩, ?_⟩
  rintro candidate ⟨split, hb, hc⟩
  have he : split = left := by omega
  subst split
  exact le_of_eq hc.symm

private theorem split_progress_extend
    (dimensions table : List Int) (matrix_count width length left split best candidate : Int)
    (hleft : left ≤ split)
    (hc : MatrixChainSplitCandidate dimensions table width left (left+length-1) split candidate)
    (hp : MatrixChainSplitProgress dimensions table matrix_count width length left split best) :
    MatrixChainSplitProgress dimensions table matrix_count width length left (split+1) (min best candidate) := by
  refine ⟨hp.1, ?_⟩
  have hm := (minimum_iff _ best).mp hp.2
  apply (minimum_iff _ _).mpr
  constructor
  · by_cases h : best ≤ candidate
    · rw [min_eq_left h]
      obtain ⟨root, hb, hr⟩ := hm.1
      exact ⟨root, ⟨hb.1, by omega⟩, hr⟩
    · rw [min_eq_right (by omega : candidate ≤ best)]
      exact ⟨split, ⟨hleft, by omega⟩, hc⟩
  · rintro value ⟨root, hb, hr⟩
    by_cases h : root < split
    · exact le_trans (min_le_left _ _) (hm.2 value ⟨root, ⟨hb.1, h⟩, hr⟩)
    · have he : root = split := by omega
      subst root
      have hv : value = candidate := hr.trans hc.symm
      rw [hv]
      exact min_le_right _ _

theorem matrix_chain_split_progress_better__min_update
    (dimensions table : List Int) (matrix_count width length left split best candidate : Int)
    (hleft : left ≤ split) (hbetter : candidate < best)
    (hc : MatrixChainSplitCandidate dimensions table width left (left+length-1) split candidate)
    (hp : MatrixChainSplitProgress dimensions table matrix_count width length left split best) :
    MatrixChainSplitProgress dimensions table matrix_count width length left (split+1) candidate := by
  simpa only [min_eq_right (le_of_lt hbetter)] using
    split_progress_extend dimensions table matrix_count width length left split best candidate hleft hc hp

theorem matrix_chain_split_progress_not_better__min_update
    (dimensions table : List Int) (matrix_count width length left split best candidate : Int)
    (hleft : left ≤ split) (hbetter : best ≤ candidate)
    (hc : MatrixChainSplitCandidate dimensions table width left (left+length-1) split candidate)
    (hp : MatrixChainSplitProgress dimensions table matrix_count width length left split best) :
    MatrixChainSplitProgress dimensions table matrix_count width length left (split+1) best := by
  simpa only [min_eq_left hbetter] using
    split_progress_extend dimensions table matrix_count width length left split best candidate hleft hc hp

theorem matrix_chain_split_progress_complete__min_update
    (dimensions table : List Int) (matrix_count length left right best : Int)
    (hlen : 2 ≤ length) (hleft : 0 ≤ left) (hr : right = left+length-1)
    (hrbound : right < matrix_count) (hdimbound : right+1 < Zlength dimensions)
    (hp : MatrixChainSplitProgress dimensions table matrix_count matrix_count length left right best) :
    MatrixChainIntervalMinimum dimensions left right best := by
  subst right
  have hdone := hp.1.1.2
  have hmin := (minimum_iff _ best).mp hp.2
  have subminimum (root : Int) (hroot : left ≤ root ∧ root < left+length-1) :=
    And.intro
      (hdone (root-left+1) left root ⟨by omega, by omega⟩ (by omega) hleft (by omega))
      (hdone (left+length-1-root) (root+1) (left+length-1) ⟨by omega, by omega⟩
        (by omega) (by omega) (by omega))
  apply (minimum_iff _ best).mpr
  constructor
  · obtain ⟨root, hb, hc⟩ := hmin.1
    have hm := subminimum root hb
    rw [hc]
    exact MatrixChainPlan_join left root (left+length-1) _ _ hleft hb hdimbound
      ((minimum_iff _ _).mp hm.1).1 ((minimum_iff _ _).mp hm.2).1
  · intro arbitrary hplan
    generalize he : left+length-1 = rr at hplan
    cases hplan with
    | MatrixChainPlan_single => omega
    | MatrixChainPlan_join l k r lc rc hl hb hd hpl hpr =>
      have hm := subminimum k ⟨hb.1, by omega⟩
      rw [← he] at hpr ⊢
      have hbl := ((minimum_iff _ _).mp hm.1).2 lc hpl
      have hbr := ((minimum_iff _ _).mp hm.2).2 rc hpr
      have hc := hmin.2 _ ⟨k, ⟨hb.1, by omega⟩, rfl⟩
      try dsimp at hbl hbr hc
      omega

end SimpleC.EE.LLM_bench.Algorithms.matrix_chain_multiplication.matrix_chain_multiplication_lib

-- Public interfaces of the current C annotations, matching the Rocq definitions.
namespace SimpleC.EE.LLM_bench.Algorithms.matrix_chain_multiplication.matrix_chain_multiplication_lib
open AUXLib

def MatrixChainLengthsComplete (dimensions table : List Int) (count next : Int) : Prop :=
  ∀ len left right : Int, (1 ≤ len ∧ len < next) → right = left + len - 1 →
    0 ≤ left → left + len ≤ count →
    MatrixChainIntervalMinimum dimensions left right (Znth (left * count + right) table 0)
def MatrixChainLeftComplete (dimensions table : List Int) (count len next : Int) : Prop :=
  MatrixChainLengthsComplete dimensions table count len ∧
  ∀ left right : Int, (0 ≤ left ∧ left < next) → right = left + len - 1 →
    left + len ≤ count →
    MatrixChainIntervalMinimum dimensions left right (Znth (left * count + right) table 0)
theorem MatrixChainLengthsDone.toAnnotation (h : MatrixChainLengthsDone dims table count next) :
    MatrixChainLengthsComplete dims table count next := h.2
theorem MatrixChainLeftProgress.toAnnotation (h : MatrixChainLeftProgress dims table count len next) :
    MatrixChainLeftComplete dims table count len next := ⟨h.1.2, h.2⟩

end SimpleC.EE.LLM_bench.Algorithms.matrix_chain_multiplication.matrix_chain_multiplication_lib
namespace SimpleC.EE.LLM_bench.Algorithms.matrix_chain_multiplication
export matrix_chain_multiplication_lib (MatrixChainLengthsComplete MatrixChainLeftComplete)
end SimpleC.EE.LLM_bench.Algorithms.matrix_chain_multiplication

-- Public interfaces of the current C annotations, matching the Rocq definitions.
namespace SimpleC.EE.LLM_bench.Algorithms.matrix_chain_multiplication.matrix_chain_multiplication_lib
open AUXLib

def MatrixChainOptimalCost (dimensions : List Int) (count answer : Int) : Prop :=
  MatrixChainIntervalMinimum dimensions 0 (count - 1) answer
def MatrixChainTableComplete (dimensions table : List Int) (count : Int) : Prop :=
  ∀ left right : Int, (0 ≤ left ∧ left ≤ right ∧ right < count) →
    MatrixChainIntervalMinimum dimensions left right (Znth (left * count + right) table 0)
def MatrixChainSplitMinimum (dimensions table : List Int)
    (count width len left next best : Int) : Prop :=
  MatrixChainLeftComplete dimensions table count len left ∧
  MaxMinLib.min_value_of_subset (LE.le (α := Int))
    (fun candidate => ∃ split : Int, (left ≤ split ∧ split < next) ∧
      MatrixChainSplitCandidate dimensions table width left (left + len - 1) split candidate)
    (fun candidate => candidate) best

end SimpleC.EE.LLM_bench.Algorithms.matrix_chain_multiplication.matrix_chain_multiplication_lib
namespace SimpleC.EE.LLM_bench.Algorithms.matrix_chain_multiplication
export matrix_chain_multiplication_lib (MatrixChainOptimalCost MatrixChainTableComplete MatrixChainSplitMinimum)
end SimpleC.EE.LLM_bench.Algorithms.matrix_chain_multiplication
