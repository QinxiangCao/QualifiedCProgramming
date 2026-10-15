import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import ListLib.General.Length
namespace SimpleC.EE.LLM_bench.Data_structures.binary_indexed_tree.binary_indexed_tree_lib
open AUXLib

def FenwickLowbit (x : Int) : Int := Z.land x (-x)
def FenwickNodeLo (i : Int) : Int := i - FenwickLowbit i + 1
def FenwickNodeSum (a : List Int) (i : Int) : Int := sum (sublist (FenwickNodeLo i) (i+1) a)
def FenwickPrefixSum (a : List Int) (pos : Int) : Int := sum (sublist 1 (pos+1) a)
def FenwickAddArray (a : List Int) (pos delta : Int) : List Int := replace_Znth pos (Znth pos a 0+delta) a

def FenwickRep (a bit : List Int) (n : Int) : Prop :=
  Zlength a = n+1 ∧ Zlength bit = n+1 ∧ Znth 0 a 0 = 0 ∧
  ∀ i, (1 ≤ i ∧ i ≤ n) → Znth i bit 0 = FenwickNodeSum a i

def FenwickIntervalsIntSafe (a : List Int) (n : Int) : Prop :=
  ∀ lo hi, (1 ≤ lo ∧ lo ≤ hi) → hi ≤ n →
    -2147483648 ≤ sum (sublist lo (hi+1) a) ∧ sum (sublist lo (hi+1) a) ≤ 2147483647

def FenwickCovers (node target : Int) : Prop := FenwickNodeLo node ≤ target ∧ target ≤ node

def FenwickAddProgress (entry current : List Int) (n target cursor delta : Int) : Prop :=
  Zlength current = Zlength entry ∧ Znth 0 current 0 = Znth 0 entry 0 ∧
  (cursor ≤ n → FenwickCovers cursor target) ∧ ∀ node, (1 ≤ node ∧ node ≤ n) →
    ((FenwickCovers node target ∧ node < cursor) → Znth node current 0 = Znth node entry 0+delta) ∧
    ((¬ FenwickCovers node target ∨ cursor ≤ node) → Znth node current 0 = Znth node entry 0)

def FenwickQueryState (a : List Int) (target cursor accumulator : Int) : Prop :=
  accumulator + FenwickPrefixSum a cursor = FenwickPrefixSum a target

private theorem lowbit_nat (n : Nat) :
    FenwickLowbit (n : Int) = ((n ^^^ (n &&& (n-1)) : Nat) : Int) := by
  cases n with
  | zero => rfl
  | succ n => rfl

private theorem lowbit_nat_le (n : Nat) : n ^^^ (n &&& (n-1)) ≤ n := by
  apply Nat.le_of_testBit
  intro i hi
  simp only [Nat.testBit_xor, Nat.testBit_and] at hi
  cases h1 : n.testBit i <;> cases h2 : (n-1).testBit i <;> simp_all

private theorem lowbit_nat_pos (n : Nat) (hn : 0 < n) : 0 < n ^^^ (n &&& (n-1)) := by
  apply Nat.pos_of_ne_zero
  intro hz
  have heq := congrArg (fun x => n ^^^ x) hz
  simp only [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor, Nat.xor_zero] at heq
  have hle : n &&& (n-1) ≤ n-1 := Nat.and_le_right
  omega

theorem FenwickLowbit_eq_land (x : Int) : FenwickLowbit x = Z.land x (-x) := rfl

theorem FenwickLowbit_positive (x : Int) (hx : 0 < x) : 0 < FenwickLowbit x := by
  cases x with
  | negSucc n => omega
  | ofNat n =>
    change 0 < FenwickLowbit (n : Int)
    rw [lowbit_nat]
    exact Int.natCast_pos.mpr (lowbit_nat_pos n (Int.ofNat_lt.mp hx))

theorem FenwickLowbit_nonnegative (x : Int) (hx : 0 ≤ x) : 0 ≤ FenwickLowbit x := by
  cases x with
  | negSucc n => omega
  | ofNat n => change 0 ≤ FenwickLowbit (n : Int); rw [lowbit_nat]; omega

theorem FenwickLowbit_le (x : Int) (hx : 0 ≤ x) : FenwickLowbit x ≤ x := by
  cases x with
  | negSucc n => omega
  | ofNat n =>
    change FenwickLowbit (n : Int) ≤ (n : Int)
    rw [lowbit_nat]
    exact Int.ofNat_le.mpr (lowbit_nat_le n)

theorem FenwickLowbit_bounds (x : Int) (hx : 0 < x) : 1 ≤ FenwickLowbit x ∧ FenwickLowbit x ≤ x := by
  have := FenwickLowbit_positive x hx
  exact ⟨by omega, FenwickLowbit_le x (by omega)⟩

theorem Fenwick_query_index_decreases (x : Int) (hx : 0 < x) : 0 ≤ x-FenwickLowbit x ∧ x-FenwickLowbit x < x := by
  have := FenwickLowbit_bounds x hx
  omega

theorem Fenwick_add_index_increases (x : Int) (hx : 0 < x) : x < x+FenwickLowbit x ∧ x+FenwickLowbit x ≤ 2*x := by
  have := FenwickLowbit_bounds x hx
  omega

theorem Fenwick_add_index_int_safe (n x : Int) (hx : 1 ≤ x ∧ x ≤ n) (hn : 2*n ≤ 2147483647) :
    x+FenwickLowbit x ≤ 2147483647 := by
  have := FenwickLowbit_bounds x (by omega)
  omega

theorem FenwickNodeLo_bounds (i : Int) (hi : 0 < i) : 1 ≤ FenwickNodeLo i ∧ FenwickNodeLo i ≤ i := by
  have := FenwickLowbit_bounds i hi
  unfold FenwickNodeLo
  omega

theorem FenwickCovers_self (i : Int) (hi : 0 < i) : FenwickCovers i i := by
  have := FenwickNodeLo_bounds i hi
  exact ⟨by omega, by omega⟩

theorem Fenwick_prefix_node_partition (a : List Int) (i : Int) (hi : 0 < i) (hil : i < Zlength a) :
    FenwickPrefixSum a i = FenwickPrefixSum a (i-FenwickLowbit i) + FenwickNodeSum a i := by
  have hb := FenwickLowbit_bounds i hi
  unfold FenwickPrefixSum FenwickNodeSum FenwickNodeLo
  rw [sublist_split 1 (i+1) (i-FenwickLowbit i+1) a (by omega) (by omega)]
  exact sum_app _ _

theorem FenwickPrefixSum_zero (a : List Int) : FenwickPrefixSum a 0 = 0 := by
  unfold FenwickPrefixSum
  rw [Zsublist_nil a 1 (0+1) (by omega)]
  rfl

theorem FenwickQueryState_initial (a : List Int) (target : Int) : FenwickQueryState a target target 0 := by
  unfold FenwickQueryState
  omega

theorem FenwickQueryState_step (a bit : List Int) (n target cursor accumulator : Int)
    (hr : FenwickRep a bit n) (hc : 0 < cursor ∧ cursor ≤ n) (hs : FenwickQueryState a target cursor accumulator) :
    FenwickQueryState a target (cursor-FenwickLowbit cursor) (accumulator+Znth cursor bit 0) := by
  have hn := hr.2.2.2 cursor (by omega)
  have hp := Fenwick_prefix_node_partition a cursor hc.1 (by have := hr.1; omega)
  unfold FenwickQueryState at *
  omega

private theorem double_bit_zero (n : Nat) : (2*n).testBit 0 = false := by simp
private theorem double_bit_succ (n i : Nat) : (2*n).testBit (i+1) = n.testBit i := by
  rw [← Nat.testBit_div_two]
  congr 1
  omega
private theorem odd_bit_zero (n : Nat) : (2*n+1).testBit 0 = true := by simp
private theorem odd_bit_succ (n i : Nat) : (2*n+1).testBit (i+1) = n.testBit i := by
  rw [← Nat.testBit_div_two]
  congr 1
  omega

private theorem lowbit_nat_odd (n : Nat) :
    (2*n+1) ^^^ ((2*n+1) &&& ((2*n+1)-1)) = 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [show 2*n+1-1 = 2*n by omega, Nat.testBit_xor, Nat.testBit_and]
  cases i with
  | zero => simp [odd_bit_zero, double_bit_zero]
  | succ i =>
    simp only [odd_bit_succ, double_bit_succ, Bool.and_self, Bool.xor_self]
    simpa using (odd_bit_succ 0 i).symm

private theorem lowbit_nat_double (n : Nat) (hn : 0 < n) :
    (2*n) ^^^ ((2*n) &&& ((2*n)-1)) = 2*(n ^^^ (n &&& (n-1))) := by
  have hp : 2*n-1 = 2*(n-1)+1 := by omega
  apply Nat.eq_of_testBit_eq
  intro i
  rw [hp, Nat.testBit_xor, Nat.testBit_and]
  cases i with
  | zero => simp [double_bit_zero]
  | succ i => simp [double_bit_succ, odd_bit_succ, Nat.testBit_xor, Nat.testBit_and]

theorem FenwickLowbit_double__add_progress_bitwise (x : Int) (hx : 0 < x) :
    FenwickLowbit (2*x) = 2*FenwickLowbit x := by
  cases x with
  | negSucc n => omega
  | ofNat n =>
    simp only [Int.ofNat_eq_coe] at hx ⊢
    have hn := lowbit_nat_double n (Int.ofNat_lt.mp hx)
    have hc := congrArg (fun x : Nat => (x : Int)) hn
    have heq : 2*(n : Int) = ((2*n : Nat) : Int) := by omega
    rw [heq, lowbit_nat, lowbit_nat]
    simpa only [Int.natCast_mul] using hc

theorem FenwickLowbit_double_plus_one__add_progress_bitwise (x : Int) (hx : 0 ≤ x) :
    FenwickLowbit (2*x+1) = 1 := by
  cases x with
  | negSucc n => omega
  | ofNat n =>
    simp only [Int.ofNat_eq_coe] at hx ⊢
    have heq : 2*(n : Int)+1 = ((2*n+1 : Nat) : Int) := by omega
    rw [heq, lowbit_nat, lowbit_nat_odd]
    rfl

private theorem lowbit_growth_nat (n : Nat) : 0 < n →
    2*FenwickLowbit (n : Int) ≤ FenwickLowbit ((n : Int)+FenwickLowbit (n : Int)) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases hodd : n % 2 = 1
    · have heq : (n : Int) = 2*(n/2 : Nat)+1 := by omega
      rw [heq, FenwickLowbit_double_plus_one__add_progress_bitwise _ (by omega)]
      rw [show 2*(n/2 : Nat)+1+1 = (2 : Int)*((n/2 : Nat)+1) by omega]
      rw [FenwickLowbit_double__add_progress_bitwise _ (by omega)]
      have hp := FenwickLowbit_positive ((n/2 : Nat)+1) (by omega)
      omega
    · have hm : 0 < n/2 := by omega
      have heq : (n : Int) = 2*(n/2 : Nat) := by omega
      have hrec := ih (n/2) (by omega) hm
      have hp := FenwickLowbit_positive (n/2 : Nat) (by omega)
      rw [heq, FenwickLowbit_double__add_progress_bitwise _ (by omega)]
      rw [show 2*(n/2 : Nat)+2*FenwickLowbit (n/2 : Nat) =
        2*((n/2 : Nat)+FenwickLowbit (n/2 : Nat)) by omega]
      rw [FenwickLowbit_double__add_progress_bitwise _ (by omega)]
      omega

theorem FenwickLowbit_successor_growth__add_progress_bitwise (x : Int) (hx : 0 < x) :
    2*FenwickLowbit x ≤ FenwickLowbit (x+FenwickLowbit x) := by
  cases x with
  | negSucc n => omega
  | ofNat n => exact lowbit_growth_nat n (Int.ofNat_lt.mp hx)

private theorem lowbit_gap_nat (n : Nat) : ∀ node : Int, 0 < n →
    ((n : Int) < node ∧ node < (n : Int)+FenwickLowbit (n : Int)) →
    FenwickLowbit node ≤ node-(n : Int) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro node hn hgap
    by_cases hodd : n % 2 = 1
    · have heq : (n : Int) = 2*(n/2 : Nat)+1 := by omega
      rw [heq, FenwickLowbit_double_plus_one__add_progress_bitwise _ (by omega)] at hgap
      omega
    · have hm : 0 < n/2 := by omega
      have heq : (n : Int) = 2*(n/2 : Nat) := by omega
      have hlow := FenwickLowbit_double__add_progress_bitwise (n/2 : Nat) (by omega)
      rw [heq, hlow] at hgap
      by_cases hnodeodd : node.toNat % 2 = 1
      · have hnode : node = 2*(node.toNat/2 : Nat)+1 := by omega
        rw [hnode, FenwickLowbit_double_plus_one__add_progress_bitwise _ (by omega)]
        omega
      · have hnode : node = 2*(node.toNat/2 : Nat) := by omega
        have hrec := ih (n/2) (by omega) (node.toNat/2 : Nat) hm (by omega)
        rw [hnode, FenwickLowbit_double__add_progress_bitwise _ (by omega)]
        omega

theorem FenwickLowbit_gap_bound__add_progress_bitwise (x node : Int)
    (hx : 0 < x) (hg : x < node ∧ node < x+FenwickLowbit x) : FenwickLowbit node ≤ node-x := by
  cases x with
  | negSucc n => omega
  | ofNat n => exact lowbit_gap_nat n node (Int.ofNat_lt.mp hx) hg

theorem Fenwick_add_successor_covers__add_progress_bitwise (cursor target : Int)
    (hc : 0 < cursor) (hcov : FenwickCovers cursor target) :
    FenwickCovers (cursor+FenwickLowbit cursor) target := by
  have hg := FenwickLowbit_successor_growth__add_progress_bitwise cursor hc
  have hp := FenwickLowbit_positive cursor hc
  unfold FenwickCovers FenwickNodeLo at *
  omega

theorem Fenwick_add_successor_gap__add_progress_bitwise (cursor node : Int)
    (hc : 0 < cursor) (hg : cursor < node ∧ node < cursor+FenwickLowbit cursor) :
    cursor < FenwickNodeLo node := by
  have hb := FenwickLowbit_gap_bound__add_progress_bitwise cursor node hc hg
  unfold FenwickNodeLo
  omega

private theorem sublist_Zlength (a : List Int) (lo hi : Int)
    (hb : 0 ≤ lo ∧ lo ≤ hi) (hh : hi ≤ Zlength a) : Zlength (sublist lo hi a) = hi-lo := by
  unfold Zlength
  rw [sublist_length lo hi a hb hh]
  exact Int.toNat_sub_of_le hb.2

private theorem sublist_replace_outside (a : List Int) (lo hi target value : Int)
    (hb : 0 ≤ lo ∧ lo ≤ hi) (hhi : hi ≤ Zlength a) (ht : 0 ≤ target ∧ target < Zlength a)
    (hout : target < lo ∨ hi ≤ target) :
    sublist lo hi (replace_Znth target value a) = sublist lo hi a := by
  have hl := Zlength_replace_Znth a target value
  apply (ListLib.list_eq_ext _ _ 0).mpr
  change (Zlength (sublist lo hi (replace_Znth target value a)) = Zlength (sublist lo hi a)) ∧
    (∀ i, (0 ≤ i ∧ i < Zlength (sublist lo hi (replace_Znth target value a))) →
      Znth i (sublist lo hi (replace_Znth target value a)) 0 = Znth i (sublist lo hi a) 0)
  constructor
  · rw [sublist_Zlength _ lo hi hb (by omega), sublist_Zlength a lo hi hb hhi]
  · intro i hindex
    have hr : 0 ≤ i ∧ i < hi-lo := by
      have hsz := sublist_Zlength (replace_Znth target value a) lo hi hb (by omega)
      change 0 ≤ i ∧ i < Zlength (sublist lo hi (replace_Znth target value a)) at hindex
      omega
    rw [Znth_sublist 0 lo i hi _ hb.1 hr, Znth_sublist 0 lo i hi a hb.1 hr]
    exact Znth_replace_Znth_Diff 0 a target (i+lo) value ht (by omega) (by omega)

theorem FenwickNodeSum_add_point__add_node_update (a : List Int) (target delta node : Int)
    (ht : 0 ≤ target ∧ target < Zlength a) (hn : 0 < node ∧ node < Zlength a) :
    (FenwickCovers node target → FenwickNodeSum (FenwickAddArray a target delta) node = FenwickNodeSum a node+delta) ∧
    (¬ FenwickCovers node target → FenwickNodeSum (FenwickAddArray a target delta) node = FenwickNodeSum a node) := by
  have hlo := FenwickNodeLo_bounds node hn.1
  have hlen := Zlength_replace_Znth a target (Znth target a 0+delta)
  unfold FenwickNodeSum FenwickAddArray
  constructor
  · intro hc
    have hcov : FenwickNodeLo node ≤ target ∧ target ≤ node := hc
    have hbefore := sublist_replace_outside a (FenwickNodeLo node) target target (Znth target a 0+delta)
      (by omega) (by omega) ht (Or.inr (by omega))
    have hafter := sublist_replace_outside a (target+1) (node+1) target (Znth target a 0+delta)
      (by omega) (by omega) ht (Or.inl (by omega))
    rw [sublist_split (FenwickNodeLo node) (node+1) target _ (by omega) (by omega),
      sublist_split target (node+1) (target+1) _ (by omega) (by omega),
      sublist_split (FenwickNodeLo node) (node+1) target a (by omega) (by omega),
      sublist_split target (node+1) (target+1) a (by omega) (by omega), hbefore, hafter,
      sublist_single 0 target (replace_Znth target (Znth target a 0+delta) a) (by omega),
      Znth_replace_Znth_Same 0 a target (Znth target a 0+delta) ht,
      sublist_single 0 target a ht]
    simp only [sum_app]
    simp only [sum, List.foldr_cons, List.foldr_nil]
    omega
  · intro hnc
    have ho : target < FenwickNodeLo node ∨ node+1 ≤ target := by
      change ¬ (FenwickNodeLo node ≤ target ∧ target ≤ node) at hnc
      omega
    rw [sublist_replace_outside a (FenwickNodeLo node) (node+1) target (Znth target a 0+delta)
      (by omega) (by omega) ht ho]

theorem Fenwick_query_step_int_safe__query_step (a bit : List Int) (n target cursor accumulator : Int)
    (hr : FenwickRep a bit n) (hsafe : FenwickIntervalsIntSafe a n)
    (hc : 0 < cursor) (hct : cursor ≤ target) (htn : target ≤ n)
    (hs : FenwickQueryState a target cursor accumulator) :
    -2147483648 ≤ accumulator+Znth cursor bit 0 ∧ accumulator+Znth cursor bit 0 ≤ 2147483647 := by
  have hd := Fenwick_query_index_decreases cursor hc
  have hl := hr.1
  have hnode := hr.2.2.2 cursor (by omega)
  have htarget : FenwickPrefixSum a target = FenwickPrefixSum a (cursor-FenwickLowbit cursor) +
      sum (sublist (cursor-FenwickLowbit cursor+1) (target+1) a) := by
    unfold FenwickPrefixSum
    rw [sublist_split 1 (target+1) (cursor-FenwickLowbit cursor+1) a (by omega) (by omega), sum_app]
  have hcursor := Fenwick_prefix_node_partition a cursor hc (by omega)
  have hsum : accumulator+Znth cursor bit 0 = sum (sublist (cursor-FenwickLowbit cursor+1) (target+1) a) := by
    unfold FenwickQueryState at hs
    omega
  rw [hsum]
  exact hsafe (cursor-FenwickLowbit cursor+1) target (by omega) htn

end SimpleC.EE.LLM_bench.Data_structures.binary_indexed_tree.binary_indexed_tree_lib
namespace SimpleC.EE.LLM_bench.Data_structures.binary_indexed_tree
export binary_indexed_tree_lib (FenwickLowbit FenwickNodeLo FenwickNodeSum FenwickPrefixSum FenwickAddArray
  FenwickRep FenwickIntervalsIntSafe FenwickCovers FenwickAddProgress FenwickQueryState)
end SimpleC.EE.LLM_bench.Data_structures.binary_indexed_tree
