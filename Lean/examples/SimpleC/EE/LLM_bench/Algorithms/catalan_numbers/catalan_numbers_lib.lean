import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import ListLib.General.Length

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
namespace SimpleC.EE.LLM_bench.Algorithms.catalan_numbers.catalan_numbers_lib
open AUXLib

def stack_run (depth : Nat) (ops : List Bool) : Option Nat :=
  match ops with
  | [] => some depth
  | true :: rest => stack_run (depth + 1) rest
  | false :: rest => match depth with
    | 0 => none
    | depth' + 1 => stack_run depth' rest

def stack_push_count : List Bool → Nat
  | [] => 0
  | true :: rest => stack_push_count rest + 1
  | false :: rest => stack_push_count rest

def all_stack_words : Nat → List (List Bool)
  | 0 => [[]]
  | len + 1 => (all_stack_words len).map (true :: ·) ++ (all_stack_words len).map (false :: ·)

def legal_stack_completion_nat (pushes depth : Nat) (ops : List Bool) : Prop :=
  ops.length = 2 * pushes + depth ∧ stack_push_count ops = pushes ∧
  stack_run depth ops = some 0

def legal_stack_completionb (pushes depth : Nat) (ops : List Bool) : Bool :=
  (ops.length == 2 * pushes + depth) && (stack_push_count ops == pushes) &&
  match stack_run depth ops with | some 0 => true | _ => false

def stack_completion_set (pushes depth : Nat) : List (List Bool) :=
  (all_stack_words (2 * pushes + depth)).filter (legal_stack_completionb pushes depth)

def LegalStackCompletion (pushes depth : Int) (ops : List Bool) : Prop :=
  0 ≤ pushes ∧ 0 ≤ depth ∧ legal_stack_completion_nat pushes.toNat depth.toNat ops

def LegalStackBehavior (pushes : Int) (ops : List Bool) : Prop := LegalStackCompletion pushes 0 ops

def StackSequenceSet (pushes : Int) : List (List Bool) := stack_completion_set pushes.toNat 0

def StackCompletionCount (pushes depth value : Int) : Prop :=
  0 ≤ pushes ∧ 0 ≤ depth ∧ value = Int.ofNat (stack_completion_set pushes.toNat depth.toNat).length

def StackSequenceCount (pushes value : Int) : Prop :=
  0 ≤ pushes ∧ value = Int.ofNat (StackSequenceSet pushes).length ∧
  ∀ ops, ops ∈ StackSequenceSet pushes ↔ LegalStackBehavior pushes ops

def StackCellIndex (n row col : Int) : Int := row * (n + 1) + col

def StackCellBound (row col value : Int) : Prop :=
  0 ≤ row ∧ 0 ≤ col ∧ 0 ≤ value ∧ value ≤ Z.pow 2 (2 * row + col)

def StackCellCorrect (n row col value : Int) : Prop :=
  row + col ≤ n → StackCompletionCount row col value

def StackTablePrefix (n : Int) (table : List Int) (written : Int) : Prop :=
  0 ≤ n ∧ (0 ≤ written ∧ Zlength table = written) ∧
  ∀ row col, (0 ≤ row ∧ row ≤ n) → (0 ≤ col ∧ col ≤ n) →
    (0 ≤ StackCellIndex n row col ∧ StackCellIndex n row col < written) →
    StackCellBound row col (Znth (StackCellIndex n row col) table 0) ∧
    StackCellCorrect n row col (Znth (StackCellIndex n row col) table 0)

def StackRowsDone (n : Int) (table : List Int) (rows_done : Int) : Prop :=
  0 ≤ rows_done ∧ StackTablePrefix n table (rows_done * (n + 1))

def StackRowProgress (n : Int) (table : List Int) (row col : Int) : Prop :=
  0 ≤ row ∧ (0 ≤ col ∧ col ≤ n + 1) ∧ StackTablePrefix n table (row * (n + 1) + col)

theorem all_stack_words_spec (len : Nat) (ops : List Bool) :
    ops ∈ all_stack_words len ↔ ops.length = len := by
  induction len generalizing ops with
  | zero => simp [all_stack_words]
  | succ len ih =>
    cases ops with
    | nil => simp [all_stack_words]
    | cons op rest =>
      cases op <;> simp [all_stack_words, ih]

theorem legal_stack_completionb_spec (pushes depth : Nat) (ops : List Bool) :
    legal_stack_completionb pushes depth ops = true ↔ legal_stack_completion_nat pushes depth ops := by
  unfold legal_stack_completionb legal_stack_completion_nat
  cases hrun : stack_run depth ops with
  | none => simp
  | some result => cases result <;> simp [and_assoc]

theorem stack_completion_set_spec (pushes depth : Nat) (ops : List Bool) :
    ops ∈ stack_completion_set pushes depth ↔ legal_stack_completion_nat pushes depth ops := by
  simp only [stack_completion_set, List.mem_filter, all_stack_words_spec, legal_stack_completionb_spec]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

theorem StackSequenceSet_spec (pushes : Int) (ops : List Bool) (hp : 0 ≤ pushes) :
    ops ∈ StackSequenceSet pushes ↔ LegalStackBehavior pushes ops := by
  simp only [StackSequenceSet, LegalStackBehavior, LegalStackCompletion, stack_completion_set_spec,
    Int.toNat_zero, hp, Int.le_refl, true_and]

theorem StackCompletionCount_zero_to_StackSequenceCount (pushes value : Int)
    (hc : StackCompletionCount pushes 0 value) : StackSequenceCount pushes value :=
  ⟨hc.1, hc.2.2, fun ops => StackSequenceSet_spec pushes ops hc.1⟩

theorem bounded_0_7_cases__cell_dp (x : Int) (hx : 0 ≤ x ∧ x ≤ 7) :
    x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7 := by omega

theorem bounded_1_7_cases__cell_dp (x : Int) (hx : 1 ≤ x ∧ x ≤ 7) :
    x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7 := by omega

private theorem cell_index_injective (n r c row col : Int) (hn : 0 ≤ n)
    (hc : 0 ≤ c ∧ c ≤ n) (hcol : 0 ≤ col ∧ col ≤ n)
    (he : StackCellIndex n r c = StackCellIndex n row col) : r = row ∧ c = col := by
  unfold StackCellIndex at he
  have hr : r = row := by
    by_cases hlt : r < row
    · have hm := Int.mul_le_mul_of_nonneg_right (show r + 1 ≤ row by omega) (show 0 ≤ n + 1 by omega)
      simp only [Int.add_mul, Int.one_mul] at hm
      omega
    · by_cases hgt : row < r
      · have hm := Int.mul_le_mul_of_nonneg_right (show row + 1 ≤ r by omega) (show 0 ≤ n + 1 by omega)
        simp only [Int.add_mul, Int.one_mul] at hm
        omega
      · omega
  exact ⟨hr, by subst r; omega⟩

theorem StackTablePrefix_snoc__cell_dp (n : Int) (table : List Int) (written row col v : Int)
    (hp : StackTablePrefix n table written) (hl : Zlength table = written)
    (hr : 0 ≤ row ∧ row ≤ n) (hc : 0 ≤ col ∧ col ≤ n)
    (hi : StackCellIndex n row col = written) (hb : StackCellBound row col v)
    (hcorrect : StackCellCorrect n row col v) : StackTablePrefix n (table ++ [v]) (written + 1) := by
  obtain ⟨hn, hw, hcells⟩ := hp
  refine ⟨hn, ⟨by omega, ?_⟩, ?_⟩
  · simp only [Zlength_app, Zlength_cons, Zlength_nil, hl]; omega
  · intro r c hrr hcc hidx
    by_cases hold : StackCellIndex n r c < written
    · have hlookup : Znth (StackCellIndex n r c) (table ++ [v]) 0 =
          Znth (StackCellIndex n r c) table 0 :=
        ListLib.app_Znth1 0 table [v] (StackCellIndex n r c) (by
          change 0 ≤ StackCellIndex n r c ∧ StackCellIndex n r c < Zlength table
          omega)
      rw [hlookup]
      exact hcells r c hrr hcc ⟨hidx.1, hold⟩
    · have he : StackCellIndex n r c = StackCellIndex n row col := by omega
      obtain ⟨her, hec⟩ := cell_index_injective n r c row col hn hcc hc he
      subst r
      subst c
      rw [app_Znth2 0 table [v] (StackCellIndex n row col) (by omega), hl, hi]
      simpa [Znth] using And.intro hb hcorrect

theorem StackRowProgress_snoc__cell_dp (n : Int) (table : List Int) (row col v : Int)
    (hp : StackRowProgress n table row col) (hl : Zlength table = row * (n + 1) + col)
    (hr : 0 ≤ row ∧ row ≤ n) (hc : 0 ≤ col ∧ col ≤ n)
    (hb : StackCellBound row col v) (hcorrect : StackCellCorrect n row col v) :
    StackRowProgress n (table ++ [v]) row (col + 1) := by
  refine ⟨hp.1, ⟨by omega, by omega⟩, ?_⟩
  have h := StackTablePrefix_snoc__cell_dp n table (row * (n + 1) + col) row col v hp.2.2 hl hr hc rfl hb hcorrect
  simpa only [Int.add_assoc] using h

private theorem pow2_eq_nat (x : Int) (hx : 0 ≤ x) : Z.pow 2 x = Int.ofNat (2 ^ x.toNat) := by
  cases x with
  | ofNat x => simp [Z.pow, Int.natCast_pow]
  | negSucc x => omega

private theorem pow2_mono (x y : Int) (hx : 0 ≤ x) (hxy : x ≤ y) : Z.pow 2 x ≤ Z.pow 2 y := by
  rw [pow2_eq_nat x hx, pow2_eq_nat y (by omega)]
  exact Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide) (by omega))

private theorem pow2_succ (x : Int) (hx : 0 ≤ x) : Z.pow 2 (x + 1) = Z.pow 2 x + Z.pow 2 x := by
  rw [pow2_eq_nat (x + 1) (by omega), pow2_eq_nat x hx]
  have he : (x + 1).toNat = x.toNat + 1 := by omega
  rw [he, Nat.pow_succ]
  simp only [Int.ofNat_eq_coe, Int.natCast_mul]
  omega

theorem StackCellBound_zero_row__cell_dp (col : Int) (hc : 0 ≤ col ∧ col ≤ 7) : StackCellBound 0 col 1 := by
  refine ⟨by omega, hc.1, by omega, ?_⟩
  have h := pow2_mono 0 col (by omega) hc.1
  simpa [Z.pow] using h

theorem StackCellBound_copy_boundary__cell_dp (row value : Int) (hr : 1 ≤ row ∧ row ≤ 7)
    (hb : StackCellBound (row - 1) 1 value) : StackCellBound row 0 value := by
  refine ⟨by omega, by omega, hb.2.2.1, ?_⟩
  exact Int.le_trans hb.2.2.2 (pow2_mono _ _ (by omega) (by omega))

theorem StackCellBound_add_step__cell_dp (row col a b : Int)
    (hr : 1 ≤ row ∧ row ≤ 7) (hc : 1 ≤ col ∧ col ≤ 7)
    (ha : StackCellBound (row - 1) (col + 1) a) (hb : StackCellBound row (col - 1) b) :
    StackCellBound row col (a + b) := by
  have he : 2 * (row - 1) + (col + 1) = 2 * row + (col - 1) := by omega
  have hpow := pow2_succ (2 * row + (col - 1)) (by omega)
  have he2 : 2 * row + (col - 1) + 1 = 2 * row + col := by omega
  rw [he2] at hpow
  have hau := ha.2.2.2
  rw [he] at hau
  exact ⟨by omega, by omega, by have := ha.2.2.1; have := hb.2.2.1; omega,
    by have := hb.2.2.2; omega⟩

theorem StackCellBound_normalize_row_end__cell_dp (row col value : Int)
    (hr : 1 ≤ row ∧ row ≤ 7) (hc : 1 ≤ col ∧ col ≤ 7) (hb : StackCellBound row 0 value) :
    StackCellBound (row - 1) (col + 1) value := by
  exact ⟨by omega, by omega, hb.2.2.1,
    Int.le_trans hb.2.2.2 (pow2_mono _ _ (by omega) (by omega))⟩

theorem StackCellBound_int_range__cell_dp (row col value : Int)
    (hr : 0 ≤ row ∧ row ≤ 7) (hc : 0 ≤ col ∧ col ≤ 7) (hb : StackCellBound row col value) :
    -2147483648 ≤ value ∧ value ≤ 2147483647 := by
  have hm := pow2_mono (2 * row + col) 21 (by omega) (by omega)
  have h21 : Z.pow 2 21 = 2097152 := by decide
  rw [h21] at hm
  have := hb.2.2.1
  have := hb.2.2.2
  omega

private theorem completionb_true (pushes depth : Nat) (ops : List Bool) :
    legal_stack_completionb (pushes + 1) depth (true :: ops) =
      legal_stack_completionb pushes (depth + 1) ops := by
  apply Bool.eq_iff_iff.mpr
  rw [legal_stack_completionb_spec, legal_stack_completionb_spec]
  simp only [legal_stack_completion_nat, List.length_cons, stack_push_count, stack_run]
  constructor <;> rintro ⟨hl, hp, hr⟩ <;> exact ⟨by omega, by omega, hr⟩

private theorem completionb_false (pushes depth : Nat) (ops : List Bool) :
    legal_stack_completionb pushes (depth + 1) (false :: ops) =
      legal_stack_completionb pushes depth ops := by
  apply Bool.eq_iff_iff.mpr
  rw [legal_stack_completionb_spec, legal_stack_completionb_spec]
  simp only [legal_stack_completion_nat, List.length_cons, stack_push_count, stack_run]
  constructor <;> rintro ⟨hl, hp, hr⟩ <;> exact ⟨by omega, by omega, hr⟩

private theorem completionb_false_zero (pushes : Nat) (ops : List Bool) :
    legal_stack_completionb pushes 0 (false :: ops) = false := by
  simp [legal_stack_completionb, stack_run]

private theorem completionb_zero_true (depth : Nat) (ops : List Bool) :
    legal_stack_completionb 0 depth (true :: ops) = false := by
  simp [legal_stack_completionb, stack_push_count]

private theorem filtered_words_succ (len pushes depth : Nat) :
    ((all_stack_words (len + 1)).filter (legal_stack_completionb pushes depth)).length =
    ((all_stack_words len).filter (fun ops => legal_stack_completionb pushes depth (true :: ops))).length +
    ((all_stack_words len).filter (fun ops => legal_stack_completionb pushes depth (false :: ops))).length := by
  simp only [all_stack_words, List.filter_append, List.filter_map, List.length_append, List.length_map,
    Function.comp_def]

private theorem filter_false_words (l : List (List Bool)) : l.filter (fun _ => false) = [] :=
  List.filter_eq_nil_iff.mpr (by simp)

private theorem completion_count_zero (depth : Nat) : (stack_completion_set 0 depth).length = 1 := by
  unfold stack_completion_set
  simp only [Nat.mul_zero, Nat.zero_add]
  induction depth with
  | zero => rfl
  | succ depth ih =>
    rw [filtered_words_succ]
    simpa [completionb_zero_true, completionb_false, filter_false_words, List.length_nil,
      Nat.zero_add] using ih

private theorem completion_count_push (pushes : Nat) :
    (stack_completion_set (pushes + 1) 0).length = (stack_completion_set pushes 1).length := by
  unfold stack_completion_set
  rw [show 2 * (pushes + 1) + 0 = (2 * pushes + 1) + 1 by omega, filtered_words_succ]
  simp [completionb_true, completionb_false_zero, List.filter_eq_nil_iff, List.length_nil, Nat.add_zero]

private theorem completion_count_step (pushes depth : Nat) :
    (stack_completion_set (pushes + 1) (depth + 1)).length =
    (stack_completion_set pushes (depth + 2)).length + (stack_completion_set (pushes + 1) depth).length := by
  unfold stack_completion_set
  rw [show 2 * (pushes + 1) + (depth + 1) = (2 * pushes + (depth + 2)) + 1 by omega,
    filtered_words_succ]
  simp only [completionb_true, completionb_false]
  rw [show 2 * (pushes + 1) + depth = 2 * pushes + (depth + 2) by omega]

theorem StackCompletionCount_zero_row__cell_dp (depth : Int) (hd : 0 ≤ depth ∧ depth ≤ 7) :
    StackCompletionCount 0 depth 1 := by
  refine ⟨by omega, hd.1, ?_⟩
  simp only [Int.toNat_zero, completion_count_zero]
  rfl

theorem StackCompletionCount_push_boundary__cell_dp (pushes value : Int)
    (hp : 1 ≤ pushes ∧ pushes ≤ 7) (hc : StackCompletionCount (pushes - 1) 1 value) :
    StackCompletionCount pushes 0 value := by
  refine ⟨by omega, by omega, ?_⟩
  have he : pushes.toNat = (pushes - 1).toNat + 1 := by omega
  rw [he, Int.toNat_zero, completion_count_push]
  exact hc.2.2

theorem StackCompletionCount_step__cell_dp (pushes depth a b : Int)
    (hp : 1 ≤ pushes) (hd : 1 ≤ depth) (hs : pushes + depth ≤ 7)
    (ha : StackCompletionCount (pushes - 1) (depth + 1) a)
    (hb : StackCompletionCount pushes (depth - 1) b) : StackCompletionCount pushes depth (a + b) := by
  refine ⟨by omega, by omega, ?_⟩
  have hep : pushes.toNat = (pushes - 1).toNat + 1 := by omega
  have hed : depth.toNat = (depth - 1).toNat + 1 := by omega
  rw [hep, hed, completion_count_step]
  have hes : (depth - 1).toNat + 2 = (depth + 1).toNat := by omega
  rw [hes, ← hep]
  have haa := ha.2.2
  have hbb := hb.2.2
  simp only [Int.ofNat_eq_coe, Int.natCast_add] at *
  omega

private theorem snoc_at_length (table : List Int) (v idx : Int) (hi : idx = Zlength table) :
    Znth idx (table ++ [v]) 0 = v := by
  rw [app_Znth2 0 table [v] idx (by omega), hi]
  simp [Znth]

theorem StackRowProgress_zero_row_extend__cell_dp (n : Int) (table : List Int) (col : Int)
    (hn : 0 ≤ n ∧ n ≤ 7) (hc : 0 ≤ col ∧ col ≤ n) (hp : StackRowProgress n table 0 col) :
    let table' := table ++ [1]
    StackRowProgress n table' 0 (col + 1) ∧
    StackCellCorrect n 0 col (Znth (StackCellIndex n 0 col) table' 0) ∧
    StackCellBound 0 col (Znth (StackCellIndex n 0 col) table' 0) := by
  dsimp only
  have hl : Zlength table = col := by simpa using hp.2.2.2.1.2
  have hb := StackCellBound_zero_row__cell_dp col (by omega)
  have hcorrect : StackCellCorrect n 0 col 1 := fun _ => StackCompletionCount_zero_row__cell_dp col (by omega)
  refine ⟨StackRowProgress_snoc__cell_dp n table 0 col 1 hp (by simpa using hl)
    (by omega) hc hb hcorrect, ?_⟩
  rw [snoc_at_length table 1 (StackCellIndex n 0 col) (by simpa [StackCellIndex] using hl.symm)]
  exact ⟨hcorrect, hb⟩

theorem StackRowProgress_copy_boundary_extend__cell_dp (n : Int) (table : List Int) (row : Int)
    (hn : 0 ≤ n ∧ n ≤ 7) (hr : 1 ≤ row ∧ row ≤ n) (hp : StackRowProgress n table row 0) :
    let v := Znth (StackCellIndex n (row - 1) 1) table 0
    let table' := table ++ [v]
    StackRowProgress n table' row 1 ∧
    StackCellCorrect n row 0 (Znth (StackCellIndex n row 0) table' 0) ∧
    StackCellBound row 0 (Znth (StackCellIndex n row 0) table' 0) := by
  dsimp only
  let v := Znth (StackCellIndex n (row - 1) 1) table 0
  have hl := hp.2.2.2.1.2
  have hm := Int.mul_nonneg (show 0 ≤ row - 1 by omega) (show 0 ≤ n + 1 by omega)
  obtain ⟨hsrcb, hsrcc⟩ := hp.2.2.2.2 (row - 1) 1 (by omega) (by omega) (by
    unfold StackCellIndex
    simp only [Int.sub_mul, Int.one_mul] at hm ⊢
    omega)
  have hb : StackCellBound row 0 v := StackCellBound_copy_boundary__cell_dp row v (by omega) hsrcb
  have hcorrect : StackCellCorrect n row 0 v := by
    intro ht
    exact StackCompletionCount_push_boundary__cell_dp row v (by omega) (hsrcc (by omega))
  refine ⟨StackRowProgress_snoc__cell_dp n table row 0 v hp hl (by omega) (by omega) hb hcorrect, ?_⟩
  change StackCellCorrect n row 0 (Znth (StackCellIndex n row 0) (table ++ [v]) 0) ∧ _
  rw [snoc_at_length table v (StackCellIndex n row 0) hl.symm]
  exact ⟨hcorrect, hb⟩

theorem StackRowProgress_add_step_extend__cell_dp (n : Int) (table : List Int) (row col : Int)
    (hn : 0 ≤ n ∧ n ≤ 7) (hr : 1 ≤ row ∧ row ≤ n) (hc : 1 ≤ col ∧ col ≤ n)
    (hp : StackRowProgress n table row col) :
    let a := Znth (StackCellIndex n (row - 1) (col + 1)) table 0
    let b := Znth (StackCellIndex n row (col - 1)) table 0
    let v := a + b
    let table' := table ++ [v]
    StackRowProgress n table' row (col + 1) ∧
    StackCellCorrect n row col (Znth (StackCellIndex n row col) table' 0) ∧
    StackCellBound row col (Znth (StackCellIndex n row col) table' 0) := by
  dsimp only
  let a := Znth (StackCellIndex n (row - 1) (col + 1)) table 0
  let b := Znth (StackCellIndex n row (col - 1)) table 0
  let v := a + b
  have hl := hp.2.2.2.1.2
  have hm := Int.mul_nonneg (show 0 ≤ row - 1 by omega) (show 0 ≤ n + 1 by omega)
  have hmrow := Int.mul_nonneg (show 0 ≤ row by omega) (show 0 ≤ n + 1 by omega)
  have hasrc : 0 ≤ StackCellIndex n (row - 1) (col + 1) ∧
      StackCellIndex n (row - 1) (col + 1) < row * (n + 1) + col := by
    unfold StackCellIndex
    simp only [Int.sub_mul, Int.one_mul] at hm ⊢
    omega
  obtain ⟨hbb, hbc⟩ := hp.2.2.2.2 row (col - 1) (by omega) (by omega) (by
    unfold StackCellIndex
    omega)
  have hab : StackCellBound (row - 1) (col + 1) a := by
    by_cases hlt : col < n
    · exact (hp.2.2.2.2 (row - 1) (col + 1) (by omega) (by omega) hasrc).1
    · have he : col = n := by omega
      have hzero := (hp.2.2.2.2 row 0 (by omega) (by omega) (by unfold StackCellIndex; omega)).1
      have hie : StackCellIndex n row 0 = StackCellIndex n (row - 1) (col + 1) := by
        unfold StackCellIndex
        simp only [Int.sub_mul, Int.one_mul]
        omega
      rw [hie] at hzero
      exact StackCellBound_normalize_row_end__cell_dp row col a (by omega) (by omega) hzero
  have hb : StackCellBound row col v := StackCellBound_add_step__cell_dp row col a b (by omega) (by omega) hab hbb
  have hcorrect : StackCellCorrect n row col v := by
    intro ht
    have hac := (hp.2.2.2.2 (row - 1) (col + 1) (by omega) (by omega) hasrc).2
    exact StackCompletionCount_step__cell_dp row col a b hr.1 hc.1 (by omega)
      (hac (by omega)) (hbc (by omega))
  refine ⟨StackRowProgress_snoc__cell_dp n table row col v hp hl (by omega) (by omega) hb hcorrect, ?_⟩
  change StackCellCorrect n row col (Znth (StackCellIndex n row col) (table ++ [v]) 0) ∧ _
  rw [snoc_at_length table v (StackCellIndex n row col) hl.symm]
  exact ⟨hcorrect, hb⟩

end SimpleC.EE.LLM_bench.Algorithms.catalan_numbers.catalan_numbers_lib
namespace SimpleC.EE.LLM_bench.Algorithms.catalan_numbers
export catalan_numbers_lib (StackSequenceCount StackCellBound StackCellCorrect StackRowsDone StackRowProgress StackTablePrefix)
abbrev Zpower := Z.pow
end SimpleC.EE.LLM_bench.Algorithms.catalan_numbers
