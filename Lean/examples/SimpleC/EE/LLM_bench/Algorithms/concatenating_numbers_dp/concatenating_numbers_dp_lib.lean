import SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib
import ListLib.General.Length
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.Nat.Log2
import Init.Data.List.Nat.Range

set_option maxHeartbeats 6000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false

namespace Z
-- Reached Coq ZArith/BinIntDef.v log2: zero on nonpositive inputs.
def log2 (x : Int) : Int := Int.ofNat x.toNat.log2
end Z

namespace Z
-- Reached Z.eqb, preserving its public Boolean equality interface.
def eqb (a b : Int) : Bool := decide (a = b)
end Z


namespace SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers_dp.concatenating_numbers_dp_lib
open AUXLib

def number_item : Type := List Int × Int

def item_digits (x : number_item) : List Int :=
  sublist 0 (Prod.snd x) (Prod.fst x)

def item_at (rows : List (List Int)) (lengths : List Int) (i : Int) :
  number_item :=
  (Znth i rows [], Znth i lengths 0)

def digit_lex_ge (xs ys : List Int) : Prop :=
  Zlength xs = Zlength ys ∧
  (xs = ys ∨
   ∃ k, (0 ≤ k ∧ k < Zlength xs) ∧
     (∀ j, (0 ≤ j ∧ j < k) → Znth j xs 0 = Znth j ys 0) ∧
     Znth k ys 0 < Znth k xs 0)

def item_before_or_equal
    (rows : List (List Int)) (lengths : List Int) (i j : Int) : Prop :=
  digit_lex_ge
    (item_digits (item_at rows lengths i) ++
     item_digits (item_at rows lengths j))
    (item_digits (item_at rows lengths j) ++
     item_digits (item_at rows lengths i))

def RowsWellFormed
    (rows : List (List Int)) (lengths : List Int)
    (count width : Int) : Prop :=
  Zlength rows = count ∧
  Zlength lengths = count ∧
  (∀ i, (0 ≤ i ∧ i < count) →
     Zlength (Znth i rows []) = width ∧ (1 ≤ Znth i lengths 0 ∧ Znth i lengths 0 ≤ width) ∧ (1 ≤ Znth 0 (Znth i rows []) 0 ∧ Znth 0 (Znth i rows []) 0 ≤ 9) ∧
     (∀ j, (0 ≤ j ∧ j < Znth i lengths 0) → (0 ≤ Znth j (Znth i rows []) 0 ∧ Znth j (Znth i rows []) 0 ≤ 9) ))

def FlatRows
    (flat : List Int) (rows : List (List Int)) (count width : Int) : Prop :=
  Zlength flat = count * width ∧
  Zlength rows = count ∧
  ∀ i, (0 ≤ i ∧ i < count) →
    Znth i rows [] = sublist (i * width) ((i + 1) * width) flat

def ConcatLeftDigit
    (rows : List (List Int)) (lens : List Int) (i j position : Int) : Int :=
  Znth position
    (item_digits (item_at rows lens i) ++
     item_digits (item_at rows lens j)) 0

def ConcatRightDigit
    (rows : List (List Int)) (lens : List Int) (i j position : Int) : Int :=
  Znth position
    (item_digits (item_at rows lens j) ++
     item_digits (item_at rows lens i)) 0

def ConcatComparePrefix
    (rows : List (List Int)) (lens : List Int)
    (i j position : Int) : Prop :=
  let lhs := item_digits (item_at rows lens i) ++
             item_digits (item_at rows lens j);
  let rhs := item_digits (item_at rows lens j) ++
             item_digits (item_at rows lens i);
  (0 ≤ position ∧ position ≤ Zlength lhs) ∧
  Zlength lhs = Zlength rhs ∧
  ∀ k, (0 ≤ k ∧ k < position) → Znth k lhs 0 = Znth k rhs 0

def concatenate_indices (rows : List (List Int)) (lengths indices : List Int) : List Int :=
  (indices.map (fun i => item_digits (item_at rows lengths i))).flatten

def all_indices (count : Int) : List Int := (List.range count.toNat).map Int.ofNat

def ConcatCompareLoopState (rows : List (List Int)) (lens : List Int) (left right left_length right_length position : Int) : Prop :=
  left_length=Znth left lens 0 ∧ right_length=Znth right lens 0 ∧ ConcatComparePrefix rows lens left right position

def ConcatCompareSignOutcome (rows : List (List Int)) (lens : List Int) (i j comparison : Int) : Prop :=
  let lhs := item_digits (item_at rows lens i)++item_digits (item_at rows lens j)
  let rhs := item_digits (item_at rows lens j)++item_digits (item_at rows lens i)
  (comparison=0 ∧ lhs=rhs) ∨
  (comparison=1 ∧ ∃ k, (0≤k ∧ k<Zlength lhs) ∧ Zlength lhs=Zlength rhs ∧
    (∀ p, (0≤p ∧ p<k) → Znth p lhs 0=Znth p rhs 0) ∧ Znth k rhs 0<Znth k lhs 0) ∨
  (comparison= -1 ∧ ∃ k, (0≤k ∧ k<Zlength lhs) ∧ Zlength lhs=Zlength rhs ∧
    (∀ p, (0≤p ∧ p<k) → Znth p lhs 0=Znth p rhs 0) ∧ Znth k lhs 0<Znth k rhs 0)

def BestIndexForMask (rows : List (List Int)) (lens : List Int) (count mask index : Int) : Prop :=
  (0≤index ∧ index<count) ∧ Z.testbit mask index=true ∧ ∀ other, (0≤other ∧ other<count) →
    Z.testbit mask other=true → item_before_or_equal rows lens index other

def DPTablePrefix (rows : List (List Int)) (lens : List Int) (count computed : Int) (choices : List Int) : Prop :=
  (1≤computed ∧ computed≤Z.shiftl 1 count) ∧ Zlength choices=computed ∧ Znth 0 choices 0= -1 ∧
    ∀ mask, (1≤mask ∧ mask<computed) → BestIndexForMask rows lens count mask (Znth mask choices 0)

def BitScanState (mask count bit bit_value : Int) : Prop :=
  (1≤mask ∧ mask<Z.shiftl 1 count) ∧ (0≤bit ∧ bit≤count) ∧ bit_value=Z.shiftl 1 bit ∧
    ∀ lower, (0≤lower ∧ lower<bit) → Z.testbit mask lower=false

def SelectedBitState (mask count bit bit_value rest : Int) : Prop :=
  BitScanState mask count bit bit_value ∧ Z.land mask bit_value≠0 ∧ (0≤bit ∧ bit<count) ∧
    Z.testbit mask bit=true ∧ rest=Z.lxor mask bit_value ∧ (0≤rest ∧ rest<mask)

def MaskIndexes (count mask : Int) (indices : List Int) : Prop :=
  ∀ index, index∈indices ↔ (0≤index ∧ index<count) ∧ Z.testbit mask index=true

def LargestConcatenation (rows : List (List Int)) (lens output : List Int) : Prop :=
  ∃ order, Permutation (all_indices (Zlength rows)) order ∧ output=concatenate_indices rows lens order ∧
    ∀ alternative, Permutation (all_indices (Zlength rows)) alternative → digit_lex_ge output (concatenate_indices rows lens alternative)

def GreedyOutputPrefix (rows : List (List Int)) (lens : List Int) (count mask : Int) (output : List Int) : Prop :=
  ∃ done todo, Permutation (all_indices count) (done++todo) ∧ MaskIndexes count mask todo ∧
    output=concatenate_indices rows lens done ∧ LargestConcatenation rows lens (concatenate_indices rows lens (done++todo))

def AppendRowPrefix (rows : List (List Int)) (lens prior : List Int) (index position : Int) (current : List Int) : Prop :=
  current=prior++sublist 0 position (item_digits (item_at rows lens index))

-- Coq Lists/List.v reached Fixpoint. Both type parameters are implicit in Coq.
def list_power {A B : Type} : List A → List B → List (List (A×B))
  | [], _ => [[]]
  | x::xs, values => (list_power xs values).flatMap (fun f => values.map (fun y => (x,y)::f))

private abbrev decimalFold (xs : List Int) (acc : Int) : Int := xs.foldl (fun value digit=>10*value+digit) acc

theorem ConcatComparePrefix_zero__compare_bounds :
  ∀ rows lens i j,
    ConcatComparePrefix rows lens i j (0 : Int) := by
  exact @SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib.ConcatComparePrefix_zero__partition_and_compare_init

theorem flat_rows_cell_lookup__compare_digits :
  ∀ flat rows count width i j,
    FlatRows flat rows count width → ((0 : Int) ≤ i ∧ i < count) → ((0 : Int) ≤ j ∧ j < width) →
    Znth (i * width + j) flat (0 : Int) = Znth j (Znth i rows []) (0 : Int) := by
  exact @SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib.FlatRows_Znth__compare_left_digit

theorem concat_pair_Zlength__compare_semantics :
  ∀ rows lens count width i j,
    RowsWellFormed rows lens count width → ((0 : Int) ≤ i ∧ i < count) → ((0 : Int) ≤ j ∧ j < count) →
    Zlength
      (item_digits (item_at rows lens i) ++
       item_digits (item_at rows lens j)) =
    Znth i lens (0 : Int) + Znth j lens (0 : Int) := by
  exact @SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib.concat_item_digits_Zlength__compare_outcome

theorem item_digits_Zlength__compare_semantics :
  ∀ rows lens count width i,
    RowsWellFormed rows lens count width → ((0 : Int) ≤ i ∧ i < count) →
    Zlength (item_digits (item_at rows lens i)) = Znth i lens (0 : Int) := by
  exact @SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib.RowsWellFormed_item_digits_length__largest_concatenation_final

theorem item_digits_length__output_initialization :
  ∀ rows lens count width i,
    RowsWellFormed rows lens count width → ((0 : Int) ≤ i ∧ i < count) →
    Zlength (item_digits (item_at rows lens i)) = Znth i lens (0 : Int) := by
  exact @SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib.RowsWellFormed_item_digits_length__largest_concatenation_final

theorem item_digits_length_for_output__output_finalization :
  ∀ rows lens count width i,
    RowsWellFormed rows lens count width → ((0 : Int) ≤ i ∧ i < count) →
    Zlength (item_digits (item_at rows lens i)) = Znth i lens (0 : Int) := by
  exact @SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib.RowsWellFormed_item_digits_length__largest_concatenation_final

theorem item_digits_length__output_finalization :
  ∀ rows lens count width i,
    RowsWellFormed rows lens count width → ((0 : Int) ≤ i ∧ i < count) →
    Zlength (item_digits (item_at rows lens i)) = Znth i lens (0 : Int) := by
  exact @SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib.RowsWellFormed_item_digits_length__largest_concatenation_final

theorem sum_permutation__output_initialization :
  ∀ xs ys, Permutation xs ys → sum xs = sum ys := by
  exact @SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib.sum_permutation__scan_advance

theorem sum_permutation__output_finalization :
  ∀ xs ys, Permutation xs ys → sum xs = sum ys := by
  exact @SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib.sum_permutation__scan_advance

theorem item_before_or_equal_transitive__dp_table_transition :
  ∀ rows lens count width i j k,
    RowsWellFormed rows lens count width → ((0 : Int) ≤ i ∧ i < count) → ((0 : Int) ≤ j ∧ j < count) → ((0 : Int) ≤ k ∧ k < count) →
    item_before_or_equal rows lens i j →
    item_before_or_equal rows lens j k →
    item_before_or_equal rows lens i k := by
  exact @SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib.item_before_or_equal_trans__quicksort_range_composition

theorem item_before_or_equal_refl__dp_table_transition :
  ∀ rows lens i,
    item_before_or_equal rows lens i i := by
  exact @SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib.item_before_or_equal_refl__quicksort_range_composition

theorem digit_lex_ge_append_right__output_finalization :
  ∀ xs ys suffix,
    digit_lex_ge xs ys →
    digit_lex_ge (xs ++ suffix) (ys ++ suffix) := by
  exact @SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib.digit_lex_ge_suffix__largest_concatenation_final

theorem digit_lex_ge_append_left__output_finalization :
  ∀ «prefix» xs ys,
    digit_lex_ge xs ys →
    digit_lex_ge («prefix» ++ xs) («prefix» ++ ys) := by
  exact @SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib.digit_lex_ge_prefix__largest_concatenation_final

theorem digit_lex_ge_refl__dp_table_transition :
  ∀ xs, digit_lex_ge xs xs := by
  exact @SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib.digit_lex_ge_refl__quicksort_range_composition

theorem decimal_fold_acc__dp_table_transition :
  ∀ xs acc,
    xs.foldl (fun value digit => 10*value+digit) acc =
    acc * Z.pow (10 : Int) (Zlength xs) +
    xs.foldl (fun value digit => 10*value+digit) (0 : Int) := by
  exact @SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib.decimal_fold_acc__quicksort_range_composition

theorem decimal_fold_app__dp_table_transition :
  ∀ xs ys,
    (xs ++ ys).foldl (fun value digit => 10*value+digit) (0 : Int) =
    xs.foldl (fun value digit => 10*value+digit) (0 : Int) *
      Z.pow (10 : Int) (Zlength ys) +
    ys.foldl (fun value digit => 10*value+digit) (0 : Int) := by
  exact @SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib.decimal_fold_app__quicksort_range_composition

theorem decimal_fold_bounds__dp_table_transition :
  ∀ xs,
    Forall (fun digit => ((0 : Int) ≤ digit ∧ digit < (10 : Int)) ) xs → ((0 : Int) ≤ xs.foldl (fun value digit => 10*value+digit) (0 : Int) ∧ xs.foldl (fun value digit => 10*value+digit) (0 : Int) < Z.pow (10 : Int) (Zlength xs)) := by
  exact @SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib.decimal_fold_bounds__quicksort_range_composition

theorem digit_lex_ge_cons_iff__dp_table_transition :
  ∀ x y xs ys,
    Zlength xs = Zlength ys →
    (digit_lex_ge (x :: xs) (y :: ys) ↔
     y < x ∨ (x = y ∧ digit_lex_ge xs ys)) := by
  exact @SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib.digit_lex_ge_cons_iff__quicksort_range_composition

theorem digit_lex_ge_decimal_iff__dp_table_transition :
  ∀ xs ys,
    Zlength xs = Zlength ys →
    Forall (fun digit => ((0 : Int) ≤ digit ∧ digit < (10 : Int)) ) xs →
    Forall (fun digit => ((0 : Int) ≤ digit ∧ digit < (10 : Int)) ) ys →
    (digit_lex_ge xs ys ↔
     xs.foldl (fun value digit => 10*value+digit) (0 : Int) ≥
     ys.foldl (fun value digit => 10*value+digit) (0 : Int)) := by
  exact @SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib.digit_lex_ge_decimal_iff__quicksort_range_composition

theorem concat_digit_order_cross_iff__dp_table_transition :
  ∀ xs ys,
    Forall (fun digit => ((0 : Int) ≤ digit ∧ digit < (10 : Int)) ) xs →
    Forall (fun digit => ((0 : Int) ≤ digit ∧ digit < (10 : Int)) ) ys →
    (digit_lex_ge (xs ++ ys) (ys ++ xs) ↔
     xs.foldl (fun value digit => 10*value+digit) (0 : Int) *
       (Z.pow (10 : Int) (Zlength ys) - (1 : Int)) ≥
     ys.foldl (fun value digit => 10*value+digit) (0 : Int) *
       (Z.pow (10 : Int) (Zlength xs) - (1 : Int))) := by
  exact @SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib.concat_digit_order_cross_iff__quicksort_range_composition

theorem concat_digit_order_trans__dp_table_transition :
  ∀ xs ys zs,
    Forall (fun digit => ((0 : Int) ≤ digit ∧ digit < (10 : Int)) ) xs →
    Forall (fun digit => ((0 : Int) ≤ digit ∧ digit < (10 : Int)) ) ys →
    Forall (fun digit => ((0 : Int) ≤ digit ∧ digit < (10 : Int)) ) zs →
    (0 : Int) < Zlength xs →
    (0 : Int) < Zlength ys →
    (0 : Int) < Zlength zs →
    digit_lex_ge (xs ++ ys) (ys ++ xs) →
    digit_lex_ge (ys ++ zs) (zs ++ ys) →
    digit_lex_ge (xs ++ zs) (zs ++ xs) := by
  exact @SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib.concat_digit_order_trans__quicksort_range_composition

theorem Forall_sublist_by_Znth__dp_table_transition :
  ∀ (P : Int → Prop) (l : List Int) lo hi, ((0 : Int) ≤ lo ∧ lo ≤ hi) →
    hi ≤ Zlength l →
    (∀ k, (lo ≤ k ∧ k < hi) → P (Znth k l (0 : Int))) →
    Forall P (sublist lo hi l) := by
  exact @SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib.Forall_sublist_by_Znth__quicksort_range_composition

theorem item_digits_properties__dp_table_transition :
  ∀ rows lens count width i,
    RowsWellFormed rows lens count width → ((0 : Int) ≤ i ∧ i < count) →
    (0 : Int) < Zlength (item_digits (item_at rows lens i)) ∧
    Forall (fun digit => ((0 : Int) ≤ digit ∧ digit < (10 : Int)) )
      (item_digits (item_at rows lens i)) := by
  exact @SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib.item_digits_properties__quicksort_range_composition

theorem digit_lex_ge_refl__output_initialization :
  ∀ xs, digit_lex_ge xs xs := by
  exact @SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib.digit_lex_ge_refl__largest_concatenation_final

theorem digit_lex_ge_cons_strict__output_initialization :
  ∀ x y xs ys,
    Zlength xs = Zlength ys →
    y < x →
    digit_lex_ge (x :: xs) (y :: ys) := by
  exact @SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib.digit_lex_ge_cons_strict__largest_concatenation_final

theorem digit_lex_ge_cons_same__output_initialization :
  ∀ x xs ys,
    digit_lex_ge xs ys →
    digit_lex_ge (x :: xs) (x :: ys) := by
  exact @SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib.digit_lex_ge_cons_same__largest_concatenation_final

theorem digit_lex_ge_cons_inv__output_initialization :
  ∀ x y xs ys,
    digit_lex_ge (x :: xs) (y :: ys) →
    Zlength xs = Zlength ys ∧
    (y < x ∨ (x = y ∧ digit_lex_ge xs ys)) := by
  exact @SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib.digit_lex_ge_cons_inv__largest_concatenation_final

theorem digit_lex_ge_trans__output_initialization :
  ∀ xs ys zs,
    digit_lex_ge xs ys →
    digit_lex_ge ys zs →
    digit_lex_ge xs zs := by
  exact @SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib.digit_lex_ge_trans__largest_concatenation_final

theorem digit_lex_ge_refl__output_finalization :
  ∀ xs, digit_lex_ge xs xs := by
  exact @SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib.digit_lex_ge_refl__largest_concatenation_final

theorem digit_lex_ge_trans__output_finalization :
  ∀ xs ys zs,
    digit_lex_ge xs ys →
    digit_lex_ge ys zs →
    digit_lex_ge xs zs := by
  exact @SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib.digit_lex_ge_trans__largest_concatenation_final

theorem concat_digit_lookup__compare_digits (flat : List Int) (rows : List (List Int)) (lens : List Int)
    (count width left right left_length right_length position : Int)
    (hw : RowsWellFormed rows lens count width) (hf : FlatRows flat rows count width)
    (hl : 0≤left ∧ left<count) (hr : 0≤right ∧ right<count)
    (hlenl : left_length=Znth left lens 0) (hlenr : right_length=Znth right lens 0) :
    ((0≤position ∧ position<left_length) → Znth (left*width+position) flat 0=ConcatLeftDigit rows lens left right position) ∧
    ((left_length≤position ∧ position<left_length+right_length) → Znth (right*width+position-left_length) flat 0=ConcatLeftDigit rows lens left right position) ∧
    ((0≤position ∧ position<right_length) → Znth (right*width+position) flat 0=ConcatRightDigit rows lens left right position) ∧
    ((right_length≤position ∧ position<right_length+left_length) → Znth (left*width+position-right_length) flat 0=ConcatRightDigit rows lens left right position) := by
  have hwl := hw.2.2 left hl
  have hwr := hw.2.2 right hr
  refine ⟨?_,?_,?_,?_⟩
  · intro hp
    change _=SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib.ConcatLeftDigit rows lens left right position
    rw [SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib.ConcatLeftDigit_first__compare_left_digit rows lens count width left right position hw hl (by omega)]
    exact flat_rows_cell_lookup__compare_digits flat rows count width left position hf hl (by omega)
  · intro hp
    change _=SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib.ConcatLeftDigit rows lens left right position
    rw [SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib.ConcatLeftDigit_second__compare_left_digit rows lens count width left right position hw hl hr (by omega)]
    have he : right*width+position-left_length=right*width+(position-Znth left lens 0) := by omega
    rw [he]
    exact flat_rows_cell_lookup__compare_digits flat rows count width right _ hf hr (by omega)
  · intro hp
    exact SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib.ConcatRightDigit_first_flat__compare_right_digit flat rows lens count width left right position hf hw hr (by omega)
  · intro hp
    have he : left*width+position-right_length=left*width+(position-Znth right lens 0) := by omega
    rw [he]
    exact SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib.ConcatRightDigit_second_flat__compare_right_digit flat rows lens count width left right position hf hw hl hr (by omega) (by omega)

theorem concat_compare_prefix_step__compare_semantics (rows : List (List Int)) (lens : List Int)
    (count width left right left_length right_length position : Int)
    (hw : RowsWellFormed rows lens count width) (hl : 0≤left ∧ left<count) (hr : 0≤right ∧ right<count)
    (hp : ConcatCompareLoopState rows lens left right left_length right_length position)
    (hlt : position<left_length+right_length)
    (he : ConcatLeftDigit rows lens left right position=ConcatRightDigit rows lens left right position) :
    ConcatCompareLoopState rows lens left right left_length right_length (position+1) := by
  refine ⟨hp.1,hp.2.1,?_⟩
  apply SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib.ConcatComparePrefix_step__compare_outcome rows lens left right position hp.2.2 he
  change position<Zlength (item_digits (item_at rows lens left)++item_digits (item_at rows lens right))
  rw [concat_pair_Zlength__compare_semantics rows lens count width left right hw hl hr]
  have := hp.1; have := hp.2.1; omega

theorem concat_compare_outcome_at_difference__compare_semantics (rows : List (List Int)) (lens : List Int)
    (count width left right left_length right_length position comparison : Int)
    (hw : RowsWellFormed rows lens count width) (hl : 0≤left ∧ left<count) (hr : 0≤right ∧ right<count)
    (hp : ConcatCompareLoopState rows lens left right left_length right_length position)
    (hlt : position<left_length+right_length)
    (he : (comparison= -1 ∧ ConcatLeftDigit rows lens left right position<ConcatRightDigit rows lens left right position) ∨
      (comparison=1 ∧ ConcatRightDigit rows lens left right position<ConcatLeftDigit rows lens left right position)) :
    ConcatCompareSignOutcome rows lens left right comparison := by
  have hlen := concat_pair_Zlength__compare_semantics rows lens count width left right hw hl hr
  have hpos : position<Zlength (item_digits (item_at rows lens left)++item_digits (item_at rows lens right)) := by
    have := hp.1; have := hp.2.1; omega
  rcases he with he|he
  · exact Or.inr (Or.inr ⟨he.1,position,⟨hp.2.2.1.1,hpos⟩,hp.2.2.2.1,hp.2.2.2.2,he.2⟩)
  · exact Or.inr (Or.inl ⟨he.1,position,⟨hp.2.2.1.1,hpos⟩,hp.2.2.2.1,hp.2.2.2.2,he.2⟩)

theorem concat_compare_outcome_at_end__compare_semantics (rows : List (List Int)) (lens : List Int)
    (count width left right left_length right_length position : Int)
    (hw : RowsWellFormed rows lens count width) (hl : 0≤left ∧ left<count) (hr : 0≤right ∧ right<count)
    (hp : ConcatCompareLoopState rows lens left right left_length right_length position)
    (hge : position≥left_length+right_length) (hle : position≤left_length+right_length) :
    ConcatCompareSignOutcome rows lens left right 0 := by
  have hout := SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib.ConcatCompareOutcome_zero__compare_outcome rows lens left right position hp.2.2 (by
    change Zlength (item_digits (item_at rows lens left)++item_digits (item_at rows lens right))≤position
    rw [concat_pair_Zlength__compare_semantics rows lens count width left right hw hl hr]
    have := hp.1;have := hp.2.1;omega)
  rcases hout with hz|⟨k,hk,hlen,hpre,hne,he⟩
  · exact Or.inl hz
  · omega

theorem dp_table_prefix_singleton__dp_initialization (rows : List (List Int)) (lens : List Int) (count : Int)
    (hs : 1≤Z.shiftl 1 count) : DPTablePrefix rows lens count 1 [-1] :=
  ⟨by omega,rfl,rfl,by intros;omega⟩

theorem dp_table_prefix_extend__dp_table_transition (rows : List (List Int)) (lens : List Int) (count mask : Int) (choices : List Int) (index : Int)
    (hp : DPTablePrefix rows lens count mask choices) (hm : mask<Z.shiftl 1 count)
    (hi : BestIndexForMask rows lens count mask index) : DPTablePrefix rows lens count (mask+1) (choices++[index]) := by
  have hread (j : Int) (hj : 0≤j ∧ j<mask) : Znth j (choices++[index]) 0=Znth j choices 0 :=
    ListLib.app_Znth1 0 choices [index] j (by change 0≤j ∧ j<Zlength choices;rw[hp.2.1];exact hj)
  refine ⟨by have := hp.1;omega,by simp only[Zlength_app,Zlength_cons,Zlength_nil,hp.2.1];omega,?_,?_⟩
  · rw [hread 0 (by have := hp.1;omega)];exact hp.2.2.1
  · intro m hr
    by_cases he : m=mask
    · rw [he,app_Znth2 0 choices [index] mask (by rw[hp.2.1] <;> omega),hp.2.1,Int.sub_self]
      exact hi
    · rw [hread m (by omega)]
      exact hp.2.2.2 m (by omega)

theorem compare_outcome_nonpositive__dp_table_transition (rows : List (List Int)) (lens : List Int) (bit previous comparison : Int)
    (hc : comparison≤0) (ho : ConcatCompareSignOutcome rows lens bit previous comparison) :
    item_before_or_equal rows lens previous bit := by
  rcases ho with ⟨_,he⟩|⟨hc1,k,hk,hlen,hpre,hgt⟩|⟨_,k,hk,hlen,hpre,hlt⟩
  · exact ⟨congrArg Zlength he.symm,Or.inl he.symm⟩
  · omega
  · exact ⟨hlen.symm,Or.inr ⟨k,by omega,fun j hj => (hpre j hj).symm,hlt⟩⟩

theorem compare_outcome_positive__dp_table_transition (rows : List (List Int)) (lens : List Int) (bit previous comparison : Int)
    (hc : comparison>0) (ho : ConcatCompareSignOutcome rows lens bit previous comparison) :
    item_before_or_equal rows lens bit previous := by
  rcases ho with ⟨hc0,_⟩|⟨_,k,hk,hlen,hpre,hgt⟩|⟨hcn,_⟩
  · omega
  · exact ⟨hlen,Or.inr ⟨k,hk,hpre,hgt⟩⟩
  · omega

theorem digit_lex_ge_total__output_initialization (xs ys : List Int) (hlen : Zlength xs=Zlength ys) :
    digit_lex_ge xs ys ∨ digit_lex_ge ys xs := by
  induction xs generalizing ys with
  | nil =>
    have : ys=[] := by simp only [Zlength,List.length_nil,Int.ofNat_eq_coe] at hlen; exact List.length_eq_zero_iff.mp (by omega)
    subst ys
    exact Or.inl (digit_lex_ge_refl__output_initialization [])
  | cons x xs ih =>
    cases ys with
    | nil => have := Zlength_nonneg xs; simp only [Zlength_cons,Zlength_nil] at hlen;omega
    | cons y ys =>
      have ht : Zlength xs=Zlength ys := by simp only [Zlength_cons] at hlen;omega
      by_cases he : x=y
      · rcases ih ys ht with h|h
        · exact Or.inl (by simpa only [he] using digit_lex_ge_cons_same__output_initialization y xs ys h)
        · exact Or.inr (by simpa only [he] using digit_lex_ge_cons_same__output_initialization y ys xs h)
      · by_cases hlt : y<x
        · exact Or.inl (digit_lex_ge_cons_strict__output_initialization x y xs ys ht hlt)
        · exact Or.inr (digit_lex_ge_cons_strict__output_initialization y x ys xs ht.symm (by omega))

theorem digit_lex_ge_antisym__output_finalization (xs ys : List Int)
    (hxy : digit_lex_ge xs ys) (hyx : digit_lex_ge ys xs) : xs=ys := by
  induction xs generalizing ys with
  | nil =>
    have hlen := hxy.1
    simp only [Zlength,List.length_nil,Int.ofNat_eq_coe] at hlen
    symm
    exact List.length_eq_zero_iff.mp (by omega)
  | cons x xs ih =>
    cases ys with
    | nil => have := hxy.1; have := Zlength_nonneg xs; simp only [Zlength_cons,Zlength_nil] at *;omega
    | cons y ys =>
      have hx := (digit_lex_ge_cons_inv__output_initialization x y xs ys hxy).2
      have hy := (digit_lex_ge_cons_inv__output_initialization y x ys xs hyx).2
      rcases hx with hx|⟨he,hx⟩ <;> rcases hy with hy|⟨he2,hy⟩
      · omega
      · omega
      · omega
      · rw [he,ih ys hx hy]

theorem finite_list_maximum_on__output_initialization (A : Type) (R : A→A→Prop) (candidates : List A)
    (hne : candidates≠[]) (htotal : ∀ x y, x∈candidates → y∈candidates → R x y ∨ R y x)
    (htrans : ∀ x y z, x∈candidates → y∈candidates → z∈candidates → R x y → R y z → R x z) :
    ∃ best, best∈candidates ∧ ∀ candidate, candidate∈candidates → R best candidate := by
  induction candidates with
  | nil => contradiction
  | cons x xs ih =>
    have hxx : R x x := by exact (htotal x x (by simp) (by simp)).elim id id
    by_cases hnil : xs=[]
    · subst xs
      refine ⟨x,by simp,?_⟩
      intro c hc
      have he : c=x := by simpa using hc
      simpa only [he] using hxx
    · obtain ⟨best,hbin,hbest⟩ := ih hnil (fun a b ha hb => htotal a b (by simp[ha]) (by simp[hb]))
        (fun a b c ha hb hc => htrans a b c (by simp[ha]) (by simp[hb]) (by simp[hc]))
      rcases htotal x best (by simp) (by simp[hbin]) with hxb|hbx
      · refine ⟨x,by simp,?_⟩
        intro c hc
        rcases List.mem_cons.mp hc with he|hm
        · simpa only [he] using hxx
        · exact htrans x best c (by simp) (by simp[hbin]) (by simp[hm]) hxb (hbest c hm)
      · refine ⟨best,by simp[hbin],?_⟩
        intro c hc
        rcases List.mem_cons.mp hc with he|hm
        · simpa only [he] using hbx
        · exact hbest c hm

theorem list_power_snd_complete__output_initialization (A B : Type) (positions : List A) (values output : List B)
    (hlen : positions.length=output.length) (hmem : ∀ x, x∈output → x∈values) :
    output∈(list_power positions values).map (fun assignment => assignment.map Prod.snd) := by
  induction positions generalizing output with
  | nil =>
    have : output=[] := List.length_eq_zero_iff.mp hlen.symm
    subst output
    simp [list_power]
  | cons p ps ih =>
    cases output with
    | nil => simp at hlen
    | cons x xs =>
      have ht : ps.length=xs.length := by simp only [List.length_cons] at hlen;omega
      have hxs := ih xs ht (fun y hy => hmem y (by simp[hy]))
      obtain ⟨assignment,ha,he⟩ := List.mem_map.mp hxs
      apply List.mem_map.mpr
      refine ⟨(p,x)::assignment,?_,by simp [he]⟩
      apply List.mem_flatMap.mpr
      exact ⟨assignment,ha,List.mem_map.mpr ⟨x,hmem x (by simp),rfl⟩⟩

private noncomputable abbrev candidate_test (base candidate : List Int) : Bool :=
  @ite Bool (Permutation base candidate) (Classical.propDecidable _) true false

theorem permutation_candidate_in__output_initialization (base order : List Int) (hp : Permutation base order) :
    order∈((list_power (List.range' 0 base.length) base).map (fun assignment => assignment.map Prod.snd)).filter (fun candidate => @ite Bool (Permutation base candidate) (Classical.propDecidable _) true false) := by
  apply List.mem_filter.mpr
  refine ⟨list_power_snd_complete__output_initialization Nat Int _ base order ?_ ?_,?_⟩
  · simp only [List.length_range']; exact hp.length_eq
  · intro x hx; exact hp.symm.mem_iff.mp hx
  · simp only [candidate_test,if_pos hp]

theorem permutation_candidate_sound__output_initialization (base order : List Int)
    (hin : order∈((list_power (List.range' 0 base.length) base).map (fun assignment => assignment.map Prod.snd)).filter (fun candidate => @ite Bool (Permutation base candidate) (Classical.propDecidable _) true false)) :
    Permutation base order := by
  have h := (List.mem_filter.mp hin).2
  split at h
  · assumption
  · contradiction

theorem concatenate_indices_length__output_finalization (rows : List (List Int)) (lens indices : List Int) :
    Zlength (concatenate_indices rows lens indices)=sum (indices.map (fun index => Zlength (item_digits (item_at rows lens index)))) := by
  induction indices with
  | nil => rfl
  | cons x xs ih =>
    change Zlength (item_digits (item_at rows lens x)++concatenate_indices rows lens xs)=_
    rw [Zlength_app,ih]
    simp only [List.map_cons,sum,List.foldr_cons]

theorem concatenate_indices_length_permutation__output_initialization (rows : List (List Int)) (lens first second : List Int)
    (hp : Permutation first second) : Zlength (concatenate_indices rows lens first)=Zlength (concatenate_indices rows lens second) := by
  rw [concatenate_indices_length__output_finalization,concatenate_indices_length__output_finalization]
  exact sum_permutation__output_finalization _ _ (hp.map _)

theorem largest_concatenation_exists__output_initialization (rows : List (List Int)) (lens : List Int) :
    ∃ order, Permutation (all_indices (Zlength rows)) order ∧ ∀ alternative,
      Permutation (all_indices (Zlength rows)) alternative →
      digit_lex_ge (concatenate_indices rows lens order) (concatenate_indices rows lens alternative) := by
  let base := all_indices (Zlength rows)
  let candidates := ((list_power (List.range' 0 base.length) base).map (fun assignment => assignment.map Prod.snd)).filter (fun candidate => @ite Bool (Permutation base candidate) (Classical.propDecidable _) true false)
  have hin : base∈candidates := permutation_candidate_in__output_initialization base base (List.Perm.refl _)
  have sound (order : List Int) (h : order∈candidates) : Permutation base order := permutation_candidate_sound__output_initialization base order h
  obtain ⟨best,hbest,hmax⟩ := finite_list_maximum_on__output_initialization (List Int)
    (fun x y => digit_lex_ge (concatenate_indices rows lens x) (concatenate_indices rows lens y)) candidates
    (by intro he;rw[he] at hin;contradiction)
    (fun x y hx hy => digit_lex_ge_total__output_initialization _ _
      (concatenate_indices_length_permutation__output_initialization rows lens x y ((sound x hx).symm.trans (sound y hy))))
    (fun x y z _ _ _ => digit_lex_ge_trans__output_initialization _ _ _)
  exact ⟨best,sound best hbest,fun alternative hp => hmax alternative (permutation_candidate_in__output_initialization base alternative hp)⟩

theorem all_indices_spec__output_initialization (count index : Int) (hc : 0≤count) :
    index∈all_indices count ↔ 0≤index ∧ index<count := by
  simp only [all_indices,List.mem_map]
  constructor
  · rintro ⟨k,hk,he⟩
    have := List.mem_range.mp hk
    simp only [Int.ofNat_eq_coe] at he
    omega
  · intro hi
    refine ⟨index.toNat,List.mem_range.mpr (by omega),?_⟩
    simp only [Int.ofNat_eq_coe]
    omega

theorem all_indices_bounds__output_finalization (count index : Int) (hc : 0≤count) (hi : index∈all_indices count) : 0≤index ∧ index<count :=
  (all_indices_spec__output_initialization count index hc).mp hi

theorem map_lens_all_indices__output_initialization (lens : List Int) :
    (all_indices (Zlength lens)).map (fun index => Znth index lens 0)=lens := by
  simp only [all_indices,Zlength,Int.toNat_ofNat,List.map_map]
  apply List.ext_getElem (by simp)
  intro i hi1 hi2
  simp only [List.getElem_map,List.getElem_range,Function.comp_apply,Int.ofNat_eq_coe,Znth,Int.toNat_natCast,
    List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi2,Option.getD_some]

theorem all_indices_lookup_lens__output_finalization (lens : List Int) :
    (all_indices (Zlength lens)).map (fun index => Znth index lens 0)=lens := map_lens_all_indices__output_initialization lens

theorem concatenate_indices_length__output_initialization (rows : List (List Int)) (lens : List Int) (count width : Int) (indices : List Int)
    (hw : RowsWellFormed rows lens count width) (hr : ∀ index, index∈indices → 0≤index ∧ index<count) :
    Zlength (concatenate_indices rows lens indices)=sum (indices.map (fun index => Znth index lens 0)) := by
  rw [concatenate_indices_length__output_finalization]
  congr 1
  apply List.map_congr_left
  intro index hi
  exact item_digits_length__output_initialization rows lens count width index hw (hr index hi)

theorem concatenate_indices_permutation_length__output_finalization (rows : List (List Int)) (lens : List Int)
    (count width : Int) (order : List Int) (hw : RowsWellFormed rows lens count width) (hp : Permutation (all_indices count) order) :
    Zlength (concatenate_indices rows lens order)=sum lens := by
  have hn : 0≤count := by have := Zlength_nonneg rows; have := hw.1; omega
  rw [concatenate_indices_length__output_initialization rows lens count width order hw (fun index hi =>
    all_indices_bounds__output_finalization count index hn (hp.mem_iff.mpr hi))]
  have hm := sum_permutation__output_finalization _ _ (hp.map (fun index => Znth index lens 0))
  rw [←hw.2.1,map_lens_all_indices__output_initialization] at hm
  exact hm.symm

theorem largest_concatenation_length__output_finalization (rows : List (List Int)) (lens : List Int)
    (count width : Int) (output : List Int) (hw : RowsWellFormed rows lens count width) (hl : LargestConcatenation rows lens output) :
    Zlength output=sum lens := by
  obtain ⟨order,hp,he,_⟩ := hl
  rw [he]
  apply concatenate_indices_permutation_length__output_finalization rows lens count width order hw
  simpa only [hw.1] using hp

theorem sum_nonnegative__output_initialization (values : List Int) (hn : ∀ value, value∈values → 0≤value) : 0≤sum values := by
  induction values with
  | nil => exact Int.le_refl _
  | cons x xs ih =>
    have hx := hn x (by simp)
    have ht := ih (fun value hv => hn value (by simp[hv]))
    change 0≤x+sum xs
    omega

theorem sum_member_le__output_initialization (values : List Int) (value : Int) (hv : value∈values)
    (hn : ∀ x, x∈values → 0≤x) : value≤sum values := by
  induction values with
  | nil => contradiction
  | cons x xs ih =>
    have hx := hn x (by simp)
    have htail (y : Int) (hy : y∈xs) : 0≤y := hn y (by simp[hy])
    have ht := sum_nonnegative__output_initialization xs htail
    change value≤x+sum xs
    rcases List.mem_cons.mp hv with he|hm
    · omega
    · have := ih hm htail;omega

theorem concatenate_indices_app__output_finalization (rows : List (List Int)) (lens left right : List Int) :
    concatenate_indices rows lens (left++right)=concatenate_indices rows lens left++concatenate_indices rows lens right := by
  simp [concatenate_indices,List.map_append,List.flatten_append]

theorem concatenate_indices_cons__output_finalization (rows : List (List Int)) (lens : List Int) (index : Int) (rest : List Int) :
    concatenate_indices rows lens (index::rest)=item_digits (item_at rows lens index)++concatenate_indices rows lens rest := rfl

theorem concatenate_indices_singleton__output_finalization (rows : List (List Int)) (lens : List Int) (index : Int) :
    concatenate_indices rows lens [index]=item_digits (item_at rows lens index) := by simp [concatenate_indices]

theorem row_output_capacity__output_row_copy (result_length : Int) (lens : List Int) (first position : Int)
    (hp : 0≤position) (hlt : position<Znth first lens 0)
    (hcap : result_length+(Znth first lens 0-position)≤sum lens) : result_length<sum lens := by omega

theorem greedy_output_remaining_length__output_initialization (rows : List (List Int)) (lens : List Int)
    (count width mask : Int) (output : List Int) (index : Int)
    (hw : RowsWellFormed rows lens count width) (hg : GreedyOutputPrefix rows lens count mask output)
    (hi : 0≤index ∧ index<count) (hbit : Z.testbit mask index=true) : Zlength output+Znth index lens 0≤sum lens := by
  obtain ⟨done,todo,hp,hm,he,hl⟩ := hg
  have hn : 0≤count := by have := hw.1;have := Zlength_nonneg rows;omega
  have htvalid (idx : Int) (hidx : idx∈todo) : 0≤idx ∧ idx<count := (hm idx).mp hidx |>.1
  have hlen := concatenate_indices_permutation_length__output_finalization rows lens count width (done++todo) hw hp
  rw [concatenate_indices_app__output_finalization,Zlength_app,
    concatenate_indices_length__output_initialization rows lens count width todo hw htvalid] at hlen
  have hmember : Znth index lens 0∈todo.map (fun idx => Znth idx lens 0) := List.mem_map.mpr ⟨index,(hm index).mpr ⟨hi,hbit⟩,rfl⟩
  have hle := sum_member_le__output_initialization _ _ hmember (by
    intro x hx
    obtain ⟨idx,hm,he⟩ := List.mem_map.mp hx
    have := (hw.2.2 idx (htvalid idx hm)).2.1
    omega)
  rw [he]
  omega

theorem append_row_prefix_step__output_row_copy (flat : List Int) (rows : List (List Int)) (lens : List Int)
    (count width : Int) (prior output : List Int) (index position : Int)
    (hw : RowsWellFormed rows lens count width) (hf : FlatRows flat rows count width)
    (hi : 0≤index ∧ index<count) (hp : 0≤position ∧ position<Znth index lens 0)
    (ha : AppendRowPrefix rows lens prior index position output) :
    AppendRowPrefix rows lens prior index (position+1) (output++[Znth (index*width+position) flat 0]) := by
  have hrow := hw.2.2 index hi
  have hlen := item_digits_length__output_finalization rows lens count width index hw hi
  have hlookup : Znth position (item_digits (item_at rows lens index)) 0=Znth (index*width+position) flat 0 := by
    rw [flat_rows_cell_lookup__compare_digits flat rows count width index position hf hi (by omega)]
    change Znth position (sublist 0 (Znth index lens 0) (Znth index rows [])) 0=Znth position (Znth index rows []) 0
    simpa only [Int.add_zero] using Znth_sublist 0 0 position (Znth index lens 0) (Znth index rows []) (by omega) (by omega)
  unfold AppendRowPrefix at ha ⊢
  rw [SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib.sublist_snoc__output_inner_loop 0 _ position (by omega),←List.append_assoc,←ha,hlookup]

theorem all_indices_nodup__output_finalization (count : Int) : (all_indices count).Nodup := by
  apply List.Pairwise.map Int.ofNat (fun a b hab he => hab (Int.ofNat.inj he)) (List.nodup_range)

theorem greedy_output_empty_mask__output_finalization (rows : List (List Int)) (lens : List Int)
    (count width : Int) (output : List Int) (hw : RowsWellFormed rows lens count width)
    (hg : GreedyOutputPrefix rows lens count 0 output) : LargestConcatenation rows lens output ∧ Zlength output=sum lens := by
  obtain ⟨done,todo,hp,hm,he,hl⟩ := hg
  have hnil : todo=[] := by
    cases todo with
    | nil => rfl
    | cons idx rest =>
      have h := ((hm idx).mp (by simp)).2
      cases idx <;> simp [Z.testbit] at h
  subst todo
  simp only [List.append_nil] at hp hl
  refine ⟨by rw[he];exact hl,?_⟩
  exact largest_concatenation_length__output_finalization rows lens count width output hw (by rw[he];exact hl)

theorem concatenate_move_best_front_ge__output_finalization (rows : List (List Int)) (lens : List Int)
    (first : Int) (before after : List Int)
    (hb : ∀ index, index∈before → item_before_or_equal rows lens first index) :
    digit_lex_ge (concatenate_indices rows lens (first::(before++after)))
      (concatenate_indices rows lens (before++first::after)) := by
  have hmove := SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib.item_moves_after_list__largest_concatenation_final (item_at rows lens first)
    (before.map (item_at rows lens)) (by
      intro y hy
      obtain ⟨idx,hidx,he⟩ := List.mem_map.mp hy
      rw [←he]
      exact hb idx hidx)
  have he : SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib.concatenate_items (before.map (item_at rows lens))=concatenate_indices rows lens before := by
    simp only [SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib.concatenate_items,concatenate_indices,List.map_map]
    rfl
  change digit_lex_ge (item_digits (item_at rows lens first)++SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib.concatenate_items (before.map (item_at rows lens)))
    (SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers.concatenating_numbers_lib.concatenate_items (before.map (item_at rows lens))++item_digits (item_at rows lens first)) at hmove
  rw [he] at hmove
  have h := digit_lex_ge_append_right__output_finalization _ _ (concatenate_indices rows lens after) hmove
  simpa only [concatenate_indices_cons__output_finalization,concatenate_indices_app__output_finalization,List.append_assoc] using h


private theorem dp_bits_pow (n : Int) (hn : 0 ≤ n) : Z.pow 2 n = Int.ofNat (2^n.toNat) := by
  cases n with
  | ofNat n => simp [Z.pow]
  | negSucc n => ((try simp only [Int.ofNat_eq_coe] at *); omega)

private theorem dp_bits_shift (n : Int) (hn : 0 ≤ n) : Z.shiftl 1 n = Int.ofNat (2^n.toNat) := by
  cases n with
  | ofNat n => simp [Z.shiftl, Int.shiftLeft_eq']
  | negSucc n => ((try simp only [Int.ofNat_eq_coe] at *); omega)

private theorem dp_bits_shift_positive_nonneg (n : Int) (hn : 0 < Z.shiftl 1 n) : 0 ≤ n := by
  cases n with
  | ofNat n => ((try simp only [Int.ofNat_eq_coe] at *); omega)
  | negSucc n =>
    have hp : 1 < (2^(n+1) : Nat) := by have := Nat.two_pow_pos n; rw [Nat.pow_succ]; ((try simp only [Int.ofNat_eq_coe] at *); omega)
    have he : Z.shiftl 1 (Int.negSucc n) = 0 := by
      change Int.ofNat (1 >>> (n+1)) = 0
      rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hp]
      rfl
    rw [he] at hn
    ((try simp only [Int.ofNat_eq_coe] at *); omega)

private theorem dp_bits_test_nonneg (x n : Int) (hx : 0 ≤ x) (hn : 0 ≤ n) :
    Z.testbit x n = Nat.testBit x.toNat n.toNat := by
  cases x <;> cases n <;> first | rfl | ((try simp only [Int.ofNat_eq_coe] at *); omega)

private theorem dp_bits_test_neg (x n : Int) (hn : n < 0) : Z.testbit x n = false := by
  cases n with
  | ofNat n => ((try simp only [Int.ofNat_eq_coe] at *); omega)
  | negSucc n => rfl

private theorem dp_bits_test_zero (n : Int) : Z.testbit 0 n = false := by
  cases n <;> simp [Z.testbit]

private theorem dp_bits_set_lt (mask count index : Int) (hm : 0 ≤ mask ∧ mask < Z.shiftl 1 count)
    (hn : 0 ≤ index) (hs : Z.testbit mask index = true) : index < count := by
  have hc := dp_bits_shift_positive_nonneg count (by ((try simp only [Int.ofNat_eq_coe] at *); omega))
  rw [dp_bits_shift count hc] at hm
  rw [dp_bits_test_nonneg mask index hm.1 hn] at hs
  have hb := Nat.ge_two_pow_of_testBit hs
  by_cases hi : index < count
  · exact hi
  · have hp : (2^count.toNat : Nat) ≤ 2^index.toNat := Nat.pow_le_pow_right (by decide) (by ((try simp only [Int.ofNat_eq_coe] at *); omega))
    ((try simp only [Int.ofNat_eq_coe] at *); omega)

private theorem dp_bits_scan_lt (mask count bit value : Int) (h : BitScanState mask count bit value) : bit < count := by
  have hm : 0 ≤ mask := by have := h.1.1; ((try simp only [Int.ofNat_eq_coe] at *); omega)
  have hne : mask.toNat ≠ 0 := by have := h.1.1; ((try simp only [Int.ofNat_eq_coe] at *); omega)
  obtain ⟨idx, hs⟩ := Nat.exists_testBit_of_ne_zero hne
  have hz : Z.testbit mask (Int.ofNat idx) = true := by
    rw [dp_bits_test_nonneg _ _ hm (by ((try simp only [Int.ofNat_eq_coe] at *); omega))]
    exact hs
  have hi := dp_bits_set_lt mask count (Int.ofNat idx) ⟨hm,h.1.2⟩ (by ((try simp only [Int.ofNat_eq_coe] at *); omega)) hz
  have hb : bit ≤ Int.ofNat idx := by
    by_cases hb : bit ≤ Int.ofNat idx
    · exact hb
    · have hf := h.2.2.2 (Int.ofNat idx) (by ((try simp only [Int.ofNat_eq_coe] at *); omega))
      rw [hz] at hf
      contradiction
  ((try simp only [Int.ofNat_eq_coe] at *); omega)

private theorem dp_bits_xor_nonneg (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ Z.lxor a b := by
  cases a <;> cases b <;> first | (simp only [Z.lxor]; ((try simp only [Int.ofNat_eq_coe] at *); omega)) | ((try simp only [Int.ofNat_eq_coe] at *); omega)

private theorem dp_bits_le_of_test (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ i, 0 ≤ i → Z.testbit a i = true → Z.testbit b i = true) : a ≤ b := by
  have hn : a.toNat ≤ b.toNat := by
    apply Nat.le_of_testBit
    intro i hi
    have ht := h i (by ((try simp only [Int.ofNat_eq_coe] at *); omega))
    rw [dp_bits_test_nonneg a i ha (by omega), dp_bits_test_nonneg b i hb (by omega)] at ht
    simp only [Int.toNat_natCast] at ht
    exact ht hi
  ((try simp only [Int.ofNat_eq_coe] at *); omega)

theorem signed_last_nbits_double_power__bit_scan (bit_value state_count count : Int)
    (hp : 1 ≤ bit_value) (hb : bit_value ≤ state_count) (hs : state_count = Z.shiftl 1 count) (hc : count ≤ 20) :
    -Z.pow 2 (32-1) ≤ bit_value*Z.pow 2 1 ∧ bit_value*Z.pow 2 1 < Z.pow 2 (32-1) := by
  change -2147483648 ≤ bit_value*2 ∧ bit_value*2 < 2147483648
  have hc0 := dp_bits_shift_positive_nonneg count (by ((try simp only [Int.ofNat_eq_coe] at *); omega))
  rw [dp_bits_shift count hc0] at hs
  have hn : (2^count.toNat : Nat) ≤ 2^20 := Nat.pow_le_pow_right (by decide) (by ((try simp only [Int.ofNat_eq_coe] at *); omega))
  change (2^count.toNat : Nat) ≤ 1048576 at hn
  ((try simp only [Int.ofNat_eq_coe] at *); omega)

theorem testbit_shiftl_one__bit_scan (bit n : Int) (hb : 0 ≤ bit) (hn : 0 ≤ n) :
    Z.testbit (Z.shiftl 1 bit) n = Z.eqb n bit := by
  rw [dp_bits_shift bit hb]
  rw [dp_bits_test_nonneg (Int.ofNat (2^bit.toNat)) n (Int.natCast_nonneg _) hn]
  change Nat.testBit (2^bit.toNat) n.toNat = decide (n = bit)
  rw [Nat.testBit_two_pow]
  have he : (bit.toNat = n.toNat) = (n = bit) := propext (by omega)
  simp only [he]

theorem bit_scan_advance__bit_scan (mask count bit bit_value : Int)
    (h : BitScanState mask count bit bit_value) (hland : Z.land mask bit_value = 0) :
    bit < count ∧ Z.testbit mask bit = false ∧ bit_value*2 = Z.shiftl 1 (bit+1) ∧
    1 ≤ bit_value*2 ∧ bit_value*2 ≤ Z.shiftl 1 count ∧
    (∀ lower, 0 ≤ lower ∧ lower < bit+1 → Z.testbit mask lower = false) := by
  have hlt := dp_bits_scan_lt mask count bit bit_value h
  have hb := h.2.1.1
  have hc : 0 ≤ count := by ((try simp only [Int.ofNat_eq_coe] at *); omega)
  have hclear : Z.testbit mask bit = false := by
    have ht := congrArg (fun x => Z.testbit x bit) hland
    change Z.testbit (Z.land mask bit_value) bit = Z.testbit 0 bit at ht
    rw [Z.land_spec, h.2.2.1, testbit_shiftl_one__bit_scan bit bit hb hb, dp_bits_test_zero] at ht
    simpa [Z.eqb] using ht
  have he : bit_value*2 = Z.shiftl 1 (bit+1) := by
    rw [h.2.2.1, dp_bits_shift bit hb, dp_bits_shift (bit+1) (by ((try simp only [Int.ofNat_eq_coe] at *); omega))]
    have hn : (bit+1).toNat = bit.toNat+1 := by ((try simp only [Int.ofNat_eq_coe] at *); omega)
    rw [hn, Nat.pow_succ]
    simp
  have hnpos := Nat.two_pow_pos (bit+1).toNat
  have hle : (2^(bit+1).toNat : Nat) ≤ 2^count.toNat := Nat.pow_le_pow_right (by decide) (by ((try simp only [Int.ofNat_eq_coe] at *); omega))
  refine ⟨hlt, hclear, he, ?_, ?_, ?_⟩
  · rw [he, dp_bits_shift (bit+1) (by ((try simp only [Int.ofNat_eq_coe] at *); omega))]; ((try simp only [Int.ofNat_eq_coe] at *); omega)
  · rw [he, dp_bits_shift (bit+1) (by ((try simp only [Int.ofNat_eq_coe] at *); omega)), dp_bits_shift count hc]; ((try simp only [Int.ofNat_eq_coe] at *); omega)
  · intro lower hl
    by_cases he : lower = bit
    · subst lower; exact hclear
    · exact h.2.2.2 lower (by ((try simp only [Int.ofNat_eq_coe] at *); omega))

theorem selected_bit_state_from_scan__bit_scan (mask count bit bit_value : Int)
    (h : BitScanState mask count bit bit_value) (hland : Z.land mask bit_value ≠ 0) :
    bit < count ∧ Z.testbit mask bit = true ∧ Z.land mask bit_value = bit_value ∧
    (0 ≤ Z.lxor mask bit_value ∧ Z.lxor mask bit_value < mask) ∧ bit_value < Z.shiftl 1 count := by
  have hb := h.2.1.1
  have hlt := dp_bits_scan_lt mask count bit bit_value h
  have hc : 0 ≤ count := by ((try simp only [Int.ofNat_eq_coe] at *); omega)
  have hone : Z.testbit mask bit = true := by
    cases ht : Z.testbit mask bit with
    | true => rfl
    | false =>
      exfalso; apply hland
      apply Z.bits_inj'
      intro n hn
      rw [Z.land_spec, h.2.2.1, testbit_shiftl_one__bit_scan bit n hb hn, dp_bits_test_zero]
      by_cases he : n = bit
      · subst n; simp [Z.eqb, ht]
      · simp [Z.eqb, he]
  have hand : Z.land mask bit_value = bit_value := by
    apply Z.bits_inj'
    intro n hn
    rw [Z.land_spec, h.2.2.1, testbit_shiftl_one__bit_scan bit n hb hn]
    by_cases he : n = bit
    · subst n; simp [Z.eqb, hone]
    · simp [Z.eqb, he]
  have hv : 0 ≤ bit_value := by rw [h.2.2.1, dp_bits_shift bit hb]; exact Int.natCast_nonneg _
  have hm : 0 ≤ mask := by have := h.1.1; ((try simp only [Int.ofNat_eq_coe] at *); omega)
  have hx0 := dp_bits_xor_nonneg mask bit_value hm hv
  have hxl : Z.lxor mask bit_value ≤ mask := by
    apply dp_bits_le_of_test _ _ hx0 hm
    intro n hn ht
    rw [Z.lxor_spec, h.2.2.1, testbit_shiftl_one__bit_scan bit n hb hn] at ht
    by_cases he : n = bit
    · subst n; simp [Z.eqb, hone] at ht
    · simpa [Z.eqb, he] using ht
  have hxne : Z.lxor mask bit_value ≠ mask := by
    intro he
    have ht := congrArg (fun x => Z.testbit x bit) he
    change Z.testbit (Z.lxor mask bit_value) bit = Z.testbit mask bit at ht
    rw [Z.lxor_spec, h.2.2.1, testbit_shiftl_one__bit_scan bit bit hb hb, hone] at ht
    simp [Z.eqb] at ht
  have hp : (2^bit.toNat : Nat) < 2^count.toNat := Nat.pow_lt_pow_of_lt (by decide) (by ((try simp only [Int.ofNat_eq_coe] at *); omega))
  refine ⟨hlt, hone, hand, ⟨hx0, by ((try simp only [Int.ofNat_eq_coe] at *); omega)⟩, ?_⟩
  rw [h.2.2.1, dp_bits_shift bit hb, dp_bits_shift count hc]
  ((try simp only [Int.ofNat_eq_coe] at *); omega)

theorem log2_lt_pow2__output_finalization (x n : Int) (hx : 0 ≤ x ∧ x < Z.pow 2 n) (hn : 0 < n) : Z.log2 x < n := by
  rw [dp_bits_pow n (by ((try simp only [Int.ofNat_eq_coe] at *); omega))] at hx
  unfold Z.log2
  by_cases h0 : x.toNat = 0
  · rw [h0, Nat.log2_zero]; ((try simp only [Int.ofNat_eq_coe] at *); omega)
  · have h := (Nat.log2_lt h0).mpr (show x.toNat < 2^n.toNat by ((try simp only [Int.ofNat_eq_coe] at *); omega))
    ((try simp only [Int.ofNat_eq_coe] at *); omega)

theorem lxor_lt_pow2__output_finalization (x y n : Int) (hx : 0 ≤ x ∧ x < Z.pow 2 n)
    (hy : 0 ≤ y ∧ y < Z.pow 2 n) (hn : 0 < n) : 0 ≤ Z.lxor x y ∧ Z.lxor x y < Z.pow 2 n := by
  rw [dp_bits_pow n (by ((try simp only [Int.ofNat_eq_coe] at *); omega))] at hx hy ⊢
  cases x with
  | negSucc x => ((try simp only [Int.ofNat_eq_coe] at *); omega)
  | ofNat x =>
    cases y with
    | negSucc y => ((try simp only [Int.ofNat_eq_coe] at *); omega)
    | ofNat y =>
      have h := Nat.xor_lt_two_pow (show x < 2^n.toNat by ((try simp only [Int.ofNat_eq_coe] at *); omega)) (show y < 2^n.toNat by ((try simp only [Int.ofNat_eq_coe] at *); omega))
      simp only [HXor.hXor, XorOp.xor] at h
      change 0 ≤ Int.ofNat (Nat.xor x y) ∧ Int.ofNat (Nat.xor x y) < Int.ofNat (2^n.toNat)
      ((try simp only [Int.ofNat_eq_coe] at *); omega)

theorem testbit_one_positive__output_finalization (k : Int) (hk : 0 < k) : Z.testbit 1 k = false := by
  rw [dp_bits_test_nonneg _ _ (by decide) (by ((try simp only [Int.ofNat_eq_coe] at *); omega))]
  cases h : k.toNat with
  | zero => ((try simp only [Int.ofNat_eq_coe] at *); omega)
  | succ n => rw [Nat.testBit_succ]; simp

theorem shifted_one_testbit__output_finalization (first index : Int) (hf : 0 ≤ first) (hi : 0 ≤ index) :
    Z.testbit (Z.shiftl 1 first) index = Z.eqb index first := testbit_shiftl_one__bit_scan first index hf hi

theorem lxor_shifted_one_true__output_finalization (mask first index : Int) (hf : 0 ≤ first)
    (hs : Z.testbit mask first = true) : Z.testbit (Z.lxor mask (Z.shiftl 1 first)) index = true ↔
    Z.testbit mask index = true ∧ index ≠ first := by
  by_cases hi : 0 ≤ index
  · rw [Z.lxor_spec, shifted_one_testbit__output_finalization first index hf hi]
    by_cases he : index = first
    · subst index; simp [Z.eqb, hs]
    · simp [Z.eqb, he]
  · rw [dp_bits_test_neg _ _ (by ((try simp only [Int.ofNat_eq_coe] at *); omega)), dp_bits_test_neg _ _ (by ((try simp only [Int.ofNat_eq_coe] at *); omega))]
    simp


theorem testbit_shiftl_one__dp_table_transition (bit index : Int) (hb : 0≤bit) (hi : 0≤index) :
    Z.testbit (Z.shiftl 1 bit) index=true ↔ index=bit := by
  rw [testbit_shiftl_one__bit_scan bit index hb hi]
  simp [Z.eqb]

theorem selected_mask_partition__dp_table_transition (mask count bit bit_value rest index : Int)
    (hs : SelectedBitState mask count bit bit_value rest) (hi : 0≤index ∧ index<count) :
    Z.testbit mask index=true ↔ index=bit ∨ Z.testbit rest index=true := by
  have hbit := hs.2.2.2.1
  have hr : rest=Z.lxor mask (Z.shiftl 1 bit) := by rw [hs.2.2.2.2.1,hs.1.2.2.1]
  rw [hr,lxor_shifted_one_true__output_finalization mask bit index hs.2.2.1.1 hbit]
  by_cases he : index=bit
  · simp [he,hbit]
  · simp [he]

theorem best_index_keep_previous__dp_table_transition (rows : List (List Int)) (lens : List Int)
    (count mask bit bit_value rest previous comparison : Int)
    (hs : SelectedBitState mask count bit bit_value rest) (hb : BestIndexForMask rows lens count rest previous)
    (hc : comparison≤0) (ho : ConcatCompareSignOutcome rows lens bit previous comparison) :
    BestIndexForMask rows lens count mask previous := by
  have hprev := (selected_mask_partition__dp_table_transition mask count bit bit_value rest previous hs hb.1).mpr (Or.inr hb.2.1)
  refine ⟨hb.1,hprev,?_⟩
  intro other hr hbit
  rcases (selected_mask_partition__dp_table_transition mask count bit bit_value rest other hs hr).mp hbit with he|hm
  · rw [he]
    exact compare_outcome_nonpositive__dp_table_transition rows lens bit previous comparison hc ho
  · exact hb.2.2 other hr hm

theorem best_index_choose_bit__dp_table_transition (rows : List (List Int)) (lens : List Int)
    (count width mask bit bit_value rest previous comparison : Int)
    (hw : RowsWellFormed rows lens count width) (hs : SelectedBitState mask count bit bit_value rest)
    (hb : BestIndexForMask rows lens count rest previous) (hc : comparison>0)
    (ho : ConcatCompareSignOutcome rows lens bit previous comparison) : BestIndexForMask rows lens count mask bit := by
  refine ⟨hs.2.2.1,hs.2.2.2.1,?_⟩
  intro other hr hbit
  rcases (selected_mask_partition__dp_table_transition mask count bit bit_value rest other hs hr).mp hbit with he|hm
  · rw [he]
    exact item_before_or_equal_refl__dp_table_transition rows lens bit
  · exact item_before_or_equal_transitive__dp_table_transition rows lens count width bit previous other hw hs.2.2.1 hb.1 hr
      (compare_outcome_positive__dp_table_transition rows lens bit previous comparison hc ho) (hb.2.2 other hr hm)

theorem best_index_singleton__dp_table_transition (rows : List (List Int)) (lens : List Int)
    (count mask bit bit_value rest : Int) (hs : SelectedBitState mask count bit bit_value rest) (hz : rest=0) :
    BestIndexForMask rows lens count mask bit := by
  refine ⟨hs.2.2.1,hs.2.2.2.1,?_⟩
  intro other hr hbit
  rcases (selected_mask_partition__dp_table_transition mask count bit bit_value rest other hs hr).mp hbit with he|hm
  · rw [he]
    exact item_before_or_equal_refl__dp_table_transition rows lens bit
  · rw [hz] at hm
    cases other <;> simp [Z.testbit] at hm

theorem full_mask_indexes__output_initialization (count : Int) (hc : 0≤count) :
    MaskIndexes count (Z.shiftl 1 count-1) (all_indices count) := by
  intro index
  rw [all_indices_spec__output_initialization count index hc]
  constructor
  · intro hi
    refine ⟨hi,?_⟩
    rw [dp_bits_shift count hc]
    have hpos := Nat.two_pow_pos count.toNat
    have he : Int.ofNat (2^count.toNat)-1=Int.ofNat (2^count.toNat-1) := by simp only[Int.ofNat_eq_coe];omega
    rw [he,dp_bits_test_nonneg (Int.ofNat (2^count.toNat-1)) index (Int.natCast_nonneg _) hi.1]
    change Nat.testBit (2^count.toNat-1) index.toNat=true
    rw [Nat.testBit_two_pow_sub_one]
    simp only [decide_eq_true_eq]
    omega
  · exact And.left

theorem greedy_output_full_mask__output_initialization (rows : List (List Int)) (lens : List Int) (count : Int)
    (hlen : Zlength rows=count) (hc : 0≤count) : GreedyOutputPrefix rows lens count (Z.shiftl 1 count-1) [] := by
  obtain ⟨order,hp,hmax⟩ := largest_concatenation_exists__output_initialization rows lens
  have hp' : Permutation (all_indices count) order := by simpa only [hlen] using hp
  refine ⟨[],order,by simpa only[List.nil_append] using hp',?_,rfl,?_⟩
  · intro index
    rw [←hp'.mem_iff]
    exact full_mask_indexes__output_initialization count hc index
  · exact ⟨order,hp,rfl,hmax⟩

theorem greedy_output_consume_best__output_finalization
    (rows : List (List Int)) (lens : List Int) (count width mask first : Int)
    (prior current : List Int) (position : Int)
    (hw : RowsWellFormed rows lens count width)
    (hb : BestIndexForMask rows lens count mask first)
    (hg : GreedyOutputPrefix rows lens count mask prior)
    (ha : AppendRowPrefix rows lens prior first position current)
    (hlo : position ≥ Znth first lens 0) (hhi : position ≤ Znth first lens 0) :
    GreedyOutputPrefix rows lens count (Z.lxor mask (Z.shiftl 1 first)) current := by
  obtain ⟨hfirst,hselected,hbest⟩ := hb
  obtain ⟨done,todo,hperm,hmask,hprior,hlargest⟩ := hg
  have hin : first∈todo := (hmask first).mpr ⟨hfirst,hselected⟩
  obtain ⟨before,after,htodo⟩ := List.mem_iff_append.mp hin
  subst todo
  have hcombined := hperm.nodup (all_indices_nodup__output_finalization count)
  have htodo := (List.nodup_append.mp hcombined).2.1
  have hremoved : first∉before++after := (List.nodup_cons.mp (htodo.perm List.perm_middle)).1
  have hlength := item_digits_length__output_finalization rows lens count width first hw hfirst
  unfold AppendRowPrefix at ha
  rw [sublist_self _ position (by omega)] at ha
  have hnewperm : Permutation (all_indices count) (done++first::(before++after)) :=
    hperm.trans (List.perm_middle.append_left done)
  refine ⟨done++[first],before++after,?_,?_,?_,?_⟩
  · simpa only [List.append_assoc,List.cons_append,List.nil_append] using hnewperm
  · intro index
    rw [lxor_shifted_one_true__output_finalization mask first index hfirst.1 hselected]
    constructor
    · intro hindex
      have hold : index∈before++first::after := by
        rcases List.mem_append.mp hindex with h|h
        · exact List.mem_append_left _ h
        · exact List.mem_append_right _ (List.mem_cons_of_mem first h)
      have h := (hmask index).mp hold
      refine ⟨h.1,h.2,?_⟩
      intro he
      subst index
      exact hremoved hindex
    · rintro ⟨hrange,hbit,hne⟩
      have hold := (hmask index).mpr ⟨hrange,hbit⟩
      rcases List.mem_append.mp hold with h|h
      · exact List.mem_append_left after h
      · rcases List.mem_cons.mp h with he|h
        · exact False.elim (hne he)
        · exact List.mem_append_right before h
  · rw [ha,hprior,concatenate_indices_app__output_finalization,
      concatenate_indices_singleton__output_finalization]
  · have hmove := concatenate_move_best_front_ge__output_finalization rows lens first before after (by
      intro index hindex
      have h := (hmask index).mp (List.mem_append_left (first::after) hindex)
      exact hbest index h.1 h.2)
    have hnewold : digit_lex_ge
        (concatenate_indices rows lens (done++first::(before++after)))
        (concatenate_indices rows lens (done++(before++first::after))) := by
      rw [concatenate_indices_app__output_finalization rows lens done _,
        concatenate_indices_app__output_finalization rows lens done _]
      exact digit_lex_ge_append_left__output_finalization _ _ _ hmove
    have hnewrows : Permutation (all_indices (Zlength rows)) (done++first::(before++after)) := by
      rw [hw.1]
      exact hnewperm
    obtain ⟨optimal,hoptimalperm,hoptimaloutput,hoptimal⟩ := hlargest
    have holdnew := hoptimal _ hnewrows
    have hequal := digit_lex_ge_antisym__output_finalization _ _ hnewold holdnew
    simp only [List.append_assoc,List.cons_append,List.nil_append]
    rw [hequal]
    exact ⟨optimal,hoptimalperm,hoptimaloutput,hoptimal⟩

end SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers_dp.concatenating_numbers_dp_lib

namespace SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers_dp
export concatenating_numbers_dp_lib (number_item item_digits item_at concatenate_indices all_indices digit_lex_ge item_before_or_equal RowsWellFormed FlatRows ConcatLeftDigit ConcatRightDigit ConcatComparePrefix ConcatCompareLoopState ConcatCompareSignOutcome BestIndexForMask DPTablePrefix BitScanState SelectedBitState MaskIndexes LargestConcatenation GreedyOutputPrefix AppendRowPrefix)
end SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers_dp

namespace SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers_dp
export SimpleC.EE.LLM_bench.Algorithms.decimal_digits (DecimalRowValues)
end SimpleC.EE.LLM_bench.Algorithms.concatenating_numbers_dp
