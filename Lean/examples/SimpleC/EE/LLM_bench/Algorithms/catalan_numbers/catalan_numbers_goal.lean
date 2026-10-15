import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Algorithms.catalan_numbers.catalan_numbers_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.catalan_numbers.catalan_numbers_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance catalan_numbers_goalSacContext : SacContext := ⟨naive_C_Rules⟩

private noncomputable abbrev charArray := naive_C_Rules.CharArray
private noncomputable abbrev charArray2 := naive_C_Rules.CharArray2
private noncomputable abbrev charArray3 := naive_C_Rules.CharArray3
private noncomputable abbrev charPtrArray2 := naive_C_Rules.CharPtrArray2
private noncomputable abbrev ucharArray := naive_C_Rules.UCharArray
private noncomputable abbrev ucharArray2 := naive_C_Rules.UCharArray2
private noncomputable abbrev ucharArray3 := naive_C_Rules.UCharArray3
private noncomputable abbrev ucharPtrArray2 := naive_C_Rules.UCharPtrArray2
private noncomputable abbrev shortArray := naive_C_Rules.ShortArray
private noncomputable abbrev shortArray2 := naive_C_Rules.ShortArray2
private noncomputable abbrev shortArray3 := naive_C_Rules.ShortArray3
private noncomputable abbrev shortPtrArray2 := naive_C_Rules.ShortPtrArray2
private noncomputable abbrev ushortArray := naive_C_Rules.UShortArray
private noncomputable abbrev ushortArray2 := naive_C_Rules.UShortArray2
private noncomputable abbrev ushortArray3 := naive_C_Rules.UShortArray3
private noncomputable abbrev ushortPtrArray2 := naive_C_Rules.UShortPtrArray2
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev intArray2 := naive_C_Rules.IntArray2
private noncomputable abbrev intArray3 := naive_C_Rules.IntArray3
private noncomputable abbrev intPtrArray2 := naive_C_Rules.IntPtrArray2
private noncomputable abbrev uintArray := naive_C_Rules.UIntArray
private noncomputable abbrev uintArray2 := naive_C_Rules.UIntArray2
private noncomputable abbrev uintArray3 := naive_C_Rules.UIntArray3
private noncomputable abbrev uintPtrArray2 := naive_C_Rules.UIntPtrArray2
private noncomputable abbrev int64Array := naive_C_Rules.Int64Array
private noncomputable abbrev int64Array2 := naive_C_Rules.Int64Array2
private noncomputable abbrev int64Array3 := naive_C_Rules.Int64Array3
private noncomputable abbrev int64PtrArray2 := naive_C_Rules.Int64PtrArray2
private noncomputable abbrev uint64Array := naive_C_Rules.UInt64Array
private noncomputable abbrev uint64Array2 := naive_C_Rules.UInt64Array2
private noncomputable abbrev uint64Array3 := naive_C_Rules.UInt64Array3
private noncomputable abbrev uint64PtrArray2 := naive_C_Rules.UInt64PtrArray2
private noncomputable abbrev ptrArray := naive_C_Rules.PtrArray
private noncomputable abbrev ptrArray2 := naive_C_Rules.PtrArray2
private noncomputable abbrev ptrArray3 := naive_C_Rules.PtrArray3
private noncomputable abbrev ptrPtrArray2 := naive_C_Rules.PtrPtrArray2
private noncomputable abbrev store_string := naive_C_Rules.store_string

noncomputable def id_safety_wit_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (n_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : ((0 : Int) <= x_pre)) (PreH4 : (x_pre <= n_pre)) (PreH5 : ((0 : Int) <= y_pre)) (PreH6 : (y_pre <= (n_pre + 1))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "y" ) )) # Int |-> (y_pre))
|--
  “ (((x_pre * (n_pre + 1)) + y_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((x_pre * (n_pre + 1)) + y_pre)) ”

noncomputable def id_safety_wit_2 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (n_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : ((0 : Int) <= x_pre)) (PreH4 : (x_pre <= n_pre)) (PreH5 : ((0 : Int) <= y_pre)) (PreH6 : (y_pre <= (n_pre + 1))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "y" ) )) # Int |-> (y_pre))
|--
  “ ((x_pre * (n_pre + 1)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (x_pre * (n_pre + 1))) ”

noncomputable def id_safety_wit_3 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (n_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : ((0 : Int) <= x_pre)) (PreH4 : (x_pre <= n_pre)) (PreH5 : ((0 : Int) <= y_pre)) (PreH6 : (y_pre <= (n_pre + 1))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "y" ) )) # Int |-> (y_pre))
|--
  “ ((n_pre + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre + 1)) ”

noncomputable def id_safety_wit_4 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (n_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : ((0 : Int) <= x_pre)) (PreH4 : (x_pre <= n_pre)) (PreH5 : ((0 : Int) <= y_pre)) (PreH6 : (y_pre <= (n_pre + 1))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "x" ) )) # Int |-> (x_pre))
  ** ((( &( "y" ) )) # Int |-> (y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def id_return_wit_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (n_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : ((0 : Int) <= x_pre)) (PreH4 : (x_pre <= n_pre)) (PreH5 : ((0 : Int) <= y_pre)) (PreH6 : (y_pre <= (n_pre + 1))) ,
  TT && emp 
|--
  “ (((x_pre * (n_pre + 1)) + y_pre) = ((x_pre * (n_pre + 1)) + y_pre)) ”
  &&  emp

noncomputable def solve_safety_wit_1 : Prop :=
  forall (n_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 7)) ,
  ((( &( "i" ) )) # Int |->_)
  ** (intArray.undef_full ( &( "f" ) ) 64)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solve_safety_wit_2 : Prop :=
  forall (n_pre : Int) (table : (List Int)) (i : Int) (PreH1 : (i <= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 7)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (n_pre + 1))) (PreH6 : (StackTablePrefix n_pre table (i * (n_pre + 1)))) (PreH7 : forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < (i * (n_pre + 1)))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c))))))) ,
  ((( &( "j" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.seg ( &( "f" ) ) (0 : Int) (i * (n_pre + 1)) table)
  ** (intArray.undef_seg ( &( "f" ) ) (i * (n_pre + 1)) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solve_safety_wit_3 : Prop :=
  forall (n_pre : Int) (table : (List Int)) (j : Int) (i : Int) (PreH1 : (j <= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 7)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= (n_pre + 1))) (PreH8 : (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j))) (PreH9 : forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c))))))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solve_safety_wit_4 : Prop :=
  forall (n_pre : Int) (table : (List Int)) (j : Int) (i : Int) (retval : Int) (PreH1 : (retval = ((i * (n_pre + 1)) + j))) (PreH2 : (i = (0 : Int))) (PreH3 : (j <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j <= (n_pre + 1))) (PreH10 : (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j))) (PreH11 : forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c))))))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solve_safety_wit_5 : Prop :=
  forall (n_pre : Int) (table : (List Int)) (j : Int) (i : Int) (PreH1 : (i ≠ (0 : Int))) (PreH2 : (j <= n_pre)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 7)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((0 : Int) <= j)) (PreH8 : (j <= (n_pre + 1))) (PreH9 : (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j))) (PreH10 : forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c))))))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solve_safety_wit_6 : Prop :=
  forall (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval : Int) (PreH1 : (retval = ((i * (n_pre + 1)) + j))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 7)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (j = (0 : Int))) (PreH7 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH8 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH9 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH10 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH11 : (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j))) (PreH12 : forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c))))))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def solve_safety_wit_7 : Prop :=
  forall (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval : Int) (PreH1 : (retval = ((i * (n_pre + 1)) + j))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 7)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (j = (0 : Int))) (PreH7 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH8 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH9 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH10 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH11 : (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j))) (PreH12 : forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c))))))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def solve_safety_wit_8 : Prop :=
  forall (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval : Int) (PreH1 : (retval = ((i * (n_pre + 1)) + j))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 7)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (j = (0 : Int))) (PreH7 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH8 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH9 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH10 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH11 : (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j))) (PreH12 : forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c))))))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solve_safety_wit_9 : Prop :=
  forall (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval : Int) (PreH1 : (retval = ((i * (n_pre + 1)) + j))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 7)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (j = (0 : Int))) (PreH7 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH8 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH9 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH10 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH11 : (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j))) (PreH12 : forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c))))))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solve_safety_wit_10 : Prop :=
  (
forall (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval_3 : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = ((i * (n_pre + 1)) + (j - 1)))) (PreH2 : (retval = (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH3 : (retval_3 = ((i * (n_pre + 1)) + j))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= n_pre)) (PreH10 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH11 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH12 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH13 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH14 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH15 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH16 : (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j))) (PreH17 : forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c))))))) ,
  (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ (((Znth (retval - (0 : Int)) table (0 : Int)) + (Znth (retval_2 - (0 : Int)) table (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth (retval - (0 : Int)) table (0 : Int)) + (Znth (retval_2 - (0 : Int)) table (0 : Int)))) ”
) \/
(
forall (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval_3 : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = ((i * (n_pre + 1)) + (j - 1)))) (PreH2 : (retval = (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH3 : (retval_3 = ((i * (n_pre + 1)) + j))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= n_pre)) (PreH10 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH11 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH12 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH13 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH14 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH15 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH16 : (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j))) (PreH17 : forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c))))))) ,
  (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ (((Znth (retval - (0 : Int)) table (0 : Int)) + (Znth (retval_2 - (0 : Int)) table (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth (retval - (0 : Int)) table (0 : Int)) + (Znth (retval_2 - (0 : Int)) table (0 : Int)))) ”
)

noncomputable def solve_safety_wit_10_split_goal_1 : Prop :=
  forall (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval_3 : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = ((i * (n_pre + 1)) + (j - 1)))) (PreH2 : (retval = (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH3 : (retval_3 = ((i * (n_pre + 1)) + j))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= n_pre)) (PreH10 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH11 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH12 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH13 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH14 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH15 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH16 : (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j))) (PreH17 : forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c))))))) ,
  (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ (((Znth (retval - (0 : Int)) table (0 : Int)) + (Znth (retval_2 - (0 : Int)) table (0 : Int))) <= INT_MAX) ”

noncomputable def solve_safety_wit_10_split_goal_2 : Prop :=
  forall (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval_3 : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = ((i * (n_pre + 1)) + (j - 1)))) (PreH2 : (retval = (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH3 : (retval_3 = ((i * (n_pre + 1)) + j))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= n_pre)) (PreH10 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH11 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH12 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH13 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH14 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH15 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH16 : (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j))) (PreH17 : forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c))))))) ,
  (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ ((INT_MIN) <= ((Znth (retval - (0 : Int)) table (0 : Int)) + (Znth (retval_2 - (0 : Int)) table (0 : Int)))) ”

noncomputable def solve_safety_wit_11 : Prop :=
  forall (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval : Int) (PreH1 : (retval = ((i * (n_pre + 1)) + j))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 7)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= j)) (PreH7 : (j <= n_pre)) (PreH8 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH9 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH10 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH11 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH12 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH13 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH14 : (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j))) (PreH15 : forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c))))))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def solve_safety_wit_12 : Prop :=
  forall (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval : Int) (PreH1 : (retval = ((i * (n_pre + 1)) + j))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 7)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= j)) (PreH7 : (j <= n_pre)) (PreH8 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH9 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH10 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH11 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH12 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH13 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH14 : (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j))) (PreH15 : forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c))))))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def solve_safety_wit_13 : Prop :=
  forall (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval : Int) (PreH1 : (retval = ((i * (n_pre + 1)) + j))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 7)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= j)) (PreH7 : (j <= n_pre)) (PreH8 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH9 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH10 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH11 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH12 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH13 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH14 : (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j))) (PreH15 : forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c))))))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solve_safety_wit_14 : Prop :=
  forall (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval : Int) (PreH1 : (retval = ((i * (n_pre + 1)) + j))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 7)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= j)) (PreH7 : (j <= n_pre)) (PreH8 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH9 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH10 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH11 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH12 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH13 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH14 : (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j))) (PreH15 : forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c))))))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solve_safety_wit_15 : Prop :=
  forall (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH2 : (retval = ((i * (n_pre + 1)) + j))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 7)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= n_pre)) (PreH9 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH10 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH11 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH12 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH13 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH14 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH15 : (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j))) (PreH16 : forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c))))))) ,
  (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ ((j - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j - 1)) ”

noncomputable def solve_safety_wit_16 : Prop :=
  forall (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH2 : (retval = ((i * (n_pre + 1)) + j))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 7)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= n_pre)) (PreH9 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH10 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH11 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH12 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH13 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH14 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH15 : (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j))) (PreH16 : forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c))))))) ,
  (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solve_safety_wit_17 : Prop :=
  forall (n_pre : Int) (table : (List Int)) (j : Int) (i : Int) (retval : Int) (PreH1 : (retval = ((i * (n_pre + 1)) + j))) (PreH2 : (i = (0 : Int))) (PreH3 : (j <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j <= (n_pre + 1))) (PreH10 : (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j))) (PreH11 : forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c))))))) ,
  (intArray.seg ( &( "f" ) ) (0 : Int) (((i * (n_pre + 1)) + j) + 1) (table ++ (1 :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "f" ) ) (((i * (n_pre + 1)) + j) + 1) ((n_pre + 1) * (n_pre + 1)))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def solve_safety_wit_18 : Prop :=
  forall (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH2 : (retval = ((i * (n_pre + 1)) + j))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 7)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (j = (0 : Int))) (PreH8 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH9 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH10 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH11 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH12 : (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j))) (PreH13 : forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c))))))) ,
  (intArray.seg ( &( "f" ) ) (0 : Int) (((i * (n_pre + 1)) + j) + 1) (table ++ ((Znth (retval_2 - (0 : Int)) table (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "f" ) ) (((i * (n_pre + 1)) + j) + 1) ((n_pre + 1) * (n_pre + 1)))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def solve_safety_wit_19 : Prop :=
  forall (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval : Int) (retval_2 : Int) (retval_3 : Int) (PreH1 : (retval_3 = ((i * (n_pre + 1)) + (j - 1)))) (PreH2 : (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH3 : (retval = ((i * (n_pre + 1)) + j))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= n_pre)) (PreH10 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH11 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH12 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH13 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH14 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH15 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH16 : (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j))) (PreH17 : forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c))))))) ,
  (intArray.seg ( &( "f" ) ) (0 : Int) (((i * (n_pre + 1)) + j) + 1) (table ++ (((Znth (retval_2 - (0 : Int)) table (0 : Int)) + (Znth (retval_3 - (0 : Int)) table (0 : Int))) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "f" ) ) (((i * (n_pre + 1)) + j) + 1) ((n_pre + 1) * (n_pre + 1)))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def solve_safety_wit_20 : Prop :=
  forall (n_pre : Int) (table : (List Int)) (j : Int) (i : Int) (PreH1 : (j > n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 7)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= (n_pre + 1))) (PreH8 : (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j))) (PreH9 : forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c))))))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def solve_safety_wit_21 : Prop :=
  forall (n_pre : Int) (table : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : ((0 : Int) <= (n_pre * (n_pre + 1)))) (PreH4 : ((n_pre * (n_pre + 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH5 : (StackSequenceCount n_pre (Znth (n_pre * (n_pre + 1)) table (0 : Int)))) ,
  ((( &( "result" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solve_entail_wit_1 : Prop :=
  (
forall (n_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 7)) ,
  (intArray.undef_full ( &( "f" ) ) 64)
|--
  EX table : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (n_pre + 1)) ” &&
  “ (StackTablePrefix n_pre table ((0 : Int) * (n_pre + 1))) ” &&
  “ forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((0 : Int) * (n_pre + 1)))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c)))))) ”
  &&  (intArray.seg ( &( "f" ) ) (0 : Int) ((0 : Int) * (n_pre + 1)) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((0 : Int) * (n_pre + 1)) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
) \/
(
forall (n_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 7)) ,
  (intArray.undef_full ( &( "f" ) ) 64)
|--
  EX table : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (n_pre + 1)) ” &&
  “ (StackTablePrefix n_pre table ((0 : Int) * (n_pre + 1))) ” &&
  “ forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((0 : Int) * (n_pre + 1)))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c)))))) ”
  &&  (intArray.seg ( &( "f" ) ) (0 : Int) ((0 : Int) * (n_pre + 1)) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((0 : Int) * (n_pre + 1)) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
)

noncomputable def solve_entail_wit_2 : Prop :=
  (
forall (n_pre : Int) (table_2 : (List Int)) (i : Int) (PreH1 : (i <= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 7)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (n_pre + 1))) (PreH6 : (StackTablePrefix n_pre table_2 (i * (n_pre + 1)))) (PreH7 : forall (r_2 : Int) , forall (c_2 : Int) , (((((((0 : Int) <= r_2) ∧ (r_2 <= n_pre)) ∧ ((0 : Int) <= c_2)) ∧ (c_2 <= n_pre)) ∧ (((r_2 * (n_pre + 1)) + c_2) < (i * (n_pre + 1)))) -> (((0 : Int) <= (Znth ((r_2 * (n_pre + 1)) + c_2) table_2 (0 : Int))) ∧ ((Znth ((r_2 * (n_pre + 1)) + c_2) table_2 (0 : Int)) <= (Zpower (2) (((2 * r_2) + c_2))))))) ,
  (intArray.seg ( &( "f" ) ) (0 : Int) (i * (n_pre + 1)) table_2)
  ** (intArray.undef_seg ( &( "f" ) ) (i * (n_pre + 1)) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  EX table : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (n_pre + 1)) ” &&
  “ (StackTablePrefix n_pre table ((i * (n_pre + 1)) + (0 : Int))) ” &&
  “ forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + (0 : Int)))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c)))))) ”
  &&  (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + (0 : Int)) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + (0 : Int)) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
) \/
(
forall (n_pre : Int) (table_2 : (List Int)) (i : Int) (PreH1 : (i <= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 7)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (n_pre + 1))) (PreH6 : (StackTablePrefix n_pre table_2 (i * (n_pre + 1)))) (PreH7 : forall (r_2 : Int) , forall (c_2 : Int) , (((((((0 : Int) <= r_2) ∧ (r_2 <= n_pre)) ∧ ((0 : Int) <= c_2)) ∧ (c_2 <= n_pre)) ∧ (((r_2 * (n_pre + 1)) + c_2) < (i * (n_pre + 1)))) -> (((0 : Int) <= (Znth ((r_2 * (n_pre + 1)) + c_2) table_2 (0 : Int))) ∧ ((Znth ((r_2 * (n_pre + 1)) + c_2) table_2 (0 : Int)) <= (Zpower (2) (((2 * r_2) + c_2))))))) ,
  (intArray.seg ( &( "f" ) ) (0 : Int) (i * (n_pre + 1)) table_2)
|--
  EX table : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (n_pre + 1)) ” &&
  “ (StackTablePrefix n_pre table ((i * (n_pre + 1)) + (0 : Int))) ” &&
  “ forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + (0 : Int)))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c)))))) ”
  &&  (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + (0 : Int)) table)
)

noncomputable def solve_entail_wit_3 : Prop :=
  (
forall (n_pre : Int) (table_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j = (0 : Int))) (PreH2 : (i ≠ (0 : Int))) (PreH3 : (j <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j <= (n_pre + 1))) (PreH10 : (StackTablePrefix n_pre table_2 ((i * (n_pre + 1)) + j))) (PreH11 : forall (r_2 : Int) , forall (c_2 : Int) , (((((((0 : Int) <= r_2) ∧ (r_2 <= n_pre)) ∧ ((0 : Int) <= c_2)) ∧ (c_2 <= n_pre)) ∧ (((r_2 * (n_pre + 1)) + c_2) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r_2 * (n_pre + 1)) + c_2) table_2 (0 : Int))) ∧ ((Znth ((r_2 * (n_pre + 1)) + c_2) table_2 (0 : Int)) <= (Zpower (2) (((2 * r_2) + c_2))))))) ,
  (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table_2)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  EX table : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (j = (0 : Int)) ” &&
  “ ((0 : Int) <= ((i * (n_pre + 1)) + j)) ” &&
  “ (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1))) ” &&
  “ ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j)) ” &&
  “ (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j)) ” &&
  “ forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c)))))) ”
  &&  (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
) \/
(
forall (n_pre : Int) (table_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j = (0 : Int))) (PreH2 : (i ≠ (0 : Int))) (PreH3 : (j <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j <= (n_pre + 1))) (PreH10 : (StackTablePrefix n_pre table_2 ((i * (n_pre + 1)) + j))) (PreH11 : forall (r_2 : Int) , forall (c_2 : Int) , (((((((0 : Int) <= r_2) ∧ (r_2 <= n_pre)) ∧ ((0 : Int) <= c_2)) ∧ (c_2 <= n_pre)) ∧ (((r_2 * (n_pre + 1)) + c_2) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r_2 * (n_pre + 1)) + c_2) table_2 (0 : Int))) ∧ ((Znth ((r_2 * (n_pre + 1)) + c_2) table_2 (0 : Int)) <= (Zpower (2) (((2 * r_2) + c_2))))))) ,
  TT && emp 
|--
  “ forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table_2 (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table_2 (0 : Int)) <= (Zpower (2) (((2 * r) + c)))))) ” &&
  “ ((((i - 1) * (n_pre + 1)) + ((0 : Int) + 1)) < ((i * (n_pre + 1)) + (0 : Int))) ” &&
  “ (((i * (n_pre + 1)) + (0 : Int)) < ((n_pre + 1) * (n_pre + 1))) ”
  &&  emp
)

noncomputable def solve_entail_wit_3_split_goal_1 : Prop :=
  forall (n_pre : Int) (table_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j = (0 : Int))) (PreH2 : (i ≠ (0 : Int))) (PreH3 : (j <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j <= (n_pre + 1))) (PreH10 : (StackTablePrefix n_pre table_2 ((i * (n_pre + 1)) + j))) (PreH11 : forall (r_2 : Int) , forall (c_2 : Int) , (((((((0 : Int) <= r_2) ∧ (r_2 <= n_pre)) ∧ ((0 : Int) <= c_2)) ∧ (c_2 <= n_pre)) ∧ (((r_2 * (n_pre + 1)) + c_2) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r_2 * (n_pre + 1)) + c_2) table_2 (0 : Int))) ∧ ((Znth ((r_2 * (n_pre + 1)) + c_2) table_2 (0 : Int)) <= (Zpower (2) (((2 * r_2) + c_2))))))) ,
  forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table_2 (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table_2 (0 : Int)) <= (Zpower (2) (((2 * r) + c))))))

noncomputable def solve_entail_wit_3_split_goal_2 : Prop :=
  forall (n_pre : Int) (table_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j = (0 : Int))) (PreH2 : (i ≠ (0 : Int))) (PreH3 : (j <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j <= (n_pre + 1))) (PreH10 : (StackTablePrefix n_pre table_2 ((i * (n_pre + 1)) + j))) (PreH11 : forall (r_2 : Int) , forall (c_2 : Int) , (((((((0 : Int) <= r_2) ∧ (r_2 <= n_pre)) ∧ ((0 : Int) <= c_2)) ∧ (c_2 <= n_pre)) ∧ (((r_2 * (n_pre + 1)) + c_2) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r_2 * (n_pre + 1)) + c_2) table_2 (0 : Int))) ∧ ((Znth ((r_2 * (n_pre + 1)) + c_2) table_2 (0 : Int)) <= (Zpower (2) (((2 * r_2) + c_2))))))) ,
  ((((i - 1) * (n_pre + 1)) + ((0 : Int) + 1)) < ((i * (n_pre + 1)) + (0 : Int)))

noncomputable def solve_entail_wit_3_split_goal_3 : Prop :=
  forall (n_pre : Int) (table_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j = (0 : Int))) (PreH2 : (i ≠ (0 : Int))) (PreH3 : (j <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j <= (n_pre + 1))) (PreH10 : (StackTablePrefix n_pre table_2 ((i * (n_pre + 1)) + j))) (PreH11 : forall (r_2 : Int) , forall (c_2 : Int) , (((((((0 : Int) <= r_2) ∧ (r_2 <= n_pre)) ∧ ((0 : Int) <= c_2)) ∧ (c_2 <= n_pre)) ∧ (((r_2 * (n_pre + 1)) + c_2) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r_2 * (n_pre + 1)) + c_2) table_2 (0 : Int))) ∧ ((Znth ((r_2 * (n_pre + 1)) + c_2) table_2 (0 : Int)) <= (Zpower (2) (((2 * r_2) + c_2))))))) ,
  (((i * (n_pre + 1)) + (0 : Int)) < ((n_pre + 1) * (n_pre + 1)))

noncomputable def solve_entail_wit_4 : Prop :=
  (
forall (n_pre : Int) (table_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j ≠ (0 : Int))) (PreH2 : (i ≠ (0 : Int))) (PreH3 : (j <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j <= (n_pre + 1))) (PreH10 : (StackTablePrefix n_pre table_2 ((i * (n_pre + 1)) + j))) (PreH11 : forall (r_2 : Int) , forall (c_2 : Int) , (((((((0 : Int) <= r_2) ∧ (r_2 <= n_pre)) ∧ ((0 : Int) <= c_2)) ∧ (c_2 <= n_pre)) ∧ (((r_2 * (n_pre + 1)) + c_2) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r_2 * (n_pre + 1)) + c_2) table_2 (0 : Int))) ∧ ((Znth ((r_2 * (n_pre + 1)) + c_2) table_2 (0 : Int)) <= (Zpower (2) (((2 * r_2) + c_2))))))) ,
  (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table_2)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  EX table : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ ((0 : Int) <= ((i * (n_pre + 1)) + j)) ” &&
  “ (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1))) ” &&
  “ ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j)) ” &&
  “ ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1))) ” &&
  “ (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j)) ” &&
  “ (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j)) ” &&
  “ forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c)))))) ”
  &&  (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
) \/
(
forall (n_pre : Int) (table_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j ≠ (0 : Int))) (PreH2 : (i ≠ (0 : Int))) (PreH3 : (j <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j <= (n_pre + 1))) (PreH10 : (StackTablePrefix n_pre table_2 ((i * (n_pre + 1)) + j))) (PreH11 : forall (r_2 : Int) , forall (c_2 : Int) , (((((((0 : Int) <= r_2) ∧ (r_2 <= n_pre)) ∧ ((0 : Int) <= c_2)) ∧ (c_2 <= n_pre)) ∧ (((r_2 * (n_pre + 1)) + c_2) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r_2 * (n_pre + 1)) + c_2) table_2 (0 : Int))) ∧ ((Znth ((r_2 * (n_pre + 1)) + c_2) table_2 (0 : Int)) <= (Zpower (2) (((2 * r_2) + c_2))))))) ,
  TT && emp 
|--
  “ forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table_2 (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table_2 (0 : Int)) <= (Zpower (2) (((2 * r) + c)))))) ” &&
  “ ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j)) ” &&
  “ (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ”
  &&  emp
)

noncomputable def solve_entail_wit_4_split_goal_1 : Prop :=
  forall (n_pre : Int) (table_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j ≠ (0 : Int))) (PreH2 : (i ≠ (0 : Int))) (PreH3 : (j <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j <= (n_pre + 1))) (PreH10 : (StackTablePrefix n_pre table_2 ((i * (n_pre + 1)) + j))) (PreH11 : forall (r_2 : Int) , forall (c_2 : Int) , (((((((0 : Int) <= r_2) ∧ (r_2 <= n_pre)) ∧ ((0 : Int) <= c_2)) ∧ (c_2 <= n_pre)) ∧ (((r_2 * (n_pre + 1)) + c_2) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r_2 * (n_pre + 1)) + c_2) table_2 (0 : Int))) ∧ ((Znth ((r_2 * (n_pre + 1)) + c_2) table_2 (0 : Int)) <= (Zpower (2) (((2 * r_2) + c_2))))))) ,
  forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table_2 (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table_2 (0 : Int)) <= (Zpower (2) (((2 * r) + c))))))

noncomputable def solve_entail_wit_4_split_goal_2 : Prop :=
  forall (n_pre : Int) (table_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j ≠ (0 : Int))) (PreH2 : (i ≠ (0 : Int))) (PreH3 : (j <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j <= (n_pre + 1))) (PreH10 : (StackTablePrefix n_pre table_2 ((i * (n_pre + 1)) + j))) (PreH11 : forall (r_2 : Int) , forall (c_2 : Int) , (((((((0 : Int) <= r_2) ∧ (r_2 <= n_pre)) ∧ ((0 : Int) <= c_2)) ∧ (c_2 <= n_pre)) ∧ (((r_2 * (n_pre + 1)) + c_2) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r_2 * (n_pre + 1)) + c_2) table_2 (0 : Int))) ∧ ((Znth ((r_2 * (n_pre + 1)) + c_2) table_2 (0 : Int)) <= (Zpower (2) (((2 * r_2) + c_2))))))) ,
  ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))

noncomputable def solve_entail_wit_4_split_goal_3 : Prop :=
  forall (n_pre : Int) (table_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j ≠ (0 : Int))) (PreH2 : (i ≠ (0 : Int))) (PreH3 : (j <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j <= (n_pre + 1))) (PreH10 : (StackTablePrefix n_pre table_2 ((i * (n_pre + 1)) + j))) (PreH11 : forall (r_2 : Int) , forall (c_2 : Int) , (((((((0 : Int) <= r_2) ∧ (r_2 <= n_pre)) ∧ ((0 : Int) <= c_2)) ∧ (c_2 <= n_pre)) ∧ (((r_2 * (n_pre + 1)) + c_2) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r_2 * (n_pre + 1)) + c_2) table_2 (0 : Int))) ∧ ((Znth ((r_2 * (n_pre + 1)) + c_2) table_2 (0 : Int)) <= (Zpower (2) (((2 * r_2) + c_2))))))) ,
  (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))

noncomputable def solve_entail_wit_5_1 : Prop :=
  (
forall (n_pre : Int) (table_2 : (List Int)) (j : Int) (i : Int) (retval : Int) (PreH1 : (retval = ((i * (n_pre + 1)) + j))) (PreH2 : (i = (0 : Int))) (PreH3 : (j <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j <= (n_pre + 1))) (PreH10 : (StackTablePrefix n_pre table_2 ((i * (n_pre + 1)) + j))) (PreH11 : forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table_2 (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table_2 (0 : Int)) <= (Zpower (2) (((2 * r) + c))))))) ,
  (intArray.seg ( &( "f" ) ) (0 : Int) (((i * (n_pre + 1)) + j) + 1) (table_2 ++ (1 :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "f" ) ) (((i * (n_pre + 1)) + j) + 1) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  EX table : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= (n_pre + 1)) ” &&
  “ (StackTablePrefix n_pre table ((i * (n_pre + 1)) + (j + 1))) ” &&
  “ forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + (j + 1)))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c)))))) ”
  &&  (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + (j + 1)) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + (j + 1)) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
) \/
(
forall (n_pre : Int) (table_2 : (List Int)) (j : Int) (i : Int) (retval : Int) (PreH1 : (retval = ((i * (n_pre + 1)) + j))) (PreH2 : (i = (0 : Int))) (PreH3 : (j <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j <= (n_pre + 1))) (PreH10 : (StackTablePrefix n_pre table_2 ((i * (n_pre + 1)) + j))) (PreH11 : forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table_2 (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table_2 (0 : Int)) <= (Zpower (2) (((2 * r) + c))))))) ,
  (intArray.seg ( &( "f" ) ) (0 : Int) (((i * (n_pre + 1)) + j) + 1) (table_2 ++ (1 :: (@List.nil Int))))
|--
  EX table : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= (n_pre + 1)) ” &&
  “ (StackTablePrefix n_pre table ((i * (n_pre + 1)) + (j + 1))) ” &&
  “ forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + (j + 1)))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c)))))) ”
  &&  (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + (j + 1)) table)
)

noncomputable def solve_entail_wit_5_2 : Prop :=
  (
forall (n_pre : Int) (table_2 : (List Int)) (i : Int) (j : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH2 : (retval = ((i * (n_pre + 1)) + j))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 7)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (j = (0 : Int))) (PreH8 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH9 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH10 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH11 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH12 : (StackTablePrefix n_pre table_2 ((i * (n_pre + 1)) + j))) (PreH13 : forall (r_2 : Int) , forall (c_2 : Int) , (((((((0 : Int) <= r_2) ∧ (r_2 <= n_pre)) ∧ ((0 : Int) <= c_2)) ∧ (c_2 <= n_pre)) ∧ (((r_2 * (n_pre + 1)) + c_2) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r_2 * (n_pre + 1)) + c_2) table_2 (0 : Int))) ∧ ((Znth ((r_2 * (n_pre + 1)) + c_2) table_2 (0 : Int)) <= (Zpower (2) (((2 * r_2) + c_2))))))) ,
  (intArray.seg ( &( "f" ) ) (0 : Int) (((i * (n_pre + 1)) + j) + 1) (table_2 ++ ((Znth (retval_2 - (0 : Int)) table_2 (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "f" ) ) (((i * (n_pre + 1)) + j) + 1) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  EX table : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= (n_pre + 1)) ” &&
  “ (StackTablePrefix n_pre table ((i * (n_pre + 1)) + (j + 1))) ” &&
  “ forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + (j + 1)))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c)))))) ”
  &&  (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + (j + 1)) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + (j + 1)) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
) \/
(
forall (n_pre : Int) (table_2 : (List Int)) (i : Int) (j : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH2 : (retval = ((i * (n_pre + 1)) + j))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 7)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (j = (0 : Int))) (PreH8 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH9 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH10 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH11 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH12 : (StackTablePrefix n_pre table_2 ((i * (n_pre + 1)) + j))) (PreH13 : forall (r_2 : Int) , forall (c_2 : Int) , (((((((0 : Int) <= r_2) ∧ (r_2 <= n_pre)) ∧ ((0 : Int) <= c_2)) ∧ (c_2 <= n_pre)) ∧ (((r_2 * (n_pre + 1)) + c_2) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r_2 * (n_pre + 1)) + c_2) table_2 (0 : Int))) ∧ ((Znth ((r_2 * (n_pre + 1)) + c_2) table_2 (0 : Int)) <= (Zpower (2) (((2 * r_2) + c_2))))))) ,
  (intArray.seg ( &( "f" ) ) (0 : Int) (((i * (n_pre + 1)) + j) + 1) (table_2 ++ ((Znth (retval_2 - (0 : Int)) table_2 (0 : Int)) :: (@List.nil Int))))
|--
  EX table : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= (n_pre + 1)) ” &&
  “ (StackTablePrefix n_pre table ((i * (n_pre + 1)) + (j + 1))) ” &&
  “ forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + (j + 1)))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c)))))) ”
  &&  (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + (j + 1)) table)
)

noncomputable def solve_entail_wit_5_3 : Prop :=
  (
forall (n_pre : Int) (table_2 : (List Int)) (i : Int) (j : Int) (retval : Int) (retval_2 : Int) (retval_3 : Int) (PreH1 : (retval_3 = ((i * (n_pre + 1)) + (j - 1)))) (PreH2 : (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH3 : (retval = ((i * (n_pre + 1)) + j))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= n_pre)) (PreH10 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH11 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH12 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH13 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH14 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH15 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH16 : (StackTablePrefix n_pre table_2 ((i * (n_pre + 1)) + j))) (PreH17 : forall (r_2 : Int) , forall (c_2 : Int) , (((((((0 : Int) <= r_2) ∧ (r_2 <= n_pre)) ∧ ((0 : Int) <= c_2)) ∧ (c_2 <= n_pre)) ∧ (((r_2 * (n_pre + 1)) + c_2) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r_2 * (n_pre + 1)) + c_2) table_2 (0 : Int))) ∧ ((Znth ((r_2 * (n_pre + 1)) + c_2) table_2 (0 : Int)) <= (Zpower (2) (((2 * r_2) + c_2))))))) ,
  (intArray.seg ( &( "f" ) ) (0 : Int) (((i * (n_pre + 1)) + j) + 1) (table_2 ++ (((Znth (retval_2 - (0 : Int)) table_2 (0 : Int)) + (Znth (retval_3 - (0 : Int)) table_2 (0 : Int))) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "f" ) ) (((i * (n_pre + 1)) + j) + 1) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  EX table : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= (n_pre + 1)) ” &&
  “ (StackTablePrefix n_pre table ((i * (n_pre + 1)) + (j + 1))) ” &&
  “ forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + (j + 1)))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c)))))) ”
  &&  (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + (j + 1)) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + (j + 1)) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
) \/
(
forall (n_pre : Int) (table_2 : (List Int)) (i : Int) (j : Int) (retval : Int) (retval_2 : Int) (retval_3 : Int) (PreH1 : (retval_3 = ((i * (n_pre + 1)) + (j - 1)))) (PreH2 : (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH3 : (retval = ((i * (n_pre + 1)) + j))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= n_pre)) (PreH10 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH11 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH12 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH13 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH14 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH15 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH16 : (StackTablePrefix n_pre table_2 ((i * (n_pre + 1)) + j))) (PreH17 : forall (r_2 : Int) , forall (c_2 : Int) , (((((((0 : Int) <= r_2) ∧ (r_2 <= n_pre)) ∧ ((0 : Int) <= c_2)) ∧ (c_2 <= n_pre)) ∧ (((r_2 * (n_pre + 1)) + c_2) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r_2 * (n_pre + 1)) + c_2) table_2 (0 : Int))) ∧ ((Znth ((r_2 * (n_pre + 1)) + c_2) table_2 (0 : Int)) <= (Zpower (2) (((2 * r_2) + c_2))))))) ,
  (intArray.seg ( &( "f" ) ) (0 : Int) (((i * (n_pre + 1)) + j) + 1) (table_2 ++ (((Znth (retval_2 - (0 : Int)) table_2 (0 : Int)) + (Znth (retval_3 - (0 : Int)) table_2 (0 : Int))) :: (@List.nil Int))))
|--
  EX table : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= (n_pre + 1)) ” &&
  “ (StackTablePrefix n_pre table ((i * (n_pre + 1)) + (j + 1))) ” &&
  “ forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + (j + 1)))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c)))))) ”
  &&  (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + (j + 1)) table)
)

noncomputable def solve_entail_wit_6 : Prop :=
  (
forall (n_pre : Int) (table_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j > n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 7)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= (n_pre + 1))) (PreH8 : (StackTablePrefix n_pre table_2 ((i * (n_pre + 1)) + j))) (PreH9 : forall (r_2 : Int) , forall (c_2 : Int) , (((((((0 : Int) <= r_2) ∧ (r_2 <= n_pre)) ∧ ((0 : Int) <= c_2)) ∧ (c_2 <= n_pre)) ∧ (((r_2 * (n_pre + 1)) + c_2) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r_2 * (n_pre + 1)) + c_2) table_2 (0 : Int))) ∧ ((Znth ((r_2 * (n_pre + 1)) + c_2) table_2 (0 : Int)) <= (Zpower (2) (((2 * r_2) + c_2))))))) ,
  (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table_2)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  EX table : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= (n_pre + 1)) ” &&
  “ (StackTablePrefix n_pre table ((i + 1) * (n_pre + 1))) ” &&
  “ forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i + 1) * (n_pre + 1)))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c)))))) ”
  &&  (intArray.seg ( &( "f" ) ) (0 : Int) ((i + 1) * (n_pre + 1)) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((i + 1) * (n_pre + 1)) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
) \/
(
forall (n_pre : Int) (table_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j > n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 7)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= n_pre)) (PreH6 : ((0 : Int) <= j)) (PreH7 : (j <= (n_pre + 1))) (PreH8 : (StackTablePrefix n_pre table_2 ((i * (n_pre + 1)) + j))) (PreH9 : forall (r_2 : Int) , forall (c_2 : Int) , (((((((0 : Int) <= r_2) ∧ (r_2 <= n_pre)) ∧ ((0 : Int) <= c_2)) ∧ (c_2 <= n_pre)) ∧ (((r_2 * (n_pre + 1)) + c_2) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r_2 * (n_pre + 1)) + c_2) table_2 (0 : Int))) ∧ ((Znth ((r_2 * (n_pre + 1)) + c_2) table_2 (0 : Int)) <= (Zpower (2) (((2 * r_2) + c_2))))))) ,
  (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table_2)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
|--
  EX table : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= (n_pre + 1)) ” &&
  “ (StackTablePrefix n_pre table ((i + 1) * (n_pre + 1))) ” &&
  “ forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i + 1) * (n_pre + 1)))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c)))))) ”
  &&  (intArray.seg ( &( "f" ) ) (0 : Int) ((i + 1) * (n_pre + 1)) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((i + 1) * (n_pre + 1)) ((n_pre + 1) * (n_pre + 1)))
)

noncomputable def solve_entail_wit_7 : Prop :=
  (
forall (n_pre : Int) (table_2 : (List Int)) (i : Int) (PreH1 : (i > n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 7)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (n_pre + 1))) (PreH6 : (StackTablePrefix n_pre table_2 (i * (n_pre + 1)))) (PreH7 : forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < (i * (n_pre + 1)))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table_2 (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table_2 (0 : Int)) <= (Zpower (2) (((2 * r) + c))))))) ,
  (intArray.seg ( &( "f" ) ) (0 : Int) (i * (n_pre + 1)) table_2)
  ** (intArray.undef_seg ( &( "f" ) ) (i * (n_pre + 1)) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  EX table : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= (n_pre * (n_pre + 1))) ” &&
  “ ((n_pre * (n_pre + 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (StackSequenceCount n_pre (Znth (n_pre * (n_pre + 1)) table (0 : Int))) ”
  &&  (intArray.full ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
) \/
(
forall (n_pre : Int) (table_2 : (List Int)) (i : Int) (PreH1 : (i > n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 7)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (n_pre + 1))) (PreH6 : (StackTablePrefix n_pre table_2 (i * (n_pre + 1)))) (PreH7 : forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < (i * (n_pre + 1)))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table_2 (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table_2 (0 : Int)) <= (Zpower (2) (((2 * r) + c))))))) ,
  (intArray.seg ( &( "f" ) ) (0 : Int) (i * (n_pre + 1)) table_2)
  ** (intArray.undef_seg ( &( "f" ) ) (i * (n_pre + 1)) ((n_pre + 1) * (n_pre + 1)))
|--
  EX table : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= (n_pre * (n_pre + 1))) ” &&
  “ ((n_pre * (n_pre + 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (StackSequenceCount n_pre (Znth (n_pre * (n_pre + 1)) table (0 : Int))) ”
  &&  (intArray.full ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) table)
)

noncomputable def solve_entail_wit_8 : Prop :=
  (
forall (n_pre : Int) (table : (List Int)) (retval : Int) (PreH1 : (retval = ((n_pre * (n_pre + 1)) + (0 : Int)))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 7)) (PreH4 : ((0 : Int) <= (n_pre * (n_pre + 1)))) (PreH5 : ((n_pre * (n_pre + 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH6 : (StackSequenceCount n_pre (Znth (n_pre * (n_pre + 1)) table (0 : Int)))) ,
  (intArray.full ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ (StackSequenceCount n_pre (Znth retval table (0 : Int))) ”
  &&  (intArray.undef_full ( &( "f" ) ) 64)
) \/
(
forall (n_pre : Int) (table : (List Int)) (retval : Int) (PreH1 : (retval = ((n_pre * (n_pre + 1)) + (0 : Int)))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 7)) (PreH4 : ((0 : Int) <= (n_pre * (n_pre + 1)))) (PreH5 : ((n_pre * (n_pre + 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH6 : (StackSequenceCount n_pre (Znth (n_pre * (n_pre + 1)) table (0 : Int)))) ,
  (intArray.full ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ (StackSequenceCount n_pre (Znth ((n_pre * (n_pre + 1)) + (0 : Int)) table (0 : Int))) ”
  &&  (intArray.undef_full ( &( "f" ) ) 64)
)

noncomputable def solve_entail_wit_8_split_goal_1 : Prop :=
  forall (n_pre : Int) (table : (List Int)) (retval : Int) (PreH1 : (retval = ((n_pre * (n_pre + 1)) + (0 : Int)))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 7)) (PreH4 : ((0 : Int) <= (n_pre * (n_pre + 1)))) (PreH5 : ((n_pre * (n_pre + 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH6 : (StackSequenceCount n_pre (Znth (n_pre * (n_pre + 1)) table (0 : Int)))) ,
  (intArray.full ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ (StackSequenceCount n_pre (Znth ((n_pre * (n_pre + 1)) + (0 : Int)) table (0 : Int))) ”

noncomputable def solve_entail_wit_8_split_goal_spatial : Prop :=
  forall (n_pre : Int) (table : (List Int)) (retval : Int) (PreH1 : (retval = ((n_pre * (n_pre + 1)) + (0 : Int)))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 7)) (PreH4 : ((0 : Int) <= (n_pre * (n_pre + 1)))) (PreH5 : ((n_pre * (n_pre + 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH6 : (StackSequenceCount n_pre (Znth (n_pre * (n_pre + 1)) table (0 : Int)))) ,
  (intArray.full ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  (intArray.undef_full ( &( "f" ) ) 64)

noncomputable def solve_return_wit_1 : Prop :=
  forall (n_pre : Int) (result : Int) (PreH1 : (StackSequenceCount n_pre result)) ,
  TT && emp 
|--
  “ (StackSequenceCount n_pre result) ”
  &&  emp

noncomputable def solve_partial_solve_wit_1_pure : Prop :=
  forall (n_pre : Int) (table : (List Int)) (j : Int) (i : Int) (PreH1 : (i = (0 : Int))) (PreH2 : (j <= n_pre)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 7)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((0 : Int) <= j)) (PreH8 : (j <= (n_pre + 1))) (PreH9 : (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j))) (PreH10 : forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c))))))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (n_pre + 1)) ”

noncomputable def solve_partial_solve_wit_1_aux : Prop :=
  forall (n_pre : Int) (table : (List Int)) (j : Int) (i : Int) (PreH1 : (i = (0 : Int))) (PreH2 : (j <= n_pre)) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 7)) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= n_pre)) (PreH7 : ((0 : Int) <= j)) (PreH8 : (j <= (n_pre + 1))) (PreH9 : (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j))) (PreH10 : forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c))))))) ,
  (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (n_pre + 1)) ” &&
  “ (i = (0 : Int)) ” &&
  “ (j <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (n_pre + 1)) ” &&
  “ (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j)) ” &&
  “ forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c)))))) ”
  &&  (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)

noncomputable def solve_partial_solve_wit_1 : Prop := solve_partial_solve_wit_1_pure -> solve_partial_solve_wit_1_aux

noncomputable def solve_partial_solve_wit_2 : Prop :=
  forall (n_pre : Int) (table : (List Int)) (j : Int) (i : Int) (retval : Int) (PreH1 : (retval = ((i * (n_pre + 1)) + j))) (PreH2 : (i = (0 : Int))) (PreH3 : (j <= n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : ((0 : Int) <= j)) (PreH9 : (j <= (n_pre + 1))) (PreH10 : (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j))) (PreH11 : forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c))))))) ,
  (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ (retval = ((i * (n_pre + 1)) + j)) ” &&
  “ (i = (0 : Int)) ” &&
  “ (j <= n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (n_pre + 1)) ” &&
  “ (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j)) ” &&
  “ forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c)))))) ”
  &&  (((( &( "f" ) ) + (retval * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_missing_i ( &( "f" ) ) retval ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)

noncomputable def solve_partial_solve_wit_3_pure : Prop :=
  forall (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : (1 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (j = (0 : Int))) (PreH6 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH7 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH9 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH10 : (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j))) (PreH11 : forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c))))))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (n_pre + 1)) ”

noncomputable def solve_partial_solve_wit_3_aux : Prop :=
  forall (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : (1 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (j = (0 : Int))) (PreH6 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH7 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH9 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH10 : (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j))) (PreH11 : forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c))))))) ,
  (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (j = (0 : Int)) ” &&
  “ ((0 : Int) <= ((i * (n_pre + 1)) + j)) ” &&
  “ (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1))) ” &&
  “ ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j)) ” &&
  “ (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j)) ” &&
  “ forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c)))))) ”
  &&  (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)

noncomputable def solve_partial_solve_wit_3 : Prop := solve_partial_solve_wit_3_pure -> solve_partial_solve_wit_3_aux

noncomputable def solve_partial_solve_wit_4_pure : Prop :=
  forall (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval : Int) (PreH1 : (retval = ((i * (n_pre + 1)) + j))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 7)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (j = (0 : Int))) (PreH7 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH8 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH9 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH10 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH11 : (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j))) (PreH12 : forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c))))))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) <= n_pre) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= (n_pre + 1)) ”

noncomputable def solve_partial_solve_wit_4_aux : Prop :=
  forall (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval : Int) (PreH1 : (retval = ((i * (n_pre + 1)) + j))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 7)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (j = (0 : Int))) (PreH7 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH8 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH9 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH10 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH11 : (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j))) (PreH12 : forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c))))))) ,
  (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) <= n_pre) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= (n_pre + 1)) ” &&
  “ (retval = ((i * (n_pre + 1)) + j)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (j = (0 : Int)) ” &&
  “ ((0 : Int) <= ((i * (n_pre + 1)) + j)) ” &&
  “ (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1))) ” &&
  “ ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j)) ” &&
  “ (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j)) ” &&
  “ forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c)))))) ”
  &&  (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)

noncomputable def solve_partial_solve_wit_4 : Prop := solve_partial_solve_wit_4_pure -> solve_partial_solve_wit_4_aux

noncomputable def solve_partial_solve_wit_5 : Prop :=
  forall (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH2 : (retval = ((i * (n_pre + 1)) + j))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 7)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (j = (0 : Int))) (PreH8 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH9 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH10 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH11 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH12 : (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j))) (PreH13 : forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c))))))) ,
  (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1))) ” &&
  “ (retval = ((i * (n_pre + 1)) + j)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (j = (0 : Int)) ” &&
  “ ((0 : Int) <= ((i * (n_pre + 1)) + j)) ” &&
  “ (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1))) ” &&
  “ ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j)) ” &&
  “ (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j)) ” &&
  “ forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c)))))) ”
  &&  (((( &( "f" ) ) + (retval_2 * sizeof(INT)))) # Int |-> ((Znth (retval_2 - (0 : Int)) table (0 : Int))))
  ** (intArray.missing_i ( &( "f" ) ) retval_2 (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)

noncomputable def solve_partial_solve_wit_6 : Prop :=
  forall (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH2 : (retval = ((i * (n_pre + 1)) + j))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 7)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (j = (0 : Int))) (PreH8 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH9 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH10 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH11 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH12 : (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j))) (PreH13 : forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c))))))) ,
  (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1))) ” &&
  “ (retval = ((i * (n_pre + 1)) + j)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (j = (0 : Int)) ” &&
  “ ((0 : Int) <= ((i * (n_pre + 1)) + j)) ” &&
  “ (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1))) ” &&
  “ ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j)) ” &&
  “ (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j)) ” &&
  “ forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c)))))) ”
  &&  (((( &( "f" ) ) + (retval * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_missing_i ( &( "f" ) ) retval ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)

noncomputable def solve_partial_solve_wit_7_pure : Prop :=
  forall (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : (1 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j <= n_pre)) (PreH7 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH8 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH9 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH10 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH11 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH12 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH13 : (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j))) (PreH14 : forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c))))))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (n_pre + 1)) ”

noncomputable def solve_partial_solve_wit_7_aux : Prop :=
  forall (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : (1 <= i)) (PreH4 : (i <= n_pre)) (PreH5 : (1 <= j)) (PreH6 : (j <= n_pre)) (PreH7 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH8 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH9 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH10 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH11 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH12 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH13 : (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j))) (PreH14 : forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c))))))) ,
  (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ ((0 : Int) <= ((i * (n_pre + 1)) + j)) ” &&
  “ (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1))) ” &&
  “ ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j)) ” &&
  “ ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1))) ” &&
  “ (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j)) ” &&
  “ (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j)) ” &&
  “ forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c)))))) ”
  &&  (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)

noncomputable def solve_partial_solve_wit_7 : Prop := solve_partial_solve_wit_7_pure -> solve_partial_solve_wit_7_aux

noncomputable def solve_partial_solve_wit_8_pure : Prop :=
  forall (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval : Int) (PreH1 : (retval = ((i * (n_pre + 1)) + j))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 7)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= j)) (PreH7 : (j <= n_pre)) (PreH8 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH9 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH10 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH11 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH12 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH13 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH14 : (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j))) (PreH15 : forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c))))))) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) <= n_pre) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= (n_pre + 1)) ”

noncomputable def solve_partial_solve_wit_8_aux : Prop :=
  forall (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval : Int) (PreH1 : (retval = ((i * (n_pre + 1)) + j))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 7)) (PreH4 : (1 <= i)) (PreH5 : (i <= n_pre)) (PreH6 : (1 <= j)) (PreH7 : (j <= n_pre)) (PreH8 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH9 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH10 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH11 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH12 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH13 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH14 : (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j))) (PreH15 : forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c))))))) ,
  (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) <= n_pre) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= (n_pre + 1)) ” &&
  “ (retval = ((i * (n_pre + 1)) + j)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ ((0 : Int) <= ((i * (n_pre + 1)) + j)) ” &&
  “ (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1))) ” &&
  “ ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j)) ” &&
  “ ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1))) ” &&
  “ (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j)) ” &&
  “ (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j)) ” &&
  “ forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c)))))) ”
  &&  (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)

noncomputable def solve_partial_solve_wit_8 : Prop := solve_partial_solve_wit_8_pure -> solve_partial_solve_wit_8_aux

noncomputable def solve_partial_solve_wit_9 : Prop :=
  forall (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH2 : (retval = ((i * (n_pre + 1)) + j))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 7)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= n_pre)) (PreH9 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH10 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH11 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH12 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH13 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH14 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH15 : (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j))) (PreH16 : forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c))))))) ,
  (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1))) ” &&
  “ (retval = ((i * (n_pre + 1)) + j)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ ((0 : Int) <= ((i * (n_pre + 1)) + j)) ” &&
  “ (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1))) ” &&
  “ ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j)) ” &&
  “ ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1))) ” &&
  “ (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j)) ” &&
  “ (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j)) ” &&
  “ forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c)))))) ”
  &&  (((( &( "f" ) ) + (retval_2 * sizeof(INT)))) # Int |-> ((Znth (retval_2 - (0 : Int)) table (0 : Int))))
  ** (intArray.missing_i ( &( "f" ) ) retval_2 (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)

noncomputable def solve_partial_solve_wit_10_pure : Prop :=
  forall (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH2 : (retval = ((i * (n_pre + 1)) + j))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 7)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= n_pre)) (PreH9 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH10 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH11 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH12 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH13 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH14 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH15 : (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j))) (PreH16 : forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c))))))) ,
  (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= (j - 1)) ” &&
  “ ((j - 1) <= (n_pre + 1)) ”

noncomputable def solve_partial_solve_wit_10_aux : Prop :=
  forall (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH2 : (retval = ((i * (n_pre + 1)) + j))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 7)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= n_pre)) (PreH9 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH10 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH11 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH12 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH13 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH14 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH15 : (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j))) (PreH16 : forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c))))))) ,
  (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= (j - 1)) ” &&
  “ ((j - 1) <= (n_pre + 1)) ” &&
  “ (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1))) ” &&
  “ (retval = ((i * (n_pre + 1)) + j)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ ((0 : Int) <= ((i * (n_pre + 1)) + j)) ” &&
  “ (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1))) ” &&
  “ ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j)) ” &&
  “ ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1))) ” &&
  “ (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j)) ” &&
  “ (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j)) ” &&
  “ forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c)))))) ”
  &&  (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)

noncomputable def solve_partial_solve_wit_10 : Prop := solve_partial_solve_wit_10_pure -> solve_partial_solve_wit_10_aux

noncomputable def solve_partial_solve_wit_11 : Prop :=
  forall (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval : Int) (retval_2 : Int) (retval_3 : Int) (PreH1 : (retval_3 = ((i * (n_pre + 1)) + (j - 1)))) (PreH2 : (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH3 : (retval = ((i * (n_pre + 1)) + j))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= n_pre)) (PreH10 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH11 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH12 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH13 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH14 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH15 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH16 : (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j))) (PreH17 : forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c))))))) ,
  (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ (retval_3 = ((i * (n_pre + 1)) + (j - 1))) ” &&
  “ (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1))) ” &&
  “ (retval = ((i * (n_pre + 1)) + j)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ ((0 : Int) <= ((i * (n_pre + 1)) + j)) ” &&
  “ (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1))) ” &&
  “ ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j)) ” &&
  “ ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1))) ” &&
  “ (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j)) ” &&
  “ (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j)) ” &&
  “ forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c)))))) ”
  &&  (((( &( "f" ) ) + (retval_3 * sizeof(INT)))) # Int |-> ((Znth (retval_3 - (0 : Int)) table (0 : Int))))
  ** (intArray.missing_i ( &( "f" ) ) retval_3 (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)

noncomputable def solve_partial_solve_wit_12 : Prop :=
  forall (n_pre : Int) (table : (List Int)) (i : Int) (j : Int) (retval : Int) (retval_2 : Int) (retval_3 : Int) (PreH1 : (retval_3 = ((i * (n_pre + 1)) + (j - 1)))) (PreH2 : (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH3 : (retval = ((i * (n_pre + 1)) + j))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 7)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= n_pre)) (PreH10 : ((0 : Int) <= ((i * (n_pre + 1)) + j))) (PreH11 : (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH12 : ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1)))) (PreH13 : ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j))) (PreH14 : ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1)))) (PreH15 : (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j))) (PreH16 : (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j))) (PreH17 : forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c))))))) ,
  (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ (retval_3 = ((i * (n_pre + 1)) + (j - 1))) ” &&
  “ (retval_2 = (((i - 1) * (n_pre + 1)) + (j + 1))) ” &&
  “ (retval = ((i * (n_pre + 1)) + j)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ ((0 : Int) <= ((i * (n_pre + 1)) + j)) ” &&
  “ (((i * (n_pre + 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= (((i - 1) * (n_pre + 1)) + (j + 1))) ” &&
  “ ((((i - 1) * (n_pre + 1)) + (j + 1)) < ((i * (n_pre + 1)) + j)) ” &&
  “ ((0 : Int) <= ((i * (n_pre + 1)) + (j - 1))) ” &&
  “ (((i * (n_pre + 1)) + (j - 1)) < ((i * (n_pre + 1)) + j)) ” &&
  “ (StackTablePrefix n_pre table ((i * (n_pre + 1)) + j)) ” &&
  “ forall (r : Int) , forall (c : Int) , (((((((0 : Int) <= r) ∧ (r <= n_pre)) ∧ ((0 : Int) <= c)) ∧ (c <= n_pre)) ∧ (((r * (n_pre + 1)) + c) < ((i * (n_pre + 1)) + j))) -> (((0 : Int) <= (Znth ((r * (n_pre + 1)) + c) table (0 : Int))) ∧ ((Znth ((r * (n_pre + 1)) + c) table (0 : Int)) <= (Zpower (2) (((2 * r) + c)))))) ”
  &&  (((( &( "f" ) ) + (retval * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_missing_i ( &( "f" ) ) retval ((i * (n_pre + 1)) + j) ((n_pre + 1) * (n_pre + 1)))
  ** (intArray.seg ( &( "f" ) ) (0 : Int) ((i * (n_pre + 1)) + j) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)

noncomputable def solve_partial_solve_wit_13_pure : Prop :=
  forall (n_pre : Int) (table : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : ((0 : Int) <= (n_pre * (n_pre + 1)))) (PreH4 : ((n_pre * (n_pre + 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH5 : (StackSequenceCount n_pre (Znth (n_pre * (n_pre + 1)) table (0 : Int)))) ,
  ((( &( "result" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (n_pre + 1)) ”

noncomputable def solve_partial_solve_wit_13_aux : Prop :=
  forall (n_pre : Int) (table : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 7)) (PreH3 : ((0 : Int) <= (n_pre * (n_pre + 1)))) (PreH4 : ((n_pre * (n_pre + 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH5 : (StackSequenceCount n_pre (Znth (n_pre * (n_pre + 1)) table (0 : Int)))) ,
  (intArray.full ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= (n_pre * (n_pre + 1))) ” &&
  “ ((n_pre * (n_pre + 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (StackSequenceCount n_pre (Znth (n_pre * (n_pre + 1)) table (0 : Int))) ”
  &&  (intArray.full ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)

noncomputable def solve_partial_solve_wit_13 : Prop := solve_partial_solve_wit_13_pure -> solve_partial_solve_wit_13_aux

noncomputable def solve_partial_solve_wit_14 : Prop :=
  forall (n_pre : Int) (table : (List Int)) (retval : Int) (PreH1 : (retval = ((n_pre * (n_pre + 1)) + (0 : Int)))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 7)) (PreH4 : ((0 : Int) <= (n_pre * (n_pre + 1)))) (PreH5 : ((n_pre * (n_pre + 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH6 : (StackSequenceCount n_pre (Znth (n_pre * (n_pre + 1)) table (0 : Int)))) ,
  (intArray.full ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)
|--
  “ (retval = ((n_pre * (n_pre + 1)) + (0 : Int))) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 7) ” &&
  “ ((0 : Int) <= (n_pre * (n_pre + 1))) ” &&
  “ ((n_pre * (n_pre + 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (StackSequenceCount n_pre (Znth (n_pre * (n_pre + 1)) table (0 : Int))) ”
  &&  (((( &( "f" ) ) + (retval * sizeof(INT)))) # Int |-> ((Znth retval table (0 : Int))))
  ** (intArray.missing_i ( &( "f" ) ) retval (0 : Int) ((n_pre + 1) * (n_pre + 1)) table)
  ** (intArray.undef_seg ( &( "f" ) ) ((n_pre + 1) * (n_pre + 1)) 64)


structure VC_Correct : Type where
  proof_of_id_safety_wit_1 : id_safety_wit_1
  proof_of_id_safety_wit_2 : id_safety_wit_2
  proof_of_id_safety_wit_3 : id_safety_wit_3
  proof_of_id_safety_wit_4 : id_safety_wit_4
  proof_of_id_return_wit_1 : id_return_wit_1
  proof_of_solve_safety_wit_1 : solve_safety_wit_1
  proof_of_solve_safety_wit_2 : solve_safety_wit_2
  proof_of_solve_safety_wit_3 : solve_safety_wit_3
  proof_of_solve_safety_wit_4 : solve_safety_wit_4
  proof_of_solve_safety_wit_5 : solve_safety_wit_5
  proof_of_solve_safety_wit_6 : solve_safety_wit_6
  proof_of_solve_safety_wit_7 : solve_safety_wit_7
  proof_of_solve_safety_wit_8 : solve_safety_wit_8
  proof_of_solve_safety_wit_9 : solve_safety_wit_9
  proof_of_solve_safety_wit_11 : solve_safety_wit_11
  proof_of_solve_safety_wit_12 : solve_safety_wit_12
  proof_of_solve_safety_wit_13 : solve_safety_wit_13
  proof_of_solve_safety_wit_14 : solve_safety_wit_14
  proof_of_solve_safety_wit_15 : solve_safety_wit_15
  proof_of_solve_safety_wit_16 : solve_safety_wit_16
  proof_of_solve_safety_wit_17 : solve_safety_wit_17
  proof_of_solve_safety_wit_18 : solve_safety_wit_18
  proof_of_solve_safety_wit_19 : solve_safety_wit_19
  proof_of_solve_safety_wit_20 : solve_safety_wit_20
  proof_of_solve_safety_wit_21 : solve_safety_wit_21
  proof_of_solve_return_wit_1 : solve_return_wit_1
  proof_of_solve_partial_solve_wit_1_pure : solve_partial_solve_wit_1_pure
  proof_of_solve_partial_solve_wit_1 : solve_partial_solve_wit_1
  proof_of_solve_partial_solve_wit_2 : solve_partial_solve_wit_2
  proof_of_solve_partial_solve_wit_3_pure : solve_partial_solve_wit_3_pure
  proof_of_solve_partial_solve_wit_3 : solve_partial_solve_wit_3
  proof_of_solve_partial_solve_wit_4_pure : solve_partial_solve_wit_4_pure
  proof_of_solve_partial_solve_wit_4 : solve_partial_solve_wit_4
  proof_of_solve_partial_solve_wit_5 : solve_partial_solve_wit_5
  proof_of_solve_partial_solve_wit_6 : solve_partial_solve_wit_6
  proof_of_solve_partial_solve_wit_7_pure : solve_partial_solve_wit_7_pure
  proof_of_solve_partial_solve_wit_7 : solve_partial_solve_wit_7
  proof_of_solve_partial_solve_wit_8_pure : solve_partial_solve_wit_8_pure
  proof_of_solve_partial_solve_wit_8 : solve_partial_solve_wit_8
  proof_of_solve_partial_solve_wit_9 : solve_partial_solve_wit_9
  proof_of_solve_partial_solve_wit_10_pure : solve_partial_solve_wit_10_pure
  proof_of_solve_partial_solve_wit_10 : solve_partial_solve_wit_10
  proof_of_solve_partial_solve_wit_11 : solve_partial_solve_wit_11
  proof_of_solve_partial_solve_wit_12 : solve_partial_solve_wit_12
  proof_of_solve_partial_solve_wit_13_pure : solve_partial_solve_wit_13_pure
  proof_of_solve_partial_solve_wit_13 : solve_partial_solve_wit_13
  proof_of_solve_partial_solve_wit_14 : solve_partial_solve_wit_14
  proof_of_solve_safety_wit_10 : solve_safety_wit_10
  proof_of_solve_entail_wit_1 : solve_entail_wit_1
  proof_of_solve_entail_wit_2 : solve_entail_wit_2
  proof_of_solve_entail_wit_3 : solve_entail_wit_3
  proof_of_solve_entail_wit_4 : solve_entail_wit_4
  proof_of_solve_entail_wit_5_1 : solve_entail_wit_5_1
  proof_of_solve_entail_wit_5_2 : solve_entail_wit_5_2
  proof_of_solve_entail_wit_5_3 : solve_entail_wit_5_3
  proof_of_solve_entail_wit_6 : solve_entail_wit_6
  proof_of_solve_entail_wit_7 : solve_entail_wit_7
  proof_of_solve_entail_wit_8 : solve_entail_wit_8

end SimpleC.EE.LLM_bench.Algorithms.catalan_numbers.catalan_numbers_goal
