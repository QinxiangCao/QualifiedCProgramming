import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Algorithms.matrix_chain_multiplication.matrix_chain_multiplication_lib
open SimpleC.EE.LLM_bench.Algorithms.matrix_chain_multiplication.matrix_chain_multiplication_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.matrix_chain_multiplication.matrix_chain_multiplication_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance matrix_chain_multiplication_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def matrixChainMinCost_safety_wit_1 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH6 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** (intArray.undef_full ( &( "cost" ) ) 64)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def matrixChainMinCost_safety_wit_2 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (i : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= (matrix_count_pre * matrix_count_pre))) (PreH6 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH7 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH8 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH9 : ((Zlength (cost_l)) = i)) (PreH10 : (Forall (Eq ((0 : Int))) cost_l)) ,
  ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.seg ( &( "cost" ) ) (0 : Int) i cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) i (matrix_count_pre * matrix_count_pre))
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ ((matrix_count_pre * matrix_count_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (matrix_count_pre * matrix_count_pre)) ”

noncomputable def matrixChainMinCost_safety_wit_3 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (i : Int) (PreH1 : (i < (matrix_count_pre * matrix_count_pre))) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= (matrix_count_pre * matrix_count_pre))) (PreH7 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH8 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH9 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH10 : ((Zlength (cost_l)) = i)) (PreH11 : (Forall (Eq ((0 : Int))) cost_l)) ,
  ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.seg ( &( "cost" ) ) (0 : Int) i cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) i (matrix_count_pre * matrix_count_pre))
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def matrixChainMinCost_safety_wit_4 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (i : Int) (PreH1 : (i < (matrix_count_pre * matrix_count_pre))) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= (matrix_count_pre * matrix_count_pre))) (PreH7 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH8 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH9 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH10 : ((Zlength (cost_l)) = i)) (PreH11 : (Forall (Eq ((0 : Int))) cost_l)) ,
  (intArray.seg ( &( "cost" ) ) (0 : Int) (i + 1) (cost_l ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "cost" ) ) (i + 1) (matrix_count_pre * matrix_count_pre))
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def matrixChainMinCost_safety_wit_5 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (i : Int) (PreH1 : (i >= (matrix_count_pre * matrix_count_pre))) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= (matrix_count_pre * matrix_count_pre))) (PreH7 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH8 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH9 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH10 : ((Zlength (cost_l)) = i)) (PreH11 : (Forall (Eq ((0 : Int))) cost_l)) ,
  ((( &( "chain_length" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.seg ( &( "cost" ) ) (0 : Int) i cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) i (matrix_count_pre * matrix_count_pre))
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def matrixChainMinCost_safety_wit_6 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (chain_length : Int) (cost_l : (List Int)) (PreH1 : (chain_length <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= (matrix_count_pre + 1))) (PreH8 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH9 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH10 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH12 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH13 : (1 <= chain_length)) (PreH14 : (MatrixChainLengthsComplete dimensions_l cost_l matrix_count_pre chain_length)) ,
  ((( &( "left" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def matrixChainMinCost_safety_wit_7 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (left : Int) (chain_length : Int) (cost_l : (List Int)) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH4 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH5 : (2 <= chain_length)) (PreH6 : (chain_length <= matrix_count_pre)) (PreH7 : ((0 : Int) <= left)) (PreH8 : (left <= ((matrix_count_pre - chain_length) + 1))) (PreH9 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH10 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH11 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH13 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH14 : (1 <= chain_length)) (PreH15 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left)) ,
  ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ ((left + chain_length) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left + chain_length)) ”

noncomputable def matrixChainMinCost_safety_wit_8 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (left : Int) (chain_length : Int) (cost_l : (List Int)) (PreH1 : ((left + chain_length) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : ((0 : Int) <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length) + 1))) (PreH10 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH12 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH14 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH15 : (1 <= chain_length)) (PreH16 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left)) ,
  ((( &( "right" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ (((left + chain_length) - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((left + chain_length) - 1)) ”

noncomputable def matrixChainMinCost_safety_wit_9 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (left : Int) (chain_length : Int) (cost_l : (List Int)) (PreH1 : ((left + chain_length) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : ((0 : Int) <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length) + 1))) (PreH10 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH12 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH14 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH15 : (1 <= chain_length)) (PreH16 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left)) ,
  ((( &( "right" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ ((left + chain_length) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left + chain_length)) ”

noncomputable def matrixChainMinCost_safety_wit_10 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (left : Int) (chain_length : Int) (cost_l : (List Int)) (PreH1 : ((left + chain_length) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : ((0 : Int) <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length) + 1))) (PreH10 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH12 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH14 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH15 : (1 <= chain_length)) (PreH16 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left)) ,
  ((( &( "right" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def matrixChainMinCost_safety_wit_11 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH34 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "best" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ ((((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) + (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int))) + (((Znth left dimensions_l (0 : Int)) * (Znth (left + 1) dimensions_l (0 : Int))) * (Znth (right + 1) dimensions_l (0 : Int)))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) + (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int))) + (((Znth left dimensions_l (0 : Int)) * (Znth (left + 1) dimensions_l (0 : Int))) * (Znth (right + 1) dimensions_l (0 : Int))))) ”

noncomputable def matrixChainMinCost_safety_wit_12 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH34 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "best" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ ((((Znth left dimensions_l (0 : Int)) * (Znth (left + 1) dimensions_l (0 : Int))) * (Znth (right + 1) dimensions_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((Znth left dimensions_l (0 : Int)) * (Znth (left + 1) dimensions_l (0 : Int))) * (Znth (right + 1) dimensions_l (0 : Int)))) ”

noncomputable def matrixChainMinCost_safety_wit_13 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH34 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "best" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ ((right + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (right + 1)) ”

noncomputable def matrixChainMinCost_safety_wit_14 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH34 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "best" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ (((Znth left dimensions_l (0 : Int)) * (Znth (left + 1) dimensions_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth left dimensions_l (0 : Int)) * (Znth (left + 1) dimensions_l (0 : Int)))) ”

noncomputable def matrixChainMinCost_safety_wit_15 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH34 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "best" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ ((left + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left + 1)) ”

noncomputable def matrixChainMinCost_safety_wit_16 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH34 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left)) ,
  (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "best" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ (((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) + (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) + (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) ”

noncomputable def matrixChainMinCost_safety_wit_17 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH34 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left)) ,
  (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "best" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ ((((left + 1) * matrix_count_pre) + right) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((left + 1) * matrix_count_pre) + right)) ”

noncomputable def matrixChainMinCost_safety_wit_18 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH34 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left)) ,
  (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "best" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ (((left + 1) * matrix_count_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((left + 1) * matrix_count_pre)) ”

noncomputable def matrixChainMinCost_safety_wit_19 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH34 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left)) ,
  (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "best" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ ((left + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left + 1)) ”

noncomputable def matrixChainMinCost_safety_wit_20 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH34 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left)) ,
  ((( &( "best" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ (((left * matrix_count_pre) + left) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((left * matrix_count_pre) + left)) ”

noncomputable def matrixChainMinCost_safety_wit_21 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH34 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left)) ,
  ((( &( "best" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ ((left * matrix_count_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left * matrix_count_pre)) ”

noncomputable def matrixChainMinCost_safety_wit_22 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH34 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left)) ,
  (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "best" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def matrixChainMinCost_safety_wit_23 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH34 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "best" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def matrixChainMinCost_safety_wit_24 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH34 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "best" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def matrixChainMinCost_safety_wit_25 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH34 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left)) ,
  ((( &( "split" ) )) # Int |->_)
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "best" ) )) # Int |-> ((((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) + (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int))) + (((Znth left dimensions_l (0 : Int)) * (Znth (left + 1) dimensions_l (0 : Int))) * (Znth (right + 1) dimensions_l (0 : Int))))))
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ ((left + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left + 1)) ”

noncomputable def matrixChainMinCost_safety_wit_26 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH34 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left)) ,
  ((( &( "split" ) )) # Int |->_)
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "best" ) )) # Int |-> ((((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) + (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int))) + (((Znth left dimensions_l (0 : Int)) * (Znth (left + 1) dimensions_l (0 : Int))) * (Znth (right + 1) dimensions_l (0 : Int))))))
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def matrixChainMinCost_safety_wit_27 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1) <= split)) (PreH11 : (split < right)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + split))) (PreH13 : (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= (((split + 1) * matrix_count_pre) + right))) (PreH15 : ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH16 : ((0 : Int) <= left)) (PreH17 : (left < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (split + 1))) (PreH19 : ((split + 1) < (matrix_count_pre + 1))) (PreH20 : ((0 : Int) <= (right + 1))) (PreH21 : ((right + 1) < (matrix_count_pre + 1))) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH26 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)))) (PreH27 : ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000)) (PreH28 : ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH29 : ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH31 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH32 : (1 <= (Znth (split + 1) dimensions_l (0 : Int)))) (PreH33 : ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)) (PreH34 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH35 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH36 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH37 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH39 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH40 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH41 : (1 <= chain_length)) (PreH42 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ ((((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) + (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int))) + (((Znth left dimensions_l (0 : Int)) * (Znth (split + 1) dimensions_l (0 : Int))) * (Znth (right + 1) dimensions_l (0 : Int)))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) + (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int))) + (((Znth left dimensions_l (0 : Int)) * (Znth (split + 1) dimensions_l (0 : Int))) * (Znth (right + 1) dimensions_l (0 : Int))))) ”

noncomputable def matrixChainMinCost_safety_wit_28 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1) <= split)) (PreH11 : (split < right)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + split))) (PreH13 : (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= (((split + 1) * matrix_count_pre) + right))) (PreH15 : ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH16 : ((0 : Int) <= left)) (PreH17 : (left < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (split + 1))) (PreH19 : ((split + 1) < (matrix_count_pre + 1))) (PreH20 : ((0 : Int) <= (right + 1))) (PreH21 : ((right + 1) < (matrix_count_pre + 1))) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH26 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)))) (PreH27 : ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000)) (PreH28 : ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH29 : ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH31 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH32 : (1 <= (Znth (split + 1) dimensions_l (0 : Int)))) (PreH33 : ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)) (PreH34 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH35 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH36 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH37 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH39 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH40 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH41 : (1 <= chain_length)) (PreH42 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ ((((Znth left dimensions_l (0 : Int)) * (Znth (split + 1) dimensions_l (0 : Int))) * (Znth (right + 1) dimensions_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((Znth left dimensions_l (0 : Int)) * (Znth (split + 1) dimensions_l (0 : Int))) * (Znth (right + 1) dimensions_l (0 : Int)))) ”

noncomputable def matrixChainMinCost_safety_wit_29 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1) <= split)) (PreH11 : (split < right)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + split))) (PreH13 : (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= (((split + 1) * matrix_count_pre) + right))) (PreH15 : ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH16 : ((0 : Int) <= left)) (PreH17 : (left < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (split + 1))) (PreH19 : ((split + 1) < (matrix_count_pre + 1))) (PreH20 : ((0 : Int) <= (right + 1))) (PreH21 : ((right + 1) < (matrix_count_pre + 1))) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH26 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)))) (PreH27 : ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000)) (PreH28 : ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH29 : ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH31 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH32 : (1 <= (Znth (split + 1) dimensions_l (0 : Int)))) (PreH33 : ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)) (PreH34 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH35 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH36 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH37 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH39 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH40 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH41 : (1 <= chain_length)) (PreH42 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ ((right + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (right + 1)) ”

noncomputable def matrixChainMinCost_safety_wit_30 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1) <= split)) (PreH11 : (split < right)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + split))) (PreH13 : (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= (((split + 1) * matrix_count_pre) + right))) (PreH15 : ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH16 : ((0 : Int) <= left)) (PreH17 : (left < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (split + 1))) (PreH19 : ((split + 1) < (matrix_count_pre + 1))) (PreH20 : ((0 : Int) <= (right + 1))) (PreH21 : ((right + 1) < (matrix_count_pre + 1))) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH26 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)))) (PreH27 : ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000)) (PreH28 : ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH29 : ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH31 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH32 : (1 <= (Znth (split + 1) dimensions_l (0 : Int)))) (PreH33 : ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)) (PreH34 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH35 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH36 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH37 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH39 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH40 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH41 : (1 <= chain_length)) (PreH42 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ (((Znth left dimensions_l (0 : Int)) * (Znth (split + 1) dimensions_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth left dimensions_l (0 : Int)) * (Znth (split + 1) dimensions_l (0 : Int)))) ”

noncomputable def matrixChainMinCost_safety_wit_31 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1) <= split)) (PreH11 : (split < right)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + split))) (PreH13 : (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= (((split + 1) * matrix_count_pre) + right))) (PreH15 : ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH16 : ((0 : Int) <= left)) (PreH17 : (left < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (split + 1))) (PreH19 : ((split + 1) < (matrix_count_pre + 1))) (PreH20 : ((0 : Int) <= (right + 1))) (PreH21 : ((right + 1) < (matrix_count_pre + 1))) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH26 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)))) (PreH27 : ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000)) (PreH28 : ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH29 : ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH31 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH32 : (1 <= (Znth (split + 1) dimensions_l (0 : Int)))) (PreH33 : ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)) (PreH34 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH35 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH36 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH37 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH39 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH40 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH41 : (1 <= chain_length)) (PreH42 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ ((split + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (split + 1)) ”

noncomputable def matrixChainMinCost_safety_wit_32 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1) <= split)) (PreH11 : (split < right)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + split))) (PreH13 : (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= (((split + 1) * matrix_count_pre) + right))) (PreH15 : ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH16 : ((0 : Int) <= left)) (PreH17 : (left < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (split + 1))) (PreH19 : ((split + 1) < (matrix_count_pre + 1))) (PreH20 : ((0 : Int) <= (right + 1))) (PreH21 : ((right + 1) < (matrix_count_pre + 1))) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH26 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)))) (PreH27 : ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000)) (PreH28 : ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH29 : ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH31 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH32 : (1 <= (Znth (split + 1) dimensions_l (0 : Int)))) (PreH33 : ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)) (PreH34 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH35 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH36 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH37 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH39 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH40 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH41 : (1 <= chain_length)) (PreH42 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ (((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) + (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) + (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) ”

noncomputable def matrixChainMinCost_safety_wit_33 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1) <= split)) (PreH11 : (split < right)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + split))) (PreH13 : (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= (((split + 1) * matrix_count_pre) + right))) (PreH15 : ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH16 : ((0 : Int) <= left)) (PreH17 : (left < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (split + 1))) (PreH19 : ((split + 1) < (matrix_count_pre + 1))) (PreH20 : ((0 : Int) <= (right + 1))) (PreH21 : ((right + 1) < (matrix_count_pre + 1))) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH26 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)))) (PreH27 : ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000)) (PreH28 : ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH29 : ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH31 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH32 : (1 <= (Znth (split + 1) dimensions_l (0 : Int)))) (PreH33 : ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)) (PreH34 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH35 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH36 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH37 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH39 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH40 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH41 : (1 <= chain_length)) (PreH42 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ ((((split + 1) * matrix_count_pre) + right) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((split + 1) * matrix_count_pre) + right)) ”

noncomputable def matrixChainMinCost_safety_wit_34 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1) <= split)) (PreH11 : (split < right)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + split))) (PreH13 : (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= (((split + 1) * matrix_count_pre) + right))) (PreH15 : ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH16 : ((0 : Int) <= left)) (PreH17 : (left < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (split + 1))) (PreH19 : ((split + 1) < (matrix_count_pre + 1))) (PreH20 : ((0 : Int) <= (right + 1))) (PreH21 : ((right + 1) < (matrix_count_pre + 1))) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH26 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)))) (PreH27 : ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000)) (PreH28 : ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH29 : ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH31 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH32 : (1 <= (Znth (split + 1) dimensions_l (0 : Int)))) (PreH33 : ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)) (PreH34 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH35 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH36 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH37 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH39 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH40 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH41 : (1 <= chain_length)) (PreH42 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ (((split + 1) * matrix_count_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((split + 1) * matrix_count_pre)) ”

noncomputable def matrixChainMinCost_safety_wit_35 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1) <= split)) (PreH11 : (split < right)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + split))) (PreH13 : (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= (((split + 1) * matrix_count_pre) + right))) (PreH15 : ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH16 : ((0 : Int) <= left)) (PreH17 : (left < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (split + 1))) (PreH19 : ((split + 1) < (matrix_count_pre + 1))) (PreH20 : ((0 : Int) <= (right + 1))) (PreH21 : ((right + 1) < (matrix_count_pre + 1))) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH26 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)))) (PreH27 : ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000)) (PreH28 : ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH29 : ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH31 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH32 : (1 <= (Znth (split + 1) dimensions_l (0 : Int)))) (PreH33 : ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)) (PreH34 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH35 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH36 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH37 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH39 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH40 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH41 : (1 <= chain_length)) (PreH42 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ ((split + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (split + 1)) ”

noncomputable def matrixChainMinCost_safety_wit_36 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1) <= split)) (PreH11 : (split < right)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + split))) (PreH13 : (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= (((split + 1) * matrix_count_pre) + right))) (PreH15 : ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH16 : ((0 : Int) <= left)) (PreH17 : (left < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (split + 1))) (PreH19 : ((split + 1) < (matrix_count_pre + 1))) (PreH20 : ((0 : Int) <= (right + 1))) (PreH21 : ((right + 1) < (matrix_count_pre + 1))) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH26 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)))) (PreH27 : ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000)) (PreH28 : ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH29 : ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH31 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH32 : (1 <= (Znth (split + 1) dimensions_l (0 : Int)))) (PreH33 : ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)) (PreH34 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH35 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH36 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH37 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH39 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH40 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH41 : (1 <= chain_length)) (PreH42 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ (((left * matrix_count_pre) + split) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((left * matrix_count_pre) + split)) ”

noncomputable def matrixChainMinCost_safety_wit_37 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1) <= split)) (PreH11 : (split < right)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + split))) (PreH13 : (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= (((split + 1) * matrix_count_pre) + right))) (PreH15 : ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH16 : ((0 : Int) <= left)) (PreH17 : (left < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (split + 1))) (PreH19 : ((split + 1) < (matrix_count_pre + 1))) (PreH20 : ((0 : Int) <= (right + 1))) (PreH21 : ((right + 1) < (matrix_count_pre + 1))) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH26 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)))) (PreH27 : ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000)) (PreH28 : ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH29 : ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH31 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH32 : (1 <= (Znth (split + 1) dimensions_l (0 : Int)))) (PreH33 : ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)) (PreH34 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH35 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH36 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH37 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH39 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH40 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH41 : (1 <= chain_length)) (PreH42 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ ((left * matrix_count_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left * matrix_count_pre)) ”

noncomputable def matrixChainMinCost_safety_wit_38 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1) <= split)) (PreH11 : (split < right)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + split))) (PreH13 : (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= (((split + 1) * matrix_count_pre) + right))) (PreH15 : ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH16 : ((0 : Int) <= left)) (PreH17 : (left < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (split + 1))) (PreH19 : ((split + 1) < (matrix_count_pre + 1))) (PreH20 : ((0 : Int) <= (right + 1))) (PreH21 : ((right + 1) < (matrix_count_pre + 1))) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH26 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)))) (PreH27 : ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000)) (PreH28 : ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH29 : ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH31 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH32 : (1 <= (Znth (split + 1) dimensions_l (0 : Int)))) (PreH33 : ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)) (PreH34 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH35 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH36 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH37 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH39 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH40 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH41 : (1 <= chain_length)) (PreH42 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def matrixChainMinCost_safety_wit_39 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1) <= split)) (PreH11 : (split < right)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + split))) (PreH13 : (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= (((split + 1) * matrix_count_pre) + right))) (PreH15 : ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH16 : ((0 : Int) <= left)) (PreH17 : (left < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (split + 1))) (PreH19 : ((split + 1) < (matrix_count_pre + 1))) (PreH20 : ((0 : Int) <= (right + 1))) (PreH21 : ((right + 1) < (matrix_count_pre + 1))) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH26 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)))) (PreH27 : ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000)) (PreH28 : ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH29 : ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH31 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH32 : (1 <= (Znth (split + 1) dimensions_l (0 : Int)))) (PreH33 : ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)) (PreH34 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH35 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH36 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH37 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH39 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH40 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH41 : (1 <= chain_length)) (PreH42 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def matrixChainMinCost_safety_wit_40 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1) <= split)) (PreH11 : (split < right)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + split))) (PreH13 : (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= (((split + 1) * matrix_count_pre) + right))) (PreH15 : ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH16 : ((0 : Int) <= left)) (PreH17 : (left < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (split + 1))) (PreH19 : ((split + 1) < (matrix_count_pre + 1))) (PreH20 : ((0 : Int) <= (right + 1))) (PreH21 : ((right + 1) < (matrix_count_pre + 1))) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH26 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)))) (PreH27 : ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000)) (PreH28 : ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH29 : ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH31 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH32 : (1 <= (Znth (split + 1) dimensions_l (0 : Int)))) (PreH33 : ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)) (PreH34 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH35 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH36 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH37 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH39 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH40 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH41 : (1 <= chain_length)) (PreH42 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "candidate" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def matrixChainMinCost_safety_wit_41 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (candidate : Int) (PreH1 : (candidate < best)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split < right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((0 : Int) <= candidate)) (PreH16 : (candidate <= 7000000)) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH18 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH19 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH20 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH23 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH24 : (MatrixChainSplitCandidate dimensions_l cost_l matrix_count_pre left right split candidate)) (PreH25 : (1 <= chain_length)) (PreH26 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (candidate))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ ((split + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (split + 1)) ”

noncomputable def matrixChainMinCost_safety_wit_42 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (candidate : Int) (PreH1 : (candidate >= best)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split < right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((0 : Int) <= candidate)) (PreH16 : (candidate <= 7000000)) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH18 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH19 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH20 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH23 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH24 : (MatrixChainSplitCandidate dimensions_l cost_l matrix_count_pre left right split candidate)) (PreH25 : (1 <= chain_length)) (PreH26 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "split" ) )) # Int |-> (split))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ ((split + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (split + 1)) ”

noncomputable def matrixChainMinCost_safety_wit_43 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= best)) (PreH11 : (best <= 7000000)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + right))) (PreH13 : (((left * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH15 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH16 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH17 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH18 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH19 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH20 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH21 : (1 <= chain_length)) (PreH22 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left right best)) (PreH23 : (MatrixChainIntervalMinimum dimensions_l left right best)) ,
  ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ (((left * matrix_count_pre) + right) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((left * matrix_count_pre) + right)) ”

noncomputable def matrixChainMinCost_safety_wit_44 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= best)) (PreH11 : (best <= 7000000)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + right))) (PreH13 : (((left * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH15 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH16 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH17 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH18 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH19 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH20 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH21 : (1 <= chain_length)) (PreH22 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left right best)) (PreH23 : (MatrixChainIntervalMinimum dimensions_l left right best)) ,
  ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** ((( &( "right" ) )) # Int |-> (right))
  ** ((( &( "best" ) )) # Int |-> (best))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ ((left * matrix_count_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left * matrix_count_pre)) ”

noncomputable def matrixChainMinCost_safety_wit_45 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= best)) (PreH11 : (best <= 7000000)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + right))) (PreH13 : (((left * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH15 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH16 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH17 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH18 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH19 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH20 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH21 : (1 <= chain_length)) (PreH22 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left right best)) (PreH23 : (MatrixChainIntervalMinimum dimensions_l left right best)) ,
  (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) (replace_Znth (((left * matrix_count_pre) + right)) (best) (cost_l)))
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** ((( &( "left" ) )) # Int |-> (left))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ ((left + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (left + 1)) ”

noncomputable def matrixChainMinCost_safety_wit_46 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (left : Int) (chain_length : Int) (cost_l : (List Int)) (PreH1 : ((left + chain_length) > matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : ((0 : Int) <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length) + 1))) (PreH10 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH12 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH14 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH15 : (1 <= chain_length)) (PreH16 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left)) ,
  ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "chain_length" ) )) # Int |-> (chain_length))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ ((chain_length + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (chain_length + 1)) ”

noncomputable def matrixChainMinCost_safety_wit_47 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (chain_length : Int) (cost_l : (List Int)) (PreH1 : (chain_length > matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= (matrix_count_pre + 1))) (PreH8 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH9 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH10 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH12 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH13 : (1 <= chain_length)) (PreH14 : (MatrixChainLengthsComplete dimensions_l cost_l matrix_count_pre chain_length)) ,
  ((( &( "result" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ ((matrix_count_pre - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (matrix_count_pre - 1)) ”

noncomputable def matrixChainMinCost_safety_wit_48 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (chain_length : Int) (cost_l : (List Int)) (PreH1 : (chain_length > matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= (matrix_count_pre + 1))) (PreH8 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH9 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH10 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH12 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH13 : (1 <= chain_length)) (PreH14 : (MatrixChainLengthsComplete dimensions_l cost_l matrix_count_pre chain_length)) ,
  ((( &( "result" ) )) # Int |->_)
  ** ((( &( "dimensions" ) )) # Ptr |-> (dimensions_pre))
  ** ((( &( "matrix_count" ) )) # Int |-> (matrix_count_pre))
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def matrixChainMinCost_entail_wit_1 : Prop :=
  (
forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH6 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) ,
  (intArray.undef_full ( &( "cost" ) ) 64)
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
|--
  EX cost_l : (List Int),
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) dimensions_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) dimensions_l) ” &&
  “ ((Zlength (cost_l)) = (0 : Int)) ” &&
  “ (Forall (Eq ((0 : Int))) cost_l) ”
  &&  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.seg ( &( "cost" ) ) (0 : Int) (0 : Int) cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (0 : Int) (matrix_count_pre * matrix_count_pre))
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
) \/
(
forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH6 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) ,
  (intArray.undef_full ( &( "cost" ) ) 64)
|--
  “ (Forall (Eq ((0 : Int))) (@List.nil Int)) ” &&
  “ ((Zlength ((@List.nil Int))) = (0 : Int)) ”
  &&  (intArray.undef_seg ( &( "cost" ) ) (0 : Int) (matrix_count_pre * matrix_count_pre))
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
)

noncomputable def matrixChainMinCost_entail_wit_1_split_goal_1 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH6 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) ,
  (intArray.undef_full ( &( "cost" ) ) 64)
|--
  “ (Forall (Eq ((0 : Int))) (@List.nil Int)) ”

noncomputable def matrixChainMinCost_entail_wit_1_split_goal_2 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH6 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) ,
  (intArray.undef_full ( &( "cost" ) ) 64)
|--
  “ ((Zlength ((@List.nil Int))) = (0 : Int)) ”

noncomputable def matrixChainMinCost_entail_wit_1_split_goal_spatial : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH6 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) ,
  (intArray.undef_full ( &( "cost" ) ) 64)
|--
  (intArray.undef_seg ( &( "cost" ) ) (0 : Int) (matrix_count_pre * matrix_count_pre))
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)

noncomputable def matrixChainMinCost_entail_wit_2 : Prop :=
  (
forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l_2 : (List Int)) (i : Int) (PreH1 : (i < (matrix_count_pre * matrix_count_pre))) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= (matrix_count_pre * matrix_count_pre))) (PreH7 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH8 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH9 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH10 : ((Zlength (cost_l_2)) = i)) (PreH11 : (Forall (Eq ((0 : Int))) cost_l_2)) ,
  (intArray.seg ( &( "cost" ) ) (0 : Int) (i + 1) (cost_l_2 ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "cost" ) ) (i + 1) (matrix_count_pre * matrix_count_pre))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  EX cost_l : (List Int),
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) dimensions_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) dimensions_l) ” &&
  “ ((Zlength (cost_l)) = (i + 1)) ” &&
  “ (Forall (Eq ((0 : Int))) cost_l) ”
  &&  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.seg ( &( "cost" ) ) (0 : Int) (i + 1) cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (i + 1) (matrix_count_pre * matrix_count_pre))
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
) \/
(
forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (cost_l_2 : (List Int)) (i : Int) (PreH1 : (i < (matrix_count_pre * matrix_count_pre))) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= (matrix_count_pre * matrix_count_pre))) (PreH7 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH8 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH9 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH10 : ((Zlength (cost_l_2)) = i)) (PreH11 : (Forall (Eq ((0 : Int))) cost_l_2)) ,
  TT && emp 
|--
  “ (Forall (Eq ((0 : Int))) (cost_l_2 ++ ((0 : Int) :: (@List.nil Int)))) ” &&
  “ ((Zlength ((cost_l_2 ++ ((0 : Int) :: (@List.nil Int))))) = (i + 1)) ”
  &&  emp
)

noncomputable def matrixChainMinCost_entail_wit_2_split_goal_1 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (cost_l_2 : (List Int)) (i : Int) (PreH1 : (i < (matrix_count_pre * matrix_count_pre))) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= (matrix_count_pre * matrix_count_pre))) (PreH7 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH8 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH9 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH10 : ((Zlength (cost_l_2)) = i)) (PreH11 : (Forall (Eq ((0 : Int))) cost_l_2)) ,
  (Forall (Eq ((0 : Int))) (cost_l_2 ++ ((0 : Int) :: (@List.nil Int))))

noncomputable def matrixChainMinCost_entail_wit_2_split_goal_2 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (cost_l_2 : (List Int)) (i : Int) (PreH1 : (i < (matrix_count_pre * matrix_count_pre))) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= (matrix_count_pre * matrix_count_pre))) (PreH7 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH8 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH9 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH10 : ((Zlength (cost_l_2)) = i)) (PreH11 : (Forall (Eq ((0 : Int))) cost_l_2)) ,
  ((Zlength ((cost_l_2 ++ ((0 : Int) :: (@List.nil Int))))) = (i + 1))

noncomputable def matrixChainMinCost_entail_wit_3 : Prop :=
  (
forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l_2 : (List Int)) (i : Int) (PreH1 : (i >= (matrix_count_pre * matrix_count_pre))) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= (matrix_count_pre * matrix_count_pre))) (PreH7 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH8 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH9 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH10 : ((Zlength (cost_l_2)) = i)) (PreH11 : (Forall (Eq ((0 : Int))) cost_l_2)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.seg ( &( "cost" ) ) (0 : Int) i cost_l_2)
  ** (intArray.undef_seg ( &( "cost" ) ) i (matrix_count_pre * matrix_count_pre))
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  EX cost_l : (List Int),
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ (2 <= 2) ” &&
  “ (2 <= (matrix_count_pre + 1)) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) dimensions_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) dimensions_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (7000000)) cost_l) ” &&
  “ (1 <= 2) ” &&
  “ (MatrixChainLengthsComplete dimensions_l cost_l matrix_count_pre 2) ”
  &&  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
) \/
(
forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (cost_l_2 : (List Int)) (i : Int) (PreH1 : (i >= (matrix_count_pre * matrix_count_pre))) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= (matrix_count_pre * matrix_count_pre))) (PreH7 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH8 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH9 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH10 : ((Zlength (cost_l_2)) = i)) (PreH11 : (Forall (Eq ((0 : Int))) cost_l_2)) ,
  TT && emp 
|--
  “ (MatrixChainLengthsComplete dimensions_l cost_l_2 matrix_count_pre 2) ” &&
  “ (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2) ”
  &&  emp
)

noncomputable def matrixChainMinCost_entail_wit_3_split_goal_1 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (cost_l_2 : (List Int)) (i : Int) (PreH1 : (i >= (matrix_count_pre * matrix_count_pre))) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= (matrix_count_pre * matrix_count_pre))) (PreH7 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH8 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH9 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH10 : ((Zlength (cost_l_2)) = i)) (PreH11 : (Forall (Eq ((0 : Int))) cost_l_2)) ,
  (MatrixChainLengthsComplete dimensions_l cost_l_2 matrix_count_pre 2)

noncomputable def matrixChainMinCost_entail_wit_3_split_goal_2 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (cost_l_2 : (List Int)) (i : Int) (PreH1 : (i >= (matrix_count_pre * matrix_count_pre))) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= (matrix_count_pre * matrix_count_pre))) (PreH7 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH8 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH9 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH10 : ((Zlength (cost_l_2)) = i)) (PreH11 : (Forall (Eq ((0 : Int))) cost_l_2)) ,
  (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)

noncomputable def matrixChainMinCost_entail_wit_3_split_goal_3 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (cost_l_2 : (List Int)) (i : Int) (PreH1 : (i >= (matrix_count_pre * matrix_count_pre))) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= (matrix_count_pre * matrix_count_pre))) (PreH7 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH8 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH9 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH10 : ((Zlength (cost_l_2)) = i)) (PreH11 : (Forall (Eq ((0 : Int))) cost_l_2)) ,
  (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)

noncomputable def matrixChainMinCost_entail_wit_4 : Prop :=
  (
forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : (chain_length <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= (matrix_count_pre + 1))) (PreH8 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH9 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH10 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH12 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH13 : (1 <= chain_length)) (PreH14 : (MatrixChainLengthsComplete dimensions_l cost_l_2 matrix_count_pre chain_length)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l_2)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  EX cost_l : (List Int),
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ (2 <= chain_length) ” &&
  “ (chain_length <= matrix_count_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= ((matrix_count_pre - chain_length) + 1)) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) dimensions_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) dimensions_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (7000000)) cost_l) ” &&
  “ (1 <= chain_length) ” &&
  “ (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length (0 : Int)) ”
  &&  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
) \/
(
forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : (chain_length <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= (matrix_count_pre + 1))) (PreH8 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH9 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH10 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH12 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH13 : (1 <= chain_length)) (PreH14 : (MatrixChainLengthsComplete dimensions_l cost_l_2 matrix_count_pre chain_length)) ,
  TT && emp 
|--
  “ (MatrixChainLeftComplete dimensions_l cost_l_2 matrix_count_pre chain_length (0 : Int)) ”
  &&  emp
)

noncomputable def matrixChainMinCost_entail_wit_4_split_goal_1 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : (chain_length <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= (matrix_count_pre + 1))) (PreH8 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH9 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH10 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH12 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH13 : (1 <= chain_length)) (PreH14 : (MatrixChainLengthsComplete dimensions_l cost_l_2 matrix_count_pre chain_length)) ,
  (MatrixChainLeftComplete dimensions_l cost_l_2 matrix_count_pre chain_length (0 : Int))

noncomputable def matrixChainMinCost_entail_wit_5 : Prop :=
  (
forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (left : Int) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : ((left + chain_length) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : ((0 : Int) <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length) + 1))) (PreH10 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH12 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH14 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH15 : (1 <= chain_length)) (PreH16 : (MatrixChainLeftComplete dimensions_l cost_l_2 matrix_count_pre chain_length left)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l_2)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  EX cost_l : (List Int),
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ (2 <= chain_length) ” &&
  “ (chain_length <= matrix_count_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + chain_length) <= matrix_count_pre) ” &&
  “ (((left + chain_length) - 1) = ((left + chain_length) - 1)) ” &&
  “ (left < ((left + chain_length) - 1)) ” &&
  “ (((left + chain_length) - 1) < matrix_count_pre) ” &&
  “ ((0 : Int) <= ((left * matrix_count_pre) + left)) ” &&
  “ (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (((left + 1) * matrix_count_pre) + ((left + chain_length) - 1))) ” &&
  “ ((((left + 1) * matrix_count_pre) + ((left + chain_length) - 1)) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (left + 1)) ” &&
  “ ((left + 1) < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (((left + chain_length) - 1) + 1)) ” &&
  “ ((((left + chain_length) - 1) + 1) < (matrix_count_pre + 1)) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int))) ” &&
  “ ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000) ” &&
  “ ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + ((left + chain_length) - 1)) cost_l (0 : Int))) ” &&
  “ ((Znth (((left + 1) * matrix_count_pre) + ((left + chain_length) - 1)) cost_l (0 : Int)) <= 7000000) ” &&
  “ (1 <= (Znth left dimensions_l (0 : Int))) ” &&
  “ ((Znth left dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (left + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (left + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (((left + chain_length) - 1) + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (((left + chain_length) - 1) + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) dimensions_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) dimensions_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (7000000)) cost_l) ” &&
  “ (1 <= chain_length) ” &&
  “ (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left) ”
  &&  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
) \/
(
forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (left : Int) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : ((left + chain_length) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : ((0 : Int) <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length) + 1))) (PreH10 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH12 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH14 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH15 : (1 <= chain_length)) (PreH16 : (MatrixChainLeftComplete dimensions_l cost_l_2 matrix_count_pre chain_length left)) ,
  TT && emp 
|--
  “ ((Znth (((left + chain_length) - 1) + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (((left + chain_length) - 1) + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (left + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (left + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth left dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth left dimensions_l (0 : Int))) ” &&
  “ ((Znth (((left + 1) * matrix_count_pre) + ((left + chain_length) - 1)) cost_l_2 (0 : Int)) <= 7000000) ” &&
  “ ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + ((left + chain_length) - 1)) cost_l_2 (0 : Int))) ” &&
  “ ((Znth ((left * matrix_count_pre) + left) cost_l_2 (0 : Int)) <= 7000000) ” &&
  “ ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l_2 (0 : Int))) ” &&
  “ ((((left + 1) * matrix_count_pre) + ((left + chain_length) - 1)) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre)) ”
  &&  emp
)

noncomputable def matrixChainMinCost_entail_wit_5_split_goal_1 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (left : Int) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : ((left + chain_length) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : ((0 : Int) <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length) + 1))) (PreH10 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH12 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH14 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH15 : (1 <= chain_length)) (PreH16 : (MatrixChainLeftComplete dimensions_l cost_l_2 matrix_count_pre chain_length left)) ,
  ((Znth (((left + chain_length) - 1) + 1) dimensions_l (0 : Int)) <= 100)

noncomputable def matrixChainMinCost_entail_wit_5_split_goal_2 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (left : Int) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : ((left + chain_length) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : ((0 : Int) <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length) + 1))) (PreH10 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH12 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH14 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH15 : (1 <= chain_length)) (PreH16 : (MatrixChainLeftComplete dimensions_l cost_l_2 matrix_count_pre chain_length left)) ,
  (1 <= (Znth (((left + chain_length) - 1) + 1) dimensions_l (0 : Int)))

noncomputable def matrixChainMinCost_entail_wit_5_split_goal_3 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (left : Int) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : ((left + chain_length) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : ((0 : Int) <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length) + 1))) (PreH10 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH12 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH14 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH15 : (1 <= chain_length)) (PreH16 : (MatrixChainLeftComplete dimensions_l cost_l_2 matrix_count_pre chain_length left)) ,
  ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)

noncomputable def matrixChainMinCost_entail_wit_5_split_goal_4 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (left : Int) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : ((left + chain_length) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : ((0 : Int) <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length) + 1))) (PreH10 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH12 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH14 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH15 : (1 <= chain_length)) (PreH16 : (MatrixChainLeftComplete dimensions_l cost_l_2 matrix_count_pre chain_length left)) ,
  (1 <= (Znth (left + 1) dimensions_l (0 : Int)))

noncomputable def matrixChainMinCost_entail_wit_5_split_goal_5 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (left : Int) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : ((left + chain_length) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : ((0 : Int) <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length) + 1))) (PreH10 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH12 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH14 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH15 : (1 <= chain_length)) (PreH16 : (MatrixChainLeftComplete dimensions_l cost_l_2 matrix_count_pre chain_length left)) ,
  ((Znth left dimensions_l (0 : Int)) <= 100)

noncomputable def matrixChainMinCost_entail_wit_5_split_goal_6 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (left : Int) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : ((left + chain_length) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : ((0 : Int) <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length) + 1))) (PreH10 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH12 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH14 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH15 : (1 <= chain_length)) (PreH16 : (MatrixChainLeftComplete dimensions_l cost_l_2 matrix_count_pre chain_length left)) ,
  (1 <= (Znth left dimensions_l (0 : Int)))

noncomputable def matrixChainMinCost_entail_wit_5_split_goal_7 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (left : Int) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : ((left + chain_length) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : ((0 : Int) <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length) + 1))) (PreH10 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH12 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH14 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH15 : (1 <= chain_length)) (PreH16 : (MatrixChainLeftComplete dimensions_l cost_l_2 matrix_count_pre chain_length left)) ,
  ((Znth (((left + 1) * matrix_count_pre) + ((left + chain_length) - 1)) cost_l_2 (0 : Int)) <= 7000000)

noncomputable def matrixChainMinCost_entail_wit_5_split_goal_8 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (left : Int) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : ((left + chain_length) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : ((0 : Int) <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length) + 1))) (PreH10 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH12 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH14 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH15 : (1 <= chain_length)) (PreH16 : (MatrixChainLeftComplete dimensions_l cost_l_2 matrix_count_pre chain_length left)) ,
  ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + ((left + chain_length) - 1)) cost_l_2 (0 : Int)))

noncomputable def matrixChainMinCost_entail_wit_5_split_goal_9 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (left : Int) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : ((left + chain_length) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : ((0 : Int) <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length) + 1))) (PreH10 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH12 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH14 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH15 : (1 <= chain_length)) (PreH16 : (MatrixChainLeftComplete dimensions_l cost_l_2 matrix_count_pre chain_length left)) ,
  ((Znth ((left * matrix_count_pre) + left) cost_l_2 (0 : Int)) <= 7000000)

noncomputable def matrixChainMinCost_entail_wit_5_split_goal_10 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (left : Int) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : ((left + chain_length) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : ((0 : Int) <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length) + 1))) (PreH10 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH12 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH14 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH15 : (1 <= chain_length)) (PreH16 : (MatrixChainLeftComplete dimensions_l cost_l_2 matrix_count_pre chain_length left)) ,
  ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l_2 (0 : Int)))

noncomputable def matrixChainMinCost_entail_wit_5_split_goal_11 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (left : Int) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : ((left + chain_length) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : ((0 : Int) <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length) + 1))) (PreH10 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH12 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH14 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH15 : (1 <= chain_length)) (PreH16 : (MatrixChainLeftComplete dimensions_l cost_l_2 matrix_count_pre chain_length left)) ,
  ((((left + 1) * matrix_count_pre) + ((left + chain_length) - 1)) < (matrix_count_pre * matrix_count_pre))

noncomputable def matrixChainMinCost_entail_wit_5_split_goal_12 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (left : Int) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : ((left + chain_length) <= matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : ((0 : Int) <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length) + 1))) (PreH10 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH12 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH14 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH15 : (1 <= chain_length)) (PreH16 : (MatrixChainLeftComplete dimensions_l cost_l_2 matrix_count_pre chain_length left)) ,
  (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))

noncomputable def matrixChainMinCost_entail_wit_6 : Prop :=
  (
forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH34 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  EX cost_l_2 : (List Int),
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ (2 <= chain_length) ” &&
  “ (chain_length <= matrix_count_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + chain_length) <= matrix_count_pre) ” &&
  “ (right = ((left + chain_length) - 1)) ” &&
  “ (left < right) ” &&
  “ (right < matrix_count_pre) ” &&
  “ ((left + 1) <= (left + 1)) ” &&
  “ ((left + 1) <= right) ” &&
  “ ((0 : Int) <= (((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) + (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int))) + (((Znth left dimensions_l (0 : Int)) * (Znth (left + 1) dimensions_l (0 : Int))) * (Znth (right + 1) dimensions_l (0 : Int))))) ” &&
  “ ((((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) + (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int))) + (((Znth left dimensions_l (0 : Int)) * (Znth (left + 1) dimensions_l (0 : Int))) * (Znth (right + 1) dimensions_l (0 : Int)))) <= 7000000) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) dimensions_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) dimensions_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2) ” &&
  “ (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2) ” &&
  “ (1 <= chain_length) ” &&
  “ (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left (left + 1) (((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) + (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int))) + (((Znth left dimensions_l (0 : Int)) * (Znth (left + 1) dimensions_l (0 : Int))) * (Znth (right + 1) dimensions_l (0 : Int))))) ”
  &&  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l_2)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
) \/
(
forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH34 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left)) ,
  TT && emp 
|--
  “ (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left (left + 1) (((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) + (Znth (((left + 1) * matrix_count_pre) + ((left + chain_length) - 1)) cost_l (0 : Int))) + (((Znth left dimensions_l (0 : Int)) * (Znth (left + 1) dimensions_l (0 : Int))) * (Znth (((left + chain_length) - 1) + 1) dimensions_l (0 : Int))))) ” &&
  “ ((((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) + (Znth (((left + 1) * matrix_count_pre) + ((left + chain_length) - 1)) cost_l (0 : Int))) + (((Znth left dimensions_l (0 : Int)) * (Znth (left + 1) dimensions_l (0 : Int))) * (Znth (((left + chain_length) - 1) + 1) dimensions_l (0 : Int)))) <= 7000000) ”
  &&  emp
)

noncomputable def matrixChainMinCost_entail_wit_6_split_goal_1 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH34 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left)) ,
  (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left (left + 1) (((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) + (Znth (((left + 1) * matrix_count_pre) + ((left + chain_length) - 1)) cost_l (0 : Int))) + (((Znth left dimensions_l (0 : Int)) * (Znth (left + 1) dimensions_l (0 : Int))) * (Znth (((left + chain_length) - 1) + 1) dimensions_l (0 : Int)))))

noncomputable def matrixChainMinCost_entail_wit_6_split_goal_2 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH34 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left)) ,
  ((((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) + (Znth (((left + 1) * matrix_count_pre) + ((left + chain_length) - 1)) cost_l (0 : Int))) + (((Znth left dimensions_l (0 : Int)) * (Znth (left + 1) dimensions_l (0 : Int))) * (Znth (((left + chain_length) - 1) + 1) dimensions_l (0 : Int)))) <= 7000000)

noncomputable def matrixChainMinCost_entail_wit_7 : Prop :=
  (
forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (chain_length : Int) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split <= right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH18 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH21 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH22 : (1 <= chain_length)) (PreH23 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l_2)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  EX cost_l : (List Int),
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ (2 <= chain_length) ” &&
  “ (chain_length <= matrix_count_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + chain_length) <= matrix_count_pre) ” &&
  “ (right = ((left + chain_length) - 1)) ” &&
  “ (left < right) ” &&
  “ (right < matrix_count_pre) ” &&
  “ ((left + 1) <= split) ” &&
  “ (split < right) ” &&
  “ ((0 : Int) <= ((left * matrix_count_pre) + split)) ” &&
  “ (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (((split + 1) * matrix_count_pre) + right)) ” &&
  “ ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (split + 1)) ” &&
  “ ((split + 1) < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (right + 1)) ” &&
  “ ((right + 1) < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 7000000) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int))) ” &&
  “ ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000) ” &&
  “ ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int))) ” &&
  “ ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000) ” &&
  “ (1 <= (Znth left dimensions_l (0 : Int))) ” &&
  “ ((Znth left dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (split + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (split + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (right + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (right + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) dimensions_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) dimensions_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (7000000)) cost_l) ” &&
  “ (1 <= chain_length) ” &&
  “ (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best) ”
  &&  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
) \/
(
forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (cost_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (chain_length : Int) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split <= right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH18 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH21 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH22 : (1 <= chain_length)) (PreH23 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  TT && emp 
|--
  “ ((Znth (((left + chain_length) - 1) + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (((left + chain_length) - 1) + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (split + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (split + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth left dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth left dimensions_l (0 : Int))) ” &&
  “ ((Znth (((split + 1) * matrix_count_pre) + ((left + chain_length) - 1)) cost_l_2 (0 : Int)) <= 7000000) ” &&
  “ ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + ((left + chain_length) - 1)) cost_l_2 (0 : Int))) ” &&
  “ ((Znth ((left * matrix_count_pre) + split) cost_l_2 (0 : Int)) <= 7000000) ” &&
  “ ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l_2 (0 : Int))) ” &&
  “ ((((split + 1) * matrix_count_pre) + ((left + chain_length) - 1)) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre)) ”
  &&  emp
)

noncomputable def matrixChainMinCost_entail_wit_7_split_goal_1 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (cost_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (chain_length : Int) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split <= right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH18 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH21 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH22 : (1 <= chain_length)) (PreH23 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  ((Znth (((left + chain_length) - 1) + 1) dimensions_l (0 : Int)) <= 100)

noncomputable def matrixChainMinCost_entail_wit_7_split_goal_2 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (cost_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (chain_length : Int) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split <= right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH18 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH21 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH22 : (1 <= chain_length)) (PreH23 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (1 <= (Znth (((left + chain_length) - 1) + 1) dimensions_l (0 : Int)))

noncomputable def matrixChainMinCost_entail_wit_7_split_goal_3 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (cost_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (chain_length : Int) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split <= right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH18 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH21 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH22 : (1 <= chain_length)) (PreH23 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)

noncomputable def matrixChainMinCost_entail_wit_7_split_goal_4 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (cost_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (chain_length : Int) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split <= right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH18 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH21 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH22 : (1 <= chain_length)) (PreH23 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (1 <= (Znth (split + 1) dimensions_l (0 : Int)))

noncomputable def matrixChainMinCost_entail_wit_7_split_goal_5 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (cost_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (chain_length : Int) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split <= right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH18 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH21 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH22 : (1 <= chain_length)) (PreH23 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  ((Znth left dimensions_l (0 : Int)) <= 100)

noncomputable def matrixChainMinCost_entail_wit_7_split_goal_6 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (cost_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (chain_length : Int) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split <= right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH18 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH21 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH22 : (1 <= chain_length)) (PreH23 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (1 <= (Znth left dimensions_l (0 : Int)))

noncomputable def matrixChainMinCost_entail_wit_7_split_goal_7 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (cost_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (chain_length : Int) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split <= right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH18 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH21 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH22 : (1 <= chain_length)) (PreH23 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  ((Znth (((split + 1) * matrix_count_pre) + ((left + chain_length) - 1)) cost_l_2 (0 : Int)) <= 7000000)

noncomputable def matrixChainMinCost_entail_wit_7_split_goal_8 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (cost_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (chain_length : Int) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split <= right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH18 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH21 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH22 : (1 <= chain_length)) (PreH23 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + ((left + chain_length) - 1)) cost_l_2 (0 : Int)))

noncomputable def matrixChainMinCost_entail_wit_7_split_goal_9 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (cost_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (chain_length : Int) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split <= right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH18 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH21 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH22 : (1 <= chain_length)) (PreH23 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  ((Znth ((left * matrix_count_pre) + split) cost_l_2 (0 : Int)) <= 7000000)

noncomputable def matrixChainMinCost_entail_wit_7_split_goal_10 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (cost_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (chain_length : Int) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split <= right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH18 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH21 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH22 : (1 <= chain_length)) (PreH23 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l_2 (0 : Int)))

noncomputable def matrixChainMinCost_entail_wit_7_split_goal_11 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (cost_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (chain_length : Int) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split <= right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH18 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH21 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH22 : (1 <= chain_length)) (PreH23 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  ((((split + 1) * matrix_count_pre) + ((left + chain_length) - 1)) < (matrix_count_pre * matrix_count_pre))

noncomputable def matrixChainMinCost_entail_wit_7_split_goal_12 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (cost_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (chain_length : Int) (PreH1 : (split < right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split <= right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH18 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH21 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH22 : (1 <= chain_length)) (PreH23 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))

noncomputable def matrixChainMinCost_entail_wit_8 : Prop :=
  (
forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1) <= split)) (PreH11 : (split < right)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + split))) (PreH13 : (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= (((split + 1) * matrix_count_pre) + right))) (PreH15 : ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH16 : ((0 : Int) <= left)) (PreH17 : (left < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (split + 1))) (PreH19 : ((split + 1) < (matrix_count_pre + 1))) (PreH20 : ((0 : Int) <= (right + 1))) (PreH21 : ((right + 1) < (matrix_count_pre + 1))) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH26 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)))) (PreH27 : ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000)) (PreH28 : ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH29 : ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH31 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH32 : (1 <= (Znth (split + 1) dimensions_l (0 : Int)))) (PreH33 : ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)) (PreH34 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH35 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH36 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH37 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH39 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH40 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH41 : (1 <= chain_length)) (PreH42 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  EX cost_l_2 : (List Int),
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ (2 <= chain_length) ” &&
  “ (chain_length <= matrix_count_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + chain_length) <= matrix_count_pre) ” &&
  “ (right = ((left + chain_length) - 1)) ” &&
  “ (left < right) ” &&
  “ (right < matrix_count_pre) ” &&
  “ ((left + 1) <= split) ” &&
  “ (split < right) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 7000000) ” &&
  “ ((0 : Int) <= (((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) + (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int))) + (((Znth left dimensions_l (0 : Int)) * (Znth (split + 1) dimensions_l (0 : Int))) * (Znth (right + 1) dimensions_l (0 : Int))))) ” &&
  “ ((((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) + (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int))) + (((Znth left dimensions_l (0 : Int)) * (Znth (split + 1) dimensions_l (0 : Int))) * (Znth (right + 1) dimensions_l (0 : Int)))) <= 7000000) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) dimensions_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) dimensions_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2) ” &&
  “ (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2) ” &&
  “ (MatrixChainSplitCandidate dimensions_l cost_l_2 matrix_count_pre left right split (((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) + (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int))) + (((Znth left dimensions_l (0 : Int)) * (Znth (split + 1) dimensions_l (0 : Int))) * (Znth (right + 1) dimensions_l (0 : Int))))) ” &&
  “ (1 <= chain_length) ” &&
  “ (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best) ”
  &&  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l_2)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
) \/
(
forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1) <= split)) (PreH11 : (split < right)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + split))) (PreH13 : (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= (((split + 1) * matrix_count_pre) + right))) (PreH15 : ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH16 : ((0 : Int) <= left)) (PreH17 : (left < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (split + 1))) (PreH19 : ((split + 1) < (matrix_count_pre + 1))) (PreH20 : ((0 : Int) <= (right + 1))) (PreH21 : ((right + 1) < (matrix_count_pre + 1))) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH26 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)))) (PreH27 : ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000)) (PreH28 : ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH29 : ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH31 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH32 : (1 <= (Znth (split + 1) dimensions_l (0 : Int)))) (PreH33 : ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)) (PreH34 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH35 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH36 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH37 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH39 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH40 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH41 : (1 <= chain_length)) (PreH42 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  TT && emp 
|--
  “ (MatrixChainSplitCandidate dimensions_l cost_l matrix_count_pre left ((left + chain_length) - 1) split (((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) + (Znth (((split + 1) * matrix_count_pre) + ((left + chain_length) - 1)) cost_l (0 : Int))) + (((Znth left dimensions_l (0 : Int)) * (Znth (split + 1) dimensions_l (0 : Int))) * (Znth (((left + chain_length) - 1) + 1) dimensions_l (0 : Int))))) ” &&
  “ ((((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) + (Znth (((split + 1) * matrix_count_pre) + ((left + chain_length) - 1)) cost_l (0 : Int))) + (((Znth left dimensions_l (0 : Int)) * (Znth (split + 1) dimensions_l (0 : Int))) * (Znth (((left + chain_length) - 1) + 1) dimensions_l (0 : Int)))) <= 7000000) ”
  &&  emp
)

noncomputable def matrixChainMinCost_entail_wit_8_split_goal_1 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1) <= split)) (PreH11 : (split < right)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + split))) (PreH13 : (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= (((split + 1) * matrix_count_pre) + right))) (PreH15 : ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH16 : ((0 : Int) <= left)) (PreH17 : (left < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (split + 1))) (PreH19 : ((split + 1) < (matrix_count_pre + 1))) (PreH20 : ((0 : Int) <= (right + 1))) (PreH21 : ((right + 1) < (matrix_count_pre + 1))) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH26 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)))) (PreH27 : ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000)) (PreH28 : ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH29 : ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH31 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH32 : (1 <= (Znth (split + 1) dimensions_l (0 : Int)))) (PreH33 : ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)) (PreH34 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH35 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH36 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH37 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH39 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH40 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH41 : (1 <= chain_length)) (PreH42 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (MatrixChainSplitCandidate dimensions_l cost_l matrix_count_pre left ((left + chain_length) - 1) split (((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) + (Znth (((split + 1) * matrix_count_pre) + ((left + chain_length) - 1)) cost_l (0 : Int))) + (((Znth left dimensions_l (0 : Int)) * (Znth (split + 1) dimensions_l (0 : Int))) * (Znth (((left + chain_length) - 1) + 1) dimensions_l (0 : Int)))))

noncomputable def matrixChainMinCost_entail_wit_8_split_goal_2 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1) <= split)) (PreH11 : (split < right)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + split))) (PreH13 : (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= (((split + 1) * matrix_count_pre) + right))) (PreH15 : ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH16 : ((0 : Int) <= left)) (PreH17 : (left < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (split + 1))) (PreH19 : ((split + 1) < (matrix_count_pre + 1))) (PreH20 : ((0 : Int) <= (right + 1))) (PreH21 : ((right + 1) < (matrix_count_pre + 1))) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH26 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)))) (PreH27 : ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000)) (PreH28 : ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH29 : ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH31 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH32 : (1 <= (Znth (split + 1) dimensions_l (0 : Int)))) (PreH33 : ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)) (PreH34 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH35 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH36 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH37 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH39 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH40 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH41 : (1 <= chain_length)) (PreH42 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  ((((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) + (Znth (((split + 1) * matrix_count_pre) + ((left + chain_length) - 1)) cost_l (0 : Int))) + (((Znth left dimensions_l (0 : Int)) * (Znth (split + 1) dimensions_l (0 : Int))) * (Znth (((left + chain_length) - 1) + 1) dimensions_l (0 : Int)))) <= 7000000)

noncomputable def matrixChainMinCost_entail_wit_9_1 : Prop :=
  (
forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l_2 : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (candidate : Int) (PreH1 : (candidate < best)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split < right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((0 : Int) <= candidate)) (PreH16 : (candidate <= 7000000)) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH18 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH19 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH20 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH23 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH24 : (MatrixChainSplitCandidate dimensions_l cost_l_2 matrix_count_pre left right split candidate)) (PreH25 : (1 <= chain_length)) (PreH26 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l_2)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  EX cost_l : (List Int),
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ (2 <= chain_length) ” &&
  “ (chain_length <= matrix_count_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + chain_length) <= matrix_count_pre) ” &&
  “ (right = ((left + chain_length) - 1)) ” &&
  “ (left < right) ” &&
  “ (right < matrix_count_pre) ” &&
  “ ((left + 1) <= (split + 1)) ” &&
  “ ((split + 1) <= right) ” &&
  “ ((0 : Int) <= candidate) ” &&
  “ (candidate <= 7000000) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) dimensions_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) dimensions_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (7000000)) cost_l) ” &&
  “ (1 <= chain_length) ” &&
  “ (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left (split + 1) candidate) ”
  &&  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
) \/
(
forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (cost_l_2 : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (candidate : Int) (PreH1 : (candidate < best)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split < right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((0 : Int) <= candidate)) (PreH16 : (candidate <= 7000000)) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH18 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH19 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH20 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH23 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH24 : (MatrixChainSplitCandidate dimensions_l cost_l_2 matrix_count_pre left right split candidate)) (PreH25 : (1 <= chain_length)) (PreH26 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  TT && emp 
|--
  “ (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left (split + 1) candidate) ”
  &&  emp
)

noncomputable def matrixChainMinCost_entail_wit_9_1_split_goal_1 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (cost_l_2 : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (candidate : Int) (PreH1 : (candidate < best)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split < right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((0 : Int) <= candidate)) (PreH16 : (candidate <= 7000000)) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH18 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH19 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH20 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH23 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH24 : (MatrixChainSplitCandidate dimensions_l cost_l_2 matrix_count_pre left right split candidate)) (PreH25 : (1 <= chain_length)) (PreH26 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left (split + 1) candidate)

noncomputable def matrixChainMinCost_entail_wit_9_2 : Prop :=
  (
forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l_2 : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (candidate : Int) (PreH1 : (candidate >= best)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split < right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((0 : Int) <= candidate)) (PreH16 : (candidate <= 7000000)) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH18 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH19 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH20 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH23 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH24 : (MatrixChainSplitCandidate dimensions_l cost_l_2 matrix_count_pre left right split candidate)) (PreH25 : (1 <= chain_length)) (PreH26 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l_2)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  EX cost_l : (List Int),
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ (2 <= chain_length) ” &&
  “ (chain_length <= matrix_count_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + chain_length) <= matrix_count_pre) ” &&
  “ (right = ((left + chain_length) - 1)) ” &&
  “ (left < right) ” &&
  “ (right < matrix_count_pre) ” &&
  “ ((left + 1) <= (split + 1)) ” &&
  “ ((split + 1) <= right) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 7000000) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) dimensions_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) dimensions_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (7000000)) cost_l) ” &&
  “ (1 <= chain_length) ” &&
  “ (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left (split + 1) best) ”
  &&  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
) \/
(
forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (cost_l_2 : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (candidate : Int) (PreH1 : (candidate >= best)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split < right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((0 : Int) <= candidate)) (PreH16 : (candidate <= 7000000)) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH18 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH19 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH20 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH23 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH24 : (MatrixChainSplitCandidate dimensions_l cost_l_2 matrix_count_pre left right split candidate)) (PreH25 : (1 <= chain_length)) (PreH26 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  TT && emp 
|--
  “ (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left (split + 1) best) ”
  &&  emp
)

noncomputable def matrixChainMinCost_entail_wit_9_2_split_goal_1 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (cost_l_2 : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (candidate : Int) (PreH1 : (candidate >= best)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split < right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((0 : Int) <= candidate)) (PreH16 : (candidate <= 7000000)) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH18 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH19 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH20 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH21 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH23 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH24 : (MatrixChainSplitCandidate dimensions_l cost_l_2 matrix_count_pre left right split candidate)) (PreH25 : (1 <= chain_length)) (PreH26 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left (split + 1) best)

noncomputable def matrixChainMinCost_entail_wit_10 : Prop :=
  (
forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (chain_length : Int) (PreH1 : (split >= right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split <= right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH18 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH21 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH22 : (1 <= chain_length)) (PreH23 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l_2)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  EX cost_l : (List Int),
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ (2 <= chain_length) ” &&
  “ (chain_length <= matrix_count_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + chain_length) <= matrix_count_pre) ” &&
  “ (right = ((left + chain_length) - 1)) ” &&
  “ (left < right) ” &&
  “ (right < matrix_count_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 7000000) ” &&
  “ ((0 : Int) <= ((left * matrix_count_pre) + right)) ” &&
  “ (((left * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) dimensions_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) dimensions_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (7000000)) cost_l) ” &&
  “ (1 <= chain_length) ” &&
  “ (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left right best) ” &&
  “ (MatrixChainIntervalMinimum dimensions_l left right best) ”
  &&  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
) \/
(
forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (cost_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (chain_length : Int) (PreH1 : (split >= right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split <= right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH18 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH21 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH22 : (1 <= chain_length)) (PreH23 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  TT && emp 
|--
  “ (MatrixChainIntervalMinimum dimensions_l left ((left + chain_length) - 1) best) ” &&
  “ (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left ((left + chain_length) - 1) best) ” &&
  “ (((left * matrix_count_pre) + ((left + chain_length) - 1)) < (matrix_count_pre * matrix_count_pre)) ”
  &&  emp
)

noncomputable def matrixChainMinCost_entail_wit_10_split_goal_1 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (cost_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (chain_length : Int) (PreH1 : (split >= right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split <= right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH18 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH21 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH22 : (1 <= chain_length)) (PreH23 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (MatrixChainIntervalMinimum dimensions_l left ((left + chain_length) - 1) best)

noncomputable def matrixChainMinCost_entail_wit_10_split_goal_2 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (cost_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (chain_length : Int) (PreH1 : (split >= right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split <= right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH18 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH21 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH22 : (1 <= chain_length)) (PreH23 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left ((left + chain_length) - 1) best)

noncomputable def matrixChainMinCost_entail_wit_10_split_goal_3 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (cost_l_2 : (List Int)) (best : Int) (split : Int) (right : Int) (left : Int) (chain_length : Int) (PreH1 : (split >= right)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : (2 <= chain_length)) (PreH5 : (chain_length <= matrix_count_pre)) (PreH6 : ((0 : Int) <= left)) (PreH7 : ((left + chain_length) <= matrix_count_pre)) (PreH8 : (right = ((left + chain_length) - 1))) (PreH9 : (left < right)) (PreH10 : (right < matrix_count_pre)) (PreH11 : ((left + 1) <= split)) (PreH12 : (split <= right)) (PreH13 : ((0 : Int) <= best)) (PreH14 : (best <= 7000000)) (PreH15 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH16 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH17 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH18 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH19 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH20 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH21 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH22 : (1 <= chain_length)) (PreH23 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (((left * matrix_count_pre) + ((left + chain_length) - 1)) < (matrix_count_pre * matrix_count_pre))

noncomputable def matrixChainMinCost_entail_wit_11 : Prop :=
  (
forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l_2 : (List Int)) (chain_length : Int) (left : Int) (right : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= best)) (PreH11 : (best <= 7000000)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + right))) (PreH13 : (((left * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH15 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH16 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH17 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH18 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH19 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH20 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH21 : (1 <= chain_length)) (PreH22 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left right best)) (PreH23 : (MatrixChainIntervalMinimum dimensions_l left right best)) ,
  (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) (replace_Znth (((left * matrix_count_pre) + right)) (best) (cost_l_2)))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  EX cost_l : (List Int),
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ (2 <= chain_length) ” &&
  “ (chain_length <= matrix_count_pre) ” &&
  “ ((0 : Int) <= (left + 1)) ” &&
  “ ((left + 1) <= ((matrix_count_pre - chain_length) + 1)) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) dimensions_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) dimensions_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (7000000)) cost_l) ” &&
  “ (1 <= chain_length) ” &&
  “ (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length (left + 1)) ”
  &&  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
) \/
(
forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (cost_l_2 : (List Int)) (chain_length : Int) (left : Int) (right : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= best)) (PreH11 : (best <= 7000000)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + right))) (PreH13 : (((left * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH15 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH16 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH17 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH18 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH19 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH20 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH21 : (1 <= chain_length)) (PreH22 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left right best)) (PreH23 : (MatrixChainIntervalMinimum dimensions_l left right best)) ,
  TT && emp 
|--
  “ (MatrixChainLeftComplete dimensions_l (replace_Znth (((left * matrix_count_pre) + ((left + chain_length) - 1))) (best) (cost_l_2)) matrix_count_pre chain_length (left + 1)) ” &&
  “ (Forall ((GE.ge (α := Int)) (7000000)) (replace_Znth (((left * matrix_count_pre) + ((left + chain_length) - 1))) (best) (cost_l_2))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (replace_Znth (((left * matrix_count_pre) + ((left + chain_length) - 1))) (best) (cost_l_2))) ” &&
  “ ((Zlength ((replace_Znth (((left * matrix_count_pre) + ((left + chain_length) - 1))) (best) (cost_l_2)))) = (matrix_count_pre * matrix_count_pre)) ”
  &&  emp
)

noncomputable def matrixChainMinCost_entail_wit_11_split_goal_1 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (cost_l_2 : (List Int)) (chain_length : Int) (left : Int) (right : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= best)) (PreH11 : (best <= 7000000)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + right))) (PreH13 : (((left * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH15 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH16 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH17 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH18 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH19 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH20 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH21 : (1 <= chain_length)) (PreH22 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left right best)) (PreH23 : (MatrixChainIntervalMinimum dimensions_l left right best)) ,
  (MatrixChainLeftComplete dimensions_l (replace_Znth (((left * matrix_count_pre) + ((left + chain_length) - 1))) (best) (cost_l_2)) matrix_count_pre chain_length (left + 1))

noncomputable def matrixChainMinCost_entail_wit_11_split_goal_2 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (cost_l_2 : (List Int)) (chain_length : Int) (left : Int) (right : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= best)) (PreH11 : (best <= 7000000)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + right))) (PreH13 : (((left * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH15 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH16 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH17 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH18 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH19 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH20 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH21 : (1 <= chain_length)) (PreH22 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left right best)) (PreH23 : (MatrixChainIntervalMinimum dimensions_l left right best)) ,
  (Forall ((GE.ge (α := Int)) (7000000)) (replace_Znth (((left * matrix_count_pre) + ((left + chain_length) - 1))) (best) (cost_l_2)))

noncomputable def matrixChainMinCost_entail_wit_11_split_goal_3 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (cost_l_2 : (List Int)) (chain_length : Int) (left : Int) (right : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= best)) (PreH11 : (best <= 7000000)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + right))) (PreH13 : (((left * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH15 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH16 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH17 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH18 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH19 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH20 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH21 : (1 <= chain_length)) (PreH22 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left right best)) (PreH23 : (MatrixChainIntervalMinimum dimensions_l left right best)) ,
  (Forall ((LE.le (α := Int)) ((0 : Int))) (replace_Znth (((left * matrix_count_pre) + ((left + chain_length) - 1))) (best) (cost_l_2)))

noncomputable def matrixChainMinCost_entail_wit_11_split_goal_4 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (cost_l_2 : (List Int)) (chain_length : Int) (left : Int) (right : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= best)) (PreH11 : (best <= 7000000)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + right))) (PreH13 : (((left * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH15 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH16 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH17 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH18 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH19 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH20 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH21 : (1 <= chain_length)) (PreH22 : (MatrixChainSplitMinimum dimensions_l cost_l_2 matrix_count_pre matrix_count_pre chain_length left right best)) (PreH23 : (MatrixChainIntervalMinimum dimensions_l left right best)) ,
  ((Zlength ((replace_Znth (((left * matrix_count_pre) + ((left + chain_length) - 1))) (best) (cost_l_2)))) = (matrix_count_pre * matrix_count_pre))

noncomputable def matrixChainMinCost_entail_wit_12 : Prop :=
  (
forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (left : Int) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : ((left + chain_length) > matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : ((0 : Int) <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length) + 1))) (PreH10 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH12 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH14 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH15 : (1 <= chain_length)) (PreH16 : (MatrixChainLeftComplete dimensions_l cost_l_2 matrix_count_pre chain_length left)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l_2)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  EX cost_l : (List Int),
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ (2 <= (chain_length + 1)) ” &&
  “ ((chain_length + 1) <= (matrix_count_pre + 1)) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) dimensions_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) dimensions_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (7000000)) cost_l) ” &&
  “ (1 <= (chain_length + 1)) ” &&
  “ (MatrixChainLengthsComplete dimensions_l cost_l matrix_count_pre (chain_length + 1)) ”
  &&  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
) \/
(
forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (left : Int) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : ((left + chain_length) > matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : ((0 : Int) <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length) + 1))) (PreH10 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH12 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH14 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH15 : (1 <= chain_length)) (PreH16 : (MatrixChainLeftComplete dimensions_l cost_l_2 matrix_count_pre chain_length left)) ,
  TT && emp 
|--
  “ (MatrixChainLengthsComplete dimensions_l cost_l_2 matrix_count_pre (chain_length + 1)) ”
  &&  emp
)

noncomputable def matrixChainMinCost_entail_wit_12_split_goal_1 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (left : Int) (chain_length : Int) (cost_l_2 : (List Int)) (PreH1 : ((left + chain_length) > matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l_2)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= matrix_count_pre)) (PreH8 : ((0 : Int) <= left)) (PreH9 : (left <= ((matrix_count_pre - chain_length) + 1))) (PreH10 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH11 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH12 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l_2)) (PreH14 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l_2)) (PreH15 : (1 <= chain_length)) (PreH16 : (MatrixChainLeftComplete dimensions_l cost_l_2 matrix_count_pre chain_length left)) ,
  (MatrixChainLengthsComplete dimensions_l cost_l_2 matrix_count_pre (chain_length + 1))

noncomputable def matrixChainMinCost_entail_wit_13 : Prop :=
  (
forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (chain_length : Int) (cost_l : (List Int)) (PreH1 : (chain_length > matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= (matrix_count_pre + 1))) (PreH8 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH9 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH10 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH12 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH13 : (1 <= chain_length)) (PreH14 : (MatrixChainLengthsComplete dimensions_l cost_l matrix_count_pre chain_length)) ,
  (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** ((( &( "width" ) )) # Int |-> (matrix_count_pre))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ (MatrixChainOptimalCost dimensions_l matrix_count_pre (Znth (matrix_count_pre - 1) cost_l (0 : Int))) ”
  &&  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.undef_full ( &( "cost" ) ) 64)
  ** ((( &( "width" ) )) # Int |->_)
) \/
(
forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (chain_length : Int) (cost_l : (List Int)) (PreH1 : (chain_length > matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= (matrix_count_pre + 1))) (PreH8 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH9 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH10 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH12 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH13 : (1 <= chain_length)) (PreH14 : (MatrixChainLengthsComplete dimensions_l cost_l matrix_count_pre chain_length)) ,
  (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ (MatrixChainOptimalCost dimensions_l matrix_count_pre (Znth (matrix_count_pre - 1) cost_l (0 : Int))) ”
  &&  (intArray.undef_full ( &( "cost" ) ) 64)
)

noncomputable def matrixChainMinCost_entail_wit_13_split_goal_1 : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (chain_length : Int) (cost_l : (List Int)) (PreH1 : (chain_length > matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= (matrix_count_pre + 1))) (PreH8 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH9 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH10 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH12 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH13 : (1 <= chain_length)) (PreH14 : (MatrixChainLengthsComplete dimensions_l cost_l matrix_count_pre chain_length)) ,
  (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ (MatrixChainOptimalCost dimensions_l matrix_count_pre (Znth (matrix_count_pre - 1) cost_l (0 : Int))) ”

noncomputable def matrixChainMinCost_entail_wit_13_split_goal_spatial : Prop :=
  forall (dimensions_l : (List Int)) (matrix_count_pre : Int) (chain_length : Int) (cost_l : (List Int)) (PreH1 : (chain_length > matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= (matrix_count_pre + 1))) (PreH8 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH9 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH10 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH12 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH13 : (1 <= chain_length)) (PreH14 : (MatrixChainLengthsComplete dimensions_l cost_l matrix_count_pre chain_length)) ,
  (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  (intArray.undef_full ( &( "cost" ) ) 64)

noncomputable def matrixChainMinCost_return_wit_1 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (result : Int) (PreH1 : (MatrixChainOptimalCost dimensions_l matrix_count_pre result)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
|--
  “ (MatrixChainOptimalCost dimensions_l matrix_count_pre result) ”
  &&  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)

noncomputable def matrixChainMinCost_partial_solve_wit_1 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (i : Int) (PreH1 : (i < (matrix_count_pre * matrix_count_pre))) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= (matrix_count_pre * matrix_count_pre))) (PreH7 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH8 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH9 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH10 : ((Zlength (cost_l)) = i)) (PreH11 : (Forall (Eq ((0 : Int))) cost_l)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.seg ( &( "cost" ) ) (0 : Int) i cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) i (matrix_count_pre * matrix_count_pre))
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ (i < (matrix_count_pre * matrix_count_pre)) ” &&
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) dimensions_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) dimensions_l) ” &&
  “ ((Zlength (cost_l)) = i) ” &&
  “ (Forall (Eq ((0 : Int))) cost_l) ”
  &&  (((( &( "cost" ) ) + (i * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg ( &( "cost" ) ) (i + 1) (matrix_count_pre * matrix_count_pre))
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.seg ( &( "cost" ) ) (0 : Int) i cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)

noncomputable def matrixChainMinCost_partial_solve_wit_2 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH34 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ (2 <= chain_length) ” &&
  “ (chain_length <= matrix_count_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + chain_length) <= matrix_count_pre) ” &&
  “ (right = ((left + chain_length) - 1)) ” &&
  “ (left < right) ” &&
  “ (right < matrix_count_pre) ” &&
  “ ((0 : Int) <= ((left * matrix_count_pre) + left)) ” &&
  “ (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (((left + 1) * matrix_count_pre) + right)) ” &&
  “ ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (left + 1)) ” &&
  “ ((left + 1) < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (right + 1)) ” &&
  “ ((right + 1) < (matrix_count_pre + 1)) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int))) ” &&
  “ ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000) ” &&
  “ ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int))) ” &&
  “ ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000) ” &&
  “ (1 <= (Znth left dimensions_l (0 : Int))) ” &&
  “ ((Znth left dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (left + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (left + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (right + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (right + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) dimensions_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) dimensions_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (7000000)) cost_l) ” &&
  “ (1 <= chain_length) ” &&
  “ (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left) ”
  &&  (((( &( "cost" ) ) + (((left * matrix_count_pre) + left) * sizeof(INT)))) # Int |-> ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int))))
  ** (intArray.missing_i ( &( "cost" ) ) ((left * matrix_count_pre) + left) (0 : Int) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)

noncomputable def matrixChainMinCost_partial_solve_wit_3 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH34 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left)) ,
  (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ (2 <= chain_length) ” &&
  “ (chain_length <= matrix_count_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + chain_length) <= matrix_count_pre) ” &&
  “ (right = ((left + chain_length) - 1)) ” &&
  “ (left < right) ” &&
  “ (right < matrix_count_pre) ” &&
  “ ((0 : Int) <= ((left * matrix_count_pre) + left)) ” &&
  “ (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (((left + 1) * matrix_count_pre) + right)) ” &&
  “ ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (left + 1)) ” &&
  “ ((left + 1) < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (right + 1)) ” &&
  “ ((right + 1) < (matrix_count_pre + 1)) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int))) ” &&
  “ ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000) ” &&
  “ ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int))) ” &&
  “ ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000) ” &&
  “ (1 <= (Znth left dimensions_l (0 : Int))) ” &&
  “ ((Znth left dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (left + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (left + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (right + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (right + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) dimensions_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) dimensions_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (7000000)) cost_l) ” &&
  “ (1 <= chain_length) ” &&
  “ (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left) ”
  &&  (((( &( "cost" ) ) + ((((left + 1) * matrix_count_pre) + right) * sizeof(INT)))) # Int |-> ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int))))
  ** (intArray.missing_i ( &( "cost" ) ) (((left + 1) * matrix_count_pre) + right) (0 : Int) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)

noncomputable def matrixChainMinCost_partial_solve_wit_4 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH34 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left)) ,
  (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ (2 <= chain_length) ” &&
  “ (chain_length <= matrix_count_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + chain_length) <= matrix_count_pre) ” &&
  “ (right = ((left + chain_length) - 1)) ” &&
  “ (left < right) ” &&
  “ (right < matrix_count_pre) ” &&
  “ ((0 : Int) <= ((left * matrix_count_pre) + left)) ” &&
  “ (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (((left + 1) * matrix_count_pre) + right)) ” &&
  “ ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (left + 1)) ” &&
  “ ((left + 1) < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (right + 1)) ” &&
  “ ((right + 1) < (matrix_count_pre + 1)) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int))) ” &&
  “ ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000) ” &&
  “ ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int))) ” &&
  “ ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000) ” &&
  “ (1 <= (Znth left dimensions_l (0 : Int))) ” &&
  “ ((Znth left dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (left + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (left + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (right + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (right + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) dimensions_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) dimensions_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (7000000)) cost_l) ” &&
  “ (1 <= chain_length) ” &&
  “ (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left) ”
  &&  (((dimensions_pre + (left * sizeof(INT)))) # Int |-> ((Znth left dimensions_l (0 : Int))))
  ** (intArray.missing_i dimensions_pre left (0 : Int) (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)

noncomputable def matrixChainMinCost_partial_solve_wit_5 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH34 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ (2 <= chain_length) ” &&
  “ (chain_length <= matrix_count_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + chain_length) <= matrix_count_pre) ” &&
  “ (right = ((left + chain_length) - 1)) ” &&
  “ (left < right) ” &&
  “ (right < matrix_count_pre) ” &&
  “ ((0 : Int) <= ((left * matrix_count_pre) + left)) ” &&
  “ (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (((left + 1) * matrix_count_pre) + right)) ” &&
  “ ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (left + 1)) ” &&
  “ ((left + 1) < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (right + 1)) ” &&
  “ ((right + 1) < (matrix_count_pre + 1)) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int))) ” &&
  “ ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000) ” &&
  “ ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int))) ” &&
  “ ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000) ” &&
  “ (1 <= (Znth left dimensions_l (0 : Int))) ” &&
  “ ((Znth left dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (left + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (left + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (right + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (right + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) dimensions_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) dimensions_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (7000000)) cost_l) ” &&
  “ (1 <= chain_length) ” &&
  “ (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left) ”
  &&  (((dimensions_pre + ((left + 1) * sizeof(INT)))) # Int |-> ((Znth (left + 1) dimensions_l (0 : Int))))
  ** (intArray.missing_i dimensions_pre (left + 1) (0 : Int) (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)

noncomputable def matrixChainMinCost_partial_solve_wit_6 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= ((left * matrix_count_pre) + left))) (PreH11 : (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre))) (PreH12 : ((0 : Int) <= (((left + 1) * matrix_count_pre) + right))) (PreH13 : ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= left)) (PreH15 : (left < (matrix_count_pre + 1))) (PreH16 : ((0 : Int) <= (left + 1))) (PreH17 : ((left + 1) < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (right + 1))) (PreH19 : ((right + 1) < (matrix_count_pre + 1))) (PreH20 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH21 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH22 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)))) (PreH23 : ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000)) (PreH24 : ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH25 : ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH26 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH27 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH28 : (1 <= (Znth (left + 1) dimensions_l (0 : Int)))) (PreH29 : ((Znth (left + 1) dimensions_l (0 : Int)) <= 100)) (PreH30 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH31 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH32 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH33 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH34 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH37 : (1 <= chain_length)) (PreH38 : (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ (2 <= chain_length) ” &&
  “ (chain_length <= matrix_count_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + chain_length) <= matrix_count_pre) ” &&
  “ (right = ((left + chain_length) - 1)) ” &&
  “ (left < right) ” &&
  “ (right < matrix_count_pre) ” &&
  “ ((0 : Int) <= ((left * matrix_count_pre) + left)) ” &&
  “ (((left * matrix_count_pre) + left) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (((left + 1) * matrix_count_pre) + right)) ” &&
  “ ((((left + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (left + 1)) ” &&
  “ ((left + 1) < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (right + 1)) ” &&
  “ ((right + 1) < (matrix_count_pre + 1)) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (Znth ((left * matrix_count_pre) + left) cost_l (0 : Int))) ” &&
  “ ((Znth ((left * matrix_count_pre) + left) cost_l (0 : Int)) <= 7000000) ” &&
  “ ((0 : Int) <= (Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int))) ” &&
  “ ((Znth (((left + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000) ” &&
  “ (1 <= (Znth left dimensions_l (0 : Int))) ” &&
  “ ((Znth left dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (left + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (left + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (right + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (right + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) dimensions_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) dimensions_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (7000000)) cost_l) ” &&
  “ (1 <= chain_length) ” &&
  “ (MatrixChainLeftComplete dimensions_l cost_l matrix_count_pre chain_length left) ”
  &&  (((dimensions_pre + ((right + 1) * sizeof(INT)))) # Int |-> ((Znth (right + 1) dimensions_l (0 : Int))))
  ** (intArray.missing_i dimensions_pre (right + 1) (0 : Int) (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)

noncomputable def matrixChainMinCost_partial_solve_wit_7 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1) <= split)) (PreH11 : (split < right)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + split))) (PreH13 : (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= (((split + 1) * matrix_count_pre) + right))) (PreH15 : ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH16 : ((0 : Int) <= left)) (PreH17 : (left < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (split + 1))) (PreH19 : ((split + 1) < (matrix_count_pre + 1))) (PreH20 : ((0 : Int) <= (right + 1))) (PreH21 : ((right + 1) < (matrix_count_pre + 1))) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH26 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)))) (PreH27 : ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000)) (PreH28 : ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH29 : ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH31 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH32 : (1 <= (Znth (split + 1) dimensions_l (0 : Int)))) (PreH33 : ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)) (PreH34 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH35 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH36 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH37 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH39 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH40 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH41 : (1 <= chain_length)) (PreH42 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ (2 <= chain_length) ” &&
  “ (chain_length <= matrix_count_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + chain_length) <= matrix_count_pre) ” &&
  “ (right = ((left + chain_length) - 1)) ” &&
  “ (left < right) ” &&
  “ (right < matrix_count_pre) ” &&
  “ ((left + 1) <= split) ” &&
  “ (split < right) ” &&
  “ ((0 : Int) <= ((left * matrix_count_pre) + split)) ” &&
  “ (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (((split + 1) * matrix_count_pre) + right)) ” &&
  “ ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (split + 1)) ” &&
  “ ((split + 1) < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (right + 1)) ” &&
  “ ((right + 1) < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 7000000) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int))) ” &&
  “ ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000) ” &&
  “ ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int))) ” &&
  “ ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000) ” &&
  “ (1 <= (Znth left dimensions_l (0 : Int))) ” &&
  “ ((Znth left dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (split + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (split + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (right + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (right + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) dimensions_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) dimensions_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (7000000)) cost_l) ” &&
  “ (1 <= chain_length) ” &&
  “ (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best) ”
  &&  (((( &( "cost" ) ) + (((left * matrix_count_pre) + split) * sizeof(INT)))) # Int |-> ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int))))
  ** (intArray.missing_i ( &( "cost" ) ) ((left * matrix_count_pre) + split) (0 : Int) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)

noncomputable def matrixChainMinCost_partial_solve_wit_8 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1) <= split)) (PreH11 : (split < right)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + split))) (PreH13 : (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= (((split + 1) * matrix_count_pre) + right))) (PreH15 : ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH16 : ((0 : Int) <= left)) (PreH17 : (left < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (split + 1))) (PreH19 : ((split + 1) < (matrix_count_pre + 1))) (PreH20 : ((0 : Int) <= (right + 1))) (PreH21 : ((right + 1) < (matrix_count_pre + 1))) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH26 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)))) (PreH27 : ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000)) (PreH28 : ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH29 : ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH31 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH32 : (1 <= (Znth (split + 1) dimensions_l (0 : Int)))) (PreH33 : ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)) (PreH34 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH35 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH36 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH37 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH39 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH40 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH41 : (1 <= chain_length)) (PreH42 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ (2 <= chain_length) ” &&
  “ (chain_length <= matrix_count_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + chain_length) <= matrix_count_pre) ” &&
  “ (right = ((left + chain_length) - 1)) ” &&
  “ (left < right) ” &&
  “ (right < matrix_count_pre) ” &&
  “ ((left + 1) <= split) ” &&
  “ (split < right) ” &&
  “ ((0 : Int) <= ((left * matrix_count_pre) + split)) ” &&
  “ (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (((split + 1) * matrix_count_pre) + right)) ” &&
  “ ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (split + 1)) ” &&
  “ ((split + 1) < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (right + 1)) ” &&
  “ ((right + 1) < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 7000000) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int))) ” &&
  “ ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000) ” &&
  “ ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int))) ” &&
  “ ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000) ” &&
  “ (1 <= (Znth left dimensions_l (0 : Int))) ” &&
  “ ((Znth left dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (split + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (split + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (right + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (right + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) dimensions_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) dimensions_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (7000000)) cost_l) ” &&
  “ (1 <= chain_length) ” &&
  “ (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best) ”
  &&  (((( &( "cost" ) ) + ((((split + 1) * matrix_count_pre) + right) * sizeof(INT)))) # Int |-> ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int))))
  ** (intArray.missing_i ( &( "cost" ) ) (((split + 1) * matrix_count_pre) + right) (0 : Int) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)

noncomputable def matrixChainMinCost_partial_solve_wit_9 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1) <= split)) (PreH11 : (split < right)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + split))) (PreH13 : (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= (((split + 1) * matrix_count_pre) + right))) (PreH15 : ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH16 : ((0 : Int) <= left)) (PreH17 : (left < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (split + 1))) (PreH19 : ((split + 1) < (matrix_count_pre + 1))) (PreH20 : ((0 : Int) <= (right + 1))) (PreH21 : ((right + 1) < (matrix_count_pre + 1))) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH26 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)))) (PreH27 : ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000)) (PreH28 : ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH29 : ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH31 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH32 : (1 <= (Znth (split + 1) dimensions_l (0 : Int)))) (PreH33 : ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)) (PreH34 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH35 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH36 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH37 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH39 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH40 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH41 : (1 <= chain_length)) (PreH42 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ (2 <= chain_length) ” &&
  “ (chain_length <= matrix_count_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + chain_length) <= matrix_count_pre) ” &&
  “ (right = ((left + chain_length) - 1)) ” &&
  “ (left < right) ” &&
  “ (right < matrix_count_pre) ” &&
  “ ((left + 1) <= split) ” &&
  “ (split < right) ” &&
  “ ((0 : Int) <= ((left * matrix_count_pre) + split)) ” &&
  “ (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (((split + 1) * matrix_count_pre) + right)) ” &&
  “ ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (split + 1)) ” &&
  “ ((split + 1) < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (right + 1)) ” &&
  “ ((right + 1) < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 7000000) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int))) ” &&
  “ ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000) ” &&
  “ ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int))) ” &&
  “ ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000) ” &&
  “ (1 <= (Znth left dimensions_l (0 : Int))) ” &&
  “ ((Znth left dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (split + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (split + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (right + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (right + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) dimensions_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) dimensions_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (7000000)) cost_l) ” &&
  “ (1 <= chain_length) ” &&
  “ (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best) ”
  &&  (((dimensions_pre + (left * sizeof(INT)))) # Int |-> ((Znth left dimensions_l (0 : Int))))
  ** (intArray.missing_i dimensions_pre left (0 : Int) (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)

noncomputable def matrixChainMinCost_partial_solve_wit_10 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1) <= split)) (PreH11 : (split < right)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + split))) (PreH13 : (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= (((split + 1) * matrix_count_pre) + right))) (PreH15 : ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH16 : ((0 : Int) <= left)) (PreH17 : (left < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (split + 1))) (PreH19 : ((split + 1) < (matrix_count_pre + 1))) (PreH20 : ((0 : Int) <= (right + 1))) (PreH21 : ((right + 1) < (matrix_count_pre + 1))) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH26 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)))) (PreH27 : ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000)) (PreH28 : ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH29 : ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH31 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH32 : (1 <= (Znth (split + 1) dimensions_l (0 : Int)))) (PreH33 : ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)) (PreH34 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH35 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH36 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH37 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH39 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH40 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH41 : (1 <= chain_length)) (PreH42 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ (2 <= chain_length) ” &&
  “ (chain_length <= matrix_count_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + chain_length) <= matrix_count_pre) ” &&
  “ (right = ((left + chain_length) - 1)) ” &&
  “ (left < right) ” &&
  “ (right < matrix_count_pre) ” &&
  “ ((left + 1) <= split) ” &&
  “ (split < right) ” &&
  “ ((0 : Int) <= ((left * matrix_count_pre) + split)) ” &&
  “ (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (((split + 1) * matrix_count_pre) + right)) ” &&
  “ ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (split + 1)) ” &&
  “ ((split + 1) < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (right + 1)) ” &&
  “ ((right + 1) < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 7000000) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int))) ” &&
  “ ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000) ” &&
  “ ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int))) ” &&
  “ ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000) ” &&
  “ (1 <= (Znth left dimensions_l (0 : Int))) ” &&
  “ ((Znth left dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (split + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (split + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (right + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (right + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) dimensions_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) dimensions_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (7000000)) cost_l) ” &&
  “ (1 <= chain_length) ” &&
  “ (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best) ”
  &&  (((dimensions_pre + ((split + 1) * sizeof(INT)))) # Int |-> ((Znth (split + 1) dimensions_l (0 : Int))))
  ** (intArray.missing_i dimensions_pre (split + 1) (0 : Int) (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)

noncomputable def matrixChainMinCost_partial_solve_wit_11 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (split : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((left + 1) <= split)) (PreH11 : (split < right)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + split))) (PreH13 : (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((0 : Int) <= (((split + 1) * matrix_count_pre) + right))) (PreH15 : ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH16 : ((0 : Int) <= left)) (PreH17 : (left < (matrix_count_pre + 1))) (PreH18 : ((0 : Int) <= (split + 1))) (PreH19 : ((split + 1) < (matrix_count_pre + 1))) (PreH20 : ((0 : Int) <= (right + 1))) (PreH21 : ((right + 1) < (matrix_count_pre + 1))) (PreH22 : ((0 : Int) <= best)) (PreH23 : (best <= 7000000)) (PreH24 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH25 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH26 : ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)))) (PreH27 : ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000)) (PreH28 : ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)))) (PreH29 : ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000)) (PreH30 : (1 <= (Znth left dimensions_l (0 : Int)))) (PreH31 : ((Znth left dimensions_l (0 : Int)) <= 100)) (PreH32 : (1 <= (Znth (split + 1) dimensions_l (0 : Int)))) (PreH33 : ((Znth (split + 1) dimensions_l (0 : Int)) <= 100)) (PreH34 : (1 <= (Znth (right + 1) dimensions_l (0 : Int)))) (PreH35 : ((Znth (right + 1) dimensions_l (0 : Int)) <= 100)) (PreH36 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH37 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH38 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH39 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH40 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH41 : (1 <= chain_length)) (PreH42 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ (2 <= chain_length) ” &&
  “ (chain_length <= matrix_count_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + chain_length) <= matrix_count_pre) ” &&
  “ (right = ((left + chain_length) - 1)) ” &&
  “ (left < right) ” &&
  “ (right < matrix_count_pre) ” &&
  “ ((left + 1) <= split) ” &&
  “ (split < right) ” &&
  “ ((0 : Int) <= ((left * matrix_count_pre) + split)) ” &&
  “ (((left * matrix_count_pre) + split) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (((split + 1) * matrix_count_pre) + right)) ” &&
  “ ((((split + 1) * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= left) ” &&
  “ (left < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (split + 1)) ” &&
  “ ((split + 1) < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= (right + 1)) ” &&
  “ ((right + 1) < (matrix_count_pre + 1)) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 7000000) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((0 : Int) <= (Znth ((left * matrix_count_pre) + split) cost_l (0 : Int))) ” &&
  “ ((Znth ((left * matrix_count_pre) + split) cost_l (0 : Int)) <= 7000000) ” &&
  “ ((0 : Int) <= (Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int))) ” &&
  “ ((Znth (((split + 1) * matrix_count_pre) + right) cost_l (0 : Int)) <= 7000000) ” &&
  “ (1 <= (Znth left dimensions_l (0 : Int))) ” &&
  “ ((Znth left dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (split + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (split + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ (1 <= (Znth (right + 1) dimensions_l (0 : Int))) ” &&
  “ ((Znth (right + 1) dimensions_l (0 : Int)) <= 100) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) dimensions_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) dimensions_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (7000000)) cost_l) ” &&
  “ (1 <= chain_length) ” &&
  “ (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left split best) ”
  &&  (((dimensions_pre + ((right + 1) * sizeof(INT)))) # Int |-> ((Znth (right + 1) dimensions_l (0 : Int))))
  ** (intArray.missing_i dimensions_pre (right + 1) (0 : Int) (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)

noncomputable def matrixChainMinCost_partial_solve_wit_12 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (cost_l : (List Int)) (chain_length : Int) (left : Int) (right : Int) (best : Int) (PreH1 : (1 <= matrix_count_pre)) (PreH2 : (matrix_count_pre <= 8)) (PreH3 : (2 <= chain_length)) (PreH4 : (chain_length <= matrix_count_pre)) (PreH5 : ((0 : Int) <= left)) (PreH6 : ((left + chain_length) <= matrix_count_pre)) (PreH7 : (right = ((left + chain_length) - 1))) (PreH8 : (left < right)) (PreH9 : (right < matrix_count_pre)) (PreH10 : ((0 : Int) <= best)) (PreH11 : (best <= 7000000)) (PreH12 : ((0 : Int) <= ((left * matrix_count_pre) + right))) (PreH13 : (((left * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre))) (PreH14 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH15 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH16 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH17 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH18 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH19 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH20 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH21 : (1 <= chain_length)) (PreH22 : (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left right best)) (PreH23 : (MatrixChainIntervalMinimum dimensions_l left right best)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ (2 <= chain_length) ” &&
  “ (chain_length <= matrix_count_pre) ” &&
  “ ((0 : Int) <= left) ” &&
  “ ((left + chain_length) <= matrix_count_pre) ” &&
  “ (right = ((left + chain_length) - 1)) ” &&
  “ (left < right) ” &&
  “ (right < matrix_count_pre) ” &&
  “ ((0 : Int) <= best) ” &&
  “ (best <= 7000000) ” &&
  “ ((0 : Int) <= ((left * matrix_count_pre) + right)) ” &&
  “ (((left * matrix_count_pre) + right) < (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) dimensions_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) dimensions_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (7000000)) cost_l) ” &&
  “ (1 <= chain_length) ” &&
  “ (MatrixChainSplitMinimum dimensions_l cost_l matrix_count_pre matrix_count_pre chain_length left right best) ” &&
  “ (MatrixChainIntervalMinimum dimensions_l left right best) ”
  &&  (((( &( "cost" ) ) + (((left * matrix_count_pre) + right) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i ( &( "cost" ) ) ((left * matrix_count_pre) + right) (0 : Int) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)

noncomputable def matrixChainMinCost_partial_solve_wit_13 : Prop :=
  forall (dimensions_l : (List Int)) (dimensions_pre : Int) (matrix_count_pre : Int) (chain_length : Int) (cost_l : (List Int)) (PreH1 : (chain_length > matrix_count_pre)) (PreH2 : (1 <= matrix_count_pre)) (PreH3 : (matrix_count_pre <= 8)) (PreH4 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH5 : ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre))) (PreH6 : (2 <= chain_length)) (PreH7 : (chain_length <= (matrix_count_pre + 1))) (PreH8 : ((Zlength (dimensions_l)) = (matrix_count_pre + 1))) (PreH9 : (Forall ((LE.le (α := Int)) (1)) dimensions_l)) (PreH10 : (Forall ((GE.ge (α := Int)) (100)) dimensions_l)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l)) (PreH12 : (Forall ((GE.ge (α := Int)) (7000000)) cost_l)) (PreH13 : (1 <= chain_length)) (PreH14 : (MatrixChainLengthsComplete dimensions_l cost_l matrix_count_pre chain_length)) ,
  (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.full ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)
|--
  “ (chain_length > matrix_count_pre) ” &&
  “ (1 <= matrix_count_pre) ” &&
  “ (matrix_count_pre <= 8) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ ((Zlength (cost_l)) = (matrix_count_pre * matrix_count_pre)) ” &&
  “ (2 <= chain_length) ” &&
  “ (chain_length <= (matrix_count_pre + 1)) ” &&
  “ ((Zlength (dimensions_l)) = (matrix_count_pre + 1)) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) dimensions_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) dimensions_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) cost_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (7000000)) cost_l) ” &&
  “ (1 <= chain_length) ” &&
  “ (MatrixChainLengthsComplete dimensions_l cost_l matrix_count_pre chain_length) ”
  &&  (((( &( "cost" ) ) + ((matrix_count_pre - 1) * sizeof(INT)))) # Int |-> ((Znth (matrix_count_pre - 1) cost_l (0 : Int))))
  ** (intArray.missing_i ( &( "cost" ) ) (matrix_count_pre - 1) (0 : Int) (matrix_count_pre * matrix_count_pre) cost_l)
  ** (intArray.full dimensions_pre (matrix_count_pre + 1) dimensions_l)
  ** (intArray.undef_seg ( &( "cost" ) ) (matrix_count_pre * matrix_count_pre) 64)


structure VC_Correct : Type where
  proof_of_matrixChainMinCost_safety_wit_1 : matrixChainMinCost_safety_wit_1
  proof_of_matrixChainMinCost_safety_wit_2 : matrixChainMinCost_safety_wit_2
  proof_of_matrixChainMinCost_safety_wit_3 : matrixChainMinCost_safety_wit_3
  proof_of_matrixChainMinCost_safety_wit_4 : matrixChainMinCost_safety_wit_4
  proof_of_matrixChainMinCost_safety_wit_5 : matrixChainMinCost_safety_wit_5
  proof_of_matrixChainMinCost_safety_wit_6 : matrixChainMinCost_safety_wit_6
  proof_of_matrixChainMinCost_safety_wit_7 : matrixChainMinCost_safety_wit_7
  proof_of_matrixChainMinCost_safety_wit_8 : matrixChainMinCost_safety_wit_8
  proof_of_matrixChainMinCost_safety_wit_9 : matrixChainMinCost_safety_wit_9
  proof_of_matrixChainMinCost_safety_wit_10 : matrixChainMinCost_safety_wit_10
  proof_of_matrixChainMinCost_safety_wit_11 : matrixChainMinCost_safety_wit_11
  proof_of_matrixChainMinCost_safety_wit_12 : matrixChainMinCost_safety_wit_12
  proof_of_matrixChainMinCost_safety_wit_13 : matrixChainMinCost_safety_wit_13
  proof_of_matrixChainMinCost_safety_wit_14 : matrixChainMinCost_safety_wit_14
  proof_of_matrixChainMinCost_safety_wit_15 : matrixChainMinCost_safety_wit_15
  proof_of_matrixChainMinCost_safety_wit_16 : matrixChainMinCost_safety_wit_16
  proof_of_matrixChainMinCost_safety_wit_17 : matrixChainMinCost_safety_wit_17
  proof_of_matrixChainMinCost_safety_wit_18 : matrixChainMinCost_safety_wit_18
  proof_of_matrixChainMinCost_safety_wit_19 : matrixChainMinCost_safety_wit_19
  proof_of_matrixChainMinCost_safety_wit_20 : matrixChainMinCost_safety_wit_20
  proof_of_matrixChainMinCost_safety_wit_21 : matrixChainMinCost_safety_wit_21
  proof_of_matrixChainMinCost_safety_wit_22 : matrixChainMinCost_safety_wit_22
  proof_of_matrixChainMinCost_safety_wit_23 : matrixChainMinCost_safety_wit_23
  proof_of_matrixChainMinCost_safety_wit_24 : matrixChainMinCost_safety_wit_24
  proof_of_matrixChainMinCost_safety_wit_25 : matrixChainMinCost_safety_wit_25
  proof_of_matrixChainMinCost_safety_wit_26 : matrixChainMinCost_safety_wit_26
  proof_of_matrixChainMinCost_safety_wit_27 : matrixChainMinCost_safety_wit_27
  proof_of_matrixChainMinCost_safety_wit_28 : matrixChainMinCost_safety_wit_28
  proof_of_matrixChainMinCost_safety_wit_29 : matrixChainMinCost_safety_wit_29
  proof_of_matrixChainMinCost_safety_wit_30 : matrixChainMinCost_safety_wit_30
  proof_of_matrixChainMinCost_safety_wit_31 : matrixChainMinCost_safety_wit_31
  proof_of_matrixChainMinCost_safety_wit_32 : matrixChainMinCost_safety_wit_32
  proof_of_matrixChainMinCost_safety_wit_33 : matrixChainMinCost_safety_wit_33
  proof_of_matrixChainMinCost_safety_wit_34 : matrixChainMinCost_safety_wit_34
  proof_of_matrixChainMinCost_safety_wit_35 : matrixChainMinCost_safety_wit_35
  proof_of_matrixChainMinCost_safety_wit_36 : matrixChainMinCost_safety_wit_36
  proof_of_matrixChainMinCost_safety_wit_37 : matrixChainMinCost_safety_wit_37
  proof_of_matrixChainMinCost_safety_wit_38 : matrixChainMinCost_safety_wit_38
  proof_of_matrixChainMinCost_safety_wit_39 : matrixChainMinCost_safety_wit_39
  proof_of_matrixChainMinCost_safety_wit_40 : matrixChainMinCost_safety_wit_40
  proof_of_matrixChainMinCost_safety_wit_41 : matrixChainMinCost_safety_wit_41
  proof_of_matrixChainMinCost_safety_wit_42 : matrixChainMinCost_safety_wit_42
  proof_of_matrixChainMinCost_safety_wit_43 : matrixChainMinCost_safety_wit_43
  proof_of_matrixChainMinCost_safety_wit_44 : matrixChainMinCost_safety_wit_44
  proof_of_matrixChainMinCost_safety_wit_45 : matrixChainMinCost_safety_wit_45
  proof_of_matrixChainMinCost_safety_wit_46 : matrixChainMinCost_safety_wit_46
  proof_of_matrixChainMinCost_safety_wit_47 : matrixChainMinCost_safety_wit_47
  proof_of_matrixChainMinCost_safety_wit_48 : matrixChainMinCost_safety_wit_48
  proof_of_matrixChainMinCost_return_wit_1 : matrixChainMinCost_return_wit_1
  proof_of_matrixChainMinCost_partial_solve_wit_1 : matrixChainMinCost_partial_solve_wit_1
  proof_of_matrixChainMinCost_partial_solve_wit_2 : matrixChainMinCost_partial_solve_wit_2
  proof_of_matrixChainMinCost_partial_solve_wit_3 : matrixChainMinCost_partial_solve_wit_3
  proof_of_matrixChainMinCost_partial_solve_wit_4 : matrixChainMinCost_partial_solve_wit_4
  proof_of_matrixChainMinCost_partial_solve_wit_5 : matrixChainMinCost_partial_solve_wit_5
  proof_of_matrixChainMinCost_partial_solve_wit_6 : matrixChainMinCost_partial_solve_wit_6
  proof_of_matrixChainMinCost_partial_solve_wit_7 : matrixChainMinCost_partial_solve_wit_7
  proof_of_matrixChainMinCost_partial_solve_wit_8 : matrixChainMinCost_partial_solve_wit_8
  proof_of_matrixChainMinCost_partial_solve_wit_9 : matrixChainMinCost_partial_solve_wit_9
  proof_of_matrixChainMinCost_partial_solve_wit_10 : matrixChainMinCost_partial_solve_wit_10
  proof_of_matrixChainMinCost_partial_solve_wit_11 : matrixChainMinCost_partial_solve_wit_11
  proof_of_matrixChainMinCost_partial_solve_wit_12 : matrixChainMinCost_partial_solve_wit_12
  proof_of_matrixChainMinCost_partial_solve_wit_13 : matrixChainMinCost_partial_solve_wit_13
  proof_of_matrixChainMinCost_entail_wit_1 : matrixChainMinCost_entail_wit_1
  proof_of_matrixChainMinCost_entail_wit_2 : matrixChainMinCost_entail_wit_2
  proof_of_matrixChainMinCost_entail_wit_3 : matrixChainMinCost_entail_wit_3
  proof_of_matrixChainMinCost_entail_wit_4 : matrixChainMinCost_entail_wit_4
  proof_of_matrixChainMinCost_entail_wit_5 : matrixChainMinCost_entail_wit_5
  proof_of_matrixChainMinCost_entail_wit_6 : matrixChainMinCost_entail_wit_6
  proof_of_matrixChainMinCost_entail_wit_7 : matrixChainMinCost_entail_wit_7
  proof_of_matrixChainMinCost_entail_wit_8 : matrixChainMinCost_entail_wit_8
  proof_of_matrixChainMinCost_entail_wit_9_1 : matrixChainMinCost_entail_wit_9_1
  proof_of_matrixChainMinCost_entail_wit_9_2 : matrixChainMinCost_entail_wit_9_2
  proof_of_matrixChainMinCost_entail_wit_10 : matrixChainMinCost_entail_wit_10
  proof_of_matrixChainMinCost_entail_wit_11 : matrixChainMinCost_entail_wit_11
  proof_of_matrixChainMinCost_entail_wit_12 : matrixChainMinCost_entail_wit_12
  proof_of_matrixChainMinCost_entail_wit_13 : matrixChainMinCost_entail_wit_13

end SimpleC.EE.LLM_bench.Algorithms.matrix_chain_multiplication.matrix_chain_multiplication_goal
