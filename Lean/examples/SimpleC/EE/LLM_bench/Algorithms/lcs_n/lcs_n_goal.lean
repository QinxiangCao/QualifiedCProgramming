import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Algorithms.lcs_n.lcs_n_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.lcs_n.lcs_n_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance lcs_n_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def longest_common_sequence_safety_wit_1 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (xs)) = n_pre)) (PreH4 : ((Zlength (ys)) = n_pre)) ,
  ((( &( "left" ) )) # Int |->_)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "j" ) )) # Int |->_)
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "stride" ) )) # Int |->_)
  ** (intArray.undef_full ( &( "table" ) ) 1002001)
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
|--
  “ ((n_pre + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre + 1)) ”

noncomputable def longest_common_sequence_safety_wit_2 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (xs)) = n_pre)) (PreH4 : ((Zlength (ys)) = n_pre)) ,
  ((( &( "left" ) )) # Int |->_)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "j" ) )) # Int |->_)
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "stride" ) )) # Int |->_)
  ** (intArray.undef_full ( &( "table" ) ) 1002001)
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def longest_common_sequence_safety_wit_3 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (xs)) = n_pre)) (PreH4 : ((Zlength (ys)) = n_pre)) ,
  ((( &( "left" ) )) # Int |->_)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "j" ) )) # Int |->_)
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "stride" ) )) # Int |-> ((n_pre + 1)))
  ** (intArray.undef_full ( &( "table" ) ) 1002001)
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def longest_common_sequence_safety_wit_4 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (i : Int) (stride : Int) (PreH1 : ((0 : Int) <= (stride * i))) (PreH2 : ((stride * i) < ((n_pre + 1) * (n_pre + 1)))) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (i <= n_pre)) (PreH6 : (stride = (n_pre + 1))) (PreH7 : ((0 : Int) <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : ((Zlength (xs)) = n_pre)) (PreH10 : ((Zlength (ys)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= (n_pre + 1))) (PreH13 : ((0 : Int) <= (stride * i))) (PreH14 : ((stride * i) <= ((n_pre + 1) * (n_pre + 1)))) (PreH15 : (LCSNColumnProgress mixed_table table_l n_pre i)) (PreH16 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH17 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "j" ) )) # Int |->_)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ ((stride * i) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (stride * i)) ”

noncomputable def longest_common_sequence_safety_wit_5 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (i : Int) (stride : Int) (PreH1 : ((0 : Int) <= (stride * i))) (PreH2 : ((stride * i) < ((n_pre + 1) * (n_pre + 1)))) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (i <= n_pre)) (PreH6 : (stride = (n_pre + 1))) (PreH7 : ((0 : Int) <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : ((Zlength (xs)) = n_pre)) (PreH10 : ((Zlength (ys)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= (n_pre + 1))) (PreH13 : ((0 : Int) <= (stride * i))) (PreH14 : ((stride * i) <= ((n_pre + 1) * (n_pre + 1)))) (PreH15 : (LCSNColumnProgress mixed_table table_l n_pre i)) (PreH16 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH17 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "j" ) )) # Int |->_)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def longest_common_sequence_safety_wit_6 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (i : Int) (stride : Int) (PreH1 : ((0 : Int) <= (stride * i))) (PreH2 : ((stride * i) < ((n_pre + 1) * (n_pre + 1)))) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (i <= n_pre)) (PreH6 : (stride = (n_pre + 1))) (PreH7 : ((0 : Int) <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : ((Zlength (xs)) = n_pre)) (PreH10 : ((Zlength (ys)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= (n_pre + 1))) (PreH13 : ((0 : Int) <= (stride * i))) (PreH14 : ((stride * i) <= ((n_pre + 1) * (n_pre + 1)))) (PreH15 : (LCSNColumnProgress mixed_table table_l n_pre i)) (PreH16 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH17 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) (replace_Znth ((stride * i)) ((Some ((0 : Int)))) (mixed_table)))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** ((( &( "j" ) )) # Int |->_)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def longest_common_sequence_safety_wit_7 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (i : Int) (stride : Int) (PreH1 : ((0 : Int) <= (stride * i))) (PreH2 : ((stride * i) < ((n_pre + 1) * (n_pre + 1)))) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (i <= n_pre)) (PreH6 : (stride = (n_pre + 1))) (PreH7 : ((0 : Int) <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : ((Zlength (xs)) = n_pre)) (PreH10 : ((Zlength (ys)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= (n_pre + 1))) (PreH13 : ((0 : Int) <= (stride * i))) (PreH14 : ((stride * i) <= ((n_pre + 1) * (n_pre + 1)))) (PreH15 : (LCSNColumnProgress mixed_table table_l n_pre i)) (PreH16 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH17 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) (replace_Znth ((stride * i)) ((Some ((0 : Int)))) (mixed_table)))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** ((( &( "j" ) )) # Int |->_)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def longest_common_sequence_safety_wit_8 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (i : Int) (stride : Int) (PreH1 : (i > n_pre)) (PreH2 : (stride = (n_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= (n_pre + 1))) (PreH9 : ((0 : Int) <= (stride * i))) (PreH10 : ((stride * i) <= ((n_pre + 1) * (n_pre + 1)))) (PreH11 : (LCSNColumnProgress mixed_table table_l n_pre i)) (PreH12 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH13 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "j" ) )) # Int |->_)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def longest_common_sequence_safety_wit_9 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (stride : Int) (PreH1 : (j <= n_pre)) (PreH2 : (stride = (n_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1))) (PreH9 : (LCSNBoundaryProgress mixed_table table_l n_pre j)) (PreH10 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH11 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def longest_common_sequence_safety_wit_10 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (stride : Int) (PreH1 : (j <= n_pre)) (PreH2 : (stride = (n_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1))) (PreH9 : (LCSNBoundaryProgress mixed_table table_l n_pre j)) (PreH10 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH11 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) (replace_Znth (j) ((Some ((0 : Int)))) (mixed_table)))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def longest_common_sequence_safety_wit_11 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (stride : Int) (PreH1 : (j <= n_pre)) (PreH2 : (stride = (n_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1))) (PreH9 : (LCSNBoundaryProgress mixed_table table_l n_pre j)) (PreH10 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH11 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) (replace_Znth (j) ((Some ((0 : Int)))) (mixed_table)))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def longest_common_sequence_safety_wit_12 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (stride : Int) (PreH1 : (j > n_pre)) (PreH2 : (stride = (n_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1))) (PreH9 : (LCSNBoundaryProgress mixed_table table_l n_pre j)) (PreH10 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH11 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def longest_common_sequence_safety_wit_13 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (i : Int) (stride : Int) (PreH1 : (i <= n_pre)) (PreH2 : (stride = (n_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre + 1))) (PreH9 : ((0 : Int) <= (stride * i))) (PreH10 : ((stride * i) <= ((n_pre + 1) * (n_pre + 1)))) (PreH11 : (LCSNRowsProgress xs ys mixed_table table_l n_pre i)) (PreH12 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH13 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "j" ) )) # Int |->_)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def longest_common_sequence_safety_wit_14 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table : (List (Option Int))) (table_l : (List Int)) (PreH1 : ((0 : Int) <= (i - 1))) (PreH2 : ((i - 1) < n_pre)) (PreH3 : ((0 : Int) <= (j - 1))) (PreH4 : ((j - 1) < n_pre)) (PreH5 : ((0 : Int) <= ((stride * i) + j))) (PreH6 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH8 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH9 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH10 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH11 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH12 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= n_pre)) (PreH16 : (stride = (n_pre + 1))) (PreH17 : ((0 : Int) <= n_pre)) (PreH18 : (n_pre <= 1000)) (PreH19 : ((Zlength (xs)) = n_pre)) (PreH20 : ((Zlength (ys)) = n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (1 <= j)) (PreH24 : (j <= (n_pre + 1))) (PreH25 : ((0 : Int) <= ((stride * i) + j))) (PreH26 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH27 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH28 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH29 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (intArray.full x_pre n_pre xs)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ ((j - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j - 1)) ”

noncomputable def longest_common_sequence_safety_wit_15 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table : (List (Option Int))) (table_l : (List Int)) (PreH1 : ((0 : Int) <= (i - 1))) (PreH2 : ((i - 1) < n_pre)) (PreH3 : ((0 : Int) <= (j - 1))) (PreH4 : ((j - 1) < n_pre)) (PreH5 : ((0 : Int) <= ((stride * i) + j))) (PreH6 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH8 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH9 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH10 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH11 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH12 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= n_pre)) (PreH16 : (stride = (n_pre + 1))) (PreH17 : ((0 : Int) <= n_pre)) (PreH18 : (n_pre <= 1000)) (PreH19 : ((Zlength (xs)) = n_pre)) (PreH20 : ((Zlength (ys)) = n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (1 <= j)) (PreH24 : (j <= (n_pre + 1))) (PreH25 : ((0 : Int) <= ((stride * i) + j))) (PreH26 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH27 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH28 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH29 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def longest_common_sequence_safety_wit_16 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table : (List (Option Int))) (table_l : (List Int)) (PreH1 : ((0 : Int) <= (i - 1))) (PreH2 : ((i - 1) < n_pre)) (PreH3 : ((0 : Int) <= (j - 1))) (PreH4 : ((j - 1) < n_pre)) (PreH5 : ((0 : Int) <= ((stride * i) + j))) (PreH6 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH8 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH9 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH10 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH11 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH12 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= n_pre)) (PreH16 : (stride = (n_pre + 1))) (PreH17 : ((0 : Int) <= n_pre)) (PreH18 : (n_pre <= 1000)) (PreH19 : ((Zlength (xs)) = n_pre)) (PreH20 : ((Zlength (ys)) = n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (1 <= j)) (PreH24 : (j <= (n_pre + 1))) (PreH25 : ((0 : Int) <= ((stride * i) + j))) (PreH26 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH27 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH28 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH29 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def longest_common_sequence_safety_wit_17 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table : (List (Option Int))) (table_l : (List Int)) (PreH1 : ((0 : Int) <= (i - 1))) (PreH2 : ((i - 1) < n_pre)) (PreH3 : ((0 : Int) <= (j - 1))) (PreH4 : ((j - 1) < n_pre)) (PreH5 : ((0 : Int) <= ((stride * i) + j))) (PreH6 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH8 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH9 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH10 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH11 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH12 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= n_pre)) (PreH16 : (stride = (n_pre + 1))) (PreH17 : ((0 : Int) <= n_pre)) (PreH18 : (n_pre <= 1000)) (PreH19 : ((Zlength (xs)) = n_pre)) (PreH20 : ((Zlength (ys)) = n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (1 <= j)) (PreH24 : (j <= (n_pre + 1))) (PreH25 : ((0 : Int) <= ((stride * i) + j))) (PreH26 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH27 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH28 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH29 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (intArray.full x_pre n_pre xs)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def longest_common_sequence_safety_wit_18 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table : (List (Option Int))) (table_l : (List Int)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table) (None)) = None)) (PreH9 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))))))) (PreH10 : ((0 : Int) <= (Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))))) (PreH11 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))) <= n_pre)) (PreH12 : ((Znth (i - 1) xs (0 : Int)) = (Znth (j - 1) ys (0 : Int)))) (PreH13 : ((0 : Int) <= (i - 1))) (PreH14 : ((i - 1) < n_pre)) (PreH15 : ((0 : Int) <= (j - 1))) (PreH16 : ((j - 1) < n_pre)) (PreH17 : ((0 : Int) <= ((stride * i) + j))) (PreH18 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH19 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH20 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH21 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH22 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH24 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= n_pre)) (PreH28 : (stride = (n_pre + 1))) (PreH29 : ((0 : Int) <= n_pre)) (PreH30 : (n_pre <= 1000)) (PreH31 : ((Zlength (xs)) = n_pre)) (PreH32 : ((Zlength (ys)) = n_pre)) (PreH33 : (1 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (1 <= j)) (PreH36 : (j <= (n_pre + 1))) (PreH37 : ((0 : Int) <= ((stride * i) + j))) (PreH38 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH39 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH40 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH41 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.mixed_seg ( &( "table" ) ) (0 : Int) (((n_pre + 1) * (i - 1)) + (j - 1)) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table)))
  ** (((( &( "table" ) ) + ((((n_pre + 1) * (i - 1)) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int)))))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * (i - 1)) + (j - 1)) + 1) (((n_pre + 1) * i) + j) (sublist (((((n_pre + 1) * (i - 1)) + (j - 1)) + 1)) ((((n_pre + 1) * i) + j)) (mixed_table)))
  ** (intArray.undef_seg ( &( "table" ) ) (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ (((stride * i) + j) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((stride * i) + j)) ”

noncomputable def longest_common_sequence_safety_wit_19 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table : (List (Option Int))) (table_l : (List Int)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table) (None)) = None)) (PreH9 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))))))) (PreH10 : ((0 : Int) <= (Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))))) (PreH11 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))) <= n_pre)) (PreH12 : ((Znth (i - 1) xs (0 : Int)) = (Znth (j - 1) ys (0 : Int)))) (PreH13 : ((0 : Int) <= (i - 1))) (PreH14 : ((i - 1) < n_pre)) (PreH15 : ((0 : Int) <= (j - 1))) (PreH16 : ((j - 1) < n_pre)) (PreH17 : ((0 : Int) <= ((stride * i) + j))) (PreH18 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH19 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH20 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH21 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH22 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH24 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= n_pre)) (PreH28 : (stride = (n_pre + 1))) (PreH29 : ((0 : Int) <= n_pre)) (PreH30 : (n_pre <= 1000)) (PreH31 : ((Zlength (xs)) = n_pre)) (PreH32 : ((Zlength (ys)) = n_pre)) (PreH33 : (1 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (1 <= j)) (PreH36 : (j <= (n_pre + 1))) (PreH37 : ((0 : Int) <= ((stride * i) + j))) (PreH38 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH39 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH40 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH41 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.mixed_seg ( &( "table" ) ) (0 : Int) (((n_pre + 1) * (i - 1)) + (j - 1)) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table)))
  ** (((( &( "table" ) ) + ((((n_pre + 1) * (i - 1)) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int)))))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * (i - 1)) + (j - 1)) + 1) (((n_pre + 1) * i) + j) (sublist (((((n_pre + 1) * (i - 1)) + (j - 1)) + 1)) ((((n_pre + 1) * i) + j)) (mixed_table)))
  ** (intArray.undef_seg ( &( "table" ) ) (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ ((stride * i) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (stride * i)) ”

noncomputable def longest_common_sequence_safety_wit_20 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table : (List (Option Int))) (table_l : (List Int)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table) (None)) = None)) (PreH9 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))))))) (PreH10 : ((0 : Int) <= (Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))))) (PreH11 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))) <= n_pre)) (PreH12 : ((Znth (i - 1) xs (0 : Int)) = (Znth (j - 1) ys (0 : Int)))) (PreH13 : ((0 : Int) <= (i - 1))) (PreH14 : ((i - 1) < n_pre)) (PreH15 : ((0 : Int) <= (j - 1))) (PreH16 : ((j - 1) < n_pre)) (PreH17 : ((0 : Int) <= ((stride * i) + j))) (PreH18 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH19 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH20 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH21 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH22 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH24 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= n_pre)) (PreH28 : (stride = (n_pre + 1))) (PreH29 : ((0 : Int) <= n_pre)) (PreH30 : (n_pre <= 1000)) (PreH31 : ((Zlength (xs)) = n_pre)) (PreH32 : ((Zlength (ys)) = n_pre)) (PreH33 : (1 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (1 <= j)) (PreH36 : (j <= (n_pre + 1))) (PreH37 : ((0 : Int) <= ((stride * i) + j))) (PreH38 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH39 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH40 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH41 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (((( &( "table" ) ) + (((stride * (i - 1)) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int)))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.mixed_seg ( &( "table" ) ) (0 : Int) (((n_pre + 1) * (i - 1)) + (j - 1)) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table)))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * (i - 1)) + (j - 1)) + 1) (((n_pre + 1) * i) + j) (sublist (((((n_pre + 1) * (i - 1)) + (j - 1)) + 1)) ((((n_pre + 1) * i) + j)) (mixed_table)))
  ** (intArray.undef_seg ( &( "table" ) ) (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ (((Znth (((((Zlength (xs)) + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))) + 1)) ”

noncomputable def longest_common_sequence_safety_wit_21 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table : (List (Option Int))) (table_l : (List Int)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table) (None)) = None)) (PreH9 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))))))) (PreH10 : ((0 : Int) <= (Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))))) (PreH11 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))) <= n_pre)) (PreH12 : ((Znth (i - 1) xs (0 : Int)) = (Znth (j - 1) ys (0 : Int)))) (PreH13 : ((0 : Int) <= (i - 1))) (PreH14 : ((i - 1) < n_pre)) (PreH15 : ((0 : Int) <= (j - 1))) (PreH16 : ((j - 1) < n_pre)) (PreH17 : ((0 : Int) <= ((stride * i) + j))) (PreH18 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH19 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH20 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH21 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH22 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH24 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= n_pre)) (PreH28 : (stride = (n_pre + 1))) (PreH29 : ((0 : Int) <= n_pre)) (PreH30 : (n_pre <= 1000)) (PreH31 : ((Zlength (xs)) = n_pre)) (PreH32 : ((Zlength (ys)) = n_pre)) (PreH33 : (1 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (1 <= j)) (PreH36 : (j <= (n_pre + 1))) (PreH37 : ((0 : Int) <= ((stride * i) + j))) (PreH38 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH39 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH40 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH41 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.mixed_seg ( &( "table" ) ) (0 : Int) (((n_pre + 1) * (i - 1)) + (j - 1)) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table)))
  ** (((( &( "table" ) ) + ((((n_pre + 1) * (i - 1)) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int)))))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * (i - 1)) + (j - 1)) + 1) (((n_pre + 1) * i) + j) (sublist (((((n_pre + 1) * (i - 1)) + (j - 1)) + 1)) ((((n_pre + 1) * i) + j)) (mixed_table)))
  ** (intArray.undef_seg ( &( "table" ) ) (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ (((stride * (i - 1)) + (j - 1)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((stride * (i - 1)) + (j - 1))) ”

noncomputable def longest_common_sequence_safety_wit_22 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table : (List (Option Int))) (table_l : (List Int)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table) (None)) = None)) (PreH9 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))))))) (PreH10 : ((0 : Int) <= (Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))))) (PreH11 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))) <= n_pre)) (PreH12 : ((Znth (i - 1) xs (0 : Int)) = (Znth (j - 1) ys (0 : Int)))) (PreH13 : ((0 : Int) <= (i - 1))) (PreH14 : ((i - 1) < n_pre)) (PreH15 : ((0 : Int) <= (j - 1))) (PreH16 : ((j - 1) < n_pre)) (PreH17 : ((0 : Int) <= ((stride * i) + j))) (PreH18 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH19 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH20 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH21 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH22 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH24 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= n_pre)) (PreH28 : (stride = (n_pre + 1))) (PreH29 : ((0 : Int) <= n_pre)) (PreH30 : (n_pre <= 1000)) (PreH31 : ((Zlength (xs)) = n_pre)) (PreH32 : ((Zlength (ys)) = n_pre)) (PreH33 : (1 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (1 <= j)) (PreH36 : (j <= (n_pre + 1))) (PreH37 : ((0 : Int) <= ((stride * i) + j))) (PreH38 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH39 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH40 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH41 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.mixed_seg ( &( "table" ) ) (0 : Int) (((n_pre + 1) * (i - 1)) + (j - 1)) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table)))
  ** (((( &( "table" ) ) + ((((n_pre + 1) * (i - 1)) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int)))))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * (i - 1)) + (j - 1)) + 1) (((n_pre + 1) * i) + j) (sublist (((((n_pre + 1) * (i - 1)) + (j - 1)) + 1)) ((((n_pre + 1) * i) + j)) (mixed_table)))
  ** (intArray.undef_seg ( &( "table" ) ) (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ ((j - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j - 1)) ”

noncomputable def longest_common_sequence_safety_wit_23 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table : (List (Option Int))) (table_l : (List Int)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table) (None)) = None)) (PreH9 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))))))) (PreH10 : ((0 : Int) <= (Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))))) (PreH11 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))) <= n_pre)) (PreH12 : ((Znth (i - 1) xs (0 : Int)) = (Znth (j - 1) ys (0 : Int)))) (PreH13 : ((0 : Int) <= (i - 1))) (PreH14 : ((i - 1) < n_pre)) (PreH15 : ((0 : Int) <= (j - 1))) (PreH16 : ((j - 1) < n_pre)) (PreH17 : ((0 : Int) <= ((stride * i) + j))) (PreH18 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH19 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH20 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH21 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH22 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH24 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= n_pre)) (PreH28 : (stride = (n_pre + 1))) (PreH29 : ((0 : Int) <= n_pre)) (PreH30 : (n_pre <= 1000)) (PreH31 : ((Zlength (xs)) = n_pre)) (PreH32 : ((Zlength (ys)) = n_pre)) (PreH33 : (1 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (1 <= j)) (PreH36 : (j <= (n_pre + 1))) (PreH37 : ((0 : Int) <= ((stride * i) + j))) (PreH38 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH39 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH40 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH41 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.mixed_seg ( &( "table" ) ) (0 : Int) (((n_pre + 1) * (i - 1)) + (j - 1)) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table)))
  ** (((( &( "table" ) ) + ((((n_pre + 1) * (i - 1)) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int)))))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * (i - 1)) + (j - 1)) + 1) (((n_pre + 1) * i) + j) (sublist (((((n_pre + 1) * (i - 1)) + (j - 1)) + 1)) ((((n_pre + 1) * i) + j)) (mixed_table)))
  ** (intArray.undef_seg ( &( "table" ) ) (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ ((stride * (i - 1)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (stride * (i - 1))) ”

noncomputable def longest_common_sequence_safety_wit_24 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table : (List (Option Int))) (table_l : (List Int)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table) (None)) = None)) (PreH9 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))))))) (PreH10 : ((0 : Int) <= (Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))))) (PreH11 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))) <= n_pre)) (PreH12 : ((Znth (i - 1) xs (0 : Int)) = (Znth (j - 1) ys (0 : Int)))) (PreH13 : ((0 : Int) <= (i - 1))) (PreH14 : ((i - 1) < n_pre)) (PreH15 : ((0 : Int) <= (j - 1))) (PreH16 : ((j - 1) < n_pre)) (PreH17 : ((0 : Int) <= ((stride * i) + j))) (PreH18 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH19 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH20 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH21 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH22 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH24 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= n_pre)) (PreH28 : (stride = (n_pre + 1))) (PreH29 : ((0 : Int) <= n_pre)) (PreH30 : (n_pre <= 1000)) (PreH31 : ((Zlength (xs)) = n_pre)) (PreH32 : ((Zlength (ys)) = n_pre)) (PreH33 : (1 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (1 <= j)) (PreH36 : (j <= (n_pre + 1))) (PreH37 : ((0 : Int) <= ((stride * i) + j))) (PreH38 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH39 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH40 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH41 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.mixed_seg ( &( "table" ) ) (0 : Int) (((n_pre + 1) * (i - 1)) + (j - 1)) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table)))
  ** (((( &( "table" ) ) + ((((n_pre + 1) * (i - 1)) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int)))))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * (i - 1)) + (j - 1)) + 1) (((n_pre + 1) * i) + j) (sublist (((((n_pre + 1) * (i - 1)) + (j - 1)) + 1)) ((((n_pre + 1) * i) + j)) (mixed_table)))
  ** (intArray.undef_seg ( &( "table" ) ) (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def longest_common_sequence_safety_wit_25 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table : (List (Option Int))) (table_l : (List Int)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table) (None)) = None)) (PreH9 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))))))) (PreH10 : ((0 : Int) <= (Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))))) (PreH11 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))) <= n_pre)) (PreH12 : ((Znth (i - 1) xs (0 : Int)) = (Znth (j - 1) ys (0 : Int)))) (PreH13 : ((0 : Int) <= (i - 1))) (PreH14 : ((i - 1) < n_pre)) (PreH15 : ((0 : Int) <= (j - 1))) (PreH16 : ((j - 1) < n_pre)) (PreH17 : ((0 : Int) <= ((stride * i) + j))) (PreH18 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH19 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH20 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH21 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH22 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH24 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= n_pre)) (PreH28 : (stride = (n_pre + 1))) (PreH29 : ((0 : Int) <= n_pre)) (PreH30 : (n_pre <= 1000)) (PreH31 : ((Zlength (xs)) = n_pre)) (PreH32 : ((Zlength (ys)) = n_pre)) (PreH33 : (1 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (1 <= j)) (PreH36 : (j <= (n_pre + 1))) (PreH37 : ((0 : Int) <= ((stride * i) + j))) (PreH38 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH39 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH40 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH41 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.mixed_seg ( &( "table" ) ) (0 : Int) (((n_pre + 1) * (i - 1)) + (j - 1)) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table)))
  ** (((( &( "table" ) ) + ((((n_pre + 1) * (i - 1)) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int)))))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * (i - 1)) + (j - 1)) + 1) (((n_pre + 1) * i) + j) (sublist (((((n_pre + 1) * (i - 1)) + (j - 1)) + 1)) ((((n_pre + 1) * i) + j)) (mixed_table)))
  ** (intArray.undef_seg ( &( "table" ) ) (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def longest_common_sequence_safety_wit_26 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table : (List (Option Int))) (table_l : (List Int)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table) (None)) = None)) (PreH9 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))))))) (PreH10 : ((0 : Int) <= (Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))))) (PreH11 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))) <= n_pre)) (PreH12 : ((Znth (i - 1) xs (0 : Int)) = (Znth (j - 1) ys (0 : Int)))) (PreH13 : ((0 : Int) <= (i - 1))) (PreH14 : ((i - 1) < n_pre)) (PreH15 : ((0 : Int) <= (j - 1))) (PreH16 : ((j - 1) < n_pre)) (PreH17 : ((0 : Int) <= ((stride * i) + j))) (PreH18 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH19 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH20 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH21 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH22 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH24 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= n_pre)) (PreH28 : (stride = (n_pre + 1))) (PreH29 : ((0 : Int) <= n_pre)) (PreH30 : (n_pre <= 1000)) (PreH31 : ((Zlength (xs)) = n_pre)) (PreH32 : ((Zlength (ys)) = n_pre)) (PreH33 : (1 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (1 <= j)) (PreH36 : (j <= (n_pre + 1))) (PreH37 : ((0 : Int) <= ((stride * i) + j))) (PreH38 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH39 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH40 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH41 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.mixed_seg ( &( "table" ) ) (0 : Int) (((n_pre + 1) * (i - 1)) + (j - 1)) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table)))
  ** (((( &( "table" ) ) + ((((n_pre + 1) * (i - 1)) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int)))))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * (i - 1)) + (j - 1)) + 1) (((n_pre + 1) * i) + j) (sublist (((((n_pre + 1) * (i - 1)) + (j - 1)) + 1)) ((((n_pre + 1) * i) + j)) (mixed_table)))
  ** (intArray.undef_seg ( &( "table" ) ) (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def longest_common_sequence_safety_wit_27 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table : (List (Option Int))) (table_l : (List Int)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table) (None)) = None)) (PreH9 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))))))) (PreH10 : ((0 : Int) <= (Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))))) (PreH11 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))) <= n_pre)) (PreH12 : ((Znth (i - 1) xs (0 : Int)) = (Znth (j - 1) ys (0 : Int)))) (PreH13 : ((0 : Int) <= (i - 1))) (PreH14 : ((i - 1) < n_pre)) (PreH15 : ((0 : Int) <= (j - 1))) (PreH16 : ((j - 1) < n_pre)) (PreH17 : ((0 : Int) <= ((stride * i) + j))) (PreH18 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH19 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH20 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH21 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH22 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH24 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= n_pre)) (PreH28 : (stride = (n_pre + 1))) (PreH29 : ((0 : Int) <= n_pre)) (PreH30 : (n_pre <= 1000)) (PreH31 : ((Zlength (xs)) = n_pre)) (PreH32 : ((Zlength (ys)) = n_pre)) (PreH33 : (1 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (1 <= j)) (PreH36 : (j <= (n_pre + 1))) (PreH37 : ((0 : Int) <= ((stride * i) + j))) (PreH38 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH39 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH40 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH41 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (((( &( "table" ) ) + (((stride * (i - 1)) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int)))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.mixed_seg ( &( "table" ) ) (0 : Int) (((n_pre + 1) * (i - 1)) + (j - 1)) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table)))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * (i - 1)) + (j - 1)) + 1) (((n_pre + 1) * i) + j) (sublist (((((n_pre + 1) * (i - 1)) + (j - 1)) + 1)) ((((n_pre + 1) * i) + j)) (mixed_table)))
  ** (intArray.undef_seg ( &( "table" ) ) (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def longest_common_sequence_safety_wit_28 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table : (List (Option Int))) (table_l : (List Int)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table) (None)) = None)) (PreH9 : ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l) ((0 : Int))))))) (PreH10 : ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l) ((0 : Int))))))) (PreH11 : ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int)))) (PreH12 : ((0 : Int) <= (i - 1))) (PreH13 : ((i - 1) < n_pre)) (PreH14 : ((0 : Int) <= (j - 1))) (PreH15 : ((j - 1) < n_pre)) (PreH16 : ((0 : Int) <= ((stride * i) + j))) (PreH17 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH18 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH19 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH20 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH21 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH22 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH23 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH24 : (n_pre <= INT_MAX)) (PreH25 : (n_pre >= INT_MIN)) (PreH26 : (j <= n_pre)) (PreH27 : (stride = (n_pre + 1))) (PreH28 : ((0 : Int) <= n_pre)) (PreH29 : (n_pre <= 1000)) (PreH30 : ((Zlength (xs)) = n_pre)) (PreH31 : ((Zlength (ys)) = n_pre)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= (n_pre + 1))) (PreH36 : ((0 : Int) <= ((stride * i) + j))) (PreH37 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH38 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH39 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH40 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.mixed_seg ( &( "table" ) ) (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table)))
  ** (((( &( "table" ) ) + ((((n_pre + 1) * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l) ((0 : Int)))))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table)))
  ** (((( &( "table" ) ) + ((((n_pre + 1) * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l) ((0 : Int)))))
  ** (intArray.undef_seg ( &( "table" ) ) (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ (((stride * (i - 1)) + j) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((stride * (i - 1)) + j)) ”

noncomputable def longest_common_sequence_safety_wit_29 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table : (List (Option Int))) (table_l : (List Int)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table) (None)) = None)) (PreH9 : ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l) ((0 : Int))))))) (PreH10 : ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l) ((0 : Int))))))) (PreH11 : ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int)))) (PreH12 : ((0 : Int) <= (i - 1))) (PreH13 : ((i - 1) < n_pre)) (PreH14 : ((0 : Int) <= (j - 1))) (PreH15 : ((j - 1) < n_pre)) (PreH16 : ((0 : Int) <= ((stride * i) + j))) (PreH17 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH18 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH19 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH20 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH21 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH22 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH23 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH24 : (n_pre <= INT_MAX)) (PreH25 : (n_pre >= INT_MIN)) (PreH26 : (j <= n_pre)) (PreH27 : (stride = (n_pre + 1))) (PreH28 : ((0 : Int) <= n_pre)) (PreH29 : (n_pre <= 1000)) (PreH30 : ((Zlength (xs)) = n_pre)) (PreH31 : ((Zlength (ys)) = n_pre)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= (n_pre + 1))) (PreH36 : ((0 : Int) <= ((stride * i) + j))) (PreH37 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH38 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH39 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH40 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.mixed_seg ( &( "table" ) ) (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table)))
  ** (((( &( "table" ) ) + ((((n_pre + 1) * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l) ((0 : Int)))))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table)))
  ** (((( &( "table" ) ) + ((((n_pre + 1) * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l) ((0 : Int)))))
  ** (intArray.undef_seg ( &( "table" ) ) (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ ((stride * (i - 1)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (stride * (i - 1))) ”

noncomputable def longest_common_sequence_safety_wit_30 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table : (List (Option Int))) (table_l : (List Int)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table) (None)) = None)) (PreH9 : ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l) ((0 : Int))))))) (PreH10 : ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l) ((0 : Int))))))) (PreH11 : ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int)))) (PreH12 : ((0 : Int) <= (i - 1))) (PreH13 : ((i - 1) < n_pre)) (PreH14 : ((0 : Int) <= (j - 1))) (PreH15 : ((j - 1) < n_pre)) (PreH16 : ((0 : Int) <= ((stride * i) + j))) (PreH17 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH18 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH19 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH20 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH21 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH22 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH23 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH24 : (n_pre <= INT_MAX)) (PreH25 : (n_pre >= INT_MIN)) (PreH26 : (j <= n_pre)) (PreH27 : (stride = (n_pre + 1))) (PreH28 : ((0 : Int) <= n_pre)) (PreH29 : (n_pre <= 1000)) (PreH30 : ((Zlength (xs)) = n_pre)) (PreH31 : ((Zlength (ys)) = n_pre)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= (n_pre + 1))) (PreH36 : ((0 : Int) <= ((stride * i) + j))) (PreH37 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH38 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH39 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH40 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.mixed_seg ( &( "table" ) ) (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table)))
  ** (((( &( "table" ) ) + ((((n_pre + 1) * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l) ((0 : Int)))))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table)))
  ** (((( &( "table" ) ) + ((((n_pre + 1) * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l) ((0 : Int)))))
  ** (intArray.undef_seg ( &( "table" ) ) (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def longest_common_sequence_safety_wit_31 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table : (List (Option Int))) (table_l : (List Int)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table) (None)) = None)) (PreH9 : ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l) ((0 : Int))))))) (PreH10 : ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l) ((0 : Int))))))) (PreH11 : ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int)))) (PreH12 : ((0 : Int) <= (i - 1))) (PreH13 : ((i - 1) < n_pre)) (PreH14 : ((0 : Int) <= (j - 1))) (PreH15 : ((j - 1) < n_pre)) (PreH16 : ((0 : Int) <= ((stride * i) + j))) (PreH17 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH18 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH19 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH20 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH21 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH22 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH23 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH24 : (n_pre <= INT_MAX)) (PreH25 : (n_pre >= INT_MIN)) (PreH26 : (j <= n_pre)) (PreH27 : (stride = (n_pre + 1))) (PreH28 : ((0 : Int) <= n_pre)) (PreH29 : (n_pre <= 1000)) (PreH30 : ((Zlength (xs)) = n_pre)) (PreH31 : ((Zlength (ys)) = n_pre)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= (n_pre + 1))) (PreH36 : ((0 : Int) <= ((stride * i) + j))) (PreH37 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH38 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH39 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH40 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.mixed_seg ( &( "table" ) ) (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table)))
  ** (((( &( "table" ) ) + ((((n_pre + 1) * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l) ((0 : Int)))))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table)))
  ** (((( &( "table" ) ) + ((((n_pre + 1) * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l) ((0 : Int)))))
  ** (intArray.undef_seg ( &( "table" ) ) (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def longest_common_sequence_safety_wit_32 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table : (List (Option Int))) (table_l : (List Int)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table) (None)) = None)) (PreH9 : ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l) ((0 : Int))))))) (PreH10 : ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l) ((0 : Int))))))) (PreH11 : ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int)))) (PreH12 : ((0 : Int) <= (i - 1))) (PreH13 : ((i - 1) < n_pre)) (PreH14 : ((0 : Int) <= (j - 1))) (PreH15 : ((j - 1) < n_pre)) (PreH16 : ((0 : Int) <= ((stride * i) + j))) (PreH17 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH18 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH19 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH20 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH21 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH22 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH23 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH24 : (n_pre <= INT_MAX)) (PreH25 : (n_pre >= INT_MIN)) (PreH26 : (j <= n_pre)) (PreH27 : (stride = (n_pre + 1))) (PreH28 : ((0 : Int) <= n_pre)) (PreH29 : (n_pre <= 1000)) (PreH30 : ((Zlength (xs)) = n_pre)) (PreH31 : ((Zlength (ys)) = n_pre)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= (n_pre + 1))) (PreH36 : ((0 : Int) <= ((stride * i) + j))) (PreH37 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH38 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH39 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH40 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (((( &( "table" ) ) + (((stride * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l) ((0 : Int)))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.mixed_seg ( &( "table" ) ) (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table)))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table)))
  ** (((( &( "table" ) ) + ((((n_pre + 1) * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l) ((0 : Int)))))
  ** (intArray.undef_seg ( &( "table" ) ) (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "above" ) )) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l) ((0 : Int)))))
  ** ((( &( "left" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ (((stride * i) + (j - 1)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((stride * i) + (j - 1))) ”

noncomputable def longest_common_sequence_safety_wit_33 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table : (List (Option Int))) (table_l : (List Int)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table) (None)) = None)) (PreH9 : ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l) ((0 : Int))))))) (PreH10 : ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l) ((0 : Int))))))) (PreH11 : ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int)))) (PreH12 : ((0 : Int) <= (i - 1))) (PreH13 : ((i - 1) < n_pre)) (PreH14 : ((0 : Int) <= (j - 1))) (PreH15 : ((j - 1) < n_pre)) (PreH16 : ((0 : Int) <= ((stride * i) + j))) (PreH17 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH18 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH19 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH20 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH21 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH22 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH23 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH24 : (n_pre <= INT_MAX)) (PreH25 : (n_pre >= INT_MIN)) (PreH26 : (j <= n_pre)) (PreH27 : (stride = (n_pre + 1))) (PreH28 : ((0 : Int) <= n_pre)) (PreH29 : (n_pre <= 1000)) (PreH30 : ((Zlength (xs)) = n_pre)) (PreH31 : ((Zlength (ys)) = n_pre)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= (n_pre + 1))) (PreH36 : ((0 : Int) <= ((stride * i) + j))) (PreH37 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH38 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH39 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH40 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (((( &( "table" ) ) + (((stride * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l) ((0 : Int)))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.mixed_seg ( &( "table" ) ) (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table)))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table)))
  ** (((( &( "table" ) ) + ((((n_pre + 1) * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l) ((0 : Int)))))
  ** (intArray.undef_seg ( &( "table" ) ) (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "above" ) )) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l) ((0 : Int)))))
  ** ((( &( "left" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ ((j - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j - 1)) ”

noncomputable def longest_common_sequence_safety_wit_34 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table : (List (Option Int))) (table_l : (List Int)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table) (None)) = None)) (PreH9 : ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l) ((0 : Int))))))) (PreH10 : ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l) ((0 : Int))))))) (PreH11 : ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int)))) (PreH12 : ((0 : Int) <= (i - 1))) (PreH13 : ((i - 1) < n_pre)) (PreH14 : ((0 : Int) <= (j - 1))) (PreH15 : ((j - 1) < n_pre)) (PreH16 : ((0 : Int) <= ((stride * i) + j))) (PreH17 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH18 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH19 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH20 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH21 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH22 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH23 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH24 : (n_pre <= INT_MAX)) (PreH25 : (n_pre >= INT_MIN)) (PreH26 : (j <= n_pre)) (PreH27 : (stride = (n_pre + 1))) (PreH28 : ((0 : Int) <= n_pre)) (PreH29 : (n_pre <= 1000)) (PreH30 : ((Zlength (xs)) = n_pre)) (PreH31 : ((Zlength (ys)) = n_pre)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= (n_pre + 1))) (PreH36 : ((0 : Int) <= ((stride * i) + j))) (PreH37 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH38 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH39 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH40 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (((( &( "table" ) ) + (((stride * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l) ((0 : Int)))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.mixed_seg ( &( "table" ) ) (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table)))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table)))
  ** (((( &( "table" ) ) + ((((n_pre + 1) * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l) ((0 : Int)))))
  ** (intArray.undef_seg ( &( "table" ) ) (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "above" ) )) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l) ((0 : Int)))))
  ** ((( &( "left" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ ((stride * i) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (stride * i)) ”

noncomputable def longest_common_sequence_safety_wit_35 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table : (List (Option Int))) (table_l : (List Int)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table) (None)) = None)) (PreH9 : ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l) ((0 : Int))))))) (PreH10 : ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l) ((0 : Int))))))) (PreH11 : ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int)))) (PreH12 : ((0 : Int) <= (i - 1))) (PreH13 : ((i - 1) < n_pre)) (PreH14 : ((0 : Int) <= (j - 1))) (PreH15 : ((j - 1) < n_pre)) (PreH16 : ((0 : Int) <= ((stride * i) + j))) (PreH17 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH18 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH19 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH20 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH21 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH22 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH23 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH24 : (n_pre <= INT_MAX)) (PreH25 : (n_pre >= INT_MIN)) (PreH26 : (j <= n_pre)) (PreH27 : (stride = (n_pre + 1))) (PreH28 : ((0 : Int) <= n_pre)) (PreH29 : (n_pre <= 1000)) (PreH30 : ((Zlength (xs)) = n_pre)) (PreH31 : ((Zlength (ys)) = n_pre)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= (n_pre + 1))) (PreH36 : ((0 : Int) <= ((stride * i) + j))) (PreH37 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH38 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH39 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH40 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (((( &( "table" ) ) + (((stride * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l) ((0 : Int)))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.mixed_seg ( &( "table" ) ) (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table)))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table)))
  ** (((( &( "table" ) ) + ((((n_pre + 1) * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l) ((0 : Int)))))
  ** (intArray.undef_seg ( &( "table" ) ) (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "above" ) )) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l) ((0 : Int)))))
  ** ((( &( "left" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def longest_common_sequence_safety_wit_36 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table : (List (Option Int))) (table_l : (List Int)) (PreH1 : ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l) ((0 : Int))) >= (Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l) ((0 : Int))))) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH7 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) (PreH9 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table) (None)) = None)) (PreH10 : ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l) ((0 : Int))))))) (PreH11 : ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l) ((0 : Int))))))) (PreH12 : ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int)))) (PreH13 : ((0 : Int) <= (i - 1))) (PreH14 : ((i - 1) < n_pre)) (PreH15 : ((0 : Int) <= (j - 1))) (PreH16 : ((j - 1) < n_pre)) (PreH17 : ((0 : Int) <= ((stride * i) + j))) (PreH18 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH19 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH20 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH21 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH22 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH24 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= n_pre)) (PreH28 : (stride = (n_pre + 1))) (PreH29 : ((0 : Int) <= n_pre)) (PreH30 : (n_pre <= 1000)) (PreH31 : ((Zlength (xs)) = n_pre)) (PreH32 : ((Zlength (ys)) = n_pre)) (PreH33 : (1 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (1 <= j)) (PreH36 : (j <= (n_pre + 1))) (PreH37 : ((0 : Int) <= ((stride * i) + j))) (PreH38 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH39 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH40 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH41 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (((( &( "table" ) ) + (((stride * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l) ((0 : Int)))))
  ** (((( &( "table" ) ) + (((stride * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l) ((0 : Int)))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.mixed_seg ( &( "table" ) ) (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table)))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table)))
  ** (intArray.undef_seg ( &( "table" ) ) (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "above" ) )) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l) ((0 : Int)))))
  ** ((( &( "left" ) )) # Int |-> ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l) ((0 : Int)))))
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ (((stride * i) + j) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((stride * i) + j)) ”

noncomputable def longest_common_sequence_safety_wit_37 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table : (List (Option Int))) (table_l : (List Int)) (PreH1 : ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l) ((0 : Int))) >= (Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l) ((0 : Int))))) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH7 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) (PreH9 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table) (None)) = None)) (PreH10 : ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l) ((0 : Int))))))) (PreH11 : ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l) ((0 : Int))))))) (PreH12 : ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int)))) (PreH13 : ((0 : Int) <= (i - 1))) (PreH14 : ((i - 1) < n_pre)) (PreH15 : ((0 : Int) <= (j - 1))) (PreH16 : ((j - 1) < n_pre)) (PreH17 : ((0 : Int) <= ((stride * i) + j))) (PreH18 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH19 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH20 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH21 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH22 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH24 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= n_pre)) (PreH28 : (stride = (n_pre + 1))) (PreH29 : ((0 : Int) <= n_pre)) (PreH30 : (n_pre <= 1000)) (PreH31 : ((Zlength (xs)) = n_pre)) (PreH32 : ((Zlength (ys)) = n_pre)) (PreH33 : (1 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (1 <= j)) (PreH36 : (j <= (n_pre + 1))) (PreH37 : ((0 : Int) <= ((stride * i) + j))) (PreH38 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH39 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH40 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH41 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (((( &( "table" ) ) + (((stride * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l) ((0 : Int)))))
  ** (((( &( "table" ) ) + (((stride * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l) ((0 : Int)))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.mixed_seg ( &( "table" ) ) (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table)))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table)))
  ** (intArray.undef_seg ( &( "table" ) ) (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "above" ) )) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l) ((0 : Int)))))
  ** ((( &( "left" ) )) # Int |-> ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l) ((0 : Int)))))
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ ((stride * i) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (stride * i)) ”

noncomputable def longest_common_sequence_safety_wit_38 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table : (List (Option Int))) (table_l : (List Int)) (PreH1 : ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l) ((0 : Int))) < (Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l) ((0 : Int))))) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH7 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) (PreH9 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table) (None)) = None)) (PreH10 : ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l) ((0 : Int))))))) (PreH11 : ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l) ((0 : Int))))))) (PreH12 : ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int)))) (PreH13 : ((0 : Int) <= (i - 1))) (PreH14 : ((i - 1) < n_pre)) (PreH15 : ((0 : Int) <= (j - 1))) (PreH16 : ((j - 1) < n_pre)) (PreH17 : ((0 : Int) <= ((stride * i) + j))) (PreH18 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH19 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH20 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH21 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH22 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH24 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= n_pre)) (PreH28 : (stride = (n_pre + 1))) (PreH29 : ((0 : Int) <= n_pre)) (PreH30 : (n_pre <= 1000)) (PreH31 : ((Zlength (xs)) = n_pre)) (PreH32 : ((Zlength (ys)) = n_pre)) (PreH33 : (1 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (1 <= j)) (PreH36 : (j <= (n_pre + 1))) (PreH37 : ((0 : Int) <= ((stride * i) + j))) (PreH38 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH39 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH40 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH41 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (((( &( "table" ) ) + (((stride * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l) ((0 : Int)))))
  ** (((( &( "table" ) ) + (((stride * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l) ((0 : Int)))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.mixed_seg ( &( "table" ) ) (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table)))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table)))
  ** (intArray.undef_seg ( &( "table" ) ) (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "above" ) )) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l) ((0 : Int)))))
  ** ((( &( "left" ) )) # Int |-> ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l) ((0 : Int)))))
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ (((stride * i) + j) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((stride * i) + j)) ”

noncomputable def longest_common_sequence_safety_wit_39 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table : (List (Option Int))) (table_l : (List Int)) (PreH1 : ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l) ((0 : Int))) < (Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l) ((0 : Int))))) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH7 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) (PreH9 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table) (None)) = None)) (PreH10 : ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l) ((0 : Int))))))) (PreH11 : ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l) ((0 : Int))))))) (PreH12 : ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int)))) (PreH13 : ((0 : Int) <= (i - 1))) (PreH14 : ((i - 1) < n_pre)) (PreH15 : ((0 : Int) <= (j - 1))) (PreH16 : ((j - 1) < n_pre)) (PreH17 : ((0 : Int) <= ((stride * i) + j))) (PreH18 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH19 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH20 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH21 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH22 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH24 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= n_pre)) (PreH28 : (stride = (n_pre + 1))) (PreH29 : ((0 : Int) <= n_pre)) (PreH30 : (n_pre <= 1000)) (PreH31 : ((Zlength (xs)) = n_pre)) (PreH32 : ((Zlength (ys)) = n_pre)) (PreH33 : (1 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (1 <= j)) (PreH36 : (j <= (n_pre + 1))) (PreH37 : ((0 : Int) <= ((stride * i) + j))) (PreH38 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH39 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH40 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH41 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (((( &( "table" ) ) + (((stride * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l) ((0 : Int)))))
  ** (((( &( "table" ) ) + (((stride * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l) ((0 : Int)))))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.mixed_seg ( &( "table" ) ) (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table)))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table)))
  ** (intArray.undef_seg ( &( "table" ) ) (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "above" ) )) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l) ((0 : Int)))))
  ** ((( &( "left" ) )) # Int |-> ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l) ((0 : Int)))))
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ ((stride * i) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (stride * i)) ”

noncomputable def longest_common_sequence_safety_wit_40 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (stride : Int) (i : Int) (j : Int) (PreH1 : (stride = (n_pre + 1))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (xs)) = n_pre)) (PreH5 : ((Zlength (ys)) = n_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (1 <= (j + 1))) (PreH11 : ((j + 1) <= (n_pre + 1))) (PreH12 : ((0 : Int) <= ((stride * i) + (j + 1)))) (PreH13 : (((stride * i) + (j + 1)) <= ((n_pre + 1) * (n_pre + 1)))) (PreH14 : (LCSNRowProgress xs ys mixed_table table_l n_pre i (j + 1))) (PreH15 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH16 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def longest_common_sequence_safety_wit_41 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (stride : Int) (i : Int) (j : Int) (PreH1 : (stride = (n_pre + 1))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (xs)) = n_pre)) (PreH5 : ((Zlength (ys)) = n_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (1 <= (j + 1))) (PreH11 : ((j + 1) <= (n_pre + 1))) (PreH12 : ((0 : Int) <= ((stride * i) + (j + 1)))) (PreH13 : (((stride * i) + (j + 1)) <= ((n_pre + 1) * (n_pre + 1)))) (PreH14 : (LCSNRowProgress xs ys mixed_table table_l n_pre i (j + 1))) (PreH15 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH16 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def longest_common_sequence_safety_wit_42 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (i : Int) (stride : Int) (PreH1 : (j > n_pre)) (PreH2 : (stride = (n_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= (n_pre + 1))) (PreH11 : ((0 : Int) <= ((stride * i) + j))) (PreH12 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH13 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH14 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH15 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def longest_common_sequence_safety_wit_43 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (i : Int) (stride : Int) (PreH1 : (j > n_pre)) (PreH2 : (stride = (n_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= (n_pre + 1))) (PreH11 : ((0 : Int) <= ((stride * i) + j))) (PreH12 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH13 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH14 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH15 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def longest_common_sequence_safety_wit_44 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (stride : Int) (PreH1 : (stride = (n_pre + 1))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (xs)) = n_pre)) (PreH5 : ((Zlength (ys)) = n_pre)) (PreH6 : (LCSNRowsProgress xs ys mixed_table table_l n_pre (n_pre + 1))) (PreH7 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) (PreH9 : (LCSNTableResult xs ys n_pre table_l)) (PreH10 : ((0 : Int) <= ((stride * n_pre) + n_pre))) (PreH11 : (((stride * n_pre) + n_pre) < ((n_pre + 1) * (n_pre + 1)))) ,
  ((( &( "result" ) )) # Int |->_)
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) table_l)
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "j" ) )) # Int |->_)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ (((stride * n_pre) + n_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((stride * n_pre) + n_pre)) ”

noncomputable def longest_common_sequence_safety_wit_45 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (stride : Int) (PreH1 : (stride = (n_pre + 1))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (xs)) = n_pre)) (PreH5 : ((Zlength (ys)) = n_pre)) (PreH6 : (LCSNRowsProgress xs ys mixed_table table_l n_pre (n_pre + 1))) (PreH7 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) (PreH9 : (LCSNTableResult xs ys n_pre table_l)) (PreH10 : ((0 : Int) <= ((stride * n_pre) + n_pre))) (PreH11 : (((stride * n_pre) + n_pre) < ((n_pre + 1) * (n_pre + 1)))) ,
  ((( &( "result" ) )) # Int |->_)
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) table_l)
  ** ((( &( "i" ) )) # Int |->_)
  ** ((( &( "j" ) )) # Int |->_)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ ((stride * n_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (stride * n_pre)) ”

noncomputable def longest_common_sequence_entail_wit_1 : Prop :=
  (
forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (xs)) = n_pre)) (PreH4 : ((Zlength (ys)) = n_pre)) ,
  (intArray.undef_full ( &( "table" ) ) 1002001)
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
|--
  EX mixed_table : (List (Option Int)), EX table_l : (List Int),
  “ ((n_pre + 1) = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= ((n_pre + 1) * (0 : Int))) ” &&
  “ (((n_pre + 1) * (0 : Int)) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNColumnProgress mixed_table table_l n_pre (0 : Int)) ” &&
  “ ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1))) ”
  &&  (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
) \/
(
forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 1000)) (PreH3 : ((Zlength (xs)) = n_pre)) (PreH4 : ((Zlength (ys)) = n_pre)) ,
  (intArray.undef_full ( &( "table" ) ) 1002001)
|--
  EX mixed_table : (List (Option Int)), EX table_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= ((n_pre + 1) * (0 : Int))) ” &&
  “ (((n_pre + 1) * (0 : Int)) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNColumnProgress mixed_table table_l n_pre (0 : Int)) ” &&
  “ ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1))) ”
  &&  (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
)

noncomputable def longest_common_sequence_entail_wit_2 : Prop :=
  (
forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (i : Int) (stride : Int) (PreH1 : (i <= n_pre)) (PreH2 : (stride = (n_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= (n_pre + 1))) (PreH9 : ((0 : Int) <= (stride * i))) (PreH10 : ((stride * i) <= ((n_pre + 1) * (n_pre + 1)))) (PreH11 : (LCSNColumnProgress mixed_table table_l n_pre i)) (PreH12 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH13 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "j" ) )) # Int |->_)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ ((0 : Int) <= (stride * i)) ” &&
  “ ((stride * i) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (i <= n_pre) ” &&
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= (stride * i)) ” &&
  “ ((stride * i) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNColumnProgress mixed_table table_l n_pre i) ” &&
  “ ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1))) ”
  &&  ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "j" ) )) # Int |->_)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
) \/
(
forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (i : Int) (stride : Int) (PreH1 : (i <= INT_MAX)) (PreH2 : (stride <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (stride >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i <= n_pre)) (PreH8 : (stride = (n_pre + 1))) (PreH9 : ((0 : Int) <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : ((Zlength (xs)) = n_pre)) (PreH12 : ((Zlength (ys)) = n_pre)) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= (n_pre + 1))) (PreH15 : ((0 : Int) <= (stride * i))) (PreH16 : ((stride * i) <= ((n_pre + 1) * (n_pre + 1)))) (PreH17 : (LCSNColumnProgress mixed_table table_l n_pre i)) (PreH18 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH19 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  TT && emp 
|--
  “ (((n_pre + 1) * i) < ((n_pre + 1) * (n_pre + 1))) ”
  &&  emp
)

noncomputable def longest_common_sequence_entail_wit_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (i : Int) (stride : Int) (PreH1 : (i <= INT_MAX)) (PreH2 : (stride <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (stride >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : (i <= n_pre)) (PreH8 : (stride = (n_pre + 1))) (PreH9 : ((0 : Int) <= n_pre)) (PreH10 : (n_pre <= 1000)) (PreH11 : ((Zlength (xs)) = n_pre)) (PreH12 : ((Zlength (ys)) = n_pre)) (PreH13 : ((0 : Int) <= i)) (PreH14 : (i <= (n_pre + 1))) (PreH15 : ((0 : Int) <= (stride * i))) (PreH16 : ((stride * i) <= ((n_pre + 1) * (n_pre + 1)))) (PreH17 : (LCSNColumnProgress mixed_table table_l n_pre i)) (PreH18 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH19 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (((n_pre + 1) * i) < ((n_pre + 1) * (n_pre + 1)))

noncomputable def longest_common_sequence_entail_wit_3 : Prop :=
  (
forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (i : Int) (stride : Int) (PreH1 : ((0 : Int) <= (stride * i))) (PreH2 : ((stride * i) < ((n_pre + 1) * (n_pre + 1)))) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (i <= n_pre)) (PreH6 : (stride = (n_pre + 1))) (PreH7 : ((0 : Int) <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : ((Zlength (xs)) = n_pre)) (PreH10 : ((Zlength (ys)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= (n_pre + 1))) (PreH13 : ((0 : Int) <= (stride * i))) (PreH14 : ((stride * i) <= ((n_pre + 1) * (n_pre + 1)))) (PreH15 : (LCSNColumnProgress mixed_table_2 table_l_2 n_pre i)) (PreH16 : ((Zlength (mixed_table_2)) = ((n_pre + 1) * (n_pre + 1)))) (PreH17 : ((Zlength (table_l_2)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) (replace_Znth ((stride * i)) ((Some ((0 : Int)))) (mixed_table_2)))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  EX mixed_table : (List (Option Int)), EX table_l : (List Int),
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= (stride * (i + 1))) ” &&
  “ ((stride * (i + 1)) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNColumnProgress mixed_table table_l n_pre (i + 1)) ” &&
  “ ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1))) ”
  &&  (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
) \/
(
forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (i : Int) (stride : Int) (PreH1 : ((0 : Int) <= (stride * i))) (PreH2 : ((stride * i) < ((n_pre + 1) * (n_pre + 1)))) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (i <= n_pre)) (PreH6 : (stride = (n_pre + 1))) (PreH7 : ((0 : Int) <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : ((Zlength (xs)) = n_pre)) (PreH10 : ((Zlength (ys)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= (n_pre + 1))) (PreH13 : ((0 : Int) <= (stride * i))) (PreH14 : ((stride * i) <= ((n_pre + 1) * (n_pre + 1)))) (PreH15 : (LCSNColumnProgress mixed_table_2 table_l_2 n_pre i)) (PreH16 : ((Zlength (mixed_table_2)) = ((n_pre + 1) * (n_pre + 1)))) (PreH17 : ((Zlength (table_l_2)) = ((n_pre + 1) * (n_pre + 1)))) ,
  TT && emp 
|--
  EX table_l : (List Int),
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= ((Zlength (xs)) + 1)) ” &&
  “ ((0 : Int) <= (((Zlength (xs)) + 1) * (i + 1))) ” &&
  “ ((((Zlength (xs)) + 1) * (i + 1)) <= (((Zlength (xs)) + 1) * ((Zlength (xs)) + 1))) ” &&
  “ (LCSNColumnProgress (replace_Znth ((((Zlength (xs)) + 1) * i)) ((Some ((0 : Int)))) (mixed_table_2)) table_l (Zlength (xs)) (i + 1)) ” &&
  “ ((Zlength ((replace_Znth ((((Zlength (xs)) + 1) * i)) ((Some ((0 : Int)))) (mixed_table_2)))) = (((Zlength (xs)) + 1) * ((Zlength (xs)) + 1))) ” &&
  “ ((Zlength (table_l)) = (((Zlength (xs)) + 1) * ((Zlength (xs)) + 1))) ”
  &&  emp
)

noncomputable def longest_common_sequence_entail_wit_4 : Prop :=
  (
forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (i : Int) (stride : Int) (PreH1 : (i > n_pre)) (PreH2 : (stride = (n_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= (n_pre + 1))) (PreH9 : ((0 : Int) <= (stride * i))) (PreH10 : ((stride * i) <= ((n_pre + 1) * (n_pre + 1)))) (PreH11 : (LCSNColumnProgress mixed_table_2 table_l_2 n_pre i)) (PreH12 : ((Zlength (mixed_table_2)) = ((n_pre + 1) * (n_pre + 1)))) (PreH13 : ((Zlength (table_l_2)) = ((n_pre + 1) * (n_pre + 1)))) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table_2)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  EX mixed_table : (List (Option Int)), EX table_l : (List Int),
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= (n_pre + 1)) ” &&
  “ (LCSNBoundaryProgress mixed_table table_l n_pre 1) ” &&
  “ ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1))) ”
  &&  (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "i" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
) \/
(
forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (i : Int) (stride : Int) (PreH1 : (i > n_pre)) (PreH2 : (stride = (n_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= (n_pre + 1))) (PreH9 : ((0 : Int) <= (stride * i))) (PreH10 : ((stride * i) <= ((n_pre + 1) * (n_pre + 1)))) (PreH11 : (LCSNColumnProgress mixed_table_2 table_l_2 n_pre i)) (PreH12 : ((Zlength (mixed_table_2)) = ((n_pre + 1) * (n_pre + 1)))) (PreH13 : ((Zlength (table_l_2)) = ((n_pre + 1) * (n_pre + 1)))) ,
  TT && emp 
|--
  EX table_l : (List Int),
  “ (1 <= 1) ” &&
  “ (1 <= ((Zlength (xs)) + 1)) ” &&
  “ (LCSNBoundaryProgress mixed_table_2 table_l (Zlength (xs)) 1) ” &&
  “ ((Zlength (table_l)) = (((Zlength (xs)) + 1) * ((Zlength (xs)) + 1))) ”
  &&  emp
)

noncomputable def longest_common_sequence_entail_wit_5 : Prop :=
  (
forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (j : Int) (stride : Int) (PreH1 : (j <= n_pre)) (PreH2 : (stride = (n_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1))) (PreH9 : (LCSNBoundaryProgress mixed_table_2 table_l_2 n_pre j)) (PreH10 : ((Zlength (mixed_table_2)) = ((n_pre + 1) * (n_pre + 1)))) (PreH11 : ((Zlength (table_l_2)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) (replace_Znth (j) ((Some ((0 : Int)))) (mixed_table_2)))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  EX mixed_table : (List (Option Int)), EX table_l : (List Int),
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= (j + 1)) ” &&
  “ ((j + 1) <= (n_pre + 1)) ” &&
  “ (LCSNBoundaryProgress mixed_table table_l n_pre (j + 1)) ” &&
  “ ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1))) ”
  &&  (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
) \/
(
forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (j : Int) (stride : Int) (PreH1 : (j <= n_pre)) (PreH2 : (stride = (n_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1))) (PreH9 : (LCSNBoundaryProgress mixed_table_2 table_l_2 n_pre j)) (PreH10 : ((Zlength (mixed_table_2)) = ((n_pre + 1) * (n_pre + 1)))) (PreH11 : ((Zlength (table_l_2)) = ((n_pre + 1) * (n_pre + 1)))) ,
  TT && emp 
|--
  EX table_l : (List Int),
  “ (1 <= (j + 1)) ” &&
  “ ((j + 1) <= ((Zlength (xs)) + 1)) ” &&
  “ (LCSNBoundaryProgress (replace_Znth (j) ((Some ((0 : Int)))) (mixed_table_2)) table_l (Zlength (xs)) (j + 1)) ” &&
  “ ((Zlength ((replace_Znth (j) ((Some ((0 : Int)))) (mixed_table_2)))) = (((Zlength (xs)) + 1) * ((Zlength (xs)) + 1))) ” &&
  “ ((Zlength (table_l)) = (((Zlength (xs)) + 1) * ((Zlength (xs)) + 1))) ”
  &&  emp
)

noncomputable def longest_common_sequence_entail_wit_6 : Prop :=
  (
forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (j : Int) (stride : Int) (PreH1 : (j > n_pre)) (PreH2 : (stride = (n_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1))) (PreH9 : (LCSNBoundaryProgress mixed_table_2 table_l_2 n_pre j)) (PreH10 : ((Zlength (mixed_table_2)) = ((n_pre + 1) * (n_pre + 1)))) (PreH11 : ((Zlength (table_l_2)) = ((n_pre + 1) * (n_pre + 1)))) ,
  ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table_2)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  EX mixed_table : (List (Option Int)), EX table_l : (List Int),
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= (stride * 1)) ” &&
  “ ((stride * 1) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNRowsProgress xs ys mixed_table table_l n_pre 1) ” &&
  “ ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1))) ”
  &&  (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "j" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
) \/
(
forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (j : Int) (stride : Int) (PreH1 : (j > n_pre)) (PreH2 : (stride = (n_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1))) (PreH9 : (LCSNBoundaryProgress mixed_table_2 table_l_2 n_pre j)) (PreH10 : ((Zlength (mixed_table_2)) = ((n_pre + 1) * (n_pre + 1)))) (PreH11 : ((Zlength (table_l_2)) = ((n_pre + 1) * (n_pre + 1)))) ,
  TT && emp 
|--
  EX table_l : (List Int),
  “ (1 <= 1) ” &&
  “ (1 <= ((Zlength (xs)) + 1)) ” &&
  “ ((0 : Int) <= (((Zlength (xs)) + 1) * 1)) ” &&
  “ ((((Zlength (xs)) + 1) * 1) <= (((Zlength (xs)) + 1) * ((Zlength (xs)) + 1))) ” &&
  “ (LCSNRowsProgress xs ys mixed_table_2 table_l (Zlength (xs)) 1) ” &&
  “ ((Zlength (table_l)) = (((Zlength (xs)) + 1) * ((Zlength (xs)) + 1))) ”
  &&  emp
)

noncomputable def longest_common_sequence_entail_wit_7 : Prop :=
  (
forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (i : Int) (stride : Int) (PreH1 : (i <= n_pre)) (PreH2 : (stride = (n_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre + 1))) (PreH9 : ((0 : Int) <= (stride * i))) (PreH10 : ((stride * i) <= ((n_pre + 1) * (n_pre + 1)))) (PreH11 : (LCSNRowsProgress xs ys mixed_table_2 table_l_2 n_pre i)) (PreH12 : ((Zlength (mixed_table_2)) = ((n_pre + 1) * (n_pre + 1)))) (PreH13 : ((Zlength (table_l_2)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table_2)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  EX mixed_table : (List (Option Int)), EX table_l : (List Int),
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= ((stride * i) + 1)) ” &&
  “ (((stride * i) + 1) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i 1) ” &&
  “ ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1))) ”
  &&  (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
) \/
(
forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (i : Int) (stride : Int) (PreH1 : (i <= n_pre)) (PreH2 : (stride = (n_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre + 1))) (PreH9 : ((0 : Int) <= (stride * i))) (PreH10 : ((stride * i) <= ((n_pre + 1) * (n_pre + 1)))) (PreH11 : (LCSNRowsProgress xs ys mixed_table_2 table_l_2 n_pre i)) (PreH12 : ((Zlength (mixed_table_2)) = ((n_pre + 1) * (n_pre + 1)))) (PreH13 : ((Zlength (table_l_2)) = ((n_pre + 1) * (n_pre + 1)))) ,
  TT && emp 
|--
  EX table_l : (List Int),
  “ (1 <= 1) ” &&
  “ (1 <= ((Zlength (xs)) + 1)) ” &&
  “ ((0 : Int) <= ((((Zlength (xs)) + 1) * i) + 1)) ” &&
  “ (((((Zlength (xs)) + 1) * i) + 1) <= (((Zlength (xs)) + 1) * ((Zlength (xs)) + 1))) ” &&
  “ (LCSNRowProgress xs ys mixed_table_2 table_l (Zlength (xs)) i 1) ” &&
  “ ((Zlength (table_l)) = (((Zlength (xs)) + 1) * ((Zlength (xs)) + 1))) ”
  &&  emp
)

noncomputable def longest_common_sequence_entail_wit_8 : Prop :=
  (
forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table : (List (Option Int))) (table_l : (List Int)) (PreH1 : (j <= n_pre)) (PreH2 : (stride = (n_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= (n_pre + 1))) (PreH11 : ((0 : Int) <= ((stride * i) + j))) (PreH12 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH13 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH14 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH15 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) < n_pre) ” &&
  “ ((0 : Int) <= (j - 1)) ” &&
  “ ((j - 1) < n_pre) ” &&
  “ ((0 : Int) <= ((stride * i) + j)) ” &&
  “ (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * (i - 1)) + (j - 1))) ” &&
  “ (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * (i - 1)) + j)) ” &&
  “ (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * i) + (j - 1))) ” &&
  “ (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (j <= n_pre) ” &&
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= ((stride * i) + j)) ” &&
  “ (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j) ” &&
  “ ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1))) ”
  &&  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
) \/
(
forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table : (List (Option Int))) (table_l : (List Int)) (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (stride <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (j >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (stride >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (j <= n_pre)) (PreH10 : (stride = (n_pre + 1))) (PreH11 : ((0 : Int) <= n_pre)) (PreH12 : (n_pre <= 1000)) (PreH13 : ((Zlength (xs)) = n_pre)) (PreH14 : ((Zlength (ys)) = n_pre)) (PreH15 : (1 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (1 <= j)) (PreH18 : (j <= (n_pre + 1))) (PreH19 : ((0 : Int) <= ((stride * i) + j))) (PreH20 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH21 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH22 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH23 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  TT && emp 
|--
  “ ((((n_pre + 1) * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((((n_pre + 1) * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((((n_pre + 1) * i) + j) < ((n_pre + 1) * (n_pre + 1))) ”
  &&  emp
)

noncomputable def longest_common_sequence_entail_wit_8_split_goal_1 : Prop :=
  forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table : (List (Option Int))) (table_l : (List Int)) (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (stride <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (j >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (stride >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (j <= n_pre)) (PreH10 : (stride = (n_pre + 1))) (PreH11 : ((0 : Int) <= n_pre)) (PreH12 : (n_pre <= 1000)) (PreH13 : ((Zlength (xs)) = n_pre)) (PreH14 : ((Zlength (ys)) = n_pre)) (PreH15 : (1 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (1 <= j)) (PreH18 : (j <= (n_pre + 1))) (PreH19 : ((0 : Int) <= ((stride * i) + j))) (PreH20 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH21 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH22 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH23 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  ((((n_pre + 1) * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))

noncomputable def longest_common_sequence_entail_wit_8_split_goal_2 : Prop :=
  forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table : (List (Option Int))) (table_l : (List Int)) (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (stride <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (j >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (stride >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (j <= n_pre)) (PreH10 : (stride = (n_pre + 1))) (PreH11 : ((0 : Int) <= n_pre)) (PreH12 : (n_pre <= 1000)) (PreH13 : ((Zlength (xs)) = n_pre)) (PreH14 : ((Zlength (ys)) = n_pre)) (PreH15 : (1 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (1 <= j)) (PreH18 : (j <= (n_pre + 1))) (PreH19 : ((0 : Int) <= ((stride * i) + j))) (PreH20 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH21 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH22 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH23 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  ((((n_pre + 1) * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))

noncomputable def longest_common_sequence_entail_wit_8_split_goal_3 : Prop :=
  forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table : (List (Option Int))) (table_l : (List Int)) (PreH1 : (j <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (stride <= INT_MAX)) (PreH4 : (n_pre <= INT_MAX)) (PreH5 : (j >= INT_MIN)) (PreH6 : (i >= INT_MIN)) (PreH7 : (stride >= INT_MIN)) (PreH8 : (n_pre >= INT_MIN)) (PreH9 : (j <= n_pre)) (PreH10 : (stride = (n_pre + 1))) (PreH11 : ((0 : Int) <= n_pre)) (PreH12 : (n_pre <= 1000)) (PreH13 : ((Zlength (xs)) = n_pre)) (PreH14 : ((Zlength (ys)) = n_pre)) (PreH15 : (1 <= i)) (PreH16 : (i <= n_pre)) (PreH17 : (1 <= j)) (PreH18 : (j <= (n_pre + 1))) (PreH19 : ((0 : Int) <= ((stride * i) + j))) (PreH20 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH21 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH22 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH23 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  ((((n_pre + 1) * i) + j) < ((n_pre + 1) * (n_pre + 1)))

noncomputable def longest_common_sequence_entail_wit_9_1 : Prop :=
  (
forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) (PreH6 : ((Zlength (mixed_table_2)) = ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((Zlength (table_l_2)) = ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table_2) (None)) = None)) (PreH9 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))))))) (PreH10 : ((0 : Int) <= (Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))))) (PreH11 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))) <= n_pre)) (PreH12 : ((Znth (i - 1) xs (0 : Int)) = (Znth (j - 1) ys (0 : Int)))) (PreH13 : ((0 : Int) <= (i - 1))) (PreH14 : ((i - 1) < n_pre)) (PreH15 : ((0 : Int) <= (j - 1))) (PreH16 : ((j - 1) < n_pre)) (PreH17 : ((0 : Int) <= ((stride * i) + j))) (PreH18 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH19 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH20 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH21 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH22 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH24 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= n_pre)) (PreH28 : (stride = (n_pre + 1))) (PreH29 : ((0 : Int) <= n_pre)) (PreH30 : (n_pre <= 1000)) (PreH31 : ((Zlength (xs)) = n_pre)) (PreH32 : ((Zlength (ys)) = n_pre)) (PreH33 : (1 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (1 <= j)) (PreH36 : (j <= (n_pre + 1))) (PreH37 : ((0 : Int) <= ((stride * i) + j))) (PreH38 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH39 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) (PreH40 : ((Zlength (mixed_table_2)) = ((n_pre + 1) * (n_pre + 1)))) (PreH41 : ((Zlength (table_l_2)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (intArray.undef_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((((n_pre + 1) * i) + j) + 1))
  ** (((( &( "table" ) ) + (((stride * i) + j) * sizeof(INT)))) # Int |-> (((Znth (((((Zlength (xs)) + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))) + 1)))
  ** (((( &( "table" ) ) + (((stride * (i - 1)) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int)))))
  ** (intArray.mixed_seg ( &( "table" ) ) (0 : Int) (((n_pre + 1) * (i - 1)) + (j - 1)) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table_2)))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * (i - 1)) + (j - 1)) + 1) (((n_pre + 1) * i) + j) (sublist (((((n_pre + 1) * (i - 1)) + (j - 1)) + 1)) ((((n_pre + 1) * i) + j)) (mixed_table_2)))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table_2)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  EX mixed_table : (List (Option Int)), EX table_l : (List Int),
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (1 <= (j + 1)) ” &&
  “ ((j + 1) <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= ((stride * i) + (j + 1))) ” &&
  “ (((stride * i) + (j + 1)) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i (j + 1)) ” &&
  “ ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1))) ”
  &&  (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
) \/
(
forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (PreH1 : ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))) <= INT_MAX)) (PreH2 : (((Znth (((((Zlength (xs)) + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))) + 1) <= INT_MAX)) (PreH3 : ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))) >= INT_MIN)) (PreH4 : (((Znth (((((Zlength (xs)) + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))) + 1) >= INT_MIN)) (PreH5 : (1 <= i)) (PreH6 : (i <= n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= n_pre)) (PreH9 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) (PreH10 : ((Zlength (mixed_table_2)) = ((n_pre + 1) * (n_pre + 1)))) (PreH11 : ((Zlength (table_l_2)) = ((n_pre + 1) * (n_pre + 1)))) (PreH12 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table_2) (None)) = None)) (PreH13 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))))))) (PreH14 : ((0 : Int) <= (Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))))) (PreH15 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))) <= n_pre)) (PreH16 : ((Znth (i - 1) xs (0 : Int)) = (Znth (j - 1) ys (0 : Int)))) (PreH17 : ((0 : Int) <= (i - 1))) (PreH18 : ((i - 1) < n_pre)) (PreH19 : ((0 : Int) <= (j - 1))) (PreH20 : ((j - 1) < n_pre)) (PreH21 : ((0 : Int) <= ((stride * i) + j))) (PreH22 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH24 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH25 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH26 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH27 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH28 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH29 : (n_pre <= INT_MAX)) (PreH30 : (n_pre >= INT_MIN)) (PreH31 : (j <= n_pre)) (PreH32 : (stride = (n_pre + 1))) (PreH33 : ((0 : Int) <= n_pre)) (PreH34 : (n_pre <= 1000)) (PreH35 : ((Zlength (xs)) = n_pre)) (PreH36 : ((Zlength (ys)) = n_pre)) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1))) (PreH41 : ((0 : Int) <= ((stride * i) + j))) (PreH42 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH43 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) (PreH44 : ((Zlength (mixed_table_2)) = ((n_pre + 1) * (n_pre + 1)))) (PreH45 : ((Zlength (table_l_2)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (((( &( "table" ) ) + (((stride * i) + j) * sizeof(INT)))) # Int |-> (((Znth (((((Zlength (xs)) + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int))) + 1)))
  ** (((( &( "table" ) ) + (((stride * (i - 1)) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + (j - 1))) (table_l_2) ((0 : Int)))))
  ** (intArray.mixed_seg ( &( "table" ) ) (0 : Int) (((n_pre + 1) * (i - 1)) + (j - 1)) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table_2)))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * (i - 1)) + (j - 1)) + 1) (((n_pre + 1) * i) + j) (sublist (((((n_pre + 1) * (i - 1)) + (j - 1)) + 1)) ((((n_pre + 1) * i) + j)) (mixed_table_2)))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table_2)))
|--
  EX mixed_table : (List (Option Int)), EX table_l : (List Int),
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (1 <= (j + 1)) ” &&
  “ ((j + 1) <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= ((stride * i) + (j + 1))) ” &&
  “ (((stride * i) + (j + 1)) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i (j + 1)) ” &&
  “ ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1))) ”
  &&  (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
)

noncomputable def longest_common_sequence_entail_wit_9_2 : Prop :=
  (
forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (PreH1 : ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int))) >= (Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_2) ((0 : Int))))) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) (PreH7 : ((Zlength (mixed_table_2)) = ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((Zlength (table_l_2)) = ((n_pre + 1) * (n_pre + 1)))) (PreH9 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table_2) (None)) = None)) (PreH10 : ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int))))))) (PreH11 : ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l_2) ((0 : Int))))))) (PreH12 : ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int)))) (PreH13 : ((0 : Int) <= (i - 1))) (PreH14 : ((i - 1) < n_pre)) (PreH15 : ((0 : Int) <= (j - 1))) (PreH16 : ((j - 1) < n_pre)) (PreH17 : ((0 : Int) <= ((stride * i) + j))) (PreH18 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH19 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH20 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH21 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH22 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH24 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= n_pre)) (PreH28 : (stride = (n_pre + 1))) (PreH29 : ((0 : Int) <= n_pre)) (PreH30 : (n_pre <= 1000)) (PreH31 : ((Zlength (xs)) = n_pre)) (PreH32 : ((Zlength (ys)) = n_pre)) (PreH33 : (1 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (1 <= j)) (PreH36 : (j <= (n_pre + 1))) (PreH37 : ((0 : Int) <= ((stride * i) + j))) (PreH38 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH39 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) (PreH40 : ((Zlength (mixed_table_2)) = ((n_pre + 1) * (n_pre + 1)))) (PreH41 : ((Zlength (table_l_2)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (intArray.undef_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((((n_pre + 1) * i) + j) + 1))
  ** (((( &( "table" ) ) + (((stride * i) + j) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int)))))
  ** (((( &( "table" ) ) + (((stride * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_2) ((0 : Int)))))
  ** (((( &( "table" ) ) + (((stride * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int)))))
  ** (intArray.mixed_seg ( &( "table" ) ) (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2)))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2)))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table_2)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "above" ) )) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int)))))
  ** ((( &( "left" ) )) # Int |-> ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_2) ((0 : Int)))))
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  EX mixed_table : (List (Option Int)), EX table_l : (List Int),
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (1 <= (j + 1)) ” &&
  “ ((j + 1) <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= ((stride * i) + (j + 1))) ” &&
  “ (((stride * i) + (j + 1)) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i (j + 1)) ” &&
  “ ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1))) ”
  &&  (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
) \/
(
forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (PreH1 : ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_2) ((0 : Int))) <= INT_MAX)) (PreH2 : ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int))) <= INT_MAX)) (PreH3 : ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_2) ((0 : Int))) >= INT_MIN)) (PreH4 : ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int))) >= INT_MIN)) (PreH5 : ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int))) >= (Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_2) ((0 : Int))))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) (PreH11 : ((Zlength (mixed_table_2)) = ((n_pre + 1) * (n_pre + 1)))) (PreH12 : ((Zlength (table_l_2)) = ((n_pre + 1) * (n_pre + 1)))) (PreH13 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table_2) (None)) = None)) (PreH14 : ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int))))))) (PreH15 : ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l_2) ((0 : Int))))))) (PreH16 : ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int)))) (PreH17 : ((0 : Int) <= (i - 1))) (PreH18 : ((i - 1) < n_pre)) (PreH19 : ((0 : Int) <= (j - 1))) (PreH20 : ((j - 1) < n_pre)) (PreH21 : ((0 : Int) <= ((stride * i) + j))) (PreH22 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH24 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH25 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH26 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH27 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH28 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH29 : (n_pre <= INT_MAX)) (PreH30 : (n_pre >= INT_MIN)) (PreH31 : (j <= n_pre)) (PreH32 : (stride = (n_pre + 1))) (PreH33 : ((0 : Int) <= n_pre)) (PreH34 : (n_pre <= 1000)) (PreH35 : ((Zlength (xs)) = n_pre)) (PreH36 : ((Zlength (ys)) = n_pre)) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1))) (PreH41 : ((0 : Int) <= ((stride * i) + j))) (PreH42 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH43 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) (PreH44 : ((Zlength (mixed_table_2)) = ((n_pre + 1) * (n_pre + 1)))) (PreH45 : ((Zlength (table_l_2)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (((( &( "table" ) ) + (((stride * i) + j) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int)))))
  ** (((( &( "table" ) ) + (((stride * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_2) ((0 : Int)))))
  ** (((( &( "table" ) ) + (((stride * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int)))))
  ** (intArray.mixed_seg ( &( "table" ) ) (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2)))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2)))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table_2)))
|--
  EX mixed_table : (List (Option Int)), EX table_l : (List Int),
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (1 <= (j + 1)) ” &&
  “ ((j + 1) <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= ((stride * i) + (j + 1))) ” &&
  “ (((stride * i) + (j + 1)) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i (j + 1)) ” &&
  “ ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1))) ”
  &&  (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
)

noncomputable def longest_common_sequence_entail_wit_9_3 : Prop :=
  (
forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (PreH1 : ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int))) < (Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_2) ((0 : Int))))) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) (PreH7 : ((Zlength (mixed_table_2)) = ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((Zlength (table_l_2)) = ((n_pre + 1) * (n_pre + 1)))) (PreH9 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table_2) (None)) = None)) (PreH10 : ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int))))))) (PreH11 : ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l_2) ((0 : Int))))))) (PreH12 : ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int)))) (PreH13 : ((0 : Int) <= (i - 1))) (PreH14 : ((i - 1) < n_pre)) (PreH15 : ((0 : Int) <= (j - 1))) (PreH16 : ((j - 1) < n_pre)) (PreH17 : ((0 : Int) <= ((stride * i) + j))) (PreH18 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH19 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH20 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH21 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH22 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH24 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= n_pre)) (PreH28 : (stride = (n_pre + 1))) (PreH29 : ((0 : Int) <= n_pre)) (PreH30 : (n_pre <= 1000)) (PreH31 : ((Zlength (xs)) = n_pre)) (PreH32 : ((Zlength (ys)) = n_pre)) (PreH33 : (1 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (1 <= j)) (PreH36 : (j <= (n_pre + 1))) (PreH37 : ((0 : Int) <= ((stride * i) + j))) (PreH38 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH39 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) (PreH40 : ((Zlength (mixed_table_2)) = ((n_pre + 1) * (n_pre + 1)))) (PreH41 : ((Zlength (table_l_2)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (intArray.undef_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((((n_pre + 1) * i) + j) + 1))
  ** (((( &( "table" ) ) + (((stride * i) + j) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_2) ((0 : Int)))))
  ** (((( &( "table" ) ) + (((stride * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_2) ((0 : Int)))))
  ** (((( &( "table" ) ) + (((stride * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int)))))
  ** (intArray.mixed_seg ( &( "table" ) ) (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2)))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2)))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table_2)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "above" ) )) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int)))))
  ** ((( &( "left" ) )) # Int |-> ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_2) ((0 : Int)))))
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  EX mixed_table : (List (Option Int)), EX table_l : (List Int),
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (1 <= (j + 1)) ” &&
  “ ((j + 1) <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= ((stride * i) + (j + 1))) ” &&
  “ (((stride * i) + (j + 1)) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i (j + 1)) ” &&
  “ ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1))) ”
  &&  (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
) \/
(
forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (PreH1 : ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int))) <= INT_MAX)) (PreH2 : ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_2) ((0 : Int))) <= INT_MAX)) (PreH3 : ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int))) >= INT_MIN)) (PreH4 : ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_2) ((0 : Int))) >= INT_MIN)) (PreH5 : ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int))) < (Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_2) ((0 : Int))))) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) (PreH11 : ((Zlength (mixed_table_2)) = ((n_pre + 1) * (n_pre + 1)))) (PreH12 : ((Zlength (table_l_2)) = ((n_pre + 1) * (n_pre + 1)))) (PreH13 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table_2) (None)) = None)) (PreH14 : ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int))))))) (PreH15 : ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l_2) ((0 : Int))))))) (PreH16 : ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int)))) (PreH17 : ((0 : Int) <= (i - 1))) (PreH18 : ((i - 1) < n_pre)) (PreH19 : ((0 : Int) <= (j - 1))) (PreH20 : ((j - 1) < n_pre)) (PreH21 : ((0 : Int) <= ((stride * i) + j))) (PreH22 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH24 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH25 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH26 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH27 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH28 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH29 : (n_pre <= INT_MAX)) (PreH30 : (n_pre >= INT_MIN)) (PreH31 : (j <= n_pre)) (PreH32 : (stride = (n_pre + 1))) (PreH33 : ((0 : Int) <= n_pre)) (PreH34 : (n_pre <= 1000)) (PreH35 : ((Zlength (xs)) = n_pre)) (PreH36 : ((Zlength (ys)) = n_pre)) (PreH37 : (1 <= i)) (PreH38 : (i <= n_pre)) (PreH39 : (1 <= j)) (PreH40 : (j <= (n_pre + 1))) (PreH41 : ((0 : Int) <= ((stride * i) + j))) (PreH42 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH43 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) (PreH44 : ((Zlength (mixed_table_2)) = ((n_pre + 1) * (n_pre + 1)))) (PreH45 : ((Zlength (table_l_2)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (((( &( "table" ) ) + (((stride * i) + j) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_2) ((0 : Int)))))
  ** (((( &( "table" ) ) + (((stride * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l_2) ((0 : Int)))))
  ** (((( &( "table" ) ) + (((stride * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l_2) ((0 : Int)))))
  ** (intArray.mixed_seg ( &( "table" ) ) (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table_2)))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table_2)))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table_2)))
|--
  EX mixed_table : (List (Option Int)), EX table_l : (List Int),
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (1 <= (j + 1)) ” &&
  “ ((j + 1) <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= ((stride * i) + (j + 1))) ” &&
  “ (((stride * i) + (j + 1)) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i (j + 1)) ” &&
  “ ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1))) ”
  &&  (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
)

noncomputable def longest_common_sequence_entail_wit_10 : Prop :=
  (
forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (stride : Int) (i : Int) (j : Int) (PreH1 : (stride = (n_pre + 1))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (xs)) = n_pre)) (PreH5 : ((Zlength (ys)) = n_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (1 <= (j + 1))) (PreH11 : ((j + 1) <= (n_pre + 1))) (PreH12 : ((0 : Int) <= ((stride * i) + (j + 1)))) (PreH13 : (((stride * i) + (j + 1)) <= ((n_pre + 1) * (n_pre + 1)))) (PreH14 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i (j + 1))) (PreH15 : ((Zlength (mixed_table_2)) = ((n_pre + 1) * (n_pre + 1)))) (PreH16 : ((Zlength (table_l_2)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table_2)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  EX mixed_table : (List (Option Int)), EX table_l : (List Int),
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= (j + 1)) ” &&
  “ ((j + 1) <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= ((stride * i) + (j + 1))) ” &&
  “ (((stride * i) + (j + 1)) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i (j + 1)) ” &&
  “ ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1))) ”
  &&  (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
) \/
(
forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (stride : Int) (i : Int) (j : Int) (PreH1 : (stride = (n_pre + 1))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (xs)) = n_pre)) (PreH5 : ((Zlength (ys)) = n_pre)) (PreH6 : (1 <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (1 <= j)) (PreH9 : (j <= n_pre)) (PreH10 : (1 <= (j + 1))) (PreH11 : ((j + 1) <= (n_pre + 1))) (PreH12 : ((0 : Int) <= ((stride * i) + (j + 1)))) (PreH13 : (((stride * i) + (j + 1)) <= ((n_pre + 1) * (n_pre + 1)))) (PreH14 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i (j + 1))) (PreH15 : ((Zlength (mixed_table_2)) = ((n_pre + 1) * (n_pre + 1)))) (PreH16 : ((Zlength (table_l_2)) = ((n_pre + 1) * (n_pre + 1)))) ,
  TT && emp 
|--
  EX table_l : (List Int),
  “ (LCSNRowProgress xs ys mixed_table_2 table_l (Zlength (xs)) i (j + 1)) ” &&
  “ ((Zlength (table_l)) = (((Zlength (xs)) + 1) * ((Zlength (xs)) + 1))) ”
  &&  emp
)

noncomputable def longest_common_sequence_entail_wit_11 : Prop :=
  (
forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (j : Int) (i : Int) (stride : Int) (PreH1 : (j > n_pre)) (PreH2 : (stride = (n_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= (n_pre + 1))) (PreH11 : ((0 : Int) <= ((stride * i) + j))) (PreH12 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH13 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) (PreH14 : ((Zlength (mixed_table_2)) = ((n_pre + 1) * (n_pre + 1)))) (PreH15 : ((Zlength (table_l_2)) = ((n_pre + 1) * (n_pre + 1)))) ,
  ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table_2)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  EX mixed_table : (List (Option Int)), EX table_l : (List Int),
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= (stride * (i + 1))) ” &&
  “ ((stride * (i + 1)) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNRowsProgress xs ys mixed_table table_l n_pre (i + 1)) ” &&
  “ ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1))) ”
  &&  (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "j" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
) \/
(
forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (j : Int) (i : Int) (stride : Int) (PreH1 : (j > n_pre)) (PreH2 : (stride = (n_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (1 <= j)) (PreH10 : (j <= (n_pre + 1))) (PreH11 : ((0 : Int) <= ((stride * i) + j))) (PreH12 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH13 : (LCSNRowProgress xs ys mixed_table_2 table_l_2 n_pre i j)) (PreH14 : ((Zlength (mixed_table_2)) = ((n_pre + 1) * (n_pre + 1)))) (PreH15 : ((Zlength (table_l_2)) = ((n_pre + 1) * (n_pre + 1)))) ,
  TT && emp 
|--
  EX table_l : (List Int),
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= ((Zlength (xs)) + 1)) ” &&
  “ ((0 : Int) <= (((Zlength (xs)) + 1) * (i + 1))) ” &&
  “ ((((Zlength (xs)) + 1) * (i + 1)) <= (((Zlength (xs)) + 1) * ((Zlength (xs)) + 1))) ” &&
  “ (LCSNRowsProgress xs ys mixed_table_2 table_l (Zlength (xs)) (i + 1)) ” &&
  “ ((Zlength (table_l)) = (((Zlength (xs)) + 1) * ((Zlength (xs)) + 1))) ”
  &&  emp
)

noncomputable def longest_common_sequence_entail_wit_12 : Prop :=
  (
forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (i : Int) (stride : Int) (PreH1 : (i > n_pre)) (PreH2 : (stride = (n_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre + 1))) (PreH9 : ((0 : Int) <= (stride * i))) (PreH10 : ((stride * i) <= ((n_pre + 1) * (n_pre + 1)))) (PreH11 : (LCSNRowsProgress xs ys mixed_table_2 table_l_2 n_pre i)) (PreH12 : ((Zlength (mixed_table_2)) = ((n_pre + 1) * (n_pre + 1)))) (PreH13 : ((Zlength (table_l_2)) = ((n_pre + 1) * (n_pre + 1)))) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table_2)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  EX mixed_table : (List (Option Int)), EX table_l : (List Int),
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (LCSNRowsProgress xs ys mixed_table table_l n_pre (n_pre + 1)) ” &&
  “ ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNTableResult xs ys n_pre table_l) ” &&
  “ ((0 : Int) <= ((stride * n_pre) + n_pre)) ” &&
  “ (((stride * n_pre) + n_pre) < ((n_pre + 1) * (n_pre + 1))) ”
  &&  (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) table_l)
  ** ((( &( "i" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
) \/
(
forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table_2 : (List (Option Int))) (table_l_2 : (List Int)) (i : Int) (stride : Int) (PreH1 : (i > n_pre)) (PreH2 : (stride = (n_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= i)) (PreH8 : (i <= (n_pre + 1))) (PreH9 : ((0 : Int) <= (stride * i))) (PreH10 : ((stride * i) <= ((n_pre + 1) * (n_pre + 1)))) (PreH11 : (LCSNRowsProgress xs ys mixed_table_2 table_l_2 n_pre i)) (PreH12 : ((Zlength (mixed_table_2)) = ((n_pre + 1) * (n_pre + 1)))) (PreH13 : ((Zlength (table_l_2)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table_2)
|--
  EX mixed_table : (List (Option Int)), EX table_l : (List Int),
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (LCSNRowsProgress xs ys mixed_table table_l n_pre (n_pre + 1)) ” &&
  “ ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNTableResult xs ys n_pre table_l) ” &&
  “ ((0 : Int) <= ((stride * n_pre) + n_pre)) ” &&
  “ (((stride * n_pre) + n_pre) < ((n_pre + 1) * (n_pre + 1))) ”
  &&  (intArray.full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) table_l)
)

noncomputable def longest_common_sequence_entail_wit_13 : Prop :=
  (
forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (stride : Int) (PreH1 : (stride = (n_pre + 1))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (xs)) = n_pre)) (PreH5 : ((Zlength (ys)) = n_pre)) (PreH6 : (LCSNRowsProgress xs ys mixed_table table_l n_pre (n_pre + 1))) (PreH7 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) (PreH9 : (LCSNTableResult xs ys n_pre table_l)) (PreH10 : ((0 : Int) <= ((stride * n_pre) + n_pre))) (PreH11 : (((stride * n_pre) + n_pre) < ((n_pre + 1) * (n_pre + 1)))) ,
  (intArray.full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) table_l)
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ (LCSNLength xs ys (Znth ((stride * n_pre) + n_pre) table_l (0 : Int))) ”
  &&  (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.undef_full ( &( "table" ) ) 1002001)
  ** ((( &( "stride" ) )) # Int |->_)
) \/
(
forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (stride : Int) (PreH1 : (stride = (n_pre + 1))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (xs)) = n_pre)) (PreH5 : ((Zlength (ys)) = n_pre)) (PreH6 : (LCSNRowsProgress xs ys mixed_table table_l n_pre (n_pre + 1))) (PreH7 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) (PreH9 : (LCSNTableResult xs ys n_pre table_l)) (PreH10 : ((0 : Int) <= ((stride * n_pre) + n_pre))) (PreH11 : (((stride * n_pre) + n_pre) < ((n_pre + 1) * (n_pre + 1)))) ,
  (intArray.full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) table_l)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ (LCSNLength xs ys (Znth (((n_pre + 1) * n_pre) + n_pre) table_l (0 : Int))) ”
  &&  (intArray.undef_full ( &( "table" ) ) 1002001)
)

noncomputable def longest_common_sequence_entail_wit_13_split_goal_1 : Prop :=
  forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (stride : Int) (PreH1 : (stride = (n_pre + 1))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (xs)) = n_pre)) (PreH5 : ((Zlength (ys)) = n_pre)) (PreH6 : (LCSNRowsProgress xs ys mixed_table table_l n_pre (n_pre + 1))) (PreH7 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) (PreH9 : (LCSNTableResult xs ys n_pre table_l)) (PreH10 : ((0 : Int) <= ((stride * n_pre) + n_pre))) (PreH11 : (((stride * n_pre) + n_pre) < ((n_pre + 1) * (n_pre + 1)))) ,
  (intArray.full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) table_l)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ (LCSNLength xs ys (Znth (((n_pre + 1) * n_pre) + n_pre) table_l (0 : Int))) ”

noncomputable def longest_common_sequence_entail_wit_13_split_goal_spatial : Prop :=
  forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (stride : Int) (PreH1 : (stride = (n_pre + 1))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (xs)) = n_pre)) (PreH5 : ((Zlength (ys)) = n_pre)) (PreH6 : (LCSNRowsProgress xs ys mixed_table table_l n_pre (n_pre + 1))) (PreH7 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) (PreH9 : (LCSNTableResult xs ys n_pre table_l)) (PreH10 : ((0 : Int) <= ((stride * n_pre) + n_pre))) (PreH11 : (((stride * n_pre) + n_pre) < ((n_pre + 1) * (n_pre + 1)))) ,
  (intArray.full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) table_l)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  (intArray.undef_full ( &( "table" ) ) 1002001)

noncomputable def longest_common_sequence_return_wit_1 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (result : Int) (PreH1 : (LCSNLength xs ys result)) ,
  (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
|--
  “ (LCSNLength xs ys result) ”
  &&  (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)

noncomputable def longest_common_sequence_partial_solve_wit_1 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (i : Int) (stride : Int) (PreH1 : ((0 : Int) <= (stride * i))) (PreH2 : ((stride * i) < ((n_pre + 1) * (n_pre + 1)))) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (n_pre >= INT_MIN)) (PreH5 : (i <= n_pre)) (PreH6 : (stride = (n_pre + 1))) (PreH7 : ((0 : Int) <= n_pre)) (PreH8 : (n_pre <= 1000)) (PreH9 : ((Zlength (xs)) = n_pre)) (PreH10 : ((Zlength (ys)) = n_pre)) (PreH11 : ((0 : Int) <= i)) (PreH12 : (i <= (n_pre + 1))) (PreH13 : ((0 : Int) <= (stride * i))) (PreH14 : ((stride * i) <= ((n_pre + 1) * (n_pre + 1)))) (PreH15 : (LCSNColumnProgress mixed_table table_l n_pre i)) (PreH16 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH17 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ ((0 : Int) <= (stride * i)) ” &&
  “ ((stride * i) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (i <= n_pre) ” &&
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= (stride * i)) ” &&
  “ ((stride * i) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNColumnProgress mixed_table table_l n_pre i) ” &&
  “ ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1))) ”
  &&  (((( &( "table" ) ) + ((stride * i) * sizeof(INT)))) # Int |->_)
  ** (intArray.mixed_missing_i ( &( "table" ) ) (stride * i) (0 : Int) ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)

noncomputable def longest_common_sequence_partial_solve_wit_2 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (j : Int) (stride : Int) (PreH1 : (j <= n_pre)) (PreH2 : (stride = (n_pre + 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 1000)) (PreH5 : ((Zlength (xs)) = n_pre)) (PreH6 : ((Zlength (ys)) = n_pre)) (PreH7 : (1 <= j)) (PreH8 : (j <= (n_pre + 1))) (PreH9 : (LCSNBoundaryProgress mixed_table table_l n_pre j)) (PreH10 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH11 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ (j <= n_pre) ” &&
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= (n_pre + 1)) ” &&
  “ (LCSNBoundaryProgress mixed_table table_l n_pre j) ” &&
  “ ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1))) ”
  &&  (((( &( "table" ) ) + (j * sizeof(INT)))) # Int |->_)
  ** (intArray.mixed_missing_i ( &( "table" ) ) j (0 : Int) ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)

noncomputable def longest_common_sequence_partial_solve_wit_3 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table : (List (Option Int))) (table_l : (List Int)) (PreH1 : ((0 : Int) <= (i - 1))) (PreH2 : ((i - 1) < n_pre)) (PreH3 : ((0 : Int) <= (j - 1))) (PreH4 : ((j - 1) < n_pre)) (PreH5 : ((0 : Int) <= ((stride * i) + j))) (PreH6 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH8 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH9 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH10 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH11 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH12 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= n_pre)) (PreH16 : (stride = (n_pre + 1))) (PreH17 : ((0 : Int) <= n_pre)) (PreH18 : (n_pre <= 1000)) (PreH19 : ((Zlength (xs)) = n_pre)) (PreH20 : ((Zlength (ys)) = n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (1 <= j)) (PreH24 : (j <= (n_pre + 1))) (PreH25 : ((0 : Int) <= ((stride * i) + j))) (PreH26 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH27 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH28 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH29 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) < n_pre) ” &&
  “ ((0 : Int) <= (j - 1)) ” &&
  “ ((j - 1) < n_pre) ” &&
  “ ((0 : Int) <= ((stride * i) + j)) ” &&
  “ (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * (i - 1)) + (j - 1))) ” &&
  “ (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * (i - 1)) + j)) ” &&
  “ (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * i) + (j - 1))) ” &&
  “ (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (j <= n_pre) ” &&
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= ((stride * i) + j)) ” &&
  “ (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j) ” &&
  “ ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1))) ”
  &&  (((x_pre + ((i - 1) * sizeof(INT)))) # Int |-> ((Znth (i - 1) xs (0 : Int))))
  ** (intArray.missing_i x_pre (i - 1) (0 : Int) n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)

noncomputable def longest_common_sequence_partial_solve_wit_4 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table : (List (Option Int))) (table_l : (List Int)) (PreH1 : ((0 : Int) <= (i - 1))) (PreH2 : ((i - 1) < n_pre)) (PreH3 : ((0 : Int) <= (j - 1))) (PreH4 : ((j - 1) < n_pre)) (PreH5 : ((0 : Int) <= ((stride * i) + j))) (PreH6 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH8 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH9 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH10 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH11 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH12 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH13 : (n_pre <= INT_MAX)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : (j <= n_pre)) (PreH16 : (stride = (n_pre + 1))) (PreH17 : ((0 : Int) <= n_pre)) (PreH18 : (n_pre <= 1000)) (PreH19 : ((Zlength (xs)) = n_pre)) (PreH20 : ((Zlength (ys)) = n_pre)) (PreH21 : (1 <= i)) (PreH22 : (i <= n_pre)) (PreH23 : (1 <= j)) (PreH24 : (j <= (n_pre + 1))) (PreH25 : ((0 : Int) <= ((stride * i) + j))) (PreH26 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH27 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH28 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH29 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) < n_pre) ” &&
  “ ((0 : Int) <= (j - 1)) ” &&
  “ ((j - 1) < n_pre) ” &&
  “ ((0 : Int) <= ((stride * i) + j)) ” &&
  “ (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * (i - 1)) + (j - 1))) ” &&
  “ (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * (i - 1)) + j)) ” &&
  “ (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * i) + (j - 1))) ” &&
  “ (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (j <= n_pre) ” &&
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= ((stride * i) + j)) ” &&
  “ (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j) ” &&
  “ ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1))) ”
  &&  (((y_pre + ((j - 1) * sizeof(INT)))) # Int |-> ((Znth (j - 1) ys (0 : Int))))
  ** (intArray.missing_i y_pre (j - 1) (0 : Int) n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)

noncomputable def longest_common_sequence_partial_solve_wit_5_pure : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table : (List (Option Int))) (table_l : (List Int)) (PreH1 : ((Znth (i - 1) xs (0 : Int)) = (Znth (j - 1) ys (0 : Int)))) (PreH2 : ((0 : Int) <= (i - 1))) (PreH3 : ((i - 1) < n_pre)) (PreH4 : ((0 : Int) <= (j - 1))) (PreH5 : ((j - 1) < n_pre)) (PreH6 : ((0 : Int) <= ((stride * i) + j))) (PreH7 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH9 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH10 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH11 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH12 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH13 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (j <= n_pre)) (PreH17 : (stride = (n_pre + 1))) (PreH18 : ((0 : Int) <= n_pre)) (PreH19 : (n_pre <= 1000)) (PreH20 : ((Zlength (xs)) = n_pre)) (PreH21 : ((Zlength (ys)) = n_pre)) (PreH22 : (1 <= i)) (PreH23 : (i <= n_pre)) (PreH24 : (1 <= j)) (PreH25 : (j <= (n_pre + 1))) (PreH26 : ((0 : Int) <= ((stride * i) + j))) (PreH27 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH28 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH29 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH30 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j) ” &&
  “ ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1))) ”

noncomputable def longest_common_sequence_partial_solve_wit_5_aux : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table : (List (Option Int))) (table_l : (List Int)) (PreH1 : ((Znth (i - 1) xs (0 : Int)) = (Znth (j - 1) ys (0 : Int)))) (PreH2 : ((0 : Int) <= (i - 1))) (PreH3 : ((i - 1) < n_pre)) (PreH4 : ((0 : Int) <= (j - 1))) (PreH5 : ((j - 1) < n_pre)) (PreH6 : ((0 : Int) <= ((stride * i) + j))) (PreH7 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH9 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH10 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH11 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH12 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH13 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (j <= n_pre)) (PreH17 : (stride = (n_pre + 1))) (PreH18 : ((0 : Int) <= n_pre)) (PreH19 : (n_pre <= 1000)) (PreH20 : ((Zlength (xs)) = n_pre)) (PreH21 : ((Zlength (ys)) = n_pre)) (PreH22 : (1 <= i)) (PreH23 : (i <= n_pre)) (PreH24 : (1 <= j)) (PreH25 : (j <= (n_pre + 1))) (PreH26 : ((0 : Int) <= ((stride * i) + j))) (PreH27 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH28 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH29 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH30 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j) ” &&
  “ ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Znth (i - 1) xs (0 : Int)) = (Znth (j - 1) ys (0 : Int))) ” &&
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) < n_pre) ” &&
  “ ((0 : Int) <= (j - 1)) ” &&
  “ ((j - 1) < n_pre) ” &&
  “ ((0 : Int) <= ((stride * i) + j)) ” &&
  “ (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * (i - 1)) + (j - 1))) ” &&
  “ (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * (i - 1)) + j)) ” &&
  “ (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * i) + (j - 1))) ” &&
  “ (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (j <= n_pre) ” &&
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= ((stride * i) + j)) ” &&
  “ (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j) ” &&
  “ ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1))) ”
  &&  (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)

noncomputable def longest_common_sequence_partial_solve_wit_5 : Prop := longest_common_sequence_partial_solve_wit_5_pure -> longest_common_sequence_partial_solve_wit_5_aux

noncomputable def longest_common_sequence_partial_solve_wit_6 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table : (List (Option Int))) (table_l : (List Int)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table) (None)) = None)) (PreH9 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))))))) (PreH10 : ((0 : Int) <= (Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))))) (PreH11 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))) <= n_pre)) (PreH12 : ((Znth (i - 1) xs (0 : Int)) = (Znth (j - 1) ys (0 : Int)))) (PreH13 : ((0 : Int) <= (i - 1))) (PreH14 : ((i - 1) < n_pre)) (PreH15 : ((0 : Int) <= (j - 1))) (PreH16 : ((j - 1) < n_pre)) (PreH17 : ((0 : Int) <= ((stride * i) + j))) (PreH18 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH19 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH20 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH21 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH22 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH24 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= n_pre)) (PreH28 : (stride = (n_pre + 1))) (PreH29 : ((0 : Int) <= n_pre)) (PreH30 : (n_pre <= 1000)) (PreH31 : ((Zlength (xs)) = n_pre)) (PreH32 : ((Zlength (ys)) = n_pre)) (PreH33 : (1 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (1 <= j)) (PreH36 : (j <= (n_pre + 1))) (PreH37 : ((0 : Int) <= ((stride * i) + j))) (PreH38 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH39 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH40 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH41 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (intArray.mixed_seg ( &( "table" ) ) (0 : Int) (((n_pre + 1) * (i - 1)) + (j - 1)) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table)))
  ** (((( &( "table" ) ) + ((((n_pre + 1) * (i - 1)) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int)))))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * (i - 1)) + (j - 1)) + 1) (((n_pre + 1) * i) + j) (sublist (((((n_pre + 1) * (i - 1)) + (j - 1)) + 1)) ((((n_pre + 1) * i) + j)) (mixed_table)))
  ** (intArray.undef_seg ( &( "table" ) ) (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j) ” &&
  “ ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Znth ((((n_pre + 1) * i) + j)) (mixed_table) (None)) = None) ” &&
  “ ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int)))))) ” &&
  “ ((0 : Int) <= (Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int)))) ” &&
  “ ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))) <= n_pre) ” &&
  “ ((Znth (i - 1) xs (0 : Int)) = (Znth (j - 1) ys (0 : Int))) ” &&
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) < n_pre) ” &&
  “ ((0 : Int) <= (j - 1)) ” &&
  “ ((j - 1) < n_pre) ” &&
  “ ((0 : Int) <= ((stride * i) + j)) ” &&
  “ (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * (i - 1)) + (j - 1))) ” &&
  “ (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * (i - 1)) + j)) ” &&
  “ (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * i) + (j - 1))) ” &&
  “ (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (j <= n_pre) ” &&
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= ((stride * i) + j)) ” &&
  “ (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j) ” &&
  “ ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1))) ”
  &&  (((( &( "table" ) ) + (((stride * (i - 1)) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int)))))
  ** (intArray.mixed_seg ( &( "table" ) ) (0 : Int) (((n_pre + 1) * (i - 1)) + (j - 1)) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table)))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * (i - 1)) + (j - 1)) + 1) (((n_pre + 1) * i) + j) (sublist (((((n_pre + 1) * (i - 1)) + (j - 1)) + 1)) ((((n_pre + 1) * i) + j)) (mixed_table)))
  ** (intArray.undef_seg ( &( "table" ) ) (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)

noncomputable def longest_common_sequence_partial_solve_wit_7 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table : (List (Option Int))) (table_l : (List Int)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table) (None)) = None)) (PreH9 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))))))) (PreH10 : ((0 : Int) <= (Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))))) (PreH11 : ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))) <= n_pre)) (PreH12 : ((Znth (i - 1) xs (0 : Int)) = (Znth (j - 1) ys (0 : Int)))) (PreH13 : ((0 : Int) <= (i - 1))) (PreH14 : ((i - 1) < n_pre)) (PreH15 : ((0 : Int) <= (j - 1))) (PreH16 : ((j - 1) < n_pre)) (PreH17 : ((0 : Int) <= ((stride * i) + j))) (PreH18 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH19 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH20 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH21 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH22 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH24 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= n_pre)) (PreH28 : (stride = (n_pre + 1))) (PreH29 : ((0 : Int) <= n_pre)) (PreH30 : (n_pre <= 1000)) (PreH31 : ((Zlength (xs)) = n_pre)) (PreH32 : ((Zlength (ys)) = n_pre)) (PreH33 : (1 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (1 <= j)) (PreH36 : (j <= (n_pre + 1))) (PreH37 : ((0 : Int) <= ((stride * i) + j))) (PreH38 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH39 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH40 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH41 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (((( &( "table" ) ) + (((stride * (i - 1)) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int)))))
  ** (intArray.mixed_seg ( &( "table" ) ) (0 : Int) (((n_pre + 1) * (i - 1)) + (j - 1)) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table)))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * (i - 1)) + (j - 1)) + 1) (((n_pre + 1) * i) + j) (sublist (((((n_pre + 1) * (i - 1)) + (j - 1)) + 1)) ((((n_pre + 1) * i) + j)) (mixed_table)))
  ** (intArray.undef_seg ( &( "table" ) ) (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j) ” &&
  “ ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Znth ((((n_pre + 1) * i) + j)) (mixed_table) (None)) = None) ” &&
  “ ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int)))))) ” &&
  “ ((0 : Int) <= (Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int)))) ” &&
  “ ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))) <= n_pre) ” &&
  “ ((Znth (i - 1) xs (0 : Int)) = (Znth (j - 1) ys (0 : Int))) ” &&
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) < n_pre) ” &&
  “ ((0 : Int) <= (j - 1)) ” &&
  “ ((j - 1) < n_pre) ” &&
  “ ((0 : Int) <= ((stride * i) + j)) ” &&
  “ (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * (i - 1)) + (j - 1))) ” &&
  “ (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * (i - 1)) + j)) ” &&
  “ (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * i) + (j - 1))) ” &&
  “ (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (j <= n_pre) ” &&
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= ((stride * i) + j)) ” &&
  “ (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j) ” &&
  “ ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1))) ”
  &&  (((( &( "table" ) ) + (((stride * i) + j) * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_missing_i ( &( "table" ) ) ((stride * i) + j) (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (((( &( "table" ) ) + (((stride * (i - 1)) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int)))))
  ** (intArray.mixed_seg ( &( "table" ) ) (0 : Int) (((n_pre + 1) * (i - 1)) + (j - 1)) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table)))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * (i - 1)) + (j - 1)) + 1) (((n_pre + 1) * i) + j) (sublist (((((n_pre + 1) * (i - 1)) + (j - 1)) + 1)) ((((n_pre + 1) * i) + j)) (mixed_table)))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)

noncomputable def longest_common_sequence_partial_solve_wit_8_pure : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table : (List (Option Int))) (table_l : (List Int)) (PreH1 : ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int)))) (PreH2 : ((0 : Int) <= (i - 1))) (PreH3 : ((i - 1) < n_pre)) (PreH4 : ((0 : Int) <= (j - 1))) (PreH5 : ((j - 1) < n_pre)) (PreH6 : ((0 : Int) <= ((stride * i) + j))) (PreH7 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH9 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH10 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH11 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH12 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH13 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (j <= n_pre)) (PreH17 : (stride = (n_pre + 1))) (PreH18 : ((0 : Int) <= n_pre)) (PreH19 : (n_pre <= 1000)) (PreH20 : ((Zlength (xs)) = n_pre)) (PreH21 : ((Zlength (ys)) = n_pre)) (PreH22 : (1 <= i)) (PreH23 : (i <= n_pre)) (PreH24 : (1 <= j)) (PreH25 : (j <= (n_pre + 1))) (PreH26 : ((0 : Int) <= ((stride * i) + j))) (PreH27 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH28 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH29 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH30 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "stride" ) )) # Int |-> (stride))
  ** ((( &( "x" ) )) # Ptr |-> (x_pre))
  ** ((( &( "y" ) )) # Ptr |-> (y_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** ((( &( "above" ) )) # Int |->_)
  ** ((( &( "left" ) )) # Int |->_)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j) ” &&
  “ ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1))) ”

noncomputable def longest_common_sequence_partial_solve_wit_8_aux : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table : (List (Option Int))) (table_l : (List Int)) (PreH1 : ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int)))) (PreH2 : ((0 : Int) <= (i - 1))) (PreH3 : ((i - 1) < n_pre)) (PreH4 : ((0 : Int) <= (j - 1))) (PreH5 : ((j - 1) < n_pre)) (PreH6 : ((0 : Int) <= ((stride * i) + j))) (PreH7 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH9 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH10 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH11 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH12 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH13 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH14 : (n_pre <= INT_MAX)) (PreH15 : (n_pre >= INT_MIN)) (PreH16 : (j <= n_pre)) (PreH17 : (stride = (n_pre + 1))) (PreH18 : ((0 : Int) <= n_pre)) (PreH19 : (n_pre <= 1000)) (PreH20 : ((Zlength (xs)) = n_pre)) (PreH21 : ((Zlength (ys)) = n_pre)) (PreH22 : (1 <= i)) (PreH23 : (i <= n_pre)) (PreH24 : (1 <= j)) (PreH25 : (j <= (n_pre + 1))) (PreH26 : ((0 : Int) <= ((stride * i) + j))) (PreH27 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH28 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH29 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH30 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j) ” &&
  “ ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int))) ” &&
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) < n_pre) ” &&
  “ ((0 : Int) <= (j - 1)) ” &&
  “ ((j - 1) < n_pre) ” &&
  “ ((0 : Int) <= ((stride * i) + j)) ” &&
  “ (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * (i - 1)) + (j - 1))) ” &&
  “ (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * (i - 1)) + j)) ” &&
  “ (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * i) + (j - 1))) ” &&
  “ (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (j <= n_pre) ” &&
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= ((stride * i) + j)) ” &&
  “ (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j) ” &&
  “ ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1))) ”
  &&  (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)

noncomputable def longest_common_sequence_partial_solve_wit_8 : Prop := longest_common_sequence_partial_solve_wit_8_pure -> longest_common_sequence_partial_solve_wit_8_aux

noncomputable def longest_common_sequence_partial_solve_wit_9 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table : (List (Option Int))) (table_l : (List Int)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table) (None)) = None)) (PreH9 : ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l) ((0 : Int))))))) (PreH10 : ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l) ((0 : Int))))))) (PreH11 : ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int)))) (PreH12 : ((0 : Int) <= (i - 1))) (PreH13 : ((i - 1) < n_pre)) (PreH14 : ((0 : Int) <= (j - 1))) (PreH15 : ((j - 1) < n_pre)) (PreH16 : ((0 : Int) <= ((stride * i) + j))) (PreH17 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH18 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH19 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH20 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH21 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH22 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH23 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH24 : (n_pre <= INT_MAX)) (PreH25 : (n_pre >= INT_MIN)) (PreH26 : (j <= n_pre)) (PreH27 : (stride = (n_pre + 1))) (PreH28 : ((0 : Int) <= n_pre)) (PreH29 : (n_pre <= 1000)) (PreH30 : ((Zlength (xs)) = n_pre)) (PreH31 : ((Zlength (ys)) = n_pre)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= (n_pre + 1))) (PreH36 : ((0 : Int) <= ((stride * i) + j))) (PreH37 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH38 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH39 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH40 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (intArray.mixed_seg ( &( "table" ) ) (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table)))
  ** (((( &( "table" ) ) + ((((n_pre + 1) * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l) ((0 : Int)))))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table)))
  ** (((( &( "table" ) ) + ((((n_pre + 1) * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l) ((0 : Int)))))
  ** (intArray.undef_seg ( &( "table" ) ) (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j) ” &&
  “ ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Znth ((((n_pre + 1) * i) + j)) (mixed_table) (None)) = None) ” &&
  “ ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l) ((0 : Int)))))) ” &&
  “ ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l) ((0 : Int)))))) ” &&
  “ ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int))) ” &&
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) < n_pre) ” &&
  “ ((0 : Int) <= (j - 1)) ” &&
  “ ((j - 1) < n_pre) ” &&
  “ ((0 : Int) <= ((stride * i) + j)) ” &&
  “ (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * (i - 1)) + (j - 1))) ” &&
  “ (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * (i - 1)) + j)) ” &&
  “ (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * i) + (j - 1))) ” &&
  “ (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (j <= n_pre) ” &&
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= ((stride * i) + j)) ” &&
  “ (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j) ” &&
  “ ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1))) ”
  &&  (((( &( "table" ) ) + (((stride * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l) ((0 : Int)))))
  ** (intArray.mixed_seg ( &( "table" ) ) (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table)))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table)))
  ** (((( &( "table" ) ) + ((((n_pre + 1) * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l) ((0 : Int)))))
  ** (intArray.undef_seg ( &( "table" ) ) (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)

noncomputable def longest_common_sequence_partial_solve_wit_10 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table : (List (Option Int))) (table_l : (List Int)) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table) (None)) = None)) (PreH9 : ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l) ((0 : Int))))))) (PreH10 : ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l) ((0 : Int))))))) (PreH11 : ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int)))) (PreH12 : ((0 : Int) <= (i - 1))) (PreH13 : ((i - 1) < n_pre)) (PreH14 : ((0 : Int) <= (j - 1))) (PreH15 : ((j - 1) < n_pre)) (PreH16 : ((0 : Int) <= ((stride * i) + j))) (PreH17 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH18 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH19 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH20 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH21 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH22 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH23 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH24 : (n_pre <= INT_MAX)) (PreH25 : (n_pre >= INT_MIN)) (PreH26 : (j <= n_pre)) (PreH27 : (stride = (n_pre + 1))) (PreH28 : ((0 : Int) <= n_pre)) (PreH29 : (n_pre <= 1000)) (PreH30 : ((Zlength (xs)) = n_pre)) (PreH31 : ((Zlength (ys)) = n_pre)) (PreH32 : (1 <= i)) (PreH33 : (i <= n_pre)) (PreH34 : (1 <= j)) (PreH35 : (j <= (n_pre + 1))) (PreH36 : ((0 : Int) <= ((stride * i) + j))) (PreH37 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH38 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH39 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH40 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (((( &( "table" ) ) + (((stride * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l) ((0 : Int)))))
  ** (intArray.mixed_seg ( &( "table" ) ) (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table)))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table)))
  ** (((( &( "table" ) ) + ((((n_pre + 1) * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l) ((0 : Int)))))
  ** (intArray.undef_seg ( &( "table" ) ) (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j) ” &&
  “ ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Znth ((((n_pre + 1) * i) + j)) (mixed_table) (None)) = None) ” &&
  “ ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l) ((0 : Int)))))) ” &&
  “ ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l) ((0 : Int)))))) ” &&
  “ ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int))) ” &&
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) < n_pre) ” &&
  “ ((0 : Int) <= (j - 1)) ” &&
  “ ((j - 1) < n_pre) ” &&
  “ ((0 : Int) <= ((stride * i) + j)) ” &&
  “ (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * (i - 1)) + (j - 1))) ” &&
  “ (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * (i - 1)) + j)) ” &&
  “ (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * i) + (j - 1))) ” &&
  “ (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (j <= n_pre) ” &&
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= ((stride * i) + j)) ” &&
  “ (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j) ” &&
  “ ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1))) ”
  &&  (((( &( "table" ) ) + (((stride * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l) ((0 : Int)))))
  ** (((( &( "table" ) ) + (((stride * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l) ((0 : Int)))))
  ** (intArray.mixed_seg ( &( "table" ) ) (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table)))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table)))
  ** (intArray.undef_seg ( &( "table" ) ) (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)

noncomputable def longest_common_sequence_partial_solve_wit_11 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table : (List (Option Int))) (table_l : (List Int)) (PreH1 : ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l) ((0 : Int))) >= (Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l) ((0 : Int))))) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH7 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) (PreH9 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table) (None)) = None)) (PreH10 : ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l) ((0 : Int))))))) (PreH11 : ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l) ((0 : Int))))))) (PreH12 : ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int)))) (PreH13 : ((0 : Int) <= (i - 1))) (PreH14 : ((i - 1) < n_pre)) (PreH15 : ((0 : Int) <= (j - 1))) (PreH16 : ((j - 1) < n_pre)) (PreH17 : ((0 : Int) <= ((stride * i) + j))) (PreH18 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH19 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH20 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH21 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH22 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH24 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= n_pre)) (PreH28 : (stride = (n_pre + 1))) (PreH29 : ((0 : Int) <= n_pre)) (PreH30 : (n_pre <= 1000)) (PreH31 : ((Zlength (xs)) = n_pre)) (PreH32 : ((Zlength (ys)) = n_pre)) (PreH33 : (1 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (1 <= j)) (PreH36 : (j <= (n_pre + 1))) (PreH37 : ((0 : Int) <= ((stride * i) + j))) (PreH38 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH39 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH40 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH41 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (((( &( "table" ) ) + (((stride * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l) ((0 : Int)))))
  ** (((( &( "table" ) ) + (((stride * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l) ((0 : Int)))))
  ** (intArray.mixed_seg ( &( "table" ) ) (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table)))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table)))
  ** (intArray.undef_seg ( &( "table" ) ) (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l) ((0 : Int))) >= (Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l) ((0 : Int)))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j) ” &&
  “ ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Znth ((((n_pre + 1) * i) + j)) (mixed_table) (None)) = None) ” &&
  “ ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l) ((0 : Int)))))) ” &&
  “ ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l) ((0 : Int)))))) ” &&
  “ ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int))) ” &&
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) < n_pre) ” &&
  “ ((0 : Int) <= (j - 1)) ” &&
  “ ((j - 1) < n_pre) ” &&
  “ ((0 : Int) <= ((stride * i) + j)) ” &&
  “ (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * (i - 1)) + (j - 1))) ” &&
  “ (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * (i - 1)) + j)) ” &&
  “ (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * i) + (j - 1))) ” &&
  “ (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (j <= n_pre) ” &&
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= ((stride * i) + j)) ” &&
  “ (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j) ” &&
  “ ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1))) ”
  &&  (((( &( "table" ) ) + (((stride * i) + j) * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_missing_i ( &( "table" ) ) ((stride * i) + j) (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (((( &( "table" ) ) + (((stride * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l) ((0 : Int)))))
  ** (((( &( "table" ) ) + (((stride * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l) ((0 : Int)))))
  ** (intArray.mixed_seg ( &( "table" ) ) (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table)))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table)))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)

noncomputable def longest_common_sequence_partial_solve_wit_12 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (j : Int) (i : Int) (stride : Int) (mixed_table : (List (Option Int))) (table_l : (List Int)) (PreH1 : ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l) ((0 : Int))) < (Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l) ((0 : Int))))) (PreH2 : (1 <= i)) (PreH3 : (i <= n_pre)) (PreH4 : (1 <= j)) (PreH5 : (j <= n_pre)) (PreH6 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH7 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) (PreH9 : ((Znth ((((n_pre + 1) * i) + j)) (mixed_table) (None)) = None)) (PreH10 : ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l) ((0 : Int))))))) (PreH11 : ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l) ((0 : Int))))))) (PreH12 : ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int)))) (PreH13 : ((0 : Int) <= (i - 1))) (PreH14 : ((i - 1) < n_pre)) (PreH15 : ((0 : Int) <= (j - 1))) (PreH16 : ((j - 1) < n_pre)) (PreH17 : ((0 : Int) <= ((stride * i) + j))) (PreH18 : (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH19 : ((0 : Int) <= ((stride * (i - 1)) + (j - 1)))) (PreH20 : (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH21 : ((0 : Int) <= ((stride * (i - 1)) + j))) (PreH22 : (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1)))) (PreH23 : ((0 : Int) <= ((stride * i) + (j - 1)))) (PreH24 : (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1)))) (PreH25 : (n_pre <= INT_MAX)) (PreH26 : (n_pre >= INT_MIN)) (PreH27 : (j <= n_pre)) (PreH28 : (stride = (n_pre + 1))) (PreH29 : ((0 : Int) <= n_pre)) (PreH30 : (n_pre <= 1000)) (PreH31 : ((Zlength (xs)) = n_pre)) (PreH32 : ((Zlength (ys)) = n_pre)) (PreH33 : (1 <= i)) (PreH34 : (i <= n_pre)) (PreH35 : (1 <= j)) (PreH36 : (j <= (n_pre + 1))) (PreH37 : ((0 : Int) <= ((stride * i) + j))) (PreH38 : (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1)))) (PreH39 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH40 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH41 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (((( &( "table" ) ) + (((stride * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l) ((0 : Int)))))
  ** (((( &( "table" ) ) + (((stride * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l) ((0 : Int)))))
  ** (intArray.mixed_seg ( &( "table" ) ) (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table)))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table)))
  ** (intArray.undef_seg ( &( "table" ) ) (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l) ((0 : Int))) < (Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l) ((0 : Int)))) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j) ” &&
  “ ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Znth ((((n_pre + 1) * i) + j)) (mixed_table) (None)) = None) ” &&
  “ ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l) ((0 : Int)))))) ” &&
  “ ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l) ((0 : Int)))))) ” &&
  “ ((Znth (i - 1) xs (0 : Int)) ≠ (Znth (j - 1) ys (0 : Int))) ” &&
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) < n_pre) ” &&
  “ ((0 : Int) <= (j - 1)) ” &&
  “ ((j - 1) < n_pre) ” &&
  “ ((0 : Int) <= ((stride * i) + j)) ” &&
  “ (((stride * i) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * (i - 1)) + (j - 1))) ” &&
  “ (((stride * (i - 1)) + (j - 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * (i - 1)) + j)) ” &&
  “ (((stride * (i - 1)) + j) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((0 : Int) <= ((stride * i) + (j - 1))) ” &&
  “ (((stride * i) + (j - 1)) < ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (n_pre <= INT_MAX) ” &&
  “ (n_pre >= INT_MIN) ” &&
  “ (j <= n_pre) ” &&
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= (n_pre + 1)) ” &&
  “ ((0 : Int) <= ((stride * i) + j)) ” &&
  “ (((stride * i) + j) <= ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j) ” &&
  “ ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1))) ”
  &&  (((( &( "table" ) ) + (((stride * i) + j) * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_missing_i ( &( "table" ) ) ((stride * i) + j) (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (((( &( "table" ) ) + (((stride * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * i) + (j - 1))) (table_l) ((0 : Int)))))
  ** (((( &( "table" ) ) + (((stride * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth (((((Zlength (xs)) + 1) * (i - 1)) + j)) (table_l) ((0 : Int)))))
  ** (intArray.mixed_seg ( &( "table" ) ) (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table)))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table)))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table)))
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)

noncomputable def longest_common_sequence_partial_solve_wit_13 : Prop :=
  forall (n_pre : Int) (y_pre : Int) (x_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (stride : Int) (PreH1 : (stride = (n_pre + 1))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 1000)) (PreH4 : ((Zlength (xs)) = n_pre)) (PreH5 : ((Zlength (ys)) = n_pre)) (PreH6 : (LCSNRowsProgress xs ys mixed_table table_l n_pre (n_pre + 1))) (PreH7 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH8 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) (PreH9 : (LCSNTableResult xs ys n_pre table_l)) (PreH10 : ((0 : Int) <= ((stride * n_pre) + n_pre))) (PreH11 : (((stride * n_pre) + n_pre) < ((n_pre + 1) * (n_pre + 1)))) ,
  (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) table_l)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)
|--
  “ (stride = (n_pre + 1)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 1000) ” &&
  “ ((Zlength (xs)) = n_pre) ” &&
  “ ((Zlength (ys)) = n_pre) ” &&
  “ (LCSNRowsProgress xs ys mixed_table table_l n_pre (n_pre + 1)) ” &&
  “ ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ (LCSNTableResult xs ys n_pre table_l) ” &&
  “ ((0 : Int) <= ((stride * n_pre) + n_pre)) ” &&
  “ (((stride * n_pre) + n_pre) < ((n_pre + 1) * (n_pre + 1))) ”
  &&  (((( &( "table" ) ) + (((stride * n_pre) + n_pre) * sizeof(INT)))) # Int |-> ((Znth ((stride * n_pre) + n_pre) table_l (0 : Int))))
  ** (intArray.missing_i ( &( "table" ) ) ((stride * n_pre) + n_pre) (0 : Int) ((n_pre + 1) * (n_pre + 1)) table_l)
  ** (intArray.full x_pre n_pre xs)
  ** (intArray.full y_pre n_pre ys)
  ** (intArray.undef_seg ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) 1002001)

noncomputable def longest_common_sequence_which_implies_wit_1 : Prop :=
  (
forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (i : Int) (j : Int) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
|--
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j) ” &&
  “ ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Znth ((((n_pre + 1) * i) + j)) (mixed_table) (None)) = None) ” &&
  “ ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int)))))) ” &&
  “ ((0 : Int) <= (Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int)))) ” &&
  “ ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))) <= n_pre) ”
  &&  (intArray.mixed_seg ( &( "table" ) ) (0 : Int) (((n_pre + 1) * (i - 1)) + (j - 1)) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table)))
  ** (((( &( "table" ) ) + ((((n_pre + 1) * (i - 1)) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int)))))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * (i - 1)) + (j - 1)) + 1) (((n_pre + 1) * i) + j) (sublist (((((n_pre + 1) * (i - 1)) + (j - 1)) + 1)) ((((n_pre + 1) * i) + j)) (mixed_table)))
  ** (intArray.undef_seg ( &( "table" ) ) (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table)))
) \/
(
forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (i : Int) (j : Int) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
|--
  “ ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))) <= n_pre) ” &&
  “ ((0 : Int) <= (Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int)))) ” &&
  “ ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int)))))) ” &&
  “ ((Znth ((((n_pre + 1) * i) + j)) (mixed_table) (None)) = None) ”
  &&  (intArray.mixed_seg ( &( "table" ) ) (0 : Int) (((n_pre + 1) * (i - 1)) + (j - 1)) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table)))
  ** (((( &( "table" ) ) + ((((n_pre + 1) * (i - 1)) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int)))))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * (i - 1)) + (j - 1)) + 1) (((n_pre + 1) * i) + j) (sublist (((((n_pre + 1) * (i - 1)) + (j - 1)) + 1)) ((((n_pre + 1) * i) + j)) (mixed_table)))
  ** (intArray.undef_seg ( &( "table" ) ) (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table)))
)

noncomputable def longest_common_sequence_which_implies_wit_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (i : Int) (j : Int) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
|--
  “ ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int))) <= n_pre) ”

noncomputable def longest_common_sequence_which_implies_wit_1_split_goal_2 : Prop :=
  forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (i : Int) (j : Int) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
|--
  “ ((0 : Int) <= (Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int)))) ”

noncomputable def longest_common_sequence_which_implies_wit_1_split_goal_3 : Prop :=
  forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (i : Int) (j : Int) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
|--
  “ ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int)))))) ”

noncomputable def longest_common_sequence_which_implies_wit_1_split_goal_4 : Prop :=
  forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (i : Int) (j : Int) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
|--
  “ ((Znth ((((n_pre + 1) * i) + j)) (mixed_table) (None)) = None) ”

noncomputable def longest_common_sequence_which_implies_wit_1_split_goal_spatial : Prop :=
  forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (i : Int) (j : Int) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
|--
  (intArray.mixed_seg ( &( "table" ) ) (0 : Int) (((n_pre + 1) * (i - 1)) + (j - 1)) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + (j - 1))) (mixed_table)))
  ** (((( &( "table" ) ) + ((((n_pre + 1) * (i - 1)) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * (i - 1)) + (j - 1))) (table_l) ((0 : Int)))))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * (i - 1)) + (j - 1)) + 1) (((n_pre + 1) * i) + j) (sublist (((((n_pre + 1) * (i - 1)) + (j - 1)) + 1)) ((((n_pre + 1) * i) + j)) (mixed_table)))
  ** (intArray.undef_seg ( &( "table" ) ) (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table)))

noncomputable def longest_common_sequence_which_implies_wit_2 : Prop :=
  (
forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (i : Int) (j : Int) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
|--
  “ (1 <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (1 <= j) ” &&
  “ (j <= n_pre) ” &&
  “ (LCSNRowProgress xs ys mixed_table table_l n_pre i j) ” &&
  “ ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1))) ” &&
  “ ((Znth ((((n_pre + 1) * i) + j)) (mixed_table) (None)) = None) ” &&
  “ ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l) ((0 : Int)))))) ” &&
  “ ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l) ((0 : Int)))))) ”
  &&  (intArray.mixed_seg ( &( "table" ) ) (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table)))
  ** (((( &( "table" ) ) + ((((n_pre + 1) * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l) ((0 : Int)))))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table)))
  ** (((( &( "table" ) ) + ((((n_pre + 1) * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l) ((0 : Int)))))
  ** (intArray.undef_seg ( &( "table" ) ) (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table)))
) \/
(
forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (i : Int) (j : Int) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
|--
  “ ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l) ((0 : Int)))))) ” &&
  “ ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l) ((0 : Int)))))) ” &&
  “ ((Znth ((((n_pre + 1) * i) + j)) (mixed_table) (None)) = None) ”
  &&  (intArray.mixed_seg ( &( "table" ) ) (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table)))
  ** (((( &( "table" ) ) + ((((n_pre + 1) * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l) ((0 : Int)))))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table)))
  ** (((( &( "table" ) ) + ((((n_pre + 1) * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l) ((0 : Int)))))
  ** (intArray.undef_seg ( &( "table" ) ) (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table)))
)

noncomputable def longest_common_sequence_which_implies_wit_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (i : Int) (j : Int) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
|--
  “ ((Znth ((((n_pre + 1) * i) + (j - 1))) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l) ((0 : Int)))))) ”

noncomputable def longest_common_sequence_which_implies_wit_2_split_goal_2 : Prop :=
  forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (i : Int) (j : Int) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
|--
  “ ((Znth ((((n_pre + 1) * (i - 1)) + j)) (mixed_table) (None)) = (Some ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l) ((0 : Int)))))) ”

noncomputable def longest_common_sequence_which_implies_wit_2_split_goal_3 : Prop :=
  forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (i : Int) (j : Int) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
|--
  “ ((Znth ((((n_pre + 1) * i) + j)) (mixed_table) (None)) = None) ”

noncomputable def longest_common_sequence_which_implies_wit_2_split_goal_spatial : Prop :=
  forall (n_pre : Int) (ys : (List Int)) (xs : (List Int)) (mixed_table : (List (Option Int))) (table_l : (List Int)) (i : Int) (j : Int) (PreH1 : (1 <= i)) (PreH2 : (i <= n_pre)) (PreH3 : (1 <= j)) (PreH4 : (j <= n_pre)) (PreH5 : (LCSNRowProgress xs ys mixed_table table_l n_pre i j)) (PreH6 : ((Zlength (mixed_table)) = ((n_pre + 1) * (n_pre + 1)))) (PreH7 : ((Zlength (table_l)) = ((n_pre + 1) * (n_pre + 1)))) ,
  (intArray.mixed_full ( &( "table" ) ) ((n_pre + 1) * (n_pre + 1)) mixed_table)
|--
  (intArray.mixed_seg ( &( "table" ) ) (0 : Int) (((n_pre + 1) * (i - 1)) + j) (sublist ((0 : Int)) ((((n_pre + 1) * (i - 1)) + j)) (mixed_table)))
  ** (((( &( "table" ) ) + ((((n_pre + 1) * (i - 1)) + j) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * (i - 1)) + j)) (table_l) ((0 : Int)))))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * (i - 1)) + j) + 1) (((n_pre + 1) * i) + (j - 1)) (sublist (((((n_pre + 1) * (i - 1)) + j) + 1)) ((((n_pre + 1) * i) + (j - 1))) (mixed_table)))
  ** (((( &( "table" ) ) + ((((n_pre + 1) * i) + (j - 1)) * sizeof(INT)))) # Int |-> ((Znth ((((n_pre + 1) * i) + (j - 1))) (table_l) ((0 : Int)))))
  ** (intArray.undef_seg ( &( "table" ) ) (((n_pre + 1) * i) + j) ((((n_pre + 1) * i) + j) + 1))
  ** (intArray.mixed_seg ( &( "table" ) ) ((((n_pre + 1) * i) + j) + 1) ((n_pre + 1) * (n_pre + 1)) (sublist (((((n_pre + 1) * i) + j) + 1)) (((n_pre + 1) * (n_pre + 1))) (mixed_table)))


structure VC_Correct : Type where
  proof_of_longest_common_sequence_safety_wit_1 : longest_common_sequence_safety_wit_1
  proof_of_longest_common_sequence_safety_wit_2 : longest_common_sequence_safety_wit_2
  proof_of_longest_common_sequence_safety_wit_3 : longest_common_sequence_safety_wit_3
  proof_of_longest_common_sequence_safety_wit_4 : longest_common_sequence_safety_wit_4
  proof_of_longest_common_sequence_safety_wit_5 : longest_common_sequence_safety_wit_5
  proof_of_longest_common_sequence_safety_wit_6 : longest_common_sequence_safety_wit_6
  proof_of_longest_common_sequence_safety_wit_7 : longest_common_sequence_safety_wit_7
  proof_of_longest_common_sequence_safety_wit_8 : longest_common_sequence_safety_wit_8
  proof_of_longest_common_sequence_safety_wit_9 : longest_common_sequence_safety_wit_9
  proof_of_longest_common_sequence_safety_wit_10 : longest_common_sequence_safety_wit_10
  proof_of_longest_common_sequence_safety_wit_11 : longest_common_sequence_safety_wit_11
  proof_of_longest_common_sequence_safety_wit_12 : longest_common_sequence_safety_wit_12
  proof_of_longest_common_sequence_safety_wit_13 : longest_common_sequence_safety_wit_13
  proof_of_longest_common_sequence_safety_wit_14 : longest_common_sequence_safety_wit_14
  proof_of_longest_common_sequence_safety_wit_15 : longest_common_sequence_safety_wit_15
  proof_of_longest_common_sequence_safety_wit_16 : longest_common_sequence_safety_wit_16
  proof_of_longest_common_sequence_safety_wit_17 : longest_common_sequence_safety_wit_17
  proof_of_longest_common_sequence_safety_wit_18 : longest_common_sequence_safety_wit_18
  proof_of_longest_common_sequence_safety_wit_19 : longest_common_sequence_safety_wit_19
  proof_of_longest_common_sequence_safety_wit_20 : longest_common_sequence_safety_wit_20
  proof_of_longest_common_sequence_safety_wit_21 : longest_common_sequence_safety_wit_21
  proof_of_longest_common_sequence_safety_wit_22 : longest_common_sequence_safety_wit_22
  proof_of_longest_common_sequence_safety_wit_23 : longest_common_sequence_safety_wit_23
  proof_of_longest_common_sequence_safety_wit_24 : longest_common_sequence_safety_wit_24
  proof_of_longest_common_sequence_safety_wit_25 : longest_common_sequence_safety_wit_25
  proof_of_longest_common_sequence_safety_wit_26 : longest_common_sequence_safety_wit_26
  proof_of_longest_common_sequence_safety_wit_27 : longest_common_sequence_safety_wit_27
  proof_of_longest_common_sequence_safety_wit_28 : longest_common_sequence_safety_wit_28
  proof_of_longest_common_sequence_safety_wit_29 : longest_common_sequence_safety_wit_29
  proof_of_longest_common_sequence_safety_wit_30 : longest_common_sequence_safety_wit_30
  proof_of_longest_common_sequence_safety_wit_31 : longest_common_sequence_safety_wit_31
  proof_of_longest_common_sequence_safety_wit_32 : longest_common_sequence_safety_wit_32
  proof_of_longest_common_sequence_safety_wit_33 : longest_common_sequence_safety_wit_33
  proof_of_longest_common_sequence_safety_wit_34 : longest_common_sequence_safety_wit_34
  proof_of_longest_common_sequence_safety_wit_35 : longest_common_sequence_safety_wit_35
  proof_of_longest_common_sequence_safety_wit_36 : longest_common_sequence_safety_wit_36
  proof_of_longest_common_sequence_safety_wit_37 : longest_common_sequence_safety_wit_37
  proof_of_longest_common_sequence_safety_wit_38 : longest_common_sequence_safety_wit_38
  proof_of_longest_common_sequence_safety_wit_39 : longest_common_sequence_safety_wit_39
  proof_of_longest_common_sequence_safety_wit_40 : longest_common_sequence_safety_wit_40
  proof_of_longest_common_sequence_safety_wit_41 : longest_common_sequence_safety_wit_41
  proof_of_longest_common_sequence_safety_wit_42 : longest_common_sequence_safety_wit_42
  proof_of_longest_common_sequence_safety_wit_43 : longest_common_sequence_safety_wit_43
  proof_of_longest_common_sequence_safety_wit_44 : longest_common_sequence_safety_wit_44
  proof_of_longest_common_sequence_safety_wit_45 : longest_common_sequence_safety_wit_45
  proof_of_longest_common_sequence_return_wit_1 : longest_common_sequence_return_wit_1
  proof_of_longest_common_sequence_partial_solve_wit_1 : longest_common_sequence_partial_solve_wit_1
  proof_of_longest_common_sequence_partial_solve_wit_2 : longest_common_sequence_partial_solve_wit_2
  proof_of_longest_common_sequence_partial_solve_wit_3 : longest_common_sequence_partial_solve_wit_3
  proof_of_longest_common_sequence_partial_solve_wit_4 : longest_common_sequence_partial_solve_wit_4
  proof_of_longest_common_sequence_partial_solve_wit_5_pure : longest_common_sequence_partial_solve_wit_5_pure
  proof_of_longest_common_sequence_partial_solve_wit_5 : longest_common_sequence_partial_solve_wit_5
  proof_of_longest_common_sequence_partial_solve_wit_6 : longest_common_sequence_partial_solve_wit_6
  proof_of_longest_common_sequence_partial_solve_wit_7 : longest_common_sequence_partial_solve_wit_7
  proof_of_longest_common_sequence_partial_solve_wit_8_pure : longest_common_sequence_partial_solve_wit_8_pure
  proof_of_longest_common_sequence_partial_solve_wit_8 : longest_common_sequence_partial_solve_wit_8
  proof_of_longest_common_sequence_partial_solve_wit_9 : longest_common_sequence_partial_solve_wit_9
  proof_of_longest_common_sequence_partial_solve_wit_10 : longest_common_sequence_partial_solve_wit_10
  proof_of_longest_common_sequence_partial_solve_wit_11 : longest_common_sequence_partial_solve_wit_11
  proof_of_longest_common_sequence_partial_solve_wit_12 : longest_common_sequence_partial_solve_wit_12
  proof_of_longest_common_sequence_partial_solve_wit_13 : longest_common_sequence_partial_solve_wit_13
  proof_of_longest_common_sequence_entail_wit_1 : longest_common_sequence_entail_wit_1
  proof_of_longest_common_sequence_entail_wit_2 : longest_common_sequence_entail_wit_2
  proof_of_longest_common_sequence_entail_wit_3 : longest_common_sequence_entail_wit_3
  proof_of_longest_common_sequence_entail_wit_4 : longest_common_sequence_entail_wit_4
  proof_of_longest_common_sequence_entail_wit_5 : longest_common_sequence_entail_wit_5
  proof_of_longest_common_sequence_entail_wit_6 : longest_common_sequence_entail_wit_6
  proof_of_longest_common_sequence_entail_wit_7 : longest_common_sequence_entail_wit_7
  proof_of_longest_common_sequence_entail_wit_8 : longest_common_sequence_entail_wit_8
  proof_of_longest_common_sequence_entail_wit_9_1 : longest_common_sequence_entail_wit_9_1
  proof_of_longest_common_sequence_entail_wit_9_2 : longest_common_sequence_entail_wit_9_2
  proof_of_longest_common_sequence_entail_wit_9_3 : longest_common_sequence_entail_wit_9_3
  proof_of_longest_common_sequence_entail_wit_10 : longest_common_sequence_entail_wit_10
  proof_of_longest_common_sequence_entail_wit_11 : longest_common_sequence_entail_wit_11
  proof_of_longest_common_sequence_entail_wit_12 : longest_common_sequence_entail_wit_12
  proof_of_longest_common_sequence_entail_wit_13 : longest_common_sequence_entail_wit_13
  proof_of_longest_common_sequence_which_implies_wit_1 : longest_common_sequence_which_implies_wit_1
  proof_of_longest_common_sequence_which_implies_wit_2 : longest_common_sequence_which_implies_wit_2

end SimpleC.EE.LLM_bench.Algorithms.lcs_n.lcs_n_goal
