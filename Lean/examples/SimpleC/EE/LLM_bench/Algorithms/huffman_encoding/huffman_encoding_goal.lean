import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Algorithms.huffman_encoding.huffman_encoding_lib
open SimpleC.EE.LLM_bench.Algorithms.huffman_encoding.huffman_encoding_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.huffman_encoding.huffman_encoding_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance huffman_encoding_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def huffman_cost_safety_wit_1 : Prop :=
  forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) ,
  ((( &( "i" ) )) # Int |->_)
  ** (intArray.undef_full ( &( "work" ) ) 8)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full weights_pre n_pre weights_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def huffman_cost_safety_wit_2 : Prop :=
  forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (i : Int) (copied : (List Int)) (remaining : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH6 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH7 : (weights_l = (copied ++ remaining))) (PreH8 : ((Zlength (copied)) = i)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) ,
  (intArray.seg ( &( "work" ) ) (0 : Int) (i + 1) (copied ++ ((Znth i weights_l (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "work" ) ) (i + 1) n_pre)
  ** (intArray.full weights_pre n_pre weights_l)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def huffman_cost_safety_wit_3 : Prop :=
  forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (i : Int) (copied : (List Int)) (remaining : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH6 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH7 : (weights_l = (copied ++ remaining))) (PreH8 : ((Zlength (copied)) = i)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) ,
  ((( &( "total" ) )) # Int |->_)
  ** ((( &( "active" ) )) # Int |-> (n_pre))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.seg ( &( "work" ) ) (0 : Int) i copied)
  ** (intArray.undef_seg ( &( "work" ) ) i n_pre)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def huffman_cost_safety_wit_4 : Prop :=
  forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (active : Int) (work_l : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : ((Zlength (work_l)) = n_pre)) (PreH5 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH6 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH7 : (1 <= active)) (PreH8 : (active <= n_pre)) (PreH9 : ((0 : Int) <= total)) (PreH10 : (total <= 56000)) (PreH11 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l)))) (PreH12 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l)))) (PreH13 : (HuffmanProgress weights_l work_l active total)) ,
  ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "active" ) )) # Int |-> (active))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full ( &( "work" ) ) n_pre work_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def huffman_cost_safety_wit_5 : Prop :=
  forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (active : Int) (work_l : (List Int)) (PreH1 : (active > 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (1 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : ((0 : Int) <= total)) (PreH11 : (total <= 56000)) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l)))) (PreH13 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l)))) (PreH14 : (HuffmanProgress weights_l work_l active total)) ,
  ((( &( "first" ) )) # Int |->_)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "active" ) )) # Int |-> (active))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full ( &( "work" ) ) n_pre work_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def huffman_cost_safety_wit_6 : Prop :=
  forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (active : Int) (work_l : (List Int)) (PreH1 : (active > 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (1 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : ((0 : Int) <= total)) (PreH11 : (total <= 56000)) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l)))) (PreH13 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l)))) (PreH14 : (HuffmanProgress weights_l work_l active total)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "first" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "active" ) )) # Int |-> (active))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full ( &( "work" ) ) n_pre work_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def huffman_cost_safety_wit_7 : Prop :=
  forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : ((Znth i work_l (0 : Int)) < (Znth first work_l (0 : Int)))) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i < n_pre)) (PreH4 : (i < active)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (work_l)) = n_pre)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH10 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH11 : (2 <= active)) (PreH12 : (active <= n_pre)) (PreH13 : (1 <= i)) (PreH14 : (i <= active)) (PreH15 : (i <= n_pre)) (PreH16 : ((0 : Int) <= first)) (PreH17 : (first < i)) (PreH18 : (first < n_pre)) (PreH19 : ((0 : Int) <= total)) (PreH20 : (total <= 56000)) (PreH21 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l)))) (PreH22 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l)))) (PreH23 : (HuffmanProgress weights_l work_l active total)) (PreH24 : (HuffmanMinScan work_l i first)) ,
  (intArray.full ( &( "work" ) ) n_pre work_l)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "active" ) )) # Int |-> (active))
  ** ((( &( "first" ) )) # Int |-> (i))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def huffman_cost_safety_wit_8 : Prop :=
  forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : ((Znth i work_l (0 : Int)) >= (Znth first work_l (0 : Int)))) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i < n_pre)) (PreH4 : (i < active)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (work_l)) = n_pre)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH10 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH11 : (2 <= active)) (PreH12 : (active <= n_pre)) (PreH13 : (1 <= i)) (PreH14 : (i <= active)) (PreH15 : (i <= n_pre)) (PreH16 : ((0 : Int) <= first)) (PreH17 : (first < i)) (PreH18 : (first < n_pre)) (PreH19 : ((0 : Int) <= total)) (PreH20 : (total <= 56000)) (PreH21 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l)))) (PreH22 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l)))) (PreH23 : (HuffmanProgress weights_l work_l active total)) (PreH24 : (HuffmanMinScan work_l i first)) ,
  (intArray.full ( &( "work" ) ) n_pre work_l)
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "active" ) )) # Int |-> (active))
  ** ((( &( "first" ) )) # Int |-> (first))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def huffman_cost_safety_wit_9 : Prop :=
  forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (2 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < i)) (PreH15 : (first < n_pre)) (PreH16 : ((0 : Int) <= total)) (PreH17 : (total <= 56000)) (PreH18 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l)))) (PreH19 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l)))) (PreH20 : (HuffmanProgress weights_l work_l active total)) (PreH21 : (HuffmanMinScan work_l i first)) ,
  (intArray.full ( &( "work" ) ) n_pre work_l)
  ** ((( &( "x" ) )) # Int |-> ((Znth first work_l (0 : Int))))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "active" ) )) # Int |-> (active))
  ** ((( &( "first" ) )) # Int |-> (first))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  “ ((active - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (active - 1)) ”

noncomputable def huffman_cost_safety_wit_10 : Prop :=
  forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (2 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < i)) (PreH15 : (first < n_pre)) (PreH16 : ((0 : Int) <= total)) (PreH17 : (total <= 56000)) (PreH18 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l)))) (PreH19 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l)))) (PreH20 : (HuffmanProgress weights_l work_l active total)) (PreH21 : (HuffmanMinScan work_l i first)) ,
  ((( &( "second" ) )) # Int |->_)
  ** (intArray.full ( &( "work" ) ) n_pre (replace_Znth (first) ((Znth (active - 1) work_l (0 : Int))) (work_l)))
  ** ((( &( "x" ) )) # Int |-> ((Znth first work_l (0 : Int))))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "active" ) )) # Int |-> ((active - 1)))
  ** ((( &( "first" ) )) # Int |-> (first))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def huffman_cost_safety_wit_11 : Prop :=
  forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (2 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < i)) (PreH15 : (first < n_pre)) (PreH16 : ((0 : Int) <= total)) (PreH17 : (total <= 56000)) (PreH18 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l)))) (PreH19 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l)))) (PreH20 : (HuffmanProgress weights_l work_l active total)) (PreH21 : (HuffmanMinScan work_l i first)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "second" ) )) # Int |-> ((0 : Int)))
  ** (intArray.full ( &( "work" ) ) n_pre (replace_Znth (first) ((Znth (active - 1) work_l (0 : Int))) (work_l)))
  ** ((( &( "x" ) )) # Int |-> ((Znth first work_l (0 : Int))))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "active" ) )) # Int |-> ((active - 1)))
  ** ((( &( "first" ) )) # Int |-> (first))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def huffman_cost_safety_wit_12 : Prop :=
  forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : ((Znth i work_l (0 : Int)) < (Znth second work_l (0 : Int)))) (PreH2 : (i < active)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (work_l)) = n_pre)) (PreH7 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH8 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH9 : (1 <= active)) (PreH10 : (active < n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= first)) (PreH15 : (first < n_pre)) (PreH16 : ((0 : Int) <= second)) (PreH17 : (second < i)) (PreH18 : (second < n_pre)) (PreH19 : (1 <= x)) (PreH20 : (x <= 8000)) (PreH21 : ((0 : Int) <= total)) (PreH22 : (total <= 56000)) (PreH23 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l)))) (PreH24 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l)))) (PreH25 : (HuffmanFirstHeld weights_l work_l active x total)) (PreH26 : (HuffmanMinScan work_l i second)) ,
  (intArray.full ( &( "work" ) ) n_pre work_l)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "active" ) )) # Int |-> (active))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "first" ) )) # Int |-> (first))
  ** ((( &( "second" ) )) # Int |-> (i))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def huffman_cost_safety_wit_13 : Prop :=
  forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : ((Znth i work_l (0 : Int)) >= (Znth second work_l (0 : Int)))) (PreH2 : (i < active)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (work_l)) = n_pre)) (PreH7 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH8 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH9 : (1 <= active)) (PreH10 : (active < n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= first)) (PreH15 : (first < n_pre)) (PreH16 : ((0 : Int) <= second)) (PreH17 : (second < i)) (PreH18 : (second < n_pre)) (PreH19 : (1 <= x)) (PreH20 : (x <= 8000)) (PreH21 : ((0 : Int) <= total)) (PreH22 : (total <= 56000)) (PreH23 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l)))) (PreH24 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l)))) (PreH25 : (HuffmanFirstHeld weights_l work_l active x total)) (PreH26 : (HuffmanMinScan work_l i second)) ,
  (intArray.full ( &( "work" ) ) n_pre work_l)
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "active" ) )) # Int |-> (active))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "first" ) )) # Int |-> (first))
  ** ((( &( "second" ) )) # Int |-> (second))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def huffman_cost_safety_wit_14 : Prop :=
  forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < n_pre)) (PreH15 : ((0 : Int) <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : ((0 : Int) <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l)))) (PreH23 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l)))) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total)) (PreH25 : (HuffmanMinScan work_l i second)) ,
  (intArray.full ( &( "work" ) ) n_pre work_l)
  ** ((( &( "y" ) )) # Int |-> ((Znth second work_l (0 : Int))))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "active" ) )) # Int |-> (active))
  ** ((( &( "first" ) )) # Int |-> (first))
  ** ((( &( "second" ) )) # Int |-> (second))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  “ ((active - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (active - 1)) ”

noncomputable def huffman_cost_safety_wit_15 : Prop :=
  (
forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < n_pre)) (PreH15 : ((0 : Int) <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : ((0 : Int) <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l)))) (PreH23 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l)))) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total)) (PreH25 : (HuffmanMinScan work_l i second)) ,
  ((( &( "merged" ) )) # Int |->_)
  ** (intArray.full ( &( "work" ) ) n_pre (replace_Znth (second) ((Znth (active - 1) work_l (0 : Int))) (work_l)))
  ** ((( &( "y" ) )) # Int |-> ((Znth second work_l (0 : Int))))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "active" ) )) # Int |-> ((active - 1)))
  ** ((( &( "first" ) )) # Int |-> (first))
  ** ((( &( "second" ) )) # Int |-> (second))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  “ ((x + (Znth second work_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (x + (Znth second work_l (0 : Int)))) ”
) \/
(
forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < n_pre)) (PreH15 : ((0 : Int) <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : ((0 : Int) <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l)))) (PreH23 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l)))) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total)) (PreH25 : (HuffmanMinScan work_l i second)) ,
  ((( &( "merged" ) )) # Int |->_)
  ** (intArray.full ( &( "work" ) ) n_pre (replace_Znth (second) ((Znth (active - 1) work_l (0 : Int))) (work_l)))
  ** ((( &( "y" ) )) # Int |-> ((Znth second work_l (0 : Int))))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "active" ) )) # Int |-> ((active - 1)))
  ** ((( &( "first" ) )) # Int |-> (first))
  ** ((( &( "second" ) )) # Int |-> (second))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  “ ((x + (Znth second work_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (x + (Znth second work_l (0 : Int)))) ”
)

noncomputable def huffman_cost_safety_wit_15_split_goal_1 : Prop :=
  forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < n_pre)) (PreH15 : ((0 : Int) <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : ((0 : Int) <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l)))) (PreH23 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l)))) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total)) (PreH25 : (HuffmanMinScan work_l i second)) ,
  ((( &( "merged" ) )) # Int |->_)
  ** (intArray.full ( &( "work" ) ) n_pre (replace_Znth (second) ((Znth (active - 1) work_l (0 : Int))) (work_l)))
  ** ((( &( "y" ) )) # Int |-> ((Znth second work_l (0 : Int))))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "active" ) )) # Int |-> ((active - 1)))
  ** ((( &( "first" ) )) # Int |-> (first))
  ** ((( &( "second" ) )) # Int |-> (second))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  “ ((x + (Znth second work_l (0 : Int))) <= INT_MAX) ”

noncomputable def huffman_cost_safety_wit_15_split_goal_2 : Prop :=
  forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < n_pre)) (PreH15 : ((0 : Int) <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : ((0 : Int) <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l)))) (PreH23 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l)))) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total)) (PreH25 : (HuffmanMinScan work_l i second)) ,
  ((( &( "merged" ) )) # Int |->_)
  ** (intArray.full ( &( "work" ) ) n_pre (replace_Znth (second) ((Znth (active - 1) work_l (0 : Int))) (work_l)))
  ** ((( &( "y" ) )) # Int |-> ((Znth second work_l (0 : Int))))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "active" ) )) # Int |-> ((active - 1)))
  ** ((( &( "first" ) )) # Int |-> (first))
  ** ((( &( "second" ) )) # Int |-> (second))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  “ ((INT_MIN) <= (x + (Znth second work_l (0 : Int)))) ”

noncomputable def huffman_cost_safety_wit_16 : Prop :=
  (
forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < n_pre)) (PreH15 : ((0 : Int) <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : ((0 : Int) <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l)))) (PreH23 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l)))) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total)) (PreH25 : (HuffmanMinScan work_l i second)) ,
  ((( &( "merged" ) )) # Int |-> ((x + (Znth second work_l (0 : Int)))))
  ** (intArray.full ( &( "work" ) ) n_pre (replace_Znth (second) ((Znth (active - 1) work_l (0 : Int))) (work_l)))
  ** ((( &( "y" ) )) # Int |-> ((Znth second work_l (0 : Int))))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "active" ) )) # Int |-> ((active - 1)))
  ** ((( &( "first" ) )) # Int |-> (first))
  ** ((( &( "second" ) )) # Int |-> (second))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  “ ((total + (x + (Znth second work_l (0 : Int)))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (total + (x + (Znth second work_l (0 : Int))))) ”
) \/
(
forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < n_pre)) (PreH15 : ((0 : Int) <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : ((0 : Int) <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l)))) (PreH23 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l)))) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total)) (PreH25 : (HuffmanMinScan work_l i second)) ,
  ((( &( "merged" ) )) # Int |-> ((x + (Znth second work_l (0 : Int)))))
  ** (intArray.full ( &( "work" ) ) n_pre (replace_Znth (second) ((Znth (active - 1) work_l (0 : Int))) (work_l)))
  ** ((( &( "y" ) )) # Int |-> ((Znth second work_l (0 : Int))))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "active" ) )) # Int |-> ((active - 1)))
  ** ((( &( "first" ) )) # Int |-> (first))
  ** ((( &( "second" ) )) # Int |-> (second))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  “ ((total + (x + (Znth second work_l (0 : Int)))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (total + (x + (Znth second work_l (0 : Int))))) ”
)

noncomputable def huffman_cost_safety_wit_16_split_goal_1 : Prop :=
  forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < n_pre)) (PreH15 : ((0 : Int) <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : ((0 : Int) <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l)))) (PreH23 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l)))) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total)) (PreH25 : (HuffmanMinScan work_l i second)) ,
  ((( &( "merged" ) )) # Int |-> ((x + (Znth second work_l (0 : Int)))))
  ** (intArray.full ( &( "work" ) ) n_pre (replace_Znth (second) ((Znth (active - 1) work_l (0 : Int))) (work_l)))
  ** ((( &( "y" ) )) # Int |-> ((Znth second work_l (0 : Int))))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "active" ) )) # Int |-> ((active - 1)))
  ** ((( &( "first" ) )) # Int |-> (first))
  ** ((( &( "second" ) )) # Int |-> (second))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  “ ((total + (x + (Znth second work_l (0 : Int)))) <= INT_MAX) ”

noncomputable def huffman_cost_safety_wit_16_split_goal_2 : Prop :=
  forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < n_pre)) (PreH15 : ((0 : Int) <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : ((0 : Int) <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l)))) (PreH23 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l)))) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total)) (PreH25 : (HuffmanMinScan work_l i second)) ,
  ((( &( "merged" ) )) # Int |-> ((x + (Znth second work_l (0 : Int)))))
  ** (intArray.full ( &( "work" ) ) n_pre (replace_Znth (second) ((Znth (active - 1) work_l (0 : Int))) (work_l)))
  ** ((( &( "y" ) )) # Int |-> ((Znth second work_l (0 : Int))))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "active" ) )) # Int |-> ((active - 1)))
  ** ((( &( "first" ) )) # Int |-> (first))
  ** ((( &( "second" ) )) # Int |-> (second))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "total" ) )) # Int |-> (total))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  “ ((INT_MIN) <= (total + (x + (Znth second work_l (0 : Int))))) ”

noncomputable def huffman_cost_safety_wit_17 : Prop :=
  forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < n_pre)) (PreH15 : ((0 : Int) <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : ((0 : Int) <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l)))) (PreH23 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l)))) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total)) (PreH25 : (HuffmanMinScan work_l i second)) ,
  (intArray.full ( &( "work" ) ) n_pre (replace_Znth ((active - 1)) ((x + (Znth second work_l (0 : Int)))) ((replace_Znth (second) ((Znth (active - 1) work_l (0 : Int))) (work_l)))))
  ** ((( &( "merged" ) )) # Int |-> ((x + (Znth second work_l (0 : Int)))))
  ** ((( &( "y" ) )) # Int |-> ((Znth second work_l (0 : Int))))
  ** ((( &( "weights" ) )) # Ptr |-> (weights_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "active" ) )) # Int |-> ((active - 1)))
  ** ((( &( "first" ) )) # Int |-> (first))
  ** ((( &( "second" ) )) # Int |-> (second))
  ** ((( &( "x" ) )) # Int |-> (x))
  ** ((( &( "total" ) )) # Int |-> ((total + (x + (Znth second work_l (0 : Int))))))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  “ (((active - 1) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((active - 1) + 1)) ”

noncomputable def huffman_cost_entail_wit_1 : Prop :=
  (
forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) ,
  (intArray.undef_full ( &( "work" ) ) 8)
  ** (intArray.full weights_pre n_pre weights_l)
|--
  EX copied : (List Int), EX remaining : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) weights_l) ” &&
  “ (weights_l = (copied ++ remaining)) ” &&
  “ ((Zlength (copied)) = (0 : Int)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.seg ( &( "work" ) ) (0 : Int) (0 : Int) copied)
  ** (intArray.undef_seg ( &( "work" ) ) (0 : Int) n_pre)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
) \/
(
forall (n_pre : Int) (weights_l : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 8)) (PreH3 : ((Zlength (weights_l)) = n_pre)) (PreH4 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) ,
  (intArray.undef_full ( &( "work" ) ) 8)
|--
  EX remaining : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) weights_l) ” &&
  “ (weights_l = ((@List.nil Int) ++ remaining)) ” &&
  “ ((Zlength ((@List.nil Int))) = (0 : Int)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ”
  &&  (intArray.undef_seg ( &( "work" ) ) (0 : Int) n_pre)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
)

noncomputable def huffman_cost_entail_wit_2 : Prop :=
  (
forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (i : Int) (copied_2 : (List Int)) (remaining_2 : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH6 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH7 : (weights_l = (copied_2 ++ remaining_2))) (PreH8 : ((Zlength (copied_2)) = i)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) ,
  (intArray.seg ( &( "work" ) ) (0 : Int) (i + 1) (copied_2 ++ ((Znth i weights_l (0 : Int)) :: (@List.nil Int))))
  ** (intArray.undef_seg ( &( "work" ) ) (i + 1) n_pre)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  EX copied : (List Int), EX remaining : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) weights_l) ” &&
  “ (weights_l = (copied ++ remaining)) ” &&
  “ ((Zlength (copied)) = (i + 1)) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.seg ( &( "work" ) ) (0 : Int) (i + 1) copied)
  ** (intArray.undef_seg ( &( "work" ) ) (i + 1) n_pre)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
) \/
(
forall (n_pre : Int) (weights_l : (List Int)) (i : Int) (copied_2 : (List Int)) (remaining_2 : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH6 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH7 : (weights_l = (copied_2 ++ remaining_2))) (PreH8 : ((Zlength (copied_2)) = i)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) ,
  TT && emp 
|--
  EX remaining : (List Int),
  “ ((copied_2 ++ remaining_2) = ((copied_2 ++ ((Znth (Zlength (copied_2)) (copied_2 ++ remaining_2) (0 : Int)) :: (@List.nil Int))) ++ remaining)) ” &&
  “ ((Zlength ((copied_2 ++ ((Znth (Zlength (copied_2)) (copied_2 ++ remaining_2) (0 : Int)) :: (@List.nil Int))))) = ((Zlength (copied_2)) + 1)) ” &&
  “ ((0 : Int) <= ((Zlength (copied_2)) + 1)) ” &&
  “ (((Zlength (copied_2)) + 1) <= (Zlength ((copied_2 ++ remaining_2)))) ”
  &&  emp
)

noncomputable def huffman_cost_entail_wit_3 : Prop :=
  (
forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (i : Int) (copied : (List Int)) (remaining : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH6 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH7 : (weights_l = (copied ++ remaining))) (PreH8 : ((Zlength (copied)) = i)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.seg ( &( "work" ) ) (0 : Int) i copied)
  ** (intArray.undef_seg ( &( "work" ) ) i n_pre)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  EX work_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (work_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) weights_l) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 56000) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (n_pre) (work_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (n_pre) (work_l))) ” &&
  “ (HuffmanProgress weights_l work_l n_pre (0 : Int)) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full ( &( "work" ) ) n_pre work_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
) \/
(
forall (n_pre : Int) (weights_l : (List Int)) (i : Int) (copied : (List Int)) (remaining : (List Int)) (PreH1 : (i >= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH6 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH7 : (weights_l = (copied ++ remaining))) (PreH8 : ((Zlength (copied)) = i)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) ,
  (intArray.seg ( &( "work" ) ) (0 : Int) i copied)
|--
  EX work_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (work_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) weights_l) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 56000) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (n_pre) (work_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (n_pre) (work_l))) ” &&
  “ (HuffmanProgress weights_l work_l n_pre (0 : Int)) ”
  &&  (intArray.full ( &( "work" ) ) n_pre work_l)
)

noncomputable def huffman_cost_entail_wit_4 : Prop :=
  (
forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (active : Int) (work_l_2 : (List Int)) (PreH1 : (active > 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l_2)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (1 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : ((0 : Int) <= total)) (PreH11 : (total <= 56000)) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l_2)))) (PreH13 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l_2)))) (PreH14 : (HuffmanProgress weights_l work_l_2 active total)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full ( &( "work" ) ) n_pre work_l_2)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  EX work_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (work_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) weights_l) ” &&
  “ (2 <= active) ” &&
  “ (active <= n_pre) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= active) ” &&
  “ (1 <= n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) < 1) ” &&
  “ ((0 : Int) < n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 56000) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l))) ” &&
  “ (HuffmanProgress weights_l work_l active total) ” &&
  “ (HuffmanMinScan work_l 1 (0 : Int)) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full ( &( "work" ) ) n_pre work_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
) \/
(
forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (active : Int) (work_l_2 : (List Int)) (PreH1 : (active > 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l_2)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (1 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : ((0 : Int) <= total)) (PreH11 : (total <= 56000)) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l_2)))) (PreH13 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l_2)))) (PreH14 : (HuffmanProgress weights_l work_l_2 active total)) ,
  TT && emp 
|--
  “ (HuffmanMinScan work_l_2 1 (0 : Int)) ”
  &&  emp
)

noncomputable def huffman_cost_entail_wit_4_split_goal_1 : Prop :=
  forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (active : Int) (work_l_2 : (List Int)) (PreH1 : (active > 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l_2)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (1 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : ((0 : Int) <= total)) (PreH11 : (total <= 56000)) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l_2)))) (PreH13 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l_2)))) (PreH14 : (HuffmanProgress weights_l work_l_2 active total)) ,
  (HuffmanMinScan work_l_2 1 (0 : Int))

noncomputable def huffman_cost_entail_wit_5 : Prop :=
  forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : (i < active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (2 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < i)) (PreH15 : (first < n_pre)) (PreH16 : ((0 : Int) <= total)) (PreH17 : (total <= 56000)) (PreH18 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l)))) (PreH19 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l)))) (PreH20 : (HuffmanProgress weights_l work_l active total)) (PreH21 : (HuffmanMinScan work_l i first)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full ( &( "work" ) ) n_pre work_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (i < active) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (work_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) weights_l) ” &&
  “ (2 <= active) ” &&
  “ (active <= n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= active) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= first) ” &&
  “ (first < i) ” &&
  “ (first < n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 56000) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l))) ” &&
  “ (HuffmanProgress weights_l work_l active total) ” &&
  “ (HuffmanMinScan work_l i first) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full ( &( "work" ) ) n_pre work_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)

noncomputable def huffman_cost_entail_wit_6_1 : Prop :=
  (
forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l_2 : (List Int)) (PreH1 : ((Znth i work_l_2 (0 : Int)) < (Znth first work_l_2 (0 : Int)))) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i < n_pre)) (PreH4 : (i < active)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (work_l_2)) = n_pre)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH10 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH11 : (2 <= active)) (PreH12 : (active <= n_pre)) (PreH13 : (1 <= i)) (PreH14 : (i <= active)) (PreH15 : (i <= n_pre)) (PreH16 : ((0 : Int) <= first)) (PreH17 : (first < i)) (PreH18 : (first < n_pre)) (PreH19 : ((0 : Int) <= total)) (PreH20 : (total <= 56000)) (PreH21 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l_2)))) (PreH22 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l_2)))) (PreH23 : (HuffmanProgress weights_l work_l_2 active total)) (PreH24 : (HuffmanMinScan work_l_2 i first)) ,
  (intArray.full ( &( "work" ) ) n_pre work_l_2)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  EX work_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (work_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) weights_l) ” &&
  “ (2 <= active) ” &&
  “ (active <= n_pre) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= active) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (i + 1)) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 56000) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l))) ” &&
  “ (HuffmanProgress weights_l work_l active total) ” &&
  “ (HuffmanMinScan work_l (i + 1) i) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full ( &( "work" ) ) n_pre work_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
) \/
(
forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l_2 : (List Int)) (PreH1 : ((Znth i work_l_2 (0 : Int)) < (Znth first work_l_2 (0 : Int)))) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i < n_pre)) (PreH4 : (i < active)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (work_l_2)) = n_pre)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH10 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH11 : (2 <= active)) (PreH12 : (active <= n_pre)) (PreH13 : (1 <= i)) (PreH14 : (i <= active)) (PreH15 : (i <= n_pre)) (PreH16 : ((0 : Int) <= first)) (PreH17 : (first < i)) (PreH18 : (first < n_pre)) (PreH19 : ((0 : Int) <= total)) (PreH20 : (total <= 56000)) (PreH21 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l_2)))) (PreH22 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l_2)))) (PreH23 : (HuffmanProgress weights_l work_l_2 active total)) (PreH24 : (HuffmanMinScan work_l_2 i first)) ,
  TT && emp 
|--
  “ (HuffmanMinScan work_l_2 (i + 1) i) ”
  &&  emp
)

noncomputable def huffman_cost_entail_wit_6_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l_2 : (List Int)) (PreH1 : ((Znth i work_l_2 (0 : Int)) < (Znth first work_l_2 (0 : Int)))) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i < n_pre)) (PreH4 : (i < active)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (work_l_2)) = n_pre)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH10 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH11 : (2 <= active)) (PreH12 : (active <= n_pre)) (PreH13 : (1 <= i)) (PreH14 : (i <= active)) (PreH15 : (i <= n_pre)) (PreH16 : ((0 : Int) <= first)) (PreH17 : (first < i)) (PreH18 : (first < n_pre)) (PreH19 : ((0 : Int) <= total)) (PreH20 : (total <= 56000)) (PreH21 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l_2)))) (PreH22 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l_2)))) (PreH23 : (HuffmanProgress weights_l work_l_2 active total)) (PreH24 : (HuffmanMinScan work_l_2 i first)) ,
  (HuffmanMinScan work_l_2 (i + 1) i)

noncomputable def huffman_cost_entail_wit_6_2 : Prop :=
  (
forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l_2 : (List Int)) (PreH1 : ((Znth i work_l_2 (0 : Int)) >= (Znth first work_l_2 (0 : Int)))) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i < n_pre)) (PreH4 : (i < active)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (work_l_2)) = n_pre)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH10 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH11 : (2 <= active)) (PreH12 : (active <= n_pre)) (PreH13 : (1 <= i)) (PreH14 : (i <= active)) (PreH15 : (i <= n_pre)) (PreH16 : ((0 : Int) <= first)) (PreH17 : (first < i)) (PreH18 : (first < n_pre)) (PreH19 : ((0 : Int) <= total)) (PreH20 : (total <= 56000)) (PreH21 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l_2)))) (PreH22 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l_2)))) (PreH23 : (HuffmanProgress weights_l work_l_2 active total)) (PreH24 : (HuffmanMinScan work_l_2 i first)) ,
  (intArray.full ( &( "work" ) ) n_pre work_l_2)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  EX work_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (work_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) weights_l) ” &&
  “ (2 <= active) ” &&
  “ (active <= n_pre) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= active) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= first) ” &&
  “ (first < (i + 1)) ” &&
  “ (first < n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 56000) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l))) ” &&
  “ (HuffmanProgress weights_l work_l active total) ” &&
  “ (HuffmanMinScan work_l (i + 1) first) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full ( &( "work" ) ) n_pre work_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
) \/
(
forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l_2 : (List Int)) (PreH1 : ((Znth i work_l_2 (0 : Int)) >= (Znth first work_l_2 (0 : Int)))) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i < n_pre)) (PreH4 : (i < active)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (work_l_2)) = n_pre)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH10 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH11 : (2 <= active)) (PreH12 : (active <= n_pre)) (PreH13 : (1 <= i)) (PreH14 : (i <= active)) (PreH15 : (i <= n_pre)) (PreH16 : ((0 : Int) <= first)) (PreH17 : (first < i)) (PreH18 : (first < n_pre)) (PreH19 : ((0 : Int) <= total)) (PreH20 : (total <= 56000)) (PreH21 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l_2)))) (PreH22 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l_2)))) (PreH23 : (HuffmanProgress weights_l work_l_2 active total)) (PreH24 : (HuffmanMinScan work_l_2 i first)) ,
  TT && emp 
|--
  “ (HuffmanMinScan work_l_2 (i + 1) first) ”
  &&  emp
)

noncomputable def huffman_cost_entail_wit_6_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l_2 : (List Int)) (PreH1 : ((Znth i work_l_2 (0 : Int)) >= (Znth first work_l_2 (0 : Int)))) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i < n_pre)) (PreH4 : (i < active)) (PreH5 : (1 <= n_pre)) (PreH6 : (n_pre <= 8)) (PreH7 : ((Zlength (weights_l)) = n_pre)) (PreH8 : ((Zlength (work_l_2)) = n_pre)) (PreH9 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH10 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH11 : (2 <= active)) (PreH12 : (active <= n_pre)) (PreH13 : (1 <= i)) (PreH14 : (i <= active)) (PreH15 : (i <= n_pre)) (PreH16 : ((0 : Int) <= first)) (PreH17 : (first < i)) (PreH18 : (first < n_pre)) (PreH19 : ((0 : Int) <= total)) (PreH20 : (total <= 56000)) (PreH21 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l_2)))) (PreH22 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l_2)))) (PreH23 : (HuffmanProgress weights_l work_l_2 active total)) (PreH24 : (HuffmanMinScan work_l_2 i first)) ,
  (HuffmanMinScan work_l_2 (i + 1) first)

noncomputable def huffman_cost_entail_wit_7 : Prop :=
  (
forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (2 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < i)) (PreH15 : (first < n_pre)) (PreH16 : ((0 : Int) <= total)) (PreH17 : (total <= 56000)) (PreH18 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l)))) (PreH19 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l)))) (PreH20 : (HuffmanProgress weights_l work_l active total)) (PreH21 : (HuffmanMinScan work_l i first)) ,
  (intArray.full ( &( "work" ) ) n_pre (replace_Znth (first) ((Znth (active - 1) work_l (0 : Int))) (work_l)))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  EX work_l_2 : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (work_l_2)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) weights_l) ” &&
  “ (1 <= (active - 1)) ” &&
  “ ((active - 1) < n_pre) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= (active - 1)) ” &&
  “ (1 < n_pre) ” &&
  “ ((0 : Int) <= first) ” &&
  “ (first < n_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) < 1) ” &&
  “ ((0 : Int) < n_pre) ” &&
  “ (1 <= (Znth first work_l (0 : Int))) ” &&
  “ ((Znth first work_l (0 : Int)) <= 8000) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 56000) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) ((active - 1)) (work_l_2))) ” &&
  “ (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) ((active - 1)) (work_l_2))) ” &&
  “ (HuffmanFirstHeld weights_l work_l_2 (active - 1) (Znth first work_l (0 : Int)) total) ” &&
  “ (HuffmanMinScan work_l_2 1 (0 : Int)) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full ( &( "work" ) ) n_pre work_l_2)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
) \/
(
forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (2 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < i)) (PreH15 : (first < n_pre)) (PreH16 : ((0 : Int) <= total)) (PreH17 : (total <= 56000)) (PreH18 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l)))) (PreH19 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l)))) (PreH20 : (HuffmanProgress weights_l work_l active total)) (PreH21 : (HuffmanMinScan work_l i first)) ,
  TT && emp 
|--
  “ (HuffmanMinScan (replace_Znth (first) ((Znth (active - 1) work_l (0 : Int))) (work_l)) 1 (0 : Int)) ” &&
  “ (HuffmanFirstHeld weights_l (replace_Znth (first) ((Znth (active - 1) work_l (0 : Int))) (work_l)) (active - 1) (Znth first work_l (0 : Int)) total) ” &&
  “ (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) ((active - 1)) ((replace_Znth (first) ((Znth (active - 1) work_l (0 : Int))) (work_l))))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) ((active - 1)) ((replace_Znth (first) ((Znth (active - 1) work_l (0 : Int))) (work_l))))) ” &&
  “ ((Znth first work_l (0 : Int)) <= 8000) ” &&
  “ (1 <= (Znth first work_l (0 : Int))) ” &&
  “ ((Zlength ((replace_Znth (first) ((Znth (active - 1) work_l (0 : Int))) (work_l)))) = n_pre) ”
  &&  emp
)

noncomputable def huffman_cost_entail_wit_7_split_goal_1 : Prop :=
  forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (2 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < i)) (PreH15 : (first < n_pre)) (PreH16 : ((0 : Int) <= total)) (PreH17 : (total <= 56000)) (PreH18 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l)))) (PreH19 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l)))) (PreH20 : (HuffmanProgress weights_l work_l active total)) (PreH21 : (HuffmanMinScan work_l i first)) ,
  (HuffmanMinScan (replace_Znth (first) ((Znth (active - 1) work_l (0 : Int))) (work_l)) 1 (0 : Int))

noncomputable def huffman_cost_entail_wit_7_split_goal_2 : Prop :=
  forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (2 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < i)) (PreH15 : (first < n_pre)) (PreH16 : ((0 : Int) <= total)) (PreH17 : (total <= 56000)) (PreH18 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l)))) (PreH19 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l)))) (PreH20 : (HuffmanProgress weights_l work_l active total)) (PreH21 : (HuffmanMinScan work_l i first)) ,
  (HuffmanFirstHeld weights_l (replace_Znth (first) ((Znth (active - 1) work_l (0 : Int))) (work_l)) (active - 1) (Znth first work_l (0 : Int)) total)

noncomputable def huffman_cost_entail_wit_7_split_goal_3 : Prop :=
  forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (2 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < i)) (PreH15 : (first < n_pre)) (PreH16 : ((0 : Int) <= total)) (PreH17 : (total <= 56000)) (PreH18 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l)))) (PreH19 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l)))) (PreH20 : (HuffmanProgress weights_l work_l active total)) (PreH21 : (HuffmanMinScan work_l i first)) ,
  (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) ((active - 1)) ((replace_Znth (first) ((Znth (active - 1) work_l (0 : Int))) (work_l)))))

noncomputable def huffman_cost_entail_wit_7_split_goal_4 : Prop :=
  forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (2 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < i)) (PreH15 : (first < n_pre)) (PreH16 : ((0 : Int) <= total)) (PreH17 : (total <= 56000)) (PreH18 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l)))) (PreH19 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l)))) (PreH20 : (HuffmanProgress weights_l work_l active total)) (PreH21 : (HuffmanMinScan work_l i first)) ,
  (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) ((active - 1)) ((replace_Znth (first) ((Znth (active - 1) work_l (0 : Int))) (work_l)))))

noncomputable def huffman_cost_entail_wit_7_split_goal_5 : Prop :=
  forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (2 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < i)) (PreH15 : (first < n_pre)) (PreH16 : ((0 : Int) <= total)) (PreH17 : (total <= 56000)) (PreH18 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l)))) (PreH19 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l)))) (PreH20 : (HuffmanProgress weights_l work_l active total)) (PreH21 : (HuffmanMinScan work_l i first)) ,
  ((Znth first work_l (0 : Int)) <= 8000)

noncomputable def huffman_cost_entail_wit_7_split_goal_6 : Prop :=
  forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (2 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < i)) (PreH15 : (first < n_pre)) (PreH16 : ((0 : Int) <= total)) (PreH17 : (total <= 56000)) (PreH18 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l)))) (PreH19 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l)))) (PreH20 : (HuffmanProgress weights_l work_l active total)) (PreH21 : (HuffmanMinScan work_l i first)) ,
  (1 <= (Znth first work_l (0 : Int)))

noncomputable def huffman_cost_entail_wit_7_split_goal_7 : Prop :=
  forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (2 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < i)) (PreH15 : (first < n_pre)) (PreH16 : ((0 : Int) <= total)) (PreH17 : (total <= 56000)) (PreH18 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l)))) (PreH19 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l)))) (PreH20 : (HuffmanProgress weights_l work_l active total)) (PreH21 : (HuffmanMinScan work_l i first)) ,
  ((Zlength ((replace_Znth (first) ((Znth (active - 1) work_l (0 : Int))) (work_l)))) = n_pre)

noncomputable def huffman_cost_entail_wit_8_1 : Prop :=
  (
forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l_2 : (List Int)) (PreH1 : ((Znth i work_l_2 (0 : Int)) < (Znth second work_l_2 (0 : Int)))) (PreH2 : (i < active)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (work_l_2)) = n_pre)) (PreH7 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH8 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH9 : (1 <= active)) (PreH10 : (active < n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= first)) (PreH15 : (first < n_pre)) (PreH16 : ((0 : Int) <= second)) (PreH17 : (second < i)) (PreH18 : (second < n_pre)) (PreH19 : (1 <= x)) (PreH20 : (x <= 8000)) (PreH21 : ((0 : Int) <= total)) (PreH22 : (total <= 56000)) (PreH23 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l_2)))) (PreH24 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l_2)))) (PreH25 : (HuffmanFirstHeld weights_l work_l_2 active x total)) (PreH26 : (HuffmanMinScan work_l_2 i second)) ,
  (intArray.full ( &( "work" ) ) n_pre work_l_2)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  EX work_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (work_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) weights_l) ” &&
  “ (1 <= active) ” &&
  “ (active < n_pre) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= active) ” &&
  “ ((i + 1) < n_pre) ” &&
  “ ((0 : Int) <= first) ” &&
  “ (first < n_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < (i + 1)) ” &&
  “ (i < n_pre) ” &&
  “ (1 <= x) ” &&
  “ (x <= 8000) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 56000) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l))) ” &&
  “ (HuffmanFirstHeld weights_l work_l active x total) ” &&
  “ (HuffmanMinScan work_l (i + 1) i) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full ( &( "work" ) ) n_pre work_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
) \/
(
forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l_2 : (List Int)) (PreH1 : ((Znth i work_l_2 (0 : Int)) < (Znth second work_l_2 (0 : Int)))) (PreH2 : (i < active)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (work_l_2)) = n_pre)) (PreH7 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH8 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH9 : (1 <= active)) (PreH10 : (active < n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= first)) (PreH15 : (first < n_pre)) (PreH16 : ((0 : Int) <= second)) (PreH17 : (second < i)) (PreH18 : (second < n_pre)) (PreH19 : (1 <= x)) (PreH20 : (x <= 8000)) (PreH21 : ((0 : Int) <= total)) (PreH22 : (total <= 56000)) (PreH23 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l_2)))) (PreH24 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l_2)))) (PreH25 : (HuffmanFirstHeld weights_l work_l_2 active x total)) (PreH26 : (HuffmanMinScan work_l_2 i second)) ,
  TT && emp 
|--
  “ (HuffmanMinScan work_l_2 (i + 1) i) ”
  &&  emp
)

noncomputable def huffman_cost_entail_wit_8_1_split_goal_1 : Prop :=
  forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l_2 : (List Int)) (PreH1 : ((Znth i work_l_2 (0 : Int)) < (Znth second work_l_2 (0 : Int)))) (PreH2 : (i < active)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (work_l_2)) = n_pre)) (PreH7 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH8 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH9 : (1 <= active)) (PreH10 : (active < n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= first)) (PreH15 : (first < n_pre)) (PreH16 : ((0 : Int) <= second)) (PreH17 : (second < i)) (PreH18 : (second < n_pre)) (PreH19 : (1 <= x)) (PreH20 : (x <= 8000)) (PreH21 : ((0 : Int) <= total)) (PreH22 : (total <= 56000)) (PreH23 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l_2)))) (PreH24 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l_2)))) (PreH25 : (HuffmanFirstHeld weights_l work_l_2 active x total)) (PreH26 : (HuffmanMinScan work_l_2 i second)) ,
  (HuffmanMinScan work_l_2 (i + 1) i)

noncomputable def huffman_cost_entail_wit_8_2 : Prop :=
  (
forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l_2 : (List Int)) (PreH1 : ((Znth i work_l_2 (0 : Int)) >= (Znth second work_l_2 (0 : Int)))) (PreH2 : (i < active)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (work_l_2)) = n_pre)) (PreH7 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH8 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH9 : (1 <= active)) (PreH10 : (active < n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= first)) (PreH15 : (first < n_pre)) (PreH16 : ((0 : Int) <= second)) (PreH17 : (second < i)) (PreH18 : (second < n_pre)) (PreH19 : (1 <= x)) (PreH20 : (x <= 8000)) (PreH21 : ((0 : Int) <= total)) (PreH22 : (total <= 56000)) (PreH23 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l_2)))) (PreH24 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l_2)))) (PreH25 : (HuffmanFirstHeld weights_l work_l_2 active x total)) (PreH26 : (HuffmanMinScan work_l_2 i second)) ,
  (intArray.full ( &( "work" ) ) n_pre work_l_2)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  EX work_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (work_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) weights_l) ” &&
  “ (1 <= active) ” &&
  “ (active < n_pre) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= active) ” &&
  “ ((i + 1) < n_pre) ” &&
  “ ((0 : Int) <= first) ” &&
  “ (first < n_pre) ” &&
  “ ((0 : Int) <= second) ” &&
  “ (second < (i + 1)) ” &&
  “ (second < n_pre) ” &&
  “ (1 <= x) ” &&
  “ (x <= 8000) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 56000) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l))) ” &&
  “ (HuffmanFirstHeld weights_l work_l active x total) ” &&
  “ (HuffmanMinScan work_l (i + 1) second) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full ( &( "work" ) ) n_pre work_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
) \/
(
forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l_2 : (List Int)) (PreH1 : ((Znth i work_l_2 (0 : Int)) >= (Znth second work_l_2 (0 : Int)))) (PreH2 : (i < active)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (work_l_2)) = n_pre)) (PreH7 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH8 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH9 : (1 <= active)) (PreH10 : (active < n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= first)) (PreH15 : (first < n_pre)) (PreH16 : ((0 : Int) <= second)) (PreH17 : (second < i)) (PreH18 : (second < n_pre)) (PreH19 : (1 <= x)) (PreH20 : (x <= 8000)) (PreH21 : ((0 : Int) <= total)) (PreH22 : (total <= 56000)) (PreH23 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l_2)))) (PreH24 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l_2)))) (PreH25 : (HuffmanFirstHeld weights_l work_l_2 active x total)) (PreH26 : (HuffmanMinScan work_l_2 i second)) ,
  TT && emp 
|--
  “ (HuffmanMinScan work_l_2 (i + 1) second) ”
  &&  emp
)

noncomputable def huffman_cost_entail_wit_8_2_split_goal_1 : Prop :=
  forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l_2 : (List Int)) (PreH1 : ((Znth i work_l_2 (0 : Int)) >= (Znth second work_l_2 (0 : Int)))) (PreH2 : (i < active)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 8)) (PreH5 : ((Zlength (weights_l)) = n_pre)) (PreH6 : ((Zlength (work_l_2)) = n_pre)) (PreH7 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH8 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH9 : (1 <= active)) (PreH10 : (active < n_pre)) (PreH11 : (1 <= i)) (PreH12 : (i <= active)) (PreH13 : (i < n_pre)) (PreH14 : ((0 : Int) <= first)) (PreH15 : (first < n_pre)) (PreH16 : ((0 : Int) <= second)) (PreH17 : (second < i)) (PreH18 : (second < n_pre)) (PreH19 : (1 <= x)) (PreH20 : (x <= 8000)) (PreH21 : ((0 : Int) <= total)) (PreH22 : (total <= 56000)) (PreH23 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l_2)))) (PreH24 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l_2)))) (PreH25 : (HuffmanFirstHeld weights_l work_l_2 active x total)) (PreH26 : (HuffmanMinScan work_l_2 i second)) ,
  (HuffmanMinScan work_l_2 (i + 1) second)

noncomputable def huffman_cost_entail_wit_9 : Prop :=
  (
forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l_2 : (List Int)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l_2)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < n_pre)) (PreH15 : ((0 : Int) <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : ((0 : Int) <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l_2)))) (PreH23 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l_2)))) (PreH24 : (HuffmanFirstHeld weights_l work_l_2 active x total)) (PreH25 : (HuffmanMinScan work_l_2 i second)) ,
  (intArray.full ( &( "work" ) ) n_pre (replace_Znth ((active - 1)) ((x + (Znth second work_l_2 (0 : Int)))) ((replace_Znth (second) ((Znth (active - 1) work_l_2 (0 : Int))) (work_l_2)))))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  EX work_l : (List Int),
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (work_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) weights_l) ” &&
  “ (1 <= ((active - 1) + 1)) ” &&
  “ (((active - 1) + 1) <= n_pre) ” &&
  “ ((0 : Int) <= (total + (x + (Znth second work_l_2 (0 : Int))))) ” &&
  “ ((total + (x + (Znth second work_l_2 (0 : Int)))) <= 56000) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (((active - 1) + 1)) (work_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (((active - 1) + 1)) (work_l))) ” &&
  “ (HuffmanProgress weights_l work_l ((active - 1) + 1) (total + (x + (Znth second work_l_2 (0 : Int))))) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full ( &( "work" ) ) n_pre work_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
) \/
(
forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l_2 : (List Int)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l_2)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < n_pre)) (PreH15 : ((0 : Int) <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : ((0 : Int) <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l_2)))) (PreH23 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l_2)))) (PreH24 : (HuffmanFirstHeld weights_l work_l_2 active x total)) (PreH25 : (HuffmanMinScan work_l_2 i second)) ,
  TT && emp 
|--
  “ (HuffmanProgress weights_l (replace_Znth ((active - 1)) ((x + (Znth second work_l_2 (0 : Int)))) ((replace_Znth (second) ((Znth (active - 1) work_l_2 (0 : Int))) (work_l_2)))) ((active - 1) + 1) (total + (x + (Znth second work_l_2 (0 : Int))))) ” &&
  “ (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (((active - 1) + 1)) ((replace_Znth ((active - 1)) ((x + (Znth second work_l_2 (0 : Int)))) ((replace_Znth (second) ((Znth (active - 1) work_l_2 (0 : Int))) (work_l_2))))))) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (((active - 1) + 1)) ((replace_Znth ((active - 1)) ((x + (Znth second work_l_2 (0 : Int)))) ((replace_Znth (second) ((Znth (active - 1) work_l_2 (0 : Int))) (work_l_2))))))) ” &&
  “ ((total + (x + (Znth second work_l_2 (0 : Int)))) <= 56000) ” &&
  “ ((0 : Int) <= (total + (x + (Znth second work_l_2 (0 : Int))))) ” &&
  “ ((Zlength ((replace_Znth ((active - 1)) ((x + (Znth second work_l_2 (0 : Int)))) ((replace_Znth (second) ((Znth (active - 1) work_l_2 (0 : Int))) (work_l_2)))))) = n_pre) ”
  &&  emp
)

noncomputable def huffman_cost_entail_wit_9_split_goal_1 : Prop :=
  forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l_2 : (List Int)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l_2)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < n_pre)) (PreH15 : ((0 : Int) <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : ((0 : Int) <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l_2)))) (PreH23 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l_2)))) (PreH24 : (HuffmanFirstHeld weights_l work_l_2 active x total)) (PreH25 : (HuffmanMinScan work_l_2 i second)) ,
  (HuffmanProgress weights_l (replace_Znth ((active - 1)) ((x + (Znth second work_l_2 (0 : Int)))) ((replace_Znth (second) ((Znth (active - 1) work_l_2 (0 : Int))) (work_l_2)))) ((active - 1) + 1) (total + (x + (Znth second work_l_2 (0 : Int)))))

noncomputable def huffman_cost_entail_wit_9_split_goal_2 : Prop :=
  forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l_2 : (List Int)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l_2)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < n_pre)) (PreH15 : ((0 : Int) <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : ((0 : Int) <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l_2)))) (PreH23 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l_2)))) (PreH24 : (HuffmanFirstHeld weights_l work_l_2 active x total)) (PreH25 : (HuffmanMinScan work_l_2 i second)) ,
  (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (((active - 1) + 1)) ((replace_Znth ((active - 1)) ((x + (Znth second work_l_2 (0 : Int)))) ((replace_Znth (second) ((Znth (active - 1) work_l_2 (0 : Int))) (work_l_2)))))))

noncomputable def huffman_cost_entail_wit_9_split_goal_3 : Prop :=
  forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l_2 : (List Int)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l_2)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < n_pre)) (PreH15 : ((0 : Int) <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : ((0 : Int) <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l_2)))) (PreH23 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l_2)))) (PreH24 : (HuffmanFirstHeld weights_l work_l_2 active x total)) (PreH25 : (HuffmanMinScan work_l_2 i second)) ,
  (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (((active - 1) + 1)) ((replace_Znth ((active - 1)) ((x + (Znth second work_l_2 (0 : Int)))) ((replace_Znth (second) ((Znth (active - 1) work_l_2 (0 : Int))) (work_l_2)))))))

noncomputable def huffman_cost_entail_wit_9_split_goal_4 : Prop :=
  forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l_2 : (List Int)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l_2)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < n_pre)) (PreH15 : ((0 : Int) <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : ((0 : Int) <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l_2)))) (PreH23 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l_2)))) (PreH24 : (HuffmanFirstHeld weights_l work_l_2 active x total)) (PreH25 : (HuffmanMinScan work_l_2 i second)) ,
  ((total + (x + (Znth second work_l_2 (0 : Int)))) <= 56000)

noncomputable def huffman_cost_entail_wit_9_split_goal_5 : Prop :=
  forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l_2 : (List Int)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l_2)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < n_pre)) (PreH15 : ((0 : Int) <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : ((0 : Int) <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l_2)))) (PreH23 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l_2)))) (PreH24 : (HuffmanFirstHeld weights_l work_l_2 active x total)) (PreH25 : (HuffmanMinScan work_l_2 i second)) ,
  ((0 : Int) <= (total + (x + (Znth second work_l_2 (0 : Int)))))

noncomputable def huffman_cost_entail_wit_9_split_goal_6 : Prop :=
  forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l_2 : (List Int)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l_2)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < n_pre)) (PreH15 : ((0 : Int) <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : ((0 : Int) <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l_2)))) (PreH23 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l_2)))) (PreH24 : (HuffmanFirstHeld weights_l work_l_2 active x total)) (PreH25 : (HuffmanMinScan work_l_2 i second)) ,
  ((Zlength ((replace_Znth ((active - 1)) ((x + (Znth second work_l_2 (0 : Int)))) ((replace_Znth (second) ((Znth (active - 1) work_l_2 (0 : Int))) (work_l_2)))))) = n_pre)

noncomputable def huffman_cost_entail_wit_10 : Prop :=
  (
forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (active : Int) (work_l : (List Int)) (PreH1 : (active <= 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (1 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : ((0 : Int) <= total)) (PreH11 : (total <= 56000)) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l)))) (PreH13 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l)))) (PreH14 : (HuffmanProgress weights_l work_l active total)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full ( &( "work" ) ) n_pre work_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  “ (active = 1) ” &&
  “ (HuffmanOptimalCost weights_l total) ”
  &&  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_full ( &( "work" ) ) 8)
) \/
(
forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (active : Int) (work_l : (List Int)) (PreH1 : (active <= 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (1 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : ((0 : Int) <= total)) (PreH11 : (total <= 56000)) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l)))) (PreH13 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l)))) (PreH14 : (HuffmanProgress weights_l work_l active total)) ,
  (intArray.full ( &( "work" ) ) n_pre work_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  “ (HuffmanOptimalCost weights_l total) ”
  &&  (intArray.undef_full ( &( "work" ) ) 8)
)

noncomputable def huffman_cost_entail_wit_10_split_goal_1 : Prop :=
  forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (active : Int) (work_l : (List Int)) (PreH1 : (active <= 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (1 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : ((0 : Int) <= total)) (PreH11 : (total <= 56000)) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l)))) (PreH13 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l)))) (PreH14 : (HuffmanProgress weights_l work_l active total)) ,
  (intArray.full ( &( "work" ) ) n_pre work_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  “ (HuffmanOptimalCost weights_l total) ”

noncomputable def huffman_cost_entail_wit_10_split_goal_spatial : Prop :=
  forall (n_pre : Int) (weights_l : (List Int)) (total : Int) (active : Int) (work_l : (List Int)) (PreH1 : (active <= 1)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (1 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : ((0 : Int) <= total)) (PreH11 : (total <= 56000)) (PreH12 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l)))) (PreH13 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l)))) (PreH14 : (HuffmanProgress weights_l work_l active total)) ,
  (intArray.full ( &( "work" ) ) n_pre work_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  (intArray.undef_full ( &( "work" ) ) 8)

noncomputable def huffman_cost_return_wit_1 : Prop :=
  forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (active : Int) (total : Int) (PreH1 : (active = 1)) (PreH2 : (HuffmanOptimalCost weights_l total)) ,
  (intArray.full weights_pre n_pre weights_l)
|--
  “ (HuffmanOptimalCost weights_l total) ”
  &&  (intArray.full weights_pre n_pre weights_l)

noncomputable def huffman_cost_partial_solve_wit_1 : Prop :=
  forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (i : Int) (copied : (List Int)) (remaining : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH6 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH7 : (weights_l = (copied ++ remaining))) (PreH8 : ((Zlength (copied)) = i)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.seg ( &( "work" ) ) (0 : Int) i copied)
  ** (intArray.undef_seg ( &( "work" ) ) i n_pre)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  “ (i < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) weights_l) ” &&
  “ (weights_l = (copied ++ remaining)) ” &&
  “ ((Zlength (copied)) = i) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ”
  &&  (((weights_pre + (i * sizeof(INT)))) # Int |-> ((Znth i weights_l (0 : Int))))
  ** (intArray.missing_i weights_pre i (0 : Int) n_pre weights_l)
  ** (intArray.seg ( &( "work" ) ) (0 : Int) i copied)
  ** (intArray.undef_seg ( &( "work" ) ) i n_pre)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)

noncomputable def huffman_cost_partial_solve_wit_2 : Prop :=
  forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (i : Int) (copied : (List Int)) (remaining : (List Int)) (PreH1 : (i < n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH6 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH7 : (weights_l = (copied ++ remaining))) (PreH8 : ((Zlength (copied)) = i)) (PreH9 : ((0 : Int) <= i)) (PreH10 : (i <= n_pre)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.seg ( &( "work" ) ) (0 : Int) i copied)
  ** (intArray.undef_seg ( &( "work" ) ) i n_pre)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  “ (i < n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) weights_l) ” &&
  “ (weights_l = (copied ++ remaining)) ” &&
  “ ((Zlength (copied)) = i) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ”
  &&  (((( &( "work" ) ) + (i * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg ( &( "work" ) ) (i + 1) n_pre)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.seg ( &( "work" ) ) (0 : Int) i copied)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)

noncomputable def huffman_cost_partial_solve_wit_3 : Prop :=
  forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : ((0 : Int) <= i)) (PreH2 : (i < n_pre)) (PreH3 : (i < active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH9 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH10 : (2 <= active)) (PreH11 : (active <= n_pre)) (PreH12 : (1 <= i)) (PreH13 : (i <= active)) (PreH14 : (i <= n_pre)) (PreH15 : ((0 : Int) <= first)) (PreH16 : (first < i)) (PreH17 : (first < n_pre)) (PreH18 : ((0 : Int) <= total)) (PreH19 : (total <= 56000)) (PreH20 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l)))) (PreH21 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l)))) (PreH22 : (HuffmanProgress weights_l work_l active total)) (PreH23 : (HuffmanMinScan work_l i first)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full ( &( "work" ) ) n_pre work_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (i < active) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (work_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) weights_l) ” &&
  “ (2 <= active) ” &&
  “ (active <= n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= active) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= first) ” &&
  “ (first < i) ” &&
  “ (first < n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 56000) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l))) ” &&
  “ (HuffmanProgress weights_l work_l active total) ” &&
  “ (HuffmanMinScan work_l i first) ”
  &&  (((( &( "work" ) ) + (i * sizeof(INT)))) # Int |-> ((Znth i work_l (0 : Int))))
  ** (intArray.missing_i ( &( "work" ) ) i (0 : Int) n_pre work_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)

noncomputable def huffman_cost_partial_solve_wit_4 : Prop :=
  forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : ((0 : Int) <= i)) (PreH2 : (i < n_pre)) (PreH3 : (i < active)) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 8)) (PreH6 : ((Zlength (weights_l)) = n_pre)) (PreH7 : ((Zlength (work_l)) = n_pre)) (PreH8 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH9 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH10 : (2 <= active)) (PreH11 : (active <= n_pre)) (PreH12 : (1 <= i)) (PreH13 : (i <= active)) (PreH14 : (i <= n_pre)) (PreH15 : ((0 : Int) <= first)) (PreH16 : (first < i)) (PreH17 : (first < n_pre)) (PreH18 : ((0 : Int) <= total)) (PreH19 : (total <= 56000)) (PreH20 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l)))) (PreH21 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l)))) (PreH22 : (HuffmanProgress weights_l work_l active total)) (PreH23 : (HuffmanMinScan work_l i first)) ,
  (intArray.full ( &( "work" ) ) n_pre work_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ (i < active) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (work_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) weights_l) ” &&
  “ (2 <= active) ” &&
  “ (active <= n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= active) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= first) ” &&
  “ (first < i) ” &&
  “ (first < n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 56000) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l))) ” &&
  “ (HuffmanProgress weights_l work_l active total) ” &&
  “ (HuffmanMinScan work_l i first) ”
  &&  (((( &( "work" ) ) + (first * sizeof(INT)))) # Int |-> ((Znth first work_l (0 : Int))))
  ** (intArray.missing_i ( &( "work" ) ) first (0 : Int) n_pre work_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)

noncomputable def huffman_cost_partial_solve_wit_5 : Prop :=
  forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (2 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < i)) (PreH15 : (first < n_pre)) (PreH16 : ((0 : Int) <= total)) (PreH17 : (total <= 56000)) (PreH18 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l)))) (PreH19 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l)))) (PreH20 : (HuffmanProgress weights_l work_l active total)) (PreH21 : (HuffmanMinScan work_l i first)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full ( &( "work" ) ) n_pre work_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  “ (i >= active) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (work_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) weights_l) ” &&
  “ (2 <= active) ” &&
  “ (active <= n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= active) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= first) ” &&
  “ (first < i) ” &&
  “ (first < n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 56000) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l))) ” &&
  “ (HuffmanProgress weights_l work_l active total) ” &&
  “ (HuffmanMinScan work_l i first) ”
  &&  (((( &( "work" ) ) + (first * sizeof(INT)))) # Int |-> ((Znth first work_l (0 : Int))))
  ** (intArray.missing_i ( &( "work" ) ) first (0 : Int) n_pre work_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)

noncomputable def huffman_cost_partial_solve_wit_6 : Prop :=
  forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (2 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < i)) (PreH15 : (first < n_pre)) (PreH16 : ((0 : Int) <= total)) (PreH17 : (total <= 56000)) (PreH18 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l)))) (PreH19 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l)))) (PreH20 : (HuffmanProgress weights_l work_l active total)) (PreH21 : (HuffmanMinScan work_l i first)) ,
  (intArray.full ( &( "work" ) ) n_pre work_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  “ (i >= active) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (work_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) weights_l) ” &&
  “ (2 <= active) ” &&
  “ (active <= n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= active) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= first) ” &&
  “ (first < i) ” &&
  “ (first < n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 56000) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l))) ” &&
  “ (HuffmanProgress weights_l work_l active total) ” &&
  “ (HuffmanMinScan work_l i first) ”
  &&  (((( &( "work" ) ) + ((active - 1) * sizeof(INT)))) # Int |-> ((Znth (active - 1) work_l (0 : Int))))
  ** (intArray.missing_i ( &( "work" ) ) (active - 1) (0 : Int) n_pre work_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)

noncomputable def huffman_cost_partial_solve_wit_7 : Prop :=
  forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (2 <= active)) (PreH9 : (active <= n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i <= n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < i)) (PreH15 : (first < n_pre)) (PreH16 : ((0 : Int) <= total)) (PreH17 : (total <= 56000)) (PreH18 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l)))) (PreH19 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l)))) (PreH20 : (HuffmanProgress weights_l work_l active total)) (PreH21 : (HuffmanMinScan work_l i first)) ,
  (intArray.full ( &( "work" ) ) n_pre work_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  “ (i >= active) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (work_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) weights_l) ” &&
  “ (2 <= active) ” &&
  “ (active <= n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= active) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= first) ” &&
  “ (first < i) ” &&
  “ (first < n_pre) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 56000) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l))) ” &&
  “ (HuffmanProgress weights_l work_l active total) ” &&
  “ (HuffmanMinScan work_l i first) ”
  &&  (((( &( "work" ) ) + (first * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i ( &( "work" ) ) first (0 : Int) n_pre work_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)

noncomputable def huffman_cost_partial_solve_wit_8 : Prop :=
  forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : (i < active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < n_pre)) (PreH15 : ((0 : Int) <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : ((0 : Int) <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l)))) (PreH23 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l)))) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total)) (PreH25 : (HuffmanMinScan work_l i second)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full ( &( "work" ) ) n_pre work_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  “ (i < active) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (work_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) weights_l) ” &&
  “ (1 <= active) ” &&
  “ (active < n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= active) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= first) ” &&
  “ (first < n_pre) ” &&
  “ ((0 : Int) <= second) ” &&
  “ (second < i) ” &&
  “ (second < n_pre) ” &&
  “ (1 <= x) ” &&
  “ (x <= 8000) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 56000) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l))) ” &&
  “ (HuffmanFirstHeld weights_l work_l active x total) ” &&
  “ (HuffmanMinScan work_l i second) ”
  &&  (((( &( "work" ) ) + (i * sizeof(INT)))) # Int |-> ((Znth i work_l (0 : Int))))
  ** (intArray.missing_i ( &( "work" ) ) i (0 : Int) n_pre work_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)

noncomputable def huffman_cost_partial_solve_wit_9 : Prop :=
  forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : (i < active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < n_pre)) (PreH15 : ((0 : Int) <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : ((0 : Int) <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l)))) (PreH23 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l)))) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total)) (PreH25 : (HuffmanMinScan work_l i second)) ,
  (intArray.full ( &( "work" ) ) n_pre work_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  “ (i < active) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (work_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) weights_l) ” &&
  “ (1 <= active) ” &&
  “ (active < n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= active) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= first) ” &&
  “ (first < n_pre) ” &&
  “ ((0 : Int) <= second) ” &&
  “ (second < i) ” &&
  “ (second < n_pre) ” &&
  “ (1 <= x) ” &&
  “ (x <= 8000) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 56000) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l))) ” &&
  “ (HuffmanFirstHeld weights_l work_l active x total) ” &&
  “ (HuffmanMinScan work_l i second) ”
  &&  (((( &( "work" ) ) + (second * sizeof(INT)))) # Int |-> ((Znth second work_l (0 : Int))))
  ** (intArray.missing_i ( &( "work" ) ) second (0 : Int) n_pre work_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)

noncomputable def huffman_cost_partial_solve_wit_10 : Prop :=
  forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < n_pre)) (PreH15 : ((0 : Int) <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : ((0 : Int) <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l)))) (PreH23 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l)))) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total)) (PreH25 : (HuffmanMinScan work_l i second)) ,
  (intArray.full weights_pre n_pre weights_l)
  ** (intArray.full ( &( "work" ) ) n_pre work_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  “ (i >= active) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (work_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) weights_l) ” &&
  “ (1 <= active) ” &&
  “ (active < n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= active) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= first) ” &&
  “ (first < n_pre) ” &&
  “ ((0 : Int) <= second) ” &&
  “ (second < i) ” &&
  “ (second < n_pre) ” &&
  “ (1 <= x) ” &&
  “ (x <= 8000) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 56000) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l))) ” &&
  “ (HuffmanFirstHeld weights_l work_l active x total) ” &&
  “ (HuffmanMinScan work_l i second) ”
  &&  (((( &( "work" ) ) + (second * sizeof(INT)))) # Int |-> ((Znth second work_l (0 : Int))))
  ** (intArray.missing_i ( &( "work" ) ) second (0 : Int) n_pre work_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)

noncomputable def huffman_cost_partial_solve_wit_11 : Prop :=
  forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < n_pre)) (PreH15 : ((0 : Int) <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : ((0 : Int) <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l)))) (PreH23 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l)))) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total)) (PreH25 : (HuffmanMinScan work_l i second)) ,
  (intArray.full ( &( "work" ) ) n_pre work_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  “ (i >= active) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (work_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) weights_l) ” &&
  “ (1 <= active) ” &&
  “ (active < n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= active) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= first) ” &&
  “ (first < n_pre) ” &&
  “ ((0 : Int) <= second) ” &&
  “ (second < i) ” &&
  “ (second < n_pre) ” &&
  “ (1 <= x) ” &&
  “ (x <= 8000) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 56000) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l))) ” &&
  “ (HuffmanFirstHeld weights_l work_l active x total) ” &&
  “ (HuffmanMinScan work_l i second) ”
  &&  (((( &( "work" ) ) + ((active - 1) * sizeof(INT)))) # Int |-> ((Znth (active - 1) work_l (0 : Int))))
  ** (intArray.missing_i ( &( "work" ) ) (active - 1) (0 : Int) n_pre work_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)

noncomputable def huffman_cost_partial_solve_wit_12 : Prop :=
  forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < n_pre)) (PreH15 : ((0 : Int) <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : ((0 : Int) <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l)))) (PreH23 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l)))) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total)) (PreH25 : (HuffmanMinScan work_l i second)) ,
  (intArray.full ( &( "work" ) ) n_pre work_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  “ (i >= active) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (work_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) weights_l) ” &&
  “ (1 <= active) ” &&
  “ (active < n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= active) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= first) ” &&
  “ (first < n_pre) ” &&
  “ ((0 : Int) <= second) ” &&
  “ (second < i) ” &&
  “ (second < n_pre) ” &&
  “ (1 <= x) ” &&
  “ (x <= 8000) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 56000) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l))) ” &&
  “ (HuffmanFirstHeld weights_l work_l active x total) ” &&
  “ (HuffmanMinScan work_l i second) ”
  &&  (((( &( "work" ) ) + (second * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i ( &( "work" ) ) second (0 : Int) n_pre work_l)
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)

noncomputable def huffman_cost_partial_solve_wit_13 : Prop :=
  forall (n_pre : Int) (weights_pre : Int) (weights_l : (List Int)) (total : Int) (x : Int) (second : Int) (first : Int) (i : Int) (active : Int) (work_l : (List Int)) (PreH1 : (i >= active)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 8)) (PreH4 : ((Zlength (weights_l)) = n_pre)) (PreH5 : ((Zlength (work_l)) = n_pre)) (PreH6 : (Forall ((LE.le (α := Int)) (1)) weights_l)) (PreH7 : (Forall ((GE.ge (α := Int)) (1000)) weights_l)) (PreH8 : (1 <= active)) (PreH9 : (active < n_pre)) (PreH10 : (1 <= i)) (PreH11 : (i <= active)) (PreH12 : (i < n_pre)) (PreH13 : ((0 : Int) <= first)) (PreH14 : (first < n_pre)) (PreH15 : ((0 : Int) <= second)) (PreH16 : (second < i)) (PreH17 : (second < n_pre)) (PreH18 : (1 <= x)) (PreH19 : (x <= 8000)) (PreH20 : ((0 : Int) <= total)) (PreH21 : (total <= 56000)) (PreH22 : (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l)))) (PreH23 : (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l)))) (PreH24 : (HuffmanFirstHeld weights_l work_l active x total)) (PreH25 : (HuffmanMinScan work_l i second)) ,
  (intArray.full ( &( "work" ) ) n_pre (replace_Znth (second) ((Znth (active - 1) work_l (0 : Int))) (work_l)))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)
|--
  “ (i >= active) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= 8) ” &&
  “ ((Zlength (weights_l)) = n_pre) ” &&
  “ ((Zlength (work_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) weights_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (1000)) weights_l) ” &&
  “ (1 <= active) ” &&
  “ (active < n_pre) ” &&
  “ (1 <= i) ” &&
  “ (i <= active) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= first) ” &&
  “ (first < n_pre) ” &&
  “ ((0 : Int) <= second) ” &&
  “ (second < i) ” &&
  “ (second < n_pre) ” &&
  “ (1 <= x) ” &&
  “ (x <= 8000) ” &&
  “ ((0 : Int) <= total) ” &&
  “ (total <= 56000) ” &&
  “ (Forall ((LE.le (α := Int)) (1)) (sublist ((0 : Int)) (active) (work_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) (8000)) (sublist ((0 : Int)) (active) (work_l))) ” &&
  “ (HuffmanFirstHeld weights_l work_l active x total) ” &&
  “ (HuffmanMinScan work_l i second) ”
  &&  (((( &( "work" ) ) + ((active - 1) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i ( &( "work" ) ) (active - 1) (0 : Int) n_pre (replace_Znth (second) ((Znth (active - 1) work_l (0 : Int))) (work_l)))
  ** (intArray.full weights_pre n_pre weights_l)
  ** (intArray.undef_seg ( &( "work" ) ) n_pre 8)


structure VC_Correct : Type where
  proof_of_huffman_cost_safety_wit_1 : huffman_cost_safety_wit_1
  proof_of_huffman_cost_safety_wit_2 : huffman_cost_safety_wit_2
  proof_of_huffman_cost_safety_wit_3 : huffman_cost_safety_wit_3
  proof_of_huffman_cost_safety_wit_4 : huffman_cost_safety_wit_4
  proof_of_huffman_cost_safety_wit_5 : huffman_cost_safety_wit_5
  proof_of_huffman_cost_safety_wit_6 : huffman_cost_safety_wit_6
  proof_of_huffman_cost_safety_wit_7 : huffman_cost_safety_wit_7
  proof_of_huffman_cost_safety_wit_8 : huffman_cost_safety_wit_8
  proof_of_huffman_cost_safety_wit_9 : huffman_cost_safety_wit_9
  proof_of_huffman_cost_safety_wit_10 : huffman_cost_safety_wit_10
  proof_of_huffman_cost_safety_wit_11 : huffman_cost_safety_wit_11
  proof_of_huffman_cost_safety_wit_12 : huffman_cost_safety_wit_12
  proof_of_huffman_cost_safety_wit_13 : huffman_cost_safety_wit_13
  proof_of_huffman_cost_safety_wit_14 : huffman_cost_safety_wit_14
  proof_of_huffman_cost_safety_wit_17 : huffman_cost_safety_wit_17
  proof_of_huffman_cost_entail_wit_5 : huffman_cost_entail_wit_5
  proof_of_huffman_cost_return_wit_1 : huffman_cost_return_wit_1
  proof_of_huffman_cost_partial_solve_wit_1 : huffman_cost_partial_solve_wit_1
  proof_of_huffman_cost_partial_solve_wit_2 : huffman_cost_partial_solve_wit_2
  proof_of_huffman_cost_partial_solve_wit_3 : huffman_cost_partial_solve_wit_3
  proof_of_huffman_cost_partial_solve_wit_4 : huffman_cost_partial_solve_wit_4
  proof_of_huffman_cost_partial_solve_wit_5 : huffman_cost_partial_solve_wit_5
  proof_of_huffman_cost_partial_solve_wit_6 : huffman_cost_partial_solve_wit_6
  proof_of_huffman_cost_partial_solve_wit_7 : huffman_cost_partial_solve_wit_7
  proof_of_huffman_cost_partial_solve_wit_8 : huffman_cost_partial_solve_wit_8
  proof_of_huffman_cost_partial_solve_wit_9 : huffman_cost_partial_solve_wit_9
  proof_of_huffman_cost_partial_solve_wit_10 : huffman_cost_partial_solve_wit_10
  proof_of_huffman_cost_partial_solve_wit_11 : huffman_cost_partial_solve_wit_11
  proof_of_huffman_cost_partial_solve_wit_12 : huffman_cost_partial_solve_wit_12
  proof_of_huffman_cost_partial_solve_wit_13 : huffman_cost_partial_solve_wit_13
  proof_of_huffman_cost_safety_wit_15 : huffman_cost_safety_wit_15
  proof_of_huffman_cost_safety_wit_16 : huffman_cost_safety_wit_16
  proof_of_huffman_cost_entail_wit_1 : huffman_cost_entail_wit_1
  proof_of_huffman_cost_entail_wit_2 : huffman_cost_entail_wit_2
  proof_of_huffman_cost_entail_wit_3 : huffman_cost_entail_wit_3
  proof_of_huffman_cost_entail_wit_4 : huffman_cost_entail_wit_4
  proof_of_huffman_cost_entail_wit_6_1 : huffman_cost_entail_wit_6_1
  proof_of_huffman_cost_entail_wit_6_2 : huffman_cost_entail_wit_6_2
  proof_of_huffman_cost_entail_wit_7 : huffman_cost_entail_wit_7
  proof_of_huffman_cost_entail_wit_8_1 : huffman_cost_entail_wit_8_1
  proof_of_huffman_cost_entail_wit_8_2 : huffman_cost_entail_wit_8_2
  proof_of_huffman_cost_entail_wit_9 : huffman_cost_entail_wit_9
  proof_of_huffman_cost_entail_wit_10 : huffman_cost_entail_wit_10

end SimpleC.EE.LLM_bench.Algorithms.huffman_encoding.huffman_encoding_goal
