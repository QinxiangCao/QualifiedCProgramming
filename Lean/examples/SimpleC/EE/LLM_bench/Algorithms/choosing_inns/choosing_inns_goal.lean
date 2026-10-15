import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Algorithms.choosing_inns.choosing_inns_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.choosing_inns.choosing_inns_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance choosing_inns_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def initCounts_safety_wit_1 : Prop :=
  forall (k_pre : Int) (good_pre : Int) (seen_pre : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "seen" ) )) # Ptr |-> (seen_pre))
  ** ((( &( "good" ) )) # Ptr |-> (good_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** (intArray.undef_full seen_pre k_pre)
  ** (intArray.undef_full good_pre k_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def initCounts_safety_wit_2 : Prop :=
  forall (k_pre : Int) (good_pre : Int) (seen_pre : Int) (good_l : (List Int)) (seen_l : (List Int)) (i : Int) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l)) = i)) (PreH7 : (Forall (Eq ((0 : Int))) seen_l)) (PreH8 : ((Zlength (good_l)) = i)) (PreH9 : (Forall (Eq ((0 : Int))) good_l)) ,
  ((( &( "seen" ) )) # Ptr |-> (seen_pre))
  ** ((( &( "good" ) )) # Ptr |-> (good_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.seg seen_pre (0 : Int) i seen_l)
  ** (intArray.undef_seg seen_pre i k_pre)
  ** (intArray.seg good_pre (0 : Int) i good_l)
  ** (intArray.undef_seg good_pre i k_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def initCounts_safety_wit_3 : Prop :=
  forall (k_pre : Int) (good_pre : Int) (seen_pre : Int) (good_l : (List Int)) (seen_l : (List Int)) (i : Int) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l)) = i)) (PreH7 : (Forall (Eq ((0 : Int))) seen_l)) (PreH8 : ((Zlength (good_l)) = i)) (PreH9 : (Forall (Eq ((0 : Int))) good_l)) ,
  (intArray.seg seen_pre (0 : Int) (i + 1) (seen_l ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg seen_pre (i + 1) k_pre)
  ** ((( &( "seen" ) )) # Ptr |-> (seen_pre))
  ** ((( &( "good" ) )) # Ptr |-> (good_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.seg good_pre (0 : Int) i good_l)
  ** (intArray.undef_seg good_pre i k_pre)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def initCounts_safety_wit_4 : Prop :=
  forall (k_pre : Int) (good_pre : Int) (seen_pre : Int) (good_l : (List Int)) (seen_l : (List Int)) (i : Int) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l)) = i)) (PreH7 : (Forall (Eq ((0 : Int))) seen_l)) (PreH8 : ((Zlength (good_l)) = i)) (PreH9 : (Forall (Eq ((0 : Int))) good_l)) ,
  (intArray.seg good_pre (0 : Int) (i + 1) (good_l ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg good_pre (i + 1) k_pre)
  ** (intArray.seg seen_pre (0 : Int) (i + 1) (seen_l ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg seen_pre (i + 1) k_pre)
  ** ((( &( "seen" ) )) # Ptr |-> (seen_pre))
  ** ((( &( "good" ) )) # Ptr |-> (good_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def initCounts_entail_wit_1 : Prop :=
  (
forall (k_pre : Int) (good_pre : Int) (seen_pre : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) ,
  (intArray.undef_full seen_pre k_pre)
  ** (intArray.undef_full good_pre k_pre)
|--
  EX good_l : (List Int), EX seen_l : (List Int),
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 50) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= k_pre) ” &&
  “ ((Zlength (seen_l)) = (0 : Int)) ” &&
  “ (Forall (Eq ((0 : Int))) seen_l) ” &&
  “ ((Zlength (good_l)) = (0 : Int)) ” &&
  “ (Forall (Eq ((0 : Int))) good_l) ”
  &&  (intArray.seg seen_pre (0 : Int) (0 : Int) seen_l)
  ** (intArray.undef_seg seen_pre (0 : Int) k_pre)
  ** (intArray.seg good_pre (0 : Int) (0 : Int) good_l)
  ** (intArray.undef_seg good_pre (0 : Int) k_pre)
) \/
(
forall (k_pre : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) ,
  TT && emp 
|--
  “ (Forall (Eq ((0 : Int))) (@List.nil Int)) ” &&
  “ ((Zlength ((@List.nil Int))) = (0 : Int)) ” &&
  “ (Forall (Eq ((0 : Int))) (@List.nil Int)) ” &&
  “ ((Zlength ((@List.nil Int))) = (0 : Int)) ”
  &&  emp
)

noncomputable def initCounts_entail_wit_1_split_goal_1 : Prop :=
  forall (k_pre : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) ,
  (Forall (Eq ((0 : Int))) (@List.nil Int))

noncomputable def initCounts_entail_wit_1_split_goal_2 : Prop :=
  forall (k_pre : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) ,
  ((Zlength ((@List.nil Int))) = (0 : Int))

noncomputable def initCounts_entail_wit_1_split_goal_3 : Prop :=
  forall (k_pre : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) ,
  (Forall (Eq ((0 : Int))) (@List.nil Int))

noncomputable def initCounts_entail_wit_1_split_goal_4 : Prop :=
  forall (k_pre : Int) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) ,
  ((Zlength ((@List.nil Int))) = (0 : Int))

noncomputable def initCounts_entail_wit_2 : Prop :=
  (
forall (k_pre : Int) (good_pre : Int) (seen_pre : Int) (good_l_2 : (List Int)) (seen_l_2 : (List Int)) (i : Int) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l_2)) = i)) (PreH7 : (Forall (Eq ((0 : Int))) seen_l_2)) (PreH8 : ((Zlength (good_l_2)) = i)) (PreH9 : (Forall (Eq ((0 : Int))) good_l_2)) ,
  (intArray.seg good_pre (0 : Int) (i + 1) (good_l_2 ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg good_pre (i + 1) k_pre)
  ** (intArray.seg seen_pre (0 : Int) (i + 1) (seen_l_2 ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg seen_pre (i + 1) k_pre)
|--
  EX good_l : (List Int), EX seen_l : (List Int),
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 50) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= k_pre) ” &&
  “ ((Zlength (seen_l)) = (i + 1)) ” &&
  “ (Forall (Eq ((0 : Int))) seen_l) ” &&
  “ ((Zlength (good_l)) = (i + 1)) ” &&
  “ (Forall (Eq ((0 : Int))) good_l) ”
  &&  (intArray.seg seen_pre (0 : Int) (i + 1) seen_l)
  ** (intArray.undef_seg seen_pre (i + 1) k_pre)
  ** (intArray.seg good_pre (0 : Int) (i + 1) good_l)
  ** (intArray.undef_seg good_pre (i + 1) k_pre)
) \/
(
forall (k_pre : Int) (good_l_2 : (List Int)) (seen_l_2 : (List Int)) (i : Int) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l_2)) = i)) (PreH7 : (Forall (Eq ((0 : Int))) seen_l_2)) (PreH8 : ((Zlength (good_l_2)) = i)) (PreH9 : (Forall (Eq ((0 : Int))) good_l_2)) ,
  TT && emp 
|--
  “ (Forall (Eq ((0 : Int))) (good_l_2 ++ ((0 : Int) :: (@List.nil Int)))) ” &&
  “ ((Zlength ((good_l_2 ++ ((0 : Int) :: (@List.nil Int))))) = (i + 1)) ” &&
  “ (Forall (Eq ((0 : Int))) (seen_l_2 ++ ((0 : Int) :: (@List.nil Int)))) ” &&
  “ ((Zlength ((seen_l_2 ++ ((0 : Int) :: (@List.nil Int))))) = (i + 1)) ”
  &&  emp
)

noncomputable def initCounts_entail_wit_2_split_goal_1 : Prop :=
  forall (k_pre : Int) (good_l_2 : (List Int)) (seen_l_2 : (List Int)) (i : Int) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l_2)) = i)) (PreH7 : (Forall (Eq ((0 : Int))) seen_l_2)) (PreH8 : ((Zlength (good_l_2)) = i)) (PreH9 : (Forall (Eq ((0 : Int))) good_l_2)) ,
  (Forall (Eq ((0 : Int))) (good_l_2 ++ ((0 : Int) :: (@List.nil Int))))

noncomputable def initCounts_entail_wit_2_split_goal_2 : Prop :=
  forall (k_pre : Int) (good_l_2 : (List Int)) (seen_l_2 : (List Int)) (i : Int) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l_2)) = i)) (PreH7 : (Forall (Eq ((0 : Int))) seen_l_2)) (PreH8 : ((Zlength (good_l_2)) = i)) (PreH9 : (Forall (Eq ((0 : Int))) good_l_2)) ,
  ((Zlength ((good_l_2 ++ ((0 : Int) :: (@List.nil Int))))) = (i + 1))

noncomputable def initCounts_entail_wit_2_split_goal_3 : Prop :=
  forall (k_pre : Int) (good_l_2 : (List Int)) (seen_l_2 : (List Int)) (i : Int) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l_2)) = i)) (PreH7 : (Forall (Eq ((0 : Int))) seen_l_2)) (PreH8 : ((Zlength (good_l_2)) = i)) (PreH9 : (Forall (Eq ((0 : Int))) good_l_2)) ,
  (Forall (Eq ((0 : Int))) (seen_l_2 ++ ((0 : Int) :: (@List.nil Int))))

noncomputable def initCounts_entail_wit_2_split_goal_4 : Prop :=
  forall (k_pre : Int) (good_l_2 : (List Int)) (seen_l_2 : (List Int)) (i : Int) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l_2)) = i)) (PreH7 : (Forall (Eq ((0 : Int))) seen_l_2)) (PreH8 : ((Zlength (good_l_2)) = i)) (PreH9 : (Forall (Eq ((0 : Int))) good_l_2)) ,
  ((Zlength ((seen_l_2 ++ ((0 : Int) :: (@List.nil Int))))) = (i + 1))

noncomputable def initCounts_return_wit_1 : Prop :=
  (
forall (k_pre : Int) (good_pre : Int) (seen_pre : Int) (good_l_2 : (List Int)) (seen_l_2 : (List Int)) (i : Int) (PreH1 : (i >= k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l_2)) = i)) (PreH7 : (Forall (Eq ((0 : Int))) seen_l_2)) (PreH8 : ((Zlength (good_l_2)) = i)) (PreH9 : (Forall (Eq ((0 : Int))) good_l_2)) ,
  (intArray.seg seen_pre (0 : Int) i seen_l_2)
  ** (intArray.undef_seg seen_pre i k_pre)
  ** (intArray.seg good_pre (0 : Int) i good_l_2)
  ** (intArray.undef_seg good_pre i k_pre)
|--
  EX good_l : (List Int), EX seen_l : (List Int),
  “ ((Zlength (seen_l)) = k_pre) ” &&
  “ (Forall (Eq ((0 : Int))) seen_l) ” &&
  “ ((Zlength (good_l)) = k_pre) ” &&
  “ (Forall (Eq ((0 : Int))) good_l) ”
  &&  (intArray.full seen_pre k_pre seen_l)
  ** (intArray.full good_pre k_pre good_l)
) \/
(
forall (k_pre : Int) (good_pre : Int) (seen_pre : Int) (good_l_2 : (List Int)) (seen_l_2 : (List Int)) (i : Int) (PreH1 : (i >= k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l_2)) = i)) (PreH7 : (Forall (Eq ((0 : Int))) seen_l_2)) (PreH8 : ((Zlength (good_l_2)) = i)) (PreH9 : (Forall (Eq ((0 : Int))) good_l_2)) ,
  (intArray.seg seen_pre (0 : Int) i seen_l_2)
  ** (intArray.seg good_pre (0 : Int) i good_l_2)
|--
  EX good_l : (List Int), EX seen_l : (List Int),
  “ ((Zlength (seen_l)) = k_pre) ” &&
  “ (Forall (Eq ((0 : Int))) seen_l) ” &&
  “ ((Zlength (good_l)) = k_pre) ” &&
  “ (Forall (Eq ((0 : Int))) good_l) ”
  &&  (intArray.full seen_pre k_pre seen_l)
  ** (intArray.full good_pre k_pre good_l)
)

noncomputable def initCounts_partial_solve_wit_1 : Prop :=
  forall (k_pre : Int) (good_pre : Int) (seen_pre : Int) (good_l : (List Int)) (seen_l : (List Int)) (i : Int) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l)) = i)) (PreH7 : (Forall (Eq ((0 : Int))) seen_l)) (PreH8 : ((Zlength (good_l)) = i)) (PreH9 : (Forall (Eq ((0 : Int))) good_l)) ,
  (intArray.seg seen_pre (0 : Int) i seen_l)
  ** (intArray.undef_seg seen_pre i k_pre)
  ** (intArray.seg good_pre (0 : Int) i good_l)
  ** (intArray.undef_seg good_pre i k_pre)
|--
  “ (i < k_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 50) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= k_pre) ” &&
  “ ((Zlength (seen_l)) = i) ” &&
  “ (Forall (Eq ((0 : Int))) seen_l) ” &&
  “ ((Zlength (good_l)) = i) ” &&
  “ (Forall (Eq ((0 : Int))) good_l) ”
  &&  (((seen_pre + (i * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg seen_pre (i + 1) k_pre)
  ** (intArray.seg seen_pre (0 : Int) i seen_l)
  ** (intArray.seg good_pre (0 : Int) i good_l)
  ** (intArray.undef_seg good_pre i k_pre)

noncomputable def initCounts_partial_solve_wit_2 : Prop :=
  forall (k_pre : Int) (good_pre : Int) (seen_pre : Int) (good_l : (List Int)) (seen_l : (List Int)) (i : Int) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l)) = i)) (PreH7 : (Forall (Eq ((0 : Int))) seen_l)) (PreH8 : ((Zlength (good_l)) = i)) (PreH9 : (Forall (Eq ((0 : Int))) good_l)) ,
  (intArray.seg seen_pre (0 : Int) (i + 1) (seen_l ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg seen_pre (i + 1) k_pre)
  ** (intArray.seg good_pre (0 : Int) i good_l)
  ** (intArray.undef_seg good_pre i k_pre)
|--
  “ (i < k_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 50) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= k_pre) ” &&
  “ ((Zlength (seen_l)) = i) ” &&
  “ (Forall (Eq ((0 : Int))) seen_l) ” &&
  “ ((Zlength (good_l)) = i) ” &&
  “ (Forall (Eq ((0 : Int))) good_l) ”
  &&  (((good_pre + (i * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg good_pre (i + 1) k_pre)
  ** (intArray.seg seen_pre (0 : Int) (i + 1) (seen_l ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg seen_pre (i + 1) k_pre)
  ** (intArray.seg good_pre (0 : Int) i good_l)

noncomputable def copyCounts_safety_wit_1 : Prop :=
  forall (k_pre : Int) (good_pre : Int) (seen_pre : Int) (good_old : (List Int)) (seen_l : (List Int)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) (PreH3 : ((Zlength (seen_l)) = k_pre)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (200000)) seen_l)) (PreH6 : ((Zlength (good_old)) = k_pre)) (PreH7 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_old)) (PreH8 : (Forall ((GE.ge (α := Int)) (200000)) good_old)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "seen" ) )) # Ptr |-> (seen_pre))
  ** ((( &( "good" ) )) # Ptr |-> (good_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** (intArray.full seen_pre k_pre seen_l)
  ** (intArray.full good_pre k_pre good_old)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def copyCounts_safety_wit_2 : Prop :=
  forall (k_pre : Int) (good_pre : Int) (seen_pre : Int) (good_old : (List Int)) (seen_l : (List Int)) (good_cur : (List Int)) (i : Int) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l)) = k_pre)) (PreH7 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l)) (PreH8 : (Forall ((GE.ge (α := Int)) (200000)) seen_l)) (PreH9 : ((Zlength (good_old)) = k_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_old)) (PreH11 : (Forall ((GE.ge (α := Int)) (200000)) good_old)) (PreH12 : ((Zlength (good_cur)) = k_pre)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_cur)) (PreH14 : (Forall ((GE.ge (α := Int)) (200000)) good_cur)) (PreH15 : (InnsCopiedPrefix seen_l good_old good_cur i k_pre)) ,
  (intArray.full good_pre k_pre (replace_Znth (i) ((Znth i seen_l (0 : Int))) (good_cur)))
  ** (intArray.full seen_pre k_pre seen_l)
  ** ((( &( "seen" ) )) # Ptr |-> (seen_pre))
  ** ((( &( "good" ) )) # Ptr |-> (good_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def copyCounts_entail_wit_1 : Prop :=
  (
forall (k_pre : Int) (good_pre : Int) (seen_pre : Int) (good_old : (List Int)) (seen_l : (List Int)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) (PreH3 : ((Zlength (seen_l)) = k_pre)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (200000)) seen_l)) (PreH6 : ((Zlength (good_old)) = k_pre)) (PreH7 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_old)) (PreH8 : (Forall ((GE.ge (α := Int)) (200000)) good_old)) ,
  (intArray.full seen_pre k_pre seen_l)
  ** (intArray.full good_pre k_pre good_old)
|--
  EX good_cur : (List Int),
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 50) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= k_pre) ” &&
  “ ((Zlength (seen_l)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (200000)) seen_l) ” &&
  “ ((Zlength (good_old)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) good_old) ” &&
  “ (Forall ((GE.ge (α := Int)) (200000)) good_old) ” &&
  “ ((Zlength (good_cur)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) good_cur) ” &&
  “ (Forall ((GE.ge (α := Int)) (200000)) good_cur) ” &&
  “ (InnsCopiedPrefix seen_l good_old good_cur (0 : Int) k_pre) ”
  &&  (intArray.full seen_pre k_pre seen_l)
  ** (intArray.full good_pre k_pre good_cur)
) \/
(
forall (k_pre : Int) (good_old : (List Int)) (seen_l : (List Int)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) (PreH3 : ((Zlength (seen_l)) = k_pre)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (200000)) seen_l)) (PreH6 : ((Zlength (good_old)) = k_pre)) (PreH7 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_old)) (PreH8 : (Forall ((GE.ge (α := Int)) (200000)) good_old)) ,
  TT && emp 
|--
  “ (InnsCopiedPrefix seen_l good_old good_old (0 : Int) k_pre) ”
  &&  emp
)

noncomputable def copyCounts_entail_wit_1_split_goal_1 : Prop :=
  forall (k_pre : Int) (good_old : (List Int)) (seen_l : (List Int)) (PreH1 : (1 <= k_pre)) (PreH2 : (k_pre <= 50)) (PreH3 : ((Zlength (seen_l)) = k_pre)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l)) (PreH5 : (Forall ((GE.ge (α := Int)) (200000)) seen_l)) (PreH6 : ((Zlength (good_old)) = k_pre)) (PreH7 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_old)) (PreH8 : (Forall ((GE.ge (α := Int)) (200000)) good_old)) ,
  (InnsCopiedPrefix seen_l good_old good_old (0 : Int) k_pre)

noncomputable def copyCounts_entail_wit_2 : Prop :=
  (
forall (k_pre : Int) (good_pre : Int) (seen_pre : Int) (good_old : (List Int)) (seen_l : (List Int)) (good_cur_2 : (List Int)) (i : Int) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l)) = k_pre)) (PreH7 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l)) (PreH8 : (Forall ((GE.ge (α := Int)) (200000)) seen_l)) (PreH9 : ((Zlength (good_old)) = k_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_old)) (PreH11 : (Forall ((GE.ge (α := Int)) (200000)) good_old)) (PreH12 : ((Zlength (good_cur_2)) = k_pre)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_cur_2)) (PreH14 : (Forall ((GE.ge (α := Int)) (200000)) good_cur_2)) (PreH15 : (InnsCopiedPrefix seen_l good_old good_cur_2 i k_pre)) ,
  (intArray.full good_pre k_pre (replace_Znth (i) ((Znth i seen_l (0 : Int))) (good_cur_2)))
  ** (intArray.full seen_pre k_pre seen_l)
|--
  EX good_cur : (List Int),
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 50) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= k_pre) ” &&
  “ ((Zlength (seen_l)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (200000)) seen_l) ” &&
  “ ((Zlength (good_old)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) good_old) ” &&
  “ (Forall ((GE.ge (α := Int)) (200000)) good_old) ” &&
  “ ((Zlength (good_cur)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) good_cur) ” &&
  “ (Forall ((GE.ge (α := Int)) (200000)) good_cur) ” &&
  “ (InnsCopiedPrefix seen_l good_old good_cur (i + 1) k_pre) ”
  &&  (intArray.full seen_pre k_pre seen_l)
  ** (intArray.full good_pre k_pre good_cur)
) \/
(
forall (k_pre : Int) (good_old : (List Int)) (seen_l : (List Int)) (good_cur_2 : (List Int)) (i : Int) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l)) = k_pre)) (PreH7 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l)) (PreH8 : (Forall ((GE.ge (α := Int)) (200000)) seen_l)) (PreH9 : ((Zlength (good_old)) = k_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_old)) (PreH11 : (Forall ((GE.ge (α := Int)) (200000)) good_old)) (PreH12 : ((Zlength (good_cur_2)) = k_pre)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_cur_2)) (PreH14 : (Forall ((GE.ge (α := Int)) (200000)) good_cur_2)) (PreH15 : (InnsCopiedPrefix seen_l good_old good_cur_2 i k_pre)) ,
  TT && emp 
|--
  “ (InnsCopiedPrefix seen_l good_old (replace_Znth (i) ((Znth i seen_l (0 : Int))) (good_cur_2)) (i + 1) k_pre) ” &&
  “ (Forall ((GE.ge (α := Int)) (200000)) (replace_Znth (i) ((Znth i seen_l (0 : Int))) (good_cur_2))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (replace_Znth (i) ((Znth i seen_l (0 : Int))) (good_cur_2))) ” &&
  “ ((Zlength ((replace_Znth (i) ((Znth i seen_l (0 : Int))) (good_cur_2)))) = k_pre) ”
  &&  emp
)

noncomputable def copyCounts_entail_wit_2_split_goal_1 : Prop :=
  forall (k_pre : Int) (good_old : (List Int)) (seen_l : (List Int)) (good_cur_2 : (List Int)) (i : Int) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l)) = k_pre)) (PreH7 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l)) (PreH8 : (Forall ((GE.ge (α := Int)) (200000)) seen_l)) (PreH9 : ((Zlength (good_old)) = k_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_old)) (PreH11 : (Forall ((GE.ge (α := Int)) (200000)) good_old)) (PreH12 : ((Zlength (good_cur_2)) = k_pre)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_cur_2)) (PreH14 : (Forall ((GE.ge (α := Int)) (200000)) good_cur_2)) (PreH15 : (InnsCopiedPrefix seen_l good_old good_cur_2 i k_pre)) ,
  (InnsCopiedPrefix seen_l good_old (replace_Znth (i) ((Znth i seen_l (0 : Int))) (good_cur_2)) (i + 1) k_pre)

noncomputable def copyCounts_entail_wit_2_split_goal_2 : Prop :=
  forall (k_pre : Int) (good_old : (List Int)) (seen_l : (List Int)) (good_cur_2 : (List Int)) (i : Int) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l)) = k_pre)) (PreH7 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l)) (PreH8 : (Forall ((GE.ge (α := Int)) (200000)) seen_l)) (PreH9 : ((Zlength (good_old)) = k_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_old)) (PreH11 : (Forall ((GE.ge (α := Int)) (200000)) good_old)) (PreH12 : ((Zlength (good_cur_2)) = k_pre)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_cur_2)) (PreH14 : (Forall ((GE.ge (α := Int)) (200000)) good_cur_2)) (PreH15 : (InnsCopiedPrefix seen_l good_old good_cur_2 i k_pre)) ,
  (Forall ((GE.ge (α := Int)) (200000)) (replace_Znth (i) ((Znth i seen_l (0 : Int))) (good_cur_2)))

noncomputable def copyCounts_entail_wit_2_split_goal_3 : Prop :=
  forall (k_pre : Int) (good_old : (List Int)) (seen_l : (List Int)) (good_cur_2 : (List Int)) (i : Int) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l)) = k_pre)) (PreH7 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l)) (PreH8 : (Forall ((GE.ge (α := Int)) (200000)) seen_l)) (PreH9 : ((Zlength (good_old)) = k_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_old)) (PreH11 : (Forall ((GE.ge (α := Int)) (200000)) good_old)) (PreH12 : ((Zlength (good_cur_2)) = k_pre)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_cur_2)) (PreH14 : (Forall ((GE.ge (α := Int)) (200000)) good_cur_2)) (PreH15 : (InnsCopiedPrefix seen_l good_old good_cur_2 i k_pre)) ,
  (Forall ((LE.le (α := Int)) ((0 : Int))) (replace_Znth (i) ((Znth i seen_l (0 : Int))) (good_cur_2)))

noncomputable def copyCounts_entail_wit_2_split_goal_4 : Prop :=
  forall (k_pre : Int) (good_old : (List Int)) (seen_l : (List Int)) (good_cur_2 : (List Int)) (i : Int) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l)) = k_pre)) (PreH7 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l)) (PreH8 : (Forall ((GE.ge (α := Int)) (200000)) seen_l)) (PreH9 : ((Zlength (good_old)) = k_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_old)) (PreH11 : (Forall ((GE.ge (α := Int)) (200000)) good_old)) (PreH12 : ((Zlength (good_cur_2)) = k_pre)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_cur_2)) (PreH14 : (Forall ((GE.ge (α := Int)) (200000)) good_cur_2)) (PreH15 : (InnsCopiedPrefix seen_l good_old good_cur_2 i k_pre)) ,
  ((Zlength ((replace_Znth (i) ((Znth i seen_l (0 : Int))) (good_cur_2)))) = k_pre)

noncomputable def copyCounts_return_wit_1 : Prop :=
  (
forall (k_pre : Int) (good_pre : Int) (seen_pre : Int) (good_old : (List Int)) (seen_l : (List Int)) (good_cur : (List Int)) (i : Int) (PreH1 : (i >= k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l)) = k_pre)) (PreH7 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l)) (PreH8 : (Forall ((GE.ge (α := Int)) (200000)) seen_l)) (PreH9 : ((Zlength (good_old)) = k_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_old)) (PreH11 : (Forall ((GE.ge (α := Int)) (200000)) good_old)) (PreH12 : ((Zlength (good_cur)) = k_pre)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_cur)) (PreH14 : (Forall ((GE.ge (α := Int)) (200000)) good_cur)) (PreH15 : (InnsCopiedPrefix seen_l good_old good_cur i k_pre)) ,
  (intArray.full seen_pre k_pre seen_l)
  ** (intArray.full good_pre k_pre good_cur)
|--
  (intArray.full seen_pre k_pre seen_l)
  ** (intArray.full good_pre k_pre seen_l)
) \/
(
forall (k_pre : Int) (good_old : (List Int)) (seen_l : (List Int)) (good_cur : (List Int)) (i : Int) (PreH1 : (i >= k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l)) = k_pre)) (PreH7 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l)) (PreH8 : (Forall ((GE.ge (α := Int)) (200000)) seen_l)) (PreH9 : ((Zlength (good_old)) = k_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_old)) (PreH11 : (Forall ((GE.ge (α := Int)) (200000)) good_old)) (PreH12 : ((Zlength (good_cur)) = k_pre)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_cur)) (PreH14 : (Forall ((GE.ge (α := Int)) (200000)) good_cur)) (PreH15 : (InnsCopiedPrefix seen_l good_old good_cur i k_pre)) ,
  TT && emp 
|--
  “ (good_cur = seen_l) ”
  &&  emp
)

noncomputable def copyCounts_return_wit_1_split_goal_1 : Prop :=
  forall (k_pre : Int) (good_old : (List Int)) (seen_l : (List Int)) (good_cur : (List Int)) (i : Int) (PreH1 : (i >= k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l)) = k_pre)) (PreH7 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l)) (PreH8 : (Forall ((GE.ge (α := Int)) (200000)) seen_l)) (PreH9 : ((Zlength (good_old)) = k_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_old)) (PreH11 : (Forall ((GE.ge (α := Int)) (200000)) good_old)) (PreH12 : ((Zlength (good_cur)) = k_pre)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_cur)) (PreH14 : (Forall ((GE.ge (α := Int)) (200000)) good_cur)) (PreH15 : (InnsCopiedPrefix seen_l good_old good_cur i k_pre)) ,
  (good_cur = seen_l)

noncomputable def copyCounts_partial_solve_wit_1 : Prop :=
  forall (k_pre : Int) (good_pre : Int) (seen_pre : Int) (good_old : (List Int)) (seen_l : (List Int)) (good_cur : (List Int)) (i : Int) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l)) = k_pre)) (PreH7 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l)) (PreH8 : (Forall ((GE.ge (α := Int)) (200000)) seen_l)) (PreH9 : ((Zlength (good_old)) = k_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_old)) (PreH11 : (Forall ((GE.ge (α := Int)) (200000)) good_old)) (PreH12 : ((Zlength (good_cur)) = k_pre)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_cur)) (PreH14 : (Forall ((GE.ge (α := Int)) (200000)) good_cur)) (PreH15 : (InnsCopiedPrefix seen_l good_old good_cur i k_pre)) ,
  (intArray.full seen_pre k_pre seen_l)
  ** (intArray.full good_pre k_pre good_cur)
|--
  “ (i < k_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 50) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= k_pre) ” &&
  “ ((Zlength (seen_l)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (200000)) seen_l) ” &&
  “ ((Zlength (good_old)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) good_old) ” &&
  “ (Forall ((GE.ge (α := Int)) (200000)) good_old) ” &&
  “ ((Zlength (good_cur)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) good_cur) ” &&
  “ (Forall ((GE.ge (α := Int)) (200000)) good_cur) ” &&
  “ (InnsCopiedPrefix seen_l good_old good_cur i k_pre) ”
  &&  (((seen_pre + (i * sizeof(INT)))) # Int |-> ((Znth i seen_l (0 : Int))))
  ** (intArray.missing_i seen_pre i (0 : Int) k_pre seen_l)
  ** (intArray.full good_pre k_pre good_cur)

noncomputable def copyCounts_partial_solve_wit_2 : Prop :=
  forall (k_pre : Int) (good_pre : Int) (seen_pre : Int) (good_old : (List Int)) (seen_l : (List Int)) (good_cur : (List Int)) (i : Int) (PreH1 : (i < k_pre)) (PreH2 : (1 <= k_pre)) (PreH3 : (k_pre <= 50)) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= k_pre)) (PreH6 : ((Zlength (seen_l)) = k_pre)) (PreH7 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l)) (PreH8 : (Forall ((GE.ge (α := Int)) (200000)) seen_l)) (PreH9 : ((Zlength (good_old)) = k_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_old)) (PreH11 : (Forall ((GE.ge (α := Int)) (200000)) good_old)) (PreH12 : ((Zlength (good_cur)) = k_pre)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_cur)) (PreH14 : (Forall ((GE.ge (α := Int)) (200000)) good_cur)) (PreH15 : (InnsCopiedPrefix seen_l good_old good_cur i k_pre)) ,
  (intArray.full seen_pre k_pre seen_l)
  ** (intArray.full good_pre k_pre good_cur)
|--
  “ (i < k_pre) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 50) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= k_pre) ” &&
  “ ((Zlength (seen_l)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (200000)) seen_l) ” &&
  “ ((Zlength (good_old)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) good_old) ” &&
  “ (Forall ((GE.ge (α := Int)) (200000)) good_old) ” &&
  “ ((Zlength (good_cur)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) good_cur) ” &&
  “ (Forall ((GE.ge (α := Int)) (200000)) good_cur) ” &&
  “ (InnsCopiedPrefix seen_l good_old good_cur i k_pre) ”
  &&  (((good_pre + (i * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i good_pre i (0 : Int) k_pre good_cur)
  ** (intArray.full seen_pre k_pre seen_l)

noncomputable def countChoosingInns_safety_wit_1 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 50)) (PreH5 : ((0 : Int) <= p_pre)) (PreH6 : (p_pre <= 100)) (PreH7 : ((Zlength (colors_l)) = n_pre)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH10 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH12 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) ,
  ((( &( "answer" ) )) # Int64 |->_)
  ** (intArray.undef_full ( &( "good" ) ) 50)
  ** (intArray.undef_full ( &( "seen" ) ) 50)
  ** ((( &( "colors" ) )) # Ptr |-> (colors_pre))
  ** ((( &( "costs" ) )) # Ptr |-> (costs_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "p" ) )) # Int |-> (p_pre))
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def countChoosingInns_safety_wit_2 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (answer : Int) (PreH1 : (answer = (0 : Int))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : ((0 : Int) <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH11 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH13 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) ,
  ((( &( "colors" ) )) # Ptr |-> (colors_pre))
  ** ((( &( "costs" ) )) # Ptr |-> (costs_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "answer" ) )) # Int64 |-> (answer))
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.undef_full (( &( "seen" ) ) + ((0 : Int) * sizeof(INT))) k_pre)
  ** (intArray.undef_full (( &( "good" ) ) + ((0 : Int) * sizeof(INT))) k_pre)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def countChoosingInns_safety_wit_3 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (answer : Int) (PreH1 : (answer = (0 : Int))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : ((0 : Int) <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH11 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH13 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) ,
  ((( &( "colors" ) )) # Ptr |-> (colors_pre))
  ** ((( &( "costs" ) )) # Ptr |-> (costs_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "answer" ) )) # Int64 |-> (answer))
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.undef_full (( &( "seen" ) ) + ((0 : Int) * sizeof(INT))) k_pre)
  ** (intArray.undef_full (( &( "good" ) ) + ((0 : Int) * sizeof(INT))) k_pre)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def countChoosingInns_safety_wit_4 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (answer : Int) (good_l : (List Int)) (seen_l : (List Int)) (PreH1 : ((Zlength (seen_l)) = k_pre)) (PreH2 : (Forall (Eq ((0 : Int))) seen_l)) (PreH3 : ((Zlength (good_l)) = k_pre)) (PreH4 : (Forall (Eq ((0 : Int))) good_l)) (PreH5 : (answer = (0 : Int))) (PreH6 : ((0 : Int) <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= 50)) (PreH10 : ((0 : Int) <= p_pre)) (PreH11 : (p_pre <= 100)) (PreH12 : ((Zlength (colors_l)) = n_pre)) (PreH13 : ((Zlength (costs_l)) = n_pre)) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH15 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH17 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) ,
  ((( &( "i" ) )) # Int |->_)
  ** (intArray.full (( &( "seen" ) ) + ((0 : Int) * sizeof(INT))) k_pre seen_l)
  ** (intArray.full (( &( "good" ) ) + ((0 : Int) * sizeof(INT))) k_pre good_l)
  ** ((( &( "colors" ) )) # Ptr |-> (colors_pre))
  ** ((( &( "costs" ) )) # Ptr |-> (costs_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "answer" ) )) # Int64 |-> (answer))
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def countChoosingInns_safety_wit_5 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l : (List Int)) (good_l : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (cost <= p_pre)) (PreH2 : (c = (Znth i colors_l (0 : Int)))) (PreH3 : (cost = (Znth i costs_l (0 : Int)))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : ((0 : Int) <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH13 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH15 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i < n_pre)) (PreH18 : ((0 : Int) <= c)) (PreH19 : (c < k_pre)) (PreH20 : ((0 : Int) <= cost)) (PreH21 : (cost <= 100)) (PreH22 : ((0 : Int) <= answer)) (PreH23 : (answer <= 19999900000)) (PreH24 : ((0 : Int) <= (Znth c seen_l (0 : Int)))) (PreH25 : ((Znth c seen_l (0 : Int)) <= i)) (PreH26 : ((0 : Int) <= (Znth c good_l (0 : Int)))) (PreH27 : ((Znth c good_l (0 : Int)) <= i)) (PreH28 : ((answer + (Znth c seen_l (0 : Int))) <= 9223372036854775807)) (PreH29 : ((answer + (Znth c good_l (0 : Int))) <= 9223372036854775807)) (PreH30 : (((Znth c seen_l (0 : Int)) + 1) <= INT_MAX)) (PreH31 : ((0 : Int) <= i)) (PreH32 : (i <= (Zlength (colors_l)))) (PreH33 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH34 : ((Zlength (seen_l)) = k_pre)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (i)) seen_l)) (PreH37 : ((Zlength (good_l)) = k_pre)) (PreH38 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l)) (PreH39 : (Forall ((GE.ge (α := Int)) (i)) good_l)) (PreH40 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l)) ,
  (intArray.full ( &( "seen" ) ) k_pre seen_l)
  ** ((( &( "colors" ) )) # Ptr |-> (colors_pre))
  ** ((( &( "costs" ) )) # Ptr |-> (costs_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cost" ) )) # Int |-> (cost))
  ** ((( &( "answer" ) )) # Int64 |-> (answer))
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full ( &( "good" ) ) k_pre good_l)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)
|--
  “ ((answer + (Znth c seen_l (0 : Int))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (answer + (Znth c seen_l (0 : Int)))) ”

noncomputable def countChoosingInns_safety_wit_6 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l : (List Int)) (good_l : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (cost <= p_pre)) (PreH2 : (c = (Znth i colors_l (0 : Int)))) (PreH3 : (cost = (Znth i costs_l (0 : Int)))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : ((0 : Int) <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH13 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH15 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i < n_pre)) (PreH18 : ((0 : Int) <= c)) (PreH19 : (c < k_pre)) (PreH20 : ((0 : Int) <= cost)) (PreH21 : (cost <= 100)) (PreH22 : ((0 : Int) <= answer)) (PreH23 : (answer <= 19999900000)) (PreH24 : ((0 : Int) <= (Znth c seen_l (0 : Int)))) (PreH25 : ((Znth c seen_l (0 : Int)) <= i)) (PreH26 : ((0 : Int) <= (Znth c good_l (0 : Int)))) (PreH27 : ((Znth c good_l (0 : Int)) <= i)) (PreH28 : ((answer + (Znth c seen_l (0 : Int))) <= 9223372036854775807)) (PreH29 : ((answer + (Znth c good_l (0 : Int))) <= 9223372036854775807)) (PreH30 : (((Znth c seen_l (0 : Int)) + 1) <= INT_MAX)) (PreH31 : ((0 : Int) <= i)) (PreH32 : (i <= (Zlength (colors_l)))) (PreH33 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH34 : ((Zlength (seen_l)) = k_pre)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (i)) seen_l)) (PreH37 : ((Zlength (good_l)) = k_pre)) (PreH38 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l)) (PreH39 : (Forall ((GE.ge (α := Int)) (i)) good_l)) (PreH40 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l)) ,
  (intArray.full ( &( "seen" ) ) k_pre seen_l)
  ** ((( &( "colors" ) )) # Ptr |-> (colors_pre))
  ** ((( &( "costs" ) )) # Ptr |-> (costs_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cost" ) )) # Int |-> (cost))
  ** ((( &( "answer" ) )) # Int64 |-> ((answer + (Znth c seen_l (0 : Int)))))
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full ( &( "good" ) ) k_pre good_l)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)
|--
  “ (((Znth c seen_l (0 : Int)) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth c seen_l (0 : Int)) + 1)) ”

noncomputable def countChoosingInns_safety_wit_7 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l : (List Int)) (good_l : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (cost <= p_pre)) (PreH2 : (c = (Znth i colors_l (0 : Int)))) (PreH3 : (cost = (Znth i costs_l (0 : Int)))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : ((0 : Int) <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH13 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH15 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i < n_pre)) (PreH18 : ((0 : Int) <= c)) (PreH19 : (c < k_pre)) (PreH20 : ((0 : Int) <= cost)) (PreH21 : (cost <= 100)) (PreH22 : ((0 : Int) <= answer)) (PreH23 : (answer <= 19999900000)) (PreH24 : ((0 : Int) <= (Znth c seen_l (0 : Int)))) (PreH25 : ((Znth c seen_l (0 : Int)) <= i)) (PreH26 : ((0 : Int) <= (Znth c good_l (0 : Int)))) (PreH27 : ((Znth c good_l (0 : Int)) <= i)) (PreH28 : ((answer + (Znth c seen_l (0 : Int))) <= 9223372036854775807)) (PreH29 : ((answer + (Znth c good_l (0 : Int))) <= 9223372036854775807)) (PreH30 : (((Znth c seen_l (0 : Int)) + 1) <= INT_MAX)) (PreH31 : ((0 : Int) <= i)) (PreH32 : (i <= (Zlength (colors_l)))) (PreH33 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH34 : ((Zlength (seen_l)) = k_pre)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (i)) seen_l)) (PreH37 : ((Zlength (good_l)) = k_pre)) (PreH38 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l)) (PreH39 : (Forall ((GE.ge (α := Int)) (i)) good_l)) (PreH40 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l)) ,
  (intArray.full ( &( "seen" ) ) k_pre seen_l)
  ** ((( &( "colors" ) )) # Ptr |-> (colors_pre))
  ** ((( &( "costs" ) )) # Ptr |-> (costs_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cost" ) )) # Int |-> (cost))
  ** ((( &( "answer" ) )) # Int64 |-> ((answer + (Znth c seen_l (0 : Int)))))
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full ( &( "good" ) ) k_pre good_l)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def countChoosingInns_safety_wit_8 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_next : (List Int)) (seen_l : (List Int)) (good_l : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (c = (Znth i colors_l (0 : Int)))) (PreH2 : (cost = (Znth i costs_l (0 : Int)))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 50)) (PreH7 : ((0 : Int) <= p_pre)) (PreH8 : (p_pre <= 100)) (PreH9 : ((Zlength (colors_l)) = n_pre)) (PreH10 : ((Zlength (costs_l)) = n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH12 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH14 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) (PreH15 : ((0 : Int) <= cost)) (PreH16 : (cost <= p_pre)) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i < n_pre)) (PreH19 : ((0 : Int) <= c)) (PreH20 : (c < k_pre)) (PreH21 : ((0 : Int) <= answer)) (PreH22 : (answer <= 19999900000)) (PreH23 : (seen_next = (replace_Znth (c) (((Znth c seen_l (0 : Int)) + 1)) (seen_l)))) (PreH24 : ((0 : Int) <= i)) (PreH25 : (i <= (Zlength (colors_l)))) (PreH26 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH27 : ((Zlength (seen_l)) = k_pre)) (PreH28 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l)) (PreH29 : (Forall ((GE.ge (α := Int)) (i)) seen_l)) (PreH30 : ((Zlength (good_l)) = k_pre)) (PreH31 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l)) (PreH32 : (Forall ((GE.ge (α := Int)) (i)) good_l)) (PreH33 : ((0 : Int) <= (i + 1))) (PreH34 : ((i + 1) <= (Zlength (colors_l)))) (PreH35 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH36 : ((Zlength (seen_next)) = k_pre)) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_next)) (PreH38 : (Forall ((GE.ge (α := Int)) ((i + 1))) seen_next)) (PreH39 : ((Zlength (good_l)) = k_pre)) (PreH40 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l)) (PreH41 : (Forall ((GE.ge (α := Int)) ((i + 1))) good_l)) (PreH42 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l (0 : Int))) seen_l good_l)) (PreH43 : ((Zlength (seen_next)) = k_pre)) (PreH44 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_next)) (PreH45 : (Forall ((GE.ge (α := Int)) (200000)) seen_next)) (PreH46 : ((Zlength (good_l)) = k_pre)) (PreH47 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l)) (PreH48 : (Forall ((GE.ge (α := Int)) (200000)) good_l)) ,
  ((( &( "colors" ) )) # Ptr |-> (colors_pre))
  ** ((( &( "costs" ) )) # Ptr |-> (costs_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cost" ) )) # Int |-> (cost))
  ** ((( &( "answer" ) )) # Int64 |-> (answer))
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full (( &( "seen" ) ) + ((0 : Int) * sizeof(INT))) k_pre seen_next)
  ** (intArray.full (( &( "good" ) ) + ((0 : Int) * sizeof(INT))) k_pre good_l)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def countChoosingInns_safety_wit_9 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_next : (List Int)) (seen_l : (List Int)) (good_l : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (c = (Znth i colors_l (0 : Int)))) (PreH2 : (cost = (Znth i costs_l (0 : Int)))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 50)) (PreH7 : ((0 : Int) <= p_pre)) (PreH8 : (p_pre <= 100)) (PreH9 : ((Zlength (colors_l)) = n_pre)) (PreH10 : ((Zlength (costs_l)) = n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH12 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH14 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) (PreH15 : ((0 : Int) <= cost)) (PreH16 : (cost <= p_pre)) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i < n_pre)) (PreH19 : ((0 : Int) <= c)) (PreH20 : (c < k_pre)) (PreH21 : ((0 : Int) <= answer)) (PreH22 : (answer <= 19999900000)) (PreH23 : (seen_next = (replace_Znth (c) (((Znth c seen_l (0 : Int)) + 1)) (seen_l)))) (PreH24 : ((0 : Int) <= i)) (PreH25 : (i <= (Zlength (colors_l)))) (PreH26 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH27 : ((Zlength (seen_l)) = k_pre)) (PreH28 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l)) (PreH29 : (Forall ((GE.ge (α := Int)) (i)) seen_l)) (PreH30 : ((Zlength (good_l)) = k_pre)) (PreH31 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l)) (PreH32 : (Forall ((GE.ge (α := Int)) (i)) good_l)) (PreH33 : ((0 : Int) <= (i + 1))) (PreH34 : ((i + 1) <= (Zlength (colors_l)))) (PreH35 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH36 : ((Zlength (seen_next)) = k_pre)) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_next)) (PreH38 : (Forall ((GE.ge (α := Int)) ((i + 1))) seen_next)) (PreH39 : ((Zlength (good_l)) = k_pre)) (PreH40 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l)) (PreH41 : (Forall ((GE.ge (α := Int)) ((i + 1))) good_l)) (PreH42 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l (0 : Int))) seen_l good_l)) (PreH43 : ((Zlength (seen_next)) = k_pre)) (PreH44 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_next)) (PreH45 : (Forall ((GE.ge (α := Int)) (200000)) seen_next)) (PreH46 : ((Zlength (good_l)) = k_pre)) (PreH47 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l)) (PreH48 : (Forall ((GE.ge (α := Int)) (200000)) good_l)) ,
  ((( &( "colors" ) )) # Ptr |-> (colors_pre))
  ** ((( &( "costs" ) )) # Ptr |-> (costs_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cost" ) )) # Int |-> (cost))
  ** ((( &( "answer" ) )) # Int64 |-> (answer))
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full (( &( "seen" ) ) + ((0 : Int) * sizeof(INT))) k_pre seen_next)
  ** (intArray.full (( &( "good" ) ) + ((0 : Int) * sizeof(INT))) k_pre good_l)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def countChoosingInns_safety_wit_10 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l : (List Int)) (good_l : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (cost > p_pre)) (PreH2 : (c = (Znth i colors_l (0 : Int)))) (PreH3 : (cost = (Znth i costs_l (0 : Int)))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : ((0 : Int) <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH13 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH15 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i < n_pre)) (PreH18 : ((0 : Int) <= c)) (PreH19 : (c < k_pre)) (PreH20 : ((0 : Int) <= cost)) (PreH21 : (cost <= 100)) (PreH22 : ((0 : Int) <= answer)) (PreH23 : (answer <= 19999900000)) (PreH24 : ((0 : Int) <= (Znth c seen_l (0 : Int)))) (PreH25 : ((Znth c seen_l (0 : Int)) <= i)) (PreH26 : ((0 : Int) <= (Znth c good_l (0 : Int)))) (PreH27 : ((Znth c good_l (0 : Int)) <= i)) (PreH28 : ((answer + (Znth c seen_l (0 : Int))) <= 9223372036854775807)) (PreH29 : ((answer + (Znth c good_l (0 : Int))) <= 9223372036854775807)) (PreH30 : (((Znth c seen_l (0 : Int)) + 1) <= INT_MAX)) (PreH31 : ((0 : Int) <= i)) (PreH32 : (i <= (Zlength (colors_l)))) (PreH33 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH34 : ((Zlength (seen_l)) = k_pre)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (i)) seen_l)) (PreH37 : ((Zlength (good_l)) = k_pre)) (PreH38 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l)) (PreH39 : (Forall ((GE.ge (α := Int)) (i)) good_l)) (PreH40 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l)) ,
  (intArray.full ( &( "good" ) ) k_pre good_l)
  ** ((( &( "colors" ) )) # Ptr |-> (colors_pre))
  ** ((( &( "costs" ) )) # Ptr |-> (costs_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cost" ) )) # Int |-> (cost))
  ** ((( &( "answer" ) )) # Int64 |-> (answer))
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full ( &( "seen" ) ) k_pre seen_l)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)
|--
  “ ((answer + (Znth c good_l (0 : Int))) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (answer + (Znth c good_l (0 : Int)))) ”

noncomputable def countChoosingInns_safety_wit_11 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l : (List Int)) (good_l : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (cost > p_pre)) (PreH2 : (c = (Znth i colors_l (0 : Int)))) (PreH3 : (cost = (Znth i costs_l (0 : Int)))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : ((0 : Int) <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH13 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH15 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i < n_pre)) (PreH18 : ((0 : Int) <= c)) (PreH19 : (c < k_pre)) (PreH20 : ((0 : Int) <= cost)) (PreH21 : (cost <= 100)) (PreH22 : ((0 : Int) <= answer)) (PreH23 : (answer <= 19999900000)) (PreH24 : ((0 : Int) <= (Znth c seen_l (0 : Int)))) (PreH25 : ((Znth c seen_l (0 : Int)) <= i)) (PreH26 : ((0 : Int) <= (Znth c good_l (0 : Int)))) (PreH27 : ((Znth c good_l (0 : Int)) <= i)) (PreH28 : ((answer + (Znth c seen_l (0 : Int))) <= 9223372036854775807)) (PreH29 : ((answer + (Znth c good_l (0 : Int))) <= 9223372036854775807)) (PreH30 : (((Znth c seen_l (0 : Int)) + 1) <= INT_MAX)) (PreH31 : ((0 : Int) <= i)) (PreH32 : (i <= (Zlength (colors_l)))) (PreH33 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH34 : ((Zlength (seen_l)) = k_pre)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (i)) seen_l)) (PreH37 : ((Zlength (good_l)) = k_pre)) (PreH38 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l)) (PreH39 : (Forall ((GE.ge (α := Int)) (i)) good_l)) (PreH40 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l)) ,
  (intArray.full ( &( "seen" ) ) k_pre seen_l)
  ** (intArray.full ( &( "good" ) ) k_pre good_l)
  ** ((( &( "colors" ) )) # Ptr |-> (colors_pre))
  ** ((( &( "costs" ) )) # Ptr |-> (costs_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cost" ) )) # Int |-> (cost))
  ** ((( &( "answer" ) )) # Int64 |-> ((answer + (Znth c good_l (0 : Int)))))
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)
|--
  “ (((Znth c seen_l (0 : Int)) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth c seen_l (0 : Int)) + 1)) ”

noncomputable def countChoosingInns_safety_wit_12 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l : (List Int)) (good_l : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (cost > p_pre)) (PreH2 : (c = (Znth i colors_l (0 : Int)))) (PreH3 : (cost = (Znth i costs_l (0 : Int)))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : ((0 : Int) <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH13 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH15 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i < n_pre)) (PreH18 : ((0 : Int) <= c)) (PreH19 : (c < k_pre)) (PreH20 : ((0 : Int) <= cost)) (PreH21 : (cost <= 100)) (PreH22 : ((0 : Int) <= answer)) (PreH23 : (answer <= 19999900000)) (PreH24 : ((0 : Int) <= (Znth c seen_l (0 : Int)))) (PreH25 : ((Znth c seen_l (0 : Int)) <= i)) (PreH26 : ((0 : Int) <= (Znth c good_l (0 : Int)))) (PreH27 : ((Znth c good_l (0 : Int)) <= i)) (PreH28 : ((answer + (Znth c seen_l (0 : Int))) <= 9223372036854775807)) (PreH29 : ((answer + (Znth c good_l (0 : Int))) <= 9223372036854775807)) (PreH30 : (((Znth c seen_l (0 : Int)) + 1) <= INT_MAX)) (PreH31 : ((0 : Int) <= i)) (PreH32 : (i <= (Zlength (colors_l)))) (PreH33 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH34 : ((Zlength (seen_l)) = k_pre)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (i)) seen_l)) (PreH37 : ((Zlength (good_l)) = k_pre)) (PreH38 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l)) (PreH39 : (Forall ((GE.ge (α := Int)) (i)) good_l)) (PreH40 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l)) ,
  (intArray.full ( &( "seen" ) ) k_pre seen_l)
  ** (intArray.full ( &( "good" ) ) k_pre good_l)
  ** ((( &( "colors" ) )) # Ptr |-> (colors_pre))
  ** ((( &( "costs" ) )) # Ptr |-> (costs_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cost" ) )) # Int |-> (cost))
  ** ((( &( "answer" ) )) # Int64 |-> ((answer + (Znth c good_l (0 : Int)))))
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def countChoosingInns_safety_wit_13 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_next : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (c = (Znth i colors_l (0 : Int)))) (PreH2 : (cost = (Znth i costs_l (0 : Int)))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 50)) (PreH7 : ((0 : Int) <= p_pre)) (PreH8 : (p_pre <= 100)) (PreH9 : ((Zlength (colors_l)) = n_pre)) (PreH10 : ((Zlength (costs_l)) = n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH12 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH14 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) (PreH15 : ((0 : Int) <= i)) (PreH16 : (i < n_pre)) (PreH17 : ((0 : Int) <= c)) (PreH18 : (c < k_pre)) (PreH19 : ((0 : Int) <= answer)) (PreH20 : (answer <= 19999900000)) (PreH21 : ((0 : Int) <= (i + 1))) (PreH22 : ((i + 1) <= (Zlength (colors_l)))) (PreH23 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH24 : ((Zlength (seen_next)) = k_pre)) (PreH25 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_next)) (PreH26 : (Forall ((GE.ge (α := Int)) ((i + 1))) seen_next)) (PreH27 : ((Zlength (seen_next)) = k_pre)) (PreH28 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_next)) (PreH29 : (Forall ((GE.ge (α := Int)) ((i + 1))) seen_next)) (PreH30 : (InnsPrefixCounts colors_l costs_l (i + 1) k_pre p_pre answer seen_next seen_next)) ,
  ((( &( "colors" ) )) # Ptr |-> (colors_pre))
  ** ((( &( "costs" ) )) # Ptr |-> (costs_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int64 |-> (answer))
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full ( &( "seen" ) ) k_pre seen_next)
  ** (intArray.full ( &( "good" ) ) k_pre seen_next)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def countChoosingInns_safety_wit_14 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_next : (List Int)) (seen_l : (List Int)) (good_l : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (c = (Znth i colors_l (0 : Int)))) (PreH2 : (cost = (Znth i costs_l (0 : Int)))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 50)) (PreH7 : ((0 : Int) <= p_pre)) (PreH8 : (p_pre <= 100)) (PreH9 : ((Zlength (colors_l)) = n_pre)) (PreH10 : ((Zlength (costs_l)) = n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH12 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH14 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) (PreH15 : (p_pre < cost)) (PreH16 : (cost <= 100)) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i < n_pre)) (PreH19 : ((0 : Int) <= c)) (PreH20 : (c < k_pre)) (PreH21 : ((0 : Int) <= answer)) (PreH22 : (answer <= 19999900000)) (PreH23 : (seen_next = (replace_Znth (c) (((Znth c seen_l (0 : Int)) + 1)) (seen_l)))) (PreH24 : ((0 : Int) <= i)) (PreH25 : (i <= (Zlength (colors_l)))) (PreH26 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH27 : ((Zlength (seen_l)) = k_pre)) (PreH28 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l)) (PreH29 : (Forall ((GE.ge (α := Int)) (i)) seen_l)) (PreH30 : ((Zlength (good_l)) = k_pre)) (PreH31 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l)) (PreH32 : (Forall ((GE.ge (α := Int)) (i)) good_l)) (PreH33 : ((0 : Int) <= (i + 1))) (PreH34 : ((i + 1) <= (Zlength (colors_l)))) (PreH35 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH36 : ((Zlength (seen_next)) = k_pre)) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_next)) (PreH38 : (Forall ((GE.ge (α := Int)) ((i + 1))) seen_next)) (PreH39 : ((Zlength (good_l)) = k_pre)) (PreH40 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l)) (PreH41 : (Forall ((GE.ge (α := Int)) ((i + 1))) good_l)) (PreH42 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre (answer - (Znth c good_l (0 : Int))) seen_l good_l)) (PreH43 : (InnsPrefixCounts colors_l costs_l (i + 1) k_pre p_pre answer seen_next good_l)) ,
  ((( &( "colors" ) )) # Ptr |-> (colors_pre))
  ** ((( &( "costs" ) )) # Ptr |-> (costs_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "answer" ) )) # Int64 |-> (answer))
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full ( &( "seen" ) ) k_pre seen_next)
  ** (intArray.full ( &( "good" ) ) k_pre good_l)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def countChoosingInns_entail_wit_1 : Prop :=
  (
forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 50)) (PreH5 : ((0 : Int) <= p_pre)) (PreH6 : (p_pre <= 100)) (PreH7 : ((Zlength (colors_l)) = n_pre)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH10 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH12 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) ,
  (intArray.undef_full ( &( "good" ) ) 50)
  ** (intArray.undef_full ( &( "seen" ) ) 50)
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
|--
  “ ((0 : Int) = (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 50) ” &&
  “ ((0 : Int) <= p_pre) ” &&
  “ (p_pre <= 100) ” &&
  “ ((Zlength (colors_l)) = n_pre) ” &&
  “ ((Zlength (costs_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) costs_l) ”
  &&  (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.undef_full (( &( "seen" ) ) + ((0 : Int) * sizeof(INT))) k_pre)
  ** (intArray.undef_full (( &( "good" ) ) + ((0 : Int) * sizeof(INT))) k_pre)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)
) \/
(
forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 50)) (PreH5 : ((0 : Int) <= p_pre)) (PreH6 : (p_pre <= 100)) (PreH7 : ((Zlength (colors_l)) = n_pre)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH10 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH12 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) ,
  (intArray.undef_full ( &( "good" ) ) 50)
  ** (intArray.undef_full ( &( "seen" ) ) 50)
|--
  (intArray.undef_full (( &( "seen" ) ) + ((0 : Int) * sizeof(INT))) k_pre)
  ** (intArray.undef_full (( &( "good" ) ) + ((0 : Int) * sizeof(INT))) k_pre)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)
)

noncomputable def countChoosingInns_entail_wit_1_split_goal_spatial : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 200000)) (PreH3 : (1 <= k_pre)) (PreH4 : (k_pre <= 50)) (PreH5 : ((0 : Int) <= p_pre)) (PreH6 : (p_pre <= 100)) (PreH7 : ((Zlength (colors_l)) = n_pre)) (PreH8 : ((Zlength (costs_l)) = n_pre)) (PreH9 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH10 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH12 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) ,
  (intArray.undef_full ( &( "good" ) ) 50)
  ** (intArray.undef_full ( &( "seen" ) ) 50)
|--
  (intArray.undef_full (( &( "seen" ) ) + ((0 : Int) * sizeof(INT))) k_pre)
  ** (intArray.undef_full (( &( "good" ) ) + ((0 : Int) * sizeof(INT))) k_pre)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)

noncomputable def countChoosingInns_entail_wit_2 : Prop :=
  (
forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (answer : Int) (good_l_2 : (List Int)) (seen_l_2 : (List Int)) (PreH1 : ((Zlength (seen_l_2)) = k_pre)) (PreH2 : (Forall (Eq ((0 : Int))) seen_l_2)) (PreH3 : ((Zlength (good_l_2)) = k_pre)) (PreH4 : (Forall (Eq ((0 : Int))) good_l_2)) (PreH5 : (answer = (0 : Int))) (PreH6 : ((0 : Int) <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= 50)) (PreH10 : ((0 : Int) <= p_pre)) (PreH11 : (p_pre <= 100)) (PreH12 : ((Zlength (colors_l)) = n_pre)) (PreH13 : ((Zlength (costs_l)) = n_pre)) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH15 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH17 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) ,
  (intArray.full (( &( "seen" ) ) + ((0 : Int) * sizeof(INT))) k_pre seen_l_2)
  ** (intArray.full (( &( "good" ) ) + ((0 : Int) * sizeof(INT))) k_pre good_l_2)
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)
|--
  EX good_l : (List Int), EX seen_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 50) ” &&
  “ ((0 : Int) <= p_pre) ” &&
  “ (p_pre <= 100) ” &&
  “ ((Zlength (colors_l)) = n_pre) ” &&
  “ ((Zlength (costs_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) costs_l) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= 19999900000) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (Zlength (colors_l))) ” &&
  “ ((Zlength (costs_l)) = (Zlength (colors_l))) ” &&
  “ ((Zlength (seen_l)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((0 : Int))) seen_l) ” &&
  “ ((Zlength (good_l)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) good_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((0 : Int))) good_l) ” &&
  “ (InnsPrefixCounts colors_l costs_l (0 : Int) k_pre p_pre answer seen_l good_l) ”
  &&  (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full ( &( "seen" ) ) k_pre seen_l)
  ** (intArray.full ( &( "good" ) ) k_pre good_l)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)
) \/
(
forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (answer : Int) (good_l_2 : (List Int)) (seen_l_2 : (List Int)) (PreH1 : ((Zlength (seen_l_2)) = k_pre)) (PreH2 : (Forall (Eq ((0 : Int))) seen_l_2)) (PreH3 : ((Zlength (good_l_2)) = k_pre)) (PreH4 : (Forall (Eq ((0 : Int))) good_l_2)) (PreH5 : (answer = (0 : Int))) (PreH6 : ((0 : Int) <= n_pre)) (PreH7 : (n_pre <= 200000)) (PreH8 : (1 <= k_pre)) (PreH9 : (k_pre <= 50)) (PreH10 : ((0 : Int) <= p_pre)) (PreH11 : (p_pre <= 100)) (PreH12 : ((Zlength (colors_l)) = n_pre)) (PreH13 : ((Zlength (costs_l)) = n_pre)) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH15 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH16 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH17 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) ,
  (intArray.full (( &( "seen" ) ) + ((0 : Int) * sizeof(INT))) k_pre seen_l_2)
  ** (intArray.full (( &( "good" ) ) + ((0 : Int) * sizeof(INT))) k_pre good_l_2)
|--
  EX good_l : (List Int), EX seen_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 50) ” &&
  “ ((0 : Int) <= p_pre) ” &&
  “ (p_pre <= 100) ” &&
  “ ((Zlength (colors_l)) = n_pre) ” &&
  “ ((Zlength (costs_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) costs_l) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= 19999900000) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (Zlength (colors_l))) ” &&
  “ ((Zlength (costs_l)) = (Zlength (colors_l))) ” &&
  “ ((Zlength (seen_l)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((0 : Int))) seen_l) ” &&
  “ ((Zlength (good_l)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) good_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((0 : Int))) good_l) ” &&
  “ (InnsPrefixCounts colors_l costs_l (0 : Int) k_pre p_pre answer seen_l good_l) ”
  &&  (intArray.full ( &( "seen" ) ) k_pre seen_l)
  ** (intArray.full ( &( "good" ) ) k_pre good_l)
)

noncomputable def countChoosingInns_entail_wit_3 : Prop :=
  (
forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (good_l_2 : (List Int)) (seen_l_2 : (List Int)) (answer : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : ((0 : Int) <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH11 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH13 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((0 : Int) <= answer)) (PreH17 : (answer <= 19999900000)) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i <= (Zlength (colors_l)))) (PreH20 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH21 : ((Zlength (seen_l_2)) = k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l_2)) (PreH23 : (Forall ((GE.ge (α := Int)) (i)) seen_l_2)) (PreH24 : ((Zlength (good_l_2)) = k_pre)) (PreH25 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l_2)) (PreH26 : (Forall ((GE.ge (α := Int)) (i)) good_l_2)) (PreH27 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2)) ,
  (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full ( &( "seen" ) ) k_pre seen_l_2)
  ** (intArray.full ( &( "good" ) ) k_pre good_l_2)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)
|--
  EX good_l : (List Int), EX seen_l : (List Int),
  “ ((Znth i colors_l (0 : Int)) = (Znth i colors_l (0 : Int))) ” &&
  “ ((Znth i costs_l (0 : Int)) = (Znth i costs_l (0 : Int))) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 50) ” &&
  “ ((0 : Int) <= p_pre) ” &&
  “ (p_pre <= 100) ” &&
  “ ((Zlength (colors_l)) = n_pre) ” &&
  “ ((Zlength (costs_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) costs_l) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= (Znth i colors_l (0 : Int))) ” &&
  “ ((Znth i colors_l (0 : Int)) < k_pre) ” &&
  “ ((0 : Int) <= (Znth i costs_l (0 : Int))) ” &&
  “ ((Znth i costs_l (0 : Int)) <= 100) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= 19999900000) ” &&
  “ ((0 : Int) <= (Znth (Znth i colors_l (0 : Int)) seen_l (0 : Int))) ” &&
  “ ((Znth (Znth i colors_l (0 : Int)) seen_l (0 : Int)) <= i) ” &&
  “ ((0 : Int) <= (Znth (Znth i colors_l (0 : Int)) good_l (0 : Int))) ” &&
  “ ((Znth (Znth i colors_l (0 : Int)) good_l (0 : Int)) <= i) ” &&
  “ ((answer + (Znth (Znth i colors_l (0 : Int)) seen_l (0 : Int))) <= 9223372036854775807) ” &&
  “ ((answer + (Znth (Znth i colors_l (0 : Int)) good_l (0 : Int))) <= 9223372036854775807) ” &&
  “ (((Znth (Znth i colors_l (0 : Int)) seen_l (0 : Int)) + 1) <= INT_MAX) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (Zlength (colors_l))) ” &&
  “ ((Zlength (costs_l)) = (Zlength (colors_l))) ” &&
  “ ((Zlength (seen_l)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (i)) seen_l) ” &&
  “ ((Zlength (good_l)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) good_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (i)) good_l) ” &&
  “ (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l) ”
  &&  (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full ( &( "seen" ) ) k_pre seen_l)
  ** (intArray.full ( &( "good" ) ) k_pre good_l)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)
) \/
(
forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (good_l_2 : (List Int)) (seen_l_2 : (List Int)) (answer : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : ((0 : Int) <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH11 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH13 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((0 : Int) <= answer)) (PreH17 : (answer <= 19999900000)) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i <= (Zlength (colors_l)))) (PreH20 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH21 : ((Zlength (seen_l_2)) = k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l_2)) (PreH23 : (Forall ((GE.ge (α := Int)) (i)) seen_l_2)) (PreH24 : ((Zlength (good_l_2)) = k_pre)) (PreH25 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l_2)) (PreH26 : (Forall ((GE.ge (α := Int)) (i)) good_l_2)) (PreH27 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2)) ,
  TT && emp 
|--
  “ (((Znth (Znth i colors_l (0 : Int)) seen_l_2 (0 : Int)) + 1) <= INT_MAX) ” &&
  “ ((answer + (Znth (Znth i colors_l (0 : Int)) good_l_2 (0 : Int))) <= 9223372036854775807) ” &&
  “ ((answer + (Znth (Znth i colors_l (0 : Int)) seen_l_2 (0 : Int))) <= 9223372036854775807) ” &&
  “ ((Znth (Znth i colors_l (0 : Int)) good_l_2 (0 : Int)) <= i) ” &&
  “ ((0 : Int) <= (Znth (Znth i colors_l (0 : Int)) good_l_2 (0 : Int))) ” &&
  “ ((Znth (Znth i colors_l (0 : Int)) seen_l_2 (0 : Int)) <= i) ” &&
  “ ((0 : Int) <= (Znth (Znth i colors_l (0 : Int)) seen_l_2 (0 : Int))) ” &&
  “ ((Znth i costs_l (0 : Int)) <= 100) ” &&
  “ ((0 : Int) <= (Znth i costs_l (0 : Int))) ” &&
  “ ((Znth i colors_l (0 : Int)) < k_pre) ” &&
  “ ((0 : Int) <= (Znth i colors_l (0 : Int))) ”
  &&  emp
)

noncomputable def countChoosingInns_entail_wit_3_split_goal_1 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (good_l_2 : (List Int)) (seen_l_2 : (List Int)) (answer : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : ((0 : Int) <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH11 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH13 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((0 : Int) <= answer)) (PreH17 : (answer <= 19999900000)) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i <= (Zlength (colors_l)))) (PreH20 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH21 : ((Zlength (seen_l_2)) = k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l_2)) (PreH23 : (Forall ((GE.ge (α := Int)) (i)) seen_l_2)) (PreH24 : ((Zlength (good_l_2)) = k_pre)) (PreH25 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l_2)) (PreH26 : (Forall ((GE.ge (α := Int)) (i)) good_l_2)) (PreH27 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2)) ,
  (((Znth (Znth i colors_l (0 : Int)) seen_l_2 (0 : Int)) + 1) <= INT_MAX)

noncomputable def countChoosingInns_entail_wit_3_split_goal_2 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (good_l_2 : (List Int)) (seen_l_2 : (List Int)) (answer : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : ((0 : Int) <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH11 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH13 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((0 : Int) <= answer)) (PreH17 : (answer <= 19999900000)) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i <= (Zlength (colors_l)))) (PreH20 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH21 : ((Zlength (seen_l_2)) = k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l_2)) (PreH23 : (Forall ((GE.ge (α := Int)) (i)) seen_l_2)) (PreH24 : ((Zlength (good_l_2)) = k_pre)) (PreH25 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l_2)) (PreH26 : (Forall ((GE.ge (α := Int)) (i)) good_l_2)) (PreH27 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2)) ,
  ((answer + (Znth (Znth i colors_l (0 : Int)) good_l_2 (0 : Int))) <= 9223372036854775807)

noncomputable def countChoosingInns_entail_wit_3_split_goal_3 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (good_l_2 : (List Int)) (seen_l_2 : (List Int)) (answer : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : ((0 : Int) <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH11 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH13 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((0 : Int) <= answer)) (PreH17 : (answer <= 19999900000)) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i <= (Zlength (colors_l)))) (PreH20 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH21 : ((Zlength (seen_l_2)) = k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l_2)) (PreH23 : (Forall ((GE.ge (α := Int)) (i)) seen_l_2)) (PreH24 : ((Zlength (good_l_2)) = k_pre)) (PreH25 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l_2)) (PreH26 : (Forall ((GE.ge (α := Int)) (i)) good_l_2)) (PreH27 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2)) ,
  ((answer + (Znth (Znth i colors_l (0 : Int)) seen_l_2 (0 : Int))) <= 9223372036854775807)

noncomputable def countChoosingInns_entail_wit_3_split_goal_4 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (good_l_2 : (List Int)) (seen_l_2 : (List Int)) (answer : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : ((0 : Int) <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH11 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH13 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((0 : Int) <= answer)) (PreH17 : (answer <= 19999900000)) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i <= (Zlength (colors_l)))) (PreH20 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH21 : ((Zlength (seen_l_2)) = k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l_2)) (PreH23 : (Forall ((GE.ge (α := Int)) (i)) seen_l_2)) (PreH24 : ((Zlength (good_l_2)) = k_pre)) (PreH25 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l_2)) (PreH26 : (Forall ((GE.ge (α := Int)) (i)) good_l_2)) (PreH27 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2)) ,
  ((Znth (Znth i colors_l (0 : Int)) good_l_2 (0 : Int)) <= i)

noncomputable def countChoosingInns_entail_wit_3_split_goal_5 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (good_l_2 : (List Int)) (seen_l_2 : (List Int)) (answer : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : ((0 : Int) <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH11 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH13 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((0 : Int) <= answer)) (PreH17 : (answer <= 19999900000)) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i <= (Zlength (colors_l)))) (PreH20 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH21 : ((Zlength (seen_l_2)) = k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l_2)) (PreH23 : (Forall ((GE.ge (α := Int)) (i)) seen_l_2)) (PreH24 : ((Zlength (good_l_2)) = k_pre)) (PreH25 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l_2)) (PreH26 : (Forall ((GE.ge (α := Int)) (i)) good_l_2)) (PreH27 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2)) ,
  ((0 : Int) <= (Znth (Znth i colors_l (0 : Int)) good_l_2 (0 : Int)))

noncomputable def countChoosingInns_entail_wit_3_split_goal_6 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (good_l_2 : (List Int)) (seen_l_2 : (List Int)) (answer : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : ((0 : Int) <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH11 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH13 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((0 : Int) <= answer)) (PreH17 : (answer <= 19999900000)) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i <= (Zlength (colors_l)))) (PreH20 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH21 : ((Zlength (seen_l_2)) = k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l_2)) (PreH23 : (Forall ((GE.ge (α := Int)) (i)) seen_l_2)) (PreH24 : ((Zlength (good_l_2)) = k_pre)) (PreH25 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l_2)) (PreH26 : (Forall ((GE.ge (α := Int)) (i)) good_l_2)) (PreH27 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2)) ,
  ((Znth (Znth i colors_l (0 : Int)) seen_l_2 (0 : Int)) <= i)

noncomputable def countChoosingInns_entail_wit_3_split_goal_7 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (good_l_2 : (List Int)) (seen_l_2 : (List Int)) (answer : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : ((0 : Int) <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH11 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH13 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((0 : Int) <= answer)) (PreH17 : (answer <= 19999900000)) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i <= (Zlength (colors_l)))) (PreH20 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH21 : ((Zlength (seen_l_2)) = k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l_2)) (PreH23 : (Forall ((GE.ge (α := Int)) (i)) seen_l_2)) (PreH24 : ((Zlength (good_l_2)) = k_pre)) (PreH25 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l_2)) (PreH26 : (Forall ((GE.ge (α := Int)) (i)) good_l_2)) (PreH27 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2)) ,
  ((0 : Int) <= (Znth (Znth i colors_l (0 : Int)) seen_l_2 (0 : Int)))

noncomputable def countChoosingInns_entail_wit_3_split_goal_8 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (good_l_2 : (List Int)) (seen_l_2 : (List Int)) (answer : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : ((0 : Int) <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH11 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH13 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((0 : Int) <= answer)) (PreH17 : (answer <= 19999900000)) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i <= (Zlength (colors_l)))) (PreH20 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH21 : ((Zlength (seen_l_2)) = k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l_2)) (PreH23 : (Forall ((GE.ge (α := Int)) (i)) seen_l_2)) (PreH24 : ((Zlength (good_l_2)) = k_pre)) (PreH25 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l_2)) (PreH26 : (Forall ((GE.ge (α := Int)) (i)) good_l_2)) (PreH27 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2)) ,
  ((Znth i costs_l (0 : Int)) <= 100)

noncomputable def countChoosingInns_entail_wit_3_split_goal_9 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (good_l_2 : (List Int)) (seen_l_2 : (List Int)) (answer : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : ((0 : Int) <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH11 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH13 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((0 : Int) <= answer)) (PreH17 : (answer <= 19999900000)) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i <= (Zlength (colors_l)))) (PreH20 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH21 : ((Zlength (seen_l_2)) = k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l_2)) (PreH23 : (Forall ((GE.ge (α := Int)) (i)) seen_l_2)) (PreH24 : ((Zlength (good_l_2)) = k_pre)) (PreH25 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l_2)) (PreH26 : (Forall ((GE.ge (α := Int)) (i)) good_l_2)) (PreH27 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2)) ,
  ((0 : Int) <= (Znth i costs_l (0 : Int)))

noncomputable def countChoosingInns_entail_wit_3_split_goal_10 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (good_l_2 : (List Int)) (seen_l_2 : (List Int)) (answer : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : ((0 : Int) <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH11 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH13 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((0 : Int) <= answer)) (PreH17 : (answer <= 19999900000)) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i <= (Zlength (colors_l)))) (PreH20 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH21 : ((Zlength (seen_l_2)) = k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l_2)) (PreH23 : (Forall ((GE.ge (α := Int)) (i)) seen_l_2)) (PreH24 : ((Zlength (good_l_2)) = k_pre)) (PreH25 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l_2)) (PreH26 : (Forall ((GE.ge (α := Int)) (i)) good_l_2)) (PreH27 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2)) ,
  ((Znth i colors_l (0 : Int)) < k_pre)

noncomputable def countChoosingInns_entail_wit_3_split_goal_11 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (good_l_2 : (List Int)) (seen_l_2 : (List Int)) (answer : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : ((0 : Int) <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH11 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH13 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((0 : Int) <= answer)) (PreH17 : (answer <= 19999900000)) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i <= (Zlength (colors_l)))) (PreH20 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH21 : ((Zlength (seen_l_2)) = k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l_2)) (PreH23 : (Forall ((GE.ge (α := Int)) (i)) seen_l_2)) (PreH24 : ((Zlength (good_l_2)) = k_pre)) (PreH25 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l_2)) (PreH26 : (Forall ((GE.ge (α := Int)) (i)) good_l_2)) (PreH27 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l_2 good_l_2)) ,
  ((0 : Int) <= (Znth i colors_l (0 : Int)))

noncomputable def countChoosingInns_entail_wit_4 : Prop :=
  (
forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l : (List Int)) (good_l_2 : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (cost <= p_pre)) (PreH2 : (c = (Znth i colors_l (0 : Int)))) (PreH3 : (cost = (Znth i costs_l (0 : Int)))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : ((0 : Int) <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH13 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH15 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i < n_pre)) (PreH18 : ((0 : Int) <= c)) (PreH19 : (c < k_pre)) (PreH20 : ((0 : Int) <= cost)) (PreH21 : (cost <= 100)) (PreH22 : ((0 : Int) <= answer)) (PreH23 : (answer <= 19999900000)) (PreH24 : ((0 : Int) <= (Znth c seen_l (0 : Int)))) (PreH25 : ((Znth c seen_l (0 : Int)) <= i)) (PreH26 : ((0 : Int) <= (Znth c good_l_2 (0 : Int)))) (PreH27 : ((Znth c good_l_2 (0 : Int)) <= i)) (PreH28 : ((answer + (Znth c seen_l (0 : Int))) <= 9223372036854775807)) (PreH29 : ((answer + (Znth c good_l_2 (0 : Int))) <= 9223372036854775807)) (PreH30 : (((Znth c seen_l (0 : Int)) + 1) <= INT_MAX)) (PreH31 : ((0 : Int) <= i)) (PreH32 : (i <= (Zlength (colors_l)))) (PreH33 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH34 : ((Zlength (seen_l)) = k_pre)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (i)) seen_l)) (PreH37 : ((Zlength (good_l_2)) = k_pre)) (PreH38 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l_2)) (PreH39 : (Forall ((GE.ge (α := Int)) (i)) good_l_2)) (PreH40 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l_2)) ,
  (intArray.full ( &( "seen" ) ) k_pre (replace_Znth (c) (((Znth c seen_l (0 : Int)) + 1)) (seen_l)))
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full ( &( "good" ) ) k_pre good_l_2)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)
|--
  EX good_l : (List Int), EX seen_l_2 : (List Int), EX seen_next : (List Int),
  “ (c = (Znth i colors_l (0 : Int))) ” &&
  “ (cost = (Znth i costs_l (0 : Int))) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 50) ” &&
  “ ((0 : Int) <= p_pre) ” &&
  “ (p_pre <= 100) ” &&
  “ ((Zlength (colors_l)) = n_pre) ” &&
  “ ((Zlength (costs_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) costs_l) ” &&
  “ ((0 : Int) <= cost) ” &&
  “ (cost <= p_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c < k_pre) ” &&
  “ ((0 : Int) <= (answer + (Znth c seen_l (0 : Int)))) ” &&
  “ ((answer + (Znth c seen_l (0 : Int))) <= 19999900000) ” &&
  “ (seen_next = (replace_Znth (c) (((Znth c seen_l_2 (0 : Int)) + 1)) (seen_l_2))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (Zlength (colors_l))) ” &&
  “ ((Zlength (costs_l)) = (Zlength (colors_l))) ” &&
  “ ((Zlength (seen_l_2)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l_2) ” &&
  “ (Forall ((GE.ge (α := Int)) (i)) seen_l_2) ” &&
  “ ((Zlength (good_l)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) good_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (i)) good_l) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= (Zlength (colors_l))) ” &&
  “ ((Zlength (costs_l)) = (Zlength (colors_l))) ” &&
  “ ((Zlength (seen_next)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) seen_next) ” &&
  “ (Forall ((GE.ge (α := Int)) ((i + 1))) seen_next) ” &&
  “ ((Zlength (good_l)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) good_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((i + 1))) good_l) ” &&
  “ (InnsPrefixCounts colors_l costs_l i k_pre p_pre ((answer + (Znth c seen_l (0 : Int))) - (Znth c seen_l_2 (0 : Int))) seen_l_2 good_l) ” &&
  “ ((Zlength (seen_next)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) seen_next) ” &&
  “ (Forall ((GE.ge (α := Int)) (200000)) seen_next) ” &&
  “ ((Zlength (good_l)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) good_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (200000)) good_l) ”
  &&  (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full (( &( "seen" ) ) + ((0 : Int) * sizeof(INT))) k_pre seen_next)
  ** (intArray.full (( &( "good" ) ) + ((0 : Int) * sizeof(INT))) k_pre good_l)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)
) \/
(
forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l : (List Int)) (good_l_2 : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (cost <= p_pre)) (PreH2 : (c = (Znth i colors_l (0 : Int)))) (PreH3 : (cost = (Znth i costs_l (0 : Int)))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : ((0 : Int) <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH13 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH15 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i < n_pre)) (PreH18 : ((0 : Int) <= c)) (PreH19 : (c < k_pre)) (PreH20 : ((0 : Int) <= cost)) (PreH21 : (cost <= 100)) (PreH22 : ((0 : Int) <= answer)) (PreH23 : (answer <= 19999900000)) (PreH24 : ((0 : Int) <= (Znth c seen_l (0 : Int)))) (PreH25 : ((Znth c seen_l (0 : Int)) <= i)) (PreH26 : ((0 : Int) <= (Znth c good_l_2 (0 : Int)))) (PreH27 : ((Znth c good_l_2 (0 : Int)) <= i)) (PreH28 : ((answer + (Znth c seen_l (0 : Int))) <= 9223372036854775807)) (PreH29 : ((answer + (Znth c good_l_2 (0 : Int))) <= 9223372036854775807)) (PreH30 : (((Znth c seen_l (0 : Int)) + 1) <= INT_MAX)) (PreH31 : ((0 : Int) <= i)) (PreH32 : (i <= (Zlength (colors_l)))) (PreH33 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH34 : ((Zlength (seen_l)) = k_pre)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (i)) seen_l)) (PreH37 : ((Zlength (good_l_2)) = k_pre)) (PreH38 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l_2)) (PreH39 : (Forall ((GE.ge (α := Int)) (i)) good_l_2)) (PreH40 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l_2)) ,
  (intArray.full ( &( "seen" ) ) k_pre (replace_Znth (c) (((Znth c seen_l (0 : Int)) + 1)) (seen_l)))
  ** (intArray.full ( &( "good" ) ) k_pre good_l_2)
|--
  EX good_l : (List Int), EX seen_l_2 : (List Int),
  “ (c = (Znth i colors_l (0 : Int))) ” &&
  “ (cost = (Znth i costs_l (0 : Int))) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 50) ” &&
  “ ((0 : Int) <= p_pre) ” &&
  “ (p_pre <= 100) ” &&
  “ ((Zlength (colors_l)) = n_pre) ” &&
  “ ((Zlength (costs_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) costs_l) ” &&
  “ ((0 : Int) <= cost) ” &&
  “ (cost <= p_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c < k_pre) ” &&
  “ ((0 : Int) <= (answer + (Znth c seen_l (0 : Int)))) ” &&
  “ ((answer + (Znth c seen_l (0 : Int))) <= 19999900000) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (Zlength (colors_l))) ” &&
  “ ((Zlength (costs_l)) = (Zlength (colors_l))) ” &&
  “ ((Zlength (seen_l_2)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l_2) ” &&
  “ (Forall ((GE.ge (α := Int)) (i)) seen_l_2) ” &&
  “ ((Zlength (good_l)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) good_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (i)) good_l) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= (Zlength (colors_l))) ” &&
  “ ((Zlength (costs_l)) = (Zlength (colors_l))) ” &&
  “ ((Zlength ((replace_Znth (c) (((Znth c seen_l_2 (0 : Int)) + 1)) (seen_l_2)))) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (replace_Znth (c) (((Znth c seen_l_2 (0 : Int)) + 1)) (seen_l_2))) ” &&
  “ (Forall ((GE.ge (α := Int)) ((i + 1))) (replace_Znth (c) (((Znth c seen_l_2 (0 : Int)) + 1)) (seen_l_2))) ” &&
  “ ((Zlength (good_l)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) good_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((i + 1))) good_l) ” &&
  “ (InnsPrefixCounts colors_l costs_l i k_pre p_pre ((answer + (Znth c seen_l (0 : Int))) - (Znth c seen_l_2 (0 : Int))) seen_l_2 good_l) ” &&
  “ ((Zlength ((replace_Znth (c) (((Znth c seen_l_2 (0 : Int)) + 1)) (seen_l_2)))) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (replace_Znth (c) (((Znth c seen_l_2 (0 : Int)) + 1)) (seen_l_2))) ” &&
  “ (Forall ((GE.ge (α := Int)) (200000)) (replace_Znth (c) (((Znth c seen_l_2 (0 : Int)) + 1)) (seen_l_2))) ” &&
  “ ((Zlength (good_l)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) good_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (200000)) good_l) ”
  &&  (intArray.full (( &( "seen" ) ) + ((0 : Int) * sizeof(INT))) k_pre (replace_Znth (c) (((Znth c seen_l_2 (0 : Int)) + 1)) (seen_l_2)))
  ** (intArray.full (( &( "good" ) ) + ((0 : Int) * sizeof(INT))) k_pre good_l)
)

noncomputable def countChoosingInns_entail_wit_5 : Prop :=
  (
forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_next_2 : (List Int)) (seen_l : (List Int)) (good_l : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (c = (Znth i colors_l (0 : Int)))) (PreH2 : (cost = (Znth i costs_l (0 : Int)))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 50)) (PreH7 : ((0 : Int) <= p_pre)) (PreH8 : (p_pre <= 100)) (PreH9 : ((Zlength (colors_l)) = n_pre)) (PreH10 : ((Zlength (costs_l)) = n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH12 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH14 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) (PreH15 : ((0 : Int) <= cost)) (PreH16 : (cost <= p_pre)) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i < n_pre)) (PreH19 : ((0 : Int) <= c)) (PreH20 : (c < k_pre)) (PreH21 : ((0 : Int) <= answer)) (PreH22 : (answer <= 19999900000)) (PreH23 : (seen_next_2 = (replace_Znth (c) (((Znth c seen_l (0 : Int)) + 1)) (seen_l)))) (PreH24 : ((0 : Int) <= i)) (PreH25 : (i <= (Zlength (colors_l)))) (PreH26 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH27 : ((Zlength (seen_l)) = k_pre)) (PreH28 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l)) (PreH29 : (Forall ((GE.ge (α := Int)) (i)) seen_l)) (PreH30 : ((Zlength (good_l)) = k_pre)) (PreH31 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l)) (PreH32 : (Forall ((GE.ge (α := Int)) (i)) good_l)) (PreH33 : ((0 : Int) <= (i + 1))) (PreH34 : ((i + 1) <= (Zlength (colors_l)))) (PreH35 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH36 : ((Zlength (seen_next_2)) = k_pre)) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_next_2)) (PreH38 : (Forall ((GE.ge (α := Int)) ((i + 1))) seen_next_2)) (PreH39 : ((Zlength (good_l)) = k_pre)) (PreH40 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l)) (PreH41 : (Forall ((GE.ge (α := Int)) ((i + 1))) good_l)) (PreH42 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l (0 : Int))) seen_l good_l)) (PreH43 : ((Zlength (seen_next_2)) = k_pre)) (PreH44 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_next_2)) (PreH45 : (Forall ((GE.ge (α := Int)) (200000)) seen_next_2)) (PreH46 : ((Zlength (good_l)) = k_pre)) (PreH47 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l)) (PreH48 : (Forall ((GE.ge (α := Int)) (200000)) good_l)) ,
  (intArray.full (( &( "seen" ) ) + ((0 : Int) * sizeof(INT))) k_pre seen_next_2)
  ** (intArray.full (( &( "good" ) ) + ((0 : Int) * sizeof(INT))) k_pre seen_next_2)
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)
|--
  EX seen_next : (List Int),
  “ (c = (Znth i colors_l (0 : Int))) ” &&
  “ (cost = (Znth i costs_l (0 : Int))) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 50) ” &&
  “ ((0 : Int) <= p_pre) ” &&
  “ (p_pre <= 100) ” &&
  “ ((Zlength (colors_l)) = n_pre) ” &&
  “ ((Zlength (costs_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) costs_l) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c < k_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= 19999900000) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= (Zlength (colors_l))) ” &&
  “ ((Zlength (costs_l)) = (Zlength (colors_l))) ” &&
  “ ((Zlength (seen_next)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) seen_next) ” &&
  “ (Forall ((GE.ge (α := Int)) ((i + 1))) seen_next) ” &&
  “ ((Zlength (seen_next)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) seen_next) ” &&
  “ (Forall ((GE.ge (α := Int)) ((i + 1))) seen_next) ” &&
  “ (InnsPrefixCounts colors_l costs_l (i + 1) k_pre p_pre answer seen_next seen_next) ”
  &&  (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full ( &( "seen" ) ) k_pre seen_next)
  ** (intArray.full ( &( "good" ) ) k_pre seen_next)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)
) \/
(
forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_next_2 : (List Int)) (seen_l : (List Int)) (good_l : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (c = (Znth i colors_l (0 : Int)))) (PreH2 : (cost = (Znth i costs_l (0 : Int)))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 50)) (PreH7 : ((0 : Int) <= p_pre)) (PreH8 : (p_pre <= 100)) (PreH9 : ((Zlength (colors_l)) = n_pre)) (PreH10 : ((Zlength (costs_l)) = n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH12 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH14 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) (PreH15 : ((0 : Int) <= cost)) (PreH16 : (cost <= p_pre)) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i < n_pre)) (PreH19 : ((0 : Int) <= c)) (PreH20 : (c < k_pre)) (PreH21 : ((0 : Int) <= answer)) (PreH22 : (answer <= 19999900000)) (PreH23 : (seen_next_2 = (replace_Znth (c) (((Znth c seen_l (0 : Int)) + 1)) (seen_l)))) (PreH24 : ((0 : Int) <= i)) (PreH25 : (i <= (Zlength (colors_l)))) (PreH26 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH27 : ((Zlength (seen_l)) = k_pre)) (PreH28 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l)) (PreH29 : (Forall ((GE.ge (α := Int)) (i)) seen_l)) (PreH30 : ((Zlength (good_l)) = k_pre)) (PreH31 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l)) (PreH32 : (Forall ((GE.ge (α := Int)) (i)) good_l)) (PreH33 : ((0 : Int) <= (i + 1))) (PreH34 : ((i + 1) <= (Zlength (colors_l)))) (PreH35 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH36 : ((Zlength (seen_next_2)) = k_pre)) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_next_2)) (PreH38 : (Forall ((GE.ge (α := Int)) ((i + 1))) seen_next_2)) (PreH39 : ((Zlength (good_l)) = k_pre)) (PreH40 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l)) (PreH41 : (Forall ((GE.ge (α := Int)) ((i + 1))) good_l)) (PreH42 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l (0 : Int))) seen_l good_l)) (PreH43 : ((Zlength (seen_next_2)) = k_pre)) (PreH44 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_next_2)) (PreH45 : (Forall ((GE.ge (α := Int)) (200000)) seen_next_2)) (PreH46 : ((Zlength (good_l)) = k_pre)) (PreH47 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l)) (PreH48 : (Forall ((GE.ge (α := Int)) (200000)) good_l)) ,
  (intArray.full (( &( "seen" ) ) + ((0 : Int) * sizeof(INT))) k_pre seen_next_2)
  ** (intArray.full (( &( "good" ) ) + ((0 : Int) * sizeof(INT))) k_pre seen_next_2)
|--
  EX seen_next : (List Int),
  “ (c = (Znth i colors_l (0 : Int))) ” &&
  “ (cost = (Znth i costs_l (0 : Int))) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 50) ” &&
  “ ((0 : Int) <= p_pre) ” &&
  “ (p_pre <= 100) ” &&
  “ ((Zlength (colors_l)) = n_pre) ” &&
  “ ((Zlength (costs_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) costs_l) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c < k_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= 19999900000) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= (Zlength (colors_l))) ” &&
  “ ((Zlength (costs_l)) = (Zlength (colors_l))) ” &&
  “ ((Zlength (seen_next)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) seen_next) ” &&
  “ (Forall ((GE.ge (α := Int)) ((i + 1))) seen_next) ” &&
  “ ((Zlength (seen_next)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) seen_next) ” &&
  “ (Forall ((GE.ge (α := Int)) ((i + 1))) seen_next) ” &&
  “ (InnsPrefixCounts colors_l costs_l (i + 1) k_pre p_pre answer seen_next seen_next) ”
  &&  (intArray.full ( &( "seen" ) ) k_pre seen_next)
  ** (intArray.full ( &( "good" ) ) k_pre seen_next)
)

noncomputable def countChoosingInns_entail_wit_6 : Prop :=
  (
forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l_2 : (List Int)) (good_l : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (cost > p_pre)) (PreH2 : (c = (Znth i colors_l (0 : Int)))) (PreH3 : (cost = (Znth i costs_l (0 : Int)))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : ((0 : Int) <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH13 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH15 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i < n_pre)) (PreH18 : ((0 : Int) <= c)) (PreH19 : (c < k_pre)) (PreH20 : ((0 : Int) <= cost)) (PreH21 : (cost <= 100)) (PreH22 : ((0 : Int) <= answer)) (PreH23 : (answer <= 19999900000)) (PreH24 : ((0 : Int) <= (Znth c seen_l_2 (0 : Int)))) (PreH25 : ((Znth c seen_l_2 (0 : Int)) <= i)) (PreH26 : ((0 : Int) <= (Znth c good_l (0 : Int)))) (PreH27 : ((Znth c good_l (0 : Int)) <= i)) (PreH28 : ((answer + (Znth c seen_l_2 (0 : Int))) <= 9223372036854775807)) (PreH29 : ((answer + (Znth c good_l (0 : Int))) <= 9223372036854775807)) (PreH30 : (((Znth c seen_l_2 (0 : Int)) + 1) <= INT_MAX)) (PreH31 : ((0 : Int) <= i)) (PreH32 : (i <= (Zlength (colors_l)))) (PreH33 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH34 : ((Zlength (seen_l_2)) = k_pre)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l_2)) (PreH36 : (Forall ((GE.ge (α := Int)) (i)) seen_l_2)) (PreH37 : ((Zlength (good_l)) = k_pre)) (PreH38 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l)) (PreH39 : (Forall ((GE.ge (α := Int)) (i)) good_l)) (PreH40 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l_2 good_l)) ,
  (intArray.full ( &( "seen" ) ) k_pre (replace_Znth (c) (((Znth c seen_l_2 (0 : Int)) + 1)) (seen_l_2)))
  ** (intArray.full ( &( "good" ) ) k_pre good_l)
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)
|--
  EX good_l_2 : (List Int), EX seen_l : (List Int), EX seen_next : (List Int),
  “ (c = (Znth i colors_l (0 : Int))) ” &&
  “ (cost = (Znth i costs_l (0 : Int))) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 50) ” &&
  “ ((0 : Int) <= p_pre) ” &&
  “ (p_pre <= 100) ” &&
  “ ((Zlength (colors_l)) = n_pre) ” &&
  “ ((Zlength (costs_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) costs_l) ” &&
  “ (p_pre < cost) ” &&
  “ (cost <= 100) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c < k_pre) ” &&
  “ ((0 : Int) <= (answer + (Znth c good_l (0 : Int)))) ” &&
  “ ((answer + (Znth c good_l (0 : Int))) <= 19999900000) ” &&
  “ (seen_next = (replace_Znth (c) (((Znth c seen_l (0 : Int)) + 1)) (seen_l))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (Zlength (colors_l))) ” &&
  “ ((Zlength (costs_l)) = (Zlength (colors_l))) ” &&
  “ ((Zlength (seen_l)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (i)) seen_l) ” &&
  “ ((Zlength (good_l_2)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) good_l_2) ” &&
  “ (Forall ((GE.ge (α := Int)) (i)) good_l_2) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= (Zlength (colors_l))) ” &&
  “ ((Zlength (costs_l)) = (Zlength (colors_l))) ” &&
  “ ((Zlength (seen_next)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) seen_next) ” &&
  “ (Forall ((GE.ge (α := Int)) ((i + 1))) seen_next) ” &&
  “ ((Zlength (good_l_2)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) good_l_2) ” &&
  “ (Forall ((GE.ge (α := Int)) ((i + 1))) good_l_2) ” &&
  “ (InnsPrefixCounts colors_l costs_l i k_pre p_pre ((answer + (Znth c good_l (0 : Int))) - (Znth c good_l_2 (0 : Int))) seen_l good_l_2) ” &&
  “ (InnsPrefixCounts colors_l costs_l (i + 1) k_pre p_pre (answer + (Znth c good_l (0 : Int))) seen_next good_l_2) ”
  &&  (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full ( &( "seen" ) ) k_pre seen_next)
  ** (intArray.full ( &( "good" ) ) k_pre good_l_2)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)
) \/
(
forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l_2 : (List Int)) (good_l : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (cost > p_pre)) (PreH2 : (c = (Znth i colors_l (0 : Int)))) (PreH3 : (cost = (Znth i costs_l (0 : Int)))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : ((0 : Int) <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH13 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH15 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i < n_pre)) (PreH18 : ((0 : Int) <= c)) (PreH19 : (c < k_pre)) (PreH20 : ((0 : Int) <= cost)) (PreH21 : (cost <= 100)) (PreH22 : ((0 : Int) <= answer)) (PreH23 : (answer <= 19999900000)) (PreH24 : ((0 : Int) <= (Znth c seen_l_2 (0 : Int)))) (PreH25 : ((Znth c seen_l_2 (0 : Int)) <= i)) (PreH26 : ((0 : Int) <= (Znth c good_l (0 : Int)))) (PreH27 : ((Znth c good_l (0 : Int)) <= i)) (PreH28 : ((answer + (Znth c seen_l_2 (0 : Int))) <= 9223372036854775807)) (PreH29 : ((answer + (Znth c good_l (0 : Int))) <= 9223372036854775807)) (PreH30 : (((Znth c seen_l_2 (0 : Int)) + 1) <= INT_MAX)) (PreH31 : ((0 : Int) <= i)) (PreH32 : (i <= (Zlength (colors_l)))) (PreH33 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH34 : ((Zlength (seen_l_2)) = k_pre)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l_2)) (PreH36 : (Forall ((GE.ge (α := Int)) (i)) seen_l_2)) (PreH37 : ((Zlength (good_l)) = k_pre)) (PreH38 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l)) (PreH39 : (Forall ((GE.ge (α := Int)) (i)) good_l)) (PreH40 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l_2 good_l)) ,
  TT && emp 
|--
  EX seen_l : (List Int),
  “ ((replace_Znth ((Znth i colors_l (0 : Int))) (((Znth (Znth i colors_l (0 : Int)) seen_l_2 (0 : Int)) + 1)) (seen_l_2)) = (replace_Znth ((Znth i colors_l (0 : Int))) (((Znth (Znth i colors_l (0 : Int)) seen_l (0 : Int)) + 1)) (seen_l))) ” &&
  “ (p_pre < (Znth i costs_l (0 : Int))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ ((0 : Int) <= (answer + (Znth (Znth i colors_l (0 : Int)) good_l (0 : Int)))) ” &&
  “ ((answer + (Znth (Znth i colors_l (0 : Int)) good_l (0 : Int))) <= 19999900000) ” &&
  “ ((0 : Int) <= i) ” &&
  “ ((Zlength (seen_l)) = (Zlength (seen_l_2))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (i)) seen_l) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= (Zlength (colors_l))) ” &&
  “ ((Zlength ((replace_Znth ((Znth i colors_l (0 : Int))) (((Znth (Znth i colors_l (0 : Int)) seen_l (0 : Int)) + 1)) (seen_l)))) = (Zlength (seen_l_2))) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) (replace_Znth ((Znth i colors_l (0 : Int))) (((Znth (Znth i colors_l (0 : Int)) seen_l (0 : Int)) + 1)) (seen_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) ((i + 1))) (replace_Znth ((Znth i colors_l (0 : Int))) (((Znth (Znth i colors_l (0 : Int)) seen_l (0 : Int)) + 1)) (seen_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) ((i + 1))) good_l) ” &&
  “ (InnsPrefixCounts colors_l costs_l i (Zlength (seen_l_2)) p_pre ((answer + (Znth (Znth i colors_l (0 : Int)) good_l (0 : Int))) - (Znth (Znth i colors_l (0 : Int)) good_l (0 : Int))) seen_l good_l) ” &&
  “ (InnsPrefixCounts colors_l costs_l (i + 1) (Zlength (seen_l_2)) p_pre (answer + (Znth (Znth i colors_l (0 : Int)) good_l (0 : Int))) (replace_Znth ((Znth i colors_l (0 : Int))) (((Znth (Znth i colors_l (0 : Int)) seen_l (0 : Int)) + 1)) (seen_l)) good_l) ”
  &&  emp
)

noncomputable def countChoosingInns_entail_wit_7_1 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_next : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (c = (Znth i colors_l (0 : Int)))) (PreH2 : (cost = (Znth i costs_l (0 : Int)))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 50)) (PreH7 : ((0 : Int) <= p_pre)) (PreH8 : (p_pre <= 100)) (PreH9 : ((Zlength (colors_l)) = n_pre)) (PreH10 : ((Zlength (costs_l)) = n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH12 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH14 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) (PreH15 : ((0 : Int) <= i)) (PreH16 : (i < n_pre)) (PreH17 : ((0 : Int) <= c)) (PreH18 : (c < k_pre)) (PreH19 : ((0 : Int) <= answer)) (PreH20 : (answer <= 19999900000)) (PreH21 : ((0 : Int) <= (i + 1))) (PreH22 : ((i + 1) <= (Zlength (colors_l)))) (PreH23 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH24 : ((Zlength (seen_next)) = k_pre)) (PreH25 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_next)) (PreH26 : (Forall ((GE.ge (α := Int)) ((i + 1))) seen_next)) (PreH27 : ((Zlength (seen_next)) = k_pre)) (PreH28 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_next)) (PreH29 : (Forall ((GE.ge (α := Int)) ((i + 1))) seen_next)) (PreH30 : (InnsPrefixCounts colors_l costs_l (i + 1) k_pre p_pre answer seen_next seen_next)) ,
  (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full ( &( "seen" ) ) k_pre seen_next)
  ** (intArray.full ( &( "good" ) ) k_pre seen_next)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)
|--
  EX good_l : (List Int), EX seen_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 50) ” &&
  “ ((0 : Int) <= p_pre) ” &&
  “ (p_pre <= 100) ” &&
  “ ((Zlength (colors_l)) = n_pre) ” &&
  “ ((Zlength (costs_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) costs_l) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= 19999900000) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= (Zlength (colors_l))) ” &&
  “ ((Zlength (costs_l)) = (Zlength (colors_l))) ” &&
  “ ((Zlength (seen_l)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((i + 1))) seen_l) ” &&
  “ ((Zlength (good_l)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) good_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((i + 1))) good_l) ” &&
  “ (InnsPrefixCounts colors_l costs_l (i + 1) k_pre p_pre answer seen_l good_l) ”
  &&  (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full ( &( "seen" ) ) k_pre seen_l)
  ** (intArray.full ( &( "good" ) ) k_pre good_l)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)

noncomputable def countChoosingInns_entail_wit_7_2 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_next : (List Int)) (seen_l_2 : (List Int)) (good_l_2 : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (c = (Znth i colors_l (0 : Int)))) (PreH2 : (cost = (Znth i costs_l (0 : Int)))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 50)) (PreH7 : ((0 : Int) <= p_pre)) (PreH8 : (p_pre <= 100)) (PreH9 : ((Zlength (colors_l)) = n_pre)) (PreH10 : ((Zlength (costs_l)) = n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH12 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH14 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) (PreH15 : (p_pre < cost)) (PreH16 : (cost <= 100)) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i < n_pre)) (PreH19 : ((0 : Int) <= c)) (PreH20 : (c < k_pre)) (PreH21 : ((0 : Int) <= answer)) (PreH22 : (answer <= 19999900000)) (PreH23 : (seen_next = (replace_Znth (c) (((Znth c seen_l_2 (0 : Int)) + 1)) (seen_l_2)))) (PreH24 : ((0 : Int) <= i)) (PreH25 : (i <= (Zlength (colors_l)))) (PreH26 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH27 : ((Zlength (seen_l_2)) = k_pre)) (PreH28 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l_2)) (PreH29 : (Forall ((GE.ge (α := Int)) (i)) seen_l_2)) (PreH30 : ((Zlength (good_l_2)) = k_pre)) (PreH31 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l_2)) (PreH32 : (Forall ((GE.ge (α := Int)) (i)) good_l_2)) (PreH33 : ((0 : Int) <= (i + 1))) (PreH34 : ((i + 1) <= (Zlength (colors_l)))) (PreH35 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH36 : ((Zlength (seen_next)) = k_pre)) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_next)) (PreH38 : (Forall ((GE.ge (α := Int)) ((i + 1))) seen_next)) (PreH39 : ((Zlength (good_l_2)) = k_pre)) (PreH40 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l_2)) (PreH41 : (Forall ((GE.ge (α := Int)) ((i + 1))) good_l_2)) (PreH42 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre (answer - (Znth c good_l_2 (0 : Int))) seen_l_2 good_l_2)) (PreH43 : (InnsPrefixCounts colors_l costs_l (i + 1) k_pre p_pre answer seen_next good_l_2)) ,
  (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full ( &( "seen" ) ) k_pre seen_next)
  ** (intArray.full ( &( "good" ) ) k_pre good_l_2)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)
|--
  EX good_l : (List Int), EX seen_l : (List Int),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 50) ” &&
  “ ((0 : Int) <= p_pre) ” &&
  “ (p_pre <= 100) ” &&
  “ ((Zlength (colors_l)) = n_pre) ” &&
  “ ((Zlength (costs_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) costs_l) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= 19999900000) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= (Zlength (colors_l))) ” &&
  “ ((Zlength (costs_l)) = (Zlength (colors_l))) ” &&
  “ ((Zlength (seen_l)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((i + 1))) seen_l) ” &&
  “ ((Zlength (good_l)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) good_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((i + 1))) good_l) ” &&
  “ (InnsPrefixCounts colors_l costs_l (i + 1) k_pre p_pre answer seen_l good_l) ”
  &&  (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full ( &( "seen" ) ) k_pre seen_l)
  ** (intArray.full ( &( "good" ) ) k_pre good_l)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)

noncomputable def countChoosingInns_entail_wit_8 : Prop :=
  (
forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (good_l : (List Int)) (seen_l : (List Int)) (answer : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : ((0 : Int) <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH11 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH13 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((0 : Int) <= answer)) (PreH17 : (answer <= 19999900000)) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i <= (Zlength (colors_l)))) (PreH20 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH21 : ((Zlength (seen_l)) = k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l)) (PreH23 : (Forall ((GE.ge (α := Int)) (i)) seen_l)) (PreH24 : ((Zlength (good_l)) = k_pre)) (PreH25 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l)) (PreH26 : (Forall ((GE.ge (α := Int)) (i)) good_l)) (PreH27 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l)) ,
  (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full ( &( "seen" ) ) k_pre seen_l)
  ** (intArray.full ( &( "good" ) ) k_pre good_l)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)
|--
  “ (InnsPairAnswer colors_l costs_l n_pre p_pre answer) ”
  &&  (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.undef_full ( &( "seen" ) ) 50)
  ** (intArray.undef_full ( &( "good" ) ) 50)
) \/
(
forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (good_l : (List Int)) (seen_l : (List Int)) (answer : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : ((0 : Int) <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH11 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH13 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((0 : Int) <= answer)) (PreH17 : (answer <= 19999900000)) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i <= (Zlength (colors_l)))) (PreH20 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH21 : ((Zlength (seen_l)) = k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l)) (PreH23 : (Forall ((GE.ge (α := Int)) (i)) seen_l)) (PreH24 : ((Zlength (good_l)) = k_pre)) (PreH25 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l)) (PreH26 : (Forall ((GE.ge (α := Int)) (i)) good_l)) (PreH27 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l)) ,
  (intArray.full ( &( "seen" ) ) k_pre seen_l)
  ** (intArray.full ( &( "good" ) ) k_pre good_l)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)
|--
  “ (InnsPairAnswer colors_l costs_l n_pre p_pre answer) ”
  &&  (intArray.undef_full ( &( "seen" ) ) 50)
  ** (intArray.undef_full ( &( "good" ) ) 50)
)

noncomputable def countChoosingInns_entail_wit_8_split_goal_1 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (good_l : (List Int)) (seen_l : (List Int)) (answer : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : ((0 : Int) <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH11 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH13 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((0 : Int) <= answer)) (PreH17 : (answer <= 19999900000)) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i <= (Zlength (colors_l)))) (PreH20 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH21 : ((Zlength (seen_l)) = k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l)) (PreH23 : (Forall ((GE.ge (α := Int)) (i)) seen_l)) (PreH24 : ((Zlength (good_l)) = k_pre)) (PreH25 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l)) (PreH26 : (Forall ((GE.ge (α := Int)) (i)) good_l)) (PreH27 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l)) ,
  (intArray.full ( &( "seen" ) ) k_pre seen_l)
  ** (intArray.full ( &( "good" ) ) k_pre good_l)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)
|--
  “ (InnsPairAnswer colors_l costs_l n_pre p_pre answer) ”

noncomputable def countChoosingInns_entail_wit_8_split_goal_spatial : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (good_l : (List Int)) (seen_l : (List Int)) (answer : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : ((0 : Int) <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH11 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH13 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((0 : Int) <= answer)) (PreH17 : (answer <= 19999900000)) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i <= (Zlength (colors_l)))) (PreH20 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH21 : ((Zlength (seen_l)) = k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l)) (PreH23 : (Forall ((GE.ge (α := Int)) (i)) seen_l)) (PreH24 : ((Zlength (good_l)) = k_pre)) (PreH25 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l)) (PreH26 : (Forall ((GE.ge (α := Int)) (i)) good_l)) (PreH27 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l)) ,
  (intArray.full ( &( "seen" ) ) k_pre seen_l)
  ** (intArray.full ( &( "good" ) ) k_pre good_l)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)
|--
  (intArray.undef_full ( &( "seen" ) ) 50)
  ** (intArray.undef_full ( &( "good" ) ) 50)

noncomputable def countChoosingInns_return_wit_1 : Prop :=
  forall (p_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (answer : Int) (PreH1 : (InnsPairAnswer colors_l costs_l n_pre p_pre answer)) ,
  (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
|--
  “ (InnsPairAnswer colors_l costs_l n_pre p_pre answer) ”
  &&  (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)

noncomputable def countChoosingInns_partial_solve_wit_1_pure : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (answer : Int) (PreH1 : (answer = (0 : Int))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : ((0 : Int) <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH11 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH13 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) ,
  ((( &( "colors" ) )) # Ptr |-> (colors_pre))
  ** ((( &( "costs" ) )) # Ptr |-> (costs_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "answer" ) )) # Int64 |-> (answer))
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.undef_full (( &( "seen" ) ) + ((0 : Int) * sizeof(INT))) k_pre)
  ** (intArray.undef_full (( &( "good" ) ) + ((0 : Int) * sizeof(INT))) k_pre)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)
|--
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 50) ”

noncomputable def countChoosingInns_partial_solve_wit_1_aux : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (answer : Int) (PreH1 : (answer = (0 : Int))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : ((0 : Int) <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH11 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH13 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) ,
  (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.undef_full (( &( "seen" ) ) + ((0 : Int) * sizeof(INT))) k_pre)
  ** (intArray.undef_full (( &( "good" ) ) + ((0 : Int) * sizeof(INT))) k_pre)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)
|--
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 50) ” &&
  “ (answer = (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 50) ” &&
  “ ((0 : Int) <= p_pre) ” &&
  “ (p_pre <= 100) ” &&
  “ ((Zlength (colors_l)) = n_pre) ” &&
  “ ((Zlength (costs_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) costs_l) ”
  &&  (intArray.undef_full (( &( "seen" ) ) + ((0 : Int) * sizeof(INT))) k_pre)
  ** (intArray.undef_full (( &( "good" ) ) + ((0 : Int) * sizeof(INT))) k_pre)
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)

noncomputable def countChoosingInns_partial_solve_wit_1 : Prop := countChoosingInns_partial_solve_wit_1_pure -> countChoosingInns_partial_solve_wit_1_aux

noncomputable def countChoosingInns_partial_solve_wit_2 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (good_l : (List Int)) (seen_l : (List Int)) (answer : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : ((0 : Int) <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH11 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH13 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((0 : Int) <= answer)) (PreH17 : (answer <= 19999900000)) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i <= (Zlength (colors_l)))) (PreH20 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH21 : ((Zlength (seen_l)) = k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l)) (PreH23 : (Forall ((GE.ge (α := Int)) (i)) seen_l)) (PreH24 : ((Zlength (good_l)) = k_pre)) (PreH25 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l)) (PreH26 : (Forall ((GE.ge (α := Int)) (i)) good_l)) (PreH27 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l)) ,
  (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full ( &( "seen" ) ) k_pre seen_l)
  ** (intArray.full ( &( "good" ) ) k_pre good_l)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)
|--
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 50) ” &&
  “ ((0 : Int) <= p_pre) ” &&
  “ (p_pre <= 100) ” &&
  “ ((Zlength (colors_l)) = n_pre) ” &&
  “ ((Zlength (costs_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) costs_l) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= 19999900000) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (Zlength (colors_l))) ” &&
  “ ((Zlength (costs_l)) = (Zlength (colors_l))) ” &&
  “ ((Zlength (seen_l)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (i)) seen_l) ” &&
  “ ((Zlength (good_l)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) good_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (i)) good_l) ” &&
  “ (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l) ”
  &&  (((colors_pre + (i * sizeof(INT)))) # Int |-> ((Znth i colors_l (0 : Int))))
  ** (intArray.missing_i colors_pre i (0 : Int) n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full ( &( "seen" ) ) k_pre seen_l)
  ** (intArray.full ( &( "good" ) ) k_pre good_l)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)

noncomputable def countChoosingInns_partial_solve_wit_3 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (good_l : (List Int)) (seen_l : (List Int)) (answer : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 200000)) (PreH4 : (1 <= k_pre)) (PreH5 : (k_pre <= 50)) (PreH6 : ((0 : Int) <= p_pre)) (PreH7 : (p_pre <= 100)) (PreH8 : ((Zlength (colors_l)) = n_pre)) (PreH9 : ((Zlength (costs_l)) = n_pre)) (PreH10 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH11 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH13 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) (PreH14 : ((0 : Int) <= i)) (PreH15 : (i <= n_pre)) (PreH16 : ((0 : Int) <= answer)) (PreH17 : (answer <= 19999900000)) (PreH18 : ((0 : Int) <= i)) (PreH19 : (i <= (Zlength (colors_l)))) (PreH20 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH21 : ((Zlength (seen_l)) = k_pre)) (PreH22 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l)) (PreH23 : (Forall ((GE.ge (α := Int)) (i)) seen_l)) (PreH24 : ((Zlength (good_l)) = k_pre)) (PreH25 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l)) (PreH26 : (Forall ((GE.ge (α := Int)) (i)) good_l)) (PreH27 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l)) ,
  (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full ( &( "seen" ) ) k_pre seen_l)
  ** (intArray.full ( &( "good" ) ) k_pre good_l)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)
|--
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 50) ” &&
  “ ((0 : Int) <= p_pre) ” &&
  “ (p_pre <= 100) ” &&
  “ ((Zlength (colors_l)) = n_pre) ” &&
  “ ((Zlength (costs_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) costs_l) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= 19999900000) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (Zlength (colors_l))) ” &&
  “ ((Zlength (costs_l)) = (Zlength (colors_l))) ” &&
  “ ((Zlength (seen_l)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (i)) seen_l) ” &&
  “ ((Zlength (good_l)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) good_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (i)) good_l) ” &&
  “ (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l) ”
  &&  (((costs_pre + (i * sizeof(INT)))) # Int |-> ((Znth i costs_l (0 : Int))))
  ** (intArray.missing_i costs_pre i (0 : Int) n_pre costs_l)
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full ( &( "seen" ) ) k_pre seen_l)
  ** (intArray.full ( &( "good" ) ) k_pre good_l)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)

noncomputable def countChoosingInns_partial_solve_wit_4 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l : (List Int)) (good_l : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (cost <= p_pre)) (PreH2 : (c = (Znth i colors_l (0 : Int)))) (PreH3 : (cost = (Znth i costs_l (0 : Int)))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : ((0 : Int) <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH13 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH15 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i < n_pre)) (PreH18 : ((0 : Int) <= c)) (PreH19 : (c < k_pre)) (PreH20 : ((0 : Int) <= cost)) (PreH21 : (cost <= 100)) (PreH22 : ((0 : Int) <= answer)) (PreH23 : (answer <= 19999900000)) (PreH24 : ((0 : Int) <= (Znth c seen_l (0 : Int)))) (PreH25 : ((Znth c seen_l (0 : Int)) <= i)) (PreH26 : ((0 : Int) <= (Znth c good_l (0 : Int)))) (PreH27 : ((Znth c good_l (0 : Int)) <= i)) (PreH28 : ((answer + (Znth c seen_l (0 : Int))) <= 9223372036854775807)) (PreH29 : ((answer + (Znth c good_l (0 : Int))) <= 9223372036854775807)) (PreH30 : (((Znth c seen_l (0 : Int)) + 1) <= INT_MAX)) (PreH31 : ((0 : Int) <= i)) (PreH32 : (i <= (Zlength (colors_l)))) (PreH33 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH34 : ((Zlength (seen_l)) = k_pre)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (i)) seen_l)) (PreH37 : ((Zlength (good_l)) = k_pre)) (PreH38 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l)) (PreH39 : (Forall ((GE.ge (α := Int)) (i)) good_l)) (PreH40 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l)) ,
  (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full ( &( "seen" ) ) k_pre seen_l)
  ** (intArray.full ( &( "good" ) ) k_pre good_l)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)
|--
  “ (cost <= p_pre) ” &&
  “ (c = (Znth i colors_l (0 : Int))) ” &&
  “ (cost = (Znth i costs_l (0 : Int))) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 50) ” &&
  “ ((0 : Int) <= p_pre) ” &&
  “ (p_pre <= 100) ” &&
  “ ((Zlength (colors_l)) = n_pre) ” &&
  “ ((Zlength (costs_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) costs_l) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c < k_pre) ” &&
  “ ((0 : Int) <= cost) ” &&
  “ (cost <= 100) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= 19999900000) ” &&
  “ ((0 : Int) <= (Znth c seen_l (0 : Int))) ” &&
  “ ((Znth c seen_l (0 : Int)) <= i) ” &&
  “ ((0 : Int) <= (Znth c good_l (0 : Int))) ” &&
  “ ((Znth c good_l (0 : Int)) <= i) ” &&
  “ ((answer + (Znth c seen_l (0 : Int))) <= 9223372036854775807) ” &&
  “ ((answer + (Znth c good_l (0 : Int))) <= 9223372036854775807) ” &&
  “ (((Znth c seen_l (0 : Int)) + 1) <= INT_MAX) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (Zlength (colors_l))) ” &&
  “ ((Zlength (costs_l)) = (Zlength (colors_l))) ” &&
  “ ((Zlength (seen_l)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (i)) seen_l) ” &&
  “ ((Zlength (good_l)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) good_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (i)) good_l) ” &&
  “ (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l) ”
  &&  (((( &( "seen" ) ) + (c * sizeof(INT)))) # Int |-> ((Znth c seen_l (0 : Int))))
  ** (intArray.missing_i ( &( "seen" ) ) c (0 : Int) k_pre seen_l)
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full ( &( "good" ) ) k_pre good_l)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)

noncomputable def countChoosingInns_partial_solve_wit_5 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l : (List Int)) (good_l : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (cost <= p_pre)) (PreH2 : (c = (Znth i colors_l (0 : Int)))) (PreH3 : (cost = (Znth i costs_l (0 : Int)))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : ((0 : Int) <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH13 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH15 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i < n_pre)) (PreH18 : ((0 : Int) <= c)) (PreH19 : (c < k_pre)) (PreH20 : ((0 : Int) <= cost)) (PreH21 : (cost <= 100)) (PreH22 : ((0 : Int) <= answer)) (PreH23 : (answer <= 19999900000)) (PreH24 : ((0 : Int) <= (Znth c seen_l (0 : Int)))) (PreH25 : ((Znth c seen_l (0 : Int)) <= i)) (PreH26 : ((0 : Int) <= (Znth c good_l (0 : Int)))) (PreH27 : ((Znth c good_l (0 : Int)) <= i)) (PreH28 : ((answer + (Znth c seen_l (0 : Int))) <= 9223372036854775807)) (PreH29 : ((answer + (Znth c good_l (0 : Int))) <= 9223372036854775807)) (PreH30 : (((Znth c seen_l (0 : Int)) + 1) <= INT_MAX)) (PreH31 : ((0 : Int) <= i)) (PreH32 : (i <= (Zlength (colors_l)))) (PreH33 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH34 : ((Zlength (seen_l)) = k_pre)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (i)) seen_l)) (PreH37 : ((Zlength (good_l)) = k_pre)) (PreH38 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l)) (PreH39 : (Forall ((GE.ge (α := Int)) (i)) good_l)) (PreH40 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l)) ,
  (intArray.full ( &( "seen" ) ) k_pre seen_l)
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full ( &( "good" ) ) k_pre good_l)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)
|--
  “ (cost <= p_pre) ” &&
  “ (c = (Znth i colors_l (0 : Int))) ” &&
  “ (cost = (Znth i costs_l (0 : Int))) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 50) ” &&
  “ ((0 : Int) <= p_pre) ” &&
  “ (p_pre <= 100) ” &&
  “ ((Zlength (colors_l)) = n_pre) ” &&
  “ ((Zlength (costs_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) costs_l) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c < k_pre) ” &&
  “ ((0 : Int) <= cost) ” &&
  “ (cost <= 100) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= 19999900000) ” &&
  “ ((0 : Int) <= (Znth c seen_l (0 : Int))) ” &&
  “ ((Znth c seen_l (0 : Int)) <= i) ” &&
  “ ((0 : Int) <= (Znth c good_l (0 : Int))) ” &&
  “ ((Znth c good_l (0 : Int)) <= i) ” &&
  “ ((answer + (Znth c seen_l (0 : Int))) <= 9223372036854775807) ” &&
  “ ((answer + (Znth c good_l (0 : Int))) <= 9223372036854775807) ” &&
  “ (((Znth c seen_l (0 : Int)) + 1) <= INT_MAX) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (Zlength (colors_l))) ” &&
  “ ((Zlength (costs_l)) = (Zlength (colors_l))) ” &&
  “ ((Zlength (seen_l)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (i)) seen_l) ” &&
  “ ((Zlength (good_l)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) good_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (i)) good_l) ” &&
  “ (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l) ”
  &&  (((( &( "seen" ) ) + (c * sizeof(INT)))) # Int |-> ((Znth c seen_l (0 : Int))))
  ** (intArray.missing_i ( &( "seen" ) ) c (0 : Int) k_pre seen_l)
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full ( &( "good" ) ) k_pre good_l)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)

noncomputable def countChoosingInns_partial_solve_wit_6 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l : (List Int)) (good_l : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (cost <= p_pre)) (PreH2 : (c = (Znth i colors_l (0 : Int)))) (PreH3 : (cost = (Znth i costs_l (0 : Int)))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : ((0 : Int) <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH13 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH15 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i < n_pre)) (PreH18 : ((0 : Int) <= c)) (PreH19 : (c < k_pre)) (PreH20 : ((0 : Int) <= cost)) (PreH21 : (cost <= 100)) (PreH22 : ((0 : Int) <= answer)) (PreH23 : (answer <= 19999900000)) (PreH24 : ((0 : Int) <= (Znth c seen_l (0 : Int)))) (PreH25 : ((Znth c seen_l (0 : Int)) <= i)) (PreH26 : ((0 : Int) <= (Znth c good_l (0 : Int)))) (PreH27 : ((Znth c good_l (0 : Int)) <= i)) (PreH28 : ((answer + (Znth c seen_l (0 : Int))) <= 9223372036854775807)) (PreH29 : ((answer + (Znth c good_l (0 : Int))) <= 9223372036854775807)) (PreH30 : (((Znth c seen_l (0 : Int)) + 1) <= INT_MAX)) (PreH31 : ((0 : Int) <= i)) (PreH32 : (i <= (Zlength (colors_l)))) (PreH33 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH34 : ((Zlength (seen_l)) = k_pre)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (i)) seen_l)) (PreH37 : ((Zlength (good_l)) = k_pre)) (PreH38 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l)) (PreH39 : (Forall ((GE.ge (α := Int)) (i)) good_l)) (PreH40 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l)) ,
  (intArray.full ( &( "seen" ) ) k_pre seen_l)
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full ( &( "good" ) ) k_pre good_l)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)
|--
  “ (cost <= p_pre) ” &&
  “ (c = (Znth i colors_l (0 : Int))) ” &&
  “ (cost = (Znth i costs_l (0 : Int))) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 50) ” &&
  “ ((0 : Int) <= p_pre) ” &&
  “ (p_pre <= 100) ” &&
  “ ((Zlength (colors_l)) = n_pre) ” &&
  “ ((Zlength (costs_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) costs_l) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c < k_pre) ” &&
  “ ((0 : Int) <= cost) ” &&
  “ (cost <= 100) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= 19999900000) ” &&
  “ ((0 : Int) <= (Znth c seen_l (0 : Int))) ” &&
  “ ((Znth c seen_l (0 : Int)) <= i) ” &&
  “ ((0 : Int) <= (Znth c good_l (0 : Int))) ” &&
  “ ((Znth c good_l (0 : Int)) <= i) ” &&
  “ ((answer + (Znth c seen_l (0 : Int))) <= 9223372036854775807) ” &&
  “ ((answer + (Znth c good_l (0 : Int))) <= 9223372036854775807) ” &&
  “ (((Znth c seen_l (0 : Int)) + 1) <= INT_MAX) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (Zlength (colors_l))) ” &&
  “ ((Zlength (costs_l)) = (Zlength (colors_l))) ” &&
  “ ((Zlength (seen_l)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (i)) seen_l) ” &&
  “ ((Zlength (good_l)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) good_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (i)) good_l) ” &&
  “ (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l) ”
  &&  (((( &( "seen" ) ) + (c * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i ( &( "seen" ) ) c (0 : Int) k_pre seen_l)
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full ( &( "good" ) ) k_pre good_l)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)

noncomputable def countChoosingInns_partial_solve_wit_7_pure : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_next : (List Int)) (seen_l : (List Int)) (good_l : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (c = (Znth i colors_l (0 : Int)))) (PreH2 : (cost = (Znth i costs_l (0 : Int)))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 50)) (PreH7 : ((0 : Int) <= p_pre)) (PreH8 : (p_pre <= 100)) (PreH9 : ((Zlength (colors_l)) = n_pre)) (PreH10 : ((Zlength (costs_l)) = n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH12 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH14 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) (PreH15 : ((0 : Int) <= cost)) (PreH16 : (cost <= p_pre)) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i < n_pre)) (PreH19 : ((0 : Int) <= c)) (PreH20 : (c < k_pre)) (PreH21 : ((0 : Int) <= answer)) (PreH22 : (answer <= 19999900000)) (PreH23 : (seen_next = (replace_Znth (c) (((Znth c seen_l (0 : Int)) + 1)) (seen_l)))) (PreH24 : ((0 : Int) <= i)) (PreH25 : (i <= (Zlength (colors_l)))) (PreH26 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH27 : ((Zlength (seen_l)) = k_pre)) (PreH28 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l)) (PreH29 : (Forall ((GE.ge (α := Int)) (i)) seen_l)) (PreH30 : ((Zlength (good_l)) = k_pre)) (PreH31 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l)) (PreH32 : (Forall ((GE.ge (α := Int)) (i)) good_l)) (PreH33 : ((0 : Int) <= (i + 1))) (PreH34 : ((i + 1) <= (Zlength (colors_l)))) (PreH35 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH36 : ((Zlength (seen_next)) = k_pre)) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_next)) (PreH38 : (Forall ((GE.ge (α := Int)) ((i + 1))) seen_next)) (PreH39 : ((Zlength (good_l)) = k_pre)) (PreH40 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l)) (PreH41 : (Forall ((GE.ge (α := Int)) ((i + 1))) good_l)) (PreH42 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l (0 : Int))) seen_l good_l)) (PreH43 : ((Zlength (seen_next)) = k_pre)) (PreH44 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_next)) (PreH45 : (Forall ((GE.ge (α := Int)) (200000)) seen_next)) (PreH46 : ((Zlength (good_l)) = k_pre)) (PreH47 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l)) (PreH48 : (Forall ((GE.ge (α := Int)) (200000)) good_l)) ,
  ((( &( "colors" ) )) # Ptr |-> (colors_pre))
  ** ((( &( "costs" ) )) # Ptr |-> (costs_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "k" ) )) # Int |-> (k_pre))
  ** ((( &( "p" ) )) # Int |-> (p_pre))
  ** ((( &( "c" ) )) # Int |-> (c))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cost" ) )) # Int |-> (cost))
  ** ((( &( "answer" ) )) # Int64 |-> (answer))
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full (( &( "seen" ) ) + ((0 : Int) * sizeof(INT))) k_pre seen_next)
  ** (intArray.full (( &( "good" ) ) + ((0 : Int) * sizeof(INT))) k_pre good_l)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)
|--
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 50) ” &&
  “ ((Zlength (seen_next)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) seen_next) ” &&
  “ (Forall ((GE.ge (α := Int)) (200000)) seen_next) ” &&
  “ ((Zlength (good_l)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) good_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (200000)) good_l) ”

noncomputable def countChoosingInns_partial_solve_wit_7_aux : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_next : (List Int)) (seen_l : (List Int)) (good_l : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (c = (Znth i colors_l (0 : Int)))) (PreH2 : (cost = (Znth i costs_l (0 : Int)))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 200000)) (PreH5 : (1 <= k_pre)) (PreH6 : (k_pre <= 50)) (PreH7 : ((0 : Int) <= p_pre)) (PreH8 : (p_pre <= 100)) (PreH9 : ((Zlength (colors_l)) = n_pre)) (PreH10 : ((Zlength (costs_l)) = n_pre)) (PreH11 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH12 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH13 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH14 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) (PreH15 : ((0 : Int) <= cost)) (PreH16 : (cost <= p_pre)) (PreH17 : ((0 : Int) <= i)) (PreH18 : (i < n_pre)) (PreH19 : ((0 : Int) <= c)) (PreH20 : (c < k_pre)) (PreH21 : ((0 : Int) <= answer)) (PreH22 : (answer <= 19999900000)) (PreH23 : (seen_next = (replace_Znth (c) (((Znth c seen_l (0 : Int)) + 1)) (seen_l)))) (PreH24 : ((0 : Int) <= i)) (PreH25 : (i <= (Zlength (colors_l)))) (PreH26 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH27 : ((Zlength (seen_l)) = k_pre)) (PreH28 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l)) (PreH29 : (Forall ((GE.ge (α := Int)) (i)) seen_l)) (PreH30 : ((Zlength (good_l)) = k_pre)) (PreH31 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l)) (PreH32 : (Forall ((GE.ge (α := Int)) (i)) good_l)) (PreH33 : ((0 : Int) <= (i + 1))) (PreH34 : ((i + 1) <= (Zlength (colors_l)))) (PreH35 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH36 : ((Zlength (seen_next)) = k_pre)) (PreH37 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_next)) (PreH38 : (Forall ((GE.ge (α := Int)) ((i + 1))) seen_next)) (PreH39 : ((Zlength (good_l)) = k_pre)) (PreH40 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l)) (PreH41 : (Forall ((GE.ge (α := Int)) ((i + 1))) good_l)) (PreH42 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l (0 : Int))) seen_l good_l)) (PreH43 : ((Zlength (seen_next)) = k_pre)) (PreH44 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_next)) (PreH45 : (Forall ((GE.ge (α := Int)) (200000)) seen_next)) (PreH46 : ((Zlength (good_l)) = k_pre)) (PreH47 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l)) (PreH48 : (Forall ((GE.ge (α := Int)) (200000)) good_l)) ,
  (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full (( &( "seen" ) ) + ((0 : Int) * sizeof(INT))) k_pre seen_next)
  ** (intArray.full (( &( "good" ) ) + ((0 : Int) * sizeof(INT))) k_pre good_l)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)
|--
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 50) ” &&
  “ ((Zlength (seen_next)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) seen_next) ” &&
  “ (Forall ((GE.ge (α := Int)) (200000)) seen_next) ” &&
  “ ((Zlength (good_l)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) good_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (200000)) good_l) ” &&
  “ (c = (Znth i colors_l (0 : Int))) ” &&
  “ (cost = (Znth i costs_l (0 : Int))) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 50) ” &&
  “ ((0 : Int) <= p_pre) ” &&
  “ (p_pre <= 100) ” &&
  “ ((Zlength (colors_l)) = n_pre) ” &&
  “ ((Zlength (costs_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) costs_l) ” &&
  “ ((0 : Int) <= cost) ” &&
  “ (cost <= p_pre) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c < k_pre) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= 19999900000) ” &&
  “ (seen_next = (replace_Znth (c) (((Znth c seen_l (0 : Int)) + 1)) (seen_l))) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (Zlength (colors_l))) ” &&
  “ ((Zlength (costs_l)) = (Zlength (colors_l))) ” &&
  “ ((Zlength (seen_l)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (i)) seen_l) ” &&
  “ ((Zlength (good_l)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) good_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (i)) good_l) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= (Zlength (colors_l))) ” &&
  “ ((Zlength (costs_l)) = (Zlength (colors_l))) ” &&
  “ ((Zlength (seen_next)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) seen_next) ” &&
  “ (Forall ((GE.ge (α := Int)) ((i + 1))) seen_next) ” &&
  “ ((Zlength (good_l)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) good_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((i + 1))) good_l) ” &&
  “ (InnsPrefixCounts colors_l costs_l i k_pre p_pre (answer - (Znth c seen_l (0 : Int))) seen_l good_l) ” &&
  “ ((Zlength (seen_next)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) seen_next) ” &&
  “ (Forall ((GE.ge (α := Int)) (200000)) seen_next) ” &&
  “ ((Zlength (good_l)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) good_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (200000)) good_l) ”
  &&  (intArray.full (( &( "seen" ) ) + ((0 : Int) * sizeof(INT))) k_pre seen_next)
  ** (intArray.full (( &( "good" ) ) + ((0 : Int) * sizeof(INT))) k_pre good_l)
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)

noncomputable def countChoosingInns_partial_solve_wit_7 : Prop := countChoosingInns_partial_solve_wit_7_pure -> countChoosingInns_partial_solve_wit_7_aux

noncomputable def countChoosingInns_partial_solve_wit_8 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l : (List Int)) (good_l : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (cost > p_pre)) (PreH2 : (c = (Znth i colors_l (0 : Int)))) (PreH3 : (cost = (Znth i costs_l (0 : Int)))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : ((0 : Int) <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH13 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH15 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i < n_pre)) (PreH18 : ((0 : Int) <= c)) (PreH19 : (c < k_pre)) (PreH20 : ((0 : Int) <= cost)) (PreH21 : (cost <= 100)) (PreH22 : ((0 : Int) <= answer)) (PreH23 : (answer <= 19999900000)) (PreH24 : ((0 : Int) <= (Znth c seen_l (0 : Int)))) (PreH25 : ((Znth c seen_l (0 : Int)) <= i)) (PreH26 : ((0 : Int) <= (Znth c good_l (0 : Int)))) (PreH27 : ((Znth c good_l (0 : Int)) <= i)) (PreH28 : ((answer + (Znth c seen_l (0 : Int))) <= 9223372036854775807)) (PreH29 : ((answer + (Znth c good_l (0 : Int))) <= 9223372036854775807)) (PreH30 : (((Znth c seen_l (0 : Int)) + 1) <= INT_MAX)) (PreH31 : ((0 : Int) <= i)) (PreH32 : (i <= (Zlength (colors_l)))) (PreH33 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH34 : ((Zlength (seen_l)) = k_pre)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (i)) seen_l)) (PreH37 : ((Zlength (good_l)) = k_pre)) (PreH38 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l)) (PreH39 : (Forall ((GE.ge (α := Int)) (i)) good_l)) (PreH40 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l)) ,
  (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full ( &( "seen" ) ) k_pre seen_l)
  ** (intArray.full ( &( "good" ) ) k_pre good_l)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)
|--
  “ (cost > p_pre) ” &&
  “ (c = (Znth i colors_l (0 : Int))) ” &&
  “ (cost = (Znth i costs_l (0 : Int))) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 50) ” &&
  “ ((0 : Int) <= p_pre) ” &&
  “ (p_pre <= 100) ” &&
  “ ((Zlength (colors_l)) = n_pre) ” &&
  “ ((Zlength (costs_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) costs_l) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c < k_pre) ” &&
  “ ((0 : Int) <= cost) ” &&
  “ (cost <= 100) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= 19999900000) ” &&
  “ ((0 : Int) <= (Znth c seen_l (0 : Int))) ” &&
  “ ((Znth c seen_l (0 : Int)) <= i) ” &&
  “ ((0 : Int) <= (Znth c good_l (0 : Int))) ” &&
  “ ((Znth c good_l (0 : Int)) <= i) ” &&
  “ ((answer + (Znth c seen_l (0 : Int))) <= 9223372036854775807) ” &&
  “ ((answer + (Znth c good_l (0 : Int))) <= 9223372036854775807) ” &&
  “ (((Znth c seen_l (0 : Int)) + 1) <= INT_MAX) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (Zlength (colors_l))) ” &&
  “ ((Zlength (costs_l)) = (Zlength (colors_l))) ” &&
  “ ((Zlength (seen_l)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (i)) seen_l) ” &&
  “ ((Zlength (good_l)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) good_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (i)) good_l) ” &&
  “ (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l) ”
  &&  (((( &( "good" ) ) + (c * sizeof(INT)))) # Int |-> ((Znth c good_l (0 : Int))))
  ** (intArray.missing_i ( &( "good" ) ) c (0 : Int) k_pre good_l)
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full ( &( "seen" ) ) k_pre seen_l)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)

noncomputable def countChoosingInns_partial_solve_wit_9 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l : (List Int)) (good_l : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (cost > p_pre)) (PreH2 : (c = (Znth i colors_l (0 : Int)))) (PreH3 : (cost = (Znth i costs_l (0 : Int)))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : ((0 : Int) <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH13 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH15 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i < n_pre)) (PreH18 : ((0 : Int) <= c)) (PreH19 : (c < k_pre)) (PreH20 : ((0 : Int) <= cost)) (PreH21 : (cost <= 100)) (PreH22 : ((0 : Int) <= answer)) (PreH23 : (answer <= 19999900000)) (PreH24 : ((0 : Int) <= (Znth c seen_l (0 : Int)))) (PreH25 : ((Znth c seen_l (0 : Int)) <= i)) (PreH26 : ((0 : Int) <= (Znth c good_l (0 : Int)))) (PreH27 : ((Znth c good_l (0 : Int)) <= i)) (PreH28 : ((answer + (Znth c seen_l (0 : Int))) <= 9223372036854775807)) (PreH29 : ((answer + (Znth c good_l (0 : Int))) <= 9223372036854775807)) (PreH30 : (((Znth c seen_l (0 : Int)) + 1) <= INT_MAX)) (PreH31 : ((0 : Int) <= i)) (PreH32 : (i <= (Zlength (colors_l)))) (PreH33 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH34 : ((Zlength (seen_l)) = k_pre)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (i)) seen_l)) (PreH37 : ((Zlength (good_l)) = k_pre)) (PreH38 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l)) (PreH39 : (Forall ((GE.ge (α := Int)) (i)) good_l)) (PreH40 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l)) ,
  (intArray.full ( &( "good" ) ) k_pre good_l)
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.full ( &( "seen" ) ) k_pre seen_l)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)
|--
  “ (cost > p_pre) ” &&
  “ (c = (Znth i colors_l (0 : Int))) ” &&
  “ (cost = (Znth i costs_l (0 : Int))) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 50) ” &&
  “ ((0 : Int) <= p_pre) ” &&
  “ (p_pre <= 100) ” &&
  “ ((Zlength (colors_l)) = n_pre) ” &&
  “ ((Zlength (costs_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) costs_l) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c < k_pre) ” &&
  “ ((0 : Int) <= cost) ” &&
  “ (cost <= 100) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= 19999900000) ” &&
  “ ((0 : Int) <= (Znth c seen_l (0 : Int))) ” &&
  “ ((Znth c seen_l (0 : Int)) <= i) ” &&
  “ ((0 : Int) <= (Znth c good_l (0 : Int))) ” &&
  “ ((Znth c good_l (0 : Int)) <= i) ” &&
  “ ((answer + (Znth c seen_l (0 : Int))) <= 9223372036854775807) ” &&
  “ ((answer + (Znth c good_l (0 : Int))) <= 9223372036854775807) ” &&
  “ (((Znth c seen_l (0 : Int)) + 1) <= INT_MAX) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (Zlength (colors_l))) ” &&
  “ ((Zlength (costs_l)) = (Zlength (colors_l))) ” &&
  “ ((Zlength (seen_l)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (i)) seen_l) ” &&
  “ ((Zlength (good_l)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) good_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (i)) good_l) ” &&
  “ (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l) ”
  &&  (((( &( "seen" ) ) + (c * sizeof(INT)))) # Int |-> ((Znth c seen_l (0 : Int))))
  ** (intArray.missing_i ( &( "seen" ) ) c (0 : Int) k_pre seen_l)
  ** (intArray.full ( &( "good" ) ) k_pre good_l)
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)

noncomputable def countChoosingInns_partial_solve_wit_10 : Prop :=
  forall (p_pre : Int) (k_pre : Int) (n_pre : Int) (costs_pre : Int) (colors_pre : Int) (costs_l : (List Int)) (colors_l : (List Int)) (seen_l : (List Int)) (good_l : (List Int)) (c : Int) (i : Int) (cost : Int) (answer : Int) (PreH1 : (cost > p_pre)) (PreH2 : (c = (Znth i colors_l (0 : Int)))) (PreH3 : (cost = (Znth i costs_l (0 : Int)))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 200000)) (PreH6 : (1 <= k_pre)) (PreH7 : (k_pre <= 50)) (PreH8 : ((0 : Int) <= p_pre)) (PreH9 : (p_pre <= 100)) (PreH10 : ((Zlength (colors_l)) = n_pre)) (PreH11 : ((Zlength (costs_l)) = n_pre)) (PreH12 : (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l)) (PreH13 : (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l)) (PreH14 : (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l)) (PreH15 : (Forall ((GE.ge (α := Int)) (100)) costs_l)) (PreH16 : ((0 : Int) <= i)) (PreH17 : (i < n_pre)) (PreH18 : ((0 : Int) <= c)) (PreH19 : (c < k_pre)) (PreH20 : ((0 : Int) <= cost)) (PreH21 : (cost <= 100)) (PreH22 : ((0 : Int) <= answer)) (PreH23 : (answer <= 19999900000)) (PreH24 : ((0 : Int) <= (Znth c seen_l (0 : Int)))) (PreH25 : ((Znth c seen_l (0 : Int)) <= i)) (PreH26 : ((0 : Int) <= (Znth c good_l (0 : Int)))) (PreH27 : ((Znth c good_l (0 : Int)) <= i)) (PreH28 : ((answer + (Znth c seen_l (0 : Int))) <= 9223372036854775807)) (PreH29 : ((answer + (Znth c good_l (0 : Int))) <= 9223372036854775807)) (PreH30 : (((Znth c seen_l (0 : Int)) + 1) <= INT_MAX)) (PreH31 : ((0 : Int) <= i)) (PreH32 : (i <= (Zlength (colors_l)))) (PreH33 : ((Zlength (costs_l)) = (Zlength (colors_l)))) (PreH34 : ((Zlength (seen_l)) = k_pre)) (PreH35 : (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l)) (PreH36 : (Forall ((GE.ge (α := Int)) (i)) seen_l)) (PreH37 : ((Zlength (good_l)) = k_pre)) (PreH38 : (Forall ((LE.le (α := Int)) ((0 : Int))) good_l)) (PreH39 : (Forall ((GE.ge (α := Int)) (i)) good_l)) (PreH40 : (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l)) ,
  (intArray.full ( &( "seen" ) ) k_pre seen_l)
  ** (intArray.full ( &( "good" ) ) k_pre good_l)
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)
|--
  “ (cost > p_pre) ” &&
  “ (c = (Znth i colors_l (0 : Int))) ” &&
  “ (cost = (Znth i costs_l (0 : Int))) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 200000) ” &&
  “ (1 <= k_pre) ” &&
  “ (k_pre <= 50) ” &&
  “ ((0 : Int) <= p_pre) ” &&
  “ (p_pre <= 100) ” &&
  “ ((Zlength (colors_l)) = n_pre) ” &&
  “ ((Zlength (costs_l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) colors_l) ” &&
  “ (Forall ((GE.ge (α := Int)) ((k_pre - 1))) colors_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) costs_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (100)) costs_l) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < n_pre) ” &&
  “ ((0 : Int) <= c) ” &&
  “ (c < k_pre) ” &&
  “ ((0 : Int) <= cost) ” &&
  “ (cost <= 100) ” &&
  “ ((0 : Int) <= answer) ” &&
  “ (answer <= 19999900000) ” &&
  “ ((0 : Int) <= (Znth c seen_l (0 : Int))) ” &&
  “ ((Znth c seen_l (0 : Int)) <= i) ” &&
  “ ((0 : Int) <= (Znth c good_l (0 : Int))) ” &&
  “ ((Znth c good_l (0 : Int)) <= i) ” &&
  “ ((answer + (Znth c seen_l (0 : Int))) <= 9223372036854775807) ” &&
  “ ((answer + (Znth c good_l (0 : Int))) <= 9223372036854775807) ” &&
  “ (((Znth c seen_l (0 : Int)) + 1) <= INT_MAX) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= (Zlength (colors_l))) ” &&
  “ ((Zlength (costs_l)) = (Zlength (colors_l))) ” &&
  “ ((Zlength (seen_l)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) seen_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (i)) seen_l) ” &&
  “ ((Zlength (good_l)) = k_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) good_l) ” &&
  “ (Forall ((GE.ge (α := Int)) (i)) good_l) ” &&
  “ (InnsPrefixCounts colors_l costs_l i k_pre p_pre answer seen_l good_l) ”
  &&  (((( &( "seen" ) ) + (c * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i ( &( "seen" ) ) c (0 : Int) k_pre seen_l)
  ** (intArray.full ( &( "good" ) ) k_pre good_l)
  ** (intArray.full colors_pre n_pre colors_l)
  ** (intArray.full costs_pre n_pre costs_l)
  ** (intArray.undef_seg ( &( "seen" ) ) k_pre 50)
  ** (intArray.undef_seg ( &( "good" ) ) k_pre 50)


structure VC_Correct : Type where
  proof_of_initCounts_safety_wit_1 : initCounts_safety_wit_1
  proof_of_initCounts_safety_wit_2 : initCounts_safety_wit_2
  proof_of_initCounts_safety_wit_3 : initCounts_safety_wit_3
  proof_of_initCounts_safety_wit_4 : initCounts_safety_wit_4
  proof_of_initCounts_partial_solve_wit_1 : initCounts_partial_solve_wit_1
  proof_of_initCounts_partial_solve_wit_2 : initCounts_partial_solve_wit_2
  proof_of_copyCounts_safety_wit_1 : copyCounts_safety_wit_1
  proof_of_copyCounts_safety_wit_2 : copyCounts_safety_wit_2
  proof_of_copyCounts_partial_solve_wit_1 : copyCounts_partial_solve_wit_1
  proof_of_copyCounts_partial_solve_wit_2 : copyCounts_partial_solve_wit_2
  proof_of_countChoosingInns_safety_wit_1 : countChoosingInns_safety_wit_1
  proof_of_countChoosingInns_safety_wit_2 : countChoosingInns_safety_wit_2
  proof_of_countChoosingInns_safety_wit_3 : countChoosingInns_safety_wit_3
  proof_of_countChoosingInns_safety_wit_4 : countChoosingInns_safety_wit_4
  proof_of_countChoosingInns_safety_wit_5 : countChoosingInns_safety_wit_5
  proof_of_countChoosingInns_safety_wit_6 : countChoosingInns_safety_wit_6
  proof_of_countChoosingInns_safety_wit_7 : countChoosingInns_safety_wit_7
  proof_of_countChoosingInns_safety_wit_8 : countChoosingInns_safety_wit_8
  proof_of_countChoosingInns_safety_wit_9 : countChoosingInns_safety_wit_9
  proof_of_countChoosingInns_safety_wit_10 : countChoosingInns_safety_wit_10
  proof_of_countChoosingInns_safety_wit_11 : countChoosingInns_safety_wit_11
  proof_of_countChoosingInns_safety_wit_12 : countChoosingInns_safety_wit_12
  proof_of_countChoosingInns_safety_wit_13 : countChoosingInns_safety_wit_13
  proof_of_countChoosingInns_safety_wit_14 : countChoosingInns_safety_wit_14
  proof_of_countChoosingInns_entail_wit_7_1 : countChoosingInns_entail_wit_7_1
  proof_of_countChoosingInns_entail_wit_7_2 : countChoosingInns_entail_wit_7_2
  proof_of_countChoosingInns_return_wit_1 : countChoosingInns_return_wit_1
  proof_of_countChoosingInns_partial_solve_wit_1_pure : countChoosingInns_partial_solve_wit_1_pure
  proof_of_countChoosingInns_partial_solve_wit_1 : countChoosingInns_partial_solve_wit_1
  proof_of_countChoosingInns_partial_solve_wit_2 : countChoosingInns_partial_solve_wit_2
  proof_of_countChoosingInns_partial_solve_wit_3 : countChoosingInns_partial_solve_wit_3
  proof_of_countChoosingInns_partial_solve_wit_4 : countChoosingInns_partial_solve_wit_4
  proof_of_countChoosingInns_partial_solve_wit_5 : countChoosingInns_partial_solve_wit_5
  proof_of_countChoosingInns_partial_solve_wit_6 : countChoosingInns_partial_solve_wit_6
  proof_of_countChoosingInns_partial_solve_wit_7_pure : countChoosingInns_partial_solve_wit_7_pure
  proof_of_countChoosingInns_partial_solve_wit_7 : countChoosingInns_partial_solve_wit_7
  proof_of_countChoosingInns_partial_solve_wit_8 : countChoosingInns_partial_solve_wit_8
  proof_of_countChoosingInns_partial_solve_wit_9 : countChoosingInns_partial_solve_wit_9
  proof_of_countChoosingInns_partial_solve_wit_10 : countChoosingInns_partial_solve_wit_10
  proof_of_initCounts_entail_wit_1 : initCounts_entail_wit_1
  proof_of_initCounts_entail_wit_2 : initCounts_entail_wit_2
  proof_of_initCounts_return_wit_1 : initCounts_return_wit_1
  proof_of_copyCounts_entail_wit_1 : copyCounts_entail_wit_1
  proof_of_copyCounts_entail_wit_2 : copyCounts_entail_wit_2
  proof_of_copyCounts_return_wit_1 : copyCounts_return_wit_1
  proof_of_countChoosingInns_entail_wit_1 : countChoosingInns_entail_wit_1
  proof_of_countChoosingInns_entail_wit_2 : countChoosingInns_entail_wit_2
  proof_of_countChoosingInns_entail_wit_3 : countChoosingInns_entail_wit_3
  proof_of_countChoosingInns_entail_wit_4 : countChoosingInns_entail_wit_4
  proof_of_countChoosingInns_entail_wit_5 : countChoosingInns_entail_wit_5
  proof_of_countChoosingInns_entail_wit_6 : countChoosingInns_entail_wit_6
  proof_of_countChoosingInns_entail_wit_8 : countChoosingInns_entail_wit_8

end SimpleC.EE.LLM_bench.Algorithms.choosing_inns.choosing_inns_goal
