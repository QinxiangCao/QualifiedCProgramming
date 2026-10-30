import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_lib
open SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance house_robber_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def rob_safety_wit_1 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH5 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "prev2" ) )) # Int |->_)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full nums_pre n_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def rob_safety_wit_2 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH5 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "prev1" ) )) # Int |->_)
  ** ((( &( "prev2" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full nums_pre n_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def rob_safety_wit_3 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH5 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "prev1" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "prev2" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** (intArray.full nums_pre n_pre l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def rob_safety_wit_4 : Prop :=
  (
forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (prev2 : Int) (prev1 : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH5 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (HouseRobberDPState l i prev2 prev1)) ,
  (intArray.full nums_pre n_pre l)
  ** ((( &( "take" ) )) # Int |->_)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "prev1" ) )) # Int |-> (prev1))
  ** ((( &( "prev2" ) )) # Int |-> (prev2))
|--
  “ ((prev2 + (Znth i l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (prev2 + (Znth i l (0 : Int)))) ”
) \/
(
forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (prev2 : Int) (prev1 : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH5 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (HouseRobberDPState l i prev2 prev1)) ,
  (intArray.full nums_pre n_pre l)
  ** ((( &( "take" ) )) # Int |->_)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "prev1" ) )) # Int |-> (prev1))
  ** ((( &( "prev2" ) )) # Int |-> (prev2))
|--
  “ ((prev2 + (Znth i l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (prev2 + (Znth i l (0 : Int)))) ”
)

noncomputable def rob_safety_wit_4_split_goal_1 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (prev2 : Int) (prev1 : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH5 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (HouseRobberDPState l i prev2 prev1)) ,
  (intArray.full nums_pre n_pre l)
  ** ((( &( "take" ) )) # Int |->_)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "prev1" ) )) # Int |-> (prev1))
  ** ((( &( "prev2" ) )) # Int |-> (prev2))
|--
  “ ((prev2 + (Znth i l (0 : Int))) <= INT_MAX) ”

noncomputable def rob_safety_wit_4_split_goal_2 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (prev2 : Int) (prev1 : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH5 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (HouseRobberDPState l i prev2 prev1)) ,
  (intArray.full nums_pre n_pre l)
  ** ((( &( "take" ) )) # Int |->_)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "prev1" ) )) # Int |-> (prev1))
  ** ((( &( "prev2" ) )) # Int |-> (prev2))
|--
  “ ((INT_MIN) <= (prev2 + (Znth i l (0 : Int)))) ”

noncomputable def rob_safety_wit_5 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (prev2 : Int) (prev1 : Int) (i : Int) (PreH1 : ((prev2 + (Znth i l (0 : Int))) > prev1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (HouseRobberDPState l i prev2 prev1)) ,
  (intArray.full nums_pre n_pre l)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "prev1" ) )) # Int |-> ((prev2 + (Znth i l (0 : Int)))))
  ** ((( &( "prev2" ) )) # Int |-> (prev1))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def rob_safety_wit_6 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (prev2 : Int) (prev1 : Int) (i : Int) (PreH1 : ((prev2 + (Znth i l (0 : Int))) <= prev1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (HouseRobberDPState l i prev2 prev1)) ,
  (intArray.full nums_pre n_pre l)
  ** ((( &( "nums" ) )) # Ptr |-> (nums_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "prev1" ) )) # Int |-> (prev1))
  ** ((( &( "prev2" ) )) # Int |-> (prev1))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def rob_entail_wit_1 : Prop :=
  (
forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH5 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (intArray.full nums_pre n_pre l)
|--
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (HouseRobberDPState l (0 : Int) (0 : Int) (0 : Int)) ”
  &&  (intArray.full nums_pre n_pre l)
) \/
(
forall (l : (List Int)) (n_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH5 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  TT && emp 
|--
  “ (HouseRobberDPState l (0 : Int) (0 : Int) (0 : Int)) ”
  &&  emp
)

noncomputable def rob_entail_wit_1_split_goal_1 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH5 : (Forall ((GE.ge (α := Int)) (10000)) l)) ,
  (HouseRobberDPState l (0 : Int) (0 : Int) (0 : Int))

noncomputable def rob_entail_wit_2_1 : Prop :=
  (
forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (prev2 : Int) (prev1 : Int) (i : Int) (PreH1 : ((prev2 + (Znth i l (0 : Int))) > prev1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (HouseRobberDPState l i prev2 prev1)) ,
  (intArray.full nums_pre n_pre l)
|--
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ (HouseRobberDPState l (i + 1) prev1 (prev2 + (Znth i l (0 : Int)))) ”
  &&  (intArray.full nums_pre n_pre l)
) \/
(
forall (l : (List Int)) (n_pre : Int) (prev2 : Int) (prev1 : Int) (i : Int) (PreH1 : ((prev2 + (Znth i l (0 : Int))) > prev1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (HouseRobberDPState l i prev2 prev1)) ,
  TT && emp 
|--
  “ (HouseRobberDPState l (i + 1) prev1 (prev2 + (Znth i l (0 : Int)))) ”
  &&  emp
)

noncomputable def rob_entail_wit_2_1_split_goal_1 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (prev2 : Int) (prev1 : Int) (i : Int) (PreH1 : ((prev2 + (Znth i l (0 : Int))) > prev1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (HouseRobberDPState l i prev2 prev1)) ,
  (HouseRobberDPState l (i + 1) prev1 (prev2 + (Znth i l (0 : Int))))

noncomputable def rob_entail_wit_2_2 : Prop :=
  (
forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (prev2 : Int) (prev1 : Int) (i : Int) (PreH1 : ((prev2 + (Znth i l (0 : Int))) <= prev1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (HouseRobberDPState l i prev2 prev1)) ,
  (intArray.full nums_pre n_pre l)
|--
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= n_pre) ” &&
  “ (HouseRobberDPState l (i + 1) prev1 prev1) ”
  &&  (intArray.full nums_pre n_pre l)
) \/
(
forall (l : (List Int)) (n_pre : Int) (prev2 : Int) (prev1 : Int) (i : Int) (PreH1 : ((prev2 + (Znth i l (0 : Int))) <= prev1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (HouseRobberDPState l i prev2 prev1)) ,
  TT && emp 
|--
  “ (HouseRobberDPState l (i + 1) prev1 prev1) ”
  &&  emp
)

noncomputable def rob_entail_wit_2_2_split_goal_1 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (prev2 : Int) (prev1 : Int) (i : Int) (PreH1 : ((prev2 + (Znth i l (0 : Int))) <= prev1)) (PreH2 : (i < n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : ((Zlength (l)) = n_pre)) (PreH5 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= n_pre)) (PreH9 : (HouseRobberDPState l i prev2 prev1)) ,
  (HouseRobberDPState l (i + 1) prev1 prev1)

noncomputable def rob_return_wit_1 : Prop :=
  (
forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (prev2 : Int) (prev1 : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH5 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (HouseRobberDPState l i prev2 prev1)) ,
  (intArray.full nums_pre n_pre l)
|--
  “ (HouseRobberAnswer l prev1) ”
  &&  (intArray.full nums_pre n_pre l)
) \/
(
forall (l : (List Int)) (n_pre : Int) (prev2 : Int) (prev1 : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH5 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (HouseRobberDPState l i prev2 prev1)) ,
  TT && emp 
|--
  “ (HouseRobberAnswer l prev1) ”
  &&  emp
)

noncomputable def rob_return_wit_1_split_goal_1 : Prop :=
  forall (l : (List Int)) (n_pre : Int) (prev2 : Int) (prev1 : Int) (i : Int) (PreH1 : (i >= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH5 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (HouseRobberDPState l i prev2 prev1)) ,
  (HouseRobberAnswer l prev1)

noncomputable def rob_partial_solve_wit_1 : Prop :=
  forall (l : (List Int)) (nums_pre : Int) (n_pre : Int) (prev2 : Int) (prev1 : Int) (i : Int) (PreH1 : (i < n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : ((Zlength (l)) = n_pre)) (PreH4 : (Forall ((LE.le (α := Int)) ((0 : Int))) l)) (PreH5 : (Forall ((GE.ge (α := Int)) (10000)) l)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= n_pre)) (PreH8 : (HouseRobberDPState l i prev2 prev1)) ,
  (intArray.full nums_pre n_pre l)
|--
  “ (i < n_pre) ” &&
  “ (n_pre <= 100000) ” &&
  “ ((Zlength (l)) = n_pre) ” &&
  “ (Forall ((LE.le (α := Int)) ((0 : Int))) l) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) l) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= n_pre) ” &&
  “ (HouseRobberDPState l i prev2 prev1) ”
  &&  (((nums_pre + (i * sizeof(INT)))) # Int |-> ((Znth i l (0 : Int))))
  ** (intArray.missing_i nums_pre i (0 : Int) n_pre l)


structure VC_Correct : Type where
  proof_of_rob_safety_wit_1 : rob_safety_wit_1
  proof_of_rob_safety_wit_2 : rob_safety_wit_2
  proof_of_rob_safety_wit_3 : rob_safety_wit_3
  proof_of_rob_safety_wit_5 : rob_safety_wit_5
  proof_of_rob_safety_wit_6 : rob_safety_wit_6
  proof_of_rob_partial_solve_wit_1 : rob_partial_solve_wit_1
  proof_of_rob_safety_wit_4 : rob_safety_wit_4
  proof_of_rob_entail_wit_1 : rob_entail_wit_1
  proof_of_rob_entail_wit_2_1 : rob_entail_wit_2_1
  proof_of_rob_entail_wit_2_2 : rob_entail_wit_2_2
  proof_of_rob_return_wit_1 : rob_return_wit_1

end SimpleC.EE.LLM_bench.Algorithms.house_robber.house_robber_goal
