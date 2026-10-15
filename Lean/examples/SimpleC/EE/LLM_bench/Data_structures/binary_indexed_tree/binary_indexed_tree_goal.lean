import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Data_structures.binary_indexed_tree.binary_indexed_tree_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Data_structures.binary_indexed_tree.binary_indexed_tree_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance binary_indexed_tree_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def lowbit_safety_wit_1 : Prop :=
  forall (x_pre : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) ,
  ((( &( "x" ) )) # Int |-> (x_pre))
|--
  “ (x_pre ≠ (INT_MIN)) ”

noncomputable def lowbit_return_wit_1 : Prop :=
  (
forall (x_pre : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Z.land x_pre (-x_pre)) = (FenwickLowbit (x_pre))) ”
  &&  emp
) \/
(
forall (x_pre : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) ,
  TT && emp 
|--
  “ ((Z.land x_pre (-x_pre)) = (FenwickLowbit (x_pre))) ”
  &&  emp
)

noncomputable def lowbit_return_wit_1_split_goal_1 : Prop :=
  forall (x_pre : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= INT_MAX)) ,
  ((Z.land x_pre (-x_pre)) = (FenwickLowbit (x_pre)))

noncomputable def add_safety_wit_1 : Prop :=
  (
forall (delta_pre : Int) (pos_pre : Int) (n_pre : Int) (bit_pre : Int) (bit_l : (List Int)) (a : (List Int)) (bit_cur : (List Int)) (pos : Int) (PreH1 : (pos <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : ((2 * n_pre) <= INT_MAX)) (PreH4 : (1 <= pos_pre)) (PreH5 : (pos_pre <= n_pre)) (PreH6 : (1 <= pos)) (PreH7 : (pos <= (2 * n_pre))) (PreH8 : (FenwickRep a bit_l n_pre)) (PreH9 : forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n_pre)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre))))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre)))))) <= INT_MAX)))) (PreH10 : (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre)) ,
  (intArray.full bit_pre (n_pre + 1) bit_cur)
  ** ((( &( "bit" ) )) # Ptr |-> (bit_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "delta" ) )) # Int |-> (delta_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
|--
  “ (((Znth pos bit_cur (0 : Int)) + delta_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth pos bit_cur (0 : Int)) + delta_pre)) ”
) \/
(
forall (delta_pre : Int) (pos_pre : Int) (n_pre : Int) (bit_pre : Int) (bit_l : (List Int)) (a : (List Int)) (bit_cur : (List Int)) (pos : Int) (PreH1 : (pos <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : ((2 * n_pre) <= INT_MAX)) (PreH4 : (1 <= pos_pre)) (PreH5 : (pos_pre <= n_pre)) (PreH6 : (1 <= pos)) (PreH7 : (pos <= (2 * n_pre))) (PreH8 : (FenwickRep a bit_l n_pre)) (PreH9 : forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n_pre)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre))))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre)))))) <= INT_MAX)))) (PreH10 : (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre)) ,
  (intArray.full bit_pre (n_pre + 1) bit_cur)
  ** ((( &( "bit" ) )) # Ptr |-> (bit_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "delta" ) )) # Int |-> (delta_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
|--
  “ (((Znth pos bit_cur (0 : Int)) + delta_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Znth pos bit_cur (0 : Int)) + delta_pre)) ”
)

noncomputable def add_safety_wit_1_split_goal_1 : Prop :=
  forall (delta_pre : Int) (pos_pre : Int) (n_pre : Int) (bit_pre : Int) (bit_l : (List Int)) (a : (List Int)) (bit_cur : (List Int)) (pos : Int) (PreH1 : (pos <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : ((2 * n_pre) <= INT_MAX)) (PreH4 : (1 <= pos_pre)) (PreH5 : (pos_pre <= n_pre)) (PreH6 : (1 <= pos)) (PreH7 : (pos <= (2 * n_pre))) (PreH8 : (FenwickRep a bit_l n_pre)) (PreH9 : forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n_pre)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre))))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre)))))) <= INT_MAX)))) (PreH10 : (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre)) ,
  (intArray.full bit_pre (n_pre + 1) bit_cur)
  ** ((( &( "bit" ) )) # Ptr |-> (bit_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "delta" ) )) # Int |-> (delta_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
|--
  “ (((Znth pos bit_cur (0 : Int)) + delta_pre) <= INT_MAX) ”

noncomputable def add_safety_wit_1_split_goal_2 : Prop :=
  forall (delta_pre : Int) (pos_pre : Int) (n_pre : Int) (bit_pre : Int) (bit_l : (List Int)) (a : (List Int)) (bit_cur : (List Int)) (pos : Int) (PreH1 : (pos <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : ((2 * n_pre) <= INT_MAX)) (PreH4 : (1 <= pos_pre)) (PreH5 : (pos_pre <= n_pre)) (PreH6 : (1 <= pos)) (PreH7 : (pos <= (2 * n_pre))) (PreH8 : (FenwickRep a bit_l n_pre)) (PreH9 : forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n_pre)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre))))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre)))))) <= INT_MAX)))) (PreH10 : (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre)) ,
  (intArray.full bit_pre (n_pre + 1) bit_cur)
  ** ((( &( "bit" ) )) # Ptr |-> (bit_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "delta" ) )) # Int |-> (delta_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
|--
  “ ((INT_MIN) <= ((Znth pos bit_cur (0 : Int)) + delta_pre)) ”

noncomputable def add_safety_wit_2 : Prop :=
  (
forall (delta_pre : Int) (pos_pre : Int) (n_pre : Int) (bit_pre : Int) (bit_l : (List Int)) (a : (List Int)) (bit_cur : (List Int)) (pos : Int) (retval : Int) (PreH1 : (retval = (FenwickLowbit (pos)))) (PreH2 : (pos <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : ((2 * n_pre) <= INT_MAX)) (PreH5 : (1 <= pos_pre)) (PreH6 : (pos_pre <= n_pre)) (PreH7 : (1 <= pos)) (PreH8 : (pos <= (2 * n_pre))) (PreH9 : (FenwickRep a bit_l n_pre)) (PreH10 : forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n_pre)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre))))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre)))))) <= INT_MAX)))) (PreH11 : (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre)) ,
  (intArray.full bit_pre (n_pre + 1) (replace_Znth (pos) (((Znth pos bit_cur (0 : Int)) + delta_pre)) (bit_cur)))
  ** ((( &( "bit" ) )) # Ptr |-> (bit_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "delta" ) )) # Int |-> (delta_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
|--
  “ ((pos + retval) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (pos + retval)) ”
) \/
(
forall (delta_pre : Int) (pos_pre : Int) (n_pre : Int) (bit_pre : Int) (bit_l : (List Int)) (a : (List Int)) (bit_cur : (List Int)) (pos : Int) (retval : Int) (PreH1 : (retval = (FenwickLowbit (pos)))) (PreH2 : (pos <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : ((2 * n_pre) <= INT_MAX)) (PreH5 : (1 <= pos_pre)) (PreH6 : (pos_pre <= n_pre)) (PreH7 : (1 <= pos)) (PreH8 : (pos <= (2 * n_pre))) (PreH9 : (FenwickRep a bit_l n_pre)) (PreH10 : forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n_pre)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre))))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre)))))) <= INT_MAX)))) (PreH11 : (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre)) ,
  (intArray.full bit_pre (n_pre + 1) (replace_Znth (pos) (((Znth pos bit_cur (0 : Int)) + delta_pre)) (bit_cur)))
  ** ((( &( "bit" ) )) # Ptr |-> (bit_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "delta" ) )) # Int |-> (delta_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
|--
  “ ((pos + retval) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (pos + retval)) ”
)

noncomputable def add_safety_wit_2_split_goal_1 : Prop :=
  forall (delta_pre : Int) (pos_pre : Int) (n_pre : Int) (bit_pre : Int) (bit_l : (List Int)) (a : (List Int)) (bit_cur : (List Int)) (pos : Int) (retval : Int) (PreH1 : (retval = (FenwickLowbit (pos)))) (PreH2 : (pos <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : ((2 * n_pre) <= INT_MAX)) (PreH5 : (1 <= pos_pre)) (PreH6 : (pos_pre <= n_pre)) (PreH7 : (1 <= pos)) (PreH8 : (pos <= (2 * n_pre))) (PreH9 : (FenwickRep a bit_l n_pre)) (PreH10 : forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n_pre)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre))))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre)))))) <= INT_MAX)))) (PreH11 : (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre)) ,
  (intArray.full bit_pre (n_pre + 1) (replace_Znth (pos) (((Znth pos bit_cur (0 : Int)) + delta_pre)) (bit_cur)))
  ** ((( &( "bit" ) )) # Ptr |-> (bit_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "delta" ) )) # Int |-> (delta_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
|--
  “ ((pos + retval) <= INT_MAX) ”

noncomputable def add_safety_wit_2_split_goal_2 : Prop :=
  forall (delta_pre : Int) (pos_pre : Int) (n_pre : Int) (bit_pre : Int) (bit_l : (List Int)) (a : (List Int)) (bit_cur : (List Int)) (pos : Int) (retval : Int) (PreH1 : (retval = (FenwickLowbit (pos)))) (PreH2 : (pos <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : ((2 * n_pre) <= INT_MAX)) (PreH5 : (1 <= pos_pre)) (PreH6 : (pos_pre <= n_pre)) (PreH7 : (1 <= pos)) (PreH8 : (pos <= (2 * n_pre))) (PreH9 : (FenwickRep a bit_l n_pre)) (PreH10 : forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n_pre)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre))))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre)))))) <= INT_MAX)))) (PreH11 : (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre)) ,
  (intArray.full bit_pre (n_pre + 1) (replace_Znth (pos) (((Znth pos bit_cur (0 : Int)) + delta_pre)) (bit_cur)))
  ** ((( &( "bit" ) )) # Ptr |-> (bit_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "delta" ) )) # Int |-> (delta_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
|--
  “ ((INT_MIN) <= (pos + retval)) ”

noncomputable def add_entail_wit_1 : Prop :=
  (
forall (delta_pre : Int) (pos_pre : Int) (n_pre : Int) (bit_pre : Int) (bit_l : (List Int)) (a : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : ((2 * n_pre) <= INT_MAX)) (PreH3 : (1 <= pos_pre)) (PreH4 : (pos_pre <= n_pre)) (PreH5 : (FenwickRep a bit_l n_pre)) (PreH6 : forall (lo_2 : Int) , forall (hi_2 : Int) , ((((1 <= lo_2) ∧ (lo_2 <= hi_2)) ∧ (hi_2 <= n_pre)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo_2) ((hi_2 + 1)) (a))))) ∧ ((ListLib.sum ((sublist (lo_2) ((hi_2 + 1)) (a)))) <= INT_MAX)))) (PreH7 : forall (lo_3 : Int) , forall (hi_3 : Int) , ((((1 <= lo_3) ∧ (lo_3 <= hi_3)) ∧ (hi_3 <= n_pre)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo_3) ((hi_3 + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre))))))) ∧ ((ListLib.sum ((sublist (lo_3) ((hi_3 + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre)))))) <= INT_MAX)))) ,
  (intArray.full bit_pre (n_pre + 1) bit_l)
|--
  EX bit_cur : (List Int),
  “ (1 <= n_pre) ” &&
  “ ((2 * n_pre) <= INT_MAX) ” &&
  “ (1 <= pos_pre) ” &&
  “ (pos_pre <= n_pre) ” &&
  “ (1 <= pos_pre) ” &&
  “ (pos_pre <= (2 * n_pre)) ” &&
  “ (FenwickRep a bit_l n_pre) ” &&
  “ forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n_pre)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre))))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre)))))) <= INT_MAX))) ” &&
  “ (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos_pre delta_pre) ”
  &&  (intArray.full bit_pre (n_pre + 1) bit_cur)
) \/
(
forall (delta_pre : Int) (pos_pre : Int) (n_pre : Int) (bit_l : (List Int)) (a : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : ((2 * n_pre) <= INT_MAX)) (PreH3 : (1 <= pos_pre)) (PreH4 : (pos_pre <= n_pre)) (PreH5 : (FenwickRep a bit_l n_pre)) (PreH6 : forall (lo_2 : Int) , forall (hi_2 : Int) , ((((1 <= lo_2) ∧ (lo_2 <= hi_2)) ∧ (hi_2 <= n_pre)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo_2) ((hi_2 + 1)) (a))))) ∧ ((ListLib.sum ((sublist (lo_2) ((hi_2 + 1)) (a)))) <= INT_MAX)))) (PreH7 : forall (lo_3 : Int) , forall (hi_3 : Int) , ((((1 <= lo_3) ∧ (lo_3 <= hi_3)) ∧ (hi_3 <= n_pre)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo_3) ((hi_3 + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre))))))) ∧ ((ListLib.sum ((sublist (lo_3) ((hi_3 + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre)))))) <= INT_MAX)))) ,
  TT && emp 
|--
  “ (FenwickAddProgress bit_l bit_l n_pre pos_pre pos_pre delta_pre) ” &&
  “ forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n_pre)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre))))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre)))))) <= INT_MAX))) ”
  &&  emp
)

noncomputable def add_entail_wit_1_split_goal_1 : Prop :=
  forall (delta_pre : Int) (pos_pre : Int) (n_pre : Int) (bit_l : (List Int)) (a : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : ((2 * n_pre) <= INT_MAX)) (PreH3 : (1 <= pos_pre)) (PreH4 : (pos_pre <= n_pre)) (PreH5 : (FenwickRep a bit_l n_pre)) (PreH6 : forall (lo_2 : Int) , forall (hi_2 : Int) , ((((1 <= lo_2) ∧ (lo_2 <= hi_2)) ∧ (hi_2 <= n_pre)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo_2) ((hi_2 + 1)) (a))))) ∧ ((ListLib.sum ((sublist (lo_2) ((hi_2 + 1)) (a)))) <= INT_MAX)))) (PreH7 : forall (lo_3 : Int) , forall (hi_3 : Int) , ((((1 <= lo_3) ∧ (lo_3 <= hi_3)) ∧ (hi_3 <= n_pre)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo_3) ((hi_3 + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre))))))) ∧ ((ListLib.sum ((sublist (lo_3) ((hi_3 + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre)))))) <= INT_MAX)))) ,
  (FenwickAddProgress bit_l bit_l n_pre pos_pre pos_pre delta_pre)

noncomputable def add_entail_wit_1_split_goal_2 : Prop :=
  forall (delta_pre : Int) (pos_pre : Int) (n_pre : Int) (bit_l : (List Int)) (a : (List Int)) (PreH1 : (1 <= n_pre)) (PreH2 : ((2 * n_pre) <= INT_MAX)) (PreH3 : (1 <= pos_pre)) (PreH4 : (pos_pre <= n_pre)) (PreH5 : (FenwickRep a bit_l n_pre)) (PreH6 : forall (lo_2 : Int) , forall (hi_2 : Int) , ((((1 <= lo_2) ∧ (lo_2 <= hi_2)) ∧ (hi_2 <= n_pre)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo_2) ((hi_2 + 1)) (a))))) ∧ ((ListLib.sum ((sublist (lo_2) ((hi_2 + 1)) (a)))) <= INT_MAX)))) (PreH7 : forall (lo_3 : Int) , forall (hi_3 : Int) , ((((1 <= lo_3) ∧ (lo_3 <= hi_3)) ∧ (hi_3 <= n_pre)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo_3) ((hi_3 + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre))))))) ∧ ((ListLib.sum ((sublist (lo_3) ((hi_3 + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre)))))) <= INT_MAX)))) ,
  forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n_pre)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre))))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre)))))) <= INT_MAX)))

noncomputable def add_entail_wit_2 : Prop :=
  (
forall (delta_pre : Int) (pos_pre : Int) (n_pre : Int) (bit_pre : Int) (bit_l : (List Int)) (a : (List Int)) (bit_cur_2 : (List Int)) (pos : Int) (retval : Int) (PreH1 : (retval = (FenwickLowbit (pos)))) (PreH2 : (pos <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : ((2 * n_pre) <= INT_MAX)) (PreH5 : (1 <= pos_pre)) (PreH6 : (pos_pre <= n_pre)) (PreH7 : (1 <= pos)) (PreH8 : (pos <= (2 * n_pre))) (PreH9 : (FenwickRep a bit_l n_pre)) (PreH10 : forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n_pre)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre))))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre)))))) <= INT_MAX)))) (PreH11 : (FenwickAddProgress bit_l bit_cur_2 n_pre pos_pre pos delta_pre)) ,
  (intArray.full bit_pre (n_pre + 1) (replace_Znth (pos) (((Znth pos bit_cur_2 (0 : Int)) + delta_pre)) (bit_cur_2)))
|--
  EX bit_cur : (List Int),
  “ (1 <= n_pre) ” &&
  “ ((2 * n_pre) <= INT_MAX) ” &&
  “ (1 <= pos_pre) ” &&
  “ (pos_pre <= n_pre) ” &&
  “ (1 <= (pos + retval)) ” &&
  “ ((pos + retval) <= (2 * n_pre)) ” &&
  “ (FenwickRep a bit_l n_pre) ” &&
  “ forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n_pre)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre))))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre)))))) <= INT_MAX))) ” &&
  “ (FenwickAddProgress bit_l bit_cur n_pre pos_pre (pos + retval) delta_pre) ”
  &&  (intArray.full bit_pre (n_pre + 1) bit_cur)
) \/
(
forall (delta_pre : Int) (pos_pre : Int) (n_pre : Int) (bit_l : (List Int)) (a : (List Int)) (bit_cur_2 : (List Int)) (pos : Int) (retval : Int) (PreH1 : (retval = (FenwickLowbit (pos)))) (PreH2 : (pos <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : ((2 * n_pre) <= INT_MAX)) (PreH5 : (1 <= pos_pre)) (PreH6 : (pos_pre <= n_pre)) (PreH7 : (1 <= pos)) (PreH8 : (pos <= (2 * n_pre))) (PreH9 : (FenwickRep a bit_l n_pre)) (PreH10 : forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n_pre)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre))))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre)))))) <= INT_MAX)))) (PreH11 : (FenwickAddProgress bit_l bit_cur_2 n_pre pos_pre pos delta_pre)) ,
  TT && emp 
|--
  “ (FenwickAddProgress bit_l (replace_Znth (pos) (((Znth pos bit_cur_2 (0 : Int)) + delta_pre)) (bit_cur_2)) n_pre pos_pre (pos + retval) delta_pre) ” &&
  “ ((pos + retval) <= (2 * n_pre)) ” &&
  “ (1 <= (pos + retval)) ”
  &&  emp
)

noncomputable def add_entail_wit_2_split_goal_1 : Prop :=
  forall (delta_pre : Int) (pos_pre : Int) (n_pre : Int) (bit_l : (List Int)) (a : (List Int)) (bit_cur_2 : (List Int)) (pos : Int) (retval : Int) (PreH1 : (retval = (FenwickLowbit (pos)))) (PreH2 : (pos <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : ((2 * n_pre) <= INT_MAX)) (PreH5 : (1 <= pos_pre)) (PreH6 : (pos_pre <= n_pre)) (PreH7 : (1 <= pos)) (PreH8 : (pos <= (2 * n_pre))) (PreH9 : (FenwickRep a bit_l n_pre)) (PreH10 : forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n_pre)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre))))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre)))))) <= INT_MAX)))) (PreH11 : (FenwickAddProgress bit_l bit_cur_2 n_pre pos_pre pos delta_pre)) ,
  (FenwickAddProgress bit_l (replace_Znth (pos) (((Znth pos bit_cur_2 (0 : Int)) + delta_pre)) (bit_cur_2)) n_pre pos_pre (pos + retval) delta_pre)

noncomputable def add_entail_wit_2_split_goal_2 : Prop :=
  forall (delta_pre : Int) (pos_pre : Int) (n_pre : Int) (bit_l : (List Int)) (a : (List Int)) (bit_cur_2 : (List Int)) (pos : Int) (retval : Int) (PreH1 : (retval = (FenwickLowbit (pos)))) (PreH2 : (pos <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : ((2 * n_pre) <= INT_MAX)) (PreH5 : (1 <= pos_pre)) (PreH6 : (pos_pre <= n_pre)) (PreH7 : (1 <= pos)) (PreH8 : (pos <= (2 * n_pre))) (PreH9 : (FenwickRep a bit_l n_pre)) (PreH10 : forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n_pre)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre))))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre)))))) <= INT_MAX)))) (PreH11 : (FenwickAddProgress bit_l bit_cur_2 n_pre pos_pre pos delta_pre)) ,
  ((pos + retval) <= (2 * n_pre))

noncomputable def add_entail_wit_2_split_goal_3 : Prop :=
  forall (delta_pre : Int) (pos_pre : Int) (n_pre : Int) (bit_l : (List Int)) (a : (List Int)) (bit_cur_2 : (List Int)) (pos : Int) (retval : Int) (PreH1 : (retval = (FenwickLowbit (pos)))) (PreH2 : (pos <= n_pre)) (PreH3 : (1 <= n_pre)) (PreH4 : ((2 * n_pre) <= INT_MAX)) (PreH5 : (1 <= pos_pre)) (PreH6 : (pos_pre <= n_pre)) (PreH7 : (1 <= pos)) (PreH8 : (pos <= (2 * n_pre))) (PreH9 : (FenwickRep a bit_l n_pre)) (PreH10 : forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n_pre)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre))))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre)))))) <= INT_MAX)))) (PreH11 : (FenwickAddProgress bit_l bit_cur_2 n_pre pos_pre pos delta_pre)) ,
  (1 <= (pos + retval))

noncomputable def add_return_wit_1 : Prop :=
  (
forall (delta_pre : Int) (pos_pre : Int) (n_pre : Int) (bit_pre : Int) (bit_l : (List Int)) (a : (List Int)) (bit_cur : (List Int)) (pos : Int) (PreH1 : (pos > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : ((2 * n_pre) <= INT_MAX)) (PreH4 : (1 <= pos_pre)) (PreH5 : (pos_pre <= n_pre)) (PreH6 : (1 <= pos)) (PreH7 : (pos <= (2 * n_pre))) (PreH8 : (FenwickRep a bit_l n_pre)) (PreH9 : forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n_pre)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre))))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre)))))) <= INT_MAX)))) (PreH10 : (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre)) ,
  (intArray.full bit_pre (n_pre + 1) bit_cur)
|--
  EX bit_l1 : (List Int),
  “ (FenwickRep (FenwickAddArray (a) (pos_pre) (delta_pre)) bit_l1 n_pre) ”
  &&  (intArray.full bit_pre (n_pre + 1) bit_l1)
) \/
(
forall (delta_pre : Int) (pos_pre : Int) (n_pre : Int) (bit_l : (List Int)) (a : (List Int)) (bit_cur : (List Int)) (pos : Int) (PreH1 : (pos > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : ((2 * n_pre) <= INT_MAX)) (PreH4 : (1 <= pos_pre)) (PreH5 : (pos_pre <= n_pre)) (PreH6 : (1 <= pos)) (PreH7 : (pos <= (2 * n_pre))) (PreH8 : (FenwickRep a bit_l n_pre)) (PreH9 : forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n_pre)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre))))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre)))))) <= INT_MAX)))) (PreH10 : (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre)) ,
  TT && emp 
|--
  “ (FenwickRep (FenwickAddArray (a) (pos_pre) (delta_pre)) bit_cur n_pre) ”
  &&  emp
)

noncomputable def add_return_wit_1_split_goal_1 : Prop :=
  forall (delta_pre : Int) (pos_pre : Int) (n_pre : Int) (bit_l : (List Int)) (a : (List Int)) (bit_cur : (List Int)) (pos : Int) (PreH1 : (pos > n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : ((2 * n_pre) <= INT_MAX)) (PreH4 : (1 <= pos_pre)) (PreH5 : (pos_pre <= n_pre)) (PreH6 : (1 <= pos)) (PreH7 : (pos <= (2 * n_pre))) (PreH8 : (FenwickRep a bit_l n_pre)) (PreH9 : forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n_pre)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre))))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre)))))) <= INT_MAX)))) (PreH10 : (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre)) ,
  (FenwickRep (FenwickAddArray (a) (pos_pre) (delta_pre)) bit_cur n_pre)

noncomputable def add_partial_solve_wit_1 : Prop :=
  forall (delta_pre : Int) (pos_pre : Int) (n_pre : Int) (bit_pre : Int) (bit_l : (List Int)) (a : (List Int)) (bit_cur : (List Int)) (pos : Int) (PreH1 : (pos <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : ((2 * n_pre) <= INT_MAX)) (PreH4 : (1 <= pos_pre)) (PreH5 : (pos_pre <= n_pre)) (PreH6 : (1 <= pos)) (PreH7 : (pos <= (2 * n_pre))) (PreH8 : (FenwickRep a bit_l n_pre)) (PreH9 : forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n_pre)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre))))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre)))))) <= INT_MAX)))) (PreH10 : (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre)) ,
  (intArray.full bit_pre (n_pre + 1) bit_cur)
|--
  “ (pos <= n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ ((2 * n_pre) <= INT_MAX) ” &&
  “ (1 <= pos_pre) ” &&
  “ (pos_pre <= n_pre) ” &&
  “ (1 <= pos) ” &&
  “ (pos <= (2 * n_pre)) ” &&
  “ (FenwickRep a bit_l n_pre) ” &&
  “ forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n_pre)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre))))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre)))))) <= INT_MAX))) ” &&
  “ (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre) ”
  &&  (((bit_pre + (pos * sizeof(INT)))) # Int |-> ((Znth pos bit_cur (0 : Int))))
  ** (intArray.missing_i bit_pre pos (0 : Int) (n_pre + 1) bit_cur)

noncomputable def add_partial_solve_wit_2 : Prop :=
  forall (delta_pre : Int) (pos_pre : Int) (n_pre : Int) (bit_pre : Int) (bit_l : (List Int)) (a : (List Int)) (bit_cur : (List Int)) (pos : Int) (PreH1 : (pos <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : ((2 * n_pre) <= INT_MAX)) (PreH4 : (1 <= pos_pre)) (PreH5 : (pos_pre <= n_pre)) (PreH6 : (1 <= pos)) (PreH7 : (pos <= (2 * n_pre))) (PreH8 : (FenwickRep a bit_l n_pre)) (PreH9 : forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n_pre)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre))))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre)))))) <= INT_MAX)))) (PreH10 : (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre)) ,
  (intArray.full bit_pre (n_pre + 1) bit_cur)
|--
  “ (pos <= n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ ((2 * n_pre) <= INT_MAX) ” &&
  “ (1 <= pos_pre) ” &&
  “ (pos_pre <= n_pre) ” &&
  “ (1 <= pos) ” &&
  “ (pos <= (2 * n_pre)) ” &&
  “ (FenwickRep a bit_l n_pre) ” &&
  “ forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n_pre)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre))))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre)))))) <= INT_MAX))) ” &&
  “ (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre) ”
  &&  (((bit_pre + (pos * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i bit_pre pos (0 : Int) (n_pre + 1) bit_cur)

noncomputable def add_partial_solve_wit_3_pure : Prop :=
  forall (delta_pre : Int) (pos_pre : Int) (n_pre : Int) (bit_pre : Int) (bit_l : (List Int)) (a : (List Int)) (bit_cur : (List Int)) (pos : Int) (PreH1 : (pos <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : ((2 * n_pre) <= INT_MAX)) (PreH4 : (1 <= pos_pre)) (PreH5 : (pos_pre <= n_pre)) (PreH6 : (1 <= pos)) (PreH7 : (pos <= (2 * n_pre))) (PreH8 : (FenwickRep a bit_l n_pre)) (PreH9 : forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n_pre)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre))))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre)))))) <= INT_MAX)))) (PreH10 : (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre)) ,
  (intArray.full bit_pre (n_pre + 1) (replace_Znth (pos) (((Znth pos bit_cur (0 : Int)) + delta_pre)) (bit_cur)))
  ** ((( &( "bit" ) )) # Ptr |-> (bit_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "delta" ) )) # Int |-> (delta_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
|--
  “ (1 <= pos) ” &&
  “ (pos <= INT_MAX) ”

noncomputable def add_partial_solve_wit_3_aux : Prop :=
  forall (delta_pre : Int) (pos_pre : Int) (n_pre : Int) (bit_pre : Int) (bit_l : (List Int)) (a : (List Int)) (bit_cur : (List Int)) (pos : Int) (PreH1 : (pos <= n_pre)) (PreH2 : (1 <= n_pre)) (PreH3 : ((2 * n_pre) <= INT_MAX)) (PreH4 : (1 <= pos_pre)) (PreH5 : (pos_pre <= n_pre)) (PreH6 : (1 <= pos)) (PreH7 : (pos <= (2 * n_pre))) (PreH8 : (FenwickRep a bit_l n_pre)) (PreH9 : forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n_pre)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre))))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre)))))) <= INT_MAX)))) (PreH10 : (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre)) ,
  (intArray.full bit_pre (n_pre + 1) (replace_Znth (pos) (((Znth pos bit_cur (0 : Int)) + delta_pre)) (bit_cur)))
|--
  “ (1 <= pos) ” &&
  “ (pos <= INT_MAX) ” &&
  “ (pos <= n_pre) ” &&
  “ (1 <= n_pre) ” &&
  “ ((2 * n_pre) <= INT_MAX) ” &&
  “ (1 <= pos_pre) ” &&
  “ (pos_pre <= n_pre) ” &&
  “ (1 <= pos) ” &&
  “ (pos <= (2 * n_pre)) ” &&
  “ (FenwickRep a bit_l n_pre) ” &&
  “ forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n_pre)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre))))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) ((FenwickAddArray (a) (pos_pre) (delta_pre)))))) <= INT_MAX))) ” &&
  “ (FenwickAddProgress bit_l bit_cur n_pre pos_pre pos delta_pre) ”
  &&  (intArray.full bit_pre (n_pre + 1) (replace_Znth (pos) (((Znth pos bit_cur (0 : Int)) + delta_pre)) (bit_cur)))

noncomputable def add_partial_solve_wit_3 : Prop := add_partial_solve_wit_3_pure -> add_partial_solve_wit_3_aux

noncomputable def query_safety_wit_1 : Prop :=
  forall (pos_pre : Int) (bit_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (PreH1 : (1 <= n)) (PreH2 : (n <= INT_MAX)) (PreH3 : ((0 : Int) <= pos_pre)) (PreH4 : (pos_pre <= n)) (PreH5 : (FenwickRep a bit_l n)) (PreH6 : forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) (a))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) (a)))) <= INT_MAX)))) ,
  ((( &( "sum" ) )) # Int |->_)
  ** ((( &( "bit" ) )) # Ptr |-> (bit_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos_pre))
  ** (intArray.full bit_pre (n + 1) bit_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def query_safety_wit_2 : Prop :=
  forall (pos_pre : Int) (bit_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (sum : Int) (pos : Int) (PreH1 : (1 <= n)) (PreH2 : (n <= INT_MAX)) (PreH3 : ((0 : Int) <= pos)) (PreH4 : (pos <= pos_pre)) (PreH5 : (pos_pre <= n)) (PreH6 : (INT_MIN <= sum)) (PreH7 : (sum <= INT_MAX)) (PreH8 : (FenwickRep a bit_l n)) (PreH9 : forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) (a))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) (a)))) <= INT_MAX)))) (PreH10 : (FenwickQueryState a pos_pre pos sum)) ,
  ((( &( "bit" ) )) # Ptr |-> (bit_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "sum" ) )) # Int |-> (sum))
  ** (intArray.full bit_pre (n + 1) bit_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def query_safety_wit_3 : Prop :=
  (
forall (pos_pre : Int) (bit_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (sum : Int) (pos : Int) (PreH1 : (pos > (0 : Int))) (PreH2 : (1 <= n)) (PreH3 : (n <= INT_MAX)) (PreH4 : ((0 : Int) <= pos)) (PreH5 : (pos <= pos_pre)) (PreH6 : (pos_pre <= n)) (PreH7 : (INT_MIN <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : (FenwickRep a bit_l n)) (PreH10 : forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) (a))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) (a)))) <= INT_MAX)))) (PreH11 : (FenwickQueryState a pos_pre pos sum)) ,
  (intArray.full bit_pre (n + 1) bit_l)
  ** ((( &( "bit" ) )) # Ptr |-> (bit_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "sum" ) )) # Int |-> (sum))
|--
  “ ((sum + (Znth pos bit_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (sum + (Znth pos bit_l (0 : Int)))) ”
) \/
(
forall (pos_pre : Int) (bit_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (sum : Int) (pos : Int) (PreH1 : (pos > (0 : Int))) (PreH2 : (1 <= n)) (PreH3 : (n <= INT_MAX)) (PreH4 : ((0 : Int) <= pos)) (PreH5 : (pos <= pos_pre)) (PreH6 : (pos_pre <= n)) (PreH7 : (INT_MIN <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : (FenwickRep a bit_l n)) (PreH10 : forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) (a))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) (a)))) <= INT_MAX)))) (PreH11 : (FenwickQueryState a pos_pre pos sum)) ,
  (intArray.full bit_pre (n + 1) bit_l)
  ** ((( &( "bit" ) )) # Ptr |-> (bit_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "sum" ) )) # Int |-> (sum))
|--
  “ ((sum + (Znth pos bit_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (sum + (Znth pos bit_l (0 : Int)))) ”
)

noncomputable def query_safety_wit_3_split_goal_1 : Prop :=
  forall (pos_pre : Int) (bit_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (sum : Int) (pos : Int) (PreH1 : (pos > (0 : Int))) (PreH2 : (1 <= n)) (PreH3 : (n <= INT_MAX)) (PreH4 : ((0 : Int) <= pos)) (PreH5 : (pos <= pos_pre)) (PreH6 : (pos_pre <= n)) (PreH7 : (INT_MIN <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : (FenwickRep a bit_l n)) (PreH10 : forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) (a))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) (a)))) <= INT_MAX)))) (PreH11 : (FenwickQueryState a pos_pre pos sum)) ,
  (intArray.full bit_pre (n + 1) bit_l)
  ** ((( &( "bit" ) )) # Ptr |-> (bit_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "sum" ) )) # Int |-> (sum))
|--
  “ ((sum + (Znth pos bit_l (0 : Int))) <= INT_MAX) ”

noncomputable def query_safety_wit_3_split_goal_2 : Prop :=
  forall (pos_pre : Int) (bit_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (sum : Int) (pos : Int) (PreH1 : (pos > (0 : Int))) (PreH2 : (1 <= n)) (PreH3 : (n <= INT_MAX)) (PreH4 : ((0 : Int) <= pos)) (PreH5 : (pos <= pos_pre)) (PreH6 : (pos_pre <= n)) (PreH7 : (INT_MIN <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : (FenwickRep a bit_l n)) (PreH10 : forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) (a))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) (a)))) <= INT_MAX)))) (PreH11 : (FenwickQueryState a pos_pre pos sum)) ,
  (intArray.full bit_pre (n + 1) bit_l)
  ** ((( &( "bit" ) )) # Ptr |-> (bit_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "sum" ) )) # Int |-> (sum))
|--
  “ ((INT_MIN) <= (sum + (Znth pos bit_l (0 : Int)))) ”

noncomputable def query_safety_wit_4 : Prop :=
  (
forall (pos_pre : Int) (bit_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (sum : Int) (pos : Int) (retval : Int) (PreH1 : (retval = (FenwickLowbit (pos)))) (PreH2 : (pos > (0 : Int))) (PreH3 : (1 <= n)) (PreH4 : (n <= INT_MAX)) (PreH5 : ((0 : Int) <= pos)) (PreH6 : (pos <= pos_pre)) (PreH7 : (pos_pre <= n)) (PreH8 : (INT_MIN <= sum)) (PreH9 : (sum <= INT_MAX)) (PreH10 : (FenwickRep a bit_l n)) (PreH11 : forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) (a))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) (a)))) <= INT_MAX)))) (PreH12 : (FenwickQueryState a pos_pre pos sum)) ,
  (intArray.full bit_pre (n + 1) bit_l)
  ** ((( &( "bit" ) )) # Ptr |-> (bit_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "sum" ) )) # Int |-> ((sum + (Znth pos bit_l (0 : Int)))))
|--
  “ ((pos - retval) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (pos - retval)) ”
) \/
(
forall (pos_pre : Int) (bit_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (sum : Int) (pos : Int) (retval : Int) (PreH1 : (retval = (FenwickLowbit (pos)))) (PreH2 : (pos > (0 : Int))) (PreH3 : (1 <= n)) (PreH4 : (n <= INT_MAX)) (PreH5 : ((0 : Int) <= pos)) (PreH6 : (pos <= pos_pre)) (PreH7 : (pos_pre <= n)) (PreH8 : (INT_MIN <= sum)) (PreH9 : (sum <= INT_MAX)) (PreH10 : (FenwickRep a bit_l n)) (PreH11 : forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) (a))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) (a)))) <= INT_MAX)))) (PreH12 : (FenwickQueryState a pos_pre pos sum)) ,
  (intArray.full bit_pre (n + 1) bit_l)
  ** ((( &( "bit" ) )) # Ptr |-> (bit_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "sum" ) )) # Int |-> ((sum + (Znth pos bit_l (0 : Int)))))
|--
  “ ((pos - retval) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (pos - retval)) ”
)

noncomputable def query_safety_wit_4_split_goal_1 : Prop :=
  forall (pos_pre : Int) (bit_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (sum : Int) (pos : Int) (retval : Int) (PreH1 : (retval = (FenwickLowbit (pos)))) (PreH2 : (pos > (0 : Int))) (PreH3 : (1 <= n)) (PreH4 : (n <= INT_MAX)) (PreH5 : ((0 : Int) <= pos)) (PreH6 : (pos <= pos_pre)) (PreH7 : (pos_pre <= n)) (PreH8 : (INT_MIN <= sum)) (PreH9 : (sum <= INT_MAX)) (PreH10 : (FenwickRep a bit_l n)) (PreH11 : forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) (a))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) (a)))) <= INT_MAX)))) (PreH12 : (FenwickQueryState a pos_pre pos sum)) ,
  (intArray.full bit_pre (n + 1) bit_l)
  ** ((( &( "bit" ) )) # Ptr |-> (bit_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "sum" ) )) # Int |-> ((sum + (Znth pos bit_l (0 : Int)))))
|--
  “ ((pos - retval) <= INT_MAX) ”

noncomputable def query_safety_wit_4_split_goal_2 : Prop :=
  forall (pos_pre : Int) (bit_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (sum : Int) (pos : Int) (retval : Int) (PreH1 : (retval = (FenwickLowbit (pos)))) (PreH2 : (pos > (0 : Int))) (PreH3 : (1 <= n)) (PreH4 : (n <= INT_MAX)) (PreH5 : ((0 : Int) <= pos)) (PreH6 : (pos <= pos_pre)) (PreH7 : (pos_pre <= n)) (PreH8 : (INT_MIN <= sum)) (PreH9 : (sum <= INT_MAX)) (PreH10 : (FenwickRep a bit_l n)) (PreH11 : forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) (a))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) (a)))) <= INT_MAX)))) (PreH12 : (FenwickQueryState a pos_pre pos sum)) ,
  (intArray.full bit_pre (n + 1) bit_l)
  ** ((( &( "bit" ) )) # Ptr |-> (bit_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "sum" ) )) # Int |-> ((sum + (Znth pos bit_l (0 : Int)))))
|--
  “ ((INT_MIN) <= (pos - retval)) ”

noncomputable def query_entail_wit_1 : Prop :=
  (
forall (pos_pre : Int) (bit_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (PreH1 : (1 <= n)) (PreH2 : (n <= INT_MAX)) (PreH3 : ((0 : Int) <= pos_pre)) (PreH4 : (pos_pre <= n)) (PreH5 : (FenwickRep a bit_l n)) (PreH6 : forall (lo_2 : Int) , forall (hi_2 : Int) , ((((1 <= lo_2) ∧ (lo_2 <= hi_2)) ∧ (hi_2 <= n)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo_2) ((hi_2 + 1)) (a))))) ∧ ((ListLib.sum ((sublist (lo_2) ((hi_2 + 1)) (a)))) <= INT_MAX)))) ,
  (intArray.full bit_pre (n + 1) bit_l)
|--
  “ (1 <= n) ” &&
  “ (n <= INT_MAX) ” &&
  “ ((0 : Int) <= pos_pre) ” &&
  “ (pos_pre <= pos_pre) ” &&
  “ (pos_pre <= n) ” &&
  “ (INT_MIN <= (0 : Int)) ” &&
  “ ((0 : Int) <= INT_MAX) ” &&
  “ (FenwickRep a bit_l n) ” &&
  “ forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) (a))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) (a)))) <= INT_MAX))) ” &&
  “ (FenwickQueryState a pos_pre pos_pre (0 : Int)) ”
  &&  (intArray.full bit_pre (n + 1) bit_l)
) \/
(
forall (pos_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (PreH1 : (1 <= n)) (PreH2 : (n <= INT_MAX)) (PreH3 : ((0 : Int) <= pos_pre)) (PreH4 : (pos_pre <= n)) (PreH5 : (FenwickRep a bit_l n)) (PreH6 : forall (lo_2 : Int) , forall (hi_2 : Int) , ((((1 <= lo_2) ∧ (lo_2 <= hi_2)) ∧ (hi_2 <= n)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo_2) ((hi_2 + 1)) (a))))) ∧ ((ListLib.sum ((sublist (lo_2) ((hi_2 + 1)) (a)))) <= INT_MAX)))) ,
  TT && emp 
|--
  “ (FenwickQueryState a pos_pre pos_pre (0 : Int)) ” &&
  “ forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) (a))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) (a)))) <= INT_MAX))) ”
  &&  emp
)

noncomputable def query_entail_wit_1_split_goal_1 : Prop :=
  forall (pos_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (PreH1 : (1 <= n)) (PreH2 : (n <= INT_MAX)) (PreH3 : ((0 : Int) <= pos_pre)) (PreH4 : (pos_pre <= n)) (PreH5 : (FenwickRep a bit_l n)) (PreH6 : forall (lo_2 : Int) , forall (hi_2 : Int) , ((((1 <= lo_2) ∧ (lo_2 <= hi_2)) ∧ (hi_2 <= n)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo_2) ((hi_2 + 1)) (a))))) ∧ ((ListLib.sum ((sublist (lo_2) ((hi_2 + 1)) (a)))) <= INT_MAX)))) ,
  (FenwickQueryState a pos_pre pos_pre (0 : Int))

noncomputable def query_entail_wit_1_split_goal_2 : Prop :=
  forall (pos_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (PreH1 : (1 <= n)) (PreH2 : (n <= INT_MAX)) (PreH3 : ((0 : Int) <= pos_pre)) (PreH4 : (pos_pre <= n)) (PreH5 : (FenwickRep a bit_l n)) (PreH6 : forall (lo_2 : Int) , forall (hi_2 : Int) , ((((1 <= lo_2) ∧ (lo_2 <= hi_2)) ∧ (hi_2 <= n)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo_2) ((hi_2 + 1)) (a))))) ∧ ((ListLib.sum ((sublist (lo_2) ((hi_2 + 1)) (a)))) <= INT_MAX)))) ,
  forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) (a))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) (a)))) <= INT_MAX)))

noncomputable def query_entail_wit_2 : Prop :=
  (
forall (pos_pre : Int) (bit_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (sum : Int) (pos : Int) (retval : Int) (PreH1 : (retval = (FenwickLowbit (pos)))) (PreH2 : (pos > (0 : Int))) (PreH3 : (1 <= n)) (PreH4 : (n <= INT_MAX)) (PreH5 : ((0 : Int) <= pos)) (PreH6 : (pos <= pos_pre)) (PreH7 : (pos_pre <= n)) (PreH8 : (INT_MIN <= sum)) (PreH9 : (sum <= INT_MAX)) (PreH10 : (FenwickRep a bit_l n)) (PreH11 : forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) (a))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) (a)))) <= INT_MAX)))) (PreH12 : (FenwickQueryState a pos_pre pos sum)) ,
  (intArray.full bit_pre (n + 1) bit_l)
|--
  “ (1 <= n) ” &&
  “ (n <= INT_MAX) ” &&
  “ ((0 : Int) <= (pos - retval)) ” &&
  “ ((pos - retval) <= pos_pre) ” &&
  “ (pos_pre <= n) ” &&
  “ (INT_MIN <= (sum + (Znth pos bit_l (0 : Int)))) ” &&
  “ ((sum + (Znth pos bit_l (0 : Int))) <= INT_MAX) ” &&
  “ (FenwickRep a bit_l n) ” &&
  “ forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) (a))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) (a)))) <= INT_MAX))) ” &&
  “ (FenwickQueryState a pos_pre (pos - retval) (sum + (Znth pos bit_l (0 : Int)))) ”
  &&  (intArray.full bit_pre (n + 1) bit_l)
) \/
(
forall (pos_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (sum : Int) (pos : Int) (retval : Int) (PreH1 : (retval = (FenwickLowbit (pos)))) (PreH2 : (pos > (0 : Int))) (PreH3 : (1 <= n)) (PreH4 : (n <= INT_MAX)) (PreH5 : ((0 : Int) <= pos)) (PreH6 : (pos <= pos_pre)) (PreH7 : (pos_pre <= n)) (PreH8 : (INT_MIN <= sum)) (PreH9 : (sum <= INT_MAX)) (PreH10 : (FenwickRep a bit_l n)) (PreH11 : forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) (a))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) (a)))) <= INT_MAX)))) (PreH12 : (FenwickQueryState a pos_pre pos sum)) ,
  TT && emp 
|--
  “ (FenwickQueryState a pos_pre (pos - retval) (sum + (Znth pos bit_l (0 : Int)))) ” &&
  “ ((sum + (Znth pos bit_l (0 : Int))) <= INT_MAX) ” &&
  “ (INT_MIN <= (sum + (Znth pos bit_l (0 : Int)))) ” &&
  “ ((pos - retval) <= pos_pre) ” &&
  “ ((0 : Int) <= (pos - retval)) ”
  &&  emp
)

noncomputable def query_entail_wit_2_split_goal_1 : Prop :=
  forall (pos_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (sum : Int) (pos : Int) (retval : Int) (PreH1 : (retval = (FenwickLowbit (pos)))) (PreH2 : (pos > (0 : Int))) (PreH3 : (1 <= n)) (PreH4 : (n <= INT_MAX)) (PreH5 : ((0 : Int) <= pos)) (PreH6 : (pos <= pos_pre)) (PreH7 : (pos_pre <= n)) (PreH8 : (INT_MIN <= sum)) (PreH9 : (sum <= INT_MAX)) (PreH10 : (FenwickRep a bit_l n)) (PreH11 : forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) (a))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) (a)))) <= INT_MAX)))) (PreH12 : (FenwickQueryState a pos_pre pos sum)) ,
  (FenwickQueryState a pos_pre (pos - retval) (sum + (Znth pos bit_l (0 : Int))))

noncomputable def query_entail_wit_2_split_goal_2 : Prop :=
  forall (pos_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (sum : Int) (pos : Int) (retval : Int) (PreH1 : (retval = (FenwickLowbit (pos)))) (PreH2 : (pos > (0 : Int))) (PreH3 : (1 <= n)) (PreH4 : (n <= INT_MAX)) (PreH5 : ((0 : Int) <= pos)) (PreH6 : (pos <= pos_pre)) (PreH7 : (pos_pre <= n)) (PreH8 : (INT_MIN <= sum)) (PreH9 : (sum <= INT_MAX)) (PreH10 : (FenwickRep a bit_l n)) (PreH11 : forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) (a))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) (a)))) <= INT_MAX)))) (PreH12 : (FenwickQueryState a pos_pre pos sum)) ,
  ((sum + (Znth pos bit_l (0 : Int))) <= INT_MAX)

noncomputable def query_entail_wit_2_split_goal_3 : Prop :=
  forall (pos_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (sum : Int) (pos : Int) (retval : Int) (PreH1 : (retval = (FenwickLowbit (pos)))) (PreH2 : (pos > (0 : Int))) (PreH3 : (1 <= n)) (PreH4 : (n <= INT_MAX)) (PreH5 : ((0 : Int) <= pos)) (PreH6 : (pos <= pos_pre)) (PreH7 : (pos_pre <= n)) (PreH8 : (INT_MIN <= sum)) (PreH9 : (sum <= INT_MAX)) (PreH10 : (FenwickRep a bit_l n)) (PreH11 : forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) (a))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) (a)))) <= INT_MAX)))) (PreH12 : (FenwickQueryState a pos_pre pos sum)) ,
  (INT_MIN <= (sum + (Znth pos bit_l (0 : Int))))

noncomputable def query_entail_wit_2_split_goal_4 : Prop :=
  forall (pos_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (sum : Int) (pos : Int) (retval : Int) (PreH1 : (retval = (FenwickLowbit (pos)))) (PreH2 : (pos > (0 : Int))) (PreH3 : (1 <= n)) (PreH4 : (n <= INT_MAX)) (PreH5 : ((0 : Int) <= pos)) (PreH6 : (pos <= pos_pre)) (PreH7 : (pos_pre <= n)) (PreH8 : (INT_MIN <= sum)) (PreH9 : (sum <= INT_MAX)) (PreH10 : (FenwickRep a bit_l n)) (PreH11 : forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) (a))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) (a)))) <= INT_MAX)))) (PreH12 : (FenwickQueryState a pos_pre pos sum)) ,
  ((pos - retval) <= pos_pre)

noncomputable def query_entail_wit_2_split_goal_5 : Prop :=
  forall (pos_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (sum : Int) (pos : Int) (retval : Int) (PreH1 : (retval = (FenwickLowbit (pos)))) (PreH2 : (pos > (0 : Int))) (PreH3 : (1 <= n)) (PreH4 : (n <= INT_MAX)) (PreH5 : ((0 : Int) <= pos)) (PreH6 : (pos <= pos_pre)) (PreH7 : (pos_pre <= n)) (PreH8 : (INT_MIN <= sum)) (PreH9 : (sum <= INT_MAX)) (PreH10 : (FenwickRep a bit_l n)) (PreH11 : forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) (a))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) (a)))) <= INT_MAX)))) (PreH12 : (FenwickQueryState a pos_pre pos sum)) ,
  ((0 : Int) <= (pos - retval))

noncomputable def query_return_wit_1 : Prop :=
  (
forall (pos_pre : Int) (bit_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (sum : Int) (pos : Int) (PreH1 : (pos <= (0 : Int))) (PreH2 : (1 <= n)) (PreH3 : (n <= INT_MAX)) (PreH4 : ((0 : Int) <= pos)) (PreH5 : (pos <= pos_pre)) (PreH6 : (pos_pre <= n)) (PreH7 : (INT_MIN <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : (FenwickRep a bit_l n)) (PreH10 : forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) (a))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) (a)))) <= INT_MAX)))) (PreH11 : (FenwickQueryState a pos_pre pos sum)) ,
  (intArray.full bit_pre (n + 1) bit_l)
|--
  “ (sum = (FenwickPrefixSum (a) (pos_pre))) ”
  &&  (intArray.full bit_pre (n + 1) bit_l)
) \/
(
forall (pos_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (sum : Int) (pos : Int) (PreH1 : (pos <= (0 : Int))) (PreH2 : (1 <= n)) (PreH3 : (n <= INT_MAX)) (PreH4 : ((0 : Int) <= pos)) (PreH5 : (pos <= pos_pre)) (PreH6 : (pos_pre <= n)) (PreH7 : (INT_MIN <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : (FenwickRep a bit_l n)) (PreH10 : forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) (a))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) (a)))) <= INT_MAX)))) (PreH11 : (FenwickQueryState a pos_pre pos sum)) ,
  TT && emp 
|--
  “ (sum = (FenwickPrefixSum (a) (pos_pre))) ”
  &&  emp
)

noncomputable def query_return_wit_1_split_goal_1 : Prop :=
  forall (pos_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (sum : Int) (pos : Int) (PreH1 : (pos <= (0 : Int))) (PreH2 : (1 <= n)) (PreH3 : (n <= INT_MAX)) (PreH4 : ((0 : Int) <= pos)) (PreH5 : (pos <= pos_pre)) (PreH6 : (pos_pre <= n)) (PreH7 : (INT_MIN <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : (FenwickRep a bit_l n)) (PreH10 : forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) (a))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) (a)))) <= INT_MAX)))) (PreH11 : (FenwickQueryState a pos_pre pos sum)) ,
  (sum = (FenwickPrefixSum (a) (pos_pre)))

noncomputable def query_partial_solve_wit_1 : Prop :=
  forall (pos_pre : Int) (bit_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (sum : Int) (pos : Int) (PreH1 : (pos > (0 : Int))) (PreH2 : (1 <= n)) (PreH3 : (n <= INT_MAX)) (PreH4 : ((0 : Int) <= pos)) (PreH5 : (pos <= pos_pre)) (PreH6 : (pos_pre <= n)) (PreH7 : (INT_MIN <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : (FenwickRep a bit_l n)) (PreH10 : forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) (a))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) (a)))) <= INT_MAX)))) (PreH11 : (FenwickQueryState a pos_pre pos sum)) ,
  (intArray.full bit_pre (n + 1) bit_l)
|--
  “ (pos > (0 : Int)) ” &&
  “ (1 <= n) ” &&
  “ (n <= INT_MAX) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= pos_pre) ” &&
  “ (pos_pre <= n) ” &&
  “ (INT_MIN <= sum) ” &&
  “ (sum <= INT_MAX) ” &&
  “ (FenwickRep a bit_l n) ” &&
  “ forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) (a))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) (a)))) <= INT_MAX))) ” &&
  “ (FenwickQueryState a pos_pre pos sum) ”
  &&  (((bit_pre + (pos * sizeof(INT)))) # Int |-> ((Znth pos bit_l (0 : Int))))
  ** (intArray.missing_i bit_pre pos (0 : Int) (n + 1) bit_l)

noncomputable def query_partial_solve_wit_2_pure : Prop :=
  forall (pos_pre : Int) (bit_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (sum : Int) (pos : Int) (PreH1 : (pos > (0 : Int))) (PreH2 : (1 <= n)) (PreH3 : (n <= INT_MAX)) (PreH4 : ((0 : Int) <= pos)) (PreH5 : (pos <= pos_pre)) (PreH6 : (pos_pre <= n)) (PreH7 : (INT_MIN <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : (FenwickRep a bit_l n)) (PreH10 : forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) (a))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) (a)))) <= INT_MAX)))) (PreH11 : (FenwickQueryState a pos_pre pos sum)) ,
  (intArray.full bit_pre (n + 1) bit_l)
  ** ((( &( "bit" ) )) # Ptr |-> (bit_pre))
  ** ((( &( "pos" ) )) # Int |-> (pos))
  ** ((( &( "sum" ) )) # Int |-> ((sum + (Znth pos bit_l (0 : Int)))))
|--
  “ (1 <= pos) ” &&
  “ (pos <= INT_MAX) ”

noncomputable def query_partial_solve_wit_2_aux : Prop :=
  forall (pos_pre : Int) (bit_pre : Int) (n : Int) (bit_l : (List Int)) (a : (List Int)) (sum : Int) (pos : Int) (PreH1 : (pos > (0 : Int))) (PreH2 : (1 <= n)) (PreH3 : (n <= INT_MAX)) (PreH4 : ((0 : Int) <= pos)) (PreH5 : (pos <= pos_pre)) (PreH6 : (pos_pre <= n)) (PreH7 : (INT_MIN <= sum)) (PreH8 : (sum <= INT_MAX)) (PreH9 : (FenwickRep a bit_l n)) (PreH10 : forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) (a))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) (a)))) <= INT_MAX)))) (PreH11 : (FenwickQueryState a pos_pre pos sum)) ,
  (intArray.full bit_pre (n + 1) bit_l)
|--
  “ (1 <= pos) ” &&
  “ (pos <= INT_MAX) ” &&
  “ (pos > (0 : Int)) ” &&
  “ (1 <= n) ” &&
  “ (n <= INT_MAX) ” &&
  “ ((0 : Int) <= pos) ” &&
  “ (pos <= pos_pre) ” &&
  “ (pos_pre <= n) ” &&
  “ (INT_MIN <= sum) ” &&
  “ (sum <= INT_MAX) ” &&
  “ (FenwickRep a bit_l n) ” &&
  “ forall (lo : Int) , forall (hi : Int) , ((((1 <= lo) ∧ (lo <= hi)) ∧ (hi <= n)) -> ((INT_MIN <= (ListLib.sum ((sublist (lo) ((hi + 1)) (a))))) ∧ ((ListLib.sum ((sublist (lo) ((hi + 1)) (a)))) <= INT_MAX))) ” &&
  “ (FenwickQueryState a pos_pre pos sum) ”
  &&  (intArray.full bit_pre (n + 1) bit_l)

noncomputable def query_partial_solve_wit_2 : Prop := query_partial_solve_wit_2_pure -> query_partial_solve_wit_2_aux


structure VC_Correct : Type where
  proof_of_lowbit_safety_wit_1 : lowbit_safety_wit_1
  proof_of_add_partial_solve_wit_1 : add_partial_solve_wit_1
  proof_of_add_partial_solve_wit_2 : add_partial_solve_wit_2
  proof_of_add_partial_solve_wit_3_pure : add_partial_solve_wit_3_pure
  proof_of_add_partial_solve_wit_3 : add_partial_solve_wit_3
  proof_of_query_safety_wit_1 : query_safety_wit_1
  proof_of_query_safety_wit_2 : query_safety_wit_2
  proof_of_query_partial_solve_wit_1 : query_partial_solve_wit_1
  proof_of_query_partial_solve_wit_2_pure : query_partial_solve_wit_2_pure
  proof_of_query_partial_solve_wit_2 : query_partial_solve_wit_2
  proof_of_lowbit_return_wit_1 : lowbit_return_wit_1
  proof_of_add_safety_wit_1 : add_safety_wit_1
  proof_of_add_safety_wit_2 : add_safety_wit_2
  proof_of_add_entail_wit_1 : add_entail_wit_1
  proof_of_add_entail_wit_2 : add_entail_wit_2
  proof_of_add_return_wit_1 : add_return_wit_1
  proof_of_query_safety_wit_3 : query_safety_wit_3
  proof_of_query_safety_wit_4 : query_safety_wit_4
  proof_of_query_entail_wit_1 : query_entail_wit_1
  proof_of_query_entail_wit_2 : query_entail_wit_2
  proof_of_query_return_wit_1 : query_return_wit_1

end SimpleC.EE.LLM_bench.Data_structures.binary_indexed_tree.binary_indexed_tree_goal
