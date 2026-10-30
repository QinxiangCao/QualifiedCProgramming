import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Algorithms.sort_point.sort_point_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.sort_point.sort_point_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance sort_point_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def cmp_polar_values_safety_wit_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((-10000) <= gx_pre)) (PreH2 : (gx_pre <= 10000)) (PreH3 : ((-10000) <= gy_pre)) (PreH4 : (gy_pre <= 10000)) (PreH5 : ((-10000) <= a_x_pre)) (PreH6 : (a_x_pre <= 10000)) (PreH7 : ((-10000) <= a_y_pre)) (PreH8 : (a_y_pre <= 10000)) (PreH9 : ((-10000) <= b_x_pre)) (PreH10 : (b_x_pre <= 10000)) (PreH11 : ((-10000) <= b_y_pre)) (PreH12 : (b_y_pre <= 10000)) ,
  ((( &( "adx" ) )) # Int |->_)
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ ((a_x_pre - gx_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (a_x_pre - gx_pre)) ”

noncomputable def cmp_polar_values_safety_wit_2 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((-10000) <= gx_pre)) (PreH2 : (gx_pre <= 10000)) (PreH3 : ((-10000) <= gy_pre)) (PreH4 : (gy_pre <= 10000)) (PreH5 : ((-10000) <= a_x_pre)) (PreH6 : (a_x_pre <= 10000)) (PreH7 : ((-10000) <= a_y_pre)) (PreH8 : (a_y_pre <= 10000)) (PreH9 : ((-10000) <= b_x_pre)) (PreH10 : (b_x_pre <= 10000)) (PreH11 : ((-10000) <= b_y_pre)) (PreH12 : (b_y_pre <= 10000)) ,
  ((( &( "ady" ) )) # Int |->_)
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ ((a_y_pre - gy_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (a_y_pre - gy_pre)) ”

noncomputable def cmp_polar_values_safety_wit_3 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((-10000) <= gx_pre)) (PreH2 : (gx_pre <= 10000)) (PreH3 : ((-10000) <= gy_pre)) (PreH4 : (gy_pre <= 10000)) (PreH5 : ((-10000) <= a_x_pre)) (PreH6 : (a_x_pre <= 10000)) (PreH7 : ((-10000) <= a_y_pre)) (PreH8 : (a_y_pre <= 10000)) (PreH9 : ((-10000) <= b_x_pre)) (PreH10 : (b_x_pre <= 10000)) (PreH11 : ((-10000) <= b_y_pre)) (PreH12 : (b_y_pre <= 10000)) ,
  ((( &( "bdx" ) )) # Int |->_)
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ ((b_x_pre - gx_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (b_x_pre - gx_pre)) ”

noncomputable def cmp_polar_values_safety_wit_4 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((-10000) <= gx_pre)) (PreH2 : (gx_pre <= 10000)) (PreH3 : ((-10000) <= gy_pre)) (PreH4 : (gy_pre <= 10000)) (PreH5 : ((-10000) <= a_x_pre)) (PreH6 : (a_x_pre <= 10000)) (PreH7 : ((-10000) <= a_y_pre)) (PreH8 : (a_y_pre <= 10000)) (PreH9 : ((-10000) <= b_x_pre)) (PreH10 : (b_x_pre <= 10000)) (PreH11 : ((-10000) <= b_y_pre)) (PreH12 : (b_y_pre <= 10000)) ,
  ((( &( "bdy" ) )) # Int |->_)
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ ((b_y_pre - gy_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (b_y_pre - gy_pre)) ”

noncomputable def cmp_polar_values_safety_wit_5 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((-10000) <= gx_pre)) (PreH2 : (gx_pre <= 10000)) (PreH3 : ((-10000) <= gy_pre)) (PreH4 : (gy_pre <= 10000)) (PreH5 : ((-10000) <= a_x_pre)) (PreH6 : (a_x_pre <= 10000)) (PreH7 : ((-10000) <= a_y_pre)) (PreH8 : (a_y_pre <= 10000)) (PreH9 : ((-10000) <= b_x_pre)) (PreH10 : (b_x_pre <= 10000)) (PreH11 : ((-10000) <= b_y_pre)) (PreH12 : (b_y_pre <= 10000)) ,
  ((( &( "cr" ) )) # Int |->_)
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))) ”

noncomputable def cmp_polar_values_safety_wit_6 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((-10000) <= gx_pre)) (PreH2 : (gx_pre <= 10000)) (PreH3 : ((-10000) <= gy_pre)) (PreH4 : (gy_pre <= 10000)) (PreH5 : ((-10000) <= a_x_pre)) (PreH6 : (a_x_pre <= 10000)) (PreH7 : ((-10000) <= a_y_pre)) (PreH8 : (a_y_pre <= 10000)) (PreH9 : ((-10000) <= b_x_pre)) (PreH10 : (b_x_pre <= 10000)) (PreH11 : ((-10000) <= b_y_pre)) (PreH12 : (b_y_pre <= 10000)) ,
  ((( &( "cr" ) )) # Int |->_)
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (((a_y_pre - gy_pre) * (b_x_pre - gx_pre)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) ”

noncomputable def cmp_polar_values_safety_wit_7 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((-10000) <= gx_pre)) (PreH2 : (gx_pre <= 10000)) (PreH3 : ((-10000) <= gy_pre)) (PreH4 : (gy_pre <= 10000)) (PreH5 : ((-10000) <= a_x_pre)) (PreH6 : (a_x_pre <= 10000)) (PreH7 : ((-10000) <= a_y_pre)) (PreH8 : (a_y_pre <= 10000)) (PreH9 : ((-10000) <= b_x_pre)) (PreH10 : (b_x_pre <= 10000)) (PreH11 : ((-10000) <= b_y_pre)) (PreH12 : (b_y_pre <= 10000)) ,
  ((( &( "cr" ) )) # Int |->_)
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((a_x_pre - gx_pre) * (b_y_pre - gy_pre))) ”

noncomputable def cmp_polar_values_safety_wit_8 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((-10000) <= gx_pre)) (PreH2 : (gx_pre <= 10000)) (PreH3 : ((-10000) <= gy_pre)) (PreH4 : (gy_pre <= 10000)) (PreH5 : ((-10000) <= a_x_pre)) (PreH6 : (a_x_pre <= 10000)) (PreH7 : ((-10000) <= a_y_pre)) (PreH8 : (a_y_pre <= 10000)) (PreH9 : ((-10000) <= b_x_pre)) (PreH10 : (b_x_pre <= 10000)) (PreH11 : ((-10000) <= b_y_pre)) (PreH12 : (b_y_pre <= 10000)) ,
  ((( &( "da" ) )) # Int |->_)
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))) ”

noncomputable def cmp_polar_values_safety_wit_9 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((-10000) <= gx_pre)) (PreH2 : (gx_pre <= 10000)) (PreH3 : ((-10000) <= gy_pre)) (PreH4 : (gy_pre <= 10000)) (PreH5 : ((-10000) <= a_x_pre)) (PreH6 : (a_x_pre <= 10000)) (PreH7 : ((-10000) <= a_y_pre)) (PreH8 : (a_y_pre <= 10000)) (PreH9 : ((-10000) <= b_x_pre)) (PreH10 : (b_x_pre <= 10000)) (PreH11 : ((-10000) <= b_y_pre)) (PreH12 : (b_y_pre <= 10000)) ,
  ((( &( "da" ) )) # Int |->_)
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (((a_y_pre - gy_pre) * (a_y_pre - gy_pre)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) ”

noncomputable def cmp_polar_values_safety_wit_10 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((-10000) <= gx_pre)) (PreH2 : (gx_pre <= 10000)) (PreH3 : ((-10000) <= gy_pre)) (PreH4 : (gy_pre <= 10000)) (PreH5 : ((-10000) <= a_x_pre)) (PreH6 : (a_x_pre <= 10000)) (PreH7 : ((-10000) <= a_y_pre)) (PreH8 : (a_y_pre <= 10000)) (PreH9 : ((-10000) <= b_x_pre)) (PreH10 : (b_x_pre <= 10000)) (PreH11 : ((-10000) <= b_y_pre)) (PreH12 : (b_y_pre <= 10000)) ,
  ((( &( "da" ) )) # Int |->_)
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((a_x_pre - gx_pre) * (a_x_pre - gx_pre))) ”

noncomputable def cmp_polar_values_safety_wit_11 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((-10000) <= gx_pre)) (PreH2 : (gx_pre <= 10000)) (PreH3 : ((-10000) <= gy_pre)) (PreH4 : (gy_pre <= 10000)) (PreH5 : ((-10000) <= a_x_pre)) (PreH6 : (a_x_pre <= 10000)) (PreH7 : ((-10000) <= a_y_pre)) (PreH8 : (a_y_pre <= 10000)) (PreH9 : ((-10000) <= b_x_pre)) (PreH10 : (b_x_pre <= 10000)) (PreH11 : ((-10000) <= b_y_pre)) (PreH12 : (b_y_pre <= 10000)) ,
  ((( &( "db" ) )) # Int |->_)
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))) ”

noncomputable def cmp_polar_values_safety_wit_12 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((-10000) <= gx_pre)) (PreH2 : (gx_pre <= 10000)) (PreH3 : ((-10000) <= gy_pre)) (PreH4 : (gy_pre <= 10000)) (PreH5 : ((-10000) <= a_x_pre)) (PreH6 : (a_x_pre <= 10000)) (PreH7 : ((-10000) <= a_y_pre)) (PreH8 : (a_y_pre <= 10000)) (PreH9 : ((-10000) <= b_x_pre)) (PreH10 : (b_x_pre <= 10000)) (PreH11 : ((-10000) <= b_y_pre)) (PreH12 : (b_y_pre <= 10000)) ,
  ((( &( "db" ) )) # Int |->_)
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (((b_y_pre - gy_pre) * (b_y_pre - gy_pre)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))) ”

noncomputable def cmp_polar_values_safety_wit_13 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((-10000) <= gx_pre)) (PreH2 : (gx_pre <= 10000)) (PreH3 : ((-10000) <= gy_pre)) (PreH4 : (gy_pre <= 10000)) (PreH5 : ((-10000) <= a_x_pre)) (PreH6 : (a_x_pre <= 10000)) (PreH7 : ((-10000) <= a_y_pre)) (PreH8 : (a_y_pre <= 10000)) (PreH9 : ((-10000) <= b_x_pre)) (PreH10 : (b_x_pre <= 10000)) (PreH11 : ((-10000) <= b_y_pre)) (PreH12 : (b_y_pre <= 10000)) ,
  ((( &( "db" ) )) # Int |->_)
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((b_x_pre - gx_pre) * (b_x_pre - gx_pre))) ”

noncomputable def cmp_polar_values_safety_wit_14 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((-10000) <= gx_pre)) (PreH2 : (gx_pre <= 10000)) (PreH3 : ((-10000) <= gy_pre)) (PreH4 : (gy_pre <= 10000)) (PreH5 : ((-10000) <= a_x_pre)) (PreH6 : (a_x_pre <= 10000)) (PreH7 : ((-10000) <= a_y_pre)) (PreH8 : (a_y_pre <= 10000)) (PreH9 : ((-10000) <= b_x_pre)) (PreH10 : (b_x_pre <= 10000)) (PreH11 : ((-10000) <= b_y_pre)) (PreH12 : (b_y_pre <= 10000)) ,
  ((( &( "ah" ) )) # Int |->_)
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def cmp_polar_values_safety_wit_15 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((-10000) <= gx_pre)) (PreH2 : (gx_pre <= 10000)) (PreH3 : ((-10000) <= gy_pre)) (PreH4 : (gy_pre <= 10000)) (PreH5 : ((-10000) <= a_x_pre)) (PreH6 : (a_x_pre <= 10000)) (PreH7 : ((-10000) <= a_y_pre)) (PreH8 : (a_y_pre <= 10000)) (PreH9 : ((-10000) <= b_x_pre)) (PreH10 : (b_x_pre <= 10000)) (PreH11 : ((-10000) <= b_y_pre)) (PreH12 : (b_y_pre <= 10000)) ,
  ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def cmp_polar_values_safety_wit_16 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH2 : ((-10000) <= gx_pre)) (PreH3 : (gx_pre <= 10000)) (PreH4 : ((-10000) <= gy_pre)) (PreH5 : (gy_pre <= 10000)) (PreH6 : ((-10000) <= a_x_pre)) (PreH7 : (a_x_pre <= 10000)) (PreH8 : ((-10000) <= a_y_pre)) (PreH9 : (a_y_pre <= 10000)) (PreH10 : ((-10000) <= b_x_pre)) (PreH11 : (b_x_pre <= 10000)) (PreH12 : ((-10000) <= b_y_pre)) (PreH13 : (b_y_pre <= 10000)) ,
  ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_17 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH2 : ((-10000) <= gx_pre)) (PreH3 : (gx_pre <= 10000)) (PreH4 : ((-10000) <= gy_pre)) (PreH5 : (gy_pre <= 10000)) (PreH6 : ((-10000) <= a_x_pre)) (PreH7 : (a_x_pre <= 10000)) (PreH8 : ((-10000) <= a_y_pre)) (PreH9 : (a_y_pre <= 10000)) (PreH10 : ((-10000) <= b_x_pre)) (PreH11 : (b_x_pre <= 10000)) (PreH12 : ((-10000) <= b_y_pre)) (PreH13 : (b_y_pre <= 10000)) ,
  ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def cmp_polar_values_safety_wit_18 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH2 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH3 : ((-10000) <= gx_pre)) (PreH4 : (gx_pre <= 10000)) (PreH5 : ((-10000) <= gy_pre)) (PreH6 : (gy_pre <= 10000)) (PreH7 : ((-10000) <= a_x_pre)) (PreH8 : (a_x_pre <= 10000)) (PreH9 : ((-10000) <= a_y_pre)) (PreH10 : (a_y_pre <= 10000)) (PreH11 : ((-10000) <= b_x_pre)) (PreH12 : (b_x_pre <= 10000)) (PreH13 : ((-10000) <= b_y_pre)) (PreH14 : (b_y_pre <= 10000)) ,
  ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def cmp_polar_values_safety_wit_19 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH2 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH3 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((-10000) <= gx_pre)) (PreH5 : (gx_pre <= 10000)) (PreH6 : ((-10000) <= gy_pre)) (PreH7 : (gy_pre <= 10000)) (PreH8 : ((-10000) <= a_x_pre)) (PreH9 : (a_x_pre <= 10000)) (PreH10 : ((-10000) <= a_y_pre)) (PreH11 : (a_y_pre <= 10000)) (PreH12 : ((-10000) <= b_x_pre)) (PreH13 : (b_x_pre <= 10000)) (PreH14 : ((-10000) <= b_y_pre)) (PreH15 : (b_y_pre <= 10000)) ,
  ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_20 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH2 : ((-10000) <= gx_pre)) (PreH3 : (gx_pre <= 10000)) (PreH4 : ((-10000) <= gy_pre)) (PreH5 : (gy_pre <= 10000)) (PreH6 : ((-10000) <= a_x_pre)) (PreH7 : (a_x_pre <= 10000)) (PreH8 : ((-10000) <= a_y_pre)) (PreH9 : (a_y_pre <= 10000)) (PreH10 : ((-10000) <= b_x_pre)) (PreH11 : (b_x_pre <= 10000)) (PreH12 : ((-10000) <= b_y_pre)) (PreH13 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |->_)
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def cmp_polar_values_safety_wit_21 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH2 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH3 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((-10000) <= gx_pre)) (PreH5 : (gx_pre <= 10000)) (PreH6 : ((-10000) <= gy_pre)) (PreH7 : (gy_pre <= 10000)) (PreH8 : ((-10000) <= a_x_pre)) (PreH9 : (a_x_pre <= 10000)) (PreH10 : ((-10000) <= a_y_pre)) (PreH11 : (a_y_pre <= 10000)) (PreH12 : ((-10000) <= b_x_pre)) (PreH13 : (b_x_pre <= 10000)) (PreH14 : ((-10000) <= b_y_pre)) (PreH15 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |->_)
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def cmp_polar_values_safety_wit_22 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH2 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH3 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((-10000) <= gx_pre)) (PreH5 : (gx_pre <= 10000)) (PreH6 : ((-10000) <= gy_pre)) (PreH7 : (gy_pre <= 10000)) (PreH8 : ((-10000) <= a_x_pre)) (PreH9 : (a_x_pre <= 10000)) (PreH10 : ((-10000) <= a_y_pre)) (PreH11 : (a_y_pre <= 10000)) (PreH12 : ((-10000) <= b_x_pre)) (PreH13 : (b_x_pre <= 10000)) (PreH14 : ((-10000) <= b_y_pre)) (PreH15 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |->_)
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def cmp_polar_values_safety_wit_23 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH2 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH3 : ((-10000) <= gx_pre)) (PreH4 : (gx_pre <= 10000)) (PreH5 : ((-10000) <= gy_pre)) (PreH6 : (gy_pre <= 10000)) (PreH7 : ((-10000) <= a_x_pre)) (PreH8 : (a_x_pre <= 10000)) (PreH9 : ((-10000) <= a_y_pre)) (PreH10 : (a_y_pre <= 10000)) (PreH11 : ((-10000) <= b_x_pre)) (PreH12 : (b_x_pre <= 10000)) (PreH13 : ((-10000) <= b_y_pre)) (PreH14 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |->_)
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def cmp_polar_values_safety_wit_24 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH2 : ((-10000) <= gx_pre)) (PreH3 : (gx_pre <= 10000)) (PreH4 : ((-10000) <= gy_pre)) (PreH5 : (gy_pre <= 10000)) (PreH6 : ((-10000) <= a_x_pre)) (PreH7 : (a_x_pre <= 10000)) (PreH8 : ((-10000) <= a_y_pre)) (PreH9 : (a_y_pre <= 10000)) (PreH10 : ((-10000) <= b_x_pre)) (PreH11 : (b_x_pre <= 10000)) (PreH12 : ((-10000) <= b_y_pre)) (PreH13 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def cmp_polar_values_safety_wit_25 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH2 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH3 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((-10000) <= gx_pre)) (PreH5 : (gx_pre <= 10000)) (PreH6 : ((-10000) <= gy_pre)) (PreH7 : (gy_pre <= 10000)) (PreH8 : ((-10000) <= a_x_pre)) (PreH9 : (a_x_pre <= 10000)) (PreH10 : ((-10000) <= a_y_pre)) (PreH11 : (a_y_pre <= 10000)) (PreH12 : ((-10000) <= b_x_pre)) (PreH13 : (b_x_pre <= 10000)) (PreH14 : ((-10000) <= b_y_pre)) (PreH15 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def cmp_polar_values_safety_wit_26 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH2 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH3 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((-10000) <= gx_pre)) (PreH5 : (gx_pre <= 10000)) (PreH6 : ((-10000) <= gy_pre)) (PreH7 : (gy_pre <= 10000)) (PreH8 : ((-10000) <= a_x_pre)) (PreH9 : (a_x_pre <= 10000)) (PreH10 : ((-10000) <= a_y_pre)) (PreH11 : (a_y_pre <= 10000)) (PreH12 : ((-10000) <= b_x_pre)) (PreH13 : (b_x_pre <= 10000)) (PreH14 : ((-10000) <= b_y_pre)) (PreH15 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def cmp_polar_values_safety_wit_27 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH2 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH3 : ((-10000) <= gx_pre)) (PreH4 : (gx_pre <= 10000)) (PreH5 : ((-10000) <= gy_pre)) (PreH6 : (gy_pre <= 10000)) (PreH7 : ((-10000) <= a_x_pre)) (PreH8 : (a_x_pre <= 10000)) (PreH9 : ((-10000) <= a_y_pre)) (PreH10 : (a_y_pre <= 10000)) (PreH11 : ((-10000) <= b_x_pre)) (PreH12 : (b_x_pre <= 10000)) (PreH13 : ((-10000) <= b_y_pre)) (PreH14 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def cmp_polar_values_safety_wit_28 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH2 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH3 : ((-10000) <= gx_pre)) (PreH4 : (gx_pre <= 10000)) (PreH5 : ((-10000) <= gy_pre)) (PreH6 : (gy_pre <= 10000)) (PreH7 : ((-10000) <= a_x_pre)) (PreH8 : (a_x_pre <= 10000)) (PreH9 : ((-10000) <= a_y_pre)) (PreH10 : (a_y_pre <= 10000)) (PreH11 : ((-10000) <= b_x_pre)) (PreH12 : (b_x_pre <= 10000)) (PreH13 : ((-10000) <= b_y_pre)) (PreH14 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_29 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH2 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH3 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH5 : ((-10000) <= gx_pre)) (PreH6 : (gx_pre <= 10000)) (PreH7 : ((-10000) <= gy_pre)) (PreH8 : (gy_pre <= 10000)) (PreH9 : ((-10000) <= a_x_pre)) (PreH10 : (a_x_pre <= 10000)) (PreH11 : ((-10000) <= a_y_pre)) (PreH12 : (a_y_pre <= 10000)) (PreH13 : ((-10000) <= b_x_pre)) (PreH14 : (b_x_pre <= 10000)) (PreH15 : ((-10000) <= b_y_pre)) (PreH16 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_30 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH2 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH3 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH5 : ((-10000) <= gx_pre)) (PreH6 : (gx_pre <= 10000)) (PreH7 : ((-10000) <= gy_pre)) (PreH8 : (gy_pre <= 10000)) (PreH9 : ((-10000) <= a_x_pre)) (PreH10 : (a_x_pre <= 10000)) (PreH11 : ((-10000) <= a_y_pre)) (PreH12 : (a_y_pre <= 10000)) (PreH13 : ((-10000) <= b_x_pre)) (PreH14 : (b_x_pre <= 10000)) (PreH15 : ((-10000) <= b_y_pre)) (PreH16 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_31 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH2 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH3 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((-10000) <= gx_pre)) (PreH5 : (gx_pre <= 10000)) (PreH6 : ((-10000) <= gy_pre)) (PreH7 : (gy_pre <= 10000)) (PreH8 : ((-10000) <= a_x_pre)) (PreH9 : (a_x_pre <= 10000)) (PreH10 : ((-10000) <= a_y_pre)) (PreH11 : (a_y_pre <= 10000)) (PreH12 : ((-10000) <= b_x_pre)) (PreH13 : (b_x_pre <= 10000)) (PreH14 : ((-10000) <= b_y_pre)) (PreH15 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_32 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH2 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH3 : ((-10000) <= gx_pre)) (PreH4 : (gx_pre <= 10000)) (PreH5 : ((-10000) <= gy_pre)) (PreH6 : (gy_pre <= 10000)) (PreH7 : ((-10000) <= a_x_pre)) (PreH8 : (a_x_pre <= 10000)) (PreH9 : ((-10000) <= a_y_pre)) (PreH10 : (a_y_pre <= 10000)) (PreH11 : ((-10000) <= b_x_pre)) (PreH12 : (b_x_pre <= 10000)) (PreH13 : ((-10000) <= b_y_pre)) (PreH14 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def cmp_polar_values_safety_wit_33 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH2 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH3 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH5 : ((-10000) <= gx_pre)) (PreH6 : (gx_pre <= 10000)) (PreH7 : ((-10000) <= gy_pre)) (PreH8 : (gy_pre <= 10000)) (PreH9 : ((-10000) <= a_x_pre)) (PreH10 : (a_x_pre <= 10000)) (PreH11 : ((-10000) <= a_y_pre)) (PreH12 : (a_y_pre <= 10000)) (PreH13 : ((-10000) <= b_x_pre)) (PreH14 : (b_x_pre <= 10000)) (PreH15 : ((-10000) <= b_y_pre)) (PreH16 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def cmp_polar_values_safety_wit_34 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH2 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH3 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH5 : ((-10000) <= gx_pre)) (PreH6 : (gx_pre <= 10000)) (PreH7 : ((-10000) <= gy_pre)) (PreH8 : (gy_pre <= 10000)) (PreH9 : ((-10000) <= a_x_pre)) (PreH10 : (a_x_pre <= 10000)) (PreH11 : ((-10000) <= a_y_pre)) (PreH12 : (a_y_pre <= 10000)) (PreH13 : ((-10000) <= b_x_pre)) (PreH14 : (b_x_pre <= 10000)) (PreH15 : ((-10000) <= b_y_pre)) (PreH16 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def cmp_polar_values_safety_wit_35 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH2 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH3 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((-10000) <= gx_pre)) (PreH5 : (gx_pre <= 10000)) (PreH6 : ((-10000) <= gy_pre)) (PreH7 : (gy_pre <= 10000)) (PreH8 : ((-10000) <= a_x_pre)) (PreH9 : (a_x_pre <= 10000)) (PreH10 : ((-10000) <= a_y_pre)) (PreH11 : (a_y_pre <= 10000)) (PreH12 : ((-10000) <= b_x_pre)) (PreH13 : (b_x_pre <= 10000)) (PreH14 : ((-10000) <= b_y_pre)) (PreH15 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def cmp_polar_values_safety_wit_36 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH3 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH4 : ((-10000) <= gx_pre)) (PreH5 : (gx_pre <= 10000)) (PreH6 : ((-10000) <= gy_pre)) (PreH7 : (gy_pre <= 10000)) (PreH8 : ((-10000) <= a_x_pre)) (PreH9 : (a_x_pre <= 10000)) (PreH10 : ((-10000) <= a_y_pre)) (PreH11 : (a_y_pre <= 10000)) (PreH12 : ((-10000) <= b_x_pre)) (PreH13 : (b_x_pre <= 10000)) (PreH14 : ((-10000) <= b_y_pre)) (PreH15 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def cmp_polar_values_safety_wit_37 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH3 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH6 : ((-10000) <= gx_pre)) (PreH7 : (gx_pre <= 10000)) (PreH8 : ((-10000) <= gy_pre)) (PreH9 : (gy_pre <= 10000)) (PreH10 : ((-10000) <= a_x_pre)) (PreH11 : (a_x_pre <= 10000)) (PreH12 : ((-10000) <= a_y_pre)) (PreH13 : (a_y_pre <= 10000)) (PreH14 : ((-10000) <= b_x_pre)) (PreH15 : (b_x_pre <= 10000)) (PreH16 : ((-10000) <= b_y_pre)) (PreH17 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def cmp_polar_values_safety_wit_38 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH3 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH6 : ((-10000) <= gx_pre)) (PreH7 : (gx_pre <= 10000)) (PreH8 : ((-10000) <= gy_pre)) (PreH9 : (gy_pre <= 10000)) (PreH10 : ((-10000) <= a_x_pre)) (PreH11 : (a_x_pre <= 10000)) (PreH12 : ((-10000) <= a_y_pre)) (PreH13 : (a_y_pre <= 10000)) (PreH14 : ((-10000) <= b_x_pre)) (PreH15 : (b_x_pre <= 10000)) (PreH16 : ((-10000) <= b_y_pre)) (PreH17 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def cmp_polar_values_safety_wit_39 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH3 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH5 : ((-10000) <= gx_pre)) (PreH6 : (gx_pre <= 10000)) (PreH7 : ((-10000) <= gy_pre)) (PreH8 : (gy_pre <= 10000)) (PreH9 : ((-10000) <= a_x_pre)) (PreH10 : (a_x_pre <= 10000)) (PreH11 : ((-10000) <= a_y_pre)) (PreH12 : (a_y_pre <= 10000)) (PreH13 : ((-10000) <= b_x_pre)) (PreH14 : (b_x_pre <= 10000)) (PreH15 : ((-10000) <= b_y_pre)) (PreH16 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def cmp_polar_values_safety_wit_40 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH5 : ((-10000) <= gx_pre)) (PreH6 : (gx_pre <= 10000)) (PreH7 : ((-10000) <= gy_pre)) (PreH8 : (gy_pre <= 10000)) (PreH9 : ((-10000) <= a_x_pre)) (PreH10 : (a_x_pre <= 10000)) (PreH11 : ((-10000) <= a_y_pre)) (PreH12 : (a_y_pre <= 10000)) (PreH13 : ((-10000) <= b_x_pre)) (PreH14 : (b_x_pre <= 10000)) (PreH15 : ((-10000) <= b_y_pre)) (PreH16 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_41 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH7 : ((-10000) <= gx_pre)) (PreH8 : (gx_pre <= 10000)) (PreH9 : ((-10000) <= gy_pre)) (PreH10 : (gy_pre <= 10000)) (PreH11 : ((-10000) <= a_x_pre)) (PreH12 : (a_x_pre <= 10000)) (PreH13 : ((-10000) <= a_y_pre)) (PreH14 : (a_y_pre <= 10000)) (PreH15 : ((-10000) <= b_x_pre)) (PreH16 : (b_x_pre <= 10000)) (PreH17 : ((-10000) <= b_y_pre)) (PreH18 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_42 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH7 : ((-10000) <= gx_pre)) (PreH8 : (gx_pre <= 10000)) (PreH9 : ((-10000) <= gy_pre)) (PreH10 : (gy_pre <= 10000)) (PreH11 : ((-10000) <= a_x_pre)) (PreH12 : (a_x_pre <= 10000)) (PreH13 : ((-10000) <= a_y_pre)) (PreH14 : (a_y_pre <= 10000)) (PreH15 : ((-10000) <= b_x_pre)) (PreH16 : (b_x_pre <= 10000)) (PreH17 : ((-10000) <= b_y_pre)) (PreH18 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_43 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH6 : ((-10000) <= gx_pre)) (PreH7 : (gx_pre <= 10000)) (PreH8 : ((-10000) <= gy_pre)) (PreH9 : (gy_pre <= 10000)) (PreH10 : ((-10000) <= a_x_pre)) (PreH11 : (a_x_pre <= 10000)) (PreH12 : ((-10000) <= a_y_pre)) (PreH13 : (a_y_pre <= 10000)) (PreH14 : ((-10000) <= b_x_pre)) (PreH15 : (b_x_pre <= 10000)) (PreH16 : ((-10000) <= b_y_pre)) (PreH17 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_44 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH3 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH6 : ((-10000) <= gx_pre)) (PreH7 : (gx_pre <= 10000)) (PreH8 : ((-10000) <= gy_pre)) (PreH9 : (gy_pre <= 10000)) (PreH10 : ((-10000) <= a_x_pre)) (PreH11 : (a_x_pre <= 10000)) (PreH12 : ((-10000) <= a_y_pre)) (PreH13 : (a_y_pre <= 10000)) (PreH14 : ((-10000) <= b_x_pre)) (PreH15 : (b_x_pre <= 10000)) (PreH16 : ((-10000) <= b_y_pre)) (PreH17 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def cmp_polar_values_safety_wit_45 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH3 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH4 : ((-10000) <= gx_pre)) (PreH5 : (gx_pre <= 10000)) (PreH6 : ((-10000) <= gy_pre)) (PreH7 : (gy_pre <= 10000)) (PreH8 : ((-10000) <= a_x_pre)) (PreH9 : (a_x_pre <= 10000)) (PreH10 : ((-10000) <= a_y_pre)) (PreH11 : (a_y_pre <= 10000)) (PreH12 : ((-10000) <= b_x_pre)) (PreH13 : (b_x_pre <= 10000)) (PreH14 : ((-10000) <= b_y_pre)) (PreH15 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def cmp_polar_values_safety_wit_46 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_x_pre - gx_pre) < (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH7 : ((-10000) <= gx_pre)) (PreH8 : (gx_pre <= 10000)) (PreH9 : ((-10000) <= gy_pre)) (PreH10 : (gy_pre <= 10000)) (PreH11 : ((-10000) <= a_x_pre)) (PreH12 : (a_x_pre <= 10000)) (PreH13 : ((-10000) <= a_y_pre)) (PreH14 : (a_y_pre <= 10000)) (PreH15 : ((-10000) <= b_x_pre)) (PreH16 : (b_x_pre <= 10000)) (PreH17 : ((-10000) <= b_y_pre)) (PreH18 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def cmp_polar_values_safety_wit_47 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_x_pre - gx_pre) < (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH5 : ((-10000) <= gx_pre)) (PreH6 : (gx_pre <= 10000)) (PreH7 : ((-10000) <= gy_pre)) (PreH8 : (gy_pre <= 10000)) (PreH9 : ((-10000) <= a_x_pre)) (PreH10 : (a_x_pre <= 10000)) (PreH11 : ((-10000) <= a_y_pre)) (PreH12 : (a_y_pre <= 10000)) (PreH13 : ((-10000) <= b_x_pre)) (PreH14 : (b_x_pre <= 10000)) (PreH15 : ((-10000) <= b_y_pre)) (PreH16 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def cmp_polar_values_safety_wit_48 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_x_pre - gx_pre) < (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH5 : ((-10000) <= gx_pre)) (PreH6 : (gx_pre <= 10000)) (PreH7 : ((-10000) <= gy_pre)) (PreH8 : (gy_pre <= 10000)) (PreH9 : ((-10000) <= a_x_pre)) (PreH10 : (a_x_pre <= 10000)) (PreH11 : ((-10000) <= a_y_pre)) (PreH12 : (a_y_pre <= 10000)) (PreH13 : ((-10000) <= b_x_pre)) (PreH14 : (b_x_pre <= 10000)) (PreH15 : ((-10000) <= b_y_pre)) (PreH16 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_49 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_x_pre - gx_pre) < (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH7 : ((-10000) <= gx_pre)) (PreH8 : (gx_pre <= 10000)) (PreH9 : ((-10000) <= gy_pre)) (PreH10 : (gy_pre <= 10000)) (PreH11 : ((-10000) <= a_x_pre)) (PreH12 : (a_x_pre <= 10000)) (PreH13 : ((-10000) <= a_y_pre)) (PreH14 : (a_y_pre <= 10000)) (PreH15 : ((-10000) <= b_x_pre)) (PreH16 : (b_x_pre <= 10000)) (PreH17 : ((-10000) <= b_y_pre)) (PreH18 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_50 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH3 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH4 : ((-10000) <= gx_pre)) (PreH5 : (gx_pre <= 10000)) (PreH6 : ((-10000) <= gy_pre)) (PreH7 : (gy_pre <= 10000)) (PreH8 : ((-10000) <= a_x_pre)) (PreH9 : (a_x_pre <= 10000)) (PreH10 : ((-10000) <= a_y_pre)) (PreH11 : (a_y_pre <= 10000)) (PreH12 : ((-10000) <= b_x_pre)) (PreH13 : (b_x_pre <= 10000)) (PreH14 : ((-10000) <= b_y_pre)) (PreH15 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_51 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH3 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH6 : ((-10000) <= gx_pre)) (PreH7 : (gx_pre <= 10000)) (PreH8 : ((-10000) <= gy_pre)) (PreH9 : (gy_pre <= 10000)) (PreH10 : ((-10000) <= a_x_pre)) (PreH11 : (a_x_pre <= 10000)) (PreH12 : ((-10000) <= a_y_pre)) (PreH13 : (a_y_pre <= 10000)) (PreH14 : ((-10000) <= b_x_pre)) (PreH15 : (b_x_pre <= 10000)) (PreH16 : ((-10000) <= b_y_pre)) (PreH17 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_52 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH2 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH3 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH5 : ((-10000) <= gx_pre)) (PreH6 : (gx_pre <= 10000)) (PreH7 : ((-10000) <= gy_pre)) (PreH8 : (gy_pre <= 10000)) (PreH9 : ((-10000) <= a_x_pre)) (PreH10 : (a_x_pre <= 10000)) (PreH11 : ((-10000) <= a_y_pre)) (PreH12 : (a_y_pre <= 10000)) (PreH13 : ((-10000) <= b_x_pre)) (PreH14 : (b_x_pre <= 10000)) (PreH15 : ((-10000) <= b_y_pre)) (PreH16 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_53 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH2 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH3 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((-10000) <= gx_pre)) (PreH5 : (gx_pre <= 10000)) (PreH6 : ((-10000) <= gy_pre)) (PreH7 : (gy_pre <= 10000)) (PreH8 : ((-10000) <= a_x_pre)) (PreH9 : (a_x_pre <= 10000)) (PreH10 : ((-10000) <= a_y_pre)) (PreH11 : (a_y_pre <= 10000)) (PreH12 : ((-10000) <= b_x_pre)) (PreH13 : (b_x_pre <= 10000)) (PreH14 : ((-10000) <= b_y_pre)) (PreH15 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_54 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH7 : ((-10000) <= gx_pre)) (PreH8 : (gx_pre <= 10000)) (PreH9 : ((-10000) <= gy_pre)) (PreH10 : (gy_pre <= 10000)) (PreH11 : ((-10000) <= a_x_pre)) (PreH12 : (a_x_pre <= 10000)) (PreH13 : ((-10000) <= a_y_pre)) (PreH14 : (a_y_pre <= 10000)) (PreH15 : ((-10000) <= b_x_pre)) (PreH16 : (b_x_pre <= 10000)) (PreH17 : ((-10000) <= b_y_pre)) (PreH18 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_55 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH6 : ((-10000) <= gx_pre)) (PreH7 : (gx_pre <= 10000)) (PreH8 : ((-10000) <= gy_pre)) (PreH9 : (gy_pre <= 10000)) (PreH10 : ((-10000) <= a_x_pre)) (PreH11 : (a_x_pre <= 10000)) (PreH12 : ((-10000) <= a_y_pre)) (PreH13 : (a_y_pre <= 10000)) (PreH14 : ((-10000) <= b_x_pre)) (PreH15 : (b_x_pre <= 10000)) (PreH16 : ((-10000) <= b_y_pre)) (PreH17 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_56 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH2 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH3 : ((-10000) <= gx_pre)) (PreH4 : (gx_pre <= 10000)) (PreH5 : ((-10000) <= gy_pre)) (PreH6 : (gy_pre <= 10000)) (PreH7 : ((-10000) <= a_x_pre)) (PreH8 : (a_x_pre <= 10000)) (PreH9 : ((-10000) <= a_y_pre)) (PreH10 : (a_y_pre <= 10000)) (PreH11 : ((-10000) <= b_x_pre)) (PreH12 : (b_x_pre <= 10000)) (PreH13 : ((-10000) <= b_y_pre)) (PreH14 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def cmp_polar_values_safety_wit_57 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH2 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH3 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH5 : ((-10000) <= gx_pre)) (PreH6 : (gx_pre <= 10000)) (PreH7 : ((-10000) <= gy_pre)) (PreH8 : (gy_pre <= 10000)) (PreH9 : ((-10000) <= a_x_pre)) (PreH10 : (a_x_pre <= 10000)) (PreH11 : ((-10000) <= a_y_pre)) (PreH12 : (a_y_pre <= 10000)) (PreH13 : ((-10000) <= b_x_pre)) (PreH14 : (b_x_pre <= 10000)) (PreH15 : ((-10000) <= b_y_pre)) (PreH16 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def cmp_polar_values_safety_wit_58 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH5 : ((-10000) <= gx_pre)) (PreH6 : (gx_pre <= 10000)) (PreH7 : ((-10000) <= gy_pre)) (PreH8 : (gy_pre <= 10000)) (PreH9 : ((-10000) <= a_x_pre)) (PreH10 : (a_x_pre <= 10000)) (PreH11 : ((-10000) <= a_y_pre)) (PreH12 : (a_y_pre <= 10000)) (PreH13 : ((-10000) <= b_x_pre)) (PreH14 : (b_x_pre <= 10000)) (PreH15 : ((-10000) <= b_y_pre)) (PreH16 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def cmp_polar_values_safety_wit_59 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH7 : ((-10000) <= gx_pre)) (PreH8 : (gx_pre <= 10000)) (PreH9 : ((-10000) <= gy_pre)) (PreH10 : (gy_pre <= 10000)) (PreH11 : ((-10000) <= a_x_pre)) (PreH12 : (a_x_pre <= 10000)) (PreH13 : ((-10000) <= a_y_pre)) (PreH14 : (a_y_pre <= 10000)) (PreH15 : ((-10000) <= b_x_pre)) (PreH16 : (b_x_pre <= 10000)) (PreH17 : ((-10000) <= b_y_pre)) (PreH18 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def cmp_polar_values_safety_wit_60 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_x_pre - gx_pre) < (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH7 : ((-10000) <= gx_pre)) (PreH8 : (gx_pre <= 10000)) (PreH9 : ((-10000) <= gy_pre)) (PreH10 : (gy_pre <= 10000)) (PreH11 : ((-10000) <= a_x_pre)) (PreH12 : (a_x_pre <= 10000)) (PreH13 : ((-10000) <= a_y_pre)) (PreH14 : (a_y_pre <= 10000)) (PreH15 : ((-10000) <= b_x_pre)) (PreH16 : (b_x_pre <= 10000)) (PreH17 : ((-10000) <= b_y_pre)) (PreH18 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def cmp_polar_values_safety_wit_61 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_x_pre - gx_pre) < (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH6 : ((-10000) <= gx_pre)) (PreH7 : (gx_pre <= 10000)) (PreH8 : ((-10000) <= gy_pre)) (PreH9 : (gy_pre <= 10000)) (PreH10 : ((-10000) <= a_x_pre)) (PreH11 : (a_x_pre <= 10000)) (PreH12 : ((-10000) <= a_y_pre)) (PreH13 : (a_y_pre <= 10000)) (PreH14 : ((-10000) <= b_x_pre)) (PreH15 : (b_x_pre <= 10000)) (PreH16 : ((-10000) <= b_y_pre)) (PreH17 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def cmp_polar_values_safety_wit_62 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH3 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH6 : ((-10000) <= gx_pre)) (PreH7 : (gx_pre <= 10000)) (PreH8 : ((-10000) <= gy_pre)) (PreH9 : (gy_pre <= 10000)) (PreH10 : ((-10000) <= a_x_pre)) (PreH11 : (a_x_pre <= 10000)) (PreH12 : ((-10000) <= a_y_pre)) (PreH13 : (a_y_pre <= 10000)) (PreH14 : ((-10000) <= b_x_pre)) (PreH15 : (b_x_pre <= 10000)) (PreH16 : ((-10000) <= b_y_pre)) (PreH17 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def cmp_polar_values_safety_wit_63 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH3 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH5 : ((-10000) <= gx_pre)) (PreH6 : (gx_pre <= 10000)) (PreH7 : ((-10000) <= gy_pre)) (PreH8 : (gy_pre <= 10000)) (PreH9 : ((-10000) <= a_x_pre)) (PreH10 : (a_x_pre <= 10000)) (PreH11 : ((-10000) <= a_y_pre)) (PreH12 : (a_y_pre <= 10000)) (PreH13 : ((-10000) <= b_x_pre)) (PreH14 : (b_x_pre <= 10000)) (PreH15 : ((-10000) <= b_y_pre)) (PreH16 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def cmp_polar_values_safety_wit_64 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) > (0 : Int))) (PreH2 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH4 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH6 : ((-10000) <= gx_pre)) (PreH7 : (gx_pre <= 10000)) (PreH8 : ((-10000) <= gy_pre)) (PreH9 : (gy_pre <= 10000)) (PreH10 : ((-10000) <= a_x_pre)) (PreH11 : (a_x_pre <= 10000)) (PreH12 : ((-10000) <= a_y_pre)) (PreH13 : (a_y_pre <= 10000)) (PreH14 : ((-10000) <= b_x_pre)) (PreH15 : (b_x_pre <= 10000)) (PreH16 : ((-10000) <= b_y_pre)) (PreH17 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ False ”

noncomputable def cmp_polar_values_safety_wit_65 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) > (0 : Int))) (PreH2 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH4 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH5 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH7 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH8 : ((-10000) <= gx_pre)) (PreH9 : (gx_pre <= 10000)) (PreH10 : ((-10000) <= gy_pre)) (PreH11 : (gy_pre <= 10000)) (PreH12 : ((-10000) <= a_x_pre)) (PreH13 : (a_x_pre <= 10000)) (PreH14 : ((-10000) <= a_y_pre)) (PreH15 : (a_y_pre <= 10000)) (PreH16 : ((-10000) <= b_x_pre)) (PreH17 : (b_x_pre <= 10000)) (PreH18 : ((-10000) <= b_y_pre)) (PreH19 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ False ”

noncomputable def cmp_polar_values_safety_wit_66 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) > (0 : Int))) (PreH2 : ((b_x_pre - gx_pre) < (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH4 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH5 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH7 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH8 : ((-10000) <= gx_pre)) (PreH9 : (gx_pre <= 10000)) (PreH10 : ((-10000) <= gy_pre)) (PreH11 : (gy_pre <= 10000)) (PreH12 : ((-10000) <= a_x_pre)) (PreH13 : (a_x_pre <= 10000)) (PreH14 : ((-10000) <= a_y_pre)) (PreH15 : (a_y_pre <= 10000)) (PreH16 : ((-10000) <= b_x_pre)) (PreH17 : (b_x_pre <= 10000)) (PreH18 : ((-10000) <= b_y_pre)) (PreH19 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ False ”

noncomputable def cmp_polar_values_safety_wit_67 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) > (0 : Int))) (PreH2 : ((b_x_pre - gx_pre) < (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH4 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH7 : ((-10000) <= gx_pre)) (PreH8 : (gx_pre <= 10000)) (PreH9 : ((-10000) <= gy_pre)) (PreH10 : (gy_pre <= 10000)) (PreH11 : ((-10000) <= a_x_pre)) (PreH12 : (a_x_pre <= 10000)) (PreH13 : ((-10000) <= a_y_pre)) (PreH14 : (a_y_pre <= 10000)) (PreH15 : ((-10000) <= b_x_pre)) (PreH16 : (b_x_pre <= 10000)) (PreH17 : ((-10000) <= b_y_pre)) (PreH18 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ False ”

noncomputable def cmp_polar_values_safety_wit_68 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH7 : ((-10000) <= gx_pre)) (PreH8 : (gx_pre <= 10000)) (PreH9 : ((-10000) <= gy_pre)) (PreH10 : (gy_pre <= 10000)) (PreH11 : ((-10000) <= a_x_pre)) (PreH12 : (a_x_pre <= 10000)) (PreH13 : ((-10000) <= a_y_pre)) (PreH14 : (a_y_pre <= 10000)) (PreH15 : ((-10000) <= b_x_pre)) (PreH16 : (b_x_pre <= 10000)) (PreH17 : ((-10000) <= b_y_pre)) (PreH18 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ False ”

noncomputable def cmp_polar_values_safety_wit_69 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) > (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH6 : ((-10000) <= gx_pre)) (PreH7 : (gx_pre <= 10000)) (PreH8 : ((-10000) <= gy_pre)) (PreH9 : (gy_pre <= 10000)) (PreH10 : ((-10000) <= a_x_pre)) (PreH11 : (a_x_pre <= 10000)) (PreH12 : ((-10000) <= a_y_pre)) (PreH13 : (a_y_pre <= 10000)) (PreH14 : ((-10000) <= b_x_pre)) (PreH15 : (b_x_pre <= 10000)) (PreH16 : ((-10000) <= b_y_pre)) (PreH17 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def cmp_polar_values_safety_wit_70 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) > (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH7 : ((-10000) <= gx_pre)) (PreH8 : (gx_pre <= 10000)) (PreH9 : ((-10000) <= gy_pre)) (PreH10 : (gy_pre <= 10000)) (PreH11 : ((-10000) <= a_x_pre)) (PreH12 : (a_x_pre <= 10000)) (PreH13 : ((-10000) <= a_y_pre)) (PreH14 : (a_y_pre <= 10000)) (PreH15 : ((-10000) <= b_x_pre)) (PreH16 : (b_x_pre <= 10000)) (PreH17 : ((-10000) <= b_y_pre)) (PreH18 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def cmp_polar_values_safety_wit_71 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) > (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH3 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH6 : ((-10000) <= gx_pre)) (PreH7 : (gx_pre <= 10000)) (PreH8 : ((-10000) <= gy_pre)) (PreH9 : (gy_pre <= 10000)) (PreH10 : ((-10000) <= a_x_pre)) (PreH11 : (a_x_pre <= 10000)) (PreH12 : ((-10000) <= a_y_pre)) (PreH13 : (a_y_pre <= 10000)) (PreH14 : ((-10000) <= b_x_pre)) (PreH15 : (b_x_pre <= 10000)) (PreH16 : ((-10000) <= b_y_pre)) (PreH17 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def cmp_polar_values_safety_wit_72 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) > (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH3 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH4 : ((-10000) <= gx_pre)) (PreH5 : (gx_pre <= 10000)) (PreH6 : ((-10000) <= gy_pre)) (PreH7 : (gy_pre <= 10000)) (PreH8 : ((-10000) <= a_x_pre)) (PreH9 : (a_x_pre <= 10000)) (PreH10 : ((-10000) <= a_y_pre)) (PreH11 : (a_y_pre <= 10000)) (PreH12 : ((-10000) <= b_x_pre)) (PreH13 : (b_x_pre <= 10000)) (PreH14 : ((-10000) <= b_y_pre)) (PreH15 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def cmp_polar_values_safety_wit_73 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) > (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH3 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH4 : ((-10000) <= gx_pre)) (PreH5 : (gx_pre <= 10000)) (PreH6 : ((-10000) <= gy_pre)) (PreH7 : (gy_pre <= 10000)) (PreH8 : ((-10000) <= a_x_pre)) (PreH9 : (a_x_pre <= 10000)) (PreH10 : ((-10000) <= a_y_pre)) (PreH11 : (a_y_pre <= 10000)) (PreH12 : ((-10000) <= b_x_pre)) (PreH13 : (b_x_pre <= 10000)) (PreH14 : ((-10000) <= b_y_pre)) (PreH15 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_74 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) > (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH3 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH6 : ((-10000) <= gx_pre)) (PreH7 : (gx_pre <= 10000)) (PreH8 : ((-10000) <= gy_pre)) (PreH9 : (gy_pre <= 10000)) (PreH10 : ((-10000) <= a_x_pre)) (PreH11 : (a_x_pre <= 10000)) (PreH12 : ((-10000) <= a_y_pre)) (PreH13 : (a_y_pre <= 10000)) (PreH14 : ((-10000) <= b_x_pre)) (PreH15 : (b_x_pre <= 10000)) (PreH16 : ((-10000) <= b_y_pre)) (PreH17 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_75 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) > (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH7 : ((-10000) <= gx_pre)) (PreH8 : (gx_pre <= 10000)) (PreH9 : ((-10000) <= gy_pre)) (PreH10 : (gy_pre <= 10000)) (PreH11 : ((-10000) <= a_x_pre)) (PreH12 : (a_x_pre <= 10000)) (PreH13 : ((-10000) <= a_y_pre)) (PreH14 : (a_y_pre <= 10000)) (PreH15 : ((-10000) <= b_x_pre)) (PreH16 : (b_x_pre <= 10000)) (PreH17 : ((-10000) <= b_y_pre)) (PreH18 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_76 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) > (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH6 : ((-10000) <= gx_pre)) (PreH7 : (gx_pre <= 10000)) (PreH8 : ((-10000) <= gy_pre)) (PreH9 : (gy_pre <= 10000)) (PreH10 : ((-10000) <= a_x_pre)) (PreH11 : (a_x_pre <= 10000)) (PreH12 : ((-10000) <= a_y_pre)) (PreH13 : (a_y_pre <= 10000)) (PreH14 : ((-10000) <= b_x_pre)) (PreH15 : (b_x_pre <= 10000)) (PreH16 : ((-10000) <= b_y_pre)) (PreH17 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_77 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH3 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH4 : ((-10000) <= gx_pre)) (PreH5 : (gx_pre <= 10000)) (PreH6 : ((-10000) <= gy_pre)) (PreH7 : (gy_pre <= 10000)) (PreH8 : ((-10000) <= a_x_pre)) (PreH9 : (a_x_pre <= 10000)) (PreH10 : ((-10000) <= a_y_pre)) (PreH11 : (a_y_pre <= 10000)) (PreH12 : ((-10000) <= b_x_pre)) (PreH13 : (b_x_pre <= 10000)) (PreH14 : ((-10000) <= b_y_pre)) (PreH15 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def cmp_polar_values_safety_wit_78 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH3 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH6 : ((-10000) <= gx_pre)) (PreH7 : (gx_pre <= 10000)) (PreH8 : ((-10000) <= gy_pre)) (PreH9 : (gy_pre <= 10000)) (PreH10 : ((-10000) <= a_x_pre)) (PreH11 : (a_x_pre <= 10000)) (PreH12 : ((-10000) <= a_y_pre)) (PreH13 : (a_y_pre <= 10000)) (PreH14 : ((-10000) <= b_x_pre)) (PreH15 : (b_x_pre <= 10000)) (PreH16 : ((-10000) <= b_y_pre)) (PreH17 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def cmp_polar_values_safety_wit_79 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH2 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH4 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH6 : ((-10000) <= gx_pre)) (PreH7 : (gx_pre <= 10000)) (PreH8 : ((-10000) <= gy_pre)) (PreH9 : (gy_pre <= 10000)) (PreH10 : ((-10000) <= a_x_pre)) (PreH11 : (a_x_pre <= 10000)) (PreH12 : ((-10000) <= a_y_pre)) (PreH13 : (a_y_pre <= 10000)) (PreH14 : ((-10000) <= b_x_pre)) (PreH15 : (b_x_pre <= 10000)) (PreH16 : ((-10000) <= b_y_pre)) (PreH17 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def cmp_polar_values_safety_wit_80 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH2 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH4 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH5 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH7 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH8 : ((-10000) <= gx_pre)) (PreH9 : (gx_pre <= 10000)) (PreH10 : ((-10000) <= gy_pre)) (PreH11 : (gy_pre <= 10000)) (PreH12 : ((-10000) <= a_x_pre)) (PreH13 : (a_x_pre <= 10000)) (PreH14 : ((-10000) <= a_y_pre)) (PreH15 : (a_y_pre <= 10000)) (PreH16 : ((-10000) <= b_x_pre)) (PreH17 : (b_x_pre <= 10000)) (PreH18 : ((-10000) <= b_y_pre)) (PreH19 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def cmp_polar_values_safety_wit_81 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH2 : ((b_x_pre - gx_pre) < (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH4 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH5 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH7 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH8 : ((-10000) <= gx_pre)) (PreH9 : (gx_pre <= 10000)) (PreH10 : ((-10000) <= gy_pre)) (PreH11 : (gy_pre <= 10000)) (PreH12 : ((-10000) <= a_x_pre)) (PreH13 : (a_x_pre <= 10000)) (PreH14 : ((-10000) <= a_y_pre)) (PreH15 : (a_y_pre <= 10000)) (PreH16 : ((-10000) <= b_x_pre)) (PreH17 : (b_x_pre <= 10000)) (PreH18 : ((-10000) <= b_y_pre)) (PreH19 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def cmp_polar_values_safety_wit_82 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH2 : ((b_x_pre - gx_pre) < (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH4 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH7 : ((-10000) <= gx_pre)) (PreH8 : (gx_pre <= 10000)) (PreH9 : ((-10000) <= gy_pre)) (PreH10 : (gy_pre <= 10000)) (PreH11 : ((-10000) <= a_x_pre)) (PreH12 : (a_x_pre <= 10000)) (PreH13 : ((-10000) <= a_y_pre)) (PreH14 : (a_y_pre <= 10000)) (PreH15 : ((-10000) <= b_x_pre)) (PreH16 : (b_x_pre <= 10000)) (PreH17 : ((-10000) <= b_y_pre)) (PreH18 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def cmp_polar_values_safety_wit_83 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH6 : ((-10000) <= gx_pre)) (PreH7 : (gx_pre <= 10000)) (PreH8 : ((-10000) <= gy_pre)) (PreH9 : (gy_pre <= 10000)) (PreH10 : ((-10000) <= a_x_pre)) (PreH11 : (a_x_pre <= 10000)) (PreH12 : ((-10000) <= a_y_pre)) (PreH13 : (a_y_pre <= 10000)) (PreH14 : ((-10000) <= b_x_pre)) (PreH15 : (b_x_pre <= 10000)) (PreH16 : ((-10000) <= b_y_pre)) (PreH17 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def cmp_polar_values_safety_wit_84 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) < (0 : Int))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH4 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH7 : ((-10000) <= gx_pre)) (PreH8 : (gx_pre <= 10000)) (PreH9 : ((-10000) <= gy_pre)) (PreH10 : (gy_pre <= 10000)) (PreH11 : ((-10000) <= a_x_pre)) (PreH12 : (a_x_pre <= 10000)) (PreH13 : ((-10000) <= a_y_pre)) (PreH14 : (a_y_pre <= 10000)) (PreH15 : ((-10000) <= b_x_pre)) (PreH16 : (b_x_pre <= 10000)) (PreH17 : ((-10000) <= b_y_pre)) (PreH18 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ False ”

noncomputable def cmp_polar_values_safety_wit_85 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) < (0 : Int))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH3 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH4 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH5 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH6 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH7 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH8 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH9 : ((-10000) <= gx_pre)) (PreH10 : (gx_pre <= 10000)) (PreH11 : ((-10000) <= gy_pre)) (PreH12 : (gy_pre <= 10000)) (PreH13 : ((-10000) <= a_x_pre)) (PreH14 : (a_x_pre <= 10000)) (PreH15 : ((-10000) <= a_y_pre)) (PreH16 : (a_y_pre <= 10000)) (PreH17 : ((-10000) <= b_x_pre)) (PreH18 : (b_x_pre <= 10000)) (PreH19 : ((-10000) <= b_y_pre)) (PreH20 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ False ”

noncomputable def cmp_polar_values_safety_wit_86 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) < (0 : Int))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH3 : ((b_x_pre - gx_pre) < (0 : Int))) (PreH4 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH5 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH6 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH7 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH8 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH9 : ((-10000) <= gx_pre)) (PreH10 : (gx_pre <= 10000)) (PreH11 : ((-10000) <= gy_pre)) (PreH12 : (gy_pre <= 10000)) (PreH13 : ((-10000) <= a_x_pre)) (PreH14 : (a_x_pre <= 10000)) (PreH15 : ((-10000) <= a_y_pre)) (PreH16 : (a_y_pre <= 10000)) (PreH17 : ((-10000) <= b_x_pre)) (PreH18 : (b_x_pre <= 10000)) (PreH19 : ((-10000) <= b_y_pre)) (PreH20 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ False ”

noncomputable def cmp_polar_values_safety_wit_87 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH3 : ((b_x_pre - gx_pre) < (0 : Int))) (PreH4 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH5 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH7 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH8 : ((-10000) <= gx_pre)) (PreH9 : (gx_pre <= 10000)) (PreH10 : ((-10000) <= gy_pre)) (PreH11 : (gy_pre <= 10000)) (PreH12 : ((-10000) <= a_x_pre)) (PreH13 : (a_x_pre <= 10000)) (PreH14 : ((-10000) <= a_y_pre)) (PreH15 : (a_y_pre <= 10000)) (PreH16 : ((-10000) <= b_x_pre)) (PreH17 : (b_x_pre <= 10000)) (PreH18 : ((-10000) <= b_y_pre)) (PreH19 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ False ”

noncomputable def cmp_polar_values_safety_wit_88 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) < (0 : Int))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH5 : ((-10000) <= gx_pre)) (PreH6 : (gx_pre <= 10000)) (PreH7 : ((-10000) <= gy_pre)) (PreH8 : (gy_pre <= 10000)) (PreH9 : ((-10000) <= a_x_pre)) (PreH10 : (a_x_pre <= 10000)) (PreH11 : ((-10000) <= a_y_pre)) (PreH12 : (a_y_pre <= 10000)) (PreH13 : ((-10000) <= b_x_pre)) (PreH14 : (b_x_pre <= 10000)) (PreH15 : ((-10000) <= b_y_pre)) (PreH16 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_89 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) < (0 : Int))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH3 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH4 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH5 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH7 : ((-10000) <= gx_pre)) (PreH8 : (gx_pre <= 10000)) (PreH9 : ((-10000) <= gy_pre)) (PreH10 : (gy_pre <= 10000)) (PreH11 : ((-10000) <= a_x_pre)) (PreH12 : (a_x_pre <= 10000)) (PreH13 : ((-10000) <= a_y_pre)) (PreH14 : (a_y_pre <= 10000)) (PreH15 : ((-10000) <= b_x_pre)) (PreH16 : (b_x_pre <= 10000)) (PreH17 : ((-10000) <= b_y_pre)) (PreH18 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_90 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) < (0 : Int))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH3 : ((b_x_pre - gx_pre) < (0 : Int))) (PreH4 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH5 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH7 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH8 : ((-10000) <= gx_pre)) (PreH9 : (gx_pre <= 10000)) (PreH10 : ((-10000) <= gy_pre)) (PreH11 : (gy_pre <= 10000)) (PreH12 : ((-10000) <= a_x_pre)) (PreH13 : (a_x_pre <= 10000)) (PreH14 : ((-10000) <= a_y_pre)) (PreH15 : (a_y_pre <= 10000)) (PreH16 : ((-10000) <= b_x_pre)) (PreH17 : (b_x_pre <= 10000)) (PreH18 : ((-10000) <= b_y_pre)) (PreH19 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_91 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) < (0 : Int))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH4 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH7 : ((-10000) <= gx_pre)) (PreH8 : (gx_pre <= 10000)) (PreH9 : ((-10000) <= gy_pre)) (PreH10 : (gy_pre <= 10000)) (PreH11 : ((-10000) <= a_x_pre)) (PreH12 : (a_x_pre <= 10000)) (PreH13 : ((-10000) <= a_y_pre)) (PreH14 : (a_y_pre <= 10000)) (PreH15 : ((-10000) <= b_x_pre)) (PreH16 : (b_x_pre <= 10000)) (PreH17 : ((-10000) <= b_y_pre)) (PreH18 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_92 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) < (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH4 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH5 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH7 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH8 : ((-10000) <= gx_pre)) (PreH9 : (gx_pre <= 10000)) (PreH10 : ((-10000) <= gy_pre)) (PreH11 : (gy_pre <= 10000)) (PreH12 : ((-10000) <= a_x_pre)) (PreH13 : (a_x_pre <= 10000)) (PreH14 : ((-10000) <= a_y_pre)) (PreH15 : (a_y_pre <= 10000)) (PreH16 : ((-10000) <= b_x_pre)) (PreH17 : (b_x_pre <= 10000)) (PreH18 : ((-10000) <= b_y_pre)) (PreH19 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def cmp_polar_values_safety_wit_93 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) < (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH4 : ((b_x_pre - gx_pre) < (0 : Int))) (PreH5 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH6 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH7 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH8 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH9 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH10 : ((-10000) <= gx_pre)) (PreH11 : (gx_pre <= 10000)) (PreH12 : ((-10000) <= gy_pre)) (PreH13 : (gy_pre <= 10000)) (PreH14 : ((-10000) <= a_x_pre)) (PreH15 : (a_x_pre <= 10000)) (PreH16 : ((-10000) <= a_y_pre)) (PreH17 : (a_y_pre <= 10000)) (PreH18 : ((-10000) <= b_x_pre)) (PreH19 : (b_x_pre <= 10000)) (PreH20 : ((-10000) <= b_y_pre)) (PreH21 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def cmp_polar_values_safety_wit_94 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) < (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH4 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH5 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH6 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH7 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH8 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH9 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH10 : ((-10000) <= gx_pre)) (PreH11 : (gx_pre <= 10000)) (PreH12 : ((-10000) <= gy_pre)) (PreH13 : (gy_pre <= 10000)) (PreH14 : ((-10000) <= a_x_pre)) (PreH15 : (a_x_pre <= 10000)) (PreH16 : ((-10000) <= a_y_pre)) (PreH17 : (a_y_pre <= 10000)) (PreH18 : ((-10000) <= b_x_pre)) (PreH19 : (b_x_pre <= 10000)) (PreH20 : ((-10000) <= b_y_pre)) (PreH21 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def cmp_polar_values_safety_wit_95 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) < (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH4 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH5 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH6 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH7 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH8 : ((-10000) <= gx_pre)) (PreH9 : (gx_pre <= 10000)) (PreH10 : ((-10000) <= gy_pre)) (PreH11 : (gy_pre <= 10000)) (PreH12 : ((-10000) <= a_x_pre)) (PreH13 : (a_x_pre <= 10000)) (PreH14 : ((-10000) <= a_y_pre)) (PreH15 : (a_y_pre <= 10000)) (PreH16 : ((-10000) <= b_x_pre)) (PreH17 : (b_x_pre <= 10000)) (PreH18 : ((-10000) <= b_y_pre)) (PreH19 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def cmp_polar_values_safety_wit_96 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) < (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH4 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH5 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH7 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH8 : ((-10000) <= gx_pre)) (PreH9 : (gx_pre <= 10000)) (PreH10 : ((-10000) <= gy_pre)) (PreH11 : (gy_pre <= 10000)) (PreH12 : ((-10000) <= a_x_pre)) (PreH13 : (a_x_pre <= 10000)) (PreH14 : ((-10000) <= a_y_pre)) (PreH15 : (a_y_pre <= 10000)) (PreH16 : ((-10000) <= b_x_pre)) (PreH17 : (b_x_pre <= 10000)) (PreH18 : ((-10000) <= b_y_pre)) (PreH19 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def cmp_polar_values_safety_wit_97 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) < (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH4 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH6 : ((-10000) <= gx_pre)) (PreH7 : (gx_pre <= 10000)) (PreH8 : ((-10000) <= gy_pre)) (PreH9 : (gy_pre <= 10000)) (PreH10 : ((-10000) <= a_x_pre)) (PreH11 : (a_x_pre <= 10000)) (PreH12 : ((-10000) <= a_y_pre)) (PreH13 : (a_y_pre <= 10000)) (PreH14 : ((-10000) <= b_x_pre)) (PreH15 : (b_x_pre <= 10000)) (PreH16 : ((-10000) <= b_y_pre)) (PreH17 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def cmp_polar_values_safety_wit_98 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) < (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH4 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH6 : ((-10000) <= gx_pre)) (PreH7 : (gx_pre <= 10000)) (PreH8 : ((-10000) <= gy_pre)) (PreH9 : (gy_pre <= 10000)) (PreH10 : ((-10000) <= a_x_pre)) (PreH11 : (a_x_pre <= 10000)) (PreH12 : ((-10000) <= a_y_pre)) (PreH13 : (a_y_pre <= 10000)) (PreH14 : ((-10000) <= b_x_pre)) (PreH15 : (b_x_pre <= 10000)) (PreH16 : ((-10000) <= b_y_pre)) (PreH17 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_99 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) < (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH4 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH5 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH7 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH8 : ((-10000) <= gx_pre)) (PreH9 : (gx_pre <= 10000)) (PreH10 : ((-10000) <= gy_pre)) (PreH11 : (gy_pre <= 10000)) (PreH12 : ((-10000) <= a_x_pre)) (PreH13 : (a_x_pre <= 10000)) (PreH14 : ((-10000) <= a_y_pre)) (PreH15 : (a_y_pre <= 10000)) (PreH16 : ((-10000) <= b_x_pre)) (PreH17 : (b_x_pre <= 10000)) (PreH18 : ((-10000) <= b_y_pre)) (PreH19 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_100 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) < (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH4 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH5 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH6 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH7 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH8 : ((-10000) <= gx_pre)) (PreH9 : (gx_pre <= 10000)) (PreH10 : ((-10000) <= gy_pre)) (PreH11 : (gy_pre <= 10000)) (PreH12 : ((-10000) <= a_x_pre)) (PreH13 : (a_x_pre <= 10000)) (PreH14 : ((-10000) <= a_y_pre)) (PreH15 : (a_y_pre <= 10000)) (PreH16 : ((-10000) <= b_x_pre)) (PreH17 : (b_x_pre <= 10000)) (PreH18 : ((-10000) <= b_y_pre)) (PreH19 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_101 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) < (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH4 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH5 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH6 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH7 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH8 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH9 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH10 : ((-10000) <= gx_pre)) (PreH11 : (gx_pre <= 10000)) (PreH12 : ((-10000) <= gy_pre)) (PreH13 : (gy_pre <= 10000)) (PreH14 : ((-10000) <= a_x_pre)) (PreH15 : (a_x_pre <= 10000)) (PreH16 : ((-10000) <= a_y_pre)) (PreH17 : (a_y_pre <= 10000)) (PreH18 : ((-10000) <= b_x_pre)) (PreH19 : (b_x_pre <= 10000)) (PreH20 : ((-10000) <= b_y_pre)) (PreH21 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_102 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) < (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH4 : ((b_x_pre - gx_pre) < (0 : Int))) (PreH5 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH6 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH7 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH8 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH9 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH10 : ((-10000) <= gx_pre)) (PreH11 : (gx_pre <= 10000)) (PreH12 : ((-10000) <= gy_pre)) (PreH13 : (gy_pre <= 10000)) (PreH14 : ((-10000) <= a_x_pre)) (PreH15 : (a_x_pre <= 10000)) (PreH16 : ((-10000) <= a_y_pre)) (PreH17 : (a_y_pre <= 10000)) (PreH18 : ((-10000) <= b_x_pre)) (PreH19 : (b_x_pre <= 10000)) (PreH20 : ((-10000) <= b_y_pre)) (PreH21 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_103 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) < (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH4 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH5 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH7 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH8 : ((-10000) <= gx_pre)) (PreH9 : (gx_pre <= 10000)) (PreH10 : ((-10000) <= gy_pre)) (PreH11 : (gy_pre <= 10000)) (PreH12 : ((-10000) <= a_x_pre)) (PreH13 : (a_x_pre <= 10000)) (PreH14 : ((-10000) <= a_y_pre)) (PreH15 : (a_y_pre <= 10000)) (PreH16 : ((-10000) <= b_x_pre)) (PreH17 : (b_x_pre <= 10000)) (PreH18 : ((-10000) <= b_y_pre)) (PreH19 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_104 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) > (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH5 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH7 : ((-10000) <= gx_pre)) (PreH8 : (gx_pre <= 10000)) (PreH9 : ((-10000) <= gy_pre)) (PreH10 : (gy_pre <= 10000)) (PreH11 : ((-10000) <= a_x_pre)) (PreH12 : (a_x_pre <= 10000)) (PreH13 : ((-10000) <= a_y_pre)) (PreH14 : (a_y_pre <= 10000)) (PreH15 : ((-10000) <= b_x_pre)) (PreH16 : (b_x_pre <= 10000)) (PreH17 : ((-10000) <= b_y_pre)) (PreH18 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_105 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) > (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH5 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH6 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH7 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH8 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH9 : ((-10000) <= gx_pre)) (PreH10 : (gx_pre <= 10000)) (PreH11 : ((-10000) <= gy_pre)) (PreH12 : (gy_pre <= 10000)) (PreH13 : ((-10000) <= a_x_pre)) (PreH14 : (a_x_pre <= 10000)) (PreH15 : ((-10000) <= a_y_pre)) (PreH16 : (a_y_pre <= 10000)) (PreH17 : ((-10000) <= b_x_pre)) (PreH18 : (b_x_pre <= 10000)) (PreH19 : ((-10000) <= b_y_pre)) (PreH20 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_106 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) > (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH5 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH6 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH7 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH8 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH9 : ((-10000) <= gx_pre)) (PreH10 : (gx_pre <= 10000)) (PreH11 : ((-10000) <= gy_pre)) (PreH12 : (gy_pre <= 10000)) (PreH13 : ((-10000) <= a_x_pre)) (PreH14 : (a_x_pre <= 10000)) (PreH15 : ((-10000) <= a_y_pre)) (PreH16 : (a_y_pre <= 10000)) (PreH17 : ((-10000) <= b_x_pre)) (PreH18 : (b_x_pre <= 10000)) (PreH19 : ((-10000) <= b_y_pre)) (PreH20 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_107 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) > (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH5 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH6 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH7 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH8 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH9 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH11 : ((-10000) <= gx_pre)) (PreH12 : (gx_pre <= 10000)) (PreH13 : ((-10000) <= gy_pre)) (PreH14 : (gy_pre <= 10000)) (PreH15 : ((-10000) <= a_x_pre)) (PreH16 : (a_x_pre <= 10000)) (PreH17 : ((-10000) <= a_y_pre)) (PreH18 : (a_y_pre <= 10000)) (PreH19 : ((-10000) <= b_x_pre)) (PreH20 : (b_x_pre <= 10000)) (PreH21 : ((-10000) <= b_y_pre)) (PreH22 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_108 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) > (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH5 : ((b_x_pre - gx_pre) < (0 : Int))) (PreH6 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH7 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH8 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH9 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH11 : ((-10000) <= gx_pre)) (PreH12 : (gx_pre <= 10000)) (PreH13 : ((-10000) <= gy_pre)) (PreH14 : (gy_pre <= 10000)) (PreH15 : ((-10000) <= a_x_pre)) (PreH16 : (a_x_pre <= 10000)) (PreH17 : ((-10000) <= a_y_pre)) (PreH18 : (a_y_pre <= 10000)) (PreH19 : ((-10000) <= b_x_pre)) (PreH20 : (b_x_pre <= 10000)) (PreH21 : ((-10000) <= b_y_pre)) (PreH22 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_109 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) > (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH5 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH6 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH7 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH8 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH9 : ((-10000) <= gx_pre)) (PreH10 : (gx_pre <= 10000)) (PreH11 : ((-10000) <= gy_pre)) (PreH12 : (gy_pre <= 10000)) (PreH13 : ((-10000) <= a_x_pre)) (PreH14 : (a_x_pre <= 10000)) (PreH15 : ((-10000) <= a_y_pre)) (PreH16 : (a_y_pre <= 10000)) (PreH17 : ((-10000) <= b_x_pre)) (PreH18 : (b_x_pre <= 10000)) (PreH19 : ((-10000) <= b_y_pre)) (PreH20 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_110 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre < b_x_pre)) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH6 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH7 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH8 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH9 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH10 : ((-10000) <= gx_pre)) (PreH11 : (gx_pre <= 10000)) (PreH12 : ((-10000) <= gy_pre)) (PreH13 : (gy_pre <= 10000)) (PreH14 : ((-10000) <= a_x_pre)) (PreH15 : (a_x_pre <= 10000)) (PreH16 : ((-10000) <= a_y_pre)) (PreH17 : (a_y_pre <= 10000)) (PreH18 : ((-10000) <= b_x_pre)) (PreH19 : (b_x_pre <= 10000)) (PreH20 : ((-10000) <= b_y_pre)) (PreH21 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def cmp_polar_values_safety_wit_111 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre < b_x_pre)) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH6 : ((b_x_pre - gx_pre) < (0 : Int))) (PreH7 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH9 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH11 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH12 : ((-10000) <= gx_pre)) (PreH13 : (gx_pre <= 10000)) (PreH14 : ((-10000) <= gy_pre)) (PreH15 : (gy_pre <= 10000)) (PreH16 : ((-10000) <= a_x_pre)) (PreH17 : (a_x_pre <= 10000)) (PreH18 : ((-10000) <= a_y_pre)) (PreH19 : (a_y_pre <= 10000)) (PreH20 : ((-10000) <= b_x_pre)) (PreH21 : (b_x_pre <= 10000)) (PreH22 : ((-10000) <= b_y_pre)) (PreH23 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def cmp_polar_values_safety_wit_112 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre < b_x_pre)) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH6 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH7 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH9 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH11 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH12 : ((-10000) <= gx_pre)) (PreH13 : (gx_pre <= 10000)) (PreH14 : ((-10000) <= gy_pre)) (PreH15 : (gy_pre <= 10000)) (PreH16 : ((-10000) <= a_x_pre)) (PreH17 : (a_x_pre <= 10000)) (PreH18 : ((-10000) <= a_y_pre)) (PreH19 : (a_y_pre <= 10000)) (PreH20 : ((-10000) <= b_x_pre)) (PreH21 : (b_x_pre <= 10000)) (PreH22 : ((-10000) <= b_y_pre)) (PreH23 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def cmp_polar_values_safety_wit_113 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre < b_x_pre)) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH6 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH7 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH9 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH10 : ((-10000) <= gx_pre)) (PreH11 : (gx_pre <= 10000)) (PreH12 : ((-10000) <= gy_pre)) (PreH13 : (gy_pre <= 10000)) (PreH14 : ((-10000) <= a_x_pre)) (PreH15 : (a_x_pre <= 10000)) (PreH16 : ((-10000) <= a_y_pre)) (PreH17 : (a_y_pre <= 10000)) (PreH18 : ((-10000) <= b_x_pre)) (PreH19 : (b_x_pre <= 10000)) (PreH20 : ((-10000) <= b_y_pre)) (PreH21 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def cmp_polar_values_safety_wit_114 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre < b_x_pre)) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH6 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH7 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH8 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH9 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH10 : ((-10000) <= gx_pre)) (PreH11 : (gx_pre <= 10000)) (PreH12 : ((-10000) <= gy_pre)) (PreH13 : (gy_pre <= 10000)) (PreH14 : ((-10000) <= a_x_pre)) (PreH15 : (a_x_pre <= 10000)) (PreH16 : ((-10000) <= a_y_pre)) (PreH17 : (a_y_pre <= 10000)) (PreH18 : ((-10000) <= b_x_pre)) (PreH19 : (b_x_pre <= 10000)) (PreH20 : ((-10000) <= b_y_pre)) (PreH21 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def cmp_polar_values_safety_wit_115 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre < b_x_pre)) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH6 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH7 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH8 : ((-10000) <= gx_pre)) (PreH9 : (gx_pre <= 10000)) (PreH10 : ((-10000) <= gy_pre)) (PreH11 : (gy_pre <= 10000)) (PreH12 : ((-10000) <= a_x_pre)) (PreH13 : (a_x_pre <= 10000)) (PreH14 : ((-10000) <= a_y_pre)) (PreH15 : (a_y_pre <= 10000)) (PreH16 : ((-10000) <= b_x_pre)) (PreH17 : (b_x_pre <= 10000)) (PreH18 : ((-10000) <= b_y_pre)) (PreH19 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def cmp_polar_values_safety_wit_116 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre < b_x_pre)) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH6 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH7 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH8 : ((-10000) <= gx_pre)) (PreH9 : (gx_pre <= 10000)) (PreH10 : ((-10000) <= gy_pre)) (PreH11 : (gy_pre <= 10000)) (PreH12 : ((-10000) <= a_x_pre)) (PreH13 : (a_x_pre <= 10000)) (PreH14 : ((-10000) <= a_y_pre)) (PreH15 : (a_y_pre <= 10000)) (PreH16 : ((-10000) <= b_x_pre)) (PreH17 : (b_x_pre <= 10000)) (PreH18 : ((-10000) <= b_y_pre)) (PreH19 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_117 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre < b_x_pre)) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH6 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH7 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH8 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH9 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH10 : ((-10000) <= gx_pre)) (PreH11 : (gx_pre <= 10000)) (PreH12 : ((-10000) <= gy_pre)) (PreH13 : (gy_pre <= 10000)) (PreH14 : ((-10000) <= a_x_pre)) (PreH15 : (a_x_pre <= 10000)) (PreH16 : ((-10000) <= a_y_pre)) (PreH17 : (a_y_pre <= 10000)) (PreH18 : ((-10000) <= b_x_pre)) (PreH19 : (b_x_pre <= 10000)) (PreH20 : ((-10000) <= b_y_pre)) (PreH21 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_118 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre < b_x_pre)) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH6 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH7 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH9 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH10 : ((-10000) <= gx_pre)) (PreH11 : (gx_pre <= 10000)) (PreH12 : ((-10000) <= gy_pre)) (PreH13 : (gy_pre <= 10000)) (PreH14 : ((-10000) <= a_x_pre)) (PreH15 : (a_x_pre <= 10000)) (PreH16 : ((-10000) <= a_y_pre)) (PreH17 : (a_y_pre <= 10000)) (PreH18 : ((-10000) <= b_x_pre)) (PreH19 : (b_x_pre <= 10000)) (PreH20 : ((-10000) <= b_y_pre)) (PreH21 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_119 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre < b_x_pre)) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH6 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH7 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH9 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH11 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH12 : ((-10000) <= gx_pre)) (PreH13 : (gx_pre <= 10000)) (PreH14 : ((-10000) <= gy_pre)) (PreH15 : (gy_pre <= 10000)) (PreH16 : ((-10000) <= a_x_pre)) (PreH17 : (a_x_pre <= 10000)) (PreH18 : ((-10000) <= a_y_pre)) (PreH19 : (a_y_pre <= 10000)) (PreH20 : ((-10000) <= b_x_pre)) (PreH21 : (b_x_pre <= 10000)) (PreH22 : ((-10000) <= b_y_pre)) (PreH23 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_120 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre < b_x_pre)) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH6 : ((b_x_pre - gx_pre) < (0 : Int))) (PreH7 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH9 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH11 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH12 : ((-10000) <= gx_pre)) (PreH13 : (gx_pre <= 10000)) (PreH14 : ((-10000) <= gy_pre)) (PreH15 : (gy_pre <= 10000)) (PreH16 : ((-10000) <= a_x_pre)) (PreH17 : (a_x_pre <= 10000)) (PreH18 : ((-10000) <= a_y_pre)) (PreH19 : (a_y_pre <= 10000)) (PreH20 : ((-10000) <= b_x_pre)) (PreH21 : (b_x_pre <= 10000)) (PreH22 : ((-10000) <= b_y_pre)) (PreH23 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_121 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre < b_x_pre)) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH6 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH7 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH8 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH9 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH10 : ((-10000) <= gx_pre)) (PreH11 : (gx_pre <= 10000)) (PreH12 : ((-10000) <= gy_pre)) (PreH13 : (gy_pre <= 10000)) (PreH14 : ((-10000) <= a_x_pre)) (PreH15 : (a_x_pre <= 10000)) (PreH16 : ((-10000) <= a_y_pre)) (PreH17 : (a_y_pre <= 10000)) (PreH18 : ((-10000) <= b_x_pre)) (PreH19 : (b_x_pre <= 10000)) (PreH20 : ((-10000) <= b_y_pre)) (PreH21 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_122 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre > b_x_pre)) (PreH2 : (a_x_pre >= b_x_pre)) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH7 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH8 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH9 : ((-10000) <= gx_pre)) (PreH10 : (gx_pre <= 10000)) (PreH11 : ((-10000) <= gy_pre)) (PreH12 : (gy_pre <= 10000)) (PreH13 : ((-10000) <= a_x_pre)) (PreH14 : (a_x_pre <= 10000)) (PreH15 : ((-10000) <= a_y_pre)) (PreH16 : (a_y_pre <= 10000)) (PreH17 : ((-10000) <= b_x_pre)) (PreH18 : (b_x_pre <= 10000)) (PreH19 : ((-10000) <= b_y_pre)) (PreH20 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_123 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre > b_x_pre)) (PreH2 : (a_x_pre >= b_x_pre)) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH7 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH8 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH9 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH11 : ((-10000) <= gx_pre)) (PreH12 : (gx_pre <= 10000)) (PreH13 : ((-10000) <= gy_pre)) (PreH14 : (gy_pre <= 10000)) (PreH15 : ((-10000) <= a_x_pre)) (PreH16 : (a_x_pre <= 10000)) (PreH17 : ((-10000) <= a_y_pre)) (PreH18 : (a_y_pre <= 10000)) (PreH19 : ((-10000) <= b_x_pre)) (PreH20 : (b_x_pre <= 10000)) (PreH21 : ((-10000) <= b_y_pre)) (PreH22 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_124 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre > b_x_pre)) (PreH2 : (a_x_pre >= b_x_pre)) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH7 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH9 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH11 : ((-10000) <= gx_pre)) (PreH12 : (gx_pre <= 10000)) (PreH13 : ((-10000) <= gy_pre)) (PreH14 : (gy_pre <= 10000)) (PreH15 : ((-10000) <= a_x_pre)) (PreH16 : (a_x_pre <= 10000)) (PreH17 : ((-10000) <= a_y_pre)) (PreH18 : (a_y_pre <= 10000)) (PreH19 : ((-10000) <= b_x_pre)) (PreH20 : (b_x_pre <= 10000)) (PreH21 : ((-10000) <= b_y_pre)) (PreH22 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_125 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre > b_x_pre)) (PreH2 : (a_x_pre >= b_x_pre)) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH7 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH9 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH10 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH11 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH12 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH13 : ((-10000) <= gx_pre)) (PreH14 : (gx_pre <= 10000)) (PreH15 : ((-10000) <= gy_pre)) (PreH16 : (gy_pre <= 10000)) (PreH17 : ((-10000) <= a_x_pre)) (PreH18 : (a_x_pre <= 10000)) (PreH19 : ((-10000) <= a_y_pre)) (PreH20 : (a_y_pre <= 10000)) (PreH21 : ((-10000) <= b_x_pre)) (PreH22 : (b_x_pre <= 10000)) (PreH23 : ((-10000) <= b_y_pre)) (PreH24 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_126 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre > b_x_pre)) (PreH2 : (a_x_pre >= b_x_pre)) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH7 : ((b_x_pre - gx_pre) < (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH9 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH10 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH11 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH12 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH13 : ((-10000) <= gx_pre)) (PreH14 : (gx_pre <= 10000)) (PreH15 : ((-10000) <= gy_pre)) (PreH16 : (gy_pre <= 10000)) (PreH17 : ((-10000) <= a_x_pre)) (PreH18 : (a_x_pre <= 10000)) (PreH19 : ((-10000) <= a_y_pre)) (PreH20 : (a_y_pre <= 10000)) (PreH21 : ((-10000) <= b_x_pre)) (PreH22 : (b_x_pre <= 10000)) (PreH23 : ((-10000) <= b_y_pre)) (PreH24 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_127 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre > b_x_pre)) (PreH2 : (a_x_pre >= b_x_pre)) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH7 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH9 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH11 : ((-10000) <= gx_pre)) (PreH12 : (gx_pre <= 10000)) (PreH13 : ((-10000) <= gy_pre)) (PreH14 : (gy_pre <= 10000)) (PreH15 : ((-10000) <= a_x_pre)) (PreH16 : (a_x_pre <= 10000)) (PreH17 : ((-10000) <= a_y_pre)) (PreH18 : (a_y_pre <= 10000)) (PreH19 : ((-10000) <= b_x_pre)) (PreH20 : (b_x_pre <= 10000)) (PreH21 : ((-10000) <= b_y_pre)) (PreH22 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_128 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre >= b_y_pre)) (PreH2 : (a_x_pre <= b_x_pre)) (PreH3 : (a_x_pre >= b_x_pre)) (PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH9 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH11 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH12 : ((-10000) <= gx_pre)) (PreH13 : (gx_pre <= 10000)) (PreH14 : ((-10000) <= gy_pre)) (PreH15 : (gy_pre <= 10000)) (PreH16 : ((-10000) <= a_x_pre)) (PreH17 : (a_x_pre <= 10000)) (PreH18 : ((-10000) <= a_y_pre)) (PreH19 : (a_y_pre <= 10000)) (PreH20 : ((-10000) <= b_x_pre)) (PreH21 : (b_x_pre <= 10000)) (PreH22 : ((-10000) <= b_y_pre)) (PreH23 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ False ”

noncomputable def cmp_polar_values_safety_wit_129 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre < b_y_pre)) (PreH2 : (a_x_pre <= b_x_pre)) (PreH3 : (a_x_pre >= b_x_pre)) (PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH8 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH9 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH10 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH11 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH12 : ((-10000) <= gx_pre)) (PreH13 : (gx_pre <= 10000)) (PreH14 : ((-10000) <= gy_pre)) (PreH15 : (gy_pre <= 10000)) (PreH16 : ((-10000) <= a_x_pre)) (PreH17 : (a_x_pre <= 10000)) (PreH18 : ((-10000) <= a_y_pre)) (PreH19 : (a_y_pre <= 10000)) (PreH20 : ((-10000) <= b_x_pre)) (PreH21 : (b_x_pre <= 10000)) (PreH22 : ((-10000) <= b_y_pre)) (PreH23 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ False ”

noncomputable def cmp_polar_values_safety_wit_130 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre < b_y_pre)) (PreH2 : (a_x_pre <= b_x_pre)) (PreH3 : (a_x_pre >= b_x_pre)) (PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH8 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH9 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH10 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH11 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH12 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH13 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH14 : ((-10000) <= gx_pre)) (PreH15 : (gx_pre <= 10000)) (PreH16 : ((-10000) <= gy_pre)) (PreH17 : (gy_pre <= 10000)) (PreH18 : ((-10000) <= a_x_pre)) (PreH19 : (a_x_pre <= 10000)) (PreH20 : ((-10000) <= a_y_pre)) (PreH21 : (a_y_pre <= 10000)) (PreH22 : ((-10000) <= b_x_pre)) (PreH23 : (b_x_pre <= 10000)) (PreH24 : ((-10000) <= b_y_pre)) (PreH25 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ False ”

noncomputable def cmp_polar_values_safety_wit_131 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre < b_y_pre)) (PreH2 : (a_x_pre <= b_x_pre)) (PreH3 : (a_x_pre >= b_x_pre)) (PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH8 : ((b_x_pre - gx_pre) < (0 : Int))) (PreH9 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH10 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH11 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH12 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH13 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH14 : ((-10000) <= gx_pre)) (PreH15 : (gx_pre <= 10000)) (PreH16 : ((-10000) <= gy_pre)) (PreH17 : (gy_pre <= 10000)) (PreH18 : ((-10000) <= a_x_pre)) (PreH19 : (a_x_pre <= 10000)) (PreH20 : ((-10000) <= a_y_pre)) (PreH21 : (a_y_pre <= 10000)) (PreH22 : ((-10000) <= b_x_pre)) (PreH23 : (b_x_pre <= 10000)) (PreH24 : ((-10000) <= b_y_pre)) (PreH25 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ False ”

noncomputable def cmp_polar_values_safety_wit_132 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre < b_y_pre)) (PreH2 : (a_x_pre <= b_x_pre)) (PreH3 : (a_x_pre >= b_x_pre)) (PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH9 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH11 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH12 : ((-10000) <= gx_pre)) (PreH13 : (gx_pre <= 10000)) (PreH14 : ((-10000) <= gy_pre)) (PreH15 : (gy_pre <= 10000)) (PreH16 : ((-10000) <= a_x_pre)) (PreH17 : (a_x_pre <= 10000)) (PreH18 : ((-10000) <= a_y_pre)) (PreH19 : (a_y_pre <= 10000)) (PreH20 : ((-10000) <= b_x_pre)) (PreH21 : (b_x_pre <= 10000)) (PreH22 : ((-10000) <= b_y_pre)) (PreH23 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def cmp_polar_values_safety_wit_133 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre < b_y_pre)) (PreH2 : (a_x_pre <= b_x_pre)) (PreH3 : (a_x_pre >= b_x_pre)) (PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH9 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH11 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH12 : ((-10000) <= gx_pre)) (PreH13 : (gx_pre <= 10000)) (PreH14 : ((-10000) <= gy_pre)) (PreH15 : (gy_pre <= 10000)) (PreH16 : ((-10000) <= a_x_pre)) (PreH17 : (a_x_pre <= 10000)) (PreH18 : ((-10000) <= a_y_pre)) (PreH19 : (a_y_pre <= 10000)) (PreH20 : ((-10000) <= b_x_pre)) (PreH21 : (b_x_pre <= 10000)) (PreH22 : ((-10000) <= b_y_pre)) (PreH23 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def cmp_polar_values_safety_wit_134 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre < b_y_pre)) (PreH2 : (a_x_pre <= b_x_pre)) (PreH3 : (a_x_pre >= b_x_pre)) (PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH9 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH10 : ((-10000) <= gx_pre)) (PreH11 : (gx_pre <= 10000)) (PreH12 : ((-10000) <= gy_pre)) (PreH13 : (gy_pre <= 10000)) (PreH14 : ((-10000) <= a_x_pre)) (PreH15 : (a_x_pre <= 10000)) (PreH16 : ((-10000) <= a_y_pre)) (PreH17 : (a_y_pre <= 10000)) (PreH18 : ((-10000) <= b_x_pre)) (PreH19 : (b_x_pre <= 10000)) (PreH20 : ((-10000) <= b_y_pre)) (PreH21 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 ≠ (INT_MIN)) ”

noncomputable def cmp_polar_values_safety_wit_135 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre < b_y_pre)) (PreH2 : (a_x_pre <= b_x_pre)) (PreH3 : (a_x_pre >= b_x_pre)) (PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH9 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH10 : ((-10000) <= gx_pre)) (PreH11 : (gx_pre <= 10000)) (PreH12 : ((-10000) <= gy_pre)) (PreH13 : (gy_pre <= 10000)) (PreH14 : ((-10000) <= a_x_pre)) (PreH15 : (a_x_pre <= 10000)) (PreH16 : ((-10000) <= a_y_pre)) (PreH17 : (a_y_pre <= 10000)) (PreH18 : ((-10000) <= b_x_pre)) (PreH19 : (b_x_pre <= 10000)) (PreH20 : ((-10000) <= b_y_pre)) (PreH21 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_136 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre < b_y_pre)) (PreH2 : (a_x_pre <= b_x_pre)) (PreH3 : (a_x_pre >= b_x_pre)) (PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH9 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH11 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH12 : ((-10000) <= gx_pre)) (PreH13 : (gx_pre <= 10000)) (PreH14 : ((-10000) <= gy_pre)) (PreH15 : (gy_pre <= 10000)) (PreH16 : ((-10000) <= a_x_pre)) (PreH17 : (a_x_pre <= 10000)) (PreH18 : ((-10000) <= a_y_pre)) (PreH19 : (a_y_pre <= 10000)) (PreH20 : ((-10000) <= b_x_pre)) (PreH21 : (b_x_pre <= 10000)) (PreH22 : ((-10000) <= b_y_pre)) (PreH23 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_137 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre < b_y_pre)) (PreH2 : (a_x_pre <= b_x_pre)) (PreH3 : (a_x_pre >= b_x_pre)) (PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH9 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH11 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH12 : ((-10000) <= gx_pre)) (PreH13 : (gx_pre <= 10000)) (PreH14 : ((-10000) <= gy_pre)) (PreH15 : (gy_pre <= 10000)) (PreH16 : ((-10000) <= a_x_pre)) (PreH17 : (a_x_pre <= 10000)) (PreH18 : ((-10000) <= a_y_pre)) (PreH19 : (a_y_pre <= 10000)) (PreH20 : ((-10000) <= b_x_pre)) (PreH21 : (b_x_pre <= 10000)) (PreH22 : ((-10000) <= b_y_pre)) (PreH23 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_138 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre <= b_y_pre)) (PreH2 : (a_y_pre >= b_y_pre)) (PreH3 : (a_x_pre <= b_x_pre)) (PreH4 : (a_x_pre >= b_x_pre)) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH8 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH9 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH10 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH11 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH12 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH13 : ((-10000) <= gx_pre)) (PreH14 : (gx_pre <= 10000)) (PreH15 : ((-10000) <= gy_pre)) (PreH16 : (gy_pre <= 10000)) (PreH17 : ((-10000) <= a_x_pre)) (PreH18 : (a_x_pre <= 10000)) (PreH19 : ((-10000) <= a_y_pre)) (PreH20 : (a_y_pre <= 10000)) (PreH21 : ((-10000) <= b_x_pre)) (PreH22 : (b_x_pre <= 10000)) (PreH23 : ((-10000) <= b_y_pre)) (PreH24 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ False ”

noncomputable def cmp_polar_values_safety_wit_139 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre > b_y_pre)) (PreH2 : (a_y_pre >= b_y_pre)) (PreH3 : (a_x_pre <= b_x_pre)) (PreH4 : (a_x_pre >= b_x_pre)) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH8 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH9 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH10 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH11 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH12 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH13 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH14 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH15 : ((-10000) <= gx_pre)) (PreH16 : (gx_pre <= 10000)) (PreH17 : ((-10000) <= gy_pre)) (PreH18 : (gy_pre <= 10000)) (PreH19 : ((-10000) <= a_x_pre)) (PreH20 : (a_x_pre <= 10000)) (PreH21 : ((-10000) <= a_y_pre)) (PreH22 : (a_y_pre <= 10000)) (PreH23 : ((-10000) <= b_x_pre)) (PreH24 : (b_x_pre <= 10000)) (PreH25 : ((-10000) <= b_y_pre)) (PreH26 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ False ”

noncomputable def cmp_polar_values_safety_wit_140 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre > b_y_pre)) (PreH2 : (a_y_pre >= b_y_pre)) (PreH3 : (a_x_pre <= b_x_pre)) (PreH4 : (a_x_pre >= b_x_pre)) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH8 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH9 : ((b_x_pre - gx_pre) < (0 : Int))) (PreH10 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH11 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH12 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH13 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH14 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH15 : ((-10000) <= gx_pre)) (PreH16 : (gx_pre <= 10000)) (PreH17 : ((-10000) <= gy_pre)) (PreH18 : (gy_pre <= 10000)) (PreH19 : ((-10000) <= a_x_pre)) (PreH20 : (a_x_pre <= 10000)) (PreH21 : ((-10000) <= a_y_pre)) (PreH22 : (a_y_pre <= 10000)) (PreH23 : ((-10000) <= b_x_pre)) (PreH24 : (b_x_pre <= 10000)) (PreH25 : ((-10000) <= b_y_pre)) (PreH26 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ False ”

noncomputable def cmp_polar_values_safety_wit_141 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre > b_y_pre)) (PreH2 : (a_y_pre >= b_y_pre)) (PreH3 : (a_x_pre <= b_x_pre)) (PreH4 : (a_x_pre >= b_x_pre)) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH8 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH9 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH11 : ((-10000) <= gx_pre)) (PreH12 : (gx_pre <= 10000)) (PreH13 : ((-10000) <= gy_pre)) (PreH14 : (gy_pre <= 10000)) (PreH15 : ((-10000) <= a_x_pre)) (PreH16 : (a_x_pre <= 10000)) (PreH17 : ((-10000) <= a_y_pre)) (PreH18 : (a_y_pre <= 10000)) (PreH19 : ((-10000) <= b_x_pre)) (PreH20 : (b_x_pre <= 10000)) (PreH21 : ((-10000) <= b_y_pre)) (PreH22 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_142 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre > b_y_pre)) (PreH2 : (a_y_pre >= b_y_pre)) (PreH3 : (a_x_pre <= b_x_pre)) (PreH4 : (a_x_pre >= b_x_pre)) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH8 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH9 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH10 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH11 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH12 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH13 : ((-10000) <= gx_pre)) (PreH14 : (gx_pre <= 10000)) (PreH15 : ((-10000) <= gy_pre)) (PreH16 : (gy_pre <= 10000)) (PreH17 : ((-10000) <= a_x_pre)) (PreH18 : (a_x_pre <= 10000)) (PreH19 : ((-10000) <= a_y_pre)) (PreH20 : (a_y_pre <= 10000)) (PreH21 : ((-10000) <= b_x_pre)) (PreH22 : (b_x_pre <= 10000)) (PreH23 : ((-10000) <= b_y_pre)) (PreH24 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_143 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre > b_y_pre)) (PreH2 : (a_y_pre >= b_y_pre)) (PreH3 : (a_x_pre <= b_x_pre)) (PreH4 : (a_x_pre >= b_x_pre)) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH8 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH9 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH10 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH11 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH12 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH13 : ((-10000) <= gx_pre)) (PreH14 : (gx_pre <= 10000)) (PreH15 : ((-10000) <= gy_pre)) (PreH16 : (gy_pre <= 10000)) (PreH17 : ((-10000) <= a_x_pre)) (PreH18 : (a_x_pre <= 10000)) (PreH19 : ((-10000) <= a_y_pre)) (PreH20 : (a_y_pre <= 10000)) (PreH21 : ((-10000) <= b_x_pre)) (PreH22 : (b_x_pre <= 10000)) (PreH23 : ((-10000) <= b_y_pre)) (PreH24 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def cmp_polar_values_safety_wit_144 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre <= b_y_pre)) (PreH2 : (a_y_pre >= b_y_pre)) (PreH3 : (a_x_pre <= b_x_pre)) (PreH4 : (a_x_pre >= b_x_pre)) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH8 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH9 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH11 : ((-10000) <= gx_pre)) (PreH12 : (gx_pre <= 10000)) (PreH13 : ((-10000) <= gy_pre)) (PreH14 : (gy_pre <= 10000)) (PreH15 : ((-10000) <= a_x_pre)) (PreH16 : (a_x_pre <= 10000)) (PreH17 : ((-10000) <= a_y_pre)) (PreH18 : (a_y_pre <= 10000)) (PreH19 : ((-10000) <= b_x_pre)) (PreH20 : (b_x_pre <= 10000)) (PreH21 : ((-10000) <= b_y_pre)) (PreH22 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def cmp_polar_values_safety_wit_145 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre <= b_y_pre)) (PreH2 : (a_y_pre >= b_y_pre)) (PreH3 : (a_x_pre <= b_x_pre)) (PreH4 : (a_x_pre >= b_x_pre)) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH8 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH9 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH10 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH11 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH12 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH13 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH14 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH15 : ((-10000) <= gx_pre)) (PreH16 : (gx_pre <= 10000)) (PreH17 : ((-10000) <= gy_pre)) (PreH18 : (gy_pre <= 10000)) (PreH19 : ((-10000) <= a_x_pre)) (PreH20 : (a_x_pre <= 10000)) (PreH21 : ((-10000) <= a_y_pre)) (PreH22 : (a_y_pre <= 10000)) (PreH23 : ((-10000) <= b_x_pre)) (PreH24 : (b_x_pre <= 10000)) (PreH25 : ((-10000) <= b_y_pre)) (PreH26 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> (1))
  ** ((( &( "ah" ) )) # Int |-> (1))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def cmp_polar_values_safety_wit_146 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre <= b_y_pre)) (PreH2 : (a_y_pre >= b_y_pre)) (PreH3 : (a_x_pre <= b_x_pre)) (PreH4 : (a_x_pre >= b_x_pre)) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH8 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH9 : ((b_x_pre - gx_pre) < (0 : Int))) (PreH10 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH11 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH12 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH13 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH14 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH15 : ((-10000) <= gx_pre)) (PreH16 : (gx_pre <= 10000)) (PreH17 : ((-10000) <= gy_pre)) (PreH18 : (gy_pre <= 10000)) (PreH19 : ((-10000) <= a_x_pre)) (PreH20 : (a_x_pre <= 10000)) (PreH21 : ((-10000) <= a_y_pre)) (PreH22 : (a_y_pre <= 10000)) (PreH23 : ((-10000) <= b_x_pre)) (PreH24 : (b_x_pre <= 10000)) (PreH25 : ((-10000) <= b_y_pre)) (PreH26 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def cmp_polar_values_safety_wit_147 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre <= b_y_pre)) (PreH2 : (a_y_pre >= b_y_pre)) (PreH3 : (a_x_pre <= b_x_pre)) (PreH4 : (a_x_pre >= b_x_pre)) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH8 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH9 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH10 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH11 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH12 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH13 : ((-10000) <= gx_pre)) (PreH14 : (gx_pre <= 10000)) (PreH15 : ((-10000) <= gy_pre)) (PreH16 : (gy_pre <= 10000)) (PreH17 : ((-10000) <= a_x_pre)) (PreH18 : (a_x_pre <= 10000)) (PreH19 : ((-10000) <= a_y_pre)) (PreH20 : (a_y_pre <= 10000)) (PreH21 : ((-10000) <= b_x_pre)) (PreH22 : (b_x_pre <= 10000)) (PreH23 : ((-10000) <= b_y_pre)) (PreH24 : (b_y_pre <= 10000)) ,
  ((( &( "bh" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "ah" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "db" ) )) # Int |-> ((((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre)))))
  ** ((( &( "da" ) )) # Int |-> ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre)))))
  ** ((( &( "cr" ) )) # Int |-> ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre)))))
  ** ((( &( "bdy" ) )) # Int |-> ((b_y_pre - gy_pre)))
  ** ((( &( "bdx" ) )) # Int |-> ((b_x_pre - gx_pre)))
  ** ((( &( "ady" ) )) # Int |-> ((a_y_pre - gy_pre)))
  ** ((( &( "adx" ) )) # Int |-> ((a_x_pre - gx_pre)))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "a_x" ) )) # Int |-> (a_x_pre))
  ** ((( &( "a_y" ) )) # Int |-> (a_y_pre))
  ** ((( &( "b_x" ) )) # Int |-> (b_x_pre))
  ** ((( &( "b_y" ) )) # Int |-> (b_y_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def cmp_polar_values_return_wit_1 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre <= b_y_pre)) (PreH2 : (a_y_pre >= b_y_pre)) (PreH3 : (a_x_pre <= b_x_pre)) (PreH4 : (a_x_pre >= b_x_pre)) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH8 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH9 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH11 : ((-10000) <= gx_pre)) (PreH12 : (gx_pre <= 10000)) (PreH13 : ((-10000) <= gy_pre)) (PreH14 : (gy_pre <= 10000)) (PreH15 : ((-10000) <= a_x_pre)) (PreH16 : (a_x_pre <= 10000)) (PreH17 : ((-10000) <= a_y_pre)) (PreH18 : (a_y_pre <= 10000)) (PreH19 : ((-10000) <= b_x_pre)) (PreH20 : (b_x_pre <= 10000)) (PreH21 : ((-10000) <= b_y_pre)) (PreH22 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (0 : Int)) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre <= b_y_pre)) (PreH2 : (a_y_pre >= b_y_pre)) (PreH3 : (a_x_pre <= b_x_pre)) (PreH4 : (a_x_pre >= b_x_pre)) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH8 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH9 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH11 : ((-10000) <= gx_pre)) (PreH12 : (gx_pre <= 10000)) (PreH13 : ((-10000) <= gy_pre)) (PreH14 : (gy_pre <= 10000)) (PreH15 : ((-10000) <= a_x_pre)) (PreH16 : (a_x_pre <= 10000)) (PreH17 : ((-10000) <= a_y_pre)) (PreH18 : (a_y_pre <= 10000)) (PreH19 : ((-10000) <= b_x_pre)) (PreH20 : (b_x_pre <= 10000)) (PreH21 : ((-10000) <= b_y_pre)) (PreH22 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (0 : Int)) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_1_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre <= b_y_pre)) (PreH2 : (a_y_pre >= b_y_pre)) (PreH3 : (a_x_pre <= b_x_pre)) (PreH4 : (a_x_pre >= b_x_pre)) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH8 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH9 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH11 : ((-10000) <= gx_pre)) (PreH12 : (gx_pre <= 10000)) (PreH13 : ((-10000) <= gy_pre)) (PreH14 : (gy_pre <= 10000)) (PreH15 : ((-10000) <= a_x_pre)) (PreH16 : (a_x_pre <= 10000)) (PreH17 : ((-10000) <= a_y_pre)) (PreH18 : (a_y_pre <= 10000)) (PreH19 : ((-10000) <= b_x_pre)) (PreH20 : (b_x_pre <= 10000)) (PreH21 : ((-10000) <= b_y_pre)) (PreH22 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (0 : Int))

noncomputable def cmp_polar_values_return_wit_2 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre <= b_y_pre)) (PreH2 : (a_y_pre >= b_y_pre)) (PreH3 : (a_x_pre <= b_x_pre)) (PreH4 : (a_x_pre >= b_x_pre)) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH8 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH9 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH10 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH11 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH12 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH13 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH14 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH15 : ((-10000) <= gx_pre)) (PreH16 : (gx_pre <= 10000)) (PreH17 : ((-10000) <= gy_pre)) (PreH18 : (gy_pre <= 10000)) (PreH19 : ((-10000) <= a_x_pre)) (PreH20 : (a_x_pre <= 10000)) (PreH21 : ((-10000) <= a_y_pre)) (PreH22 : (a_y_pre <= 10000)) (PreH23 : ((-10000) <= b_x_pre)) (PreH24 : (b_x_pre <= 10000)) (PreH25 : ((-10000) <= b_y_pre)) (PreH26 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (0 : Int)) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre <= b_y_pre)) (PreH2 : (a_y_pre >= b_y_pre)) (PreH3 : (a_x_pre <= b_x_pre)) (PreH4 : (a_x_pre >= b_x_pre)) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH8 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH9 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH10 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH11 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH12 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH13 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH14 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH15 : ((-10000) <= gx_pre)) (PreH16 : (gx_pre <= 10000)) (PreH17 : ((-10000) <= gy_pre)) (PreH18 : (gy_pre <= 10000)) (PreH19 : ((-10000) <= a_x_pre)) (PreH20 : (a_x_pre <= 10000)) (PreH21 : ((-10000) <= a_y_pre)) (PreH22 : (a_y_pre <= 10000)) (PreH23 : ((-10000) <= b_x_pre)) (PreH24 : (b_x_pre <= 10000)) (PreH25 : ((-10000) <= b_y_pre)) (PreH26 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (0 : Int)) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_2_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre <= b_y_pre)) (PreH2 : (a_y_pre >= b_y_pre)) (PreH3 : (a_x_pre <= b_x_pre)) (PreH4 : (a_x_pre >= b_x_pre)) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH8 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH9 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH10 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH11 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH12 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH13 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH14 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH15 : ((-10000) <= gx_pre)) (PreH16 : (gx_pre <= 10000)) (PreH17 : ((-10000) <= gy_pre)) (PreH18 : (gy_pre <= 10000)) (PreH19 : ((-10000) <= a_x_pre)) (PreH20 : (a_x_pre <= 10000)) (PreH21 : ((-10000) <= a_y_pre)) (PreH22 : (a_y_pre <= 10000)) (PreH23 : ((-10000) <= b_x_pre)) (PreH24 : (b_x_pre <= 10000)) (PreH25 : ((-10000) <= b_y_pre)) (PreH26 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (0 : Int))

noncomputable def cmp_polar_values_return_wit_3 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre <= b_y_pre)) (PreH2 : (a_y_pre >= b_y_pre)) (PreH3 : (a_x_pre <= b_x_pre)) (PreH4 : (a_x_pre >= b_x_pre)) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH8 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH9 : ((b_x_pre - gx_pre) < (0 : Int))) (PreH10 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH11 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH12 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH13 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH14 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH15 : ((-10000) <= gx_pre)) (PreH16 : (gx_pre <= 10000)) (PreH17 : ((-10000) <= gy_pre)) (PreH18 : (gy_pre <= 10000)) (PreH19 : ((-10000) <= a_x_pre)) (PreH20 : (a_x_pre <= 10000)) (PreH21 : ((-10000) <= a_y_pre)) (PreH22 : (a_y_pre <= 10000)) (PreH23 : ((-10000) <= b_x_pre)) (PreH24 : (b_x_pre <= 10000)) (PreH25 : ((-10000) <= b_y_pre)) (PreH26 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (0 : Int)) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre <= b_y_pre)) (PreH2 : (a_y_pre >= b_y_pre)) (PreH3 : (a_x_pre <= b_x_pre)) (PreH4 : (a_x_pre >= b_x_pre)) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH8 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH9 : ((b_x_pre - gx_pre) < (0 : Int))) (PreH10 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH11 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH12 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH13 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH14 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH15 : ((-10000) <= gx_pre)) (PreH16 : (gx_pre <= 10000)) (PreH17 : ((-10000) <= gy_pre)) (PreH18 : (gy_pre <= 10000)) (PreH19 : ((-10000) <= a_x_pre)) (PreH20 : (a_x_pre <= 10000)) (PreH21 : ((-10000) <= a_y_pre)) (PreH22 : (a_y_pre <= 10000)) (PreH23 : ((-10000) <= b_x_pre)) (PreH24 : (b_x_pre <= 10000)) (PreH25 : ((-10000) <= b_y_pre)) (PreH26 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (0 : Int)) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_3_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre <= b_y_pre)) (PreH2 : (a_y_pre >= b_y_pre)) (PreH3 : (a_x_pre <= b_x_pre)) (PreH4 : (a_x_pre >= b_x_pre)) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH8 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH9 : ((b_x_pre - gx_pre) < (0 : Int))) (PreH10 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH11 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH12 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH13 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH14 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH15 : ((-10000) <= gx_pre)) (PreH16 : (gx_pre <= 10000)) (PreH17 : ((-10000) <= gy_pre)) (PreH18 : (gy_pre <= 10000)) (PreH19 : ((-10000) <= a_x_pre)) (PreH20 : (a_x_pre <= 10000)) (PreH21 : ((-10000) <= a_y_pre)) (PreH22 : (a_y_pre <= 10000)) (PreH23 : ((-10000) <= b_x_pre)) (PreH24 : (b_x_pre <= 10000)) (PreH25 : ((-10000) <= b_y_pre)) (PreH26 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (0 : Int))

noncomputable def cmp_polar_values_return_wit_4 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre <= b_y_pre)) (PreH2 : (a_y_pre >= b_y_pre)) (PreH3 : (a_x_pre <= b_x_pre)) (PreH4 : (a_x_pre >= b_x_pre)) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH8 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH9 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH10 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH11 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH12 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH13 : ((-10000) <= gx_pre)) (PreH14 : (gx_pre <= 10000)) (PreH15 : ((-10000) <= gy_pre)) (PreH16 : (gy_pre <= 10000)) (PreH17 : ((-10000) <= a_x_pre)) (PreH18 : (a_x_pre <= 10000)) (PreH19 : ((-10000) <= a_y_pre)) (PreH20 : (a_y_pre <= 10000)) (PreH21 : ((-10000) <= b_x_pre)) (PreH22 : (b_x_pre <= 10000)) (PreH23 : ((-10000) <= b_y_pre)) (PreH24 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (0 : Int)) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre <= b_y_pre)) (PreH2 : (a_y_pre >= b_y_pre)) (PreH3 : (a_x_pre <= b_x_pre)) (PreH4 : (a_x_pre >= b_x_pre)) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH8 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH9 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH10 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH11 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH12 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH13 : ((-10000) <= gx_pre)) (PreH14 : (gx_pre <= 10000)) (PreH15 : ((-10000) <= gy_pre)) (PreH16 : (gy_pre <= 10000)) (PreH17 : ((-10000) <= a_x_pre)) (PreH18 : (a_x_pre <= 10000)) (PreH19 : ((-10000) <= a_y_pre)) (PreH20 : (a_y_pre <= 10000)) (PreH21 : ((-10000) <= b_x_pre)) (PreH22 : (b_x_pre <= 10000)) (PreH23 : ((-10000) <= b_y_pre)) (PreH24 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (0 : Int)) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_4_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre <= b_y_pre)) (PreH2 : (a_y_pre >= b_y_pre)) (PreH3 : (a_x_pre <= b_x_pre)) (PreH4 : (a_x_pre >= b_x_pre)) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH8 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH9 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH10 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH11 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH12 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH13 : ((-10000) <= gx_pre)) (PreH14 : (gx_pre <= 10000)) (PreH15 : ((-10000) <= gy_pre)) (PreH16 : (gy_pre <= 10000)) (PreH17 : ((-10000) <= a_x_pre)) (PreH18 : (a_x_pre <= 10000)) (PreH19 : ((-10000) <= a_y_pre)) (PreH20 : (a_y_pre <= 10000)) (PreH21 : ((-10000) <= b_x_pre)) (PreH22 : (b_x_pre <= 10000)) (PreH23 : ((-10000) <= b_y_pre)) (PreH24 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (0 : Int))

noncomputable def cmp_polar_values_return_wit_5 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre > b_y_pre)) (PreH2 : (a_y_pre >= b_y_pre)) (PreH3 : (a_x_pre <= b_x_pre)) (PreH4 : (a_x_pre >= b_x_pre)) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH8 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH9 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH11 : ((-10000) <= gx_pre)) (PreH12 : (gx_pre <= 10000)) (PreH13 : ((-10000) <= gy_pre)) (PreH14 : (gy_pre <= 10000)) (PreH15 : ((-10000) <= a_x_pre)) (PreH16 : (a_x_pre <= 10000)) (PreH17 : ((-10000) <= a_y_pre)) (PreH18 : (a_y_pre <= 10000)) (PreH19 : ((-10000) <= b_x_pre)) (PreH20 : (b_x_pre <= 10000)) (PreH21 : ((-10000) <= b_y_pre)) (PreH22 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre > b_y_pre)) (PreH2 : (a_y_pre >= b_y_pre)) (PreH3 : (a_x_pre <= b_x_pre)) (PreH4 : (a_x_pre >= b_x_pre)) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH8 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH9 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH11 : ((-10000) <= gx_pre)) (PreH12 : (gx_pre <= 10000)) (PreH13 : ((-10000) <= gy_pre)) (PreH14 : (gy_pre <= 10000)) (PreH15 : ((-10000) <= a_x_pre)) (PreH16 : (a_x_pre <= 10000)) (PreH17 : ((-10000) <= a_y_pre)) (PreH18 : (a_y_pre <= 10000)) (PreH19 : ((-10000) <= b_x_pre)) (PreH20 : (b_x_pre <= 10000)) (PreH21 : ((-10000) <= b_y_pre)) (PreH22 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_5_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre > b_y_pre)) (PreH2 : (a_y_pre >= b_y_pre)) (PreH3 : (a_x_pre <= b_x_pre)) (PreH4 : (a_x_pre >= b_x_pre)) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH8 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH9 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH11 : ((-10000) <= gx_pre)) (PreH12 : (gx_pre <= 10000)) (PreH13 : ((-10000) <= gy_pre)) (PreH14 : (gy_pre <= 10000)) (PreH15 : ((-10000) <= a_x_pre)) (PreH16 : (a_x_pre <= 10000)) (PreH17 : ((-10000) <= a_y_pre)) (PreH18 : (a_y_pre <= 10000)) (PreH19 : ((-10000) <= b_x_pre)) (PreH20 : (b_x_pre <= 10000)) (PreH21 : ((-10000) <= b_y_pre)) (PreH22 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1)

noncomputable def cmp_polar_values_return_wit_6 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre > b_y_pre)) (PreH2 : (a_y_pre >= b_y_pre)) (PreH3 : (a_x_pre <= b_x_pre)) (PreH4 : (a_x_pre >= b_x_pre)) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH8 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH9 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH10 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH11 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH12 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH13 : ((-10000) <= gx_pre)) (PreH14 : (gx_pre <= 10000)) (PreH15 : ((-10000) <= gy_pre)) (PreH16 : (gy_pre <= 10000)) (PreH17 : ((-10000) <= a_x_pre)) (PreH18 : (a_x_pre <= 10000)) (PreH19 : ((-10000) <= a_y_pre)) (PreH20 : (a_y_pre <= 10000)) (PreH21 : ((-10000) <= b_x_pre)) (PreH22 : (b_x_pre <= 10000)) (PreH23 : ((-10000) <= b_y_pre)) (PreH24 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre > b_y_pre)) (PreH2 : (a_y_pre >= b_y_pre)) (PreH3 : (a_x_pre <= b_x_pre)) (PreH4 : (a_x_pre >= b_x_pre)) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH8 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH9 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH10 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH11 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH12 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH13 : ((-10000) <= gx_pre)) (PreH14 : (gx_pre <= 10000)) (PreH15 : ((-10000) <= gy_pre)) (PreH16 : (gy_pre <= 10000)) (PreH17 : ((-10000) <= a_x_pre)) (PreH18 : (a_x_pre <= 10000)) (PreH19 : ((-10000) <= a_y_pre)) (PreH20 : (a_y_pre <= 10000)) (PreH21 : ((-10000) <= b_x_pre)) (PreH22 : (b_x_pre <= 10000)) (PreH23 : ((-10000) <= b_y_pre)) (PreH24 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_6_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre > b_y_pre)) (PreH2 : (a_y_pre >= b_y_pre)) (PreH3 : (a_x_pre <= b_x_pre)) (PreH4 : (a_x_pre >= b_x_pre)) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH8 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH9 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH10 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH11 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH12 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH13 : ((-10000) <= gx_pre)) (PreH14 : (gx_pre <= 10000)) (PreH15 : ((-10000) <= gy_pre)) (PreH16 : (gy_pre <= 10000)) (PreH17 : ((-10000) <= a_x_pre)) (PreH18 : (a_x_pre <= 10000)) (PreH19 : ((-10000) <= a_y_pre)) (PreH20 : (a_y_pre <= 10000)) (PreH21 : ((-10000) <= b_x_pre)) (PreH22 : (b_x_pre <= 10000)) (PreH23 : ((-10000) <= b_y_pre)) (PreH24 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1)

noncomputable def cmp_polar_values_return_wit_7 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre > b_y_pre)) (PreH2 : (a_y_pre >= b_y_pre)) (PreH3 : (a_x_pre <= b_x_pre)) (PreH4 : (a_x_pre >= b_x_pre)) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH8 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH9 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH10 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH11 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH12 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH13 : ((-10000) <= gx_pre)) (PreH14 : (gx_pre <= 10000)) (PreH15 : ((-10000) <= gy_pre)) (PreH16 : (gy_pre <= 10000)) (PreH17 : ((-10000) <= a_x_pre)) (PreH18 : (a_x_pre <= 10000)) (PreH19 : ((-10000) <= a_y_pre)) (PreH20 : (a_y_pre <= 10000)) (PreH21 : ((-10000) <= b_x_pre)) (PreH22 : (b_x_pre <= 10000)) (PreH23 : ((-10000) <= b_y_pre)) (PreH24 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre > b_y_pre)) (PreH2 : (a_y_pre >= b_y_pre)) (PreH3 : (a_x_pre <= b_x_pre)) (PreH4 : (a_x_pre >= b_x_pre)) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH8 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH9 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH10 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH11 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH12 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH13 : ((-10000) <= gx_pre)) (PreH14 : (gx_pre <= 10000)) (PreH15 : ((-10000) <= gy_pre)) (PreH16 : (gy_pre <= 10000)) (PreH17 : ((-10000) <= a_x_pre)) (PreH18 : (a_x_pre <= 10000)) (PreH19 : ((-10000) <= a_y_pre)) (PreH20 : (a_y_pre <= 10000)) (PreH21 : ((-10000) <= b_x_pre)) (PreH22 : (b_x_pre <= 10000)) (PreH23 : ((-10000) <= b_y_pre)) (PreH24 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_7_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre > b_y_pre)) (PreH2 : (a_y_pre >= b_y_pre)) (PreH3 : (a_x_pre <= b_x_pre)) (PreH4 : (a_x_pre >= b_x_pre)) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH8 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH9 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH10 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH11 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH12 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH13 : ((-10000) <= gx_pre)) (PreH14 : (gx_pre <= 10000)) (PreH15 : ((-10000) <= gy_pre)) (PreH16 : (gy_pre <= 10000)) (PreH17 : ((-10000) <= a_x_pre)) (PreH18 : (a_x_pre <= 10000)) (PreH19 : ((-10000) <= a_y_pre)) (PreH20 : (a_y_pre <= 10000)) (PreH21 : ((-10000) <= b_x_pre)) (PreH22 : (b_x_pre <= 10000)) (PreH23 : ((-10000) <= b_y_pre)) (PreH24 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1)

noncomputable def cmp_polar_values_return_wit_8 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre < b_y_pre)) (PreH2 : (a_x_pre <= b_x_pre)) (PreH3 : (a_x_pre >= b_x_pre)) (PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH9 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH10 : ((-10000) <= gx_pre)) (PreH11 : (gx_pre <= 10000)) (PreH12 : ((-10000) <= gy_pre)) (PreH13 : (gy_pre <= 10000)) (PreH14 : ((-10000) <= a_x_pre)) (PreH15 : (a_x_pre <= 10000)) (PreH16 : ((-10000) <= a_y_pre)) (PreH17 : (a_y_pre <= 10000)) (PreH18 : ((-10000) <= b_x_pre)) (PreH19 : (b_x_pre <= 10000)) (PreH20 : ((-10000) <= b_y_pre)) (PreH21 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1)) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre < b_y_pre)) (PreH2 : (a_x_pre <= b_x_pre)) (PreH3 : (a_x_pre >= b_x_pre)) (PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH9 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH10 : ((-10000) <= gx_pre)) (PreH11 : (gx_pre <= 10000)) (PreH12 : ((-10000) <= gy_pre)) (PreH13 : (gy_pre <= 10000)) (PreH14 : ((-10000) <= a_x_pre)) (PreH15 : (a_x_pre <= 10000)) (PreH16 : ((-10000) <= a_y_pre)) (PreH17 : (a_y_pre <= 10000)) (PreH18 : ((-10000) <= b_x_pre)) (PreH19 : (b_x_pre <= 10000)) (PreH20 : ((-10000) <= b_y_pre)) (PreH21 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1)) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_8_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre < b_y_pre)) (PreH2 : (a_x_pre <= b_x_pre)) (PreH3 : (a_x_pre >= b_x_pre)) (PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH9 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH10 : ((-10000) <= gx_pre)) (PreH11 : (gx_pre <= 10000)) (PreH12 : ((-10000) <= gy_pre)) (PreH13 : (gy_pre <= 10000)) (PreH14 : ((-10000) <= a_x_pre)) (PreH15 : (a_x_pre <= 10000)) (PreH16 : ((-10000) <= a_y_pre)) (PreH17 : (a_y_pre <= 10000)) (PreH18 : ((-10000) <= b_x_pre)) (PreH19 : (b_x_pre <= 10000)) (PreH20 : ((-10000) <= b_y_pre)) (PreH21 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1))

noncomputable def cmp_polar_values_return_wit_9 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre < b_y_pre)) (PreH2 : (a_x_pre <= b_x_pre)) (PreH3 : (a_x_pre >= b_x_pre)) (PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH9 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH11 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH12 : ((-10000) <= gx_pre)) (PreH13 : (gx_pre <= 10000)) (PreH14 : ((-10000) <= gy_pre)) (PreH15 : (gy_pre <= 10000)) (PreH16 : ((-10000) <= a_x_pre)) (PreH17 : (a_x_pre <= 10000)) (PreH18 : ((-10000) <= a_y_pre)) (PreH19 : (a_y_pre <= 10000)) (PreH20 : ((-10000) <= b_x_pre)) (PreH21 : (b_x_pre <= 10000)) (PreH22 : ((-10000) <= b_y_pre)) (PreH23 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1)) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre < b_y_pre)) (PreH2 : (a_x_pre <= b_x_pre)) (PreH3 : (a_x_pre >= b_x_pre)) (PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH9 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH11 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH12 : ((-10000) <= gx_pre)) (PreH13 : (gx_pre <= 10000)) (PreH14 : ((-10000) <= gy_pre)) (PreH15 : (gy_pre <= 10000)) (PreH16 : ((-10000) <= a_x_pre)) (PreH17 : (a_x_pre <= 10000)) (PreH18 : ((-10000) <= a_y_pre)) (PreH19 : (a_y_pre <= 10000)) (PreH20 : ((-10000) <= b_x_pre)) (PreH21 : (b_x_pre <= 10000)) (PreH22 : ((-10000) <= b_y_pre)) (PreH23 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1)) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_9_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre < b_y_pre)) (PreH2 : (a_x_pre <= b_x_pre)) (PreH3 : (a_x_pre >= b_x_pre)) (PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH9 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH11 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH12 : ((-10000) <= gx_pre)) (PreH13 : (gx_pre <= 10000)) (PreH14 : ((-10000) <= gy_pre)) (PreH15 : (gy_pre <= 10000)) (PreH16 : ((-10000) <= a_x_pre)) (PreH17 : (a_x_pre <= 10000)) (PreH18 : ((-10000) <= a_y_pre)) (PreH19 : (a_y_pre <= 10000)) (PreH20 : ((-10000) <= b_x_pre)) (PreH21 : (b_x_pre <= 10000)) (PreH22 : ((-10000) <= b_y_pre)) (PreH23 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1))

noncomputable def cmp_polar_values_return_wit_10 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre < b_y_pre)) (PreH2 : (a_x_pre <= b_x_pre)) (PreH3 : (a_x_pre >= b_x_pre)) (PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH9 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH11 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH12 : ((-10000) <= gx_pre)) (PreH13 : (gx_pre <= 10000)) (PreH14 : ((-10000) <= gy_pre)) (PreH15 : (gy_pre <= 10000)) (PreH16 : ((-10000) <= a_x_pre)) (PreH17 : (a_x_pre <= 10000)) (PreH18 : ((-10000) <= a_y_pre)) (PreH19 : (a_y_pre <= 10000)) (PreH20 : ((-10000) <= b_x_pre)) (PreH21 : (b_x_pre <= 10000)) (PreH22 : ((-10000) <= b_y_pre)) (PreH23 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1)) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre < b_y_pre)) (PreH2 : (a_x_pre <= b_x_pre)) (PreH3 : (a_x_pre >= b_x_pre)) (PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH9 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH11 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH12 : ((-10000) <= gx_pre)) (PreH13 : (gx_pre <= 10000)) (PreH14 : ((-10000) <= gy_pre)) (PreH15 : (gy_pre <= 10000)) (PreH16 : ((-10000) <= a_x_pre)) (PreH17 : (a_x_pre <= 10000)) (PreH18 : ((-10000) <= a_y_pre)) (PreH19 : (a_y_pre <= 10000)) (PreH20 : ((-10000) <= b_x_pre)) (PreH21 : (b_x_pre <= 10000)) (PreH22 : ((-10000) <= b_y_pre)) (PreH23 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1)) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_10_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_y_pre < b_y_pre)) (PreH2 : (a_x_pre <= b_x_pre)) (PreH3 : (a_x_pre >= b_x_pre)) (PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH5 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH7 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH9 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH11 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH12 : ((-10000) <= gx_pre)) (PreH13 : (gx_pre <= 10000)) (PreH14 : ((-10000) <= gy_pre)) (PreH15 : (gy_pre <= 10000)) (PreH16 : ((-10000) <= a_x_pre)) (PreH17 : (a_x_pre <= 10000)) (PreH18 : ((-10000) <= a_y_pre)) (PreH19 : (a_y_pre <= 10000)) (PreH20 : ((-10000) <= b_x_pre)) (PreH21 : (b_x_pre <= 10000)) (PreH22 : ((-10000) <= b_y_pre)) (PreH23 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1))

noncomputable def cmp_polar_values_return_wit_11 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre > b_x_pre)) (PreH2 : (a_x_pre >= b_x_pre)) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH7 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH8 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH9 : ((-10000) <= gx_pre)) (PreH10 : (gx_pre <= 10000)) (PreH11 : ((-10000) <= gy_pre)) (PreH12 : (gy_pre <= 10000)) (PreH13 : ((-10000) <= a_x_pre)) (PreH14 : (a_x_pre <= 10000)) (PreH15 : ((-10000) <= a_y_pre)) (PreH16 : (a_y_pre <= 10000)) (PreH17 : ((-10000) <= b_x_pre)) (PreH18 : (b_x_pre <= 10000)) (PreH19 : ((-10000) <= b_y_pre)) (PreH20 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre > b_x_pre)) (PreH2 : (a_x_pre >= b_x_pre)) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH7 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH8 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH9 : ((-10000) <= gx_pre)) (PreH10 : (gx_pre <= 10000)) (PreH11 : ((-10000) <= gy_pre)) (PreH12 : (gy_pre <= 10000)) (PreH13 : ((-10000) <= a_x_pre)) (PreH14 : (a_x_pre <= 10000)) (PreH15 : ((-10000) <= a_y_pre)) (PreH16 : (a_y_pre <= 10000)) (PreH17 : ((-10000) <= b_x_pre)) (PreH18 : (b_x_pre <= 10000)) (PreH19 : ((-10000) <= b_y_pre)) (PreH20 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_11_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre > b_x_pre)) (PreH2 : (a_x_pre >= b_x_pre)) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH7 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH8 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH9 : ((-10000) <= gx_pre)) (PreH10 : (gx_pre <= 10000)) (PreH11 : ((-10000) <= gy_pre)) (PreH12 : (gy_pre <= 10000)) (PreH13 : ((-10000) <= a_x_pre)) (PreH14 : (a_x_pre <= 10000)) (PreH15 : ((-10000) <= a_y_pre)) (PreH16 : (a_y_pre <= 10000)) (PreH17 : ((-10000) <= b_x_pre)) (PreH18 : (b_x_pre <= 10000)) (PreH19 : ((-10000) <= b_y_pre)) (PreH20 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1)

noncomputable def cmp_polar_values_return_wit_12 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre > b_x_pre)) (PreH2 : (a_x_pre >= b_x_pre)) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH7 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH8 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH9 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH11 : ((-10000) <= gx_pre)) (PreH12 : (gx_pre <= 10000)) (PreH13 : ((-10000) <= gy_pre)) (PreH14 : (gy_pre <= 10000)) (PreH15 : ((-10000) <= a_x_pre)) (PreH16 : (a_x_pre <= 10000)) (PreH17 : ((-10000) <= a_y_pre)) (PreH18 : (a_y_pre <= 10000)) (PreH19 : ((-10000) <= b_x_pre)) (PreH20 : (b_x_pre <= 10000)) (PreH21 : ((-10000) <= b_y_pre)) (PreH22 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre > b_x_pre)) (PreH2 : (a_x_pre >= b_x_pre)) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH7 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH8 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH9 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH11 : ((-10000) <= gx_pre)) (PreH12 : (gx_pre <= 10000)) (PreH13 : ((-10000) <= gy_pre)) (PreH14 : (gy_pre <= 10000)) (PreH15 : ((-10000) <= a_x_pre)) (PreH16 : (a_x_pre <= 10000)) (PreH17 : ((-10000) <= a_y_pre)) (PreH18 : (a_y_pre <= 10000)) (PreH19 : ((-10000) <= b_x_pre)) (PreH20 : (b_x_pre <= 10000)) (PreH21 : ((-10000) <= b_y_pre)) (PreH22 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_12_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre > b_x_pre)) (PreH2 : (a_x_pre >= b_x_pre)) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH7 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH8 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH9 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH11 : ((-10000) <= gx_pre)) (PreH12 : (gx_pre <= 10000)) (PreH13 : ((-10000) <= gy_pre)) (PreH14 : (gy_pre <= 10000)) (PreH15 : ((-10000) <= a_x_pre)) (PreH16 : (a_x_pre <= 10000)) (PreH17 : ((-10000) <= a_y_pre)) (PreH18 : (a_y_pre <= 10000)) (PreH19 : ((-10000) <= b_x_pre)) (PreH20 : (b_x_pre <= 10000)) (PreH21 : ((-10000) <= b_y_pre)) (PreH22 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1)

noncomputable def cmp_polar_values_return_wit_13 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre > b_x_pre)) (PreH2 : (a_x_pre >= b_x_pre)) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH7 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH9 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH11 : ((-10000) <= gx_pre)) (PreH12 : (gx_pre <= 10000)) (PreH13 : ((-10000) <= gy_pre)) (PreH14 : (gy_pre <= 10000)) (PreH15 : ((-10000) <= a_x_pre)) (PreH16 : (a_x_pre <= 10000)) (PreH17 : ((-10000) <= a_y_pre)) (PreH18 : (a_y_pre <= 10000)) (PreH19 : ((-10000) <= b_x_pre)) (PreH20 : (b_x_pre <= 10000)) (PreH21 : ((-10000) <= b_y_pre)) (PreH22 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre > b_x_pre)) (PreH2 : (a_x_pre >= b_x_pre)) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH7 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH9 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH11 : ((-10000) <= gx_pre)) (PreH12 : (gx_pre <= 10000)) (PreH13 : ((-10000) <= gy_pre)) (PreH14 : (gy_pre <= 10000)) (PreH15 : ((-10000) <= a_x_pre)) (PreH16 : (a_x_pre <= 10000)) (PreH17 : ((-10000) <= a_y_pre)) (PreH18 : (a_y_pre <= 10000)) (PreH19 : ((-10000) <= b_x_pre)) (PreH20 : (b_x_pre <= 10000)) (PreH21 : ((-10000) <= b_y_pre)) (PreH22 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_13_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre > b_x_pre)) (PreH2 : (a_x_pre >= b_x_pre)) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH7 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH9 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH11 : ((-10000) <= gx_pre)) (PreH12 : (gx_pre <= 10000)) (PreH13 : ((-10000) <= gy_pre)) (PreH14 : (gy_pre <= 10000)) (PreH15 : ((-10000) <= a_x_pre)) (PreH16 : (a_x_pre <= 10000)) (PreH17 : ((-10000) <= a_y_pre)) (PreH18 : (a_y_pre <= 10000)) (PreH19 : ((-10000) <= b_x_pre)) (PreH20 : (b_x_pre <= 10000)) (PreH21 : ((-10000) <= b_y_pre)) (PreH22 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1)

noncomputable def cmp_polar_values_return_wit_14 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre > b_x_pre)) (PreH2 : (a_x_pre >= b_x_pre)) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH7 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH9 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH10 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH11 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH12 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH13 : ((-10000) <= gx_pre)) (PreH14 : (gx_pre <= 10000)) (PreH15 : ((-10000) <= gy_pre)) (PreH16 : (gy_pre <= 10000)) (PreH17 : ((-10000) <= a_x_pre)) (PreH18 : (a_x_pre <= 10000)) (PreH19 : ((-10000) <= a_y_pre)) (PreH20 : (a_y_pre <= 10000)) (PreH21 : ((-10000) <= b_x_pre)) (PreH22 : (b_x_pre <= 10000)) (PreH23 : ((-10000) <= b_y_pre)) (PreH24 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre > b_x_pre)) (PreH2 : (a_x_pre >= b_x_pre)) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH7 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH9 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH10 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH11 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH12 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH13 : ((-10000) <= gx_pre)) (PreH14 : (gx_pre <= 10000)) (PreH15 : ((-10000) <= gy_pre)) (PreH16 : (gy_pre <= 10000)) (PreH17 : ((-10000) <= a_x_pre)) (PreH18 : (a_x_pre <= 10000)) (PreH19 : ((-10000) <= a_y_pre)) (PreH20 : (a_y_pre <= 10000)) (PreH21 : ((-10000) <= b_x_pre)) (PreH22 : (b_x_pre <= 10000)) (PreH23 : ((-10000) <= b_y_pre)) (PreH24 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_14_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre > b_x_pre)) (PreH2 : (a_x_pre >= b_x_pre)) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH7 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH9 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH10 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH11 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH12 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH13 : ((-10000) <= gx_pre)) (PreH14 : (gx_pre <= 10000)) (PreH15 : ((-10000) <= gy_pre)) (PreH16 : (gy_pre <= 10000)) (PreH17 : ((-10000) <= a_x_pre)) (PreH18 : (a_x_pre <= 10000)) (PreH19 : ((-10000) <= a_y_pre)) (PreH20 : (a_y_pre <= 10000)) (PreH21 : ((-10000) <= b_x_pre)) (PreH22 : (b_x_pre <= 10000)) (PreH23 : ((-10000) <= b_y_pre)) (PreH24 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1)

noncomputable def cmp_polar_values_return_wit_15 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre > b_x_pre)) (PreH2 : (a_x_pre >= b_x_pre)) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH7 : ((b_x_pre - gx_pre) < (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH9 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH10 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH11 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH12 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH13 : ((-10000) <= gx_pre)) (PreH14 : (gx_pre <= 10000)) (PreH15 : ((-10000) <= gy_pre)) (PreH16 : (gy_pre <= 10000)) (PreH17 : ((-10000) <= a_x_pre)) (PreH18 : (a_x_pre <= 10000)) (PreH19 : ((-10000) <= a_y_pre)) (PreH20 : (a_y_pre <= 10000)) (PreH21 : ((-10000) <= b_x_pre)) (PreH22 : (b_x_pre <= 10000)) (PreH23 : ((-10000) <= b_y_pre)) (PreH24 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre > b_x_pre)) (PreH2 : (a_x_pre >= b_x_pre)) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH7 : ((b_x_pre - gx_pre) < (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH9 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH10 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH11 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH12 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH13 : ((-10000) <= gx_pre)) (PreH14 : (gx_pre <= 10000)) (PreH15 : ((-10000) <= gy_pre)) (PreH16 : (gy_pre <= 10000)) (PreH17 : ((-10000) <= a_x_pre)) (PreH18 : (a_x_pre <= 10000)) (PreH19 : ((-10000) <= a_y_pre)) (PreH20 : (a_y_pre <= 10000)) (PreH21 : ((-10000) <= b_x_pre)) (PreH22 : (b_x_pre <= 10000)) (PreH23 : ((-10000) <= b_y_pre)) (PreH24 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_15_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre > b_x_pre)) (PreH2 : (a_x_pre >= b_x_pre)) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH7 : ((b_x_pre - gx_pre) < (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH9 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH10 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH11 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH12 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH13 : ((-10000) <= gx_pre)) (PreH14 : (gx_pre <= 10000)) (PreH15 : ((-10000) <= gy_pre)) (PreH16 : (gy_pre <= 10000)) (PreH17 : ((-10000) <= a_x_pre)) (PreH18 : (a_x_pre <= 10000)) (PreH19 : ((-10000) <= a_y_pre)) (PreH20 : (a_y_pre <= 10000)) (PreH21 : ((-10000) <= b_x_pre)) (PreH22 : (b_x_pre <= 10000)) (PreH23 : ((-10000) <= b_y_pre)) (PreH24 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1)

noncomputable def cmp_polar_values_return_wit_16 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre > b_x_pre)) (PreH2 : (a_x_pre >= b_x_pre)) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH7 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH9 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH11 : ((-10000) <= gx_pre)) (PreH12 : (gx_pre <= 10000)) (PreH13 : ((-10000) <= gy_pre)) (PreH14 : (gy_pre <= 10000)) (PreH15 : ((-10000) <= a_x_pre)) (PreH16 : (a_x_pre <= 10000)) (PreH17 : ((-10000) <= a_y_pre)) (PreH18 : (a_y_pre <= 10000)) (PreH19 : ((-10000) <= b_x_pre)) (PreH20 : (b_x_pre <= 10000)) (PreH21 : ((-10000) <= b_y_pre)) (PreH22 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre > b_x_pre)) (PreH2 : (a_x_pre >= b_x_pre)) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH7 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH9 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH11 : ((-10000) <= gx_pre)) (PreH12 : (gx_pre <= 10000)) (PreH13 : ((-10000) <= gy_pre)) (PreH14 : (gy_pre <= 10000)) (PreH15 : ((-10000) <= a_x_pre)) (PreH16 : (a_x_pre <= 10000)) (PreH17 : ((-10000) <= a_y_pre)) (PreH18 : (a_y_pre <= 10000)) (PreH19 : ((-10000) <= b_x_pre)) (PreH20 : (b_x_pre <= 10000)) (PreH21 : ((-10000) <= b_y_pre)) (PreH22 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_16_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre > b_x_pre)) (PreH2 : (a_x_pre >= b_x_pre)) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH6 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH7 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH9 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH11 : ((-10000) <= gx_pre)) (PreH12 : (gx_pre <= 10000)) (PreH13 : ((-10000) <= gy_pre)) (PreH14 : (gy_pre <= 10000)) (PreH15 : ((-10000) <= a_x_pre)) (PreH16 : (a_x_pre <= 10000)) (PreH17 : ((-10000) <= a_y_pre)) (PreH18 : (a_y_pre <= 10000)) (PreH19 : ((-10000) <= b_x_pre)) (PreH20 : (b_x_pre <= 10000)) (PreH21 : ((-10000) <= b_y_pre)) (PreH22 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1)

noncomputable def cmp_polar_values_return_wit_17 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre < b_x_pre)) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH6 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH7 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH8 : ((-10000) <= gx_pre)) (PreH9 : (gx_pre <= 10000)) (PreH10 : ((-10000) <= gy_pre)) (PreH11 : (gy_pre <= 10000)) (PreH12 : ((-10000) <= a_x_pre)) (PreH13 : (a_x_pre <= 10000)) (PreH14 : ((-10000) <= a_y_pre)) (PreH15 : (a_y_pre <= 10000)) (PreH16 : ((-10000) <= b_x_pre)) (PreH17 : (b_x_pre <= 10000)) (PreH18 : ((-10000) <= b_y_pre)) (PreH19 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1)) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre < b_x_pre)) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH6 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH7 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH8 : ((-10000) <= gx_pre)) (PreH9 : (gx_pre <= 10000)) (PreH10 : ((-10000) <= gy_pre)) (PreH11 : (gy_pre <= 10000)) (PreH12 : ((-10000) <= a_x_pre)) (PreH13 : (a_x_pre <= 10000)) (PreH14 : ((-10000) <= a_y_pre)) (PreH15 : (a_y_pre <= 10000)) (PreH16 : ((-10000) <= b_x_pre)) (PreH17 : (b_x_pre <= 10000)) (PreH18 : ((-10000) <= b_y_pre)) (PreH19 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1)) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_17_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre < b_x_pre)) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH6 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH7 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH8 : ((-10000) <= gx_pre)) (PreH9 : (gx_pre <= 10000)) (PreH10 : ((-10000) <= gy_pre)) (PreH11 : (gy_pre <= 10000)) (PreH12 : ((-10000) <= a_x_pre)) (PreH13 : (a_x_pre <= 10000)) (PreH14 : ((-10000) <= a_y_pre)) (PreH15 : (a_y_pre <= 10000)) (PreH16 : ((-10000) <= b_x_pre)) (PreH17 : (b_x_pre <= 10000)) (PreH18 : ((-10000) <= b_y_pre)) (PreH19 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1))

noncomputable def cmp_polar_values_return_wit_18 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre < b_x_pre)) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH6 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH7 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH8 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH9 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH10 : ((-10000) <= gx_pre)) (PreH11 : (gx_pre <= 10000)) (PreH12 : ((-10000) <= gy_pre)) (PreH13 : (gy_pre <= 10000)) (PreH14 : ((-10000) <= a_x_pre)) (PreH15 : (a_x_pre <= 10000)) (PreH16 : ((-10000) <= a_y_pre)) (PreH17 : (a_y_pre <= 10000)) (PreH18 : ((-10000) <= b_x_pre)) (PreH19 : (b_x_pre <= 10000)) (PreH20 : ((-10000) <= b_y_pre)) (PreH21 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1)) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre < b_x_pre)) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH6 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH7 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH8 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH9 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH10 : ((-10000) <= gx_pre)) (PreH11 : (gx_pre <= 10000)) (PreH12 : ((-10000) <= gy_pre)) (PreH13 : (gy_pre <= 10000)) (PreH14 : ((-10000) <= a_x_pre)) (PreH15 : (a_x_pre <= 10000)) (PreH16 : ((-10000) <= a_y_pre)) (PreH17 : (a_y_pre <= 10000)) (PreH18 : ((-10000) <= b_x_pre)) (PreH19 : (b_x_pre <= 10000)) (PreH20 : ((-10000) <= b_y_pre)) (PreH21 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1)) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_18_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre < b_x_pre)) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH6 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH7 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH8 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH9 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH10 : ((-10000) <= gx_pre)) (PreH11 : (gx_pre <= 10000)) (PreH12 : ((-10000) <= gy_pre)) (PreH13 : (gy_pre <= 10000)) (PreH14 : ((-10000) <= a_x_pre)) (PreH15 : (a_x_pre <= 10000)) (PreH16 : ((-10000) <= a_y_pre)) (PreH17 : (a_y_pre <= 10000)) (PreH18 : ((-10000) <= b_x_pre)) (PreH19 : (b_x_pre <= 10000)) (PreH20 : ((-10000) <= b_y_pre)) (PreH21 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1))

noncomputable def cmp_polar_values_return_wit_19 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre < b_x_pre)) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH6 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH7 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH9 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH10 : ((-10000) <= gx_pre)) (PreH11 : (gx_pre <= 10000)) (PreH12 : ((-10000) <= gy_pre)) (PreH13 : (gy_pre <= 10000)) (PreH14 : ((-10000) <= a_x_pre)) (PreH15 : (a_x_pre <= 10000)) (PreH16 : ((-10000) <= a_y_pre)) (PreH17 : (a_y_pre <= 10000)) (PreH18 : ((-10000) <= b_x_pre)) (PreH19 : (b_x_pre <= 10000)) (PreH20 : ((-10000) <= b_y_pre)) (PreH21 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1)) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre < b_x_pre)) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH6 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH7 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH9 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH10 : ((-10000) <= gx_pre)) (PreH11 : (gx_pre <= 10000)) (PreH12 : ((-10000) <= gy_pre)) (PreH13 : (gy_pre <= 10000)) (PreH14 : ((-10000) <= a_x_pre)) (PreH15 : (a_x_pre <= 10000)) (PreH16 : ((-10000) <= a_y_pre)) (PreH17 : (a_y_pre <= 10000)) (PreH18 : ((-10000) <= b_x_pre)) (PreH19 : (b_x_pre <= 10000)) (PreH20 : ((-10000) <= b_y_pre)) (PreH21 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1)) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_19_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre < b_x_pre)) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH6 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH7 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH9 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH10 : ((-10000) <= gx_pre)) (PreH11 : (gx_pre <= 10000)) (PreH12 : ((-10000) <= gy_pre)) (PreH13 : (gy_pre <= 10000)) (PreH14 : ((-10000) <= a_x_pre)) (PreH15 : (a_x_pre <= 10000)) (PreH16 : ((-10000) <= a_y_pre)) (PreH17 : (a_y_pre <= 10000)) (PreH18 : ((-10000) <= b_x_pre)) (PreH19 : (b_x_pre <= 10000)) (PreH20 : ((-10000) <= b_y_pre)) (PreH21 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1))

noncomputable def cmp_polar_values_return_wit_20 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre < b_x_pre)) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH6 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH7 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH9 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH11 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH12 : ((-10000) <= gx_pre)) (PreH13 : (gx_pre <= 10000)) (PreH14 : ((-10000) <= gy_pre)) (PreH15 : (gy_pre <= 10000)) (PreH16 : ((-10000) <= a_x_pre)) (PreH17 : (a_x_pre <= 10000)) (PreH18 : ((-10000) <= a_y_pre)) (PreH19 : (a_y_pre <= 10000)) (PreH20 : ((-10000) <= b_x_pre)) (PreH21 : (b_x_pre <= 10000)) (PreH22 : ((-10000) <= b_y_pre)) (PreH23 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1)) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre < b_x_pre)) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH6 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH7 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH9 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH11 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH12 : ((-10000) <= gx_pre)) (PreH13 : (gx_pre <= 10000)) (PreH14 : ((-10000) <= gy_pre)) (PreH15 : (gy_pre <= 10000)) (PreH16 : ((-10000) <= a_x_pre)) (PreH17 : (a_x_pre <= 10000)) (PreH18 : ((-10000) <= a_y_pre)) (PreH19 : (a_y_pre <= 10000)) (PreH20 : ((-10000) <= b_x_pre)) (PreH21 : (b_x_pre <= 10000)) (PreH22 : ((-10000) <= b_y_pre)) (PreH23 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1)) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_20_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre < b_x_pre)) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH6 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH7 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH9 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH11 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH12 : ((-10000) <= gx_pre)) (PreH13 : (gx_pre <= 10000)) (PreH14 : ((-10000) <= gy_pre)) (PreH15 : (gy_pre <= 10000)) (PreH16 : ((-10000) <= a_x_pre)) (PreH17 : (a_x_pre <= 10000)) (PreH18 : ((-10000) <= a_y_pre)) (PreH19 : (a_y_pre <= 10000)) (PreH20 : ((-10000) <= b_x_pre)) (PreH21 : (b_x_pre <= 10000)) (PreH22 : ((-10000) <= b_y_pre)) (PreH23 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1))

noncomputable def cmp_polar_values_return_wit_21 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre < b_x_pre)) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH6 : ((b_x_pre - gx_pre) < (0 : Int))) (PreH7 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH9 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH11 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH12 : ((-10000) <= gx_pre)) (PreH13 : (gx_pre <= 10000)) (PreH14 : ((-10000) <= gy_pre)) (PreH15 : (gy_pre <= 10000)) (PreH16 : ((-10000) <= a_x_pre)) (PreH17 : (a_x_pre <= 10000)) (PreH18 : ((-10000) <= a_y_pre)) (PreH19 : (a_y_pre <= 10000)) (PreH20 : ((-10000) <= b_x_pre)) (PreH21 : (b_x_pre <= 10000)) (PreH22 : ((-10000) <= b_y_pre)) (PreH23 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1)) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre < b_x_pre)) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH6 : ((b_x_pre - gx_pre) < (0 : Int))) (PreH7 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH9 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH11 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH12 : ((-10000) <= gx_pre)) (PreH13 : (gx_pre <= 10000)) (PreH14 : ((-10000) <= gy_pre)) (PreH15 : (gy_pre <= 10000)) (PreH16 : ((-10000) <= a_x_pre)) (PreH17 : (a_x_pre <= 10000)) (PreH18 : ((-10000) <= a_y_pre)) (PreH19 : (a_y_pre <= 10000)) (PreH20 : ((-10000) <= b_x_pre)) (PreH21 : (b_x_pre <= 10000)) (PreH22 : ((-10000) <= b_y_pre)) (PreH23 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1)) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_21_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre < b_x_pre)) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH6 : ((b_x_pre - gx_pre) < (0 : Int))) (PreH7 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH8 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH9 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH11 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH12 : ((-10000) <= gx_pre)) (PreH13 : (gx_pre <= 10000)) (PreH14 : ((-10000) <= gy_pre)) (PreH15 : (gy_pre <= 10000)) (PreH16 : ((-10000) <= a_x_pre)) (PreH17 : (a_x_pre <= 10000)) (PreH18 : ((-10000) <= a_y_pre)) (PreH19 : (a_y_pre <= 10000)) (PreH20 : ((-10000) <= b_x_pre)) (PreH21 : (b_x_pre <= 10000)) (PreH22 : ((-10000) <= b_y_pre)) (PreH23 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1))

noncomputable def cmp_polar_values_return_wit_22 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre < b_x_pre)) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH6 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH7 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH8 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH9 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH10 : ((-10000) <= gx_pre)) (PreH11 : (gx_pre <= 10000)) (PreH12 : ((-10000) <= gy_pre)) (PreH13 : (gy_pre <= 10000)) (PreH14 : ((-10000) <= a_x_pre)) (PreH15 : (a_x_pre <= 10000)) (PreH16 : ((-10000) <= a_y_pre)) (PreH17 : (a_y_pre <= 10000)) (PreH18 : ((-10000) <= b_x_pre)) (PreH19 : (b_x_pre <= 10000)) (PreH20 : ((-10000) <= b_y_pre)) (PreH21 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1)) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre < b_x_pre)) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH6 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH7 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH8 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH9 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH10 : ((-10000) <= gx_pre)) (PreH11 : (gx_pre <= 10000)) (PreH12 : ((-10000) <= gy_pre)) (PreH13 : (gy_pre <= 10000)) (PreH14 : ((-10000) <= a_x_pre)) (PreH15 : (a_x_pre <= 10000)) (PreH16 : ((-10000) <= a_y_pre)) (PreH17 : (a_y_pre <= 10000)) (PreH18 : ((-10000) <= b_x_pre)) (PreH19 : (b_x_pre <= 10000)) (PreH20 : ((-10000) <= b_y_pre)) (PreH21 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1)) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_22_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : (a_x_pre < b_x_pre)) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) <= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH5 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH6 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH7 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH8 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH9 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH10 : ((-10000) <= gx_pre)) (PreH11 : (gx_pre <= 10000)) (PreH12 : ((-10000) <= gy_pre)) (PreH13 : (gy_pre <= 10000)) (PreH14 : ((-10000) <= a_x_pre)) (PreH15 : (a_x_pre <= 10000)) (PreH16 : ((-10000) <= a_y_pre)) (PreH17 : (a_y_pre <= 10000)) (PreH18 : ((-10000) <= b_x_pre)) (PreH19 : (b_x_pre <= 10000)) (PreH20 : ((-10000) <= b_y_pre)) (PreH21 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1))

noncomputable def cmp_polar_values_return_wit_23 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) > (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH5 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH7 : ((-10000) <= gx_pre)) (PreH8 : (gx_pre <= 10000)) (PreH9 : ((-10000) <= gy_pre)) (PreH10 : (gy_pre <= 10000)) (PreH11 : ((-10000) <= a_x_pre)) (PreH12 : (a_x_pre <= 10000)) (PreH13 : ((-10000) <= a_y_pre)) (PreH14 : (a_y_pre <= 10000)) (PreH15 : ((-10000) <= b_x_pre)) (PreH16 : (b_x_pre <= 10000)) (PreH17 : ((-10000) <= b_y_pre)) (PreH18 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) > (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH5 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH7 : ((-10000) <= gx_pre)) (PreH8 : (gx_pre <= 10000)) (PreH9 : ((-10000) <= gy_pre)) (PreH10 : (gy_pre <= 10000)) (PreH11 : ((-10000) <= a_x_pre)) (PreH12 : (a_x_pre <= 10000)) (PreH13 : ((-10000) <= a_y_pre)) (PreH14 : (a_y_pre <= 10000)) (PreH15 : ((-10000) <= b_x_pre)) (PreH16 : (b_x_pre <= 10000)) (PreH17 : ((-10000) <= b_y_pre)) (PreH18 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_23_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) > (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH5 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH7 : ((-10000) <= gx_pre)) (PreH8 : (gx_pre <= 10000)) (PreH9 : ((-10000) <= gy_pre)) (PreH10 : (gy_pre <= 10000)) (PreH11 : ((-10000) <= a_x_pre)) (PreH12 : (a_x_pre <= 10000)) (PreH13 : ((-10000) <= a_y_pre)) (PreH14 : (a_y_pre <= 10000)) (PreH15 : ((-10000) <= b_x_pre)) (PreH16 : (b_x_pre <= 10000)) (PreH17 : ((-10000) <= b_y_pre)) (PreH18 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1)

noncomputable def cmp_polar_values_return_wit_24 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) > (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH5 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH6 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH7 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH8 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH9 : ((-10000) <= gx_pre)) (PreH10 : (gx_pre <= 10000)) (PreH11 : ((-10000) <= gy_pre)) (PreH12 : (gy_pre <= 10000)) (PreH13 : ((-10000) <= a_x_pre)) (PreH14 : (a_x_pre <= 10000)) (PreH15 : ((-10000) <= a_y_pre)) (PreH16 : (a_y_pre <= 10000)) (PreH17 : ((-10000) <= b_x_pre)) (PreH18 : (b_x_pre <= 10000)) (PreH19 : ((-10000) <= b_y_pre)) (PreH20 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) > (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH5 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH6 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH7 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH8 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH9 : ((-10000) <= gx_pre)) (PreH10 : (gx_pre <= 10000)) (PreH11 : ((-10000) <= gy_pre)) (PreH12 : (gy_pre <= 10000)) (PreH13 : ((-10000) <= a_x_pre)) (PreH14 : (a_x_pre <= 10000)) (PreH15 : ((-10000) <= a_y_pre)) (PreH16 : (a_y_pre <= 10000)) (PreH17 : ((-10000) <= b_x_pre)) (PreH18 : (b_x_pre <= 10000)) (PreH19 : ((-10000) <= b_y_pre)) (PreH20 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_24_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) > (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH5 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH6 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH7 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH8 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH9 : ((-10000) <= gx_pre)) (PreH10 : (gx_pre <= 10000)) (PreH11 : ((-10000) <= gy_pre)) (PreH12 : (gy_pre <= 10000)) (PreH13 : ((-10000) <= a_x_pre)) (PreH14 : (a_x_pre <= 10000)) (PreH15 : ((-10000) <= a_y_pre)) (PreH16 : (a_y_pre <= 10000)) (PreH17 : ((-10000) <= b_x_pre)) (PreH18 : (b_x_pre <= 10000)) (PreH19 : ((-10000) <= b_y_pre)) (PreH20 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1)

noncomputable def cmp_polar_values_return_wit_25 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) > (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH5 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH6 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH7 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH8 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH9 : ((-10000) <= gx_pre)) (PreH10 : (gx_pre <= 10000)) (PreH11 : ((-10000) <= gy_pre)) (PreH12 : (gy_pre <= 10000)) (PreH13 : ((-10000) <= a_x_pre)) (PreH14 : (a_x_pre <= 10000)) (PreH15 : ((-10000) <= a_y_pre)) (PreH16 : (a_y_pre <= 10000)) (PreH17 : ((-10000) <= b_x_pre)) (PreH18 : (b_x_pre <= 10000)) (PreH19 : ((-10000) <= b_y_pre)) (PreH20 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) > (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH5 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH6 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH7 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH8 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH9 : ((-10000) <= gx_pre)) (PreH10 : (gx_pre <= 10000)) (PreH11 : ((-10000) <= gy_pre)) (PreH12 : (gy_pre <= 10000)) (PreH13 : ((-10000) <= a_x_pre)) (PreH14 : (a_x_pre <= 10000)) (PreH15 : ((-10000) <= a_y_pre)) (PreH16 : (a_y_pre <= 10000)) (PreH17 : ((-10000) <= b_x_pre)) (PreH18 : (b_x_pre <= 10000)) (PreH19 : ((-10000) <= b_y_pre)) (PreH20 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_25_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) > (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH5 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH6 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH7 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH8 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH9 : ((-10000) <= gx_pre)) (PreH10 : (gx_pre <= 10000)) (PreH11 : ((-10000) <= gy_pre)) (PreH12 : (gy_pre <= 10000)) (PreH13 : ((-10000) <= a_x_pre)) (PreH14 : (a_x_pre <= 10000)) (PreH15 : ((-10000) <= a_y_pre)) (PreH16 : (a_y_pre <= 10000)) (PreH17 : ((-10000) <= b_x_pre)) (PreH18 : (b_x_pre <= 10000)) (PreH19 : ((-10000) <= b_y_pre)) (PreH20 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1)

noncomputable def cmp_polar_values_return_wit_26 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) > (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH5 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH6 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH7 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH8 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH9 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH11 : ((-10000) <= gx_pre)) (PreH12 : (gx_pre <= 10000)) (PreH13 : ((-10000) <= gy_pre)) (PreH14 : (gy_pre <= 10000)) (PreH15 : ((-10000) <= a_x_pre)) (PreH16 : (a_x_pre <= 10000)) (PreH17 : ((-10000) <= a_y_pre)) (PreH18 : (a_y_pre <= 10000)) (PreH19 : ((-10000) <= b_x_pre)) (PreH20 : (b_x_pre <= 10000)) (PreH21 : ((-10000) <= b_y_pre)) (PreH22 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) > (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH5 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH6 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH7 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH8 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH9 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH11 : ((-10000) <= gx_pre)) (PreH12 : (gx_pre <= 10000)) (PreH13 : ((-10000) <= gy_pre)) (PreH14 : (gy_pre <= 10000)) (PreH15 : ((-10000) <= a_x_pre)) (PreH16 : (a_x_pre <= 10000)) (PreH17 : ((-10000) <= a_y_pre)) (PreH18 : (a_y_pre <= 10000)) (PreH19 : ((-10000) <= b_x_pre)) (PreH20 : (b_x_pre <= 10000)) (PreH21 : ((-10000) <= b_y_pre)) (PreH22 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_26_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) > (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH5 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH6 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH7 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH8 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH9 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH11 : ((-10000) <= gx_pre)) (PreH12 : (gx_pre <= 10000)) (PreH13 : ((-10000) <= gy_pre)) (PreH14 : (gy_pre <= 10000)) (PreH15 : ((-10000) <= a_x_pre)) (PreH16 : (a_x_pre <= 10000)) (PreH17 : ((-10000) <= a_y_pre)) (PreH18 : (a_y_pre <= 10000)) (PreH19 : ((-10000) <= b_x_pre)) (PreH20 : (b_x_pre <= 10000)) (PreH21 : ((-10000) <= b_y_pre)) (PreH22 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1)

noncomputable def cmp_polar_values_return_wit_27 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) > (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH5 : ((b_x_pre - gx_pre) < (0 : Int))) (PreH6 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH7 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH8 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH9 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH11 : ((-10000) <= gx_pre)) (PreH12 : (gx_pre <= 10000)) (PreH13 : ((-10000) <= gy_pre)) (PreH14 : (gy_pre <= 10000)) (PreH15 : ((-10000) <= a_x_pre)) (PreH16 : (a_x_pre <= 10000)) (PreH17 : ((-10000) <= a_y_pre)) (PreH18 : (a_y_pre <= 10000)) (PreH19 : ((-10000) <= b_x_pre)) (PreH20 : (b_x_pre <= 10000)) (PreH21 : ((-10000) <= b_y_pre)) (PreH22 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) > (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH5 : ((b_x_pre - gx_pre) < (0 : Int))) (PreH6 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH7 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH8 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH9 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH11 : ((-10000) <= gx_pre)) (PreH12 : (gx_pre <= 10000)) (PreH13 : ((-10000) <= gy_pre)) (PreH14 : (gy_pre <= 10000)) (PreH15 : ((-10000) <= a_x_pre)) (PreH16 : (a_x_pre <= 10000)) (PreH17 : ((-10000) <= a_y_pre)) (PreH18 : (a_y_pre <= 10000)) (PreH19 : ((-10000) <= b_x_pre)) (PreH20 : (b_x_pre <= 10000)) (PreH21 : ((-10000) <= b_y_pre)) (PreH22 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_27_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) > (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH5 : ((b_x_pre - gx_pre) < (0 : Int))) (PreH6 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH7 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH8 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH9 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH10 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH11 : ((-10000) <= gx_pre)) (PreH12 : (gx_pre <= 10000)) (PreH13 : ((-10000) <= gy_pre)) (PreH14 : (gy_pre <= 10000)) (PreH15 : ((-10000) <= a_x_pre)) (PreH16 : (a_x_pre <= 10000)) (PreH17 : ((-10000) <= a_y_pre)) (PreH18 : (a_y_pre <= 10000)) (PreH19 : ((-10000) <= b_x_pre)) (PreH20 : (b_x_pre <= 10000)) (PreH21 : ((-10000) <= b_y_pre)) (PreH22 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1)

noncomputable def cmp_polar_values_return_wit_28 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) > (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH5 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH6 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH7 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH8 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH9 : ((-10000) <= gx_pre)) (PreH10 : (gx_pre <= 10000)) (PreH11 : ((-10000) <= gy_pre)) (PreH12 : (gy_pre <= 10000)) (PreH13 : ((-10000) <= a_x_pre)) (PreH14 : (a_x_pre <= 10000)) (PreH15 : ((-10000) <= a_y_pre)) (PreH16 : (a_y_pre <= 10000)) (PreH17 : ((-10000) <= b_x_pre)) (PreH18 : (b_x_pre <= 10000)) (PreH19 : ((-10000) <= b_y_pre)) (PreH20 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) > (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH5 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH6 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH7 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH8 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH9 : ((-10000) <= gx_pre)) (PreH10 : (gx_pre <= 10000)) (PreH11 : ((-10000) <= gy_pre)) (PreH12 : (gy_pre <= 10000)) (PreH13 : ((-10000) <= a_x_pre)) (PreH14 : (a_x_pre <= 10000)) (PreH15 : ((-10000) <= a_y_pre)) (PreH16 : (a_y_pre <= 10000)) (PreH17 : ((-10000) <= b_x_pre)) (PreH18 : (b_x_pre <= 10000)) (PreH19 : ((-10000) <= b_y_pre)) (PreH20 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_28_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) > (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) >= (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH4 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH5 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH6 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH7 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH8 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH9 : ((-10000) <= gx_pre)) (PreH10 : (gx_pre <= 10000)) (PreH11 : ((-10000) <= gy_pre)) (PreH12 : (gy_pre <= 10000)) (PreH13 : ((-10000) <= a_x_pre)) (PreH14 : (a_x_pre <= 10000)) (PreH15 : ((-10000) <= a_y_pre)) (PreH16 : (a_y_pre <= 10000)) (PreH17 : ((-10000) <= b_x_pre)) (PreH18 : (b_x_pre <= 10000)) (PreH19 : ((-10000) <= b_y_pre)) (PreH20 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1)

noncomputable def cmp_polar_values_return_wit_29 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) < (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH4 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH6 : ((-10000) <= gx_pre)) (PreH7 : (gx_pre <= 10000)) (PreH8 : ((-10000) <= gy_pre)) (PreH9 : (gy_pre <= 10000)) (PreH10 : ((-10000) <= a_x_pre)) (PreH11 : (a_x_pre <= 10000)) (PreH12 : ((-10000) <= a_y_pre)) (PreH13 : (a_y_pre <= 10000)) (PreH14 : ((-10000) <= b_x_pre)) (PreH15 : (b_x_pre <= 10000)) (PreH16 : ((-10000) <= b_y_pre)) (PreH17 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1)) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) < (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH4 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH6 : ((-10000) <= gx_pre)) (PreH7 : (gx_pre <= 10000)) (PreH8 : ((-10000) <= gy_pre)) (PreH9 : (gy_pre <= 10000)) (PreH10 : ((-10000) <= a_x_pre)) (PreH11 : (a_x_pre <= 10000)) (PreH12 : ((-10000) <= a_y_pre)) (PreH13 : (a_y_pre <= 10000)) (PreH14 : ((-10000) <= b_x_pre)) (PreH15 : (b_x_pre <= 10000)) (PreH16 : ((-10000) <= b_y_pre)) (PreH17 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1)) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_29_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) < (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH4 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH6 : ((-10000) <= gx_pre)) (PreH7 : (gx_pre <= 10000)) (PreH8 : ((-10000) <= gy_pre)) (PreH9 : (gy_pre <= 10000)) (PreH10 : ((-10000) <= a_x_pre)) (PreH11 : (a_x_pre <= 10000)) (PreH12 : ((-10000) <= a_y_pre)) (PreH13 : (a_y_pre <= 10000)) (PreH14 : ((-10000) <= b_x_pre)) (PreH15 : (b_x_pre <= 10000)) (PreH16 : ((-10000) <= b_y_pre)) (PreH17 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1))

noncomputable def cmp_polar_values_return_wit_30 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) < (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH4 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH5 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH7 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH8 : ((-10000) <= gx_pre)) (PreH9 : (gx_pre <= 10000)) (PreH10 : ((-10000) <= gy_pre)) (PreH11 : (gy_pre <= 10000)) (PreH12 : ((-10000) <= a_x_pre)) (PreH13 : (a_x_pre <= 10000)) (PreH14 : ((-10000) <= a_y_pre)) (PreH15 : (a_y_pre <= 10000)) (PreH16 : ((-10000) <= b_x_pre)) (PreH17 : (b_x_pre <= 10000)) (PreH18 : ((-10000) <= b_y_pre)) (PreH19 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1)) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) < (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH4 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH5 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH7 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH8 : ((-10000) <= gx_pre)) (PreH9 : (gx_pre <= 10000)) (PreH10 : ((-10000) <= gy_pre)) (PreH11 : (gy_pre <= 10000)) (PreH12 : ((-10000) <= a_x_pre)) (PreH13 : (a_x_pre <= 10000)) (PreH14 : ((-10000) <= a_y_pre)) (PreH15 : (a_y_pre <= 10000)) (PreH16 : ((-10000) <= b_x_pre)) (PreH17 : (b_x_pre <= 10000)) (PreH18 : ((-10000) <= b_y_pre)) (PreH19 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1)) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_30_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) < (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH4 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH5 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH7 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH8 : ((-10000) <= gx_pre)) (PreH9 : (gx_pre <= 10000)) (PreH10 : ((-10000) <= gy_pre)) (PreH11 : (gy_pre <= 10000)) (PreH12 : ((-10000) <= a_x_pre)) (PreH13 : (a_x_pre <= 10000)) (PreH14 : ((-10000) <= a_y_pre)) (PreH15 : (a_y_pre <= 10000)) (PreH16 : ((-10000) <= b_x_pre)) (PreH17 : (b_x_pre <= 10000)) (PreH18 : ((-10000) <= b_y_pre)) (PreH19 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1))

noncomputable def cmp_polar_values_return_wit_31 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) < (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH4 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH5 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH6 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH7 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH8 : ((-10000) <= gx_pre)) (PreH9 : (gx_pre <= 10000)) (PreH10 : ((-10000) <= gy_pre)) (PreH11 : (gy_pre <= 10000)) (PreH12 : ((-10000) <= a_x_pre)) (PreH13 : (a_x_pre <= 10000)) (PreH14 : ((-10000) <= a_y_pre)) (PreH15 : (a_y_pre <= 10000)) (PreH16 : ((-10000) <= b_x_pre)) (PreH17 : (b_x_pre <= 10000)) (PreH18 : ((-10000) <= b_y_pre)) (PreH19 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1)) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) < (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH4 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH5 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH6 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH7 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH8 : ((-10000) <= gx_pre)) (PreH9 : (gx_pre <= 10000)) (PreH10 : ((-10000) <= gy_pre)) (PreH11 : (gy_pre <= 10000)) (PreH12 : ((-10000) <= a_x_pre)) (PreH13 : (a_x_pre <= 10000)) (PreH14 : ((-10000) <= a_y_pre)) (PreH15 : (a_y_pre <= 10000)) (PreH16 : ((-10000) <= b_x_pre)) (PreH17 : (b_x_pre <= 10000)) (PreH18 : ((-10000) <= b_y_pre)) (PreH19 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1)) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_31_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) < (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH4 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH5 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH6 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH7 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH8 : ((-10000) <= gx_pre)) (PreH9 : (gx_pre <= 10000)) (PreH10 : ((-10000) <= gy_pre)) (PreH11 : (gy_pre <= 10000)) (PreH12 : ((-10000) <= a_x_pre)) (PreH13 : (a_x_pre <= 10000)) (PreH14 : ((-10000) <= a_y_pre)) (PreH15 : (a_y_pre <= 10000)) (PreH16 : ((-10000) <= b_x_pre)) (PreH17 : (b_x_pre <= 10000)) (PreH18 : ((-10000) <= b_y_pre)) (PreH19 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1))

noncomputable def cmp_polar_values_return_wit_32 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) < (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH4 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH5 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH6 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH7 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH8 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH9 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH10 : ((-10000) <= gx_pre)) (PreH11 : (gx_pre <= 10000)) (PreH12 : ((-10000) <= gy_pre)) (PreH13 : (gy_pre <= 10000)) (PreH14 : ((-10000) <= a_x_pre)) (PreH15 : (a_x_pre <= 10000)) (PreH16 : ((-10000) <= a_y_pre)) (PreH17 : (a_y_pre <= 10000)) (PreH18 : ((-10000) <= b_x_pre)) (PreH19 : (b_x_pre <= 10000)) (PreH20 : ((-10000) <= b_y_pre)) (PreH21 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1)) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) < (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH4 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH5 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH6 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH7 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH8 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH9 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH10 : ((-10000) <= gx_pre)) (PreH11 : (gx_pre <= 10000)) (PreH12 : ((-10000) <= gy_pre)) (PreH13 : (gy_pre <= 10000)) (PreH14 : ((-10000) <= a_x_pre)) (PreH15 : (a_x_pre <= 10000)) (PreH16 : ((-10000) <= a_y_pre)) (PreH17 : (a_y_pre <= 10000)) (PreH18 : ((-10000) <= b_x_pre)) (PreH19 : (b_x_pre <= 10000)) (PreH20 : ((-10000) <= b_y_pre)) (PreH21 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1)) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_32_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) < (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH4 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH5 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH6 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH7 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH8 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH9 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH10 : ((-10000) <= gx_pre)) (PreH11 : (gx_pre <= 10000)) (PreH12 : ((-10000) <= gy_pre)) (PreH13 : (gy_pre <= 10000)) (PreH14 : ((-10000) <= a_x_pre)) (PreH15 : (a_x_pre <= 10000)) (PreH16 : ((-10000) <= a_y_pre)) (PreH17 : (a_y_pre <= 10000)) (PreH18 : ((-10000) <= b_x_pre)) (PreH19 : (b_x_pre <= 10000)) (PreH20 : ((-10000) <= b_y_pre)) (PreH21 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1))

noncomputable def cmp_polar_values_return_wit_33 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) < (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH4 : ((b_x_pre - gx_pre) < (0 : Int))) (PreH5 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH6 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH7 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH8 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH9 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH10 : ((-10000) <= gx_pre)) (PreH11 : (gx_pre <= 10000)) (PreH12 : ((-10000) <= gy_pre)) (PreH13 : (gy_pre <= 10000)) (PreH14 : ((-10000) <= a_x_pre)) (PreH15 : (a_x_pre <= 10000)) (PreH16 : ((-10000) <= a_y_pre)) (PreH17 : (a_y_pre <= 10000)) (PreH18 : ((-10000) <= b_x_pre)) (PreH19 : (b_x_pre <= 10000)) (PreH20 : ((-10000) <= b_y_pre)) (PreH21 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1)) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) < (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH4 : ((b_x_pre - gx_pre) < (0 : Int))) (PreH5 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH6 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH7 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH8 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH9 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH10 : ((-10000) <= gx_pre)) (PreH11 : (gx_pre <= 10000)) (PreH12 : ((-10000) <= gy_pre)) (PreH13 : (gy_pre <= 10000)) (PreH14 : ((-10000) <= a_x_pre)) (PreH15 : (a_x_pre <= 10000)) (PreH16 : ((-10000) <= a_y_pre)) (PreH17 : (a_y_pre <= 10000)) (PreH18 : ((-10000) <= b_x_pre)) (PreH19 : (b_x_pre <= 10000)) (PreH20 : ((-10000) <= b_y_pre)) (PreH21 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1)) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_33_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) < (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH4 : ((b_x_pre - gx_pre) < (0 : Int))) (PreH5 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH6 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH7 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH8 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH9 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH10 : ((-10000) <= gx_pre)) (PreH11 : (gx_pre <= 10000)) (PreH12 : ((-10000) <= gy_pre)) (PreH13 : (gy_pre <= 10000)) (PreH14 : ((-10000) <= a_x_pre)) (PreH15 : (a_x_pre <= 10000)) (PreH16 : ((-10000) <= a_y_pre)) (PreH17 : (a_y_pre <= 10000)) (PreH18 : ((-10000) <= b_x_pre)) (PreH19 : (b_x_pre <= 10000)) (PreH20 : ((-10000) <= b_y_pre)) (PreH21 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1))

noncomputable def cmp_polar_values_return_wit_34 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) < (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH4 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH5 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH7 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH8 : ((-10000) <= gx_pre)) (PreH9 : (gx_pre <= 10000)) (PreH10 : ((-10000) <= gy_pre)) (PreH11 : (gy_pre <= 10000)) (PreH12 : ((-10000) <= a_x_pre)) (PreH13 : (a_x_pre <= 10000)) (PreH14 : ((-10000) <= a_y_pre)) (PreH15 : (a_y_pre <= 10000)) (PreH16 : ((-10000) <= b_x_pre)) (PreH17 : (b_x_pre <= 10000)) (PreH18 : ((-10000) <= b_y_pre)) (PreH19 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1)) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) < (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH4 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH5 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH7 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH8 : ((-10000) <= gx_pre)) (PreH9 : (gx_pre <= 10000)) (PreH10 : ((-10000) <= gy_pre)) (PreH11 : (gy_pre <= 10000)) (PreH12 : ((-10000) <= a_x_pre)) (PreH13 : (a_x_pre <= 10000)) (PreH14 : ((-10000) <= a_y_pre)) (PreH15 : (a_y_pre <= 10000)) (PreH16 : ((-10000) <= b_x_pre)) (PreH17 : (b_x_pre <= 10000)) (PreH18 : ((-10000) <= b_y_pre)) (PreH19 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1)) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_34_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (a_x_pre - gx_pre)) + ((a_y_pre - gy_pre) * (a_y_pre - gy_pre))) < (((b_x_pre - gx_pre) * (b_x_pre - gx_pre)) + ((b_y_pre - gy_pre) * (b_y_pre - gy_pre))))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) >= (0 : Int))) (PreH3 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH4 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH5 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH7 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH8 : ((-10000) <= gx_pre)) (PreH9 : (gx_pre <= 10000)) (PreH10 : ((-10000) <= gy_pre)) (PreH11 : (gy_pre <= 10000)) (PreH12 : ((-10000) <= a_x_pre)) (PreH13 : (a_x_pre <= 10000)) (PreH14 : ((-10000) <= a_y_pre)) (PreH15 : (a_y_pre <= 10000)) (PreH16 : ((-10000) <= b_x_pre)) (PreH17 : (b_x_pre <= 10000)) (PreH18 : ((-10000) <= b_y_pre)) (PreH19 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1))

noncomputable def cmp_polar_values_return_wit_35 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) < (0 : Int))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH5 : ((-10000) <= gx_pre)) (PreH6 : (gx_pre <= 10000)) (PreH7 : ((-10000) <= gy_pre)) (PreH8 : (gy_pre <= 10000)) (PreH9 : ((-10000) <= a_x_pre)) (PreH10 : (a_x_pre <= 10000)) (PreH11 : ((-10000) <= a_y_pre)) (PreH12 : (a_y_pre <= 10000)) (PreH13 : ((-10000) <= b_x_pre)) (PreH14 : (b_x_pre <= 10000)) (PreH15 : ((-10000) <= b_y_pre)) (PreH16 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) < (0 : Int))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH5 : ((-10000) <= gx_pre)) (PreH6 : (gx_pre <= 10000)) (PreH7 : ((-10000) <= gy_pre)) (PreH8 : (gy_pre <= 10000)) (PreH9 : ((-10000) <= a_x_pre)) (PreH10 : (a_x_pre <= 10000)) (PreH11 : ((-10000) <= a_y_pre)) (PreH12 : (a_y_pre <= 10000)) (PreH13 : ((-10000) <= b_x_pre)) (PreH14 : (b_x_pre <= 10000)) (PreH15 : ((-10000) <= b_y_pre)) (PreH16 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_35_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) < (0 : Int))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH5 : ((-10000) <= gx_pre)) (PreH6 : (gx_pre <= 10000)) (PreH7 : ((-10000) <= gy_pre)) (PreH8 : (gy_pre <= 10000)) (PreH9 : ((-10000) <= a_x_pre)) (PreH10 : (a_x_pre <= 10000)) (PreH11 : ((-10000) <= a_y_pre)) (PreH12 : (a_y_pre <= 10000)) (PreH13 : ((-10000) <= b_x_pre)) (PreH14 : (b_x_pre <= 10000)) (PreH15 : ((-10000) <= b_y_pre)) (PreH16 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1)

noncomputable def cmp_polar_values_return_wit_36 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) < (0 : Int))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH3 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH4 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH5 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH7 : ((-10000) <= gx_pre)) (PreH8 : (gx_pre <= 10000)) (PreH9 : ((-10000) <= gy_pre)) (PreH10 : (gy_pre <= 10000)) (PreH11 : ((-10000) <= a_x_pre)) (PreH12 : (a_x_pre <= 10000)) (PreH13 : ((-10000) <= a_y_pre)) (PreH14 : (a_y_pre <= 10000)) (PreH15 : ((-10000) <= b_x_pre)) (PreH16 : (b_x_pre <= 10000)) (PreH17 : ((-10000) <= b_y_pre)) (PreH18 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) < (0 : Int))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH3 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH4 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH5 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH7 : ((-10000) <= gx_pre)) (PreH8 : (gx_pre <= 10000)) (PreH9 : ((-10000) <= gy_pre)) (PreH10 : (gy_pre <= 10000)) (PreH11 : ((-10000) <= a_x_pre)) (PreH12 : (a_x_pre <= 10000)) (PreH13 : ((-10000) <= a_y_pre)) (PreH14 : (a_y_pre <= 10000)) (PreH15 : ((-10000) <= b_x_pre)) (PreH16 : (b_x_pre <= 10000)) (PreH17 : ((-10000) <= b_y_pre)) (PreH18 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_36_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) < (0 : Int))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH3 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH4 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH5 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH7 : ((-10000) <= gx_pre)) (PreH8 : (gx_pre <= 10000)) (PreH9 : ((-10000) <= gy_pre)) (PreH10 : (gy_pre <= 10000)) (PreH11 : ((-10000) <= a_x_pre)) (PreH12 : (a_x_pre <= 10000)) (PreH13 : ((-10000) <= a_y_pre)) (PreH14 : (a_y_pre <= 10000)) (PreH15 : ((-10000) <= b_x_pre)) (PreH16 : (b_x_pre <= 10000)) (PreH17 : ((-10000) <= b_y_pre)) (PreH18 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1)

noncomputable def cmp_polar_values_return_wit_37 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) < (0 : Int))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH3 : ((b_x_pre - gx_pre) < (0 : Int))) (PreH4 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH5 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH7 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH8 : ((-10000) <= gx_pre)) (PreH9 : (gx_pre <= 10000)) (PreH10 : ((-10000) <= gy_pre)) (PreH11 : (gy_pre <= 10000)) (PreH12 : ((-10000) <= a_x_pre)) (PreH13 : (a_x_pre <= 10000)) (PreH14 : ((-10000) <= a_y_pre)) (PreH15 : (a_y_pre <= 10000)) (PreH16 : ((-10000) <= b_x_pre)) (PreH17 : (b_x_pre <= 10000)) (PreH18 : ((-10000) <= b_y_pre)) (PreH19 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) < (0 : Int))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH3 : ((b_x_pre - gx_pre) < (0 : Int))) (PreH4 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH5 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH7 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH8 : ((-10000) <= gx_pre)) (PreH9 : (gx_pre <= 10000)) (PreH10 : ((-10000) <= gy_pre)) (PreH11 : (gy_pre <= 10000)) (PreH12 : ((-10000) <= a_x_pre)) (PreH13 : (a_x_pre <= 10000)) (PreH14 : ((-10000) <= a_y_pre)) (PreH15 : (a_y_pre <= 10000)) (PreH16 : ((-10000) <= b_x_pre)) (PreH17 : (b_x_pre <= 10000)) (PreH18 : ((-10000) <= b_y_pre)) (PreH19 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_37_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) < (0 : Int))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH3 : ((b_x_pre - gx_pre) < (0 : Int))) (PreH4 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH5 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH7 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH8 : ((-10000) <= gx_pre)) (PreH9 : (gx_pre <= 10000)) (PreH10 : ((-10000) <= gy_pre)) (PreH11 : (gy_pre <= 10000)) (PreH12 : ((-10000) <= a_x_pre)) (PreH13 : (a_x_pre <= 10000)) (PreH14 : ((-10000) <= a_y_pre)) (PreH15 : (a_y_pre <= 10000)) (PreH16 : ((-10000) <= b_x_pre)) (PreH17 : (b_x_pre <= 10000)) (PreH18 : ((-10000) <= b_y_pre)) (PreH19 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1)

noncomputable def cmp_polar_values_return_wit_38 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) < (0 : Int))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH4 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH7 : ((-10000) <= gx_pre)) (PreH8 : (gx_pre <= 10000)) (PreH9 : ((-10000) <= gy_pre)) (PreH10 : (gy_pre <= 10000)) (PreH11 : ((-10000) <= a_x_pre)) (PreH12 : (a_x_pre <= 10000)) (PreH13 : ((-10000) <= a_y_pre)) (PreH14 : (a_y_pre <= 10000)) (PreH15 : ((-10000) <= b_x_pre)) (PreH16 : (b_x_pre <= 10000)) (PreH17 : ((-10000) <= b_y_pre)) (PreH18 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) < (0 : Int))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH4 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH7 : ((-10000) <= gx_pre)) (PreH8 : (gx_pre <= 10000)) (PreH9 : ((-10000) <= gy_pre)) (PreH10 : (gy_pre <= 10000)) (PreH11 : ((-10000) <= a_x_pre)) (PreH12 : (a_x_pre <= 10000)) (PreH13 : ((-10000) <= a_y_pre)) (PreH14 : (a_y_pre <= 10000)) (PreH15 : ((-10000) <= b_x_pre)) (PreH16 : (b_x_pre <= 10000)) (PreH17 : ((-10000) <= b_y_pre)) (PreH18 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_38_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) < (0 : Int))) (PreH2 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) <= (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH4 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH7 : ((-10000) <= gx_pre)) (PreH8 : (gx_pre <= 10000)) (PreH9 : ((-10000) <= gy_pre)) (PreH10 : (gy_pre <= 10000)) (PreH11 : ((-10000) <= a_x_pre)) (PreH12 : (a_x_pre <= 10000)) (PreH13 : ((-10000) <= a_y_pre)) (PreH14 : (a_y_pre <= 10000)) (PreH15 : ((-10000) <= b_x_pre)) (PreH16 : (b_x_pre <= 10000)) (PreH17 : ((-10000) <= b_y_pre)) (PreH18 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1)

noncomputable def cmp_polar_values_return_wit_39 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) > (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH3 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH4 : ((-10000) <= gx_pre)) (PreH5 : (gx_pre <= 10000)) (PreH6 : ((-10000) <= gy_pre)) (PreH7 : (gy_pre <= 10000)) (PreH8 : ((-10000) <= a_x_pre)) (PreH9 : (a_x_pre <= 10000)) (PreH10 : ((-10000) <= a_y_pre)) (PreH11 : (a_y_pre <= 10000)) (PreH12 : ((-10000) <= b_x_pre)) (PreH13 : (b_x_pre <= 10000)) (PreH14 : ((-10000) <= b_y_pre)) (PreH15 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1)) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) > (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH3 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH4 : ((-10000) <= gx_pre)) (PreH5 : (gx_pre <= 10000)) (PreH6 : ((-10000) <= gy_pre)) (PreH7 : (gy_pre <= 10000)) (PreH8 : ((-10000) <= a_x_pre)) (PreH9 : (a_x_pre <= 10000)) (PreH10 : ((-10000) <= a_y_pre)) (PreH11 : (a_y_pre <= 10000)) (PreH12 : ((-10000) <= b_x_pre)) (PreH13 : (b_x_pre <= 10000)) (PreH14 : ((-10000) <= b_y_pre)) (PreH15 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1)) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_39_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) > (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH3 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH4 : ((-10000) <= gx_pre)) (PreH5 : (gx_pre <= 10000)) (PreH6 : ((-10000) <= gy_pre)) (PreH7 : (gy_pre <= 10000)) (PreH8 : ((-10000) <= a_x_pre)) (PreH9 : (a_x_pre <= 10000)) (PreH10 : ((-10000) <= a_y_pre)) (PreH11 : (a_y_pre <= 10000)) (PreH12 : ((-10000) <= b_x_pre)) (PreH13 : (b_x_pre <= 10000)) (PreH14 : ((-10000) <= b_y_pre)) (PreH15 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1))

noncomputable def cmp_polar_values_return_wit_40 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) > (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH3 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH6 : ((-10000) <= gx_pre)) (PreH7 : (gx_pre <= 10000)) (PreH8 : ((-10000) <= gy_pre)) (PreH9 : (gy_pre <= 10000)) (PreH10 : ((-10000) <= a_x_pre)) (PreH11 : (a_x_pre <= 10000)) (PreH12 : ((-10000) <= a_y_pre)) (PreH13 : (a_y_pre <= 10000)) (PreH14 : ((-10000) <= b_x_pre)) (PreH15 : (b_x_pre <= 10000)) (PreH16 : ((-10000) <= b_y_pre)) (PreH17 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1)) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) > (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH3 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH6 : ((-10000) <= gx_pre)) (PreH7 : (gx_pre <= 10000)) (PreH8 : ((-10000) <= gy_pre)) (PreH9 : (gy_pre <= 10000)) (PreH10 : ((-10000) <= a_x_pre)) (PreH11 : (a_x_pre <= 10000)) (PreH12 : ((-10000) <= a_y_pre)) (PreH13 : (a_y_pre <= 10000)) (PreH14 : ((-10000) <= b_x_pre)) (PreH15 : (b_x_pre <= 10000)) (PreH16 : ((-10000) <= b_y_pre)) (PreH17 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1)) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_40_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) > (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH3 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH6 : ((-10000) <= gx_pre)) (PreH7 : (gx_pre <= 10000)) (PreH8 : ((-10000) <= gy_pre)) (PreH9 : (gy_pre <= 10000)) (PreH10 : ((-10000) <= a_x_pre)) (PreH11 : (a_x_pre <= 10000)) (PreH12 : ((-10000) <= a_y_pre)) (PreH13 : (a_y_pre <= 10000)) (PreH14 : ((-10000) <= b_x_pre)) (PreH15 : (b_x_pre <= 10000)) (PreH16 : ((-10000) <= b_y_pre)) (PreH17 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1))

noncomputable def cmp_polar_values_return_wit_41 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) > (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH7 : ((-10000) <= gx_pre)) (PreH8 : (gx_pre <= 10000)) (PreH9 : ((-10000) <= gy_pre)) (PreH10 : (gy_pre <= 10000)) (PreH11 : ((-10000) <= a_x_pre)) (PreH12 : (a_x_pre <= 10000)) (PreH13 : ((-10000) <= a_y_pre)) (PreH14 : (a_y_pre <= 10000)) (PreH15 : ((-10000) <= b_x_pre)) (PreH16 : (b_x_pre <= 10000)) (PreH17 : ((-10000) <= b_y_pre)) (PreH18 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1)) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) > (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH7 : ((-10000) <= gx_pre)) (PreH8 : (gx_pre <= 10000)) (PreH9 : ((-10000) <= gy_pre)) (PreH10 : (gy_pre <= 10000)) (PreH11 : ((-10000) <= a_x_pre)) (PreH12 : (a_x_pre <= 10000)) (PreH13 : ((-10000) <= a_y_pre)) (PreH14 : (a_y_pre <= 10000)) (PreH15 : ((-10000) <= b_x_pre)) (PreH16 : (b_x_pre <= 10000)) (PreH17 : ((-10000) <= b_y_pre)) (PreH18 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1)) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_41_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) > (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH7 : ((-10000) <= gx_pre)) (PreH8 : (gx_pre <= 10000)) (PreH9 : ((-10000) <= gy_pre)) (PreH10 : (gy_pre <= 10000)) (PreH11 : ((-10000) <= a_x_pre)) (PreH12 : (a_x_pre <= 10000)) (PreH13 : ((-10000) <= a_y_pre)) (PreH14 : (a_y_pre <= 10000)) (PreH15 : ((-10000) <= b_x_pre)) (PreH16 : (b_x_pre <= 10000)) (PreH17 : ((-10000) <= b_y_pre)) (PreH18 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1))

noncomputable def cmp_polar_values_return_wit_42 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) > (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH6 : ((-10000) <= gx_pre)) (PreH7 : (gx_pre <= 10000)) (PreH8 : ((-10000) <= gy_pre)) (PreH9 : (gy_pre <= 10000)) (PreH10 : ((-10000) <= a_x_pre)) (PreH11 : (a_x_pre <= 10000)) (PreH12 : ((-10000) <= a_y_pre)) (PreH13 : (a_y_pre <= 10000)) (PreH14 : ((-10000) <= b_x_pre)) (PreH15 : (b_x_pre <= 10000)) (PreH16 : ((-10000) <= b_y_pre)) (PreH17 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1)) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) > (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH6 : ((-10000) <= gx_pre)) (PreH7 : (gx_pre <= 10000)) (PreH8 : ((-10000) <= gy_pre)) (PreH9 : (gy_pre <= 10000)) (PreH10 : ((-10000) <= a_x_pre)) (PreH11 : (a_x_pre <= 10000)) (PreH12 : ((-10000) <= a_y_pre)) (PreH13 : (a_y_pre <= 10000)) (PreH14 : ((-10000) <= b_x_pre)) (PreH15 : (b_x_pre <= 10000)) (PreH16 : ((-10000) <= b_y_pre)) (PreH17 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1)) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_42_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((((a_x_pre - gx_pre) * (b_y_pre - gy_pre)) - ((a_y_pre - gy_pre) * (b_x_pre - gx_pre))) > (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH6 : ((-10000) <= gx_pre)) (PreH7 : (gx_pre <= 10000)) (PreH8 : ((-10000) <= gy_pre)) (PreH9 : (gy_pre <= 10000)) (PreH10 : ((-10000) <= a_x_pre)) (PreH11 : (a_x_pre <= 10000)) (PreH12 : ((-10000) <= a_y_pre)) (PreH13 : (a_y_pre <= 10000)) (PreH14 : ((-10000) <= b_x_pre)) (PreH15 : (b_x_pre <= 10000)) (PreH16 : ((-10000) <= b_y_pre)) (PreH17 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1))

noncomputable def cmp_polar_values_return_wit_43 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH2 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH3 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH5 : ((-10000) <= gx_pre)) (PreH6 : (gx_pre <= 10000)) (PreH7 : ((-10000) <= gy_pre)) (PreH8 : (gy_pre <= 10000)) (PreH9 : ((-10000) <= a_x_pre)) (PreH10 : (a_x_pre <= 10000)) (PreH11 : ((-10000) <= a_y_pre)) (PreH12 : (a_y_pre <= 10000)) (PreH13 : ((-10000) <= b_x_pre)) (PreH14 : (b_x_pre <= 10000)) (PreH15 : ((-10000) <= b_y_pre)) (PreH16 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH2 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH3 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH5 : ((-10000) <= gx_pre)) (PreH6 : (gx_pre <= 10000)) (PreH7 : ((-10000) <= gy_pre)) (PreH8 : (gy_pre <= 10000)) (PreH9 : ((-10000) <= a_x_pre)) (PreH10 : (a_x_pre <= 10000)) (PreH11 : ((-10000) <= a_y_pre)) (PreH12 : (a_y_pre <= 10000)) (PreH13 : ((-10000) <= b_x_pre)) (PreH14 : (b_x_pre <= 10000)) (PreH15 : ((-10000) <= b_y_pre)) (PreH16 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_43_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH2 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH3 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH5 : ((-10000) <= gx_pre)) (PreH6 : (gx_pre <= 10000)) (PreH7 : ((-10000) <= gy_pre)) (PreH8 : (gy_pre <= 10000)) (PreH9 : ((-10000) <= a_x_pre)) (PreH10 : (a_x_pre <= 10000)) (PreH11 : ((-10000) <= a_y_pre)) (PreH12 : (a_y_pre <= 10000)) (PreH13 : ((-10000) <= b_x_pre)) (PreH14 : (b_x_pre <= 10000)) (PreH15 : ((-10000) <= b_y_pre)) (PreH16 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1)

noncomputable def cmp_polar_values_return_wit_44 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH2 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH3 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((-10000) <= gx_pre)) (PreH5 : (gx_pre <= 10000)) (PreH6 : ((-10000) <= gy_pre)) (PreH7 : (gy_pre <= 10000)) (PreH8 : ((-10000) <= a_x_pre)) (PreH9 : (a_x_pre <= 10000)) (PreH10 : ((-10000) <= a_y_pre)) (PreH11 : (a_y_pre <= 10000)) (PreH12 : ((-10000) <= b_x_pre)) (PreH13 : (b_x_pre <= 10000)) (PreH14 : ((-10000) <= b_y_pre)) (PreH15 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH2 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH3 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((-10000) <= gx_pre)) (PreH5 : (gx_pre <= 10000)) (PreH6 : ((-10000) <= gy_pre)) (PreH7 : (gy_pre <= 10000)) (PreH8 : ((-10000) <= a_x_pre)) (PreH9 : (a_x_pre <= 10000)) (PreH10 : ((-10000) <= a_y_pre)) (PreH11 : (a_y_pre <= 10000)) (PreH12 : ((-10000) <= b_x_pre)) (PreH13 : (b_x_pre <= 10000)) (PreH14 : ((-10000) <= b_y_pre)) (PreH15 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_44_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_y_pre - gy_pre) > (0 : Int))) (PreH2 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH3 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((-10000) <= gx_pre)) (PreH5 : (gx_pre <= 10000)) (PreH6 : ((-10000) <= gy_pre)) (PreH7 : (gy_pre <= 10000)) (PreH8 : ((-10000) <= a_x_pre)) (PreH9 : (a_x_pre <= 10000)) (PreH10 : ((-10000) <= a_y_pre)) (PreH11 : (a_y_pre <= 10000)) (PreH12 : ((-10000) <= b_x_pre)) (PreH13 : (b_x_pre <= 10000)) (PreH14 : ((-10000) <= b_y_pre)) (PreH15 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1)

noncomputable def cmp_polar_values_return_wit_45 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH7 : ((-10000) <= gx_pre)) (PreH8 : (gx_pre <= 10000)) (PreH9 : ((-10000) <= gy_pre)) (PreH10 : (gy_pre <= 10000)) (PreH11 : ((-10000) <= a_x_pre)) (PreH12 : (a_x_pre <= 10000)) (PreH13 : ((-10000) <= a_y_pre)) (PreH14 : (a_y_pre <= 10000)) (PreH15 : ((-10000) <= b_x_pre)) (PreH16 : (b_x_pre <= 10000)) (PreH17 : ((-10000) <= b_y_pre)) (PreH18 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH7 : ((-10000) <= gx_pre)) (PreH8 : (gx_pre <= 10000)) (PreH9 : ((-10000) <= gy_pre)) (PreH10 : (gy_pre <= 10000)) (PreH11 : ((-10000) <= a_x_pre)) (PreH12 : (a_x_pre <= 10000)) (PreH13 : ((-10000) <= a_y_pre)) (PreH14 : (a_y_pre <= 10000)) (PreH15 : ((-10000) <= b_x_pre)) (PreH16 : (b_x_pre <= 10000)) (PreH17 : ((-10000) <= b_y_pre)) (PreH18 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_45_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((a_x_pre - gx_pre) < (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH7 : ((-10000) <= gx_pre)) (PreH8 : (gx_pre <= 10000)) (PreH9 : ((-10000) <= gy_pre)) (PreH10 : (gy_pre <= 10000)) (PreH11 : ((-10000) <= a_x_pre)) (PreH12 : (a_x_pre <= 10000)) (PreH13 : ((-10000) <= a_y_pre)) (PreH14 : (a_y_pre <= 10000)) (PreH15 : ((-10000) <= b_x_pre)) (PreH16 : (b_x_pre <= 10000)) (PreH17 : ((-10000) <= b_y_pre)) (PreH18 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1)

noncomputable def cmp_polar_values_return_wit_46 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH6 : ((-10000) <= gx_pre)) (PreH7 : (gx_pre <= 10000)) (PreH8 : ((-10000) <= gy_pre)) (PreH9 : (gy_pre <= 10000)) (PreH10 : ((-10000) <= a_x_pre)) (PreH11 : (a_x_pre <= 10000)) (PreH12 : ((-10000) <= a_y_pre)) (PreH13 : (a_y_pre <= 10000)) (PreH14 : ((-10000) <= b_x_pre)) (PreH15 : (b_x_pre <= 10000)) (PreH16 : ((-10000) <= b_y_pre)) (PreH17 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH6 : ((-10000) <= gx_pre)) (PreH7 : (gx_pre <= 10000)) (PreH8 : ((-10000) <= gy_pre)) (PreH9 : (gy_pre <= 10000)) (PreH10 : ((-10000) <= a_x_pre)) (PreH11 : (a_x_pre <= 10000)) (PreH12 : ((-10000) <= a_y_pre)) (PreH13 : (a_y_pre <= 10000)) (PreH14 : ((-10000) <= b_x_pre)) (PreH15 : (b_x_pre <= 10000)) (PreH16 : ((-10000) <= b_y_pre)) (PreH17 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_46_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_x_pre - gx_pre) >= (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) ≠ (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH6 : ((-10000) <= gx_pre)) (PreH7 : (gx_pre <= 10000)) (PreH8 : ((-10000) <= gy_pre)) (PreH9 : (gy_pre <= 10000)) (PreH10 : ((-10000) <= a_x_pre)) (PreH11 : (a_x_pre <= 10000)) (PreH12 : ((-10000) <= a_y_pre)) (PreH13 : (a_y_pre <= 10000)) (PreH14 : ((-10000) <= b_x_pre)) (PreH15 : (b_x_pre <= 10000)) (PreH16 : ((-10000) <= b_y_pre)) (PreH17 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) 1)

noncomputable def cmp_polar_values_return_wit_47 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_x_pre - gx_pre) < (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH5 : ((-10000) <= gx_pre)) (PreH6 : (gx_pre <= 10000)) (PreH7 : ((-10000) <= gy_pre)) (PreH8 : (gy_pre <= 10000)) (PreH9 : ((-10000) <= a_x_pre)) (PreH10 : (a_x_pre <= 10000)) (PreH11 : ((-10000) <= a_y_pre)) (PreH12 : (a_y_pre <= 10000)) (PreH13 : ((-10000) <= b_x_pre)) (PreH14 : (b_x_pre <= 10000)) (PreH15 : ((-10000) <= b_y_pre)) (PreH16 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1)) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_x_pre - gx_pre) < (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH5 : ((-10000) <= gx_pre)) (PreH6 : (gx_pre <= 10000)) (PreH7 : ((-10000) <= gy_pre)) (PreH8 : (gy_pre <= 10000)) (PreH9 : ((-10000) <= a_x_pre)) (PreH10 : (a_x_pre <= 10000)) (PreH11 : ((-10000) <= a_y_pre)) (PreH12 : (a_y_pre <= 10000)) (PreH13 : ((-10000) <= b_x_pre)) (PreH14 : (b_x_pre <= 10000)) (PreH15 : ((-10000) <= b_y_pre)) (PreH16 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1)) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_47_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_x_pre - gx_pre) < (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH5 : ((-10000) <= gx_pre)) (PreH6 : (gx_pre <= 10000)) (PreH7 : ((-10000) <= gy_pre)) (PreH8 : (gy_pre <= 10000)) (PreH9 : ((-10000) <= a_x_pre)) (PreH10 : (a_x_pre <= 10000)) (PreH11 : ((-10000) <= a_y_pre)) (PreH12 : (a_y_pre <= 10000)) (PreH13 : ((-10000) <= b_x_pre)) (PreH14 : (b_x_pre <= 10000)) (PreH15 : ((-10000) <= b_y_pre)) (PreH16 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1))

noncomputable def cmp_polar_values_return_wit_48 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_x_pre - gx_pre) < (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH7 : ((-10000) <= gx_pre)) (PreH8 : (gx_pre <= 10000)) (PreH9 : ((-10000) <= gy_pre)) (PreH10 : (gy_pre <= 10000)) (PreH11 : ((-10000) <= a_x_pre)) (PreH12 : (a_x_pre <= 10000)) (PreH13 : ((-10000) <= a_y_pre)) (PreH14 : (a_y_pre <= 10000)) (PreH15 : ((-10000) <= b_x_pre)) (PreH16 : (b_x_pre <= 10000)) (PreH17 : ((-10000) <= b_y_pre)) (PreH18 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1)) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_x_pre - gx_pre) < (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH7 : ((-10000) <= gx_pre)) (PreH8 : (gx_pre <= 10000)) (PreH9 : ((-10000) <= gy_pre)) (PreH10 : (gy_pre <= 10000)) (PreH11 : ((-10000) <= a_x_pre)) (PreH12 : (a_x_pre <= 10000)) (PreH13 : ((-10000) <= a_y_pre)) (PreH14 : (a_y_pre <= 10000)) (PreH15 : ((-10000) <= b_x_pre)) (PreH16 : (b_x_pre <= 10000)) (PreH17 : ((-10000) <= b_y_pre)) (PreH18 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1)) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_48_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_x_pre - gx_pre) < (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) = (0 : Int))) (PreH3 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH4 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH6 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH7 : ((-10000) <= gx_pre)) (PreH8 : (gx_pre <= 10000)) (PreH9 : ((-10000) <= gy_pre)) (PreH10 : (gy_pre <= 10000)) (PreH11 : ((-10000) <= a_x_pre)) (PreH12 : (a_x_pre <= 10000)) (PreH13 : ((-10000) <= a_y_pre)) (PreH14 : (a_y_pre <= 10000)) (PreH15 : ((-10000) <= b_x_pre)) (PreH16 : (b_x_pre <= 10000)) (PreH17 : ((-10000) <= b_y_pre)) (PreH18 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1))

noncomputable def cmp_polar_values_return_wit_49 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH3 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH4 : ((-10000) <= gx_pre)) (PreH5 : (gx_pre <= 10000)) (PreH6 : ((-10000) <= gy_pre)) (PreH7 : (gy_pre <= 10000)) (PreH8 : ((-10000) <= a_x_pre)) (PreH9 : (a_x_pre <= 10000)) (PreH10 : ((-10000) <= a_y_pre)) (PreH11 : (a_y_pre <= 10000)) (PreH12 : ((-10000) <= b_x_pre)) (PreH13 : (b_x_pre <= 10000)) (PreH14 : ((-10000) <= b_y_pre)) (PreH15 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1)) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH3 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH4 : ((-10000) <= gx_pre)) (PreH5 : (gx_pre <= 10000)) (PreH6 : ((-10000) <= gy_pre)) (PreH7 : (gy_pre <= 10000)) (PreH8 : ((-10000) <= a_x_pre)) (PreH9 : (a_x_pre <= 10000)) (PreH10 : ((-10000) <= a_y_pre)) (PreH11 : (a_y_pre <= 10000)) (PreH12 : ((-10000) <= b_x_pre)) (PreH13 : (b_x_pre <= 10000)) (PreH14 : ((-10000) <= b_y_pre)) (PreH15 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1)) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_49_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH3 : ((a_y_pre - gy_pre) > (0 : Int))) (PreH4 : ((-10000) <= gx_pre)) (PreH5 : (gx_pre <= 10000)) (PreH6 : ((-10000) <= gy_pre)) (PreH7 : (gy_pre <= 10000)) (PreH8 : ((-10000) <= a_x_pre)) (PreH9 : (a_x_pre <= 10000)) (PreH10 : ((-10000) <= a_y_pre)) (PreH11 : (a_y_pre <= 10000)) (PreH12 : ((-10000) <= b_x_pre)) (PreH13 : (b_x_pre <= 10000)) (PreH14 : ((-10000) <= b_y_pre)) (PreH15 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1))

noncomputable def cmp_polar_values_return_wit_50 : Prop :=
  (
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH3 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH6 : ((-10000) <= gx_pre)) (PreH7 : (gx_pre <= 10000)) (PreH8 : ((-10000) <= gy_pre)) (PreH9 : (gy_pre <= 10000)) (PreH10 : ((-10000) <= a_x_pre)) (PreH11 : (a_x_pre <= 10000)) (PreH12 : ((-10000) <= a_y_pre)) (PreH13 : (a_y_pre <= 10000)) (PreH14 : ((-10000) <= b_x_pre)) (PreH15 : (b_x_pre <= 10000)) (PreH16 : ((-10000) <= b_y_pre)) (PreH17 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1)) ”
  &&  emp
) \/
(
forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH3 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH6 : ((-10000) <= gx_pre)) (PreH7 : (gx_pre <= 10000)) (PreH8 : ((-10000) <= gy_pre)) (PreH9 : (gy_pre <= 10000)) (PreH10 : ((-10000) <= a_x_pre)) (PreH11 : (a_x_pre <= 10000)) (PreH12 : ((-10000) <= a_y_pre)) (PreH13 : (a_y_pre <= 10000)) (PreH14 : ((-10000) <= b_x_pre)) (PreH15 : (b_x_pre <= 10000)) (PreH16 : ((-10000) <= b_y_pre)) (PreH17 : (b_y_pre <= 10000)) ,
  TT && emp 
|--
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1)) ”
  &&  emp
)

noncomputable def cmp_polar_values_return_wit_50_split_goal_1 : Prop :=
  forall (gx_pre : Int) (gy_pre : Int) (a_x_pre : Int) (a_y_pre : Int) (b_x_pre : Int) (b_y_pre : Int) (PreH1 : ((b_y_pre - gy_pre) ≠ (0 : Int))) (PreH2 : ((b_y_pre - gy_pre) <= (0 : Int))) (PreH3 : ((a_x_pre - gx_pre) >= (0 : Int))) (PreH4 : ((a_y_pre - gy_pre) = (0 : Int))) (PreH5 : ((a_y_pre - gy_pre) <= (0 : Int))) (PreH6 : ((-10000) <= gx_pre)) (PreH7 : (gx_pre <= 10000)) (PreH8 : ((-10000) <= gy_pre)) (PreH9 : (gy_pre <= 10000)) (PreH10 : ((-10000) <= a_x_pre)) (PreH11 : (a_x_pre <= 10000)) (PreH12 : ((-10000) <= a_y_pre)) (PreH13 : (a_y_pre <= 10000)) (PreH14 : ((-10000) <= b_x_pre)) (PreH15 : (b_x_pre <= 10000)) (PreH16 : ((-10000) <= b_y_pre)) (PreH17 : (b_y_pre <= 10000)) ,
  (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point (a_x_pre) (a_y_pre)) (mk_point (b_x_pre) (b_y_pre)) (-1))

noncomputable def swap_points_safety_wit_1 : Prop :=
  forall (pts_l : (List point)) (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (FlatPoints flat pts_l)) (PreH9 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_l)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_l)))) (PreH11 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_l)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_l)))) ,
  ((( &( "tmp_x" ) )) # Int |->_)
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
  ** (intArray.full coords_pre (2 * n_pre) flat)
|--
  “ ((2 * i_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (2 * i_pre)) ”

noncomputable def swap_points_safety_wit_2 : Prop :=
  forall (pts_l : (List point)) (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (FlatPoints flat pts_l)) (PreH9 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_l)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_l)))) (PreH11 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_l)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_l)))) ,
  ((( &( "tmp_x" ) )) # Int |->_)
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
  ** (intArray.full coords_pre (2 * n_pre) flat)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def swap_points_safety_wit_3 : Prop :=
  forall (pts_l : (List point)) (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (FlatPoints flat pts_l)) (PreH9 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_l)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_l)))) (PreH11 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_l)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_l)))) ,
  ((( &( "tmp_y" ) )) # Int |->_)
  ** (intArray.full coords_pre (2 * n_pre) flat)
  ** ((( &( "tmp_x" ) )) # Int |-> ((Znth (2 * i_pre) flat (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
|--
  “ (((2 * i_pre) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((2 * i_pre) + 1)) ”

noncomputable def swap_points_safety_wit_4 : Prop :=
  forall (pts_l : (List point)) (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (FlatPoints flat pts_l)) (PreH9 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_l)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_l)))) (PreH11 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_l)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_l)))) ,
  ((( &( "tmp_y" ) )) # Int |->_)
  ** (intArray.full coords_pre (2 * n_pre) flat)
  ** ((( &( "tmp_x" ) )) # Int |-> ((Znth (2 * i_pre) flat (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
|--
  “ ((2 * i_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (2 * i_pre)) ”

noncomputable def swap_points_safety_wit_5 : Prop :=
  forall (pts_l : (List point)) (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (FlatPoints flat pts_l)) (PreH9 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_l)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_l)))) (PreH11 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_l)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_l)))) ,
  ((( &( "tmp_y" ) )) # Int |->_)
  ** (intArray.full coords_pre (2 * n_pre) flat)
  ** ((( &( "tmp_x" ) )) # Int |-> ((Znth (2 * i_pre) flat (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def swap_points_safety_wit_6 : Prop :=
  forall (pts_l : (List point)) (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (FlatPoints flat pts_l)) (PreH9 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_l)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_l)))) (PreH11 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_l)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_l)))) ,
  ((( &( "tmp_y" ) )) # Int |->_)
  ** (intArray.full coords_pre (2 * n_pre) flat)
  ** ((( &( "tmp_x" ) )) # Int |-> ((Znth (2 * i_pre) flat (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def swap_points_safety_wit_7 : Prop :=
  forall (pts_l : (List point)) (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (FlatPoints flat pts_l)) (PreH9 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_l)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_l)))) (PreH11 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_l)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_l)))) ,
  (intArray.full coords_pre (2 * n_pre) flat)
  ** ((( &( "tmp_y" ) )) # Int |-> ((Znth ((2 * i_pre) + 1) flat (0 : Int))))
  ** ((( &( "tmp_x" ) )) # Int |-> ((Znth (2 * i_pre) flat (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
|--
  “ ((2 * i_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (2 * i_pre)) ”

noncomputable def swap_points_safety_wit_8 : Prop :=
  forall (pts_l : (List point)) (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (FlatPoints flat pts_l)) (PreH9 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_l)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_l)))) (PreH11 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_l)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_l)))) ,
  (intArray.full coords_pre (2 * n_pre) flat)
  ** ((( &( "tmp_y" ) )) # Int |-> ((Znth ((2 * i_pre) + 1) flat (0 : Int))))
  ** ((( &( "tmp_x" ) )) # Int |-> ((Znth (2 * i_pre) flat (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def swap_points_safety_wit_9 : Prop :=
  forall (pts_l : (List point)) (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (FlatPoints flat pts_l)) (PreH9 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_l)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_l)))) (PreH11 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_l)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_l)))) ,
  (intArray.full coords_pre (2 * n_pre) flat)
  ** ((( &( "tmp_y" ) )) # Int |-> ((Znth ((2 * i_pre) + 1) flat (0 : Int))))
  ** ((( &( "tmp_x" ) )) # Int |-> ((Znth (2 * i_pre) flat (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
|--
  “ ((2 * j_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (2 * j_pre)) ”

noncomputable def swap_points_safety_wit_10 : Prop :=
  forall (pts_l : (List point)) (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (FlatPoints flat pts_l)) (PreH9 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_l)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_l)))) (PreH11 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_l)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_l)))) ,
  (intArray.full coords_pre (2 * n_pre) flat)
  ** ((( &( "tmp_y" ) )) # Int |-> ((Znth ((2 * i_pre) + 1) flat (0 : Int))))
  ** ((( &( "tmp_x" ) )) # Int |-> ((Znth (2 * i_pre) flat (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def swap_points_safety_wit_11 : Prop :=
  forall (pts_l : (List point)) (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (FlatPoints flat pts_l)) (PreH9 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_l)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_l)))) (PreH11 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_l)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_l)))) ,
  (intArray.full coords_pre (2 * n_pre) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))
  ** ((( &( "tmp_y" ) )) # Int |-> ((Znth ((2 * i_pre) + 1) flat (0 : Int))))
  ** ((( &( "tmp_x" ) )) # Int |-> ((Znth (2 * i_pre) flat (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
|--
  “ (((2 * i_pre) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((2 * i_pre) + 1)) ”

noncomputable def swap_points_safety_wit_12 : Prop :=
  forall (pts_l : (List point)) (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (FlatPoints flat pts_l)) (PreH9 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_l)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_l)))) (PreH11 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_l)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_l)))) ,
  (intArray.full coords_pre (2 * n_pre) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))
  ** ((( &( "tmp_y" ) )) # Int |-> ((Znth ((2 * i_pre) + 1) flat (0 : Int))))
  ** ((( &( "tmp_x" ) )) # Int |-> ((Znth (2 * i_pre) flat (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
|--
  “ ((2 * i_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (2 * i_pre)) ”

noncomputable def swap_points_safety_wit_13 : Prop :=
  forall (pts_l : (List point)) (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (FlatPoints flat pts_l)) (PreH9 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_l)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_l)))) (PreH11 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_l)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_l)))) ,
  (intArray.full coords_pre (2 * n_pre) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))
  ** ((( &( "tmp_y" ) )) # Int |-> ((Znth ((2 * i_pre) + 1) flat (0 : Int))))
  ** ((( &( "tmp_x" ) )) # Int |-> ((Znth (2 * i_pre) flat (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def swap_points_safety_wit_14 : Prop :=
  forall (pts_l : (List point)) (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (FlatPoints flat pts_l)) (PreH9 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_l)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_l)))) (PreH11 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_l)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_l)))) ,
  (intArray.full coords_pre (2 * n_pre) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))
  ** ((( &( "tmp_y" ) )) # Int |-> ((Znth ((2 * i_pre) + 1) flat (0 : Int))))
  ** ((( &( "tmp_x" ) )) # Int |-> ((Znth (2 * i_pre) flat (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def swap_points_safety_wit_15 : Prop :=
  forall (pts_l : (List point)) (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (FlatPoints flat pts_l)) (PreH9 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_l)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_l)))) (PreH11 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_l)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_l)))) ,
  (intArray.full coords_pre (2 * n_pre) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))
  ** ((( &( "tmp_y" ) )) # Int |-> ((Znth ((2 * i_pre) + 1) flat (0 : Int))))
  ** ((( &( "tmp_x" ) )) # Int |-> ((Znth (2 * i_pre) flat (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
|--
  “ (((2 * j_pre) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((2 * j_pre) + 1)) ”

noncomputable def swap_points_safety_wit_16 : Prop :=
  forall (pts_l : (List point)) (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (FlatPoints flat pts_l)) (PreH9 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_l)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_l)))) (PreH11 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_l)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_l)))) ,
  (intArray.full coords_pre (2 * n_pre) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))
  ** ((( &( "tmp_y" ) )) # Int |-> ((Znth ((2 * i_pre) + 1) flat (0 : Int))))
  ** ((( &( "tmp_x" ) )) # Int |-> ((Znth (2 * i_pre) flat (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
|--
  “ ((2 * j_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (2 * j_pre)) ”

noncomputable def swap_points_safety_wit_17 : Prop :=
  forall (pts_l : (List point)) (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (FlatPoints flat pts_l)) (PreH9 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_l)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_l)))) (PreH11 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_l)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_l)))) ,
  (intArray.full coords_pre (2 * n_pre) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))
  ** ((( &( "tmp_y" ) )) # Int |-> ((Znth ((2 * i_pre) + 1) flat (0 : Int))))
  ** ((( &( "tmp_x" ) )) # Int |-> ((Znth (2 * i_pre) flat (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def swap_points_safety_wit_18 : Prop :=
  forall (pts_l : (List point)) (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (FlatPoints flat pts_l)) (PreH9 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_l)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_l)))) (PreH11 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_l)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_l)))) ,
  (intArray.full coords_pre (2 * n_pre) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))
  ** ((( &( "tmp_y" ) )) # Int |-> ((Znth ((2 * i_pre) + 1) flat (0 : Int))))
  ** ((( &( "tmp_x" ) )) # Int |-> ((Znth (2 * i_pre) flat (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def swap_points_safety_wit_19 : Prop :=
  forall (pts_l : (List point)) (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (FlatPoints flat pts_l)) (PreH9 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_l)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_l)))) (PreH11 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_l)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_l)))) ,
  (intArray.full coords_pre (2 * n_pre) (replace_Znth (((2 * i_pre) + 1)) ((Znth ((2 * j_pre) + 1) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)) (0 : Int))) ((replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))))
  ** ((( &( "tmp_y" ) )) # Int |-> ((Znth ((2 * i_pre) + 1) flat (0 : Int))))
  ** ((( &( "tmp_x" ) )) # Int |-> ((Znth (2 * i_pre) flat (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
|--
  “ ((2 * j_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (2 * j_pre)) ”

noncomputable def swap_points_safety_wit_20 : Prop :=
  forall (pts_l : (List point)) (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (FlatPoints flat pts_l)) (PreH9 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_l)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_l)))) (PreH11 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_l)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_l)))) ,
  (intArray.full coords_pre (2 * n_pre) (replace_Znth (((2 * i_pre) + 1)) ((Znth ((2 * j_pre) + 1) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)) (0 : Int))) ((replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))))
  ** ((( &( "tmp_y" ) )) # Int |-> ((Znth ((2 * i_pre) + 1) flat (0 : Int))))
  ** ((( &( "tmp_x" ) )) # Int |-> ((Znth (2 * i_pre) flat (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def swap_points_safety_wit_21 : Prop :=
  forall (pts_l : (List point)) (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (FlatPoints flat pts_l)) (PreH9 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_l)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_l)))) (PreH11 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_l)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_l)))) ,
  (intArray.full coords_pre (2 * n_pre) (replace_Znth ((2 * j_pre)) ((Znth (2 * i_pre) flat (0 : Int))) ((replace_Znth (((2 * i_pre) + 1)) ((Znth ((2 * j_pre) + 1) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)) (0 : Int))) ((replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))))))
  ** ((( &( "tmp_y" ) )) # Int |-> ((Znth ((2 * i_pre) + 1) flat (0 : Int))))
  ** ((( &( "tmp_x" ) )) # Int |-> ((Znth (2 * i_pre) flat (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
|--
  “ (((2 * j_pre) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((2 * j_pre) + 1)) ”

noncomputable def swap_points_safety_wit_22 : Prop :=
  forall (pts_l : (List point)) (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (FlatPoints flat pts_l)) (PreH9 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_l)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_l)))) (PreH11 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_l)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_l)))) ,
  (intArray.full coords_pre (2 * n_pre) (replace_Znth ((2 * j_pre)) ((Znth (2 * i_pre) flat (0 : Int))) ((replace_Znth (((2 * i_pre) + 1)) ((Znth ((2 * j_pre) + 1) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)) (0 : Int))) ((replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))))))
  ** ((( &( "tmp_y" ) )) # Int |-> ((Znth ((2 * i_pre) + 1) flat (0 : Int))))
  ** ((( &( "tmp_x" ) )) # Int |-> ((Znth (2 * i_pre) flat (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
|--
  “ ((2 * j_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (2 * j_pre)) ”

noncomputable def swap_points_safety_wit_23 : Prop :=
  forall (pts_l : (List point)) (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (FlatPoints flat pts_l)) (PreH9 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_l)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_l)))) (PreH11 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_l)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_l)))) ,
  (intArray.full coords_pre (2 * n_pre) (replace_Znth ((2 * j_pre)) ((Znth (2 * i_pre) flat (0 : Int))) ((replace_Znth (((2 * i_pre) + 1)) ((Znth ((2 * j_pre) + 1) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)) (0 : Int))) ((replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))))))
  ** ((( &( "tmp_y" ) )) # Int |-> ((Znth ((2 * i_pre) + 1) flat (0 : Int))))
  ** ((( &( "tmp_x" ) )) # Int |-> ((Znth (2 * i_pre) flat (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def swap_points_safety_wit_24 : Prop :=
  forall (pts_l : (List point)) (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (FlatPoints flat pts_l)) (PreH9 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_l)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_l)))) (PreH11 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_l)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_l)))) ,
  (intArray.full coords_pre (2 * n_pre) (replace_Znth ((2 * j_pre)) ((Znth (2 * i_pre) flat (0 : Int))) ((replace_Znth (((2 * i_pre) + 1)) ((Znth ((2 * j_pre) + 1) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)) (0 : Int))) ((replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))))))
  ** ((( &( "tmp_y" ) )) # Int |-> ((Znth ((2 * i_pre) + 1) flat (0 : Int))))
  ** ((( &( "tmp_x" ) )) # Int |-> ((Znth (2 * i_pre) flat (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "j" ) )) # Int |-> (j_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def swap_points_return_wit_1 : Prop :=
  (
forall (pts_l : (List point)) (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (FlatPoints flat pts_l)) (PreH9 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_l)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_l)))) (PreH11 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_l)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_l)))) ,
  (intArray.full coords_pre (2 * n_pre) (replace_Znth (((2 * j_pre) + 1)) ((Znth ((2 * i_pre) + 1) flat (0 : Int))) ((replace_Znth ((2 * j_pre)) ((Znth (2 * i_pre) flat (0 : Int))) ((replace_Znth (((2 * i_pre) + 1)) ((Znth ((2 * j_pre) + 1) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)) (0 : Int))) ((replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))))))))
|--
  “ (FlatPoints (point_swap_flat (flat) (i_pre) (j_pre)) (point_swap_points (pts_l) (i_pre) (j_pre))) ” &&
  “ (PointPermutation pts_l (point_swap_points (pts_l) (i_pre) (j_pre))) ”
  &&  (intArray.full coords_pre (2 * n_pre) (point_swap_flat (flat) (i_pre) (j_pre)))
) \/
(
forall (pts_l : (List point)) (flat : (List Int)) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (FlatPoints flat pts_l)) (PreH9 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_l)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_l)))) (PreH11 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_l)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_l)))) ,
  TT && emp 
|--
  “ (PointPermutation pts_l (point_swap_points (pts_l) (i_pre) (j_pre))) ” &&
  “ (FlatPoints (point_swap_flat (flat) (i_pre) (j_pre)) (point_swap_points (pts_l) (i_pre) (j_pre))) ” &&
  “ ((replace_Znth (((2 * j_pre) + 1)) ((Znth ((2 * i_pre) + 1) flat (0 : Int))) ((replace_Znth ((2 * j_pre)) ((Znth (2 * i_pre) flat (0 : Int))) ((replace_Znth (((2 * i_pre) + 1)) ((Znth ((2 * j_pre) + 1) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)) (0 : Int))) ((replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))))))) = (point_swap_flat (flat) (i_pre) (j_pre))) ”
  &&  emp
)

noncomputable def swap_points_return_wit_1_split_goal_1 : Prop :=
  forall (pts_l : (List point)) (flat : (List Int)) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (FlatPoints flat pts_l)) (PreH9 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_l)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_l)))) (PreH11 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_l)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_l)))) ,
  (PointPermutation pts_l (point_swap_points (pts_l) (i_pre) (j_pre)))

noncomputable def swap_points_return_wit_1_split_goal_2 : Prop :=
  forall (pts_l : (List point)) (flat : (List Int)) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (FlatPoints flat pts_l)) (PreH9 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_l)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_l)))) (PreH11 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_l)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_l)))) ,
  (FlatPoints (point_swap_flat (flat) (i_pre) (j_pre)) (point_swap_points (pts_l) (i_pre) (j_pre)))

noncomputable def swap_points_return_wit_1_split_goal_3 : Prop :=
  forall (pts_l : (List point)) (flat : (List Int)) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (FlatPoints flat pts_l)) (PreH9 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_l)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_l)))) (PreH11 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_l)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_l)))) ,
  ((replace_Znth (((2 * j_pre) + 1)) ((Znth ((2 * i_pre) + 1) flat (0 : Int))) ((replace_Znth ((2 * j_pre)) ((Znth (2 * i_pre) flat (0 : Int))) ((replace_Znth (((2 * i_pre) + 1)) ((Znth ((2 * j_pre) + 1) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)) (0 : Int))) ((replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))))))) = (point_swap_flat (flat) (i_pre) (j_pre)))

noncomputable def swap_points_partial_solve_wit_1 : Prop :=
  forall (pts_l : (List point)) (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (FlatPoints flat pts_l)) (PreH9 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_l)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_l)))) (PreH11 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_l)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_l)))) ,
  (intArray.full coords_pre (2 * n_pre) flat)
|--
  “ ((0 : Int) <= i_pre) ” &&
  “ (i_pre < n_pre) ” &&
  “ ((0 : Int) <= j_pre) ” &&
  “ (j_pre < n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ ((Zlength (pts_l)) = n_pre) ” &&
  “ (FlatPoints flat pts_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_l))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_l))) ”
  &&  (((coords_pre + ((2 * i_pre) * sizeof(INT)))) # Int |-> ((Znth (2 * i_pre) flat (0 : Int))))
  ** (intArray.missing_i coords_pre (2 * i_pre) (0 : Int) (2 * n_pre) flat)

noncomputable def swap_points_partial_solve_wit_2 : Prop :=
  forall (pts_l : (List point)) (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (FlatPoints flat pts_l)) (PreH9 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_l)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_l)))) (PreH11 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_l)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_l)))) ,
  (intArray.full coords_pre (2 * n_pre) flat)
|--
  “ ((0 : Int) <= i_pre) ” &&
  “ (i_pre < n_pre) ” &&
  “ ((0 : Int) <= j_pre) ” &&
  “ (j_pre < n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ ((Zlength (pts_l)) = n_pre) ” &&
  “ (FlatPoints flat pts_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_l))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_l))) ”
  &&  (((coords_pre + (((2 * i_pre) + 1) * sizeof(INT)))) # Int |-> ((Znth ((2 * i_pre) + 1) flat (0 : Int))))
  ** (intArray.missing_i coords_pre ((2 * i_pre) + 1) (0 : Int) (2 * n_pre) flat)

noncomputable def swap_points_partial_solve_wit_3 : Prop :=
  forall (pts_l : (List point)) (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (FlatPoints flat pts_l)) (PreH9 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_l)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_l)))) (PreH11 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_l)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_l)))) ,
  (intArray.full coords_pre (2 * n_pre) flat)
|--
  “ ((0 : Int) <= i_pre) ” &&
  “ (i_pre < n_pre) ” &&
  “ ((0 : Int) <= j_pre) ” &&
  “ (j_pre < n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ ((Zlength (pts_l)) = n_pre) ” &&
  “ (FlatPoints flat pts_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_l))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_l))) ”
  &&  (((coords_pre + ((2 * j_pre) * sizeof(INT)))) # Int |-> ((Znth (2 * j_pre) flat (0 : Int))))
  ** (intArray.missing_i coords_pre (2 * j_pre) (0 : Int) (2 * n_pre) flat)

noncomputable def swap_points_partial_solve_wit_4 : Prop :=
  forall (pts_l : (List point)) (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (FlatPoints flat pts_l)) (PreH9 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_l)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_l)))) (PreH11 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_l)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_l)))) ,
  (intArray.full coords_pre (2 * n_pre) flat)
|--
  “ ((0 : Int) <= i_pre) ” &&
  “ (i_pre < n_pre) ” &&
  “ ((0 : Int) <= j_pre) ” &&
  “ (j_pre < n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ ((Zlength (pts_l)) = n_pre) ” &&
  “ (FlatPoints flat pts_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_l))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_l))) ”
  &&  (((coords_pre + ((2 * i_pre) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i coords_pre (2 * i_pre) (0 : Int) (2 * n_pre) flat)

noncomputable def swap_points_partial_solve_wit_5 : Prop :=
  forall (pts_l : (List point)) (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (FlatPoints flat pts_l)) (PreH9 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_l)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_l)))) (PreH11 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_l)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_l)))) ,
  (intArray.full coords_pre (2 * n_pre) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))
|--
  “ ((0 : Int) <= i_pre) ” &&
  “ (i_pre < n_pre) ” &&
  “ ((0 : Int) <= j_pre) ” &&
  “ (j_pre < n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ ((Zlength (pts_l)) = n_pre) ” &&
  “ (FlatPoints flat pts_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_l))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_l))) ”
  &&  (((coords_pre + (((2 * j_pre) + 1) * sizeof(INT)))) # Int |-> ((Znth ((2 * j_pre) + 1) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)) (0 : Int))))
  ** (intArray.missing_i coords_pre ((2 * j_pre) + 1) (0 : Int) (2 * n_pre) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))

noncomputable def swap_points_partial_solve_wit_6 : Prop :=
  forall (pts_l : (List point)) (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (FlatPoints flat pts_l)) (PreH9 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_l)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_l)))) (PreH11 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_l)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_l)))) ,
  (intArray.full coords_pre (2 * n_pre) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))
|--
  “ ((0 : Int) <= i_pre) ” &&
  “ (i_pre < n_pre) ” &&
  “ ((0 : Int) <= j_pre) ” &&
  “ (j_pre < n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ ((Zlength (pts_l)) = n_pre) ” &&
  “ (FlatPoints flat pts_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_l))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_l))) ”
  &&  (((coords_pre + (((2 * i_pre) + 1) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i coords_pre ((2 * i_pre) + 1) (0 : Int) (2 * n_pre) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))

noncomputable def swap_points_partial_solve_wit_7 : Prop :=
  forall (pts_l : (List point)) (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (FlatPoints flat pts_l)) (PreH9 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_l)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_l)))) (PreH11 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_l)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_l)))) ,
  (intArray.full coords_pre (2 * n_pre) (replace_Znth (((2 * i_pre) + 1)) ((Znth ((2 * j_pre) + 1) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)) (0 : Int))) ((replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))))
|--
  “ ((0 : Int) <= i_pre) ” &&
  “ (i_pre < n_pre) ” &&
  “ ((0 : Int) <= j_pre) ” &&
  “ (j_pre < n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ ((Zlength (pts_l)) = n_pre) ” &&
  “ (FlatPoints flat pts_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_l))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_l))) ”
  &&  (((coords_pre + ((2 * j_pre) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i coords_pre (2 * j_pre) (0 : Int) (2 * n_pre) (replace_Znth (((2 * i_pre) + 1)) ((Znth ((2 * j_pre) + 1) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)) (0 : Int))) ((replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))))

noncomputable def swap_points_partial_solve_wit_8 : Prop :=
  forall (pts_l : (List point)) (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (i_pre : Int) (j_pre : Int) (PreH1 : ((0 : Int) <= i_pre)) (PreH2 : (i_pre < n_pre)) (PreH3 : ((0 : Int) <= j_pre)) (PreH4 : (j_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((Zlength (pts_l)) = n_pre)) (PreH8 : (FlatPoints flat pts_l)) (PreH9 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_l)))) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_l)))) (PreH11 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_l)))) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_l)))) ,
  (intArray.full coords_pre (2 * n_pre) (replace_Znth ((2 * j_pre)) ((Znth (2 * i_pre) flat (0 : Int))) ((replace_Znth (((2 * i_pre) + 1)) ((Znth ((2 * j_pre) + 1) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)) (0 : Int))) ((replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))))))
|--
  “ ((0 : Int) <= i_pre) ” &&
  “ (i_pre < n_pre) ” &&
  “ ((0 : Int) <= j_pre) ” &&
  “ (j_pre < n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ ((Zlength (pts_l)) = n_pre) ” &&
  “ (FlatPoints flat pts_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_l))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_l))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_l))) ”
  &&  (((coords_pre + (((2 * j_pre) + 1) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i coords_pre ((2 * j_pre) + 1) (0 : Int) (2 * n_pre) (replace_Znth ((2 * j_pre)) ((Znth (2 * i_pre) flat (0 : Int))) ((replace_Znth (((2 * i_pre) + 1)) ((Znth ((2 * j_pre) + 1) (replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)) (0 : Int))) ((replace_Znth ((2 * i_pre)) ((Znth (2 * j_pre) flat (0 : Int))) (flat)))))))

noncomputable def partition_points_safety_wit_1 : Prop :=
  forall (pts_l : (List point)) (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (PreH1 : ((0 : Int) <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : (FlatPoints flat pts_l)) (PreH8 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH9 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH10 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH11 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  ((( &( "pivot_x" ) )) # Int |->_)
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** (intArray.full coords_pre (2 * n_pre) flat)
|--
  “ ((2 * high_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (2 * high_pre)) ”

noncomputable def partition_points_safety_wit_2 : Prop :=
  forall (pts_l : (List point)) (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (PreH1 : ((0 : Int) <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : (FlatPoints flat pts_l)) (PreH8 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH9 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH10 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH11 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  ((( &( "pivot_x" ) )) # Int |->_)
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** (intArray.full coords_pre (2 * n_pre) flat)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def partition_points_safety_wit_3 : Prop :=
  forall (pts_l : (List point)) (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (PreH1 : ((0 : Int) <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : (FlatPoints flat pts_l)) (PreH8 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH9 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH10 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH11 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  ((( &( "pivot_y" ) )) # Int |->_)
  ** (intArray.full coords_pre (2 * n_pre) flat)
  ** ((( &( "pivot_x" ) )) # Int |-> ((Znth (2 * high_pre) flat (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
|--
  “ (((2 * high_pre) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((2 * high_pre) + 1)) ”

noncomputable def partition_points_safety_wit_4 : Prop :=
  forall (pts_l : (List point)) (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (PreH1 : ((0 : Int) <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : (FlatPoints flat pts_l)) (PreH8 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH9 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH10 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH11 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  ((( &( "pivot_y" ) )) # Int |->_)
  ** (intArray.full coords_pre (2 * n_pre) flat)
  ** ((( &( "pivot_x" ) )) # Int |-> ((Znth (2 * high_pre) flat (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
|--
  “ ((2 * high_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (2 * high_pre)) ”

noncomputable def partition_points_safety_wit_5 : Prop :=
  forall (pts_l : (List point)) (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (PreH1 : ((0 : Int) <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : (FlatPoints flat pts_l)) (PreH8 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH9 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH10 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH11 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  ((( &( "pivot_y" ) )) # Int |->_)
  ** (intArray.full coords_pre (2 * n_pre) flat)
  ** ((( &( "pivot_x" ) )) # Int |-> ((Znth (2 * high_pre) flat (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def partition_points_safety_wit_6 : Prop :=
  forall (pts_l : (List point)) (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (PreH1 : ((0 : Int) <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : (FlatPoints flat pts_l)) (PreH8 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH9 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH10 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH11 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  ((( &( "pivot_y" ) )) # Int |->_)
  ** (intArray.full coords_pre (2 * n_pre) flat)
  ** ((( &( "pivot_x" ) )) # Int |-> ((Znth (2 * high_pre) flat (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def partition_points_safety_wit_7 : Prop :=
  forall (pts_l : (List point)) (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (PreH1 : ((0 : Int) <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : (FlatPoints flat pts_l)) (PreH8 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH9 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH10 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH11 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  ((( &( "i" ) )) # Int |->_)
  ** (intArray.full coords_pre (2 * n_pre) flat)
  ** ((( &( "pivot_y" ) )) # Int |-> ((Znth ((2 * high_pre) + 1) flat (0 : Int))))
  ** ((( &( "pivot_x" ) )) # Int |-> ((Znth (2 * high_pre) flat (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
|--
  “ ((low_pre - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (low_pre - 1)) ”

noncomputable def partition_points_safety_wit_8 : Prop :=
  forall (pts_l : (List point)) (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (PreH1 : ((0 : Int) <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : (FlatPoints flat pts_l)) (PreH8 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH9 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH10 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH11 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  ((( &( "i" ) )) # Int |->_)
  ** (intArray.full coords_pre (2 * n_pre) flat)
  ** ((( &( "pivot_y" ) )) # Int |-> ((Znth ((2 * high_pre) + 1) flat (0 : Int))))
  ** ((( &( "pivot_x" ) )) # Int |-> ((Znth (2 * high_pre) flat (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def partition_points_safety_wit_9 : Prop :=
  forall (pts_l : (List point)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (flat_cur : (List Int)) (pivot_x : Int) (pivot_y : Int) (pts_cur : (List point)) (j : Int) (i : Int) (PreH1 : (j < high_pre)) (PreH2 : ((0 : Int) <= low_pre)) (PreH3 : (low_pre <= high_pre)) (PreH4 : (high_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((low_pre - 1) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : ((Zlength (pts_l)) = n_pre)) (PreH11 : ((Zlength (pts_cur)) = n_pre)) (PreH12 : ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point)))) (PreH13 : (FlatPoints flat_cur pts_cur)) (PreH14 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur)))) (PreH15 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur)))) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur)))) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur)))) (PreH18 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH19 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH20 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH21 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH22 : (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j)) ,
  ((( &( "ax" ) )) # Int |->_)
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pivot_y" ) )) # Int |-> (pivot_y))
  ** ((( &( "pivot_x" ) )) # Int |-> (pivot_x))
  ** (intArray.full coords_pre (2 * n_pre) flat_cur)
|--
  “ ((2 * j) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (2 * j)) ”

noncomputable def partition_points_safety_wit_10 : Prop :=
  forall (pts_l : (List point)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (flat_cur : (List Int)) (pivot_x : Int) (pivot_y : Int) (pts_cur : (List point)) (j : Int) (i : Int) (PreH1 : (j < high_pre)) (PreH2 : ((0 : Int) <= low_pre)) (PreH3 : (low_pre <= high_pre)) (PreH4 : (high_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((low_pre - 1) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : ((Zlength (pts_l)) = n_pre)) (PreH11 : ((Zlength (pts_cur)) = n_pre)) (PreH12 : ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point)))) (PreH13 : (FlatPoints flat_cur pts_cur)) (PreH14 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur)))) (PreH15 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur)))) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur)))) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur)))) (PreH18 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH19 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH20 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH21 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH22 : (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j)) ,
  ((( &( "ax" ) )) # Int |->_)
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pivot_y" ) )) # Int |-> (pivot_y))
  ** ((( &( "pivot_x" ) )) # Int |-> (pivot_x))
  ** (intArray.full coords_pre (2 * n_pre) flat_cur)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def partition_points_safety_wit_11 : Prop :=
  forall (pts_l : (List point)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (flat_cur : (List Int)) (pivot_x : Int) (pivot_y : Int) (pts_cur : (List point)) (j : Int) (i : Int) (PreH1 : (j < high_pre)) (PreH2 : ((0 : Int) <= low_pre)) (PreH3 : (low_pre <= high_pre)) (PreH4 : (high_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((low_pre - 1) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : ((Zlength (pts_l)) = n_pre)) (PreH11 : ((Zlength (pts_cur)) = n_pre)) (PreH12 : ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point)))) (PreH13 : (FlatPoints flat_cur pts_cur)) (PreH14 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur)))) (PreH15 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur)))) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur)))) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur)))) (PreH18 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH19 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH20 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH21 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH22 : (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j)) ,
  ((( &( "ay" ) )) # Int |->_)
  ** (intArray.full coords_pre (2 * n_pre) flat_cur)
  ** ((( &( "ax" ) )) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pivot_y" ) )) # Int |-> (pivot_y))
  ** ((( &( "pivot_x" ) )) # Int |-> (pivot_x))
|--
  “ (((2 * j) + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((2 * j) + 1)) ”

noncomputable def partition_points_safety_wit_12 : Prop :=
  forall (pts_l : (List point)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (flat_cur : (List Int)) (pivot_x : Int) (pivot_y : Int) (pts_cur : (List point)) (j : Int) (i : Int) (PreH1 : (j < high_pre)) (PreH2 : ((0 : Int) <= low_pre)) (PreH3 : (low_pre <= high_pre)) (PreH4 : (high_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((low_pre - 1) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : ((Zlength (pts_l)) = n_pre)) (PreH11 : ((Zlength (pts_cur)) = n_pre)) (PreH12 : ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point)))) (PreH13 : (FlatPoints flat_cur pts_cur)) (PreH14 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur)))) (PreH15 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur)))) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur)))) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur)))) (PreH18 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH19 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH20 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH21 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH22 : (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j)) ,
  ((( &( "ay" ) )) # Int |->_)
  ** (intArray.full coords_pre (2 * n_pre) flat_cur)
  ** ((( &( "ax" ) )) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pivot_y" ) )) # Int |-> (pivot_y))
  ** ((( &( "pivot_x" ) )) # Int |-> (pivot_x))
|--
  “ ((2 * j) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (2 * j)) ”

noncomputable def partition_points_safety_wit_13 : Prop :=
  forall (pts_l : (List point)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (flat_cur : (List Int)) (pivot_x : Int) (pivot_y : Int) (pts_cur : (List point)) (j : Int) (i : Int) (PreH1 : (j < high_pre)) (PreH2 : ((0 : Int) <= low_pre)) (PreH3 : (low_pre <= high_pre)) (PreH4 : (high_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((low_pre - 1) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : ((Zlength (pts_l)) = n_pre)) (PreH11 : ((Zlength (pts_cur)) = n_pre)) (PreH12 : ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point)))) (PreH13 : (FlatPoints flat_cur pts_cur)) (PreH14 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur)))) (PreH15 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur)))) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur)))) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur)))) (PreH18 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH19 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH20 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH21 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH22 : (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j)) ,
  ((( &( "ay" ) )) # Int |->_)
  ** (intArray.full coords_pre (2 * n_pre) flat_cur)
  ** ((( &( "ax" ) )) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pivot_y" ) )) # Int |-> (pivot_y))
  ** ((( &( "pivot_x" ) )) # Int |-> (pivot_x))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def partition_points_safety_wit_14 : Prop :=
  forall (pts_l : (List point)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (flat_cur : (List Int)) (pivot_x : Int) (pivot_y : Int) (pts_cur : (List point)) (j : Int) (i : Int) (PreH1 : (j < high_pre)) (PreH2 : ((0 : Int) <= low_pre)) (PreH3 : (low_pre <= high_pre)) (PreH4 : (high_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((low_pre - 1) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : ((Zlength (pts_l)) = n_pre)) (PreH11 : ((Zlength (pts_cur)) = n_pre)) (PreH12 : ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point)))) (PreH13 : (FlatPoints flat_cur pts_cur)) (PreH14 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur)))) (PreH15 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur)))) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur)))) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur)))) (PreH18 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH19 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH20 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH21 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH22 : (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j)) ,
  ((( &( "ay" ) )) # Int |->_)
  ** (intArray.full coords_pre (2 * n_pre) flat_cur)
  ** ((( &( "ax" ) )) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pivot_y" ) )) # Int |-> (pivot_y))
  ** ((( &( "pivot_x" ) )) # Int |-> (pivot_x))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def partition_points_safety_wit_15 : Prop :=
  forall (pts_l : (List point)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (pivot_x : Int) (pivot_y : Int) (j : Int) (i : Int) (retval : Int) (flat_cur : (List Int)) (pts_cur : (List point)) (PreH1 : (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point ((Znth (2 * j) flat_cur (0 : Int))) ((Znth ((2 * j) + 1) flat_cur (0 : Int)))) (mk_point (pivot_x) (pivot_y)) retval)) (PreH2 : (j < high_pre)) (PreH3 : ((0 : Int) <= low_pre)) (PreH4 : (low_pre <= high_pre)) (PreH5 : (high_pre < n_pre)) (PreH6 : ((0 : Int) <= n_pre)) (PreH7 : (n_pre <= 50000)) (PreH8 : ((low_pre - 1) <= i)) (PreH9 : (i < j)) (PreH10 : (j <= high_pre)) (PreH11 : ((Zlength (pts_l)) = n_pre)) (PreH12 : ((Zlength (pts_cur)) = n_pre)) (PreH13 : ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point)))) (PreH14 : (FlatPoints flat_cur pts_cur)) (PreH15 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur)))) (PreH16 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur)))) (PreH17 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur)))) (PreH18 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur)))) (PreH19 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH20 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH21 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH22 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH23 : (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j)) ,
  ((( &( "c" ) )) # Int |-> (retval))
  ** (intArray.full coords_pre (2 * n_pre) flat_cur)
  ** ((( &( "ay" ) )) # Int |-> ((Znth ((2 * j) + 1) flat_cur (0 : Int))))
  ** ((( &( "ax" ) )) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pivot_y" ) )) # Int |-> (pivot_y))
  ** ((( &( "pivot_x" ) )) # Int |-> (pivot_x))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def partition_points_safety_wit_16 : Prop :=
  forall (pts_l : (List point)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (pivot_x : Int) (pivot_y : Int) (j : Int) (i : Int) (retval : Int) (flat_cur : (List Int)) (pts_cur : (List point)) (PreH1 : (retval <= (0 : Int))) (PreH2 : (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point ((Znth (2 * j) flat_cur (0 : Int))) ((Znth ((2 * j) + 1) flat_cur (0 : Int)))) (mk_point (pivot_x) (pivot_y)) retval)) (PreH3 : (j < high_pre)) (PreH4 : ((0 : Int) <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((0 : Int) <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((low_pre - 1) <= i)) (PreH10 : (i < j)) (PreH11 : (j <= high_pre)) (PreH12 : ((Zlength (pts_l)) = n_pre)) (PreH13 : ((Zlength (pts_cur)) = n_pre)) (PreH14 : ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point)))) (PreH15 : (FlatPoints flat_cur pts_cur)) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur)))) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur)))) (PreH18 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur)))) (PreH19 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur)))) (PreH20 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH21 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH22 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH23 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH24 : (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j)) ,
  ((( &( "c" ) )) # Int |-> (retval))
  ** (intArray.full coords_pre (2 * n_pre) flat_cur)
  ** ((( &( "ay" ) )) # Int |-> ((Znth ((2 * j) + 1) flat_cur (0 : Int))))
  ** ((( &( "ax" ) )) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pivot_y" ) )) # Int |-> (pivot_y))
  ** ((( &( "pivot_x" ) )) # Int |-> (pivot_x))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def partition_points_safety_wit_17 : Prop :=
  forall (pts_l : (List point)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (pivot_x : Int) (pivot_y : Int) (j : Int) (i : Int) (retval : Int) (flat_cur : (List Int)) (pts_cur : (List point)) (PreH1 : (FlatPoints (point_swap_flat (flat_cur) ((i + 1)) (j)) (point_swap_points (pts_cur) ((i + 1)) (j)))) (PreH2 : (PointPermutation pts_cur (point_swap_points (pts_cur) ((i + 1)) (j)))) (PreH3 : (retval <= (0 : Int))) (PreH4 : (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point ((Znth (2 * j) flat_cur (0 : Int))) ((Znth ((2 * j) + 1) flat_cur (0 : Int)))) (mk_point (pivot_x) (pivot_y)) retval)) (PreH5 : (j < high_pre)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n_pre)) (PreH9 : ((0 : Int) <= n_pre)) (PreH10 : (n_pre <= 50000)) (PreH11 : ((low_pre - 1) <= i)) (PreH12 : (i < j)) (PreH13 : (j <= high_pre)) (PreH14 : ((Zlength (pts_l)) = n_pre)) (PreH15 : ((Zlength (pts_cur)) = n_pre)) (PreH16 : ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point)))) (PreH17 : (FlatPoints flat_cur pts_cur)) (PreH18 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur)))) (PreH19 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur)))) (PreH20 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur)))) (PreH21 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur)))) (PreH22 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH23 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH24 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH25 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH26 : (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j)) ,
  (intArray.full coords_pre (2 * n_pre) (point_swap_flat (flat_cur) ((i + 1)) (j)))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "i" ) )) # Int |-> ((i + 1)))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pivot_y" ) )) # Int |-> (pivot_y))
  ** ((( &( "pivot_x" ) )) # Int |-> (pivot_x))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def partition_points_safety_wit_18 : Prop :=
  forall (pts_l : (List point)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (pivot_x : Int) (pivot_y : Int) (j : Int) (i : Int) (retval : Int) (flat_cur : (List Int)) (pts_cur : (List point)) (PreH1 : (retval > (0 : Int))) (PreH2 : (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point ((Znth (2 * j) flat_cur (0 : Int))) ((Znth ((2 * j) + 1) flat_cur (0 : Int)))) (mk_point (pivot_x) (pivot_y)) retval)) (PreH3 : (j < high_pre)) (PreH4 : ((0 : Int) <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((0 : Int) <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((low_pre - 1) <= i)) (PreH10 : (i < j)) (PreH11 : (j <= high_pre)) (PreH12 : ((Zlength (pts_l)) = n_pre)) (PreH13 : ((Zlength (pts_cur)) = n_pre)) (PreH14 : ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point)))) (PreH15 : (FlatPoints flat_cur pts_cur)) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur)))) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur)))) (PreH18 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur)))) (PreH19 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur)))) (PreH20 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH21 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH22 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH23 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH24 : (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j)) ,
  (intArray.full coords_pre (2 * n_pre) flat_cur)
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pivot_y" ) )) # Int |-> (pivot_y))
  ** ((( &( "pivot_x" ) )) # Int |-> (pivot_x))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def partition_points_safety_wit_19 : Prop :=
  forall (pts_l : (List point)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (pivot_x : Int) (pivot_y : Int) (j : Int) (i : Int) (flat_cur : (List Int)) (pts_cur : (List point)) (PreH1 : (j >= high_pre)) (PreH2 : ((0 : Int) <= low_pre)) (PreH3 : (low_pre <= high_pre)) (PreH4 : (high_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((low_pre - 1) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : ((Zlength (pts_l)) = n_pre)) (PreH11 : ((Zlength (pts_cur)) = n_pre)) (PreH12 : ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point)))) (PreH13 : (FlatPoints flat_cur pts_cur)) (PreH14 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur)))) (PreH15 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur)))) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur)))) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur)))) (PreH18 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH19 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH20 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH21 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH22 : (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j)) ,
  ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "pivot_y" ) )) # Int |-> (pivot_y))
  ** ((( &( "pivot_x" ) )) # Int |-> (pivot_x))
  ** (intArray.full coords_pre (2 * n_pre) flat_cur)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def partition_points_safety_wit_20 : Prop :=
  forall (pts_l : (List point)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (pivot_x : Int) (pivot_y : Int) (j : Int) (i : Int) (flat_cur : (List Int)) (pts_cur : (List point)) (PreH1 : (j >= high_pre)) (PreH2 : ((0 : Int) <= low_pre)) (PreH3 : (low_pre <= high_pre)) (PreH4 : (high_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((low_pre - 1) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : ((Zlength (pts_l)) = n_pre)) (PreH11 : ((Zlength (pts_cur)) = n_pre)) (PreH12 : ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point)))) (PreH13 : (FlatPoints flat_cur pts_cur)) (PreH14 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur)))) (PreH15 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur)))) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur)))) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur)))) (PreH18 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH19 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH20 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH21 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH22 : (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j)) ,
  ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "pivot_y" ) )) # Int |-> (pivot_y))
  ** ((( &( "pivot_x" ) )) # Int |-> (pivot_x))
  ** (intArray.full coords_pre (2 * n_pre) flat_cur)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def partition_points_safety_wit_21 : Prop :=
  forall (pts_l : (List point)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (pivot_x : Int) (pivot_y : Int) (j : Int) (i : Int) (flat_cur : (List Int)) (pts_cur : (List point)) (PreH1 : (FlatPoints (point_swap_flat (flat_cur) ((i + 1)) (high_pre)) (point_swap_points (pts_cur) ((i + 1)) (high_pre)))) (PreH2 : (PointPermutation pts_cur (point_swap_points (pts_cur) ((i + 1)) (high_pre)))) (PreH3 : (j >= high_pre)) (PreH4 : ((0 : Int) <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((0 : Int) <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((low_pre - 1) <= i)) (PreH10 : (i < j)) (PreH11 : (j <= high_pre)) (PreH12 : ((Zlength (pts_l)) = n_pre)) (PreH13 : ((Zlength (pts_cur)) = n_pre)) (PreH14 : ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point)))) (PreH15 : (FlatPoints flat_cur pts_cur)) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur)))) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur)))) (PreH18 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur)))) (PreH19 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur)))) (PreH20 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH21 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH22 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH23 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH24 : (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j)) ,
  (intArray.full coords_pre (2 * n_pre) (point_swap_flat (flat_cur) ((i + 1)) (high_pre)))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "pivot_y" ) )) # Int |-> (pivot_y))
  ** ((( &( "pivot_x" ) )) # Int |-> (pivot_x))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def partition_points_safety_wit_22 : Prop :=
  forall (pts_l : (List point)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (pivot_x : Int) (pivot_y : Int) (j : Int) (i : Int) (flat_cur : (List Int)) (pts_cur : (List point)) (PreH1 : (FlatPoints (point_swap_flat (flat_cur) ((i + 1)) (high_pre)) (point_swap_points (pts_cur) ((i + 1)) (high_pre)))) (PreH2 : (PointPermutation pts_cur (point_swap_points (pts_cur) ((i + 1)) (high_pre)))) (PreH3 : (j >= high_pre)) (PreH4 : ((0 : Int) <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((0 : Int) <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((low_pre - 1) <= i)) (PreH10 : (i < j)) (PreH11 : (j <= high_pre)) (PreH12 : ((Zlength (pts_l)) = n_pre)) (PreH13 : ((Zlength (pts_cur)) = n_pre)) (PreH14 : ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point)))) (PreH15 : (FlatPoints flat_cur pts_cur)) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur)))) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur)))) (PreH18 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur)))) (PreH19 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur)))) (PreH20 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH21 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH22 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH23 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH24 : (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j)) ,
  (intArray.full coords_pre (2 * n_pre) (point_swap_flat (flat_cur) ((i + 1)) (high_pre)))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "pivot_y" ) )) # Int |-> (pivot_y))
  ** ((( &( "pivot_x" ) )) # Int |-> (pivot_x))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def partition_points_entail_wit_1 : Prop :=
  (
forall (pts_l : (List point)) (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (PreH1 : ((0 : Int) <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : (FlatPoints flat pts_l)) (PreH8 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH9 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH10 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH11 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  (intArray.full coords_pre (2 * n_pre) flat)
|--
  EX flat_cur : (List Int), EX pts_cur : (List point),
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre <= high_pre) ” &&
  “ (high_pre < n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ ((low_pre - 1) <= (low_pre - 1)) ” &&
  “ ((low_pre - 1) < low_pre) ” &&
  “ (low_pre <= high_pre) ” &&
  “ ((Zlength (pts_l)) = n_pre) ” &&
  “ ((Zlength (pts_cur)) = n_pre) ” &&
  “ ((mk_point ((Znth (2 * high_pre) flat (0 : Int))) ((Znth ((2 * high_pre) + 1) flat (0 : Int)))) = (Znth (high_pre) (pts_cur) (default_point))) ” &&
  “ (FlatPoints flat_cur pts_cur) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur)))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur)))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur)))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur)))) ” &&
  “ (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point ((Znth (2 * high_pre) flat (0 : Int))) ((Znth ((2 * high_pre) + 1) flat (0 : Int)))) (low_pre - 1) low_pre) ”
  &&  (intArray.full coords_pre (2 * n_pre) flat_cur)
) \/
(
forall (pts_l : (List point)) (flat : (List Int)) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (PreH1 : ((0 : Int) <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : (FlatPoints flat pts_l)) (PreH8 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH9 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH10 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH11 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  TT && emp 
|--
  EX pts_cur : (List point),
  “ ((low_pre - 1) <= (low_pre - 1)) ” &&
  “ ((low_pre - 1) < low_pre) ” &&
  “ ((Zlength (pts_cur)) = (Zlength (pts_l))) ” &&
  “ ((mk_point ((Znth (2 * high_pre) flat (0 : Int))) ((Znth ((2 * high_pre) + 1) flat (0 : Int)))) = (Znth (high_pre) (pts_cur) (default_point))) ” &&
  “ (FlatPoints flat pts_cur) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur)))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur)))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur)))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur)))) ” &&
  “ (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point ((Znth (2 * high_pre) flat (0 : Int))) ((Znth ((2 * high_pre) + 1) flat (0 : Int)))) (low_pre - 1) low_pre) ”
  &&  emp
)

noncomputable def partition_points_entail_wit_2_1 : Prop :=
  (
forall (pts_l : (List point)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (pivot_x : Int) (pivot_y : Int) (j : Int) (i : Int) (retval : Int) (flat_cur_2 : (List Int)) (pts_cur_2 : (List point)) (PreH1 : (FlatPoints (point_swap_flat (flat_cur_2) ((i + 1)) (j)) (point_swap_points (pts_cur_2) ((i + 1)) (j)))) (PreH2 : (PointPermutation pts_cur_2 (point_swap_points (pts_cur_2) ((i + 1)) (j)))) (PreH3 : (retval <= (0 : Int))) (PreH4 : (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point ((Znth (2 * j) flat_cur_2 (0 : Int))) ((Znth ((2 * j) + 1) flat_cur_2 (0 : Int)))) (mk_point (pivot_x) (pivot_y)) retval)) (PreH5 : (j < high_pre)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n_pre)) (PreH9 : ((0 : Int) <= n_pre)) (PreH10 : (n_pre <= 50000)) (PreH11 : ((low_pre - 1) <= i)) (PreH12 : (i < j)) (PreH13 : (j <= high_pre)) (PreH14 : ((Zlength (pts_l)) = n_pre)) (PreH15 : ((Zlength (pts_cur_2)) = n_pre)) (PreH16 : ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur_2) (default_point)))) (PreH17 : (FlatPoints flat_cur_2 pts_cur_2)) (PreH18 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur_2)))) (PreH19 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur_2)))) (PreH20 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur_2)))) (PreH21 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur_2)))) (PreH22 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur_2))))) (PreH23 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur_2))))) (PreH24 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur_2))))) (PreH25 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur_2))))) (PreH26 : (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur_2 low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j)) ,
  (intArray.full coords_pre (2 * n_pre) (point_swap_flat (flat_cur_2) ((i + 1)) (j)))
|--
  EX flat_cur : (List Int), EX pts_cur : (List point),
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre <= high_pre) ” &&
  “ (high_pre < n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ ((low_pre - 1) <= (i + 1)) ” &&
  “ ((i + 1) < (j + 1)) ” &&
  “ ((j + 1) <= high_pre) ” &&
  “ ((Zlength (pts_l)) = n_pre) ” &&
  “ ((Zlength (pts_cur)) = n_pre) ” &&
  “ ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point))) ” &&
  “ (FlatPoints flat_cur pts_cur) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur)))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur)))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur)))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur)))) ” &&
  “ (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) (i + 1) (j + 1)) ”
  &&  (intArray.full coords_pre (2 * n_pre) flat_cur)
) \/
(
forall (pts_l : (List point)) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (pivot_x : Int) (pivot_y : Int) (j : Int) (i : Int) (retval : Int) (flat_cur_2 : (List Int)) (pts_cur_2 : (List point)) (PreH1 : (FlatPoints (point_swap_flat (flat_cur_2) ((i + 1)) (j)) (point_swap_points (pts_cur_2) ((i + 1)) (j)))) (PreH2 : (PointPermutation pts_cur_2 (point_swap_points (pts_cur_2) ((i + 1)) (j)))) (PreH3 : (retval <= (0 : Int))) (PreH4 : (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point ((Znth (2 * j) flat_cur_2 (0 : Int))) ((Znth ((2 * j) + 1) flat_cur_2 (0 : Int)))) (mk_point (pivot_x) (pivot_y)) retval)) (PreH5 : (j < high_pre)) (PreH6 : ((0 : Int) <= low_pre)) (PreH7 : (low_pre <= high_pre)) (PreH8 : (high_pre < n_pre)) (PreH9 : ((0 : Int) <= n_pre)) (PreH10 : (n_pre <= 50000)) (PreH11 : ((low_pre - 1) <= i)) (PreH12 : (i < j)) (PreH13 : (j <= high_pre)) (PreH14 : ((Zlength (pts_l)) = n_pre)) (PreH15 : ((Zlength (pts_cur_2)) = n_pre)) (PreH16 : ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur_2) (default_point)))) (PreH17 : (FlatPoints flat_cur_2 pts_cur_2)) (PreH18 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur_2)))) (PreH19 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur_2)))) (PreH20 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur_2)))) (PreH21 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur_2)))) (PreH22 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur_2))))) (PreH23 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur_2))))) (PreH24 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur_2))))) (PreH25 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur_2))))) (PreH26 : (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur_2 low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j)) ,
  TT && emp 
|--
  EX pts_cur : (List point),
  “ ((low_pre - 1) <= (i + 1)) ” &&
  “ ((i + 1) < (j + 1)) ” &&
  “ ((j + 1) <= high_pre) ” &&
  “ ((Zlength (pts_cur)) = (Zlength (pts_l))) ” &&
  “ ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point))) ” &&
  “ (FlatPoints (point_swap_flat (flat_cur_2) ((i + 1)) (j)) pts_cur) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur)))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur)))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur)))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur)))) ” &&
  “ (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) (i + 1) (j + 1)) ”
  &&  emp
)

noncomputable def partition_points_entail_wit_2_2 : Prop :=
  (
forall (pts_l : (List point)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (pivot_x : Int) (pivot_y : Int) (j : Int) (i : Int) (retval : Int) (flat_cur_2 : (List Int)) (pts_cur_2 : (List point)) (PreH1 : (retval > (0 : Int))) (PreH2 : (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point ((Znth (2 * j) flat_cur_2 (0 : Int))) ((Znth ((2 * j) + 1) flat_cur_2 (0 : Int)))) (mk_point (pivot_x) (pivot_y)) retval)) (PreH3 : (j < high_pre)) (PreH4 : ((0 : Int) <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((0 : Int) <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((low_pre - 1) <= i)) (PreH10 : (i < j)) (PreH11 : (j <= high_pre)) (PreH12 : ((Zlength (pts_l)) = n_pre)) (PreH13 : ((Zlength (pts_cur_2)) = n_pre)) (PreH14 : ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur_2) (default_point)))) (PreH15 : (FlatPoints flat_cur_2 pts_cur_2)) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur_2)))) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur_2)))) (PreH18 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur_2)))) (PreH19 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur_2)))) (PreH20 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur_2))))) (PreH21 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur_2))))) (PreH22 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur_2))))) (PreH23 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur_2))))) (PreH24 : (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur_2 low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j)) ,
  (intArray.full coords_pre (2 * n_pre) flat_cur_2)
|--
  EX flat_cur : (List Int), EX pts_cur : (List point),
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre <= high_pre) ” &&
  “ (high_pre < n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ ((low_pre - 1) <= i) ” &&
  “ (i < (j + 1)) ” &&
  “ ((j + 1) <= high_pre) ” &&
  “ ((Zlength (pts_l)) = n_pre) ” &&
  “ ((Zlength (pts_cur)) = n_pre) ” &&
  “ ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point))) ” &&
  “ (FlatPoints flat_cur pts_cur) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur)))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur)))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur)))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur)))) ” &&
  “ (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i (j + 1)) ”
  &&  (intArray.full coords_pre (2 * n_pre) flat_cur)
) \/
(
forall (pts_l : (List point)) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (pivot_x : Int) (pivot_y : Int) (j : Int) (i : Int) (retval : Int) (flat_cur_2 : (List Int)) (pts_cur_2 : (List point)) (PreH1 : (retval > (0 : Int))) (PreH2 : (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point ((Znth (2 * j) flat_cur_2 (0 : Int))) ((Znth ((2 * j) + 1) flat_cur_2 (0 : Int)))) (mk_point (pivot_x) (pivot_y)) retval)) (PreH3 : (j < high_pre)) (PreH4 : ((0 : Int) <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((0 : Int) <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((low_pre - 1) <= i)) (PreH10 : (i < j)) (PreH11 : (j <= high_pre)) (PreH12 : ((Zlength (pts_l)) = n_pre)) (PreH13 : ((Zlength (pts_cur_2)) = n_pre)) (PreH14 : ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur_2) (default_point)))) (PreH15 : (FlatPoints flat_cur_2 pts_cur_2)) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur_2)))) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur_2)))) (PreH18 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur_2)))) (PreH19 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur_2)))) (PreH20 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur_2))))) (PreH21 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur_2))))) (PreH22 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur_2))))) (PreH23 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur_2))))) (PreH24 : (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur_2 low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j)) ,
  TT && emp 
|--
  EX pts_cur : (List point),
  “ (i < (j + 1)) ” &&
  “ ((j + 1) <= high_pre) ” &&
  “ ((Zlength (pts_cur)) = (Zlength (pts_l))) ” &&
  “ ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point))) ” &&
  “ (FlatPoints flat_cur_2 pts_cur) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur)))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur)))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur)))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur)))) ” &&
  “ (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i (j + 1)) ”
  &&  emp
)

noncomputable def partition_points_return_wit_1 : Prop :=
  (
forall (pts_l : (List point)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (pivot_x : Int) (pivot_y : Int) (j : Int) (i : Int) (flat_cur : (List Int)) (pts_cur : (List point)) (PreH1 : (FlatPoints (point_swap_flat (flat_cur) ((i + 1)) (high_pre)) (point_swap_points (pts_cur) ((i + 1)) (high_pre)))) (PreH2 : (PointPermutation pts_cur (point_swap_points (pts_cur) ((i + 1)) (high_pre)))) (PreH3 : (j >= high_pre)) (PreH4 : ((0 : Int) <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((0 : Int) <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((low_pre - 1) <= i)) (PreH10 : (i < j)) (PreH11 : (j <= high_pre)) (PreH12 : ((Zlength (pts_l)) = n_pre)) (PreH13 : ((Zlength (pts_cur)) = n_pre)) (PreH14 : ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point)))) (PreH15 : (FlatPoints flat_cur pts_cur)) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur)))) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur)))) (PreH18 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur)))) (PreH19 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur)))) (PreH20 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH21 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH22 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH23 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH24 : (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j)) ,
  (intArray.full coords_pre (2 * n_pre) (point_swap_flat (flat_cur) ((i + 1)) (high_pre)))
|--
  EX flat_out : (List Int), EX pts_out : (List point),
  “ (low_pre <= (i + 1)) ” &&
  “ ((i + 1) <= high_pre) ” &&
  “ (FlatPoints flat_out pts_out) ” &&
  “ (PointPermutation pts_l pts_out) ” &&
  “ (PointSameOutsideRange pts_l pts_out low_pre high_pre) ” &&
  “ (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out low_pre high_pre (i + 1)) ”
  &&  (intArray.full coords_pre (2 * n_pre) flat_out)
) \/
(
forall (pts_l : (List point)) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (pivot_x : Int) (pivot_y : Int) (j : Int) (i : Int) (flat_cur : (List Int)) (pts_cur : (List point)) (PreH1 : (FlatPoints (point_swap_flat (flat_cur) ((i + 1)) (high_pre)) (point_swap_points (pts_cur) ((i + 1)) (high_pre)))) (PreH2 : (PointPermutation pts_cur (point_swap_points (pts_cur) ((i + 1)) (high_pre)))) (PreH3 : (j >= high_pre)) (PreH4 : ((0 : Int) <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((0 : Int) <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((low_pre - 1) <= i)) (PreH10 : (i < j)) (PreH11 : (j <= high_pre)) (PreH12 : ((Zlength (pts_l)) = n_pre)) (PreH13 : ((Zlength (pts_cur)) = n_pre)) (PreH14 : ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point)))) (PreH15 : (FlatPoints flat_cur pts_cur)) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur)))) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur)))) (PreH18 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur)))) (PreH19 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur)))) (PreH20 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH21 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH22 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH23 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH24 : (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j)) ,
  TT && emp 
|--
  EX pts_out : (List point),
  “ (low_pre <= (i + 1)) ” &&
  “ ((i + 1) <= high_pre) ” &&
  “ (FlatPoints (point_swap_flat (flat_cur) ((i + 1)) (high_pre)) pts_out) ” &&
  “ (PointPermutation pts_l pts_out) ” &&
  “ (PointSameOutsideRange pts_l pts_out low_pre high_pre) ” &&
  “ (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out low_pre high_pre (i + 1)) ”
  &&  emp
)

noncomputable def partition_points_partial_solve_wit_1 : Prop :=
  forall (pts_l : (List point)) (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (PreH1 : ((0 : Int) <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : (FlatPoints flat pts_l)) (PreH8 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH9 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH10 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH11 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  (intArray.full coords_pre (2 * n_pre) flat)
|--
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre <= high_pre) ” &&
  “ (high_pre < n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ ((Zlength (pts_l)) = n_pre) ” &&
  “ (FlatPoints flat pts_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l)))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l)))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l)))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l)))) ”
  &&  (((coords_pre + ((2 * high_pre) * sizeof(INT)))) # Int |-> ((Znth (2 * high_pre) flat (0 : Int))))
  ** (intArray.missing_i coords_pre (2 * high_pre) (0 : Int) (2 * n_pre) flat)

noncomputable def partition_points_partial_solve_wit_2 : Prop :=
  forall (pts_l : (List point)) (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (PreH1 : ((0 : Int) <= low_pre)) (PreH2 : (low_pre <= high_pre)) (PreH3 : (high_pre < n_pre)) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : (n_pre <= 50000)) (PreH6 : ((Zlength (pts_l)) = n_pre)) (PreH7 : (FlatPoints flat pts_l)) (PreH8 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH9 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH10 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH11 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  (intArray.full coords_pre (2 * n_pre) flat)
|--
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre <= high_pre) ” &&
  “ (high_pre < n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ ((Zlength (pts_l)) = n_pre) ” &&
  “ (FlatPoints flat pts_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l)))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l)))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l)))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l)))) ”
  &&  (((coords_pre + (((2 * high_pre) + 1) * sizeof(INT)))) # Int |-> ((Znth ((2 * high_pre) + 1) flat (0 : Int))))
  ** (intArray.missing_i coords_pre ((2 * high_pre) + 1) (0 : Int) (2 * n_pre) flat)

noncomputable def partition_points_partial_solve_wit_3 : Prop :=
  forall (pts_l : (List point)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (flat_cur : (List Int)) (pivot_x : Int) (pivot_y : Int) (pts_cur : (List point)) (j : Int) (i : Int) (PreH1 : (j < high_pre)) (PreH2 : ((0 : Int) <= low_pre)) (PreH3 : (low_pre <= high_pre)) (PreH4 : (high_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((low_pre - 1) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : ((Zlength (pts_l)) = n_pre)) (PreH11 : ((Zlength (pts_cur)) = n_pre)) (PreH12 : ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point)))) (PreH13 : (FlatPoints flat_cur pts_cur)) (PreH14 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur)))) (PreH15 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur)))) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur)))) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur)))) (PreH18 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH19 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH20 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH21 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH22 : (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j)) ,
  (intArray.full coords_pre (2 * n_pre) flat_cur)
|--
  “ (j < high_pre) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre <= high_pre) ” &&
  “ (high_pre < n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ ((low_pre - 1) <= i) ” &&
  “ (i < j) ” &&
  “ (j <= high_pre) ” &&
  “ ((Zlength (pts_l)) = n_pre) ” &&
  “ ((Zlength (pts_cur)) = n_pre) ” &&
  “ ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point))) ” &&
  “ (FlatPoints flat_cur pts_cur) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur)))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur)))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur)))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur)))) ” &&
  “ (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j) ”
  &&  (((coords_pre + ((2 * j) * sizeof(INT)))) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** (intArray.missing_i coords_pre (2 * j) (0 : Int) (2 * n_pre) flat_cur)

noncomputable def partition_points_partial_solve_wit_4 : Prop :=
  forall (pts_l : (List point)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (flat_cur : (List Int)) (pivot_x : Int) (pivot_y : Int) (pts_cur : (List point)) (j : Int) (i : Int) (PreH1 : (j < high_pre)) (PreH2 : ((0 : Int) <= low_pre)) (PreH3 : (low_pre <= high_pre)) (PreH4 : (high_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((low_pre - 1) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : ((Zlength (pts_l)) = n_pre)) (PreH11 : ((Zlength (pts_cur)) = n_pre)) (PreH12 : ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point)))) (PreH13 : (FlatPoints flat_cur pts_cur)) (PreH14 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur)))) (PreH15 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur)))) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur)))) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur)))) (PreH18 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH19 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH20 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH21 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH22 : (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j)) ,
  (intArray.full coords_pre (2 * n_pre) flat_cur)
|--
  “ (j < high_pre) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre <= high_pre) ” &&
  “ (high_pre < n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ ((low_pre - 1) <= i) ” &&
  “ (i < j) ” &&
  “ (j <= high_pre) ” &&
  “ ((Zlength (pts_l)) = n_pre) ” &&
  “ ((Zlength (pts_cur)) = n_pre) ” &&
  “ ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point))) ” &&
  “ (FlatPoints flat_cur pts_cur) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur)))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur)))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur)))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur)))) ” &&
  “ (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j) ”
  &&  (((coords_pre + (((2 * j) + 1) * sizeof(INT)))) # Int |-> ((Znth ((2 * j) + 1) flat_cur (0 : Int))))
  ** (intArray.missing_i coords_pre ((2 * j) + 1) (0 : Int) (2 * n_pre) flat_cur)

noncomputable def partition_points_partial_solve_wit_5_pure : Prop :=
  (
forall (pts_l : (List point)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (flat_cur : (List Int)) (pivot_x : Int) (pivot_y : Int) (pts_cur : (List point)) (j : Int) (i : Int) (PreH1 : (j < high_pre)) (PreH2 : ((0 : Int) <= low_pre)) (PreH3 : (low_pre <= high_pre)) (PreH4 : (high_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((low_pre - 1) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : ((Zlength (pts_l)) = n_pre)) (PreH11 : ((Zlength (pts_cur)) = n_pre)) (PreH12 : ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point)))) (PreH13 : (FlatPoints flat_cur pts_cur)) (PreH14 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur)))) (PreH15 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur)))) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur)))) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur)))) (PreH18 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH19 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH20 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH21 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH22 : (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j)) ,
  ((( &( "c" ) )) # Int |->_)
  ** (intArray.full coords_pre (2 * n_pre) flat_cur)
  ** ((( &( "ay" ) )) # Int |-> ((Znth ((2 * j) + 1) flat_cur (0 : Int))))
  ** ((( &( "ax" ) )) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pivot_y" ) )) # Int |-> (pivot_y))
  ** ((( &( "pivot_x" ) )) # Int |-> (pivot_x))
|--
  “ (pivot_y <= 10000) ” &&
  “ ((-10000) <= pivot_y) ” &&
  “ (pivot_x <= 10000) ” &&
  “ ((-10000) <= pivot_x) ” &&
  “ ((Znth ((2 * j) + 1) flat_cur (0 : Int)) <= 10000) ” &&
  “ ((-10000) <= (Znth ((2 * j) + 1) flat_cur (0 : Int))) ” &&
  “ ((Znth (2 * j) flat_cur (0 : Int)) <= 10000) ” &&
  “ ((-10000) <= (Znth (2 * j) flat_cur (0 : Int))) ” &&
  “ (gy_pre <= 10000) ” &&
  “ ((-10000) <= gy_pre) ” &&
  “ (gx_pre <= 10000) ” &&
  “ ((-10000) <= gx_pre) ”
) \/
(
forall (pts_l : (List point)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (flat_cur : (List Int)) (pivot_x : Int) (pivot_y : Int) (pts_cur : (List point)) (j : Int) (i : Int) (PreH1 : (pivot_x <= INT_MAX)) (PreH2 : (pivot_y <= INT_MAX)) (PreH3 : (j <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (gy_pre <= INT_MAX)) (PreH6 : (gx_pre <= INT_MAX)) (PreH7 : (high_pre <= INT_MAX)) (PreH8 : (low_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : ((Znth (2 * j) flat_cur (0 : Int)) <= INT_MAX)) (PreH11 : ((Znth ((2 * j) + 1) flat_cur (0 : Int)) <= INT_MAX)) (PreH12 : (pivot_x >= INT_MIN)) (PreH13 : (pivot_y >= INT_MIN)) (PreH14 : (j >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (gy_pre >= INT_MIN)) (PreH17 : (gx_pre >= INT_MIN)) (PreH18 : (high_pre >= INT_MIN)) (PreH19 : (low_pre >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : ((Znth (2 * j) flat_cur (0 : Int)) >= INT_MIN)) (PreH22 : ((Znth ((2 * j) + 1) flat_cur (0 : Int)) >= INT_MIN)) (PreH23 : (j < high_pre)) (PreH24 : ((0 : Int) <= low_pre)) (PreH25 : (low_pre <= high_pre)) (PreH26 : (high_pre < n_pre)) (PreH27 : ((0 : Int) <= n_pre)) (PreH28 : (n_pre <= 50000)) (PreH29 : ((low_pre - 1) <= i)) (PreH30 : (i < j)) (PreH31 : (j <= high_pre)) (PreH32 : ((Zlength (pts_l)) = n_pre)) (PreH33 : ((Zlength (pts_cur)) = n_pre)) (PreH34 : ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point)))) (PreH35 : (FlatPoints flat_cur pts_cur)) (PreH36 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur)))) (PreH37 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur)))) (PreH38 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur)))) (PreH39 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur)))) (PreH40 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH41 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH42 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH43 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH44 : (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j)) ,
  ((( &( "c" ) )) # Int |->_)
  ** (intArray.full coords_pre (2 * n_pre) flat_cur)
  ** ((( &( "ay" ) )) # Int |-> ((Znth ((2 * j) + 1) flat_cur (0 : Int))))
  ** ((( &( "ax" ) )) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pivot_y" ) )) # Int |-> (pivot_y))
  ** ((( &( "pivot_x" ) )) # Int |-> (pivot_x))
|--
  “ ((-10000) <= gx_pre) ” &&
  “ (gx_pre <= 10000) ” &&
  “ ((-10000) <= gy_pre) ” &&
  “ (gy_pre <= 10000) ” &&
  “ ((-10000) <= (Znth (2 * j) flat_cur (0 : Int))) ” &&
  “ ((Znth (2 * j) flat_cur (0 : Int)) <= 10000) ” &&
  “ ((-10000) <= (Znth ((2 * j) + 1) flat_cur (0 : Int))) ” &&
  “ ((Znth ((2 * j) + 1) flat_cur (0 : Int)) <= 10000) ” &&
  “ ((-10000) <= pivot_x) ” &&
  “ (pivot_x <= 10000) ” &&
  “ ((-10000) <= pivot_y) ” &&
  “ (pivot_y <= 10000) ”
)

noncomputable def partition_points_partial_solve_wit_5_pure_split_goal_1 : Prop :=
  forall (pts_l : (List point)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (flat_cur : (List Int)) (pivot_x : Int) (pivot_y : Int) (pts_cur : (List point)) (j : Int) (i : Int) (PreH1 : (pivot_x <= INT_MAX)) (PreH2 : (pivot_y <= INT_MAX)) (PreH3 : (j <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (gy_pre <= INT_MAX)) (PreH6 : (gx_pre <= INT_MAX)) (PreH7 : (high_pre <= INT_MAX)) (PreH8 : (low_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : ((Znth (2 * j) flat_cur (0 : Int)) <= INT_MAX)) (PreH11 : ((Znth ((2 * j) + 1) flat_cur (0 : Int)) <= INT_MAX)) (PreH12 : (pivot_x >= INT_MIN)) (PreH13 : (pivot_y >= INT_MIN)) (PreH14 : (j >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (gy_pre >= INT_MIN)) (PreH17 : (gx_pre >= INT_MIN)) (PreH18 : (high_pre >= INT_MIN)) (PreH19 : (low_pre >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : ((Znth (2 * j) flat_cur (0 : Int)) >= INT_MIN)) (PreH22 : ((Znth ((2 * j) + 1) flat_cur (0 : Int)) >= INT_MIN)) (PreH23 : (j < high_pre)) (PreH24 : ((0 : Int) <= low_pre)) (PreH25 : (low_pre <= high_pre)) (PreH26 : (high_pre < n_pre)) (PreH27 : ((0 : Int) <= n_pre)) (PreH28 : (n_pre <= 50000)) (PreH29 : ((low_pre - 1) <= i)) (PreH30 : (i < j)) (PreH31 : (j <= high_pre)) (PreH32 : ((Zlength (pts_l)) = n_pre)) (PreH33 : ((Zlength (pts_cur)) = n_pre)) (PreH34 : ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point)))) (PreH35 : (FlatPoints flat_cur pts_cur)) (PreH36 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur)))) (PreH37 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur)))) (PreH38 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur)))) (PreH39 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur)))) (PreH40 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH41 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH42 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH43 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH44 : (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j)) ,
  ((( &( "c" ) )) # Int |->_)
  ** (intArray.full coords_pre (2 * n_pre) flat_cur)
  ** ((( &( "ay" ) )) # Int |-> ((Znth ((2 * j) + 1) flat_cur (0 : Int))))
  ** ((( &( "ax" ) )) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pivot_y" ) )) # Int |-> (pivot_y))
  ** ((( &( "pivot_x" ) )) # Int |-> (pivot_x))
|--
  “ ((-10000) <= gx_pre) ”

noncomputable def partition_points_partial_solve_wit_5_pure_split_goal_2 : Prop :=
  forall (pts_l : (List point)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (flat_cur : (List Int)) (pivot_x : Int) (pivot_y : Int) (pts_cur : (List point)) (j : Int) (i : Int) (PreH1 : (pivot_x <= INT_MAX)) (PreH2 : (pivot_y <= INT_MAX)) (PreH3 : (j <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (gy_pre <= INT_MAX)) (PreH6 : (gx_pre <= INT_MAX)) (PreH7 : (high_pre <= INT_MAX)) (PreH8 : (low_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : ((Znth (2 * j) flat_cur (0 : Int)) <= INT_MAX)) (PreH11 : ((Znth ((2 * j) + 1) flat_cur (0 : Int)) <= INT_MAX)) (PreH12 : (pivot_x >= INT_MIN)) (PreH13 : (pivot_y >= INT_MIN)) (PreH14 : (j >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (gy_pre >= INT_MIN)) (PreH17 : (gx_pre >= INT_MIN)) (PreH18 : (high_pre >= INT_MIN)) (PreH19 : (low_pre >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : ((Znth (2 * j) flat_cur (0 : Int)) >= INT_MIN)) (PreH22 : ((Znth ((2 * j) + 1) flat_cur (0 : Int)) >= INT_MIN)) (PreH23 : (j < high_pre)) (PreH24 : ((0 : Int) <= low_pre)) (PreH25 : (low_pre <= high_pre)) (PreH26 : (high_pre < n_pre)) (PreH27 : ((0 : Int) <= n_pre)) (PreH28 : (n_pre <= 50000)) (PreH29 : ((low_pre - 1) <= i)) (PreH30 : (i < j)) (PreH31 : (j <= high_pre)) (PreH32 : ((Zlength (pts_l)) = n_pre)) (PreH33 : ((Zlength (pts_cur)) = n_pre)) (PreH34 : ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point)))) (PreH35 : (FlatPoints flat_cur pts_cur)) (PreH36 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur)))) (PreH37 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur)))) (PreH38 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur)))) (PreH39 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur)))) (PreH40 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH41 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH42 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH43 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH44 : (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j)) ,
  ((( &( "c" ) )) # Int |->_)
  ** (intArray.full coords_pre (2 * n_pre) flat_cur)
  ** ((( &( "ay" ) )) # Int |-> ((Znth ((2 * j) + 1) flat_cur (0 : Int))))
  ** ((( &( "ax" ) )) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pivot_y" ) )) # Int |-> (pivot_y))
  ** ((( &( "pivot_x" ) )) # Int |-> (pivot_x))
|--
  “ (gx_pre <= 10000) ”

noncomputable def partition_points_partial_solve_wit_5_pure_split_goal_3 : Prop :=
  forall (pts_l : (List point)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (flat_cur : (List Int)) (pivot_x : Int) (pivot_y : Int) (pts_cur : (List point)) (j : Int) (i : Int) (PreH1 : (pivot_x <= INT_MAX)) (PreH2 : (pivot_y <= INT_MAX)) (PreH3 : (j <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (gy_pre <= INT_MAX)) (PreH6 : (gx_pre <= INT_MAX)) (PreH7 : (high_pre <= INT_MAX)) (PreH8 : (low_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : ((Znth (2 * j) flat_cur (0 : Int)) <= INT_MAX)) (PreH11 : ((Znth ((2 * j) + 1) flat_cur (0 : Int)) <= INT_MAX)) (PreH12 : (pivot_x >= INT_MIN)) (PreH13 : (pivot_y >= INT_MIN)) (PreH14 : (j >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (gy_pre >= INT_MIN)) (PreH17 : (gx_pre >= INT_MIN)) (PreH18 : (high_pre >= INT_MIN)) (PreH19 : (low_pre >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : ((Znth (2 * j) flat_cur (0 : Int)) >= INT_MIN)) (PreH22 : ((Znth ((2 * j) + 1) flat_cur (0 : Int)) >= INT_MIN)) (PreH23 : (j < high_pre)) (PreH24 : ((0 : Int) <= low_pre)) (PreH25 : (low_pre <= high_pre)) (PreH26 : (high_pre < n_pre)) (PreH27 : ((0 : Int) <= n_pre)) (PreH28 : (n_pre <= 50000)) (PreH29 : ((low_pre - 1) <= i)) (PreH30 : (i < j)) (PreH31 : (j <= high_pre)) (PreH32 : ((Zlength (pts_l)) = n_pre)) (PreH33 : ((Zlength (pts_cur)) = n_pre)) (PreH34 : ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point)))) (PreH35 : (FlatPoints flat_cur pts_cur)) (PreH36 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur)))) (PreH37 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur)))) (PreH38 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur)))) (PreH39 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur)))) (PreH40 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH41 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH42 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH43 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH44 : (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j)) ,
  ((( &( "c" ) )) # Int |->_)
  ** (intArray.full coords_pre (2 * n_pre) flat_cur)
  ** ((( &( "ay" ) )) # Int |-> ((Znth ((2 * j) + 1) flat_cur (0 : Int))))
  ** ((( &( "ax" ) )) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pivot_y" ) )) # Int |-> (pivot_y))
  ** ((( &( "pivot_x" ) )) # Int |-> (pivot_x))
|--
  “ ((-10000) <= gy_pre) ”

noncomputable def partition_points_partial_solve_wit_5_pure_split_goal_4 : Prop :=
  forall (pts_l : (List point)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (flat_cur : (List Int)) (pivot_x : Int) (pivot_y : Int) (pts_cur : (List point)) (j : Int) (i : Int) (PreH1 : (pivot_x <= INT_MAX)) (PreH2 : (pivot_y <= INT_MAX)) (PreH3 : (j <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (gy_pre <= INT_MAX)) (PreH6 : (gx_pre <= INT_MAX)) (PreH7 : (high_pre <= INT_MAX)) (PreH8 : (low_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : ((Znth (2 * j) flat_cur (0 : Int)) <= INT_MAX)) (PreH11 : ((Znth ((2 * j) + 1) flat_cur (0 : Int)) <= INT_MAX)) (PreH12 : (pivot_x >= INT_MIN)) (PreH13 : (pivot_y >= INT_MIN)) (PreH14 : (j >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (gy_pre >= INT_MIN)) (PreH17 : (gx_pre >= INT_MIN)) (PreH18 : (high_pre >= INT_MIN)) (PreH19 : (low_pre >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : ((Znth (2 * j) flat_cur (0 : Int)) >= INT_MIN)) (PreH22 : ((Znth ((2 * j) + 1) flat_cur (0 : Int)) >= INT_MIN)) (PreH23 : (j < high_pre)) (PreH24 : ((0 : Int) <= low_pre)) (PreH25 : (low_pre <= high_pre)) (PreH26 : (high_pre < n_pre)) (PreH27 : ((0 : Int) <= n_pre)) (PreH28 : (n_pre <= 50000)) (PreH29 : ((low_pre - 1) <= i)) (PreH30 : (i < j)) (PreH31 : (j <= high_pre)) (PreH32 : ((Zlength (pts_l)) = n_pre)) (PreH33 : ((Zlength (pts_cur)) = n_pre)) (PreH34 : ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point)))) (PreH35 : (FlatPoints flat_cur pts_cur)) (PreH36 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur)))) (PreH37 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur)))) (PreH38 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur)))) (PreH39 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur)))) (PreH40 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH41 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH42 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH43 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH44 : (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j)) ,
  ((( &( "c" ) )) # Int |->_)
  ** (intArray.full coords_pre (2 * n_pre) flat_cur)
  ** ((( &( "ay" ) )) # Int |-> ((Znth ((2 * j) + 1) flat_cur (0 : Int))))
  ** ((( &( "ax" ) )) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pivot_y" ) )) # Int |-> (pivot_y))
  ** ((( &( "pivot_x" ) )) # Int |-> (pivot_x))
|--
  “ (gy_pre <= 10000) ”

noncomputable def partition_points_partial_solve_wit_5_pure_split_goal_5 : Prop :=
  forall (pts_l : (List point)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (flat_cur : (List Int)) (pivot_x : Int) (pivot_y : Int) (pts_cur : (List point)) (j : Int) (i : Int) (PreH1 : (pivot_x <= INT_MAX)) (PreH2 : (pivot_y <= INT_MAX)) (PreH3 : (j <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (gy_pre <= INT_MAX)) (PreH6 : (gx_pre <= INT_MAX)) (PreH7 : (high_pre <= INT_MAX)) (PreH8 : (low_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : ((Znth (2 * j) flat_cur (0 : Int)) <= INT_MAX)) (PreH11 : ((Znth ((2 * j) + 1) flat_cur (0 : Int)) <= INT_MAX)) (PreH12 : (pivot_x >= INT_MIN)) (PreH13 : (pivot_y >= INT_MIN)) (PreH14 : (j >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (gy_pre >= INT_MIN)) (PreH17 : (gx_pre >= INT_MIN)) (PreH18 : (high_pre >= INT_MIN)) (PreH19 : (low_pre >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : ((Znth (2 * j) flat_cur (0 : Int)) >= INT_MIN)) (PreH22 : ((Znth ((2 * j) + 1) flat_cur (0 : Int)) >= INT_MIN)) (PreH23 : (j < high_pre)) (PreH24 : ((0 : Int) <= low_pre)) (PreH25 : (low_pre <= high_pre)) (PreH26 : (high_pre < n_pre)) (PreH27 : ((0 : Int) <= n_pre)) (PreH28 : (n_pre <= 50000)) (PreH29 : ((low_pre - 1) <= i)) (PreH30 : (i < j)) (PreH31 : (j <= high_pre)) (PreH32 : ((Zlength (pts_l)) = n_pre)) (PreH33 : ((Zlength (pts_cur)) = n_pre)) (PreH34 : ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point)))) (PreH35 : (FlatPoints flat_cur pts_cur)) (PreH36 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur)))) (PreH37 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur)))) (PreH38 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur)))) (PreH39 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur)))) (PreH40 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH41 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH42 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH43 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH44 : (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j)) ,
  ((( &( "c" ) )) # Int |->_)
  ** (intArray.full coords_pre (2 * n_pre) flat_cur)
  ** ((( &( "ay" ) )) # Int |-> ((Znth ((2 * j) + 1) flat_cur (0 : Int))))
  ** ((( &( "ax" ) )) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pivot_y" ) )) # Int |-> (pivot_y))
  ** ((( &( "pivot_x" ) )) # Int |-> (pivot_x))
|--
  “ ((-10000) <= (Znth (2 * j) flat_cur (0 : Int))) ”

noncomputable def partition_points_partial_solve_wit_5_pure_split_goal_6 : Prop :=
  forall (pts_l : (List point)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (flat_cur : (List Int)) (pivot_x : Int) (pivot_y : Int) (pts_cur : (List point)) (j : Int) (i : Int) (PreH1 : (pivot_x <= INT_MAX)) (PreH2 : (pivot_y <= INT_MAX)) (PreH3 : (j <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (gy_pre <= INT_MAX)) (PreH6 : (gx_pre <= INT_MAX)) (PreH7 : (high_pre <= INT_MAX)) (PreH8 : (low_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : ((Znth (2 * j) flat_cur (0 : Int)) <= INT_MAX)) (PreH11 : ((Znth ((2 * j) + 1) flat_cur (0 : Int)) <= INT_MAX)) (PreH12 : (pivot_x >= INT_MIN)) (PreH13 : (pivot_y >= INT_MIN)) (PreH14 : (j >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (gy_pre >= INT_MIN)) (PreH17 : (gx_pre >= INT_MIN)) (PreH18 : (high_pre >= INT_MIN)) (PreH19 : (low_pre >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : ((Znth (2 * j) flat_cur (0 : Int)) >= INT_MIN)) (PreH22 : ((Znth ((2 * j) + 1) flat_cur (0 : Int)) >= INT_MIN)) (PreH23 : (j < high_pre)) (PreH24 : ((0 : Int) <= low_pre)) (PreH25 : (low_pre <= high_pre)) (PreH26 : (high_pre < n_pre)) (PreH27 : ((0 : Int) <= n_pre)) (PreH28 : (n_pre <= 50000)) (PreH29 : ((low_pre - 1) <= i)) (PreH30 : (i < j)) (PreH31 : (j <= high_pre)) (PreH32 : ((Zlength (pts_l)) = n_pre)) (PreH33 : ((Zlength (pts_cur)) = n_pre)) (PreH34 : ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point)))) (PreH35 : (FlatPoints flat_cur pts_cur)) (PreH36 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur)))) (PreH37 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur)))) (PreH38 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur)))) (PreH39 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur)))) (PreH40 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH41 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH42 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH43 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH44 : (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j)) ,
  ((( &( "c" ) )) # Int |->_)
  ** (intArray.full coords_pre (2 * n_pre) flat_cur)
  ** ((( &( "ay" ) )) # Int |-> ((Znth ((2 * j) + 1) flat_cur (0 : Int))))
  ** ((( &( "ax" ) )) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pivot_y" ) )) # Int |-> (pivot_y))
  ** ((( &( "pivot_x" ) )) # Int |-> (pivot_x))
|--
  “ ((Znth (2 * j) flat_cur (0 : Int)) <= 10000) ”

noncomputable def partition_points_partial_solve_wit_5_pure_split_goal_7 : Prop :=
  forall (pts_l : (List point)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (flat_cur : (List Int)) (pivot_x : Int) (pivot_y : Int) (pts_cur : (List point)) (j : Int) (i : Int) (PreH1 : (pivot_x <= INT_MAX)) (PreH2 : (pivot_y <= INT_MAX)) (PreH3 : (j <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (gy_pre <= INT_MAX)) (PreH6 : (gx_pre <= INT_MAX)) (PreH7 : (high_pre <= INT_MAX)) (PreH8 : (low_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : ((Znth (2 * j) flat_cur (0 : Int)) <= INT_MAX)) (PreH11 : ((Znth ((2 * j) + 1) flat_cur (0 : Int)) <= INT_MAX)) (PreH12 : (pivot_x >= INT_MIN)) (PreH13 : (pivot_y >= INT_MIN)) (PreH14 : (j >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (gy_pre >= INT_MIN)) (PreH17 : (gx_pre >= INT_MIN)) (PreH18 : (high_pre >= INT_MIN)) (PreH19 : (low_pre >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : ((Znth (2 * j) flat_cur (0 : Int)) >= INT_MIN)) (PreH22 : ((Znth ((2 * j) + 1) flat_cur (0 : Int)) >= INT_MIN)) (PreH23 : (j < high_pre)) (PreH24 : ((0 : Int) <= low_pre)) (PreH25 : (low_pre <= high_pre)) (PreH26 : (high_pre < n_pre)) (PreH27 : ((0 : Int) <= n_pre)) (PreH28 : (n_pre <= 50000)) (PreH29 : ((low_pre - 1) <= i)) (PreH30 : (i < j)) (PreH31 : (j <= high_pre)) (PreH32 : ((Zlength (pts_l)) = n_pre)) (PreH33 : ((Zlength (pts_cur)) = n_pre)) (PreH34 : ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point)))) (PreH35 : (FlatPoints flat_cur pts_cur)) (PreH36 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur)))) (PreH37 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur)))) (PreH38 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur)))) (PreH39 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur)))) (PreH40 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH41 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH42 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH43 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH44 : (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j)) ,
  ((( &( "c" ) )) # Int |->_)
  ** (intArray.full coords_pre (2 * n_pre) flat_cur)
  ** ((( &( "ay" ) )) # Int |-> ((Znth ((2 * j) + 1) flat_cur (0 : Int))))
  ** ((( &( "ax" ) )) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pivot_y" ) )) # Int |-> (pivot_y))
  ** ((( &( "pivot_x" ) )) # Int |-> (pivot_x))
|--
  “ ((-10000) <= (Znth ((2 * j) + 1) flat_cur (0 : Int))) ”

noncomputable def partition_points_partial_solve_wit_5_pure_split_goal_8 : Prop :=
  forall (pts_l : (List point)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (flat_cur : (List Int)) (pivot_x : Int) (pivot_y : Int) (pts_cur : (List point)) (j : Int) (i : Int) (PreH1 : (pivot_x <= INT_MAX)) (PreH2 : (pivot_y <= INT_MAX)) (PreH3 : (j <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (gy_pre <= INT_MAX)) (PreH6 : (gx_pre <= INT_MAX)) (PreH7 : (high_pre <= INT_MAX)) (PreH8 : (low_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : ((Znth (2 * j) flat_cur (0 : Int)) <= INT_MAX)) (PreH11 : ((Znth ((2 * j) + 1) flat_cur (0 : Int)) <= INT_MAX)) (PreH12 : (pivot_x >= INT_MIN)) (PreH13 : (pivot_y >= INT_MIN)) (PreH14 : (j >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (gy_pre >= INT_MIN)) (PreH17 : (gx_pre >= INT_MIN)) (PreH18 : (high_pre >= INT_MIN)) (PreH19 : (low_pre >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : ((Znth (2 * j) flat_cur (0 : Int)) >= INT_MIN)) (PreH22 : ((Znth ((2 * j) + 1) flat_cur (0 : Int)) >= INT_MIN)) (PreH23 : (j < high_pre)) (PreH24 : ((0 : Int) <= low_pre)) (PreH25 : (low_pre <= high_pre)) (PreH26 : (high_pre < n_pre)) (PreH27 : ((0 : Int) <= n_pre)) (PreH28 : (n_pre <= 50000)) (PreH29 : ((low_pre - 1) <= i)) (PreH30 : (i < j)) (PreH31 : (j <= high_pre)) (PreH32 : ((Zlength (pts_l)) = n_pre)) (PreH33 : ((Zlength (pts_cur)) = n_pre)) (PreH34 : ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point)))) (PreH35 : (FlatPoints flat_cur pts_cur)) (PreH36 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur)))) (PreH37 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur)))) (PreH38 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur)))) (PreH39 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur)))) (PreH40 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH41 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH42 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH43 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH44 : (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j)) ,
  ((( &( "c" ) )) # Int |->_)
  ** (intArray.full coords_pre (2 * n_pre) flat_cur)
  ** ((( &( "ay" ) )) # Int |-> ((Znth ((2 * j) + 1) flat_cur (0 : Int))))
  ** ((( &( "ax" ) )) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pivot_y" ) )) # Int |-> (pivot_y))
  ** ((( &( "pivot_x" ) )) # Int |-> (pivot_x))
|--
  “ ((Znth ((2 * j) + 1) flat_cur (0 : Int)) <= 10000) ”

noncomputable def partition_points_partial_solve_wit_5_pure_split_goal_9 : Prop :=
  forall (pts_l : (List point)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (flat_cur : (List Int)) (pivot_x : Int) (pivot_y : Int) (pts_cur : (List point)) (j : Int) (i : Int) (PreH1 : (pivot_x <= INT_MAX)) (PreH2 : (pivot_y <= INT_MAX)) (PreH3 : (j <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (gy_pre <= INT_MAX)) (PreH6 : (gx_pre <= INT_MAX)) (PreH7 : (high_pre <= INT_MAX)) (PreH8 : (low_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : ((Znth (2 * j) flat_cur (0 : Int)) <= INT_MAX)) (PreH11 : ((Znth ((2 * j) + 1) flat_cur (0 : Int)) <= INT_MAX)) (PreH12 : (pivot_x >= INT_MIN)) (PreH13 : (pivot_y >= INT_MIN)) (PreH14 : (j >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (gy_pre >= INT_MIN)) (PreH17 : (gx_pre >= INT_MIN)) (PreH18 : (high_pre >= INT_MIN)) (PreH19 : (low_pre >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : ((Znth (2 * j) flat_cur (0 : Int)) >= INT_MIN)) (PreH22 : ((Znth ((2 * j) + 1) flat_cur (0 : Int)) >= INT_MIN)) (PreH23 : (j < high_pre)) (PreH24 : ((0 : Int) <= low_pre)) (PreH25 : (low_pre <= high_pre)) (PreH26 : (high_pre < n_pre)) (PreH27 : ((0 : Int) <= n_pre)) (PreH28 : (n_pre <= 50000)) (PreH29 : ((low_pre - 1) <= i)) (PreH30 : (i < j)) (PreH31 : (j <= high_pre)) (PreH32 : ((Zlength (pts_l)) = n_pre)) (PreH33 : ((Zlength (pts_cur)) = n_pre)) (PreH34 : ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point)))) (PreH35 : (FlatPoints flat_cur pts_cur)) (PreH36 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur)))) (PreH37 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur)))) (PreH38 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur)))) (PreH39 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur)))) (PreH40 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH41 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH42 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH43 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH44 : (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j)) ,
  ((( &( "c" ) )) # Int |->_)
  ** (intArray.full coords_pre (2 * n_pre) flat_cur)
  ** ((( &( "ay" ) )) # Int |-> ((Znth ((2 * j) + 1) flat_cur (0 : Int))))
  ** ((( &( "ax" ) )) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pivot_y" ) )) # Int |-> (pivot_y))
  ** ((( &( "pivot_x" ) )) # Int |-> (pivot_x))
|--
  “ ((-10000) <= pivot_x) ”

noncomputable def partition_points_partial_solve_wit_5_pure_split_goal_10 : Prop :=
  forall (pts_l : (List point)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (flat_cur : (List Int)) (pivot_x : Int) (pivot_y : Int) (pts_cur : (List point)) (j : Int) (i : Int) (PreH1 : (pivot_x <= INT_MAX)) (PreH2 : (pivot_y <= INT_MAX)) (PreH3 : (j <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (gy_pre <= INT_MAX)) (PreH6 : (gx_pre <= INT_MAX)) (PreH7 : (high_pre <= INT_MAX)) (PreH8 : (low_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : ((Znth (2 * j) flat_cur (0 : Int)) <= INT_MAX)) (PreH11 : ((Znth ((2 * j) + 1) flat_cur (0 : Int)) <= INT_MAX)) (PreH12 : (pivot_x >= INT_MIN)) (PreH13 : (pivot_y >= INT_MIN)) (PreH14 : (j >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (gy_pre >= INT_MIN)) (PreH17 : (gx_pre >= INT_MIN)) (PreH18 : (high_pre >= INT_MIN)) (PreH19 : (low_pre >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : ((Znth (2 * j) flat_cur (0 : Int)) >= INT_MIN)) (PreH22 : ((Znth ((2 * j) + 1) flat_cur (0 : Int)) >= INT_MIN)) (PreH23 : (j < high_pre)) (PreH24 : ((0 : Int) <= low_pre)) (PreH25 : (low_pre <= high_pre)) (PreH26 : (high_pre < n_pre)) (PreH27 : ((0 : Int) <= n_pre)) (PreH28 : (n_pre <= 50000)) (PreH29 : ((low_pre - 1) <= i)) (PreH30 : (i < j)) (PreH31 : (j <= high_pre)) (PreH32 : ((Zlength (pts_l)) = n_pre)) (PreH33 : ((Zlength (pts_cur)) = n_pre)) (PreH34 : ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point)))) (PreH35 : (FlatPoints flat_cur pts_cur)) (PreH36 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur)))) (PreH37 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur)))) (PreH38 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur)))) (PreH39 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur)))) (PreH40 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH41 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH42 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH43 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH44 : (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j)) ,
  ((( &( "c" ) )) # Int |->_)
  ** (intArray.full coords_pre (2 * n_pre) flat_cur)
  ** ((( &( "ay" ) )) # Int |-> ((Znth ((2 * j) + 1) flat_cur (0 : Int))))
  ** ((( &( "ax" ) )) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pivot_y" ) )) # Int |-> (pivot_y))
  ** ((( &( "pivot_x" ) )) # Int |-> (pivot_x))
|--
  “ (pivot_x <= 10000) ”

noncomputable def partition_points_partial_solve_wit_5_pure_split_goal_11 : Prop :=
  forall (pts_l : (List point)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (flat_cur : (List Int)) (pivot_x : Int) (pivot_y : Int) (pts_cur : (List point)) (j : Int) (i : Int) (PreH1 : (pivot_x <= INT_MAX)) (PreH2 : (pivot_y <= INT_MAX)) (PreH3 : (j <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (gy_pre <= INT_MAX)) (PreH6 : (gx_pre <= INT_MAX)) (PreH7 : (high_pre <= INT_MAX)) (PreH8 : (low_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : ((Znth (2 * j) flat_cur (0 : Int)) <= INT_MAX)) (PreH11 : ((Znth ((2 * j) + 1) flat_cur (0 : Int)) <= INT_MAX)) (PreH12 : (pivot_x >= INT_MIN)) (PreH13 : (pivot_y >= INT_MIN)) (PreH14 : (j >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (gy_pre >= INT_MIN)) (PreH17 : (gx_pre >= INT_MIN)) (PreH18 : (high_pre >= INT_MIN)) (PreH19 : (low_pre >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : ((Znth (2 * j) flat_cur (0 : Int)) >= INT_MIN)) (PreH22 : ((Znth ((2 * j) + 1) flat_cur (0 : Int)) >= INT_MIN)) (PreH23 : (j < high_pre)) (PreH24 : ((0 : Int) <= low_pre)) (PreH25 : (low_pre <= high_pre)) (PreH26 : (high_pre < n_pre)) (PreH27 : ((0 : Int) <= n_pre)) (PreH28 : (n_pre <= 50000)) (PreH29 : ((low_pre - 1) <= i)) (PreH30 : (i < j)) (PreH31 : (j <= high_pre)) (PreH32 : ((Zlength (pts_l)) = n_pre)) (PreH33 : ((Zlength (pts_cur)) = n_pre)) (PreH34 : ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point)))) (PreH35 : (FlatPoints flat_cur pts_cur)) (PreH36 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur)))) (PreH37 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur)))) (PreH38 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur)))) (PreH39 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur)))) (PreH40 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH41 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH42 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH43 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH44 : (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j)) ,
  ((( &( "c" ) )) # Int |->_)
  ** (intArray.full coords_pre (2 * n_pre) flat_cur)
  ** ((( &( "ay" ) )) # Int |-> ((Znth ((2 * j) + 1) flat_cur (0 : Int))))
  ** ((( &( "ax" ) )) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pivot_y" ) )) # Int |-> (pivot_y))
  ** ((( &( "pivot_x" ) )) # Int |-> (pivot_x))
|--
  “ ((-10000) <= pivot_y) ”

noncomputable def partition_points_partial_solve_wit_5_pure_split_goal_12 : Prop :=
  forall (pts_l : (List point)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (flat_cur : (List Int)) (pivot_x : Int) (pivot_y : Int) (pts_cur : (List point)) (j : Int) (i : Int) (PreH1 : (pivot_x <= INT_MAX)) (PreH2 : (pivot_y <= INT_MAX)) (PreH3 : (j <= INT_MAX)) (PreH4 : (i <= INT_MAX)) (PreH5 : (gy_pre <= INT_MAX)) (PreH6 : (gx_pre <= INT_MAX)) (PreH7 : (high_pre <= INT_MAX)) (PreH8 : (low_pre <= INT_MAX)) (PreH9 : (n_pre <= INT_MAX)) (PreH10 : ((Znth (2 * j) flat_cur (0 : Int)) <= INT_MAX)) (PreH11 : ((Znth ((2 * j) + 1) flat_cur (0 : Int)) <= INT_MAX)) (PreH12 : (pivot_x >= INT_MIN)) (PreH13 : (pivot_y >= INT_MIN)) (PreH14 : (j >= INT_MIN)) (PreH15 : (i >= INT_MIN)) (PreH16 : (gy_pre >= INT_MIN)) (PreH17 : (gx_pre >= INT_MIN)) (PreH18 : (high_pre >= INT_MIN)) (PreH19 : (low_pre >= INT_MIN)) (PreH20 : (n_pre >= INT_MIN)) (PreH21 : ((Znth (2 * j) flat_cur (0 : Int)) >= INT_MIN)) (PreH22 : ((Znth ((2 * j) + 1) flat_cur (0 : Int)) >= INT_MIN)) (PreH23 : (j < high_pre)) (PreH24 : ((0 : Int) <= low_pre)) (PreH25 : (low_pre <= high_pre)) (PreH26 : (high_pre < n_pre)) (PreH27 : ((0 : Int) <= n_pre)) (PreH28 : (n_pre <= 50000)) (PreH29 : ((low_pre - 1) <= i)) (PreH30 : (i < j)) (PreH31 : (j <= high_pre)) (PreH32 : ((Zlength (pts_l)) = n_pre)) (PreH33 : ((Zlength (pts_cur)) = n_pre)) (PreH34 : ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point)))) (PreH35 : (FlatPoints flat_cur pts_cur)) (PreH36 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur)))) (PreH37 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur)))) (PreH38 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur)))) (PreH39 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur)))) (PreH40 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH41 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH42 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH43 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH44 : (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j)) ,
  ((( &( "c" ) )) # Int |->_)
  ** (intArray.full coords_pre (2 * n_pre) flat_cur)
  ** ((( &( "ay" ) )) # Int |-> ((Znth ((2 * j) + 1) flat_cur (0 : Int))))
  ** ((( &( "ax" ) )) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pivot_y" ) )) # Int |-> (pivot_y))
  ** ((( &( "pivot_x" ) )) # Int |-> (pivot_x))
|--
  “ (pivot_y <= 10000) ”

noncomputable def partition_points_partial_solve_wit_5_aux : Prop :=
  forall (pts_l : (List point)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (flat_cur : (List Int)) (pivot_x : Int) (pivot_y : Int) (pts_cur : (List point)) (j : Int) (i : Int) (PreH1 : (j < high_pre)) (PreH2 : ((0 : Int) <= low_pre)) (PreH3 : (low_pre <= high_pre)) (PreH4 : (high_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((low_pre - 1) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : ((Zlength (pts_l)) = n_pre)) (PreH11 : ((Zlength (pts_cur)) = n_pre)) (PreH12 : ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point)))) (PreH13 : (FlatPoints flat_cur pts_cur)) (PreH14 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur)))) (PreH15 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur)))) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur)))) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur)))) (PreH18 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH19 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH20 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH21 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH22 : (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j)) ,
  (intArray.full coords_pre (2 * n_pre) flat_cur)
|--
  “ (pivot_y <= 10000) ” &&
  “ ((-10000) <= pivot_y) ” &&
  “ (pivot_x <= 10000) ” &&
  “ ((-10000) <= pivot_x) ” &&
  “ ((Znth ((2 * j) + 1) flat_cur (0 : Int)) <= 10000) ” &&
  “ ((-10000) <= (Znth ((2 * j) + 1) flat_cur (0 : Int))) ” &&
  “ ((Znth (2 * j) flat_cur (0 : Int)) <= 10000) ” &&
  “ ((-10000) <= (Znth (2 * j) flat_cur (0 : Int))) ” &&
  “ (gy_pre <= 10000) ” &&
  “ ((-10000) <= gy_pre) ” &&
  “ (gx_pre <= 10000) ” &&
  “ ((-10000) <= gx_pre) ” &&
  “ (j < high_pre) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre <= high_pre) ” &&
  “ (high_pre < n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ ((low_pre - 1) <= i) ” &&
  “ (i < j) ” &&
  “ (j <= high_pre) ” &&
  “ ((Zlength (pts_l)) = n_pre) ” &&
  “ ((Zlength (pts_cur)) = n_pre) ” &&
  “ ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point))) ” &&
  “ (FlatPoints flat_cur pts_cur) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur)))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur)))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur)))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur)))) ” &&
  “ (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j) ”
  &&  (intArray.full coords_pre (2 * n_pre) flat_cur)

noncomputable def partition_points_partial_solve_wit_5 : Prop := partition_points_partial_solve_wit_5_pure -> partition_points_partial_solve_wit_5_aux

noncomputable def partition_points_partial_solve_wit_6_pure : Prop :=
  forall (pts_l : (List point)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (pivot_x : Int) (pivot_y : Int) (j : Int) (i : Int) (retval : Int) (flat_cur : (List Int)) (pts_cur : (List point)) (PreH1 : (retval <= (0 : Int))) (PreH2 : (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point ((Znth (2 * j) flat_cur (0 : Int))) ((Znth ((2 * j) + 1) flat_cur (0 : Int)))) (mk_point (pivot_x) (pivot_y)) retval)) (PreH3 : (j < high_pre)) (PreH4 : ((0 : Int) <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((0 : Int) <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((low_pre - 1) <= i)) (PreH10 : (i < j)) (PreH11 : (j <= high_pre)) (PreH12 : ((Zlength (pts_l)) = n_pre)) (PreH13 : ((Zlength (pts_cur)) = n_pre)) (PreH14 : ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point)))) (PreH15 : (FlatPoints flat_cur pts_cur)) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur)))) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur)))) (PreH18 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur)))) (PreH19 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur)))) (PreH20 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH21 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH22 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH23 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH24 : (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j)) ,
  ((( &( "c" ) )) # Int |-> (retval))
  ** (intArray.full coords_pre (2 * n_pre) flat_cur)
  ** ((( &( "ay" ) )) # Int |-> ((Znth ((2 * j) + 1) flat_cur (0 : Int))))
  ** ((( &( "ax" ) )) # Int |-> ((Znth (2 * j) flat_cur (0 : Int))))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "i" ) )) # Int |-> ((i + 1)))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "pivot_y" ) )) # Int |-> (pivot_y))
  ** ((( &( "pivot_x" ) )) # Int |-> (pivot_x))
|--
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) < n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ ((Zlength (pts_cur)) = n_pre) ” &&
  “ (FlatPoints flat_cur pts_cur) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur))) ”

noncomputable def partition_points_partial_solve_wit_6_aux : Prop :=
  forall (pts_l : (List point)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (pivot_x : Int) (pivot_y : Int) (j : Int) (i : Int) (retval : Int) (flat_cur : (List Int)) (pts_cur : (List point)) (PreH1 : (retval <= (0 : Int))) (PreH2 : (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point ((Znth (2 * j) flat_cur (0 : Int))) ((Znth ((2 * j) + 1) flat_cur (0 : Int)))) (mk_point (pivot_x) (pivot_y)) retval)) (PreH3 : (j < high_pre)) (PreH4 : ((0 : Int) <= low_pre)) (PreH5 : (low_pre <= high_pre)) (PreH6 : (high_pre < n_pre)) (PreH7 : ((0 : Int) <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((low_pre - 1) <= i)) (PreH10 : (i < j)) (PreH11 : (j <= high_pre)) (PreH12 : ((Zlength (pts_l)) = n_pre)) (PreH13 : ((Zlength (pts_cur)) = n_pre)) (PreH14 : ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point)))) (PreH15 : (FlatPoints flat_cur pts_cur)) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur)))) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur)))) (PreH18 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur)))) (PreH19 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur)))) (PreH20 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH21 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH22 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH23 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH24 : (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j)) ,
  (intArray.full coords_pre (2 * n_pre) flat_cur)
|--
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) < n_pre) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j < n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ ((Zlength (pts_cur)) = n_pre) ” &&
  “ (FlatPoints flat_cur pts_cur) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur))) ” &&
  “ (retval <= (0 : Int)) ” &&
  “ (PolarCmpResult (mk_point (gx_pre) (gy_pre)) (mk_point ((Znth (2 * j) flat_cur (0 : Int))) ((Znth ((2 * j) + 1) flat_cur (0 : Int)))) (mk_point (pivot_x) (pivot_y)) retval) ” &&
  “ (j < high_pre) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre <= high_pre) ” &&
  “ (high_pre < n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ ((low_pre - 1) <= i) ” &&
  “ (i < j) ” &&
  “ (j <= high_pre) ” &&
  “ ((Zlength (pts_l)) = n_pre) ” &&
  “ ((Zlength (pts_cur)) = n_pre) ” &&
  “ ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point))) ” &&
  “ (FlatPoints flat_cur pts_cur) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur)))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur)))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur)))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur)))) ” &&
  “ (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j) ”
  &&  (intArray.full coords_pre (2 * n_pre) flat_cur)

noncomputable def partition_points_partial_solve_wit_6 : Prop := partition_points_partial_solve_wit_6_pure -> partition_points_partial_solve_wit_6_aux

noncomputable def partition_points_partial_solve_wit_7_pure : Prop :=
  forall (pts_l : (List point)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (pivot_x : Int) (pivot_y : Int) (j : Int) (i : Int) (flat_cur : (List Int)) (pts_cur : (List point)) (PreH1 : (j >= high_pre)) (PreH2 : ((0 : Int) <= low_pre)) (PreH3 : (low_pre <= high_pre)) (PreH4 : (high_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((low_pre - 1) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : ((Zlength (pts_l)) = n_pre)) (PreH11 : ((Zlength (pts_cur)) = n_pre)) (PreH12 : ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point)))) (PreH13 : (FlatPoints flat_cur pts_cur)) (PreH14 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur)))) (PreH15 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur)))) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur)))) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur)))) (PreH18 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH19 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH20 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH21 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH22 : (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j)) ,
  ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "low" ) )) # Int |-> (low_pre))
  ** ((( &( "high" ) )) # Int |-> (high_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "pivot_y" ) )) # Int |-> (pivot_y))
  ** ((( &( "pivot_x" ) )) # Int |-> (pivot_x))
  ** (intArray.full coords_pre (2 * n_pre) flat_cur)
|--
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) < n_pre) ” &&
  “ ((0 : Int) <= high_pre) ” &&
  “ (high_pre < n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ ((Zlength (pts_cur)) = n_pre) ” &&
  “ (FlatPoints flat_cur pts_cur) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur))) ”

noncomputable def partition_points_partial_solve_wit_7_aux : Prop :=
  forall (pts_l : (List point)) (coords_pre : Int) (n_pre : Int) (low_pre : Int) (high_pre : Int) (gx_pre : Int) (gy_pre : Int) (pivot_x : Int) (pivot_y : Int) (j : Int) (i : Int) (flat_cur : (List Int)) (pts_cur : (List point)) (PreH1 : (j >= high_pre)) (PreH2 : ((0 : Int) <= low_pre)) (PreH3 : (low_pre <= high_pre)) (PreH4 : (high_pre < n_pre)) (PreH5 : ((0 : Int) <= n_pre)) (PreH6 : (n_pre <= 50000)) (PreH7 : ((low_pre - 1) <= i)) (PreH8 : (i < j)) (PreH9 : (j <= high_pre)) (PreH10 : ((Zlength (pts_l)) = n_pre)) (PreH11 : ((Zlength (pts_cur)) = n_pre)) (PreH12 : ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point)))) (PreH13 : (FlatPoints flat_cur pts_cur)) (PreH14 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur)))) (PreH15 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur)))) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur)))) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur)))) (PreH18 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH19 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH20 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH21 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur))))) (PreH22 : (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j)) ,
  (intArray.full coords_pre (2 * n_pre) flat_cur)
|--
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) < n_pre) ” &&
  “ ((0 : Int) <= high_pre) ” &&
  “ (high_pre < n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ ((Zlength (pts_cur)) = n_pre) ” &&
  “ (FlatPoints flat_cur pts_cur) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur))) ” &&
  “ (j >= high_pre) ” &&
  “ ((0 : Int) <= low_pre) ” &&
  “ (low_pre <= high_pre) ” &&
  “ (high_pre < n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ ((low_pre - 1) <= i) ” &&
  “ (i < j) ” &&
  “ (j <= high_pre) ” &&
  “ ((Zlength (pts_l)) = n_pre) ” &&
  “ ((Zlength (pts_cur)) = n_pre) ” &&
  “ ((mk_point (pivot_x) (pivot_y)) = (Znth (high_pre) (pts_cur) (default_point))) ” &&
  “ (FlatPoints flat_cur pts_cur) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (pts_cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (pts_cur))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (pts_cur))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (pts_cur))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur)))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_cur)))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur)))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_cur)))) ” &&
  “ (PointPartitionScanInv (mk_point (gx_pre) (gy_pre)) pts_l pts_cur low_pre high_pre (mk_point (pivot_x) (pivot_y)) i j) ”
  &&  (intArray.full coords_pre (2 * n_pre) flat_cur)

noncomputable def partition_points_partial_solve_wit_7 : Prop := partition_points_partial_solve_wit_7_pure -> partition_points_partial_solve_wit_7_aux

noncomputable def quicksort_points_range_safety_wit_1 : Prop :=
  forall (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (gx_pre : Int) (gy_pre : Int) (pts_l : (List point)) (flat_out : (List Int)) (pts_out : (List point)) (retval : Int) (PreH1 : (retval > left_pre)) (PreH2 : (left_pre <= retval)) (PreH3 : (retval <= right_pre)) (PreH4 : (FlatPoints flat_out pts_out)) (PreH5 : (PointPermutation pts_l pts_out)) (PreH6 : (PointSameOutsideRange pts_l pts_out left_pre right_pre)) (PreH7 : (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval)) (PreH8 : ((0 : Int) <= n_pre)) (PreH9 : (n_pre <= 50000)) (PreH10 : ((0 : Int) <= left_pre)) (PreH11 : (left_pre < right_pre)) (PreH12 : (right_pre < n_pre)) (PreH13 : (PointFlatModel flat)) (PreH14 : ((Zlength (flat)) = (2 * n_pre))) (PreH15 : ((-10000) <= gx_pre)) (PreH16 : (gx_pre <= 10000)) (PreH17 : ((-10000) <= gy_pre)) (PreH18 : (gy_pre <= 10000)) (PreH19 : (Forall ((LE.le (α := Int)) ((-10000))) flat)) (PreH20 : (Forall ((GE.ge (α := Int)) (10000)) flat)) (PreH21 : ((Zlength (pts_l)) = n_pre)) (PreH22 : (FlatPoints flat pts_l)) (PreH23 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH24 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH25 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH26 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  (intArray.full coords_pre (2 * n_pre) flat_out)
  ** ((( &( "p" ) )) # Int |-> (retval))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
|--
  “ ((retval - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (retval - 1)) ”

noncomputable def quicksort_points_range_safety_wit_2 : Prop :=
  forall (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (gx_pre : Int) (gy_pre : Int) (pts_l : (List point)) (flat_out : (List Int)) (pts_out : (List point)) (retval : Int) (PreH1 : (retval > left_pre)) (PreH2 : (left_pre <= retval)) (PreH3 : (retval <= right_pre)) (PreH4 : (FlatPoints flat_out pts_out)) (PreH5 : (PointPermutation pts_l pts_out)) (PreH6 : (PointSameOutsideRange pts_l pts_out left_pre right_pre)) (PreH7 : (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval)) (PreH8 : ((0 : Int) <= n_pre)) (PreH9 : (n_pre <= 50000)) (PreH10 : ((0 : Int) <= left_pre)) (PreH11 : (left_pre < right_pre)) (PreH12 : (right_pre < n_pre)) (PreH13 : (PointFlatModel flat)) (PreH14 : ((Zlength (flat)) = (2 * n_pre))) (PreH15 : ((-10000) <= gx_pre)) (PreH16 : (gx_pre <= 10000)) (PreH17 : ((-10000) <= gy_pre)) (PreH18 : (gy_pre <= 10000)) (PreH19 : (Forall ((LE.le (α := Int)) ((-10000))) flat)) (PreH20 : (Forall ((GE.ge (α := Int)) (10000)) flat)) (PreH21 : ((Zlength (pts_l)) = n_pre)) (PreH22 : (FlatPoints flat pts_l)) (PreH23 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH24 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH25 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH26 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  (intArray.full coords_pre (2 * n_pre) flat_out)
  ** ((( &( "p" ) )) # Int |-> (retval))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def quicksort_points_range_safety_wit_3 : Prop :=
  forall (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (gx_pre : Int) (gy_pre : Int) (pts_l : (List point)) (flat_out : (List Int)) (pts_out : (List point)) (retval : Int) (PreH1 : (retval >= right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : (FlatPoints flat_out pts_out)) (PreH6 : (PointPermutation pts_l pts_out)) (PreH7 : (PointSameOutsideRange pts_l pts_out left_pre right_pre)) (PreH8 : (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval)) (PreH9 : ((0 : Int) <= n_pre)) (PreH10 : (n_pre <= 50000)) (PreH11 : ((0 : Int) <= left_pre)) (PreH12 : (left_pre < right_pre)) (PreH13 : (right_pre < n_pre)) (PreH14 : (PointFlatModel flat)) (PreH15 : ((Zlength (flat)) = (2 * n_pre))) (PreH16 : ((-10000) <= gx_pre)) (PreH17 : (gx_pre <= 10000)) (PreH18 : ((-10000) <= gy_pre)) (PreH19 : (gy_pre <= 10000)) (PreH20 : (Forall ((LE.le (α := Int)) ((-10000))) flat)) (PreH21 : (Forall ((GE.ge (α := Int)) (10000)) flat)) (PreH22 : ((Zlength (pts_l)) = n_pre)) (PreH23 : (FlatPoints flat pts_l)) (PreH24 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH25 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH26 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH27 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  (intArray.full coords_pre (2 * n_pre) flat_out)
  ** ((( &( "p" ) )) # Int |-> (retval))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
|--
  “ False ”

noncomputable def quicksort_points_range_safety_wit_4 : Prop :=
  forall (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (gx_pre : Int) (gy_pre : Int) (pts_l : (List point)) (flat_out : (List Int)) (pts_out : (List point)) (retval : Int) (flat_out_2 : (List Int)) (pts_out_2 : (List point)) (PreH1 : (retval < right_pre)) (PreH2 : (FlatPoints flat_out_2 pts_out_2)) (PreH3 : (PointRangeSortResult (mk_point (gx_pre) (gy_pre)) flat_out pts_out_2 left_pre (retval - 1))) (PreH4 : (retval > left_pre)) (PreH5 : (left_pre <= retval)) (PreH6 : (retval <= right_pre)) (PreH7 : (FlatPoints flat_out pts_out)) (PreH8 : (PointPermutation pts_l pts_out)) (PreH9 : (PointSameOutsideRange pts_l pts_out left_pre right_pre)) (PreH10 : (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval)) (PreH11 : ((0 : Int) <= n_pre)) (PreH12 : (n_pre <= 50000)) (PreH13 : ((0 : Int) <= left_pre)) (PreH14 : (left_pre < right_pre)) (PreH15 : (right_pre < n_pre)) (PreH16 : (PointFlatModel flat)) (PreH17 : ((Zlength (flat)) = (2 * n_pre))) (PreH18 : ((-10000) <= gx_pre)) (PreH19 : (gx_pre <= 10000)) (PreH20 : ((-10000) <= gy_pre)) (PreH21 : (gy_pre <= 10000)) (PreH22 : (Forall ((LE.le (α := Int)) ((-10000))) flat)) (PreH23 : (Forall ((GE.ge (α := Int)) (10000)) flat)) (PreH24 : ((Zlength (pts_l)) = n_pre)) (PreH25 : (FlatPoints flat pts_l)) (PreH26 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH27 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH28 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH29 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  (intArray.full coords_pre (2 * n_pre) flat_out_2)
  ** ((( &( "p" ) )) # Int |-> (retval))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
|--
  “ ((retval + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (retval + 1)) ”

noncomputable def quicksort_points_range_safety_wit_5 : Prop :=
  forall (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (gx_pre : Int) (gy_pre : Int) (pts_l : (List point)) (flat_out : (List Int)) (pts_out : (List point)) (retval : Int) (flat_out_2 : (List Int)) (pts_out_2 : (List point)) (PreH1 : (retval < right_pre)) (PreH2 : (FlatPoints flat_out_2 pts_out_2)) (PreH3 : (PointRangeSortResult (mk_point (gx_pre) (gy_pre)) flat_out pts_out_2 left_pre (retval - 1))) (PreH4 : (retval > left_pre)) (PreH5 : (left_pre <= retval)) (PreH6 : (retval <= right_pre)) (PreH7 : (FlatPoints flat_out pts_out)) (PreH8 : (PointPermutation pts_l pts_out)) (PreH9 : (PointSameOutsideRange pts_l pts_out left_pre right_pre)) (PreH10 : (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval)) (PreH11 : ((0 : Int) <= n_pre)) (PreH12 : (n_pre <= 50000)) (PreH13 : ((0 : Int) <= left_pre)) (PreH14 : (left_pre < right_pre)) (PreH15 : (right_pre < n_pre)) (PreH16 : (PointFlatModel flat)) (PreH17 : ((Zlength (flat)) = (2 * n_pre))) (PreH18 : ((-10000) <= gx_pre)) (PreH19 : (gx_pre <= 10000)) (PreH20 : ((-10000) <= gy_pre)) (PreH21 : (gy_pre <= 10000)) (PreH22 : (Forall ((LE.le (α := Int)) ((-10000))) flat)) (PreH23 : (Forall ((GE.ge (α := Int)) (10000)) flat)) (PreH24 : ((Zlength (pts_l)) = n_pre)) (PreH25 : (FlatPoints flat pts_l)) (PreH26 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH27 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH28 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH29 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  (intArray.full coords_pre (2 * n_pre) flat_out_2)
  ** ((( &( "p" ) )) # Int |-> (retval))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def quicksort_points_range_safety_wit_6 : Prop :=
  forall (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (gx_pre : Int) (gy_pre : Int) (pts_l : (List point)) (flat_out : (List Int)) (pts_out : (List point)) (retval : Int) (PreH1 : (retval < right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : (FlatPoints flat_out pts_out)) (PreH6 : (PointPermutation pts_l pts_out)) (PreH7 : (PointSameOutsideRange pts_l pts_out left_pre right_pre)) (PreH8 : (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval)) (PreH9 : ((0 : Int) <= n_pre)) (PreH10 : (n_pre <= 50000)) (PreH11 : ((0 : Int) <= left_pre)) (PreH12 : (left_pre < right_pre)) (PreH13 : (right_pre < n_pre)) (PreH14 : (PointFlatModel flat)) (PreH15 : ((Zlength (flat)) = (2 * n_pre))) (PreH16 : ((-10000) <= gx_pre)) (PreH17 : (gx_pre <= 10000)) (PreH18 : ((-10000) <= gy_pre)) (PreH19 : (gy_pre <= 10000)) (PreH20 : (Forall ((LE.le (α := Int)) ((-10000))) flat)) (PreH21 : (Forall ((GE.ge (α := Int)) (10000)) flat)) (PreH22 : ((Zlength (pts_l)) = n_pre)) (PreH23 : (FlatPoints flat pts_l)) (PreH24 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH25 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH26 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH27 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  (intArray.full coords_pre (2 * n_pre) flat_out)
  ** ((( &( "p" ) )) # Int |-> (retval))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
|--
  “ ((retval + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (retval + 1)) ”

noncomputable def quicksort_points_range_safety_wit_7 : Prop :=
  forall (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (gx_pre : Int) (gy_pre : Int) (pts_l : (List point)) (flat_out : (List Int)) (pts_out : (List point)) (retval : Int) (PreH1 : (retval < right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : (FlatPoints flat_out pts_out)) (PreH6 : (PointPermutation pts_l pts_out)) (PreH7 : (PointSameOutsideRange pts_l pts_out left_pre right_pre)) (PreH8 : (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval)) (PreH9 : ((0 : Int) <= n_pre)) (PreH10 : (n_pre <= 50000)) (PreH11 : ((0 : Int) <= left_pre)) (PreH12 : (left_pre < right_pre)) (PreH13 : (right_pre < n_pre)) (PreH14 : (PointFlatModel flat)) (PreH15 : ((Zlength (flat)) = (2 * n_pre))) (PreH16 : ((-10000) <= gx_pre)) (PreH17 : (gx_pre <= 10000)) (PreH18 : ((-10000) <= gy_pre)) (PreH19 : (gy_pre <= 10000)) (PreH20 : (Forall ((LE.le (α := Int)) ((-10000))) flat)) (PreH21 : (Forall ((GE.ge (α := Int)) (10000)) flat)) (PreH22 : ((Zlength (pts_l)) = n_pre)) (PreH23 : (FlatPoints flat pts_l)) (PreH24 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH25 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH26 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH27 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  (intArray.full coords_pre (2 * n_pre) flat_out)
  ** ((( &( "p" ) )) # Int |-> (retval))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def quicksort_points_range_entail_wit_1 : Prop :=
  (
forall (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (gx_pre : Int) (gy_pre : Int) (PreH1 : (left_pre < right_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((0 : Int) <= left_pre)) (PreH5 : ((-1) <= right_pre)) (PreH6 : (right_pre < n_pre)) (PreH7 : (PointFlatModel flat)) (PreH8 : ((Zlength (flat)) = (2 * n_pre))) (PreH9 : ((-10000) <= gx_pre)) (PreH10 : (gx_pre <= 10000)) (PreH11 : ((-10000) <= gy_pre)) (PreH12 : (gy_pre <= 10000)) (PreH13 : (Forall ((LE.le (α := Int)) ((-10000))) flat)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) flat)) ,
  (intArray.full coords_pre (2 * n_pre) flat)
|--
  EX pts_l : (List point),
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre < right_pre) ” &&
  “ (right_pre < n_pre) ” &&
  “ (PointFlatModel flat) ” &&
  “ ((Zlength (flat)) = (2 * n_pre)) ” &&
  “ ((-10000) <= gx_pre) ” &&
  “ (gx_pre <= 10000) ” &&
  “ ((-10000) <= gy_pre) ” &&
  “ (gy_pre <= 10000) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) flat) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) flat) ” &&
  “ ((Zlength (pts_l)) = n_pre) ” &&
  “ (FlatPoints flat pts_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l)))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l)))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l)))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l)))) ”
  &&  (intArray.full coords_pre (2 * n_pre) flat)
) \/
(
forall (flat : (List Int)) (n_pre : Int) (left_pre : Int) (right_pre : Int) (gx_pre : Int) (gy_pre : Int) (PreH1 : (left_pre < right_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((0 : Int) <= left_pre)) (PreH5 : ((-1) <= right_pre)) (PreH6 : (right_pre < n_pre)) (PreH7 : (PointFlatModel flat)) (PreH8 : ((Zlength (flat)) = (2 * n_pre))) (PreH9 : ((-10000) <= gx_pre)) (PreH10 : (gx_pre <= 10000)) (PreH11 : ((-10000) <= gy_pre)) (PreH12 : (gy_pre <= 10000)) (PreH13 : (Forall ((LE.le (α := Int)) ((-10000))) flat)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) flat)) ,
  TT && emp 
|--
  EX pts_l : (List point),
  “ ((Zlength (pts_l)) = n_pre) ” &&
  “ (FlatPoints flat pts_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l)))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l)))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l)))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l)))) ”
  &&  emp
)

noncomputable def quicksort_points_range_return_wit_1 : Prop :=
  (
forall (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (gx_pre : Int) (gy_pre : Int) (pts_l : (List point)) (flat_out_2 : (List Int)) (pts_out_2 : (List point)) (retval : Int) (flat_out_3 : (List Int)) (pts_out_3 : (List point)) (flat_out_4 : (List Int)) (pts_out_4 : (List point)) (PreH1 : (FlatPoints flat_out_4 pts_out_4)) (PreH2 : (PointRangeSortResult (mk_point (gx_pre) (gy_pre)) flat_out_3 pts_out_4 (retval + 1) right_pre)) (PreH3 : (retval < right_pre)) (PreH4 : (FlatPoints flat_out_3 pts_out_3)) (PreH5 : (PointRangeSortResult (mk_point (gx_pre) (gy_pre)) flat_out_2 pts_out_3 left_pre (retval - 1))) (PreH6 : (retval > left_pre)) (PreH7 : (left_pre <= retval)) (PreH8 : (retval <= right_pre)) (PreH9 : (FlatPoints flat_out_2 pts_out_2)) (PreH10 : (PointPermutation pts_l pts_out_2)) (PreH11 : (PointSameOutsideRange pts_l pts_out_2 left_pre right_pre)) (PreH12 : (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre retval)) (PreH13 : ((0 : Int) <= n_pre)) (PreH14 : (n_pre <= 50000)) (PreH15 : ((0 : Int) <= left_pre)) (PreH16 : (left_pre < right_pre)) (PreH17 : (right_pre < n_pre)) (PreH18 : (PointFlatModel flat)) (PreH19 : ((Zlength (flat)) = (2 * n_pre))) (PreH20 : ((-10000) <= gx_pre)) (PreH21 : (gx_pre <= 10000)) (PreH22 : ((-10000) <= gy_pre)) (PreH23 : (gy_pre <= 10000)) (PreH24 : (Forall ((LE.le (α := Int)) ((-10000))) flat)) (PreH25 : (Forall ((GE.ge (α := Int)) (10000)) flat)) (PreH26 : ((Zlength (pts_l)) = n_pre)) (PreH27 : (FlatPoints flat pts_l)) (PreH28 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH29 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH30 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH31 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  (intArray.full coords_pre (2 * n_pre) flat_out_4)
|--
  EX flat_out : (List Int), EX pts_out : (List point),
  “ (FlatPoints flat_out pts_out) ” &&
  “ (PointRangeSortResult (mk_point (gx_pre) (gy_pre)) flat pts_out left_pre right_pre) ”
  &&  (intArray.full coords_pre (2 * n_pre) flat_out)
) \/
(
forall (flat : (List Int)) (n_pre : Int) (left_pre : Int) (right_pre : Int) (gx_pre : Int) (gy_pre : Int) (pts_l : (List point)) (flat_out_2 : (List Int)) (pts_out_2 : (List point)) (retval : Int) (flat_out_3 : (List Int)) (pts_out_3 : (List point)) (flat_out_4 : (List Int)) (pts_out_4 : (List point)) (PreH1 : (FlatPoints flat_out_4 pts_out_4)) (PreH2 : (PointRangeSortResult (mk_point (gx_pre) (gy_pre)) flat_out_3 pts_out_4 (retval + 1) right_pre)) (PreH3 : (retval < right_pre)) (PreH4 : (FlatPoints flat_out_3 pts_out_3)) (PreH5 : (PointRangeSortResult (mk_point (gx_pre) (gy_pre)) flat_out_2 pts_out_3 left_pre (retval - 1))) (PreH6 : (retval > left_pre)) (PreH7 : (left_pre <= retval)) (PreH8 : (retval <= right_pre)) (PreH9 : (FlatPoints flat_out_2 pts_out_2)) (PreH10 : (PointPermutation pts_l pts_out_2)) (PreH11 : (PointSameOutsideRange pts_l pts_out_2 left_pre right_pre)) (PreH12 : (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre retval)) (PreH13 : ((0 : Int) <= n_pre)) (PreH14 : (n_pre <= 50000)) (PreH15 : ((0 : Int) <= left_pre)) (PreH16 : (left_pre < right_pre)) (PreH17 : (right_pre < n_pre)) (PreH18 : (PointFlatModel flat)) (PreH19 : ((Zlength (flat)) = (2 * n_pre))) (PreH20 : ((-10000) <= gx_pre)) (PreH21 : (gx_pre <= 10000)) (PreH22 : ((-10000) <= gy_pre)) (PreH23 : (gy_pre <= 10000)) (PreH24 : (Forall ((LE.le (α := Int)) ((-10000))) flat)) (PreH25 : (Forall ((GE.ge (α := Int)) (10000)) flat)) (PreH26 : ((Zlength (pts_l)) = n_pre)) (PreH27 : (FlatPoints flat pts_l)) (PreH28 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH29 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH30 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH31 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  TT && emp 
|--
  EX pts_out : (List point),
  “ (FlatPoints flat_out_4 pts_out) ” &&
  “ (PointRangeSortResult (mk_point (gx_pre) (gy_pre)) flat pts_out left_pre right_pre) ”
  &&  emp
)

noncomputable def quicksort_points_range_return_wit_2 : Prop :=
  (
forall (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (gx_pre : Int) (gy_pre : Int) (pts_l : (List point)) (flat_out_2 : (List Int)) (pts_out_2 : (List point)) (retval : Int) (flat_out_3 : (List Int)) (pts_out_3 : (List point)) (PreH1 : (FlatPoints flat_out_3 pts_out_3)) (PreH2 : (PointRangeSortResult (mk_point (gx_pre) (gy_pre)) flat_out_2 pts_out_3 (retval + 1) right_pre)) (PreH3 : (retval < right_pre)) (PreH4 : (retval <= left_pre)) (PreH5 : (left_pre <= retval)) (PreH6 : (retval <= right_pre)) (PreH7 : (FlatPoints flat_out_2 pts_out_2)) (PreH8 : (PointPermutation pts_l pts_out_2)) (PreH9 : (PointSameOutsideRange pts_l pts_out_2 left_pre right_pre)) (PreH10 : (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre retval)) (PreH11 : ((0 : Int) <= n_pre)) (PreH12 : (n_pre <= 50000)) (PreH13 : ((0 : Int) <= left_pre)) (PreH14 : (left_pre < right_pre)) (PreH15 : (right_pre < n_pre)) (PreH16 : (PointFlatModel flat)) (PreH17 : ((Zlength (flat)) = (2 * n_pre))) (PreH18 : ((-10000) <= gx_pre)) (PreH19 : (gx_pre <= 10000)) (PreH20 : ((-10000) <= gy_pre)) (PreH21 : (gy_pre <= 10000)) (PreH22 : (Forall ((LE.le (α := Int)) ((-10000))) flat)) (PreH23 : (Forall ((GE.ge (α := Int)) (10000)) flat)) (PreH24 : ((Zlength (pts_l)) = n_pre)) (PreH25 : (FlatPoints flat pts_l)) (PreH26 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH27 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH28 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH29 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  (intArray.full coords_pre (2 * n_pre) flat_out_3)
|--
  EX flat_out : (List Int), EX pts_out : (List point),
  “ (FlatPoints flat_out pts_out) ” &&
  “ (PointRangeSortResult (mk_point (gx_pre) (gy_pre)) flat pts_out left_pre right_pre) ”
  &&  (intArray.full coords_pre (2 * n_pre) flat_out)
) \/
(
forall (flat : (List Int)) (n_pre : Int) (left_pre : Int) (right_pre : Int) (gx_pre : Int) (gy_pre : Int) (pts_l : (List point)) (flat_out_2 : (List Int)) (pts_out_2 : (List point)) (retval : Int) (flat_out_3 : (List Int)) (pts_out_3 : (List point)) (PreH1 : (FlatPoints flat_out_3 pts_out_3)) (PreH2 : (PointRangeSortResult (mk_point (gx_pre) (gy_pre)) flat_out_2 pts_out_3 (retval + 1) right_pre)) (PreH3 : (retval < right_pre)) (PreH4 : (retval <= left_pre)) (PreH5 : (left_pre <= retval)) (PreH6 : (retval <= right_pre)) (PreH7 : (FlatPoints flat_out_2 pts_out_2)) (PreH8 : (PointPermutation pts_l pts_out_2)) (PreH9 : (PointSameOutsideRange pts_l pts_out_2 left_pre right_pre)) (PreH10 : (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre retval)) (PreH11 : ((0 : Int) <= n_pre)) (PreH12 : (n_pre <= 50000)) (PreH13 : ((0 : Int) <= left_pre)) (PreH14 : (left_pre < right_pre)) (PreH15 : (right_pre < n_pre)) (PreH16 : (PointFlatModel flat)) (PreH17 : ((Zlength (flat)) = (2 * n_pre))) (PreH18 : ((-10000) <= gx_pre)) (PreH19 : (gx_pre <= 10000)) (PreH20 : ((-10000) <= gy_pre)) (PreH21 : (gy_pre <= 10000)) (PreH22 : (Forall ((LE.le (α := Int)) ((-10000))) flat)) (PreH23 : (Forall ((GE.ge (α := Int)) (10000)) flat)) (PreH24 : ((Zlength (pts_l)) = n_pre)) (PreH25 : (FlatPoints flat pts_l)) (PreH26 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH27 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH28 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH29 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  TT && emp 
|--
  EX pts_out : (List point),
  “ (FlatPoints flat_out_3 pts_out) ” &&
  “ (PointRangeSortResult (mk_point (gx_pre) (gy_pre)) flat pts_out left_pre right_pre) ”
  &&  emp
)

noncomputable def quicksort_points_range_return_wit_3 : Prop :=
  (
forall (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (gx_pre : Int) (gy_pre : Int) (pts_l : (List point)) (flat_out_2 : (List Int)) (pts_out_2 : (List point)) (retval : Int) (flat_out_3 : (List Int)) (pts_out_3 : (List point)) (PreH1 : (retval >= right_pre)) (PreH2 : (FlatPoints flat_out_3 pts_out_3)) (PreH3 : (PointRangeSortResult (mk_point (gx_pre) (gy_pre)) flat_out_2 pts_out_3 left_pre (retval - 1))) (PreH4 : (retval > left_pre)) (PreH5 : (left_pre <= retval)) (PreH6 : (retval <= right_pre)) (PreH7 : (FlatPoints flat_out_2 pts_out_2)) (PreH8 : (PointPermutation pts_l pts_out_2)) (PreH9 : (PointSameOutsideRange pts_l pts_out_2 left_pre right_pre)) (PreH10 : (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre retval)) (PreH11 : ((0 : Int) <= n_pre)) (PreH12 : (n_pre <= 50000)) (PreH13 : ((0 : Int) <= left_pre)) (PreH14 : (left_pre < right_pre)) (PreH15 : (right_pre < n_pre)) (PreH16 : (PointFlatModel flat)) (PreH17 : ((Zlength (flat)) = (2 * n_pre))) (PreH18 : ((-10000) <= gx_pre)) (PreH19 : (gx_pre <= 10000)) (PreH20 : ((-10000) <= gy_pre)) (PreH21 : (gy_pre <= 10000)) (PreH22 : (Forall ((LE.le (α := Int)) ((-10000))) flat)) (PreH23 : (Forall ((GE.ge (α := Int)) (10000)) flat)) (PreH24 : ((Zlength (pts_l)) = n_pre)) (PreH25 : (FlatPoints flat pts_l)) (PreH26 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH27 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH28 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH29 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  (intArray.full coords_pre (2 * n_pre) flat_out_3)
|--
  EX flat_out : (List Int), EX pts_out : (List point),
  “ (FlatPoints flat_out pts_out) ” &&
  “ (PointRangeSortResult (mk_point (gx_pre) (gy_pre)) flat pts_out left_pre right_pre) ”
  &&  (intArray.full coords_pre (2 * n_pre) flat_out)
) \/
(
forall (flat : (List Int)) (n_pre : Int) (left_pre : Int) (right_pre : Int) (gx_pre : Int) (gy_pre : Int) (pts_l : (List point)) (flat_out_2 : (List Int)) (pts_out_2 : (List point)) (retval : Int) (flat_out_3 : (List Int)) (pts_out_3 : (List point)) (PreH1 : (retval >= right_pre)) (PreH2 : (FlatPoints flat_out_3 pts_out_3)) (PreH3 : (PointRangeSortResult (mk_point (gx_pre) (gy_pre)) flat_out_2 pts_out_3 left_pre (retval - 1))) (PreH4 : (retval > left_pre)) (PreH5 : (left_pre <= retval)) (PreH6 : (retval <= right_pre)) (PreH7 : (FlatPoints flat_out_2 pts_out_2)) (PreH8 : (PointPermutation pts_l pts_out_2)) (PreH9 : (PointSameOutsideRange pts_l pts_out_2 left_pre right_pre)) (PreH10 : (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out_2 left_pre right_pre retval)) (PreH11 : ((0 : Int) <= n_pre)) (PreH12 : (n_pre <= 50000)) (PreH13 : ((0 : Int) <= left_pre)) (PreH14 : (left_pre < right_pre)) (PreH15 : (right_pre < n_pre)) (PreH16 : (PointFlatModel flat)) (PreH17 : ((Zlength (flat)) = (2 * n_pre))) (PreH18 : ((-10000) <= gx_pre)) (PreH19 : (gx_pre <= 10000)) (PreH20 : ((-10000) <= gy_pre)) (PreH21 : (gy_pre <= 10000)) (PreH22 : (Forall ((LE.le (α := Int)) ((-10000))) flat)) (PreH23 : (Forall ((GE.ge (α := Int)) (10000)) flat)) (PreH24 : ((Zlength (pts_l)) = n_pre)) (PreH25 : (FlatPoints flat pts_l)) (PreH26 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH27 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH28 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH29 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  TT && emp 
|--
  EX pts_out : (List point),
  “ (FlatPoints flat_out_3 pts_out) ” &&
  “ (PointRangeSortResult (mk_point (gx_pre) (gy_pre)) flat pts_out left_pre right_pre) ”
  &&  emp
)

noncomputable def quicksort_points_range_return_wit_4 : Prop :=
  (
forall (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (gx_pre : Int) (gy_pre : Int) (PreH1 : (left_pre >= right_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((0 : Int) <= left_pre)) (PreH5 : ((-1) <= right_pre)) (PreH6 : (right_pre < n_pre)) (PreH7 : (PointFlatModel flat)) (PreH8 : ((Zlength (flat)) = (2 * n_pre))) (PreH9 : ((-10000) <= gx_pre)) (PreH10 : (gx_pre <= 10000)) (PreH11 : ((-10000) <= gy_pre)) (PreH12 : (gy_pre <= 10000)) (PreH13 : (Forall ((LE.le (α := Int)) ((-10000))) flat)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) flat)) ,
  (intArray.full coords_pre (2 * n_pre) flat)
|--
  EX flat_out : (List Int), EX pts_out : (List point),
  “ (FlatPoints flat_out pts_out) ” &&
  “ (PointRangeSortResult (mk_point (gx_pre) (gy_pre)) flat pts_out left_pre right_pre) ”
  &&  (intArray.full coords_pre (2 * n_pre) flat_out)
) \/
(
forall (flat : (List Int)) (n_pre : Int) (left_pre : Int) (right_pre : Int) (gx_pre : Int) (gy_pre : Int) (PreH1 : (left_pre >= right_pre)) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : (n_pre <= 50000)) (PreH4 : ((0 : Int) <= left_pre)) (PreH5 : ((-1) <= right_pre)) (PreH6 : (right_pre < n_pre)) (PreH7 : (PointFlatModel flat)) (PreH8 : ((Zlength (flat)) = (2 * n_pre))) (PreH9 : ((-10000) <= gx_pre)) (PreH10 : (gx_pre <= 10000)) (PreH11 : ((-10000) <= gy_pre)) (PreH12 : (gy_pre <= 10000)) (PreH13 : (Forall ((LE.le (α := Int)) ((-10000))) flat)) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) flat)) ,
  TT && emp 
|--
  EX pts_out : (List point),
  “ (FlatPoints flat pts_out) ” &&
  “ (PointRangeSortResult (mk_point (gx_pre) (gy_pre)) flat pts_out left_pre right_pre) ”
  &&  emp
)

noncomputable def quicksort_points_range_partial_solve_wit_1_pure : Prop :=
  forall (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (gx_pre : Int) (gy_pre : Int) (pts_l : (List point)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((0 : Int) <= left_pre)) (PreH4 : (left_pre < right_pre)) (PreH5 : (right_pre < n_pre)) (PreH6 : (PointFlatModel flat)) (PreH7 : ((Zlength (flat)) = (2 * n_pre))) (PreH8 : ((-10000) <= gx_pre)) (PreH9 : (gx_pre <= 10000)) (PreH10 : ((-10000) <= gy_pre)) (PreH11 : (gy_pre <= 10000)) (PreH12 : (Forall ((LE.le (α := Int)) ((-10000))) flat)) (PreH13 : (Forall ((GE.ge (α := Int)) (10000)) flat)) (PreH14 : ((Zlength (pts_l)) = n_pre)) (PreH15 : (FlatPoints flat pts_l)) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH18 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH19 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  ((( &( "p" ) )) # Int |->_)
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
  ** (intArray.full coords_pre (2 * n_pre) flat)
|--
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= right_pre) ” &&
  “ (right_pre < n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ ((Zlength (pts_l)) = n_pre) ” &&
  “ (FlatPoints flat pts_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l)))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l)))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l)))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l)))) ”

noncomputable def quicksort_points_range_partial_solve_wit_1_aux : Prop :=
  forall (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (gx_pre : Int) (gy_pre : Int) (pts_l : (List point)) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((0 : Int) <= left_pre)) (PreH4 : (left_pre < right_pre)) (PreH5 : (right_pre < n_pre)) (PreH6 : (PointFlatModel flat)) (PreH7 : ((Zlength (flat)) = (2 * n_pre))) (PreH8 : ((-10000) <= gx_pre)) (PreH9 : (gx_pre <= 10000)) (PreH10 : ((-10000) <= gy_pre)) (PreH11 : (gy_pre <= 10000)) (PreH12 : (Forall ((LE.le (α := Int)) ((-10000))) flat)) (PreH13 : (Forall ((GE.ge (α := Int)) (10000)) flat)) (PreH14 : ((Zlength (pts_l)) = n_pre)) (PreH15 : (FlatPoints flat pts_l)) (PreH16 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH17 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH18 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH19 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  (intArray.full coords_pre (2 * n_pre) flat)
|--
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre <= right_pre) ” &&
  “ (right_pre < n_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ ((Zlength (pts_l)) = n_pre) ” &&
  “ (FlatPoints flat pts_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l)))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l)))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l)))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l)))) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre < right_pre) ” &&
  “ (right_pre < n_pre) ” &&
  “ (PointFlatModel flat) ” &&
  “ ((Zlength (flat)) = (2 * n_pre)) ” &&
  “ ((-10000) <= gx_pre) ” &&
  “ (gx_pre <= 10000) ” &&
  “ ((-10000) <= gy_pre) ” &&
  “ (gy_pre <= 10000) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) flat) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) flat) ” &&
  “ ((Zlength (pts_l)) = n_pre) ” &&
  “ (FlatPoints flat pts_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l)))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l)))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l)))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l)))) ”
  &&  (intArray.full coords_pre (2 * n_pre) flat)

noncomputable def quicksort_points_range_partial_solve_wit_1 : Prop := quicksort_points_range_partial_solve_wit_1_pure -> quicksort_points_range_partial_solve_wit_1_aux

noncomputable def quicksort_points_range_partial_solve_wit_2_pure : Prop :=
  (
forall (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (gx_pre : Int) (gy_pre : Int) (pts_l : (List point)) (flat_out : (List Int)) (pts_out : (List point)) (retval : Int) (PreH1 : (retval > left_pre)) (PreH2 : (left_pre <= retval)) (PreH3 : (retval <= right_pre)) (PreH4 : (FlatPoints flat_out pts_out)) (PreH5 : (PointPermutation pts_l pts_out)) (PreH6 : (PointSameOutsideRange pts_l pts_out left_pre right_pre)) (PreH7 : (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval)) (PreH8 : ((0 : Int) <= n_pre)) (PreH9 : (n_pre <= 50000)) (PreH10 : ((0 : Int) <= left_pre)) (PreH11 : (left_pre < right_pre)) (PreH12 : (right_pre < n_pre)) (PreH13 : (PointFlatModel flat)) (PreH14 : ((Zlength (flat)) = (2 * n_pre))) (PreH15 : ((-10000) <= gx_pre)) (PreH16 : (gx_pre <= 10000)) (PreH17 : ((-10000) <= gy_pre)) (PreH18 : (gy_pre <= 10000)) (PreH19 : (Forall ((LE.le (α := Int)) ((-10000))) flat)) (PreH20 : (Forall ((GE.ge (α := Int)) (10000)) flat)) (PreH21 : ((Zlength (pts_l)) = n_pre)) (PreH22 : (FlatPoints flat pts_l)) (PreH23 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH24 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH25 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH26 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  (intArray.full coords_pre (2 * n_pre) flat_out)
  ** ((( &( "p" ) )) # Int |-> (retval))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ ((-1) <= (retval - 1)) ” &&
  “ ((retval - 1) < n_pre) ” &&
  “ ((-10000) <= gx_pre) ” &&
  “ (gx_pre <= 10000) ” &&
  “ ((-10000) <= gy_pre) ” &&
  “ (gy_pre <= 10000) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) flat_out) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) flat_out) ” &&
  “ ((Zlength (flat_out)) = (2 * n_pre)) ” &&
  “ (PointFlatModel flat_out) ”
) \/
(
forall (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (gx_pre : Int) (gy_pre : Int) (pts_l : (List point)) (flat_out : (List Int)) (pts_out : (List point)) (retval : Int) (PreH1 : (gy_pre <= INT_MAX)) (PreH2 : (gx_pre <= INT_MAX)) (PreH3 : (right_pre <= INT_MAX)) (PreH4 : (left_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (retval <= INT_MAX)) (PreH7 : (gy_pre >= INT_MIN)) (PreH8 : (gx_pre >= INT_MIN)) (PreH9 : (right_pre >= INT_MIN)) (PreH10 : (left_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (retval > left_pre)) (PreH14 : (left_pre <= retval)) (PreH15 : (retval <= right_pre)) (PreH16 : (FlatPoints flat_out pts_out)) (PreH17 : (PointPermutation pts_l pts_out)) (PreH18 : (PointSameOutsideRange pts_l pts_out left_pre right_pre)) (PreH19 : (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval)) (PreH20 : ((0 : Int) <= n_pre)) (PreH21 : (n_pre <= 50000)) (PreH22 : ((0 : Int) <= left_pre)) (PreH23 : (left_pre < right_pre)) (PreH24 : (right_pre < n_pre)) (PreH25 : (PointFlatModel flat)) (PreH26 : ((Zlength (flat)) = (2 * n_pre))) (PreH27 : ((-10000) <= gx_pre)) (PreH28 : (gx_pre <= 10000)) (PreH29 : ((-10000) <= gy_pre)) (PreH30 : (gy_pre <= 10000)) (PreH31 : (Forall ((LE.le (α := Int)) ((-10000))) flat)) (PreH32 : (Forall ((GE.ge (α := Int)) (10000)) flat)) (PreH33 : ((Zlength (pts_l)) = n_pre)) (PreH34 : (FlatPoints flat pts_l)) (PreH35 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH37 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH38 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  (intArray.full coords_pre (2 * n_pre) flat_out)
  ** ((( &( "p" ) )) # Int |-> (retval))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
|--
  “ (PointFlatModel flat_out) ” &&
  “ ((Zlength (flat_out)) = (2 * n_pre)) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) flat_out) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) flat_out) ”
)

noncomputable def quicksort_points_range_partial_solve_wit_2_pure_split_goal_1 : Prop :=
  forall (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (gx_pre : Int) (gy_pre : Int) (pts_l : (List point)) (flat_out : (List Int)) (pts_out : (List point)) (retval : Int) (PreH1 : (gy_pre <= INT_MAX)) (PreH2 : (gx_pre <= INT_MAX)) (PreH3 : (right_pre <= INT_MAX)) (PreH4 : (left_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (retval <= INT_MAX)) (PreH7 : (gy_pre >= INT_MIN)) (PreH8 : (gx_pre >= INT_MIN)) (PreH9 : (right_pre >= INT_MIN)) (PreH10 : (left_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (retval > left_pre)) (PreH14 : (left_pre <= retval)) (PreH15 : (retval <= right_pre)) (PreH16 : (FlatPoints flat_out pts_out)) (PreH17 : (PointPermutation pts_l pts_out)) (PreH18 : (PointSameOutsideRange pts_l pts_out left_pre right_pre)) (PreH19 : (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval)) (PreH20 : ((0 : Int) <= n_pre)) (PreH21 : (n_pre <= 50000)) (PreH22 : ((0 : Int) <= left_pre)) (PreH23 : (left_pre < right_pre)) (PreH24 : (right_pre < n_pre)) (PreH25 : (PointFlatModel flat)) (PreH26 : ((Zlength (flat)) = (2 * n_pre))) (PreH27 : ((-10000) <= gx_pre)) (PreH28 : (gx_pre <= 10000)) (PreH29 : ((-10000) <= gy_pre)) (PreH30 : (gy_pre <= 10000)) (PreH31 : (Forall ((LE.le (α := Int)) ((-10000))) flat)) (PreH32 : (Forall ((GE.ge (α := Int)) (10000)) flat)) (PreH33 : ((Zlength (pts_l)) = n_pre)) (PreH34 : (FlatPoints flat pts_l)) (PreH35 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH37 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH38 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  (intArray.full coords_pre (2 * n_pre) flat_out)
  ** ((( &( "p" ) )) # Int |-> (retval))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
|--
  “ (PointFlatModel flat_out) ”

noncomputable def quicksort_points_range_partial_solve_wit_2_pure_split_goal_2 : Prop :=
  forall (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (gx_pre : Int) (gy_pre : Int) (pts_l : (List point)) (flat_out : (List Int)) (pts_out : (List point)) (retval : Int) (PreH1 : (gy_pre <= INT_MAX)) (PreH2 : (gx_pre <= INT_MAX)) (PreH3 : (right_pre <= INT_MAX)) (PreH4 : (left_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (retval <= INT_MAX)) (PreH7 : (gy_pre >= INT_MIN)) (PreH8 : (gx_pre >= INT_MIN)) (PreH9 : (right_pre >= INT_MIN)) (PreH10 : (left_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (retval > left_pre)) (PreH14 : (left_pre <= retval)) (PreH15 : (retval <= right_pre)) (PreH16 : (FlatPoints flat_out pts_out)) (PreH17 : (PointPermutation pts_l pts_out)) (PreH18 : (PointSameOutsideRange pts_l pts_out left_pre right_pre)) (PreH19 : (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval)) (PreH20 : ((0 : Int) <= n_pre)) (PreH21 : (n_pre <= 50000)) (PreH22 : ((0 : Int) <= left_pre)) (PreH23 : (left_pre < right_pre)) (PreH24 : (right_pre < n_pre)) (PreH25 : (PointFlatModel flat)) (PreH26 : ((Zlength (flat)) = (2 * n_pre))) (PreH27 : ((-10000) <= gx_pre)) (PreH28 : (gx_pre <= 10000)) (PreH29 : ((-10000) <= gy_pre)) (PreH30 : (gy_pre <= 10000)) (PreH31 : (Forall ((LE.le (α := Int)) ((-10000))) flat)) (PreH32 : (Forall ((GE.ge (α := Int)) (10000)) flat)) (PreH33 : ((Zlength (pts_l)) = n_pre)) (PreH34 : (FlatPoints flat pts_l)) (PreH35 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH37 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH38 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  (intArray.full coords_pre (2 * n_pre) flat_out)
  ** ((( &( "p" ) )) # Int |-> (retval))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
|--
  “ ((Zlength (flat_out)) = (2 * n_pre)) ”

noncomputable def quicksort_points_range_partial_solve_wit_2_pure_split_goal_3 : Prop :=
  forall (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (gx_pre : Int) (gy_pre : Int) (pts_l : (List point)) (flat_out : (List Int)) (pts_out : (List point)) (retval : Int) (PreH1 : (gy_pre <= INT_MAX)) (PreH2 : (gx_pre <= INT_MAX)) (PreH3 : (right_pre <= INT_MAX)) (PreH4 : (left_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (retval <= INT_MAX)) (PreH7 : (gy_pre >= INT_MIN)) (PreH8 : (gx_pre >= INT_MIN)) (PreH9 : (right_pre >= INT_MIN)) (PreH10 : (left_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (retval > left_pre)) (PreH14 : (left_pre <= retval)) (PreH15 : (retval <= right_pre)) (PreH16 : (FlatPoints flat_out pts_out)) (PreH17 : (PointPermutation pts_l pts_out)) (PreH18 : (PointSameOutsideRange pts_l pts_out left_pre right_pre)) (PreH19 : (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval)) (PreH20 : ((0 : Int) <= n_pre)) (PreH21 : (n_pre <= 50000)) (PreH22 : ((0 : Int) <= left_pre)) (PreH23 : (left_pre < right_pre)) (PreH24 : (right_pre < n_pre)) (PreH25 : (PointFlatModel flat)) (PreH26 : ((Zlength (flat)) = (2 * n_pre))) (PreH27 : ((-10000) <= gx_pre)) (PreH28 : (gx_pre <= 10000)) (PreH29 : ((-10000) <= gy_pre)) (PreH30 : (gy_pre <= 10000)) (PreH31 : (Forall ((LE.le (α := Int)) ((-10000))) flat)) (PreH32 : (Forall ((GE.ge (α := Int)) (10000)) flat)) (PreH33 : ((Zlength (pts_l)) = n_pre)) (PreH34 : (FlatPoints flat pts_l)) (PreH35 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH37 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH38 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  (intArray.full coords_pre (2 * n_pre) flat_out)
  ** ((( &( "p" ) )) # Int |-> (retval))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
|--
  “ (Forall ((LE.le (α := Int)) ((-10000))) flat_out) ”

noncomputable def quicksort_points_range_partial_solve_wit_2_pure_split_goal_4 : Prop :=
  forall (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (gx_pre : Int) (gy_pre : Int) (pts_l : (List point)) (flat_out : (List Int)) (pts_out : (List point)) (retval : Int) (PreH1 : (gy_pre <= INT_MAX)) (PreH2 : (gx_pre <= INT_MAX)) (PreH3 : (right_pre <= INT_MAX)) (PreH4 : (left_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (retval <= INT_MAX)) (PreH7 : (gy_pre >= INT_MIN)) (PreH8 : (gx_pre >= INT_MIN)) (PreH9 : (right_pre >= INT_MIN)) (PreH10 : (left_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (retval > left_pre)) (PreH14 : (left_pre <= retval)) (PreH15 : (retval <= right_pre)) (PreH16 : (FlatPoints flat_out pts_out)) (PreH17 : (PointPermutation pts_l pts_out)) (PreH18 : (PointSameOutsideRange pts_l pts_out left_pre right_pre)) (PreH19 : (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval)) (PreH20 : ((0 : Int) <= n_pre)) (PreH21 : (n_pre <= 50000)) (PreH22 : ((0 : Int) <= left_pre)) (PreH23 : (left_pre < right_pre)) (PreH24 : (right_pre < n_pre)) (PreH25 : (PointFlatModel flat)) (PreH26 : ((Zlength (flat)) = (2 * n_pre))) (PreH27 : ((-10000) <= gx_pre)) (PreH28 : (gx_pre <= 10000)) (PreH29 : ((-10000) <= gy_pre)) (PreH30 : (gy_pre <= 10000)) (PreH31 : (Forall ((LE.le (α := Int)) ((-10000))) flat)) (PreH32 : (Forall ((GE.ge (α := Int)) (10000)) flat)) (PreH33 : ((Zlength (pts_l)) = n_pre)) (PreH34 : (FlatPoints flat pts_l)) (PreH35 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH36 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH37 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH38 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  (intArray.full coords_pre (2 * n_pre) flat_out)
  ** ((( &( "p" ) )) # Int |-> (retval))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
|--
  “ (Forall ((GE.ge (α := Int)) (10000)) flat_out) ”

noncomputable def quicksort_points_range_partial_solve_wit_2_aux : Prop :=
  forall (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (gx_pre : Int) (gy_pre : Int) (pts_l : (List point)) (flat_out : (List Int)) (pts_out : (List point)) (retval : Int) (PreH1 : (retval > left_pre)) (PreH2 : (left_pre <= retval)) (PreH3 : (retval <= right_pre)) (PreH4 : (FlatPoints flat_out pts_out)) (PreH5 : (PointPermutation pts_l pts_out)) (PreH6 : (PointSameOutsideRange pts_l pts_out left_pre right_pre)) (PreH7 : (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval)) (PreH8 : ((0 : Int) <= n_pre)) (PreH9 : (n_pre <= 50000)) (PreH10 : ((0 : Int) <= left_pre)) (PreH11 : (left_pre < right_pre)) (PreH12 : (right_pre < n_pre)) (PreH13 : (PointFlatModel flat)) (PreH14 : ((Zlength (flat)) = (2 * n_pre))) (PreH15 : ((-10000) <= gx_pre)) (PreH16 : (gx_pre <= 10000)) (PreH17 : ((-10000) <= gy_pre)) (PreH18 : (gy_pre <= 10000)) (PreH19 : (Forall ((LE.le (α := Int)) ((-10000))) flat)) (PreH20 : (Forall ((GE.ge (α := Int)) (10000)) flat)) (PreH21 : ((Zlength (pts_l)) = n_pre)) (PreH22 : (FlatPoints flat pts_l)) (PreH23 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH24 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH25 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH26 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  (intArray.full coords_pre (2 * n_pre) flat_out)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ ((-1) <= (retval - 1)) ” &&
  “ ((retval - 1) < n_pre) ” &&
  “ ((-10000) <= gx_pre) ” &&
  “ (gx_pre <= 10000) ” &&
  “ ((-10000) <= gy_pre) ” &&
  “ (gy_pre <= 10000) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) flat_out) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) flat_out) ” &&
  “ ((Zlength (flat_out)) = (2 * n_pre)) ” &&
  “ (PointFlatModel flat_out) ” &&
  “ (retval > left_pre) ” &&
  “ (left_pre <= retval) ” &&
  “ (retval <= right_pre) ” &&
  “ (FlatPoints flat_out pts_out) ” &&
  “ (PointPermutation pts_l pts_out) ” &&
  “ (PointSameOutsideRange pts_l pts_out left_pre right_pre) ” &&
  “ (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre < right_pre) ” &&
  “ (right_pre < n_pre) ” &&
  “ (PointFlatModel flat) ” &&
  “ ((Zlength (flat)) = (2 * n_pre)) ” &&
  “ ((-10000) <= gx_pre) ” &&
  “ (gx_pre <= 10000) ” &&
  “ ((-10000) <= gy_pre) ” &&
  “ (gy_pre <= 10000) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) flat) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) flat) ” &&
  “ ((Zlength (pts_l)) = n_pre) ” &&
  “ (FlatPoints flat pts_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l)))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l)))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l)))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l)))) ”
  &&  (intArray.full coords_pre (2 * n_pre) flat_out)

noncomputable def quicksort_points_range_partial_solve_wit_2 : Prop := quicksort_points_range_partial_solve_wit_2_pure -> quicksort_points_range_partial_solve_wit_2_aux

noncomputable def quicksort_points_range_partial_solve_wit_3_pure : Prop :=
  (
forall (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (gx_pre : Int) (gy_pre : Int) (pts_l : (List point)) (flat_out_2 : (List Int)) (pts_out : (List point)) (retval : Int) (flat_out : (List Int)) (pts_out_2 : (List point)) (PreH1 : (retval < right_pre)) (PreH2 : (FlatPoints flat_out pts_out_2)) (PreH3 : (PointRangeSortResult (mk_point (gx_pre) (gy_pre)) flat_out_2 pts_out_2 left_pre (retval - 1))) (PreH4 : (retval > left_pre)) (PreH5 : (left_pre <= retval)) (PreH6 : (retval <= right_pre)) (PreH7 : (FlatPoints flat_out_2 pts_out)) (PreH8 : (PointPermutation pts_l pts_out)) (PreH9 : (PointSameOutsideRange pts_l pts_out left_pre right_pre)) (PreH10 : (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval)) (PreH11 : ((0 : Int) <= n_pre)) (PreH12 : (n_pre <= 50000)) (PreH13 : ((0 : Int) <= left_pre)) (PreH14 : (left_pre < right_pre)) (PreH15 : (right_pre < n_pre)) (PreH16 : (PointFlatModel flat)) (PreH17 : ((Zlength (flat)) = (2 * n_pre))) (PreH18 : ((-10000) <= gx_pre)) (PreH19 : (gx_pre <= 10000)) (PreH20 : ((-10000) <= gy_pre)) (PreH21 : (gy_pre <= 10000)) (PreH22 : (Forall ((LE.le (α := Int)) ((-10000))) flat)) (PreH23 : (Forall ((GE.ge (α := Int)) (10000)) flat)) (PreH24 : ((Zlength (pts_l)) = n_pre)) (PreH25 : (FlatPoints flat pts_l)) (PreH26 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH27 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH28 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH29 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  (intArray.full coords_pre (2 * n_pre) flat_out)
  ** ((( &( "p" ) )) # Int |-> (retval))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ ((0 : Int) <= (retval + 1)) ” &&
  “ ((-1) <= right_pre) ” &&
  “ (right_pre < n_pre) ” &&
  “ ((-10000) <= gx_pre) ” &&
  “ (gx_pre <= 10000) ” &&
  “ ((-10000) <= gy_pre) ” &&
  “ (gy_pre <= 10000) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) flat_out) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) flat_out) ” &&
  “ ((Zlength (flat_out)) = (2 * n_pre)) ” &&
  “ (PointFlatModel flat_out) ”
) \/
(
forall (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (gx_pre : Int) (gy_pre : Int) (pts_l : (List point)) (flat_out_2 : (List Int)) (pts_out : (List point)) (retval : Int) (flat_out : (List Int)) (pts_out_2 : (List point)) (PreH1 : (gy_pre <= INT_MAX)) (PreH2 : (gx_pre <= INT_MAX)) (PreH3 : (right_pre <= INT_MAX)) (PreH4 : (left_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (retval <= INT_MAX)) (PreH7 : (gy_pre >= INT_MIN)) (PreH8 : (gx_pre >= INT_MIN)) (PreH9 : (right_pre >= INT_MIN)) (PreH10 : (left_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (retval < right_pre)) (PreH14 : (FlatPoints flat_out pts_out_2)) (PreH15 : (PointRangeSortResult (mk_point (gx_pre) (gy_pre)) flat_out_2 pts_out_2 left_pre (retval - 1))) (PreH16 : (retval > left_pre)) (PreH17 : (left_pre <= retval)) (PreH18 : (retval <= right_pre)) (PreH19 : (FlatPoints flat_out_2 pts_out)) (PreH20 : (PointPermutation pts_l pts_out)) (PreH21 : (PointSameOutsideRange pts_l pts_out left_pre right_pre)) (PreH22 : (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval)) (PreH23 : ((0 : Int) <= n_pre)) (PreH24 : (n_pre <= 50000)) (PreH25 : ((0 : Int) <= left_pre)) (PreH26 : (left_pre < right_pre)) (PreH27 : (right_pre < n_pre)) (PreH28 : (PointFlatModel flat)) (PreH29 : ((Zlength (flat)) = (2 * n_pre))) (PreH30 : ((-10000) <= gx_pre)) (PreH31 : (gx_pre <= 10000)) (PreH32 : ((-10000) <= gy_pre)) (PreH33 : (gy_pre <= 10000)) (PreH34 : (Forall ((LE.le (α := Int)) ((-10000))) flat)) (PreH35 : (Forall ((GE.ge (α := Int)) (10000)) flat)) (PreH36 : ((Zlength (pts_l)) = n_pre)) (PreH37 : (FlatPoints flat pts_l)) (PreH38 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH39 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH40 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH41 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  (intArray.full coords_pre (2 * n_pre) flat_out)
  ** ((( &( "p" ) )) # Int |-> (retval))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
|--
  “ (PointFlatModel flat_out) ” &&
  “ ((Zlength (flat_out)) = (2 * n_pre)) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) flat_out) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) flat_out) ”
)

noncomputable def quicksort_points_range_partial_solve_wit_3_pure_split_goal_1 : Prop :=
  forall (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (gx_pre : Int) (gy_pre : Int) (pts_l : (List point)) (flat_out_2 : (List Int)) (pts_out : (List point)) (retval : Int) (flat_out : (List Int)) (pts_out_2 : (List point)) (PreH1 : (gy_pre <= INT_MAX)) (PreH2 : (gx_pre <= INT_MAX)) (PreH3 : (right_pre <= INT_MAX)) (PreH4 : (left_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (retval <= INT_MAX)) (PreH7 : (gy_pre >= INT_MIN)) (PreH8 : (gx_pre >= INT_MIN)) (PreH9 : (right_pre >= INT_MIN)) (PreH10 : (left_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (retval < right_pre)) (PreH14 : (FlatPoints flat_out pts_out_2)) (PreH15 : (PointRangeSortResult (mk_point (gx_pre) (gy_pre)) flat_out_2 pts_out_2 left_pre (retval - 1))) (PreH16 : (retval > left_pre)) (PreH17 : (left_pre <= retval)) (PreH18 : (retval <= right_pre)) (PreH19 : (FlatPoints flat_out_2 pts_out)) (PreH20 : (PointPermutation pts_l pts_out)) (PreH21 : (PointSameOutsideRange pts_l pts_out left_pre right_pre)) (PreH22 : (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval)) (PreH23 : ((0 : Int) <= n_pre)) (PreH24 : (n_pre <= 50000)) (PreH25 : ((0 : Int) <= left_pre)) (PreH26 : (left_pre < right_pre)) (PreH27 : (right_pre < n_pre)) (PreH28 : (PointFlatModel flat)) (PreH29 : ((Zlength (flat)) = (2 * n_pre))) (PreH30 : ((-10000) <= gx_pre)) (PreH31 : (gx_pre <= 10000)) (PreH32 : ((-10000) <= gy_pre)) (PreH33 : (gy_pre <= 10000)) (PreH34 : (Forall ((LE.le (α := Int)) ((-10000))) flat)) (PreH35 : (Forall ((GE.ge (α := Int)) (10000)) flat)) (PreH36 : ((Zlength (pts_l)) = n_pre)) (PreH37 : (FlatPoints flat pts_l)) (PreH38 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH39 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH40 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH41 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  (intArray.full coords_pre (2 * n_pre) flat_out)
  ** ((( &( "p" ) )) # Int |-> (retval))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
|--
  “ (PointFlatModel flat_out) ”

noncomputable def quicksort_points_range_partial_solve_wit_3_pure_split_goal_2 : Prop :=
  forall (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (gx_pre : Int) (gy_pre : Int) (pts_l : (List point)) (flat_out_2 : (List Int)) (pts_out : (List point)) (retval : Int) (flat_out : (List Int)) (pts_out_2 : (List point)) (PreH1 : (gy_pre <= INT_MAX)) (PreH2 : (gx_pre <= INT_MAX)) (PreH3 : (right_pre <= INT_MAX)) (PreH4 : (left_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (retval <= INT_MAX)) (PreH7 : (gy_pre >= INT_MIN)) (PreH8 : (gx_pre >= INT_MIN)) (PreH9 : (right_pre >= INT_MIN)) (PreH10 : (left_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (retval < right_pre)) (PreH14 : (FlatPoints flat_out pts_out_2)) (PreH15 : (PointRangeSortResult (mk_point (gx_pre) (gy_pre)) flat_out_2 pts_out_2 left_pre (retval - 1))) (PreH16 : (retval > left_pre)) (PreH17 : (left_pre <= retval)) (PreH18 : (retval <= right_pre)) (PreH19 : (FlatPoints flat_out_2 pts_out)) (PreH20 : (PointPermutation pts_l pts_out)) (PreH21 : (PointSameOutsideRange pts_l pts_out left_pre right_pre)) (PreH22 : (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval)) (PreH23 : ((0 : Int) <= n_pre)) (PreH24 : (n_pre <= 50000)) (PreH25 : ((0 : Int) <= left_pre)) (PreH26 : (left_pre < right_pre)) (PreH27 : (right_pre < n_pre)) (PreH28 : (PointFlatModel flat)) (PreH29 : ((Zlength (flat)) = (2 * n_pre))) (PreH30 : ((-10000) <= gx_pre)) (PreH31 : (gx_pre <= 10000)) (PreH32 : ((-10000) <= gy_pre)) (PreH33 : (gy_pre <= 10000)) (PreH34 : (Forall ((LE.le (α := Int)) ((-10000))) flat)) (PreH35 : (Forall ((GE.ge (α := Int)) (10000)) flat)) (PreH36 : ((Zlength (pts_l)) = n_pre)) (PreH37 : (FlatPoints flat pts_l)) (PreH38 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH39 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH40 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH41 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  (intArray.full coords_pre (2 * n_pre) flat_out)
  ** ((( &( "p" ) )) # Int |-> (retval))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
|--
  “ ((Zlength (flat_out)) = (2 * n_pre)) ”

noncomputable def quicksort_points_range_partial_solve_wit_3_pure_split_goal_3 : Prop :=
  forall (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (gx_pre : Int) (gy_pre : Int) (pts_l : (List point)) (flat_out_2 : (List Int)) (pts_out : (List point)) (retval : Int) (flat_out : (List Int)) (pts_out_2 : (List point)) (PreH1 : (gy_pre <= INT_MAX)) (PreH2 : (gx_pre <= INT_MAX)) (PreH3 : (right_pre <= INT_MAX)) (PreH4 : (left_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (retval <= INT_MAX)) (PreH7 : (gy_pre >= INT_MIN)) (PreH8 : (gx_pre >= INT_MIN)) (PreH9 : (right_pre >= INT_MIN)) (PreH10 : (left_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (retval < right_pre)) (PreH14 : (FlatPoints flat_out pts_out_2)) (PreH15 : (PointRangeSortResult (mk_point (gx_pre) (gy_pre)) flat_out_2 pts_out_2 left_pre (retval - 1))) (PreH16 : (retval > left_pre)) (PreH17 : (left_pre <= retval)) (PreH18 : (retval <= right_pre)) (PreH19 : (FlatPoints flat_out_2 pts_out)) (PreH20 : (PointPermutation pts_l pts_out)) (PreH21 : (PointSameOutsideRange pts_l pts_out left_pre right_pre)) (PreH22 : (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval)) (PreH23 : ((0 : Int) <= n_pre)) (PreH24 : (n_pre <= 50000)) (PreH25 : ((0 : Int) <= left_pre)) (PreH26 : (left_pre < right_pre)) (PreH27 : (right_pre < n_pre)) (PreH28 : (PointFlatModel flat)) (PreH29 : ((Zlength (flat)) = (2 * n_pre))) (PreH30 : ((-10000) <= gx_pre)) (PreH31 : (gx_pre <= 10000)) (PreH32 : ((-10000) <= gy_pre)) (PreH33 : (gy_pre <= 10000)) (PreH34 : (Forall ((LE.le (α := Int)) ((-10000))) flat)) (PreH35 : (Forall ((GE.ge (α := Int)) (10000)) flat)) (PreH36 : ((Zlength (pts_l)) = n_pre)) (PreH37 : (FlatPoints flat pts_l)) (PreH38 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH39 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH40 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH41 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  (intArray.full coords_pre (2 * n_pre) flat_out)
  ** ((( &( "p" ) )) # Int |-> (retval))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
|--
  “ (Forall ((LE.le (α := Int)) ((-10000))) flat_out) ”

noncomputable def quicksort_points_range_partial_solve_wit_3_pure_split_goal_4 : Prop :=
  forall (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (gx_pre : Int) (gy_pre : Int) (pts_l : (List point)) (flat_out_2 : (List Int)) (pts_out : (List point)) (retval : Int) (flat_out : (List Int)) (pts_out_2 : (List point)) (PreH1 : (gy_pre <= INT_MAX)) (PreH2 : (gx_pre <= INT_MAX)) (PreH3 : (right_pre <= INT_MAX)) (PreH4 : (left_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (retval <= INT_MAX)) (PreH7 : (gy_pre >= INT_MIN)) (PreH8 : (gx_pre >= INT_MIN)) (PreH9 : (right_pre >= INT_MIN)) (PreH10 : (left_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (retval < right_pre)) (PreH14 : (FlatPoints flat_out pts_out_2)) (PreH15 : (PointRangeSortResult (mk_point (gx_pre) (gy_pre)) flat_out_2 pts_out_2 left_pre (retval - 1))) (PreH16 : (retval > left_pre)) (PreH17 : (left_pre <= retval)) (PreH18 : (retval <= right_pre)) (PreH19 : (FlatPoints flat_out_2 pts_out)) (PreH20 : (PointPermutation pts_l pts_out)) (PreH21 : (PointSameOutsideRange pts_l pts_out left_pre right_pre)) (PreH22 : (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval)) (PreH23 : ((0 : Int) <= n_pre)) (PreH24 : (n_pre <= 50000)) (PreH25 : ((0 : Int) <= left_pre)) (PreH26 : (left_pre < right_pre)) (PreH27 : (right_pre < n_pre)) (PreH28 : (PointFlatModel flat)) (PreH29 : ((Zlength (flat)) = (2 * n_pre))) (PreH30 : ((-10000) <= gx_pre)) (PreH31 : (gx_pre <= 10000)) (PreH32 : ((-10000) <= gy_pre)) (PreH33 : (gy_pre <= 10000)) (PreH34 : (Forall ((LE.le (α := Int)) ((-10000))) flat)) (PreH35 : (Forall ((GE.ge (α := Int)) (10000)) flat)) (PreH36 : ((Zlength (pts_l)) = n_pre)) (PreH37 : (FlatPoints flat pts_l)) (PreH38 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH39 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH40 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH41 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  (intArray.full coords_pre (2 * n_pre) flat_out)
  ** ((( &( "p" ) )) # Int |-> (retval))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
|--
  “ (Forall ((GE.ge (α := Int)) (10000)) flat_out) ”

noncomputable def quicksort_points_range_partial_solve_wit_3_aux : Prop :=
  forall (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (gx_pre : Int) (gy_pre : Int) (pts_l : (List point)) (flat_out_2 : (List Int)) (pts_out : (List point)) (retval : Int) (flat_out : (List Int)) (pts_out_2 : (List point)) (PreH1 : (retval < right_pre)) (PreH2 : (FlatPoints flat_out pts_out_2)) (PreH3 : (PointRangeSortResult (mk_point (gx_pre) (gy_pre)) flat_out_2 pts_out_2 left_pre (retval - 1))) (PreH4 : (retval > left_pre)) (PreH5 : (left_pre <= retval)) (PreH6 : (retval <= right_pre)) (PreH7 : (FlatPoints flat_out_2 pts_out)) (PreH8 : (PointPermutation pts_l pts_out)) (PreH9 : (PointSameOutsideRange pts_l pts_out left_pre right_pre)) (PreH10 : (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval)) (PreH11 : ((0 : Int) <= n_pre)) (PreH12 : (n_pre <= 50000)) (PreH13 : ((0 : Int) <= left_pre)) (PreH14 : (left_pre < right_pre)) (PreH15 : (right_pre < n_pre)) (PreH16 : (PointFlatModel flat)) (PreH17 : ((Zlength (flat)) = (2 * n_pre))) (PreH18 : ((-10000) <= gx_pre)) (PreH19 : (gx_pre <= 10000)) (PreH20 : ((-10000) <= gy_pre)) (PreH21 : (gy_pre <= 10000)) (PreH22 : (Forall ((LE.le (α := Int)) ((-10000))) flat)) (PreH23 : (Forall ((GE.ge (α := Int)) (10000)) flat)) (PreH24 : ((Zlength (pts_l)) = n_pre)) (PreH25 : (FlatPoints flat pts_l)) (PreH26 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH27 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH28 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH29 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  (intArray.full coords_pre (2 * n_pre) flat_out)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ ((0 : Int) <= (retval + 1)) ” &&
  “ ((-1) <= right_pre) ” &&
  “ (right_pre < n_pre) ” &&
  “ ((-10000) <= gx_pre) ” &&
  “ (gx_pre <= 10000) ” &&
  “ ((-10000) <= gy_pre) ” &&
  “ (gy_pre <= 10000) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) flat_out) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) flat_out) ” &&
  “ ((Zlength (flat_out)) = (2 * n_pre)) ” &&
  “ (PointFlatModel flat_out) ” &&
  “ (retval < right_pre) ” &&
  “ (FlatPoints flat_out pts_out_2) ” &&
  “ (PointRangeSortResult (mk_point (gx_pre) (gy_pre)) flat_out_2 pts_out_2 left_pre (retval - 1)) ” &&
  “ (retval > left_pre) ” &&
  “ (left_pre <= retval) ” &&
  “ (retval <= right_pre) ” &&
  “ (FlatPoints flat_out_2 pts_out) ” &&
  “ (PointPermutation pts_l pts_out) ” &&
  “ (PointSameOutsideRange pts_l pts_out left_pre right_pre) ” &&
  “ (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre < right_pre) ” &&
  “ (right_pre < n_pre) ” &&
  “ (PointFlatModel flat) ” &&
  “ ((Zlength (flat)) = (2 * n_pre)) ” &&
  “ ((-10000) <= gx_pre) ” &&
  “ (gx_pre <= 10000) ” &&
  “ ((-10000) <= gy_pre) ” &&
  “ (gy_pre <= 10000) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) flat) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) flat) ” &&
  “ ((Zlength (pts_l)) = n_pre) ” &&
  “ (FlatPoints flat pts_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l)))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l)))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l)))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l)))) ”
  &&  (intArray.full coords_pre (2 * n_pre) flat_out)

noncomputable def quicksort_points_range_partial_solve_wit_3 : Prop := quicksort_points_range_partial_solve_wit_3_pure -> quicksort_points_range_partial_solve_wit_3_aux

noncomputable def quicksort_points_range_partial_solve_wit_4_pure : Prop :=
  (
forall (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (gx_pre : Int) (gy_pre : Int) (pts_l : (List point)) (flat_out : (List Int)) (pts_out : (List point)) (retval : Int) (PreH1 : (retval < right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : (FlatPoints flat_out pts_out)) (PreH6 : (PointPermutation pts_l pts_out)) (PreH7 : (PointSameOutsideRange pts_l pts_out left_pre right_pre)) (PreH8 : (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval)) (PreH9 : ((0 : Int) <= n_pre)) (PreH10 : (n_pre <= 50000)) (PreH11 : ((0 : Int) <= left_pre)) (PreH12 : (left_pre < right_pre)) (PreH13 : (right_pre < n_pre)) (PreH14 : (PointFlatModel flat)) (PreH15 : ((Zlength (flat)) = (2 * n_pre))) (PreH16 : ((-10000) <= gx_pre)) (PreH17 : (gx_pre <= 10000)) (PreH18 : ((-10000) <= gy_pre)) (PreH19 : (gy_pre <= 10000)) (PreH20 : (Forall ((LE.le (α := Int)) ((-10000))) flat)) (PreH21 : (Forall ((GE.ge (α := Int)) (10000)) flat)) (PreH22 : ((Zlength (pts_l)) = n_pre)) (PreH23 : (FlatPoints flat pts_l)) (PreH24 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH25 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH26 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH27 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  (intArray.full coords_pre (2 * n_pre) flat_out)
  ** ((( &( "p" ) )) # Int |-> (retval))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ ((0 : Int) <= (retval + 1)) ” &&
  “ ((-1) <= right_pre) ” &&
  “ (right_pre < n_pre) ” &&
  “ ((-10000) <= gx_pre) ” &&
  “ (gx_pre <= 10000) ” &&
  “ ((-10000) <= gy_pre) ” &&
  “ (gy_pre <= 10000) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) flat_out) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) flat_out) ” &&
  “ ((Zlength (flat_out)) = (2 * n_pre)) ” &&
  “ (PointFlatModel flat_out) ”
) \/
(
forall (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (gx_pre : Int) (gy_pre : Int) (pts_l : (List point)) (flat_out : (List Int)) (pts_out : (List point)) (retval : Int) (PreH1 : (gy_pre <= INT_MAX)) (PreH2 : (gx_pre <= INT_MAX)) (PreH3 : (right_pre <= INT_MAX)) (PreH4 : (left_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (retval <= INT_MAX)) (PreH7 : (gy_pre >= INT_MIN)) (PreH8 : (gx_pre >= INT_MIN)) (PreH9 : (right_pre >= INT_MIN)) (PreH10 : (left_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (retval < right_pre)) (PreH14 : (retval <= left_pre)) (PreH15 : (left_pre <= retval)) (PreH16 : (retval <= right_pre)) (PreH17 : (FlatPoints flat_out pts_out)) (PreH18 : (PointPermutation pts_l pts_out)) (PreH19 : (PointSameOutsideRange pts_l pts_out left_pre right_pre)) (PreH20 : (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval)) (PreH21 : ((0 : Int) <= n_pre)) (PreH22 : (n_pre <= 50000)) (PreH23 : ((0 : Int) <= left_pre)) (PreH24 : (left_pre < right_pre)) (PreH25 : (right_pre < n_pre)) (PreH26 : (PointFlatModel flat)) (PreH27 : ((Zlength (flat)) = (2 * n_pre))) (PreH28 : ((-10000) <= gx_pre)) (PreH29 : (gx_pre <= 10000)) (PreH30 : ((-10000) <= gy_pre)) (PreH31 : (gy_pre <= 10000)) (PreH32 : (Forall ((LE.le (α := Int)) ((-10000))) flat)) (PreH33 : (Forall ((GE.ge (α := Int)) (10000)) flat)) (PreH34 : ((Zlength (pts_l)) = n_pre)) (PreH35 : (FlatPoints flat pts_l)) (PreH36 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH37 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH38 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH39 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  (intArray.full coords_pre (2 * n_pre) flat_out)
  ** ((( &( "p" ) )) # Int |-> (retval))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
|--
  “ (PointFlatModel flat_out) ” &&
  “ ((Zlength (flat_out)) = (2 * n_pre)) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) flat_out) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) flat_out) ”
)

noncomputable def quicksort_points_range_partial_solve_wit_4_pure_split_goal_1 : Prop :=
  forall (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (gx_pre : Int) (gy_pre : Int) (pts_l : (List point)) (flat_out : (List Int)) (pts_out : (List point)) (retval : Int) (PreH1 : (gy_pre <= INT_MAX)) (PreH2 : (gx_pre <= INT_MAX)) (PreH3 : (right_pre <= INT_MAX)) (PreH4 : (left_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (retval <= INT_MAX)) (PreH7 : (gy_pre >= INT_MIN)) (PreH8 : (gx_pre >= INT_MIN)) (PreH9 : (right_pre >= INT_MIN)) (PreH10 : (left_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (retval < right_pre)) (PreH14 : (retval <= left_pre)) (PreH15 : (left_pre <= retval)) (PreH16 : (retval <= right_pre)) (PreH17 : (FlatPoints flat_out pts_out)) (PreH18 : (PointPermutation pts_l pts_out)) (PreH19 : (PointSameOutsideRange pts_l pts_out left_pre right_pre)) (PreH20 : (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval)) (PreH21 : ((0 : Int) <= n_pre)) (PreH22 : (n_pre <= 50000)) (PreH23 : ((0 : Int) <= left_pre)) (PreH24 : (left_pre < right_pre)) (PreH25 : (right_pre < n_pre)) (PreH26 : (PointFlatModel flat)) (PreH27 : ((Zlength (flat)) = (2 * n_pre))) (PreH28 : ((-10000) <= gx_pre)) (PreH29 : (gx_pre <= 10000)) (PreH30 : ((-10000) <= gy_pre)) (PreH31 : (gy_pre <= 10000)) (PreH32 : (Forall ((LE.le (α := Int)) ((-10000))) flat)) (PreH33 : (Forall ((GE.ge (α := Int)) (10000)) flat)) (PreH34 : ((Zlength (pts_l)) = n_pre)) (PreH35 : (FlatPoints flat pts_l)) (PreH36 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH37 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH38 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH39 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  (intArray.full coords_pre (2 * n_pre) flat_out)
  ** ((( &( "p" ) )) # Int |-> (retval))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
|--
  “ (PointFlatModel flat_out) ”

noncomputable def quicksort_points_range_partial_solve_wit_4_pure_split_goal_2 : Prop :=
  forall (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (gx_pre : Int) (gy_pre : Int) (pts_l : (List point)) (flat_out : (List Int)) (pts_out : (List point)) (retval : Int) (PreH1 : (gy_pre <= INT_MAX)) (PreH2 : (gx_pre <= INT_MAX)) (PreH3 : (right_pre <= INT_MAX)) (PreH4 : (left_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (retval <= INT_MAX)) (PreH7 : (gy_pre >= INT_MIN)) (PreH8 : (gx_pre >= INT_MIN)) (PreH9 : (right_pre >= INT_MIN)) (PreH10 : (left_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (retval < right_pre)) (PreH14 : (retval <= left_pre)) (PreH15 : (left_pre <= retval)) (PreH16 : (retval <= right_pre)) (PreH17 : (FlatPoints flat_out pts_out)) (PreH18 : (PointPermutation pts_l pts_out)) (PreH19 : (PointSameOutsideRange pts_l pts_out left_pre right_pre)) (PreH20 : (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval)) (PreH21 : ((0 : Int) <= n_pre)) (PreH22 : (n_pre <= 50000)) (PreH23 : ((0 : Int) <= left_pre)) (PreH24 : (left_pre < right_pre)) (PreH25 : (right_pre < n_pre)) (PreH26 : (PointFlatModel flat)) (PreH27 : ((Zlength (flat)) = (2 * n_pre))) (PreH28 : ((-10000) <= gx_pre)) (PreH29 : (gx_pre <= 10000)) (PreH30 : ((-10000) <= gy_pre)) (PreH31 : (gy_pre <= 10000)) (PreH32 : (Forall ((LE.le (α := Int)) ((-10000))) flat)) (PreH33 : (Forall ((GE.ge (α := Int)) (10000)) flat)) (PreH34 : ((Zlength (pts_l)) = n_pre)) (PreH35 : (FlatPoints flat pts_l)) (PreH36 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH37 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH38 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH39 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  (intArray.full coords_pre (2 * n_pre) flat_out)
  ** ((( &( "p" ) )) # Int |-> (retval))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
|--
  “ ((Zlength (flat_out)) = (2 * n_pre)) ”

noncomputable def quicksort_points_range_partial_solve_wit_4_pure_split_goal_3 : Prop :=
  forall (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (gx_pre : Int) (gy_pre : Int) (pts_l : (List point)) (flat_out : (List Int)) (pts_out : (List point)) (retval : Int) (PreH1 : (gy_pre <= INT_MAX)) (PreH2 : (gx_pre <= INT_MAX)) (PreH3 : (right_pre <= INT_MAX)) (PreH4 : (left_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (retval <= INT_MAX)) (PreH7 : (gy_pre >= INT_MIN)) (PreH8 : (gx_pre >= INT_MIN)) (PreH9 : (right_pre >= INT_MIN)) (PreH10 : (left_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (retval < right_pre)) (PreH14 : (retval <= left_pre)) (PreH15 : (left_pre <= retval)) (PreH16 : (retval <= right_pre)) (PreH17 : (FlatPoints flat_out pts_out)) (PreH18 : (PointPermutation pts_l pts_out)) (PreH19 : (PointSameOutsideRange pts_l pts_out left_pre right_pre)) (PreH20 : (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval)) (PreH21 : ((0 : Int) <= n_pre)) (PreH22 : (n_pre <= 50000)) (PreH23 : ((0 : Int) <= left_pre)) (PreH24 : (left_pre < right_pre)) (PreH25 : (right_pre < n_pre)) (PreH26 : (PointFlatModel flat)) (PreH27 : ((Zlength (flat)) = (2 * n_pre))) (PreH28 : ((-10000) <= gx_pre)) (PreH29 : (gx_pre <= 10000)) (PreH30 : ((-10000) <= gy_pre)) (PreH31 : (gy_pre <= 10000)) (PreH32 : (Forall ((LE.le (α := Int)) ((-10000))) flat)) (PreH33 : (Forall ((GE.ge (α := Int)) (10000)) flat)) (PreH34 : ((Zlength (pts_l)) = n_pre)) (PreH35 : (FlatPoints flat pts_l)) (PreH36 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH37 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH38 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH39 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  (intArray.full coords_pre (2 * n_pre) flat_out)
  ** ((( &( "p" ) )) # Int |-> (retval))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
|--
  “ (Forall ((LE.le (α := Int)) ((-10000))) flat_out) ”

noncomputable def quicksort_points_range_partial_solve_wit_4_pure_split_goal_4 : Prop :=
  forall (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (gx_pre : Int) (gy_pre : Int) (pts_l : (List point)) (flat_out : (List Int)) (pts_out : (List point)) (retval : Int) (PreH1 : (gy_pre <= INT_MAX)) (PreH2 : (gx_pre <= INT_MAX)) (PreH3 : (right_pre <= INT_MAX)) (PreH4 : (left_pre <= INT_MAX)) (PreH5 : (n_pre <= INT_MAX)) (PreH6 : (retval <= INT_MAX)) (PreH7 : (gy_pre >= INT_MIN)) (PreH8 : (gx_pre >= INT_MIN)) (PreH9 : (right_pre >= INT_MIN)) (PreH10 : (left_pre >= INT_MIN)) (PreH11 : (n_pre >= INT_MIN)) (PreH12 : (retval >= INT_MIN)) (PreH13 : (retval < right_pre)) (PreH14 : (retval <= left_pre)) (PreH15 : (left_pre <= retval)) (PreH16 : (retval <= right_pre)) (PreH17 : (FlatPoints flat_out pts_out)) (PreH18 : (PointPermutation pts_l pts_out)) (PreH19 : (PointSameOutsideRange pts_l pts_out left_pre right_pre)) (PreH20 : (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval)) (PreH21 : ((0 : Int) <= n_pre)) (PreH22 : (n_pre <= 50000)) (PreH23 : ((0 : Int) <= left_pre)) (PreH24 : (left_pre < right_pre)) (PreH25 : (right_pre < n_pre)) (PreH26 : (PointFlatModel flat)) (PreH27 : ((Zlength (flat)) = (2 * n_pre))) (PreH28 : ((-10000) <= gx_pre)) (PreH29 : (gx_pre <= 10000)) (PreH30 : ((-10000) <= gy_pre)) (PreH31 : (gy_pre <= 10000)) (PreH32 : (Forall ((LE.le (α := Int)) ((-10000))) flat)) (PreH33 : (Forall ((GE.ge (α := Int)) (10000)) flat)) (PreH34 : ((Zlength (pts_l)) = n_pre)) (PreH35 : (FlatPoints flat pts_l)) (PreH36 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH37 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH38 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH39 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  (intArray.full coords_pre (2 * n_pre) flat_out)
  ** ((( &( "p" ) )) # Int |-> (retval))
  ** ((( &( "coords" ) )) # Ptr |-> (coords_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "left" ) )) # Int |-> (left_pre))
  ** ((( &( "right" ) )) # Int |-> (right_pre))
  ** ((( &( "gx" ) )) # Int |-> (gx_pre))
  ** ((( &( "gy" ) )) # Int |-> (gy_pre))
|--
  “ (Forall ((GE.ge (α := Int)) (10000)) flat_out) ”

noncomputable def quicksort_points_range_partial_solve_wit_4_aux : Prop :=
  forall (flat : (List Int)) (coords_pre : Int) (n_pre : Int) (left_pre : Int) (right_pre : Int) (gx_pre : Int) (gy_pre : Int) (pts_l : (List point)) (flat_out : (List Int)) (pts_out : (List point)) (retval : Int) (PreH1 : (retval < right_pre)) (PreH2 : (retval <= left_pre)) (PreH3 : (left_pre <= retval)) (PreH4 : (retval <= right_pre)) (PreH5 : (FlatPoints flat_out pts_out)) (PreH6 : (PointPermutation pts_l pts_out)) (PreH7 : (PointSameOutsideRange pts_l pts_out left_pre right_pre)) (PreH8 : (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval)) (PreH9 : ((0 : Int) <= n_pre)) (PreH10 : (n_pre <= 50000)) (PreH11 : ((0 : Int) <= left_pre)) (PreH12 : (left_pre < right_pre)) (PreH13 : (right_pre < n_pre)) (PreH14 : (PointFlatModel flat)) (PreH15 : ((Zlength (flat)) = (2 * n_pre))) (PreH16 : ((-10000) <= gx_pre)) (PreH17 : (gx_pre <= 10000)) (PreH18 : ((-10000) <= gy_pre)) (PreH19 : (gy_pre <= 10000)) (PreH20 : (Forall ((LE.le (α := Int)) ((-10000))) flat)) (PreH21 : (Forall ((GE.ge (α := Int)) (10000)) flat)) (PreH22 : ((Zlength (pts_l)) = n_pre)) (PreH23 : (FlatPoints flat pts_l)) (PreH24 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH25 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH26 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) (PreH27 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l))))) ,
  (intArray.full coords_pre (2 * n_pre) flat_out)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ ((0 : Int) <= (retval + 1)) ” &&
  “ ((-1) <= right_pre) ” &&
  “ (right_pre < n_pre) ” &&
  “ ((-10000) <= gx_pre) ” &&
  “ (gx_pre <= 10000) ” &&
  “ ((-10000) <= gy_pre) ” &&
  “ (gy_pre <= 10000) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) flat_out) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) flat_out) ” &&
  “ ((Zlength (flat_out)) = (2 * n_pre)) ” &&
  “ (PointFlatModel flat_out) ” &&
  “ (retval < right_pre) ” &&
  “ (retval <= left_pre) ” &&
  “ (left_pre <= retval) ” &&
  “ (retval <= right_pre) ” &&
  “ (FlatPoints flat_out pts_out) ” &&
  “ (PointPermutation pts_l pts_out) ” &&
  “ (PointSameOutsideRange pts_l pts_out left_pre right_pre) ” &&
  “ (PointPartitionedAt (mk_point (gx_pre) (gy_pre)) pts_out left_pre right_pre retval) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ ((0 : Int) <= left_pre) ” &&
  “ (left_pre < right_pre) ” &&
  “ (right_pre < n_pre) ” &&
  “ (PointFlatModel flat) ” &&
  “ ((Zlength (flat)) = (2 * n_pre)) ” &&
  “ ((-10000) <= gx_pre) ” &&
  “ (gx_pre <= 10000) ” &&
  “ ((-10000) <= gy_pre) ” &&
  “ (gy_pre <= 10000) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) flat) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) flat) ” &&
  “ ((Zlength (pts_l)) = n_pre) ” &&
  “ (FlatPoints flat pts_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l)))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx_pre) (gy_pre)) :: pts_l)))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l)))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx_pre) (gy_pre)) :: pts_l)))) ”
  &&  (intArray.full coords_pre (2 * n_pre) flat_out)

noncomputable def quicksort_points_range_partial_solve_wit_4 : Prop := quicksort_points_range_partial_solve_wit_4_pure -> quicksort_points_range_partial_solve_wit_4_aux

noncomputable def sort_safety_wit_1 : Prop :=
  forall (gy : Int) (gx : Int) (pts_l : (List point)) (flat : (List Int)) (pts_pre : Int) (n_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((Zlength (pts_l)) = n_pre)) (PreH4 : (FlatPoints flat pts_l)) (PreH5 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx) (gy)) :: pts_l))))) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx) (gy)) :: pts_l))))) (PreH7 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx) (gy)) :: pts_l))))) (PreH8 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx) (gy)) :: pts_l))))) ,
  ((( &( "coords" ) )) # Ptr |-> (pts_pre))
  ** ((( &( "pts" ) )) # Ptr |-> (pts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((&(( &( "gp" ) ) ->ₛ "x")) # Int |-> (gx))
  ** ((&(( &( "gp" ) ) ->ₛ "y")) # Int |-> (gy))
  ** (intArray.full pts_pre (2 * n_pre) flat)
|--
  “ ((n_pre - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre - 1)) ”

noncomputable def sort_safety_wit_2 : Prop :=
  forall (gy : Int) (gx : Int) (pts_l : (List point)) (flat : (List Int)) (pts_pre : Int) (n_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((Zlength (pts_l)) = n_pre)) (PreH4 : (FlatPoints flat pts_l)) (PreH5 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx) (gy)) :: pts_l))))) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx) (gy)) :: pts_l))))) (PreH7 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx) (gy)) :: pts_l))))) (PreH8 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx) (gy)) :: pts_l))))) ,
  ((( &( "coords" ) )) # Ptr |-> (pts_pre))
  ** ((( &( "pts" ) )) # Ptr |-> (pts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((&(( &( "gp" ) ) ->ₛ "x")) # Int |-> (gx))
  ** ((&(( &( "gp" ) ) ->ₛ "y")) # Int |-> (gy))
  ** (intArray.full pts_pre (2 * n_pre) flat)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def sort_safety_wit_3 : Prop :=
  forall (gy : Int) (gx : Int) (pts_l : (List point)) (flat : (List Int)) (pts_pre : Int) (n_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((Zlength (pts_l)) = n_pre)) (PreH4 : (FlatPoints flat pts_l)) (PreH5 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx) (gy)) :: pts_l))))) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx) (gy)) :: pts_l))))) (PreH7 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx) (gy)) :: pts_l))))) (PreH8 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx) (gy)) :: pts_l))))) ,
  ((( &( "coords" ) )) # Ptr |-> (pts_pre))
  ** ((( &( "pts" ) )) # Ptr |-> (pts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((&(( &( "gp" ) ) ->ₛ "x")) # Int |-> (gx))
  ** ((&(( &( "gp" ) ) ->ₛ "y")) # Int |-> (gy))
  ** (intArray.full pts_pre (2 * n_pre) flat)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def sort_return_wit_1 : Prop :=
  (
forall (gy : Int) (gx : Int) (pts_l : (List point)) (flat : (List Int)) (pts_pre : Int) (n_pre : Int) (flat_out_2 : (List Int)) (pts_out_2 : (List point)) (PreH1 : (FlatPoints flat_out_2 pts_out_2)) (PreH2 : (PointRangeSortResult (mk_point (gx) (gy)) flat pts_out_2 (0 : Int) (n_pre - 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : ((Zlength (pts_l)) = n_pre)) (PreH6 : (FlatPoints flat pts_l)) (PreH7 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx) (gy)) :: pts_l))))) (PreH8 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx) (gy)) :: pts_l))))) (PreH9 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx) (gy)) :: pts_l))))) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx) (gy)) :: pts_l))))) ,
  (intArray.full pts_pre (2 * n_pre) flat_out_2)
  ** ((&(( &( "gp" ) ) ->ₛ "x")) # Int |-> (gx))
  ** ((&(( &( "gp" ) ) ->ₛ "y")) # Int |-> (gy))
|--
  EX flat_out : (List Int), EX pts_out : (List point),
  “ (FlatPoints flat_out pts_out) ” &&
  “ (PointPermutation pts_l pts_out) ” &&
  “ (PolarSorted (mk_point (gx) (gy)) pts_out) ”
  &&  ((&(( &( "gp" ) ) ->ₛ "x")) # Int |-> (gx))
  ** ((&(( &( "gp" ) ) ->ₛ "y")) # Int |-> (gy))
  ** (intArray.full pts_pre (2 * n_pre) flat_out)
) \/
(
forall (gy : Int) (gx : Int) (pts_l : (List point)) (flat : (List Int)) (n_pre : Int) (flat_out_2 : (List Int)) (pts_out_2 : (List point)) (PreH1 : (FlatPoints flat_out_2 pts_out_2)) (PreH2 : (PointRangeSortResult (mk_point (gx) (gy)) flat pts_out_2 (0 : Int) (n_pre - 1))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : (n_pre <= 50000)) (PreH5 : ((Zlength (pts_l)) = n_pre)) (PreH6 : (FlatPoints flat pts_l)) (PreH7 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx) (gy)) :: pts_l))))) (PreH8 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx) (gy)) :: pts_l))))) (PreH9 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx) (gy)) :: pts_l))))) (PreH10 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx) (gy)) :: pts_l))))) ,
  TT && emp 
|--
  EX pts_out : (List point),
  “ (FlatPoints flat_out_2 pts_out) ” &&
  “ (PointPermutation pts_l pts_out) ” &&
  “ (PolarSorted (mk_point (gx) (gy)) pts_out) ”
  &&  emp
)

noncomputable def sort_partial_solve_wit_1_pure : Prop :=
  (
forall (gy : Int) (gx : Int) (pts_l : (List point)) (flat : (List Int)) (pts_pre : Int) (n_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((Zlength (pts_l)) = n_pre)) (PreH4 : (FlatPoints flat pts_l)) (PreH5 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx) (gy)) :: pts_l))))) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx) (gy)) :: pts_l))))) (PreH7 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx) (gy)) :: pts_l))))) (PreH8 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx) (gy)) :: pts_l))))) ,
  ((( &( "coords" ) )) # Ptr |-> (pts_pre))
  ** ((( &( "pts" ) )) # Ptr |-> (pts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((&(( &( "gp" ) ) ->ₛ "x")) # Int |-> (gx))
  ** ((&(( &( "gp" ) ) ->ₛ "y")) # Int |-> (gy))
  ** (intArray.full pts_pre (2 * n_pre) flat)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((-1) <= (n_pre - 1)) ” &&
  “ ((n_pre - 1) < n_pre) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) flat) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) flat) ” &&
  “ (gy <= 10000) ” &&
  “ ((-10000) <= gy) ” &&
  “ (gx <= 10000) ” &&
  “ ((-10000) <= gx) ” &&
  “ ((Zlength (flat)) = (2 * n_pre)) ” &&
  “ (PointFlatModel flat) ”
) \/
(
forall (gy : Int) (gx : Int) (pts_l : (List point)) (flat : (List Int)) (pts_pre : Int) (n_pre : Int) (PreH1 : (gy <= INT_MAX)) (PreH2 : (gx <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (gy >= INT_MIN)) (PreH5 : (gx >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : ((0 : Int) <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l)) = n_pre)) (PreH10 : (FlatPoints flat pts_l)) (PreH11 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx) (gy)) :: pts_l))))) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx) (gy)) :: pts_l))))) (PreH13 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx) (gy)) :: pts_l))))) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx) (gy)) :: pts_l))))) ,
  ((( &( "coords" ) )) # Ptr |-> (pts_pre))
  ** ((( &( "pts" ) )) # Ptr |-> (pts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((&(( &( "gp" ) ) ->ₛ "x")) # Int |-> (gx))
  ** ((&(( &( "gp" ) ) ->ₛ "y")) # Int |-> (gy))
  ** (intArray.full pts_pre (2 * n_pre) flat)
|--
  “ (PointFlatModel flat) ” &&
  “ ((Zlength (flat)) = (2 * n_pre)) ” &&
  “ ((-10000) <= gx) ” &&
  “ (gx <= 10000) ” &&
  “ ((-10000) <= gy) ” &&
  “ (gy <= 10000) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) flat) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) flat) ”
)

noncomputable def sort_partial_solve_wit_1_pure_split_goal_1 : Prop :=
  forall (gy : Int) (gx : Int) (pts_l : (List point)) (flat : (List Int)) (pts_pre : Int) (n_pre : Int) (PreH1 : (gy <= INT_MAX)) (PreH2 : (gx <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (gy >= INT_MIN)) (PreH5 : (gx >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : ((0 : Int) <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l)) = n_pre)) (PreH10 : (FlatPoints flat pts_l)) (PreH11 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx) (gy)) :: pts_l))))) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx) (gy)) :: pts_l))))) (PreH13 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx) (gy)) :: pts_l))))) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx) (gy)) :: pts_l))))) ,
  ((( &( "coords" ) )) # Ptr |-> (pts_pre))
  ** ((( &( "pts" ) )) # Ptr |-> (pts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((&(( &( "gp" ) ) ->ₛ "x")) # Int |-> (gx))
  ** ((&(( &( "gp" ) ) ->ₛ "y")) # Int |-> (gy))
  ** (intArray.full pts_pre (2 * n_pre) flat)
|--
  “ (PointFlatModel flat) ”

noncomputable def sort_partial_solve_wit_1_pure_split_goal_2 : Prop :=
  forall (gy : Int) (gx : Int) (pts_l : (List point)) (flat : (List Int)) (pts_pre : Int) (n_pre : Int) (PreH1 : (gy <= INT_MAX)) (PreH2 : (gx <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (gy >= INT_MIN)) (PreH5 : (gx >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : ((0 : Int) <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l)) = n_pre)) (PreH10 : (FlatPoints flat pts_l)) (PreH11 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx) (gy)) :: pts_l))))) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx) (gy)) :: pts_l))))) (PreH13 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx) (gy)) :: pts_l))))) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx) (gy)) :: pts_l))))) ,
  ((( &( "coords" ) )) # Ptr |-> (pts_pre))
  ** ((( &( "pts" ) )) # Ptr |-> (pts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((&(( &( "gp" ) ) ->ₛ "x")) # Int |-> (gx))
  ** ((&(( &( "gp" ) ) ->ₛ "y")) # Int |-> (gy))
  ** (intArray.full pts_pre (2 * n_pre) flat)
|--
  “ ((Zlength (flat)) = (2 * n_pre)) ”

noncomputable def sort_partial_solve_wit_1_pure_split_goal_3 : Prop :=
  forall (gy : Int) (gx : Int) (pts_l : (List point)) (flat : (List Int)) (pts_pre : Int) (n_pre : Int) (PreH1 : (gy <= INT_MAX)) (PreH2 : (gx <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (gy >= INT_MIN)) (PreH5 : (gx >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : ((0 : Int) <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l)) = n_pre)) (PreH10 : (FlatPoints flat pts_l)) (PreH11 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx) (gy)) :: pts_l))))) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx) (gy)) :: pts_l))))) (PreH13 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx) (gy)) :: pts_l))))) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx) (gy)) :: pts_l))))) ,
  ((( &( "coords" ) )) # Ptr |-> (pts_pre))
  ** ((( &( "pts" ) )) # Ptr |-> (pts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((&(( &( "gp" ) ) ->ₛ "x")) # Int |-> (gx))
  ** ((&(( &( "gp" ) ) ->ₛ "y")) # Int |-> (gy))
  ** (intArray.full pts_pre (2 * n_pre) flat)
|--
  “ ((-10000) <= gx) ”

noncomputable def sort_partial_solve_wit_1_pure_split_goal_4 : Prop :=
  forall (gy : Int) (gx : Int) (pts_l : (List point)) (flat : (List Int)) (pts_pre : Int) (n_pre : Int) (PreH1 : (gy <= INT_MAX)) (PreH2 : (gx <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (gy >= INT_MIN)) (PreH5 : (gx >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : ((0 : Int) <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l)) = n_pre)) (PreH10 : (FlatPoints flat pts_l)) (PreH11 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx) (gy)) :: pts_l))))) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx) (gy)) :: pts_l))))) (PreH13 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx) (gy)) :: pts_l))))) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx) (gy)) :: pts_l))))) ,
  ((( &( "coords" ) )) # Ptr |-> (pts_pre))
  ** ((( &( "pts" ) )) # Ptr |-> (pts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((&(( &( "gp" ) ) ->ₛ "x")) # Int |-> (gx))
  ** ((&(( &( "gp" ) ) ->ₛ "y")) # Int |-> (gy))
  ** (intArray.full pts_pre (2 * n_pre) flat)
|--
  “ (gx <= 10000) ”

noncomputable def sort_partial_solve_wit_1_pure_split_goal_5 : Prop :=
  forall (gy : Int) (gx : Int) (pts_l : (List point)) (flat : (List Int)) (pts_pre : Int) (n_pre : Int) (PreH1 : (gy <= INT_MAX)) (PreH2 : (gx <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (gy >= INT_MIN)) (PreH5 : (gx >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : ((0 : Int) <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l)) = n_pre)) (PreH10 : (FlatPoints flat pts_l)) (PreH11 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx) (gy)) :: pts_l))))) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx) (gy)) :: pts_l))))) (PreH13 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx) (gy)) :: pts_l))))) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx) (gy)) :: pts_l))))) ,
  ((( &( "coords" ) )) # Ptr |-> (pts_pre))
  ** ((( &( "pts" ) )) # Ptr |-> (pts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((&(( &( "gp" ) ) ->ₛ "x")) # Int |-> (gx))
  ** ((&(( &( "gp" ) ) ->ₛ "y")) # Int |-> (gy))
  ** (intArray.full pts_pre (2 * n_pre) flat)
|--
  “ ((-10000) <= gy) ”

noncomputable def sort_partial_solve_wit_1_pure_split_goal_6 : Prop :=
  forall (gy : Int) (gx : Int) (pts_l : (List point)) (flat : (List Int)) (pts_pre : Int) (n_pre : Int) (PreH1 : (gy <= INT_MAX)) (PreH2 : (gx <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (gy >= INT_MIN)) (PreH5 : (gx >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : ((0 : Int) <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l)) = n_pre)) (PreH10 : (FlatPoints flat pts_l)) (PreH11 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx) (gy)) :: pts_l))))) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx) (gy)) :: pts_l))))) (PreH13 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx) (gy)) :: pts_l))))) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx) (gy)) :: pts_l))))) ,
  ((( &( "coords" ) )) # Ptr |-> (pts_pre))
  ** ((( &( "pts" ) )) # Ptr |-> (pts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((&(( &( "gp" ) ) ->ₛ "x")) # Int |-> (gx))
  ** ((&(( &( "gp" ) ) ->ₛ "y")) # Int |-> (gy))
  ** (intArray.full pts_pre (2 * n_pre) flat)
|--
  “ (gy <= 10000) ”

noncomputable def sort_partial_solve_wit_1_pure_split_goal_7 : Prop :=
  forall (gy : Int) (gx : Int) (pts_l : (List point)) (flat : (List Int)) (pts_pre : Int) (n_pre : Int) (PreH1 : (gy <= INT_MAX)) (PreH2 : (gx <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (gy >= INT_MIN)) (PreH5 : (gx >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : ((0 : Int) <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l)) = n_pre)) (PreH10 : (FlatPoints flat pts_l)) (PreH11 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx) (gy)) :: pts_l))))) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx) (gy)) :: pts_l))))) (PreH13 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx) (gy)) :: pts_l))))) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx) (gy)) :: pts_l))))) ,
  ((( &( "coords" ) )) # Ptr |-> (pts_pre))
  ** ((( &( "pts" ) )) # Ptr |-> (pts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((&(( &( "gp" ) ) ->ₛ "x")) # Int |-> (gx))
  ** ((&(( &( "gp" ) ) ->ₛ "y")) # Int |-> (gy))
  ** (intArray.full pts_pre (2 * n_pre) flat)
|--
  “ (Forall ((LE.le (α := Int)) ((-10000))) flat) ”

noncomputable def sort_partial_solve_wit_1_pure_split_goal_8 : Prop :=
  forall (gy : Int) (gx : Int) (pts_l : (List point)) (flat : (List Int)) (pts_pre : Int) (n_pre : Int) (PreH1 : (gy <= INT_MAX)) (PreH2 : (gx <= INT_MAX)) (PreH3 : (n_pre <= INT_MAX)) (PreH4 : (gy >= INT_MIN)) (PreH5 : (gx >= INT_MIN)) (PreH6 : (n_pre >= INT_MIN)) (PreH7 : ((0 : Int) <= n_pre)) (PreH8 : (n_pre <= 50000)) (PreH9 : ((Zlength (pts_l)) = n_pre)) (PreH10 : (FlatPoints flat pts_l)) (PreH11 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx) (gy)) :: pts_l))))) (PreH12 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx) (gy)) :: pts_l))))) (PreH13 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx) (gy)) :: pts_l))))) (PreH14 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx) (gy)) :: pts_l))))) ,
  ((( &( "coords" ) )) # Ptr |-> (pts_pre))
  ** ((( &( "pts" ) )) # Ptr |-> (pts_pre))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((&(( &( "gp" ) ) ->ₛ "x")) # Int |-> (gx))
  ** ((&(( &( "gp" ) ) ->ₛ "y")) # Int |-> (gy))
  ** (intArray.full pts_pre (2 * n_pre) flat)
|--
  “ (Forall ((GE.ge (α := Int)) (10000)) flat) ”

noncomputable def sort_partial_solve_wit_1_aux : Prop :=
  forall (gy : Int) (gx : Int) (pts_l : (List point)) (flat : (List Int)) (pts_pre : Int) (n_pre : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : (n_pre <= 50000)) (PreH3 : ((Zlength (pts_l)) = n_pre)) (PreH4 : (FlatPoints flat pts_l)) (PreH5 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx) (gy)) :: pts_l))))) (PreH6 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx) (gy)) :: pts_l))))) (PreH7 : (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx) (gy)) :: pts_l))))) (PreH8 : (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx) (gy)) :: pts_l))))) ,
  ((&(( &( "gp" ) ) ->ₛ "x")) # Int |-> (gx))
  ** ((&(( &( "gp" ) ) ->ₛ "y")) # Int |-> (gy))
  ** (intArray.full pts_pre (2 * n_pre) flat)
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((-1) <= (n_pre - 1)) ” &&
  “ ((n_pre - 1) < n_pre) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) flat) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) flat) ” &&
  “ (gy <= 10000) ” &&
  “ ((-10000) <= gy) ” &&
  “ (gx <= 10000) ” &&
  “ ((-10000) <= gx) ” &&
  “ ((Zlength (flat)) = (2 * n_pre)) ” &&
  “ (PointFlatModel flat) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= 50000) ” &&
  “ ((Zlength (pts_l)) = n_pre) ” &&
  “ (FlatPoints flat pts_l) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_x) (((mk_point (gx) (gy)) :: pts_l)))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_x) (((mk_point (gx) (gy)) :: pts_l)))) ” &&
  “ (Forall ((LE.le (α := Int)) ((-10000))) (List.map (point_y) (((mk_point (gx) (gy)) :: pts_l)))) ” &&
  “ (Forall ((GE.ge (α := Int)) (10000)) (List.map (point_y) (((mk_point (gx) (gy)) :: pts_l)))) ”
  &&  (intArray.full pts_pre (2 * n_pre) flat)
  ** ((&(( &( "gp" ) ) ->ₛ "x")) # Int |-> (gx))
  ** ((&(( &( "gp" ) ) ->ₛ "y")) # Int |-> (gy))

noncomputable def sort_partial_solve_wit_1 : Prop := sort_partial_solve_wit_1_pure -> sort_partial_solve_wit_1_aux


structure VC_Correct : Type where
  proof_of_cmp_polar_values_safety_wit_1 : cmp_polar_values_safety_wit_1
  proof_of_cmp_polar_values_safety_wit_2 : cmp_polar_values_safety_wit_2
  proof_of_cmp_polar_values_safety_wit_3 : cmp_polar_values_safety_wit_3
  proof_of_cmp_polar_values_safety_wit_4 : cmp_polar_values_safety_wit_4
  proof_of_cmp_polar_values_safety_wit_5 : cmp_polar_values_safety_wit_5
  proof_of_cmp_polar_values_safety_wit_6 : cmp_polar_values_safety_wit_6
  proof_of_cmp_polar_values_safety_wit_7 : cmp_polar_values_safety_wit_7
  proof_of_cmp_polar_values_safety_wit_8 : cmp_polar_values_safety_wit_8
  proof_of_cmp_polar_values_safety_wit_9 : cmp_polar_values_safety_wit_9
  proof_of_cmp_polar_values_safety_wit_10 : cmp_polar_values_safety_wit_10
  proof_of_cmp_polar_values_safety_wit_11 : cmp_polar_values_safety_wit_11
  proof_of_cmp_polar_values_safety_wit_12 : cmp_polar_values_safety_wit_12
  proof_of_cmp_polar_values_safety_wit_13 : cmp_polar_values_safety_wit_13
  proof_of_cmp_polar_values_safety_wit_14 : cmp_polar_values_safety_wit_14
  proof_of_cmp_polar_values_safety_wit_15 : cmp_polar_values_safety_wit_15
  proof_of_cmp_polar_values_safety_wit_16 : cmp_polar_values_safety_wit_16
  proof_of_cmp_polar_values_safety_wit_17 : cmp_polar_values_safety_wit_17
  proof_of_cmp_polar_values_safety_wit_18 : cmp_polar_values_safety_wit_18
  proof_of_cmp_polar_values_safety_wit_19 : cmp_polar_values_safety_wit_19
  proof_of_cmp_polar_values_safety_wit_20 : cmp_polar_values_safety_wit_20
  proof_of_cmp_polar_values_safety_wit_21 : cmp_polar_values_safety_wit_21
  proof_of_cmp_polar_values_safety_wit_22 : cmp_polar_values_safety_wit_22
  proof_of_cmp_polar_values_safety_wit_23 : cmp_polar_values_safety_wit_23
  proof_of_cmp_polar_values_safety_wit_24 : cmp_polar_values_safety_wit_24
  proof_of_cmp_polar_values_safety_wit_25 : cmp_polar_values_safety_wit_25
  proof_of_cmp_polar_values_safety_wit_26 : cmp_polar_values_safety_wit_26
  proof_of_cmp_polar_values_safety_wit_27 : cmp_polar_values_safety_wit_27
  proof_of_cmp_polar_values_safety_wit_28 : cmp_polar_values_safety_wit_28
  proof_of_cmp_polar_values_safety_wit_29 : cmp_polar_values_safety_wit_29
  proof_of_cmp_polar_values_safety_wit_30 : cmp_polar_values_safety_wit_30
  proof_of_cmp_polar_values_safety_wit_31 : cmp_polar_values_safety_wit_31
  proof_of_cmp_polar_values_safety_wit_32 : cmp_polar_values_safety_wit_32
  proof_of_cmp_polar_values_safety_wit_33 : cmp_polar_values_safety_wit_33
  proof_of_cmp_polar_values_safety_wit_34 : cmp_polar_values_safety_wit_34
  proof_of_cmp_polar_values_safety_wit_35 : cmp_polar_values_safety_wit_35
  proof_of_cmp_polar_values_safety_wit_36 : cmp_polar_values_safety_wit_36
  proof_of_cmp_polar_values_safety_wit_37 : cmp_polar_values_safety_wit_37
  proof_of_cmp_polar_values_safety_wit_38 : cmp_polar_values_safety_wit_38
  proof_of_cmp_polar_values_safety_wit_39 : cmp_polar_values_safety_wit_39
  proof_of_cmp_polar_values_safety_wit_40 : cmp_polar_values_safety_wit_40
  proof_of_cmp_polar_values_safety_wit_41 : cmp_polar_values_safety_wit_41
  proof_of_cmp_polar_values_safety_wit_42 : cmp_polar_values_safety_wit_42
  proof_of_cmp_polar_values_safety_wit_43 : cmp_polar_values_safety_wit_43
  proof_of_cmp_polar_values_safety_wit_44 : cmp_polar_values_safety_wit_44
  proof_of_cmp_polar_values_safety_wit_45 : cmp_polar_values_safety_wit_45
  proof_of_cmp_polar_values_safety_wit_46 : cmp_polar_values_safety_wit_46
  proof_of_cmp_polar_values_safety_wit_47 : cmp_polar_values_safety_wit_47
  proof_of_cmp_polar_values_safety_wit_48 : cmp_polar_values_safety_wit_48
  proof_of_cmp_polar_values_safety_wit_49 : cmp_polar_values_safety_wit_49
  proof_of_cmp_polar_values_safety_wit_50 : cmp_polar_values_safety_wit_50
  proof_of_cmp_polar_values_safety_wit_51 : cmp_polar_values_safety_wit_51
  proof_of_cmp_polar_values_safety_wit_52 : cmp_polar_values_safety_wit_52
  proof_of_cmp_polar_values_safety_wit_53 : cmp_polar_values_safety_wit_53
  proof_of_cmp_polar_values_safety_wit_54 : cmp_polar_values_safety_wit_54
  proof_of_cmp_polar_values_safety_wit_55 : cmp_polar_values_safety_wit_55
  proof_of_cmp_polar_values_safety_wit_56 : cmp_polar_values_safety_wit_56
  proof_of_cmp_polar_values_safety_wit_57 : cmp_polar_values_safety_wit_57
  proof_of_cmp_polar_values_safety_wit_58 : cmp_polar_values_safety_wit_58
  proof_of_cmp_polar_values_safety_wit_59 : cmp_polar_values_safety_wit_59
  proof_of_cmp_polar_values_safety_wit_60 : cmp_polar_values_safety_wit_60
  proof_of_cmp_polar_values_safety_wit_61 : cmp_polar_values_safety_wit_61
  proof_of_cmp_polar_values_safety_wit_62 : cmp_polar_values_safety_wit_62
  proof_of_cmp_polar_values_safety_wit_63 : cmp_polar_values_safety_wit_63
  proof_of_cmp_polar_values_safety_wit_64 : cmp_polar_values_safety_wit_64
  proof_of_cmp_polar_values_safety_wit_65 : cmp_polar_values_safety_wit_65
  proof_of_cmp_polar_values_safety_wit_66 : cmp_polar_values_safety_wit_66
  proof_of_cmp_polar_values_safety_wit_67 : cmp_polar_values_safety_wit_67
  proof_of_cmp_polar_values_safety_wit_68 : cmp_polar_values_safety_wit_68
  proof_of_cmp_polar_values_safety_wit_69 : cmp_polar_values_safety_wit_69
  proof_of_cmp_polar_values_safety_wit_70 : cmp_polar_values_safety_wit_70
  proof_of_cmp_polar_values_safety_wit_71 : cmp_polar_values_safety_wit_71
  proof_of_cmp_polar_values_safety_wit_72 : cmp_polar_values_safety_wit_72
  proof_of_cmp_polar_values_safety_wit_73 : cmp_polar_values_safety_wit_73
  proof_of_cmp_polar_values_safety_wit_74 : cmp_polar_values_safety_wit_74
  proof_of_cmp_polar_values_safety_wit_75 : cmp_polar_values_safety_wit_75
  proof_of_cmp_polar_values_safety_wit_76 : cmp_polar_values_safety_wit_76
  proof_of_cmp_polar_values_safety_wit_77 : cmp_polar_values_safety_wit_77
  proof_of_cmp_polar_values_safety_wit_78 : cmp_polar_values_safety_wit_78
  proof_of_cmp_polar_values_safety_wit_79 : cmp_polar_values_safety_wit_79
  proof_of_cmp_polar_values_safety_wit_80 : cmp_polar_values_safety_wit_80
  proof_of_cmp_polar_values_safety_wit_81 : cmp_polar_values_safety_wit_81
  proof_of_cmp_polar_values_safety_wit_82 : cmp_polar_values_safety_wit_82
  proof_of_cmp_polar_values_safety_wit_83 : cmp_polar_values_safety_wit_83
  proof_of_cmp_polar_values_safety_wit_84 : cmp_polar_values_safety_wit_84
  proof_of_cmp_polar_values_safety_wit_85 : cmp_polar_values_safety_wit_85
  proof_of_cmp_polar_values_safety_wit_86 : cmp_polar_values_safety_wit_86
  proof_of_cmp_polar_values_safety_wit_87 : cmp_polar_values_safety_wit_87
  proof_of_cmp_polar_values_safety_wit_88 : cmp_polar_values_safety_wit_88
  proof_of_cmp_polar_values_safety_wit_89 : cmp_polar_values_safety_wit_89
  proof_of_cmp_polar_values_safety_wit_90 : cmp_polar_values_safety_wit_90
  proof_of_cmp_polar_values_safety_wit_91 : cmp_polar_values_safety_wit_91
  proof_of_cmp_polar_values_safety_wit_92 : cmp_polar_values_safety_wit_92
  proof_of_cmp_polar_values_safety_wit_93 : cmp_polar_values_safety_wit_93
  proof_of_cmp_polar_values_safety_wit_94 : cmp_polar_values_safety_wit_94
  proof_of_cmp_polar_values_safety_wit_95 : cmp_polar_values_safety_wit_95
  proof_of_cmp_polar_values_safety_wit_96 : cmp_polar_values_safety_wit_96
  proof_of_cmp_polar_values_safety_wit_97 : cmp_polar_values_safety_wit_97
  proof_of_cmp_polar_values_safety_wit_98 : cmp_polar_values_safety_wit_98
  proof_of_cmp_polar_values_safety_wit_99 : cmp_polar_values_safety_wit_99
  proof_of_cmp_polar_values_safety_wit_100 : cmp_polar_values_safety_wit_100
  proof_of_cmp_polar_values_safety_wit_101 : cmp_polar_values_safety_wit_101
  proof_of_cmp_polar_values_safety_wit_102 : cmp_polar_values_safety_wit_102
  proof_of_cmp_polar_values_safety_wit_103 : cmp_polar_values_safety_wit_103
  proof_of_cmp_polar_values_safety_wit_104 : cmp_polar_values_safety_wit_104
  proof_of_cmp_polar_values_safety_wit_105 : cmp_polar_values_safety_wit_105
  proof_of_cmp_polar_values_safety_wit_106 : cmp_polar_values_safety_wit_106
  proof_of_cmp_polar_values_safety_wit_107 : cmp_polar_values_safety_wit_107
  proof_of_cmp_polar_values_safety_wit_108 : cmp_polar_values_safety_wit_108
  proof_of_cmp_polar_values_safety_wit_109 : cmp_polar_values_safety_wit_109
  proof_of_cmp_polar_values_safety_wit_110 : cmp_polar_values_safety_wit_110
  proof_of_cmp_polar_values_safety_wit_111 : cmp_polar_values_safety_wit_111
  proof_of_cmp_polar_values_safety_wit_112 : cmp_polar_values_safety_wit_112
  proof_of_cmp_polar_values_safety_wit_113 : cmp_polar_values_safety_wit_113
  proof_of_cmp_polar_values_safety_wit_114 : cmp_polar_values_safety_wit_114
  proof_of_cmp_polar_values_safety_wit_115 : cmp_polar_values_safety_wit_115
  proof_of_cmp_polar_values_safety_wit_116 : cmp_polar_values_safety_wit_116
  proof_of_cmp_polar_values_safety_wit_117 : cmp_polar_values_safety_wit_117
  proof_of_cmp_polar_values_safety_wit_118 : cmp_polar_values_safety_wit_118
  proof_of_cmp_polar_values_safety_wit_119 : cmp_polar_values_safety_wit_119
  proof_of_cmp_polar_values_safety_wit_120 : cmp_polar_values_safety_wit_120
  proof_of_cmp_polar_values_safety_wit_121 : cmp_polar_values_safety_wit_121
  proof_of_cmp_polar_values_safety_wit_122 : cmp_polar_values_safety_wit_122
  proof_of_cmp_polar_values_safety_wit_123 : cmp_polar_values_safety_wit_123
  proof_of_cmp_polar_values_safety_wit_124 : cmp_polar_values_safety_wit_124
  proof_of_cmp_polar_values_safety_wit_125 : cmp_polar_values_safety_wit_125
  proof_of_cmp_polar_values_safety_wit_126 : cmp_polar_values_safety_wit_126
  proof_of_cmp_polar_values_safety_wit_127 : cmp_polar_values_safety_wit_127
  proof_of_cmp_polar_values_safety_wit_128 : cmp_polar_values_safety_wit_128
  proof_of_cmp_polar_values_safety_wit_129 : cmp_polar_values_safety_wit_129
  proof_of_cmp_polar_values_safety_wit_130 : cmp_polar_values_safety_wit_130
  proof_of_cmp_polar_values_safety_wit_131 : cmp_polar_values_safety_wit_131
  proof_of_cmp_polar_values_safety_wit_132 : cmp_polar_values_safety_wit_132
  proof_of_cmp_polar_values_safety_wit_133 : cmp_polar_values_safety_wit_133
  proof_of_cmp_polar_values_safety_wit_134 : cmp_polar_values_safety_wit_134
  proof_of_cmp_polar_values_safety_wit_135 : cmp_polar_values_safety_wit_135
  proof_of_cmp_polar_values_safety_wit_136 : cmp_polar_values_safety_wit_136
  proof_of_cmp_polar_values_safety_wit_137 : cmp_polar_values_safety_wit_137
  proof_of_cmp_polar_values_safety_wit_138 : cmp_polar_values_safety_wit_138
  proof_of_cmp_polar_values_safety_wit_139 : cmp_polar_values_safety_wit_139
  proof_of_cmp_polar_values_safety_wit_140 : cmp_polar_values_safety_wit_140
  proof_of_cmp_polar_values_safety_wit_141 : cmp_polar_values_safety_wit_141
  proof_of_cmp_polar_values_safety_wit_142 : cmp_polar_values_safety_wit_142
  proof_of_cmp_polar_values_safety_wit_143 : cmp_polar_values_safety_wit_143
  proof_of_cmp_polar_values_safety_wit_144 : cmp_polar_values_safety_wit_144
  proof_of_cmp_polar_values_safety_wit_145 : cmp_polar_values_safety_wit_145
  proof_of_cmp_polar_values_safety_wit_146 : cmp_polar_values_safety_wit_146
  proof_of_cmp_polar_values_safety_wit_147 : cmp_polar_values_safety_wit_147
  proof_of_swap_points_safety_wit_1 : swap_points_safety_wit_1
  proof_of_swap_points_safety_wit_2 : swap_points_safety_wit_2
  proof_of_swap_points_safety_wit_3 : swap_points_safety_wit_3
  proof_of_swap_points_safety_wit_4 : swap_points_safety_wit_4
  proof_of_swap_points_safety_wit_5 : swap_points_safety_wit_5
  proof_of_swap_points_safety_wit_6 : swap_points_safety_wit_6
  proof_of_swap_points_safety_wit_7 : swap_points_safety_wit_7
  proof_of_swap_points_safety_wit_8 : swap_points_safety_wit_8
  proof_of_swap_points_safety_wit_9 : swap_points_safety_wit_9
  proof_of_swap_points_safety_wit_10 : swap_points_safety_wit_10
  proof_of_swap_points_safety_wit_11 : swap_points_safety_wit_11
  proof_of_swap_points_safety_wit_12 : swap_points_safety_wit_12
  proof_of_swap_points_safety_wit_13 : swap_points_safety_wit_13
  proof_of_swap_points_safety_wit_14 : swap_points_safety_wit_14
  proof_of_swap_points_safety_wit_15 : swap_points_safety_wit_15
  proof_of_swap_points_safety_wit_16 : swap_points_safety_wit_16
  proof_of_swap_points_safety_wit_17 : swap_points_safety_wit_17
  proof_of_swap_points_safety_wit_18 : swap_points_safety_wit_18
  proof_of_swap_points_safety_wit_19 : swap_points_safety_wit_19
  proof_of_swap_points_safety_wit_20 : swap_points_safety_wit_20
  proof_of_swap_points_safety_wit_21 : swap_points_safety_wit_21
  proof_of_swap_points_safety_wit_22 : swap_points_safety_wit_22
  proof_of_swap_points_safety_wit_23 : swap_points_safety_wit_23
  proof_of_swap_points_safety_wit_24 : swap_points_safety_wit_24
  proof_of_swap_points_partial_solve_wit_1 : swap_points_partial_solve_wit_1
  proof_of_swap_points_partial_solve_wit_2 : swap_points_partial_solve_wit_2
  proof_of_swap_points_partial_solve_wit_3 : swap_points_partial_solve_wit_3
  proof_of_swap_points_partial_solve_wit_4 : swap_points_partial_solve_wit_4
  proof_of_swap_points_partial_solve_wit_5 : swap_points_partial_solve_wit_5
  proof_of_swap_points_partial_solve_wit_6 : swap_points_partial_solve_wit_6
  proof_of_swap_points_partial_solve_wit_7 : swap_points_partial_solve_wit_7
  proof_of_swap_points_partial_solve_wit_8 : swap_points_partial_solve_wit_8
  proof_of_partition_points_safety_wit_1 : partition_points_safety_wit_1
  proof_of_partition_points_safety_wit_2 : partition_points_safety_wit_2
  proof_of_partition_points_safety_wit_3 : partition_points_safety_wit_3
  proof_of_partition_points_safety_wit_4 : partition_points_safety_wit_4
  proof_of_partition_points_safety_wit_5 : partition_points_safety_wit_5
  proof_of_partition_points_safety_wit_6 : partition_points_safety_wit_6
  proof_of_partition_points_safety_wit_7 : partition_points_safety_wit_7
  proof_of_partition_points_safety_wit_8 : partition_points_safety_wit_8
  proof_of_partition_points_safety_wit_9 : partition_points_safety_wit_9
  proof_of_partition_points_safety_wit_10 : partition_points_safety_wit_10
  proof_of_partition_points_safety_wit_11 : partition_points_safety_wit_11
  proof_of_partition_points_safety_wit_12 : partition_points_safety_wit_12
  proof_of_partition_points_safety_wit_13 : partition_points_safety_wit_13
  proof_of_partition_points_safety_wit_14 : partition_points_safety_wit_14
  proof_of_partition_points_safety_wit_15 : partition_points_safety_wit_15
  proof_of_partition_points_safety_wit_16 : partition_points_safety_wit_16
  proof_of_partition_points_safety_wit_17 : partition_points_safety_wit_17
  proof_of_partition_points_safety_wit_18 : partition_points_safety_wit_18
  proof_of_partition_points_safety_wit_19 : partition_points_safety_wit_19
  proof_of_partition_points_safety_wit_20 : partition_points_safety_wit_20
  proof_of_partition_points_safety_wit_21 : partition_points_safety_wit_21
  proof_of_partition_points_safety_wit_22 : partition_points_safety_wit_22
  proof_of_partition_points_partial_solve_wit_1 : partition_points_partial_solve_wit_1
  proof_of_partition_points_partial_solve_wit_2 : partition_points_partial_solve_wit_2
  proof_of_partition_points_partial_solve_wit_3 : partition_points_partial_solve_wit_3
  proof_of_partition_points_partial_solve_wit_4 : partition_points_partial_solve_wit_4
  proof_of_partition_points_partial_solve_wit_5 : partition_points_partial_solve_wit_5
  proof_of_partition_points_partial_solve_wit_6_pure : partition_points_partial_solve_wit_6_pure
  proof_of_partition_points_partial_solve_wit_6 : partition_points_partial_solve_wit_6
  proof_of_partition_points_partial_solve_wit_7_pure : partition_points_partial_solve_wit_7_pure
  proof_of_partition_points_partial_solve_wit_7 : partition_points_partial_solve_wit_7
  proof_of_quicksort_points_range_safety_wit_1 : quicksort_points_range_safety_wit_1
  proof_of_quicksort_points_range_safety_wit_2 : quicksort_points_range_safety_wit_2
  proof_of_quicksort_points_range_safety_wit_3 : quicksort_points_range_safety_wit_3
  proof_of_quicksort_points_range_safety_wit_4 : quicksort_points_range_safety_wit_4
  proof_of_quicksort_points_range_safety_wit_5 : quicksort_points_range_safety_wit_5
  proof_of_quicksort_points_range_safety_wit_6 : quicksort_points_range_safety_wit_6
  proof_of_quicksort_points_range_safety_wit_7 : quicksort_points_range_safety_wit_7
  proof_of_quicksort_points_range_partial_solve_wit_1_pure : quicksort_points_range_partial_solve_wit_1_pure
  proof_of_quicksort_points_range_partial_solve_wit_1 : quicksort_points_range_partial_solve_wit_1
  proof_of_quicksort_points_range_partial_solve_wit_2 : quicksort_points_range_partial_solve_wit_2
  proof_of_quicksort_points_range_partial_solve_wit_3 : quicksort_points_range_partial_solve_wit_3
  proof_of_quicksort_points_range_partial_solve_wit_4 : quicksort_points_range_partial_solve_wit_4
  proof_of_sort_safety_wit_1 : sort_safety_wit_1
  proof_of_sort_safety_wit_2 : sort_safety_wit_2
  proof_of_sort_safety_wit_3 : sort_safety_wit_3
  proof_of_sort_partial_solve_wit_1 : sort_partial_solve_wit_1
  proof_of_cmp_polar_values_return_wit_1 : cmp_polar_values_return_wit_1
  proof_of_cmp_polar_values_return_wit_2 : cmp_polar_values_return_wit_2
  proof_of_cmp_polar_values_return_wit_3 : cmp_polar_values_return_wit_3
  proof_of_cmp_polar_values_return_wit_4 : cmp_polar_values_return_wit_4
  proof_of_cmp_polar_values_return_wit_5 : cmp_polar_values_return_wit_5
  proof_of_cmp_polar_values_return_wit_6 : cmp_polar_values_return_wit_6
  proof_of_cmp_polar_values_return_wit_7 : cmp_polar_values_return_wit_7
  proof_of_cmp_polar_values_return_wit_8 : cmp_polar_values_return_wit_8
  proof_of_cmp_polar_values_return_wit_9 : cmp_polar_values_return_wit_9
  proof_of_cmp_polar_values_return_wit_10 : cmp_polar_values_return_wit_10
  proof_of_cmp_polar_values_return_wit_11 : cmp_polar_values_return_wit_11
  proof_of_cmp_polar_values_return_wit_12 : cmp_polar_values_return_wit_12
  proof_of_cmp_polar_values_return_wit_13 : cmp_polar_values_return_wit_13
  proof_of_cmp_polar_values_return_wit_14 : cmp_polar_values_return_wit_14
  proof_of_cmp_polar_values_return_wit_15 : cmp_polar_values_return_wit_15
  proof_of_cmp_polar_values_return_wit_16 : cmp_polar_values_return_wit_16
  proof_of_cmp_polar_values_return_wit_17 : cmp_polar_values_return_wit_17
  proof_of_cmp_polar_values_return_wit_18 : cmp_polar_values_return_wit_18
  proof_of_cmp_polar_values_return_wit_19 : cmp_polar_values_return_wit_19
  proof_of_cmp_polar_values_return_wit_20 : cmp_polar_values_return_wit_20
  proof_of_cmp_polar_values_return_wit_21 : cmp_polar_values_return_wit_21
  proof_of_cmp_polar_values_return_wit_22 : cmp_polar_values_return_wit_22
  proof_of_cmp_polar_values_return_wit_23 : cmp_polar_values_return_wit_23
  proof_of_cmp_polar_values_return_wit_24 : cmp_polar_values_return_wit_24
  proof_of_cmp_polar_values_return_wit_25 : cmp_polar_values_return_wit_25
  proof_of_cmp_polar_values_return_wit_26 : cmp_polar_values_return_wit_26
  proof_of_cmp_polar_values_return_wit_27 : cmp_polar_values_return_wit_27
  proof_of_cmp_polar_values_return_wit_28 : cmp_polar_values_return_wit_28
  proof_of_cmp_polar_values_return_wit_29 : cmp_polar_values_return_wit_29
  proof_of_cmp_polar_values_return_wit_30 : cmp_polar_values_return_wit_30
  proof_of_cmp_polar_values_return_wit_31 : cmp_polar_values_return_wit_31
  proof_of_cmp_polar_values_return_wit_32 : cmp_polar_values_return_wit_32
  proof_of_cmp_polar_values_return_wit_33 : cmp_polar_values_return_wit_33
  proof_of_cmp_polar_values_return_wit_34 : cmp_polar_values_return_wit_34
  proof_of_cmp_polar_values_return_wit_35 : cmp_polar_values_return_wit_35
  proof_of_cmp_polar_values_return_wit_36 : cmp_polar_values_return_wit_36
  proof_of_cmp_polar_values_return_wit_37 : cmp_polar_values_return_wit_37
  proof_of_cmp_polar_values_return_wit_38 : cmp_polar_values_return_wit_38
  proof_of_cmp_polar_values_return_wit_39 : cmp_polar_values_return_wit_39
  proof_of_cmp_polar_values_return_wit_40 : cmp_polar_values_return_wit_40
  proof_of_cmp_polar_values_return_wit_41 : cmp_polar_values_return_wit_41
  proof_of_cmp_polar_values_return_wit_42 : cmp_polar_values_return_wit_42
  proof_of_cmp_polar_values_return_wit_43 : cmp_polar_values_return_wit_43
  proof_of_cmp_polar_values_return_wit_44 : cmp_polar_values_return_wit_44
  proof_of_cmp_polar_values_return_wit_45 : cmp_polar_values_return_wit_45
  proof_of_cmp_polar_values_return_wit_46 : cmp_polar_values_return_wit_46
  proof_of_cmp_polar_values_return_wit_47 : cmp_polar_values_return_wit_47
  proof_of_cmp_polar_values_return_wit_48 : cmp_polar_values_return_wit_48
  proof_of_cmp_polar_values_return_wit_49 : cmp_polar_values_return_wit_49
  proof_of_cmp_polar_values_return_wit_50 : cmp_polar_values_return_wit_50
  proof_of_swap_points_return_wit_1 : swap_points_return_wit_1
  proof_of_partition_points_entail_wit_1 : partition_points_entail_wit_1
  proof_of_partition_points_entail_wit_2_1 : partition_points_entail_wit_2_1
  proof_of_partition_points_entail_wit_2_2 : partition_points_entail_wit_2_2
  proof_of_partition_points_return_wit_1 : partition_points_return_wit_1
  proof_of_partition_points_partial_solve_wit_5_pure : partition_points_partial_solve_wit_5_pure
  proof_of_quicksort_points_range_entail_wit_1 : quicksort_points_range_entail_wit_1
  proof_of_quicksort_points_range_return_wit_1 : quicksort_points_range_return_wit_1
  proof_of_quicksort_points_range_return_wit_2 : quicksort_points_range_return_wit_2
  proof_of_quicksort_points_range_return_wit_3 : quicksort_points_range_return_wit_3
  proof_of_quicksort_points_range_return_wit_4 : quicksort_points_range_return_wit_4
  proof_of_quicksort_points_range_partial_solve_wit_2_pure : quicksort_points_range_partial_solve_wit_2_pure
  proof_of_quicksort_points_range_partial_solve_wit_3_pure : quicksort_points_range_partial_solve_wit_3_pure
  proof_of_quicksort_points_range_partial_solve_wit_4_pure : quicksort_points_range_partial_solve_wit_4_pure
  proof_of_sort_return_wit_1 : sort_return_wit_1
  proof_of_sort_partial_solve_wit_1_pure : sort_partial_solve_wit_1_pure

end SimpleC.EE.LLM_bench.Algorithms.sort_point.sort_point_goal
