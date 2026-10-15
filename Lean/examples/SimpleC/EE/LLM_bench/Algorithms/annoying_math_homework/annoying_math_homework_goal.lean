import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Algorithms.annoying_math_homework.annoying_math_homework_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.annoying_math_homework.annoying_math_homework_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance annoying_math_homework_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def digits_sum_init_safety_wit_1 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) ,
  ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** (intArray.undef_full dp_pre 200)
  ** (intArray.undef_full power_pre 20)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def digits_sum_init_safety_wit_2 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) ,
  ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** (intArray.undef_full dp_pre 200)
  ** (intArray.undef_full power_pre 20)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def digits_sum_init_safety_wit_3 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) ,
  ((( &( "i" ) )) # Int |->_)
  ** (((power_pre + ((0 : Int) * sizeof(INT)))) # Int |-> (1))
  ** (intArray.undef_seg power_pre 1 20)
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** (intArray.undef_full dp_pre 200)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def digits_sum_init_safety_wit_4 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (i : Int) (PreH1 : (1 <= i)) (PreH2 : (i <= 20)) (PreH3 : ((Zlength (power_l)) = i)) (PreH4 : (PowerPrefix power_l i)) ,
  ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_full dp_pre 200)
  ** (intArray.seg power_pre (0 : Int) i power_l)
  ** (intArray.undef_seg power_pre i 20)
|--
  “ (20 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 20) ”

noncomputable def digits_sum_init_safety_wit_5 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (i : Int) (PreH1 : (i < 20)) (PreH2 : (1 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (power_l)) = i)) (PreH5 : (PowerPrefix power_l i)) ,
  ((( &( "bef" ) )) # Int64 |->_)
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_full dp_pre 200)
  ** (intArray.seg power_pre (0 : Int) i power_l)
  ** (intArray.undef_seg power_pre i 20)
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def digits_sum_init_safety_wit_6 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (i : Int) (PreH1 : (i < 20)) (PreH2 : (1 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (power_l)) = i)) (PreH5 : (PowerPrefix power_l i)) ,
  ((( &( "bef" ) )) # Int64 |->_)
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_full dp_pre 200)
  ** (intArray.seg power_pre (0 : Int) i power_l)
  ** (intArray.undef_seg power_pre i 20)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def digits_sum_init_safety_wit_7 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (i : Int) (PreH1 : (i < 20)) (PreH2 : (1 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (power_l)) = i)) (PreH5 : (PowerPrefix power_l i)) ,
  (intArray.seg power_pre (0 : Int) i power_l)
  ** ((( &( "bef" ) )) # Int64 |-> ((Znth ((i - 1) - (0 : Int)) power_l (0 : Int))))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_full dp_pre 200)
  ** (intArray.undef_seg power_pre i 20)
|--
  “ ((((Znth ((i - 1) - (0 : Int)) power_l (0 : Int)) * 10) ≠ (-9223372036854775808)) ∨ (1000000007 ≠ (-1))) ” &&
  “ (1000000007 ≠ (0 : Int)) ”

noncomputable def digits_sum_init_safety_wit_8 : Prop :=
  (
forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (i : Int) (PreH1 : (i < 20)) (PreH2 : (1 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (power_l)) = i)) (PreH5 : (PowerPrefix power_l i)) ,
  (intArray.seg power_pre (0 : Int) i power_l)
  ** ((( &( "bef" ) )) # Int64 |-> ((Znth ((i - 1) - (0 : Int)) power_l (0 : Int))))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_full dp_pre 200)
  ** (intArray.undef_seg power_pre i 20)
|--
  “ (((Znth ((i - 1) - (0 : Int)) power_l (0 : Int)) * 10) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= ((Znth ((i - 1) - (0 : Int)) power_l (0 : Int)) * 10)) ”
) \/
(
forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (i : Int) (PreH1 : (i < 20)) (PreH2 : (1 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (power_l)) = i)) (PreH5 : (PowerPrefix power_l i)) ,
  (intArray.seg power_pre (0 : Int) i power_l)
  ** ((( &( "bef" ) )) # Int64 |-> ((Znth ((i - 1) - (0 : Int)) power_l (0 : Int))))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_full dp_pre 200)
  ** (intArray.undef_seg power_pre i 20)
|--
  “ (((Znth ((i - 1) - (0 : Int)) power_l (0 : Int)) * 10) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= ((Znth ((i - 1) - (0 : Int)) power_l (0 : Int)) * 10)) ”
)

noncomputable def digits_sum_init_safety_wit_8_split_goal_1 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (i : Int) (PreH1 : (i < 20)) (PreH2 : (1 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (power_l)) = i)) (PreH5 : (PowerPrefix power_l i)) ,
  (intArray.seg power_pre (0 : Int) i power_l)
  ** ((( &( "bef" ) )) # Int64 |-> ((Znth ((i - 1) - (0 : Int)) power_l (0 : Int))))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_full dp_pre 200)
  ** (intArray.undef_seg power_pre i 20)
|--
  “ (((Znth ((i - 1) - (0 : Int)) power_l (0 : Int)) * 10) <= 9223372036854775807) ”

noncomputable def digits_sum_init_safety_wit_8_split_goal_2 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (i : Int) (PreH1 : (i < 20)) (PreH2 : (1 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (power_l)) = i)) (PreH5 : (PowerPrefix power_l i)) ,
  (intArray.seg power_pre (0 : Int) i power_l)
  ** ((( &( "bef" ) )) # Int64 |-> ((Znth ((i - 1) - (0 : Int)) power_l (0 : Int))))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_full dp_pre 200)
  ** (intArray.undef_seg power_pre i 20)
|--
  “ ((-9223372036854775808) <= ((Znth ((i - 1) - (0 : Int)) power_l (0 : Int)) * 10)) ”

noncomputable def digits_sum_init_safety_wit_9 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (i : Int) (PreH1 : (i < 20)) (PreH2 : (1 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (power_l)) = i)) (PreH5 : (PowerPrefix power_l i)) ,
  (intArray.seg power_pre (0 : Int) i power_l)
  ** ((( &( "bef" ) )) # Int64 |-> ((Znth ((i - 1) - (0 : Int)) power_l (0 : Int))))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_full dp_pre 200)
  ** (intArray.undef_seg power_pre i 20)
|--
  “ (10 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 10) ”

noncomputable def digits_sum_init_safety_wit_10 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (i : Int) (PreH1 : (i < 20)) (PreH2 : (1 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (power_l)) = i)) (PreH5 : (PowerPrefix power_l i)) ,
  (intArray.seg power_pre (0 : Int) i power_l)
  ** ((( &( "bef" ) )) # Int64 |-> ((Znth ((i - 1) - (0 : Int)) power_l (0 : Int))))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_full dp_pre 200)
  ** (intArray.undef_seg power_pre i 20)
|--
  “ (1000000007 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1000000007) ”

noncomputable def digits_sum_init_safety_wit_11 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (i : Int) (PreH1 : (i < 20)) (PreH2 : (1 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (power_l)) = i)) (PreH5 : (PowerPrefix power_l i)) ,
  (intArray.seg power_pre (0 : Int) (i + 1) (power_l ++ ((signed_last_nbits ((Z.rem ((Znth ((i - 1) - (0 : Int)) power_l (0 : Int)) * 10) 1000000007)) (32)) :: (@List.nil Int))))
  ** (intArray.undef_seg power_pre (i + 1) 20)
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_full dp_pre 200)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def digits_sum_init_safety_wit_12 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (i : Int) (PreH1 : (i >= 20)) (PreH2 : (1 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (power_l)) = i)) (PreH5 : (PowerPrefix power_l i)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** (intArray.undef_full dp_pre 200)
  ** (intArray.seg power_pre (0 : Int) i power_l)
  ** (intArray.undef_seg power_pre i 20)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def digits_sum_init_safety_wit_13 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (i : Int) (PreH1 : ((0 : Int) <= i)) (PreH2 : (i <= 20)) (PreH3 : ((Zlength (dp_l)) = (i * 10))) (PreH4 : (Forall (Eq ((0 : Int))) dp_l)) (PreH5 : (PowerTable power_l)) ,
  ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.seg dp_pre (0 : Int) (i * 10) dp_l)
  ** (intArray.undef_seg dp_pre (i * 10) 200)
  ** (intArray.full power_pre 20 power_l)
|--
  “ (20 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 20) ”

noncomputable def digits_sum_init_safety_wit_14 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (i : Int) (PreH1 : (i < 20)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (dp_l)) = (i * 10))) (PreH5 : (Forall (Eq ((0 : Int))) dp_l)) (PreH6 : (PowerTable power_l)) ,
  ((( &( "j" ) )) # Int |->_)
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.seg dp_pre (0 : Int) (i * 10) dp_l)
  ** (intArray.undef_seg dp_pre (i * 10) 200)
  ** (intArray.full power_pre 20 power_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def digits_sum_init_safety_wit_15 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (PreH1 : ((0 : Int) <= i)) (PreH2 : (i < 20)) (PreH3 : ((0 : Int) <= j)) (PreH4 : (j <= 10)) (PreH5 : ((Zlength (dp_l)) = ((i * 10) + j))) (PreH6 : (Forall (Eq ((0 : Int))) dp_l)) (PreH7 : (PowerTable power_l)) ,
  ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg dp_pre (0 : Int) ((i * 10) + j) dp_l)
  ** (intArray.undef_seg dp_pre ((i * 10) + j) 200)
  ** (intArray.full power_pre 20 power_l)
|--
  “ (10 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 10) ”

noncomputable def digits_sum_init_safety_wit_16 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (PreH1 : (j < 10)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j <= 10)) (PreH6 : ((Zlength (dp_l)) = ((i * 10) + j))) (PreH7 : (Forall (Eq ((0 : Int))) dp_l)) (PreH8 : (PowerTable power_l)) ,
  ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg dp_pre (0 : Int) ((i * 10) + j) dp_l)
  ** (intArray.undef_seg dp_pre ((i * 10) + j) 200)
  ** (intArray.full power_pre 20 power_l)
|--
  “ (((i * 10) + j) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((i * 10) + j)) ”

noncomputable def digits_sum_init_safety_wit_17 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (PreH1 : (j < 10)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j <= 10)) (PreH6 : ((Zlength (dp_l)) = ((i * 10) + j))) (PreH7 : (Forall (Eq ((0 : Int))) dp_l)) (PreH8 : (PowerTable power_l)) ,
  ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg dp_pre (0 : Int) ((i * 10) + j) dp_l)
  ** (intArray.undef_seg dp_pre ((i * 10) + j) 200)
  ** (intArray.full power_pre 20 power_l)
|--
  “ ((i * 10) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i * 10)) ”

noncomputable def digits_sum_init_safety_wit_18 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (PreH1 : (j < 10)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j <= 10)) (PreH6 : ((Zlength (dp_l)) = ((i * 10) + j))) (PreH7 : (Forall (Eq ((0 : Int))) dp_l)) (PreH8 : (PowerTable power_l)) ,
  ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg dp_pre (0 : Int) ((i * 10) + j) dp_l)
  ** (intArray.undef_seg dp_pre ((i * 10) + j) 200)
  ** (intArray.full power_pre 20 power_l)
|--
  “ (10 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 10) ”

noncomputable def digits_sum_init_safety_wit_19 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (PreH1 : (j < 10)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j <= 10)) (PreH6 : ((Zlength (dp_l)) = ((i * 10) + j))) (PreH7 : (Forall (Eq ((0 : Int))) dp_l)) (PreH8 : (PowerTable power_l)) ,
  ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.seg dp_pre (0 : Int) ((i * 10) + j) dp_l)
  ** (intArray.undef_seg dp_pre ((i * 10) + j) 200)
  ** (intArray.full power_pre 20 power_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def digits_sum_init_safety_wit_20 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (PreH1 : (j < 10)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j <= 10)) (PreH6 : ((Zlength (dp_l)) = ((i * 10) + j))) (PreH7 : (Forall (Eq ((0 : Int))) dp_l)) (PreH8 : (PowerTable power_l)) ,
  (intArray.seg dp_pre (0 : Int) (((i * 10) + j) + 1) (dp_l ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg dp_pre (((i * 10) + j) + 1) 200)
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full power_pre 20 power_l)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def digits_sum_init_safety_wit_21 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (PreH1 : (j >= 10)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j <= 10)) (PreH6 : ((Zlength (dp_l)) = ((i * 10) + j))) (PreH7 : (Forall (Eq ((0 : Int))) dp_l)) (PreH8 : (PowerTable power_l)) ,
  ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.seg dp_pre (0 : Int) ((i * 10) + j) dp_l)
  ** (intArray.undef_seg dp_pre ((i * 10) + j) 200)
  ** (intArray.full power_pre 20 power_l)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def digits_sum_init_safety_wit_22 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (i : Int) (PreH1 : (i >= 20)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (dp_l)) = (i * 10))) (PreH5 : (Forall (Eq ((0 : Int))) dp_l)) (PreH6 : (PowerTable power_l)) ,
  ((( &( "j" ) )) # Int |->_)
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** (intArray.seg dp_pre (0 : Int) (i * 10) dp_l)
  ** (intArray.undef_seg dp_pre (i * 10) 200)
  ** (intArray.full power_pre 20 power_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def digits_sum_init_safety_wit_23 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (j : Int) (PreH1 : ((0 : Int) <= j)) (PreH2 : (j <= 10)) (PreH3 : ((Zlength (dp_l)) = 200)) (PreH4 : (DigitDPBaseProgress dp_l j)) (PreH5 : (PowerTable power_l)) ,
  ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full dp_pre 200 dp_l)
  ** (intArray.full power_pre 20 power_l)
|--
  “ (10 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 10) ”

noncomputable def digits_sum_init_safety_wit_24 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (j : Int) (PreH1 : (j < 10)) (PreH2 : ((0 : Int) <= j)) (PreH3 : (j <= 10)) (PreH4 : ((Zlength (dp_l)) = 200)) (PreH5 : (DigitDPBaseProgress dp_l j)) (PreH6 : (PowerTable power_l)) ,
  ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full dp_pre 200 dp_l)
  ** (intArray.full power_pre 20 power_l)
|--
  “ ((10 + j) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (10 + j)) ”

noncomputable def digits_sum_init_safety_wit_25 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (j : Int) (PreH1 : (j < 10)) (PreH2 : ((0 : Int) <= j)) (PreH3 : (j <= 10)) (PreH4 : ((Zlength (dp_l)) = 200)) (PreH5 : (DigitDPBaseProgress dp_l j)) (PreH6 : (PowerTable power_l)) ,
  ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full dp_pre 200 dp_l)
  ** (intArray.full power_pre 20 power_l)
|--
  “ (10 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 10) ”

noncomputable def digits_sum_init_safety_wit_26 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (j : Int) (PreH1 : (j < 10)) (PreH2 : ((0 : Int) <= j)) (PreH3 : (j <= 10)) (PreH4 : ((Zlength (dp_l)) = 200)) (PreH5 : (DigitDPBaseProgress dp_l j)) (PreH6 : (PowerTable power_l)) ,
  (intArray.full dp_pre 200 (replace_Znth ((10 + j)) (j) (dp_l)))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full power_pre 20 power_l)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def digits_sum_init_safety_wit_27 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (j : Int) (PreH1 : (j >= 10)) (PreH2 : ((0 : Int) <= j)) (PreH3 : (j <= 10)) (PreH4 : ((Zlength (dp_l)) = 200)) (PreH5 : (DigitDPBaseProgress dp_l j)) (PreH6 : (PowerTable power_l)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** (intArray.full dp_pre 200 dp_l)
  ** (intArray.full power_pre 20 power_l)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def digits_sum_init_safety_wit_28 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (i : Int) (PreH1 : (2 <= i)) (PreH2 : (i <= 20)) (PreH3 : ((Zlength (dp_l)) = 200)) (PreH4 : (DigitDPOuterProgress dp_l i)) (PreH5 : (PowerTable power_l)) ,
  ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full dp_pre 200 dp_l)
  ** (intArray.full power_pre 20 power_l)
|--
  “ (20 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 20) ”

noncomputable def digits_sum_init_safety_wit_29 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (i : Int) (PreH1 : (i < 20)) (PreH2 : (2 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (dp_l)) = 200)) (PreH5 : (DigitDPOuterProgress dp_l i)) (PreH6 : (PowerTable power_l)) ,
  ((( &( "j" ) )) # Int |->_)
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full dp_pre 200 dp_l)
  ** (intArray.full power_pre 20 power_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def digits_sum_init_safety_wit_30 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (PreH1 : (2 <= i)) (PreH2 : (i < 20)) (PreH3 : ((0 : Int) <= j)) (PreH4 : (j <= 10)) (PreH5 : ((Zlength (dp_l)) = 200)) (PreH6 : (DigitDPRowProgress dp_l i j)) (PreH7 : (PowerTable power_l)) ,
  ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full dp_pre 200 dp_l)
  ** (intArray.full power_pre 20 power_l)
|--
  “ (10 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 10) ”

noncomputable def digits_sum_init_safety_wit_31 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (PreH1 : (j < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j <= 10)) (PreH6 : ((Zlength (dp_l)) = 200)) (PreH7 : (DigitDPRowProgress dp_l i j)) (PreH8 : (PowerTable power_l)) ,
  ((( &( "k" ) )) # Int |->_)
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full dp_pre 200 dp_l)
  ** (intArray.full power_pre 20 power_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def digits_sum_init_safety_wit_32 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (k : Int) (j : Int) (i : Int) (PreH1 : (2 <= i)) (PreH2 : (i < 20)) (PreH3 : ((0 : Int) <= j)) (PreH4 : (j < 10)) (PreH5 : ((0 : Int) <= k)) (PreH6 : (k <= 10)) (PreH7 : ((Zlength (dp_l)) = 200)) (PreH8 : (DigitDPCellProgress dp_l i j k)) (PreH9 : (PowerTable power_l)) ,
  ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full dp_pre 200 dp_l)
  ** (intArray.full power_pre 20 power_l)
|--
  “ (10 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 10) ”

noncomputable def digits_sum_init_safety_wit_33 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (k : Int) (j : Int) (i : Int) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j < 10)) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k)) (PreH10 : (PowerTable power_l)) ,
  ((( &( "sub_power" ) )) # Int64 |->_)
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full dp_pre 200 dp_l)
  ** (intArray.full power_pre 20 power_l)
|--
  “ ((i - 2) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 2)) ”

noncomputable def digits_sum_init_safety_wit_34 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (k : Int) (j : Int) (i : Int) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j < 10)) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k)) (PreH10 : (PowerTable power_l)) ,
  ((( &( "sub_power" ) )) # Int64 |->_)
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full dp_pre 200 dp_l)
  ** (intArray.full power_pre 20 power_l)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def digits_sum_init_safety_wit_35 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (k : Int) (j : Int) (i : Int) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j < 10)) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k)) (PreH10 : (PowerTable power_l)) ,
  (intArray.full dp_pre 200 dp_l)
  ** ((( &( "moving" ) )) # Int64 |->_)
  ** (intArray.full power_pre 20 power_l)
  ** ((( &( "sub_power" ) )) # Int64 |-> ((Znth (i - 2) power_l (0 : Int))))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ ((((Znth (((i - 1) * 10) + k) dp_l (0 : Int)) + (Z.rem ((Znth (i - 2) power_l (0 : Int)) * j) 1000000007)) ≠ (-9223372036854775808)) ∨ (1000000007 ≠ (-1))) ” &&
  “ (1000000007 ≠ (0 : Int)) ”

noncomputable def digits_sum_init_safety_wit_36 : Prop :=
  (
forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (k : Int) (j : Int) (i : Int) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j < 10)) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k)) (PreH10 : (PowerTable power_l)) ,
  (intArray.full dp_pre 200 dp_l)
  ** ((( &( "moving" ) )) # Int64 |->_)
  ** (intArray.full power_pre 20 power_l)
  ** ((( &( "sub_power" ) )) # Int64 |-> ((Znth (i - 2) power_l (0 : Int))))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ (((Znth (((i - 1) * 10) + k) dp_l (0 : Int)) + (Z.rem ((Znth (i - 2) power_l (0 : Int)) * j) 1000000007)) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= ((Znth (((i - 1) * 10) + k) dp_l (0 : Int)) + (Z.rem ((Znth (i - 2) power_l (0 : Int)) * j) 1000000007))) ”
) \/
(
forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (k : Int) (j : Int) (i : Int) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j < 10)) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k)) (PreH10 : (PowerTable power_l)) ,
  (intArray.full dp_pre 200 dp_l)
  ** ((( &( "moving" ) )) # Int64 |->_)
  ** (intArray.full power_pre 20 power_l)
  ** ((( &( "sub_power" ) )) # Int64 |-> ((Znth (i - 2) power_l (0 : Int))))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ (((Znth (((i - 1) * 10) + k) dp_l (0 : Int)) + (Z.rem ((Znth (i - 2) power_l (0 : Int)) * j) 1000000007)) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= ((Znth (((i - 1) * 10) + k) dp_l (0 : Int)) + (Z.rem ((Znth (i - 2) power_l (0 : Int)) * j) 1000000007))) ”
)

noncomputable def digits_sum_init_safety_wit_36_split_goal_1 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (k : Int) (j : Int) (i : Int) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j < 10)) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k)) (PreH10 : (PowerTable power_l)) ,
  (intArray.full dp_pre 200 dp_l)
  ** ((( &( "moving" ) )) # Int64 |->_)
  ** (intArray.full power_pre 20 power_l)
  ** ((( &( "sub_power" ) )) # Int64 |-> ((Znth (i - 2) power_l (0 : Int))))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ (((Znth (((i - 1) * 10) + k) dp_l (0 : Int)) + (Z.rem ((Znth (i - 2) power_l (0 : Int)) * j) 1000000007)) <= 9223372036854775807) ”

noncomputable def digits_sum_init_safety_wit_36_split_goal_2 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (k : Int) (j : Int) (i : Int) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j < 10)) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k)) (PreH10 : (PowerTable power_l)) ,
  (intArray.full dp_pre 200 dp_l)
  ** ((( &( "moving" ) )) # Int64 |->_)
  ** (intArray.full power_pre 20 power_l)
  ** ((( &( "sub_power" ) )) # Int64 |-> ((Znth (i - 2) power_l (0 : Int))))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ ((-9223372036854775808) <= ((Znth (((i - 1) * 10) + k) dp_l (0 : Int)) + (Z.rem ((Znth (i - 2) power_l (0 : Int)) * j) 1000000007))) ”

noncomputable def digits_sum_init_safety_wit_37 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (k : Int) (j : Int) (i : Int) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j < 10)) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k)) (PreH10 : (PowerTable power_l)) ,
  (intArray.full dp_pre 200 dp_l)
  ** ((( &( "moving" ) )) # Int64 |->_)
  ** (intArray.full power_pre 20 power_l)
  ** ((( &( "sub_power" ) )) # Int64 |-> ((Znth (i - 2) power_l (0 : Int))))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ ((((Znth (i - 2) power_l (0 : Int)) * j) ≠ (-9223372036854775808)) ∨ (1000000007 ≠ (-1))) ” &&
  “ (1000000007 ≠ (0 : Int)) ”

noncomputable def digits_sum_init_safety_wit_38 : Prop :=
  (
forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (k : Int) (j : Int) (i : Int) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j < 10)) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k)) (PreH10 : (PowerTable power_l)) ,
  (intArray.full dp_pre 200 dp_l)
  ** ((( &( "moving" ) )) # Int64 |->_)
  ** (intArray.full power_pre 20 power_l)
  ** ((( &( "sub_power" ) )) # Int64 |-> ((Znth (i - 2) power_l (0 : Int))))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ (((Znth (i - 2) power_l (0 : Int)) * j) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= ((Znth (i - 2) power_l (0 : Int)) * j)) ”
) \/
(
forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (k : Int) (j : Int) (i : Int) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j < 10)) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k)) (PreH10 : (PowerTable power_l)) ,
  (intArray.full dp_pre 200 dp_l)
  ** ((( &( "moving" ) )) # Int64 |->_)
  ** (intArray.full power_pre 20 power_l)
  ** ((( &( "sub_power" ) )) # Int64 |-> ((Znth (i - 2) power_l (0 : Int))))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ (((Znth (i - 2) power_l (0 : Int)) * j) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= ((Znth (i - 2) power_l (0 : Int)) * j)) ”
)

noncomputable def digits_sum_init_safety_wit_38_split_goal_1 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (k : Int) (j : Int) (i : Int) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j < 10)) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k)) (PreH10 : (PowerTable power_l)) ,
  (intArray.full dp_pre 200 dp_l)
  ** ((( &( "moving" ) )) # Int64 |->_)
  ** (intArray.full power_pre 20 power_l)
  ** ((( &( "sub_power" ) )) # Int64 |-> ((Znth (i - 2) power_l (0 : Int))))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ (((Znth (i - 2) power_l (0 : Int)) * j) <= 9223372036854775807) ”

noncomputable def digits_sum_init_safety_wit_38_split_goal_2 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (k : Int) (j : Int) (i : Int) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j < 10)) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k)) (PreH10 : (PowerTable power_l)) ,
  (intArray.full dp_pre 200 dp_l)
  ** ((( &( "moving" ) )) # Int64 |->_)
  ** (intArray.full power_pre 20 power_l)
  ** ((( &( "sub_power" ) )) # Int64 |-> ((Znth (i - 2) power_l (0 : Int))))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ ((-9223372036854775808) <= ((Znth (i - 2) power_l (0 : Int)) * j)) ”

noncomputable def digits_sum_init_safety_wit_39 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (k : Int) (j : Int) (i : Int) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j < 10)) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k)) (PreH10 : (PowerTable power_l)) ,
  ((( &( "moving" ) )) # Int64 |->_)
  ** (intArray.full power_pre 20 power_l)
  ** ((( &( "sub_power" ) )) # Int64 |-> ((Znth (i - 2) power_l (0 : Int))))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full dp_pre 200 dp_l)
|--
  “ ((((i - 1) * 10) + k) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (((i - 1) * 10) + k)) ”

noncomputable def digits_sum_init_safety_wit_40 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (k : Int) (j : Int) (i : Int) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j < 10)) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k)) (PreH10 : (PowerTable power_l)) ,
  ((( &( "moving" ) )) # Int64 |->_)
  ** (intArray.full power_pre 20 power_l)
  ** ((( &( "sub_power" ) )) # Int64 |-> ((Znth (i - 2) power_l (0 : Int))))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full dp_pre 200 dp_l)
|--
  “ (((i - 1) * 10) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((i - 1) * 10)) ”

noncomputable def digits_sum_init_safety_wit_41 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (k : Int) (j : Int) (i : Int) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j < 10)) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k)) (PreH10 : (PowerTable power_l)) ,
  ((( &( "moving" ) )) # Int64 |->_)
  ** (intArray.full power_pre 20 power_l)
  ** ((( &( "sub_power" ) )) # Int64 |-> ((Znth (i - 2) power_l (0 : Int))))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full dp_pre 200 dp_l)
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def digits_sum_init_safety_wit_42 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (k : Int) (j : Int) (i : Int) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j < 10)) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k)) (PreH10 : (PowerTable power_l)) ,
  ((( &( "moving" ) )) # Int64 |->_)
  ** (intArray.full power_pre 20 power_l)
  ** ((( &( "sub_power" ) )) # Int64 |-> ((Znth (i - 2) power_l (0 : Int))))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full dp_pre 200 dp_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def digits_sum_init_safety_wit_43 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (k : Int) (j : Int) (i : Int) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j < 10)) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k)) (PreH10 : (PowerTable power_l)) ,
  ((( &( "moving" ) )) # Int64 |->_)
  ** (intArray.full power_pre 20 power_l)
  ** ((( &( "sub_power" ) )) # Int64 |-> ((Znth (i - 2) power_l (0 : Int))))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
  ** (intArray.full dp_pre 200 dp_l)
|--
  “ (10 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 10) ”

noncomputable def digits_sum_init_safety_wit_44 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (k : Int) (j : Int) (i : Int) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j < 10)) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k)) (PreH10 : (PowerTable power_l)) ,
  (intArray.full dp_pre 200 dp_l)
  ** ((( &( "moving" ) )) # Int64 |->_)
  ** (intArray.full power_pre 20 power_l)
  ** ((( &( "sub_power" ) )) # Int64 |-> ((Znth (i - 2) power_l (0 : Int))))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ (1000000007 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1000000007) ”

noncomputable def digits_sum_init_safety_wit_45 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (k : Int) (j : Int) (i : Int) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j < 10)) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k)) (PreH10 : (PowerTable power_l)) ,
  (intArray.full dp_pre 200 dp_l)
  ** ((( &( "moving" ) )) # Int64 |->_)
  ** (intArray.full power_pre 20 power_l)
  ** ((( &( "sub_power" ) )) # Int64 |-> ((Znth (i - 2) power_l (0 : Int))))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ (1000000007 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1000000007) ”

noncomputable def digits_sum_init_safety_wit_46 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (k : Int) (j : Int) (i : Int) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j < 10)) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k)) (PreH10 : (PowerTable power_l)) ,
  (intArray.full dp_pre 200 dp_l)
  ** ((( &( "new_dp" ) )) # Int64 |->_)
  ** ((( &( "moving" ) )) # Int64 |-> ((Z.rem ((Znth (((i - 1) * 10) + k) dp_l (0 : Int)) + (Z.rem ((Znth (i - 2) power_l (0 : Int)) * j) 1000000007)) 1000000007)))
  ** (intArray.full power_pre 20 power_l)
  ** ((( &( "sub_power" ) )) # Int64 |-> ((Znth (i - 2) power_l (0 : Int))))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ ((((Znth ((i * 10) + j) dp_l (0 : Int)) + (Z.rem ((Znth (((i - 1) * 10) + k) dp_l (0 : Int)) + (Z.rem ((Znth (i - 2) power_l (0 : Int)) * j) 1000000007)) 1000000007)) ≠ (-9223372036854775808)) ∨ (1000000007 ≠ (-1))) ” &&
  “ (1000000007 ≠ (0 : Int)) ”

noncomputable def digits_sum_init_safety_wit_47 : Prop :=
  (
forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (k : Int) (j : Int) (i : Int) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j < 10)) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k)) (PreH10 : (PowerTable power_l)) ,
  (intArray.full dp_pre 200 dp_l)
  ** ((( &( "new_dp" ) )) # Int64 |->_)
  ** ((( &( "moving" ) )) # Int64 |-> ((Z.rem ((Znth (((i - 1) * 10) + k) dp_l (0 : Int)) + (Z.rem ((Znth (i - 2) power_l (0 : Int)) * j) 1000000007)) 1000000007)))
  ** (intArray.full power_pre 20 power_l)
  ** ((( &( "sub_power" ) )) # Int64 |-> ((Znth (i - 2) power_l (0 : Int))))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ (((Znth ((i * 10) + j) dp_l (0 : Int)) + (Z.rem ((Znth (((i - 1) * 10) + k) dp_l (0 : Int)) + (Z.rem ((Znth (i - 2) power_l (0 : Int)) * j) 1000000007)) 1000000007)) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= ((Znth ((i * 10) + j) dp_l (0 : Int)) + (Z.rem ((Znth (((i - 1) * 10) + k) dp_l (0 : Int)) + (Z.rem ((Znth (i - 2) power_l (0 : Int)) * j) 1000000007)) 1000000007))) ”
) \/
(
forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (k : Int) (j : Int) (i : Int) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j < 10)) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k)) (PreH10 : (PowerTable power_l)) ,
  (intArray.full dp_pre 200 dp_l)
  ** ((( &( "new_dp" ) )) # Int64 |->_)
  ** ((( &( "moving" ) )) # Int64 |-> ((Z.rem ((Znth (((i - 1) * 10) + k) dp_l (0 : Int)) + (Z.rem ((Znth (i - 2) power_l (0 : Int)) * j) 1000000007)) 1000000007)))
  ** (intArray.full power_pre 20 power_l)
  ** ((( &( "sub_power" ) )) # Int64 |-> ((Znth (i - 2) power_l (0 : Int))))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ (((Znth ((i * 10) + j) dp_l (0 : Int)) + (Z.rem ((Znth (((i - 1) * 10) + k) dp_l (0 : Int)) + (Z.rem ((Znth (i - 2) power_l (0 : Int)) * j) 1000000007)) 1000000007)) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= ((Znth ((i * 10) + j) dp_l (0 : Int)) + (Z.rem ((Znth (((i - 1) * 10) + k) dp_l (0 : Int)) + (Z.rem ((Znth (i - 2) power_l (0 : Int)) * j) 1000000007)) 1000000007))) ”
)

noncomputable def digits_sum_init_safety_wit_47_split_goal_1 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (k : Int) (j : Int) (i : Int) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j < 10)) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k)) (PreH10 : (PowerTable power_l)) ,
  (intArray.full dp_pre 200 dp_l)
  ** ((( &( "new_dp" ) )) # Int64 |->_)
  ** ((( &( "moving" ) )) # Int64 |-> ((Z.rem ((Znth (((i - 1) * 10) + k) dp_l (0 : Int)) + (Z.rem ((Znth (i - 2) power_l (0 : Int)) * j) 1000000007)) 1000000007)))
  ** (intArray.full power_pre 20 power_l)
  ** ((( &( "sub_power" ) )) # Int64 |-> ((Znth (i - 2) power_l (0 : Int))))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ (((Znth ((i * 10) + j) dp_l (0 : Int)) + (Z.rem ((Znth (((i - 1) * 10) + k) dp_l (0 : Int)) + (Z.rem ((Znth (i - 2) power_l (0 : Int)) * j) 1000000007)) 1000000007)) <= 9223372036854775807) ”

noncomputable def digits_sum_init_safety_wit_47_split_goal_2 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (k : Int) (j : Int) (i : Int) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j < 10)) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k)) (PreH10 : (PowerTable power_l)) ,
  (intArray.full dp_pre 200 dp_l)
  ** ((( &( "new_dp" ) )) # Int64 |->_)
  ** ((( &( "moving" ) )) # Int64 |-> ((Z.rem ((Znth (((i - 1) * 10) + k) dp_l (0 : Int)) + (Z.rem ((Znth (i - 2) power_l (0 : Int)) * j) 1000000007)) 1000000007)))
  ** (intArray.full power_pre 20 power_l)
  ** ((( &( "sub_power" ) )) # Int64 |-> ((Znth (i - 2) power_l (0 : Int))))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ ((-9223372036854775808) <= ((Znth ((i * 10) + j) dp_l (0 : Int)) + (Z.rem ((Znth (((i - 1) * 10) + k) dp_l (0 : Int)) + (Z.rem ((Znth (i - 2) power_l (0 : Int)) * j) 1000000007)) 1000000007))) ”

noncomputable def digits_sum_init_safety_wit_48 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (k : Int) (j : Int) (i : Int) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j < 10)) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k)) (PreH10 : (PowerTable power_l)) ,
  ((( &( "new_dp" ) )) # Int64 |->_)
  ** (intArray.full dp_pre 200 dp_l)
  ** ((( &( "moving" ) )) # Int64 |-> ((Z.rem ((Znth (((i - 1) * 10) + k) dp_l (0 : Int)) + (Z.rem ((Znth (i - 2) power_l (0 : Int)) * j) 1000000007)) 1000000007)))
  ** (intArray.full power_pre 20 power_l)
  ** ((( &( "sub_power" ) )) # Int64 |-> ((Znth (i - 2) power_l (0 : Int))))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ (((i * 10) + j) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((i * 10) + j)) ”

noncomputable def digits_sum_init_safety_wit_49 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (k : Int) (j : Int) (i : Int) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j < 10)) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k)) (PreH10 : (PowerTable power_l)) ,
  ((( &( "new_dp" ) )) # Int64 |->_)
  ** (intArray.full dp_pre 200 dp_l)
  ** ((( &( "moving" ) )) # Int64 |-> ((Z.rem ((Znth (((i - 1) * 10) + k) dp_l (0 : Int)) + (Z.rem ((Znth (i - 2) power_l (0 : Int)) * j) 1000000007)) 1000000007)))
  ** (intArray.full power_pre 20 power_l)
  ** ((( &( "sub_power" ) )) # Int64 |-> ((Znth (i - 2) power_l (0 : Int))))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ ((i * 10) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i * 10)) ”

noncomputable def digits_sum_init_safety_wit_50 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (k : Int) (j : Int) (i : Int) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j < 10)) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k)) (PreH10 : (PowerTable power_l)) ,
  ((( &( "new_dp" ) )) # Int64 |->_)
  ** (intArray.full dp_pre 200 dp_l)
  ** ((( &( "moving" ) )) # Int64 |-> ((Z.rem ((Znth (((i - 1) * 10) + k) dp_l (0 : Int)) + (Z.rem ((Znth (i - 2) power_l (0 : Int)) * j) 1000000007)) 1000000007)))
  ** (intArray.full power_pre 20 power_l)
  ** ((( &( "sub_power" ) )) # Int64 |-> ((Znth (i - 2) power_l (0 : Int))))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ (10 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 10) ”

noncomputable def digits_sum_init_safety_wit_51 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (k : Int) (j : Int) (i : Int) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j < 10)) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k)) (PreH10 : (PowerTable power_l)) ,
  (intArray.full dp_pre 200 dp_l)
  ** ((( &( "new_dp" ) )) # Int64 |->_)
  ** ((( &( "moving" ) )) # Int64 |-> ((Z.rem ((Znth (((i - 1) * 10) + k) dp_l (0 : Int)) + (Z.rem ((Znth (i - 2) power_l (0 : Int)) * j) 1000000007)) 1000000007)))
  ** (intArray.full power_pre 20 power_l)
  ** ((( &( "sub_power" ) )) # Int64 |-> ((Znth (i - 2) power_l (0 : Int))))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ (1000000007 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1000000007) ”

noncomputable def digits_sum_init_safety_wit_52 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (k : Int) (j : Int) (i : Int) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j < 10)) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k)) (PreH10 : (PowerTable power_l)) ,
  (intArray.full dp_pre 200 dp_l)
  ** ((( &( "new_dp" ) )) # Int64 |-> ((Z.rem ((Znth ((i * 10) + j) dp_l (0 : Int)) + (Z.rem ((Znth (((i - 1) * 10) + k) dp_l (0 : Int)) + (Z.rem ((Znth (i - 2) power_l (0 : Int)) * j) 1000000007)) 1000000007)) 1000000007)))
  ** ((( &( "moving" ) )) # Int64 |-> ((Z.rem ((Znth (((i - 1) * 10) + k) dp_l (0 : Int)) + (Z.rem ((Znth (i - 2) power_l (0 : Int)) * j) 1000000007)) 1000000007)))
  ** (intArray.full power_pre 20 power_l)
  ** ((( &( "sub_power" ) )) # Int64 |-> ((Znth (i - 2) power_l (0 : Int))))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ (((i * 10) + j) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((i * 10) + j)) ”

noncomputable def digits_sum_init_safety_wit_53 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (k : Int) (j : Int) (i : Int) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j < 10)) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k)) (PreH10 : (PowerTable power_l)) ,
  (intArray.full dp_pre 200 dp_l)
  ** ((( &( "new_dp" ) )) # Int64 |-> ((Z.rem ((Znth ((i * 10) + j) dp_l (0 : Int)) + (Z.rem ((Znth (((i - 1) * 10) + k) dp_l (0 : Int)) + (Z.rem ((Znth (i - 2) power_l (0 : Int)) * j) 1000000007)) 1000000007)) 1000000007)))
  ** ((( &( "moving" ) )) # Int64 |-> ((Z.rem ((Znth (((i - 1) * 10) + k) dp_l (0 : Int)) + (Z.rem ((Znth (i - 2) power_l (0 : Int)) * j) 1000000007)) 1000000007)))
  ** (intArray.full power_pre 20 power_l)
  ** ((( &( "sub_power" ) )) # Int64 |-> ((Znth (i - 2) power_l (0 : Int))))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ ((i * 10) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i * 10)) ”

noncomputable def digits_sum_init_safety_wit_54 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (k : Int) (j : Int) (i : Int) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j < 10)) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k)) (PreH10 : (PowerTable power_l)) ,
  (intArray.full dp_pre 200 dp_l)
  ** ((( &( "new_dp" ) )) # Int64 |-> ((Z.rem ((Znth ((i * 10) + j) dp_l (0 : Int)) + (Z.rem ((Znth (((i - 1) * 10) + k) dp_l (0 : Int)) + (Z.rem ((Znth (i - 2) power_l (0 : Int)) * j) 1000000007)) 1000000007)) 1000000007)))
  ** ((( &( "moving" ) )) # Int64 |-> ((Z.rem ((Znth (((i - 1) * 10) + k) dp_l (0 : Int)) + (Z.rem ((Znth (i - 2) power_l (0 : Int)) * j) 1000000007)) 1000000007)))
  ** (intArray.full power_pre 20 power_l)
  ** ((( &( "sub_power" ) )) # Int64 |-> ((Znth (i - 2) power_l (0 : Int))))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ (10 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 10) ”

noncomputable def digits_sum_init_safety_wit_55 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (k : Int) (j : Int) (i : Int) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j < 10)) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k)) (PreH10 : (PowerTable power_l)) ,
  (intArray.full dp_pre 200 (replace_Znth (((i * 10) + j)) ((signed_last_nbits ((Z.rem ((Znth ((i * 10) + j) dp_l (0 : Int)) + (Z.rem ((Znth (((i - 1) * 10) + k) dp_l (0 : Int)) + (Z.rem ((Znth (i - 2) power_l (0 : Int)) * j) 1000000007)) 1000000007)) 1000000007)) (32))) (dp_l)))
  ** (intArray.full power_pre 20 power_l)
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "k" ) )) # Int |-> (k))
|--
  “ ((k + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (k + 1)) ”

noncomputable def digits_sum_init_safety_wit_56 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (k : Int) (j : Int) (i : Int) (PreH1 : (k >= 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j < 10)) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k)) (PreH10 : (PowerTable power_l)) ,
  ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** (intArray.full dp_pre 200 dp_l)
  ** (intArray.full power_pre 20 power_l)
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def digits_sum_init_safety_wit_57 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (PreH1 : (j >= 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j <= 10)) (PreH6 : ((Zlength (dp_l)) = 200)) (PreH7 : (DigitDPRowProgress dp_l i j)) (PreH8 : (PowerTable power_l)) ,
  ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "power" ) )) # Ptr |-> (power_pre))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full dp_pre 200 dp_l)
  ** (intArray.full power_pre 20 power_l)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def digits_sum_init_entail_wit_1 : Prop :=
  (
forall (power_pre : Int) (dp_pre : Int) ,
  (((power_pre + ((0 : Int) * sizeof(INT)))) # Int |-> (1))
  ** (intArray.undef_seg power_pre 1 20)
  ** (intArray.undef_full dp_pre 200)
|--
  EX power_l : (List Int),
  “ (1 <= 1) ” &&
  “ (1 <= 20) ” &&
  “ ((Zlength (power_l)) = 1) ” &&
  “ (PowerPrefix power_l 1) ”
  &&  (intArray.undef_full dp_pre 200)
  ** (intArray.seg power_pre (0 : Int) 1 power_l)
  ** (intArray.undef_seg power_pre 1 20)
) \/
(
forall (power_pre : Int) (PreH1 : (1 <= INT_MAX)) (PreH2 : (1 >= INT_MIN)) ,
  (((power_pre + ((0 : Int) * sizeof(INT)))) # Int |-> (1))
|--
  EX power_l : (List Int),
  “ (1 <= 1) ” &&
  “ (1 <= 20) ” &&
  “ ((Zlength (power_l)) = 1) ” &&
  “ (PowerPrefix power_l 1) ”
  &&  (intArray.seg power_pre (0 : Int) 1 power_l)
)

noncomputable def digits_sum_init_entail_wit_2 : Prop :=
  (
forall (power_pre : Int) (dp_pre : Int) (power_l_2 : (List Int)) (i : Int) (PreH1 : (i < 20)) (PreH2 : (1 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (power_l_2)) = i)) (PreH5 : (PowerPrefix power_l_2 i)) ,
  (intArray.seg power_pre (0 : Int) (i + 1) (power_l_2 ++ ((signed_last_nbits ((Z.rem ((Znth ((i - 1) - (0 : Int)) power_l_2 (0 : Int)) * 10) 1000000007)) (32)) :: (@List.nil Int))))
  ** (intArray.undef_seg power_pre (i + 1) 20)
  ** (intArray.undef_full dp_pre 200)
|--
  EX power_l : (List Int),
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= 20) ” &&
  “ ((Zlength (power_l)) = (i + 1)) ” &&
  “ (PowerPrefix power_l (i + 1)) ”
  &&  (intArray.undef_full dp_pre 200)
  ** (intArray.seg power_pre (0 : Int) (i + 1) power_l)
  ** (intArray.undef_seg power_pre (i + 1) 20)
) \/
(
forall (power_l_2 : (List Int)) (i : Int) (PreH1 : (i < 20)) (PreH2 : (1 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (power_l_2)) = i)) (PreH5 : (PowerPrefix power_l_2 i)) ,
  TT && emp 
|--
  “ (PowerPrefix (power_l_2 ++ ((signed_last_nbits ((Z.rem ((Znth ((i - 1) - (0 : Int)) power_l_2 (0 : Int)) * 10) 1000000007)) (32)) :: (@List.nil Int))) (i + 1)) ” &&
  “ ((Zlength ((power_l_2 ++ ((signed_last_nbits ((Z.rem ((Znth ((i - 1) - (0 : Int)) power_l_2 (0 : Int)) * 10) 1000000007)) (32)) :: (@List.nil Int))))) = (i + 1)) ”
  &&  emp
)

noncomputable def digits_sum_init_entail_wit_2_split_goal_1 : Prop :=
  forall (power_l_2 : (List Int)) (i : Int) (PreH1 : (i < 20)) (PreH2 : (1 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (power_l_2)) = i)) (PreH5 : (PowerPrefix power_l_2 i)) ,
  (PowerPrefix (power_l_2 ++ ((signed_last_nbits ((Z.rem ((Znth ((i - 1) - (0 : Int)) power_l_2 (0 : Int)) * 10) 1000000007)) (32)) :: (@List.nil Int))) (i + 1))

noncomputable def digits_sum_init_entail_wit_2_split_goal_2 : Prop :=
  forall (power_l_2 : (List Int)) (i : Int) (PreH1 : (i < 20)) (PreH2 : (1 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (power_l_2)) = i)) (PreH5 : (PowerPrefix power_l_2 i)) ,
  ((Zlength ((power_l_2 ++ ((signed_last_nbits ((Z.rem ((Znth ((i - 1) - (0 : Int)) power_l_2 (0 : Int)) * 10) 1000000007)) (32)) :: (@List.nil Int))))) = (i + 1))

noncomputable def digits_sum_init_entail_wit_3 : Prop :=
  (
forall (power_pre : Int) (dp_pre : Int) (power_l_2 : (List Int)) (i : Int) (PreH1 : (i >= 20)) (PreH2 : (1 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (power_l_2)) = i)) (PreH5 : (PowerPrefix power_l_2 i)) ,
  (intArray.undef_full dp_pre 200)
  ** (intArray.seg power_pre (0 : Int) i power_l_2)
  ** (intArray.undef_seg power_pre i 20)
|--
  EX power_l : (List Int), EX dp_l : (List Int),
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 20) ” &&
  “ ((Zlength (dp_l)) = ((0 : Int) * 10)) ” &&
  “ (Forall (Eq ((0 : Int))) dp_l) ” &&
  “ (PowerTable power_l) ”
  &&  (intArray.seg dp_pre (0 : Int) ((0 : Int) * 10) dp_l)
  ** (intArray.undef_seg dp_pre ((0 : Int) * 10) 200)
  ** (intArray.full power_pre 20 power_l)
) \/
(
forall (dp_pre : Int) (power_l_2 : (List Int)) (i : Int) (PreH1 : (i >= 20)) (PreH2 : (1 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (power_l_2)) = i)) (PreH5 : (PowerPrefix power_l_2 i)) ,
  (intArray.undef_full dp_pre 200)
|--
  EX dp_l : (List Int),
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 20) ” &&
  “ ((Zlength (dp_l)) = ((0 : Int) * 10)) ” &&
  “ (Forall (Eq ((0 : Int))) dp_l) ” &&
  “ (PowerTable power_l_2) ”
  &&  (intArray.seg dp_pre (0 : Int) ((0 : Int) * 10) dp_l)
  ** (intArray.undef_seg dp_pre ((0 : Int) * 10) 200)
)

noncomputable def digits_sum_init_entail_wit_4 : Prop :=
  (
forall (power_pre : Int) (dp_pre : Int) (power_l_2 : (List Int)) (dp_l_2 : (List Int)) (i : Int) (PreH1 : (i < 20)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (dp_l_2)) = (i * 10))) (PreH5 : (Forall (Eq ((0 : Int))) dp_l_2)) (PreH6 : (PowerTable power_l_2)) ,
  (intArray.seg dp_pre (0 : Int) (i * 10) dp_l_2)
  ** (intArray.undef_seg dp_pre (i * 10) 200)
  ** (intArray.full power_pre 20 power_l_2)
|--
  EX power_l : (List Int), EX dp_l : (List Int),
  “ ((0 : Int) <= i) ” &&
  “ (i < 20) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 10) ” &&
  “ ((Zlength (dp_l)) = ((i * 10) + (0 : Int))) ” &&
  “ (Forall (Eq ((0 : Int))) dp_l) ” &&
  “ (PowerTable power_l) ”
  &&  (intArray.seg dp_pre (0 : Int) ((i * 10) + (0 : Int)) dp_l)
  ** (intArray.undef_seg dp_pre ((i * 10) + (0 : Int)) 200)
  ** (intArray.full power_pre 20 power_l)
) \/
(
forall (dp_pre : Int) (power_l_2 : (List Int)) (dp_l_2 : (List Int)) (i : Int) (PreH1 : (i < 20)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (dp_l_2)) = (i * 10))) (PreH5 : (Forall (Eq ((0 : Int))) dp_l_2)) (PreH6 : (PowerTable power_l_2)) ,
  (intArray.seg dp_pre (0 : Int) (i * 10) dp_l_2)
|--
  EX dp_l : (List Int),
  “ ((0 : Int) <= i) ” &&
  “ (i < 20) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 10) ” &&
  “ ((Zlength (dp_l)) = ((i * 10) + (0 : Int))) ” &&
  “ (Forall (Eq ((0 : Int))) dp_l) ” &&
  “ (PowerTable power_l_2) ”
  &&  (intArray.seg dp_pre (0 : Int) ((i * 10) + (0 : Int)) dp_l)
)

noncomputable def digits_sum_init_entail_wit_5 : Prop :=
  (
forall (power_pre : Int) (dp_pre : Int) (power_l_2 : (List Int)) (dp_l_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j < 10)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j <= 10)) (PreH6 : ((Zlength (dp_l_2)) = ((i * 10) + j))) (PreH7 : (Forall (Eq ((0 : Int))) dp_l_2)) (PreH8 : (PowerTable power_l_2)) ,
  (intArray.seg dp_pre (0 : Int) (((i * 10) + j) + 1) (dp_l_2 ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg dp_pre (((i * 10) + j) + 1) 200)
  ** (intArray.full power_pre 20 power_l_2)
|--
  EX power_l : (List Int), EX dp_l : (List Int),
  “ ((0 : Int) <= i) ” &&
  “ (i < 20) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= 10) ” &&
  “ ((Zlength (dp_l)) = ((i * 10) + (j + 1))) ” &&
  “ (Forall (Eq ((0 : Int))) dp_l) ” &&
  “ (PowerTable power_l) ”
  &&  (intArray.seg dp_pre (0 : Int) ((i * 10) + (j + 1)) dp_l)
  ** (intArray.undef_seg dp_pre ((i * 10) + (j + 1)) 200)
  ** (intArray.full power_pre 20 power_l)
) \/
(
forall (dp_pre : Int) (power_l_2 : (List Int)) (dp_l_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j < 10)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j <= 10)) (PreH6 : ((Zlength (dp_l_2)) = ((i * 10) + j))) (PreH7 : (Forall (Eq ((0 : Int))) dp_l_2)) (PreH8 : (PowerTable power_l_2)) ,
  (intArray.seg dp_pre (0 : Int) (((i * 10) + j) + 1) (dp_l_2 ++ ((0 : Int) :: (@List.nil Int))))
|--
  EX dp_l : (List Int),
  “ ((0 : Int) <= i) ” &&
  “ (i < 20) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= 10) ” &&
  “ ((Zlength (dp_l)) = ((i * 10) + (j + 1))) ” &&
  “ (Forall (Eq ((0 : Int))) dp_l) ” &&
  “ (PowerTable power_l_2) ”
  &&  (intArray.seg dp_pre (0 : Int) ((i * 10) + (j + 1)) dp_l)
)

noncomputable def digits_sum_init_entail_wit_6 : Prop :=
  (
forall (power_pre : Int) (dp_pre : Int) (power_l_2 : (List Int)) (dp_l_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j >= 10)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j <= 10)) (PreH6 : ((Zlength (dp_l_2)) = ((i * 10) + j))) (PreH7 : (Forall (Eq ((0 : Int))) dp_l_2)) (PreH8 : (PowerTable power_l_2)) ,
  (intArray.seg dp_pre (0 : Int) ((i * 10) + j) dp_l_2)
  ** (intArray.undef_seg dp_pre ((i * 10) + j) 200)
  ** (intArray.full power_pre 20 power_l_2)
|--
  EX power_l : (List Int), EX dp_l : (List Int),
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= 20) ” &&
  “ ((Zlength (dp_l)) = ((i + 1) * 10)) ” &&
  “ (Forall (Eq ((0 : Int))) dp_l) ” &&
  “ (PowerTable power_l) ”
  &&  (intArray.seg dp_pre (0 : Int) ((i + 1) * 10) dp_l)
  ** (intArray.undef_seg dp_pre ((i + 1) * 10) 200)
  ** (intArray.full power_pre 20 power_l)
) \/
(
forall (dp_pre : Int) (power_l_2 : (List Int)) (dp_l_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j >= 10)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j <= 10)) (PreH6 : ((Zlength (dp_l_2)) = ((i * 10) + j))) (PreH7 : (Forall (Eq ((0 : Int))) dp_l_2)) (PreH8 : (PowerTable power_l_2)) ,
  (intArray.seg dp_pre (0 : Int) ((i * 10) + j) dp_l_2)
|--
  EX dp_l : (List Int),
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= 20) ” &&
  “ ((Zlength (dp_l)) = ((i + 1) * 10)) ” &&
  “ (Forall (Eq ((0 : Int))) dp_l) ” &&
  “ (PowerTable power_l_2) ”
  &&  (intArray.seg dp_pre (0 : Int) ((i + 1) * 10) dp_l)
)

noncomputable def digits_sum_init_entail_wit_7 : Prop :=
  (
forall (power_pre : Int) (dp_pre : Int) (power_l_2 : (List Int)) (dp_l_2 : (List Int)) (i : Int) (PreH1 : (i >= 20)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (dp_l_2)) = (i * 10))) (PreH5 : (Forall (Eq ((0 : Int))) dp_l_2)) (PreH6 : (PowerTable power_l_2)) ,
  (intArray.seg dp_pre (0 : Int) (i * 10) dp_l_2)
  ** (intArray.undef_seg dp_pre (i * 10) 200)
  ** (intArray.full power_pre 20 power_l_2)
|--
  EX power_l : (List Int), EX dp_l : (List Int),
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 10) ” &&
  “ ((Zlength (dp_l)) = 200) ” &&
  “ (DigitDPBaseProgress dp_l (0 : Int)) ” &&
  “ (PowerTable power_l) ”
  &&  (intArray.full dp_pre 200 dp_l)
  ** (intArray.full power_pre 20 power_l)
) \/
(
forall (power_l_2 : (List Int)) (dp_l_2 : (List Int)) (i : Int) (PreH1 : (i >= 20)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (dp_l_2)) = (i * 10))) (PreH5 : (Forall (Eq ((0 : Int))) dp_l_2)) (PreH6 : (PowerTable power_l_2)) ,
  TT && emp 
|--
  “ (DigitDPBaseProgress dp_l_2 (0 : Int)) ”
  &&  emp
)

noncomputable def digits_sum_init_entail_wit_7_split_goal_1 : Prop :=
  forall (power_l_2 : (List Int)) (dp_l_2 : (List Int)) (i : Int) (PreH1 : (i >= 20)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (dp_l_2)) = (i * 10))) (PreH5 : (Forall (Eq ((0 : Int))) dp_l_2)) (PreH6 : (PowerTable power_l_2)) ,
  (DigitDPBaseProgress dp_l_2 (0 : Int))

noncomputable def digits_sum_init_entail_wit_8 : Prop :=
  (
forall (power_pre : Int) (dp_pre : Int) (power_l_2 : (List Int)) (dp_l_2 : (List Int)) (j : Int) (PreH1 : (j < 10)) (PreH2 : ((0 : Int) <= j)) (PreH3 : (j <= 10)) (PreH4 : ((Zlength (dp_l_2)) = 200)) (PreH5 : (DigitDPBaseProgress dp_l_2 j)) (PreH6 : (PowerTable power_l_2)) ,
  (intArray.full dp_pre 200 (replace_Znth ((10 + j)) (j) (dp_l_2)))
  ** (intArray.full power_pre 20 power_l_2)
|--
  EX power_l : (List Int), EX dp_l : (List Int),
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= 10) ” &&
  “ ((Zlength (dp_l)) = 200) ” &&
  “ (DigitDPBaseProgress dp_l (j + 1)) ” &&
  “ (PowerTable power_l) ”
  &&  (intArray.full dp_pre 200 dp_l)
  ** (intArray.full power_pre 20 power_l)
) \/
(
forall (power_l_2 : (List Int)) (dp_l_2 : (List Int)) (j : Int) (PreH1 : (j < 10)) (PreH2 : ((0 : Int) <= j)) (PreH3 : (j <= 10)) (PreH4 : ((Zlength (dp_l_2)) = 200)) (PreH5 : (DigitDPBaseProgress dp_l_2 j)) (PreH6 : (PowerTable power_l_2)) ,
  TT && emp 
|--
  “ (DigitDPBaseProgress (replace_Znth ((10 + j)) (j) (dp_l_2)) (j + 1)) ” &&
  “ ((Zlength ((replace_Znth ((10 + j)) (j) (dp_l_2)))) = 200) ”
  &&  emp
)

noncomputable def digits_sum_init_entail_wit_8_split_goal_1 : Prop :=
  forall (power_l_2 : (List Int)) (dp_l_2 : (List Int)) (j : Int) (PreH1 : (j < 10)) (PreH2 : ((0 : Int) <= j)) (PreH3 : (j <= 10)) (PreH4 : ((Zlength (dp_l_2)) = 200)) (PreH5 : (DigitDPBaseProgress dp_l_2 j)) (PreH6 : (PowerTable power_l_2)) ,
  (DigitDPBaseProgress (replace_Znth ((10 + j)) (j) (dp_l_2)) (j + 1))

noncomputable def digits_sum_init_entail_wit_8_split_goal_2 : Prop :=
  forall (power_l_2 : (List Int)) (dp_l_2 : (List Int)) (j : Int) (PreH1 : (j < 10)) (PreH2 : ((0 : Int) <= j)) (PreH3 : (j <= 10)) (PreH4 : ((Zlength (dp_l_2)) = 200)) (PreH5 : (DigitDPBaseProgress dp_l_2 j)) (PreH6 : (PowerTable power_l_2)) ,
  ((Zlength ((replace_Znth ((10 + j)) (j) (dp_l_2)))) = 200)

noncomputable def digits_sum_init_entail_wit_9 : Prop :=
  (
forall (power_pre : Int) (dp_pre : Int) (power_l_2 : (List Int)) (dp_l_2 : (List Int)) (j : Int) (PreH1 : (j >= 10)) (PreH2 : ((0 : Int) <= j)) (PreH3 : (j <= 10)) (PreH4 : ((Zlength (dp_l_2)) = 200)) (PreH5 : (DigitDPBaseProgress dp_l_2 j)) (PreH6 : (PowerTable power_l_2)) ,
  (intArray.full dp_pre 200 dp_l_2)
  ** (intArray.full power_pre 20 power_l_2)
|--
  EX power_l : (List Int), EX dp_l : (List Int),
  “ (2 <= 2) ” &&
  “ (2 <= 20) ” &&
  “ ((Zlength (dp_l)) = 200) ” &&
  “ (DigitDPOuterProgress dp_l 2) ” &&
  “ (PowerTable power_l) ”
  &&  (intArray.full dp_pre 200 dp_l)
  ** (intArray.full power_pre 20 power_l)
) \/
(
forall (power_l_2 : (List Int)) (dp_l_2 : (List Int)) (j : Int) (PreH1 : (j >= 10)) (PreH2 : ((0 : Int) <= j)) (PreH3 : (j <= 10)) (PreH4 : ((Zlength (dp_l_2)) = 200)) (PreH5 : (DigitDPBaseProgress dp_l_2 j)) (PreH6 : (PowerTable power_l_2)) ,
  TT && emp 
|--
  “ (DigitDPOuterProgress dp_l_2 2) ”
  &&  emp
)

noncomputable def digits_sum_init_entail_wit_9_split_goal_1 : Prop :=
  forall (power_l_2 : (List Int)) (dp_l_2 : (List Int)) (j : Int) (PreH1 : (j >= 10)) (PreH2 : ((0 : Int) <= j)) (PreH3 : (j <= 10)) (PreH4 : ((Zlength (dp_l_2)) = 200)) (PreH5 : (DigitDPBaseProgress dp_l_2 j)) (PreH6 : (PowerTable power_l_2)) ,
  (DigitDPOuterProgress dp_l_2 2)

noncomputable def digits_sum_init_entail_wit_10 : Prop :=
  (
forall (power_pre : Int) (dp_pre : Int) (power_l_2 : (List Int)) (dp_l_2 : (List Int)) (i : Int) (PreH1 : (i < 20)) (PreH2 : (2 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (dp_l_2)) = 200)) (PreH5 : (DigitDPOuterProgress dp_l_2 i)) (PreH6 : (PowerTable power_l_2)) ,
  (intArray.full dp_pre 200 dp_l_2)
  ** (intArray.full power_pre 20 power_l_2)
|--
  EX power_l : (List Int), EX dp_l : (List Int),
  “ (2 <= i) ” &&
  “ (i < 20) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 10) ” &&
  “ ((Zlength (dp_l)) = 200) ” &&
  “ (DigitDPRowProgress dp_l i (0 : Int)) ” &&
  “ (PowerTable power_l) ”
  &&  (intArray.full dp_pre 200 dp_l)
  ** (intArray.full power_pre 20 power_l)
) \/
(
forall (power_l_2 : (List Int)) (dp_l_2 : (List Int)) (i : Int) (PreH1 : (i < 20)) (PreH2 : (2 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (dp_l_2)) = 200)) (PreH5 : (DigitDPOuterProgress dp_l_2 i)) (PreH6 : (PowerTable power_l_2)) ,
  TT && emp 
|--
  “ (DigitDPRowProgress dp_l_2 i (0 : Int)) ”
  &&  emp
)

noncomputable def digits_sum_init_entail_wit_10_split_goal_1 : Prop :=
  forall (power_l_2 : (List Int)) (dp_l_2 : (List Int)) (i : Int) (PreH1 : (i < 20)) (PreH2 : (2 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (dp_l_2)) = 200)) (PreH5 : (DigitDPOuterProgress dp_l_2 i)) (PreH6 : (PowerTable power_l_2)) ,
  (DigitDPRowProgress dp_l_2 i (0 : Int))

noncomputable def digits_sum_init_entail_wit_11 : Prop :=
  (
forall (power_pre : Int) (dp_pre : Int) (power_l_2 : (List Int)) (dp_l_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j <= 10)) (PreH6 : ((Zlength (dp_l_2)) = 200)) (PreH7 : (DigitDPRowProgress dp_l_2 i j)) (PreH8 : (PowerTable power_l_2)) ,
  (intArray.full dp_pre 200 dp_l_2)
  ** (intArray.full power_pre 20 power_l_2)
|--
  EX power_l : (List Int), EX dp_l : (List Int),
  “ (2 <= i) ” &&
  “ (i < 20) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j < 10) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 10) ” &&
  “ ((Zlength (dp_l)) = 200) ” &&
  “ (DigitDPCellProgress dp_l i j (0 : Int)) ” &&
  “ (PowerTable power_l) ”
  &&  (intArray.full dp_pre 200 dp_l)
  ** (intArray.full power_pre 20 power_l)
) \/
(
forall (power_l_2 : (List Int)) (dp_l_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j <= 10)) (PreH6 : ((Zlength (dp_l_2)) = 200)) (PreH7 : (DigitDPRowProgress dp_l_2 i j)) (PreH8 : (PowerTable power_l_2)) ,
  TT && emp 
|--
  “ (DigitDPCellProgress dp_l_2 i j (0 : Int)) ”
  &&  emp
)

noncomputable def digits_sum_init_entail_wit_11_split_goal_1 : Prop :=
  forall (power_l_2 : (List Int)) (dp_l_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j <= 10)) (PreH6 : ((Zlength (dp_l_2)) = 200)) (PreH7 : (DigitDPRowProgress dp_l_2 i j)) (PreH8 : (PowerTable power_l_2)) ,
  (DigitDPCellProgress dp_l_2 i j (0 : Int))

noncomputable def digits_sum_init_entail_wit_12 : Prop :=
  (
forall (power_pre : Int) (dp_pre : Int) (power_l_2 : (List Int)) (dp_l_2 : (List Int)) (k : Int) (j : Int) (i : Int) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j < 10)) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l_2)) = 200)) (PreH9 : (DigitDPCellProgress dp_l_2 i j k)) (PreH10 : (PowerTable power_l_2)) ,
  (intArray.full dp_pre 200 (replace_Znth (((i * 10) + j)) ((signed_last_nbits ((Z.rem ((Znth ((i * 10) + j) dp_l_2 (0 : Int)) + (Z.rem ((Znth (((i - 1) * 10) + k) dp_l_2 (0 : Int)) + (Z.rem ((Znth (i - 2) power_l_2 (0 : Int)) * j) 1000000007)) 1000000007)) 1000000007)) (32))) (dp_l_2)))
  ** (intArray.full power_pre 20 power_l_2)
|--
  EX power_l : (List Int), EX dp_l : (List Int),
  “ (2 <= i) ” &&
  “ (i < 20) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j < 10) ” &&
  “ ((0 : Int) <= (k + 1)) ” &&
  “ ((k + 1) <= 10) ” &&
  “ ((Zlength (dp_l)) = 200) ” &&
  “ (DigitDPCellProgress dp_l i j (k + 1)) ” &&
  “ (PowerTable power_l) ”
  &&  (intArray.full dp_pre 200 dp_l)
  ** (intArray.full power_pre 20 power_l)
) \/
(
forall (power_l_2 : (List Int)) (dp_l_2 : (List Int)) (k : Int) (j : Int) (i : Int) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j < 10)) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l_2)) = 200)) (PreH9 : (DigitDPCellProgress dp_l_2 i j k)) (PreH10 : (PowerTable power_l_2)) ,
  TT && emp 
|--
  “ (DigitDPCellProgress (replace_Znth (((i * 10) + j)) ((signed_last_nbits ((Z.rem ((Znth ((i * 10) + j) dp_l_2 (0 : Int)) + (Z.rem ((Znth (((i - 1) * 10) + k) dp_l_2 (0 : Int)) + (Z.rem ((Znth (i - 2) power_l_2 (0 : Int)) * j) 1000000007)) 1000000007)) 1000000007)) (32))) (dp_l_2)) i j (k + 1)) ” &&
  “ ((Zlength ((replace_Znth (((i * 10) + j)) ((signed_last_nbits ((Z.rem ((Znth ((i * 10) + j) dp_l_2 (0 : Int)) + (Z.rem ((Znth (((i - 1) * 10) + k) dp_l_2 (0 : Int)) + (Z.rem ((Znth (i - 2) power_l_2 (0 : Int)) * j) 1000000007)) 1000000007)) 1000000007)) (32))) (dp_l_2)))) = 200) ”
  &&  emp
)

noncomputable def digits_sum_init_entail_wit_12_split_goal_1 : Prop :=
  forall (power_l_2 : (List Int)) (dp_l_2 : (List Int)) (k : Int) (j : Int) (i : Int) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j < 10)) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l_2)) = 200)) (PreH9 : (DigitDPCellProgress dp_l_2 i j k)) (PreH10 : (PowerTable power_l_2)) ,
  (DigitDPCellProgress (replace_Znth (((i * 10) + j)) ((signed_last_nbits ((Z.rem ((Znth ((i * 10) + j) dp_l_2 (0 : Int)) + (Z.rem ((Znth (((i - 1) * 10) + k) dp_l_2 (0 : Int)) + (Z.rem ((Znth (i - 2) power_l_2 (0 : Int)) * j) 1000000007)) 1000000007)) 1000000007)) (32))) (dp_l_2)) i j (k + 1))

noncomputable def digits_sum_init_entail_wit_12_split_goal_2 : Prop :=
  forall (power_l_2 : (List Int)) (dp_l_2 : (List Int)) (k : Int) (j : Int) (i : Int) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j < 10)) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l_2)) = 200)) (PreH9 : (DigitDPCellProgress dp_l_2 i j k)) (PreH10 : (PowerTable power_l_2)) ,
  ((Zlength ((replace_Znth (((i * 10) + j)) ((signed_last_nbits ((Z.rem ((Znth ((i * 10) + j) dp_l_2 (0 : Int)) + (Z.rem ((Znth (((i - 1) * 10) + k) dp_l_2 (0 : Int)) + (Z.rem ((Znth (i - 2) power_l_2 (0 : Int)) * j) 1000000007)) 1000000007)) 1000000007)) (32))) (dp_l_2)))) = 200)

noncomputable def digits_sum_init_entail_wit_13 : Prop :=
  (
forall (power_pre : Int) (dp_pre : Int) (power_l_2 : (List Int)) (dp_l_2 : (List Int)) (k : Int) (j : Int) (i : Int) (PreH1 : (k >= 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j < 10)) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l_2)) = 200)) (PreH9 : (DigitDPCellProgress dp_l_2 i j k)) (PreH10 : (PowerTable power_l_2)) ,
  (intArray.full dp_pre 200 dp_l_2)
  ** (intArray.full power_pre 20 power_l_2)
|--
  EX power_l : (List Int), EX dp_l : (List Int),
  “ (2 <= i) ” &&
  “ (i < 20) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= 10) ” &&
  “ ((Zlength (dp_l)) = 200) ” &&
  “ (DigitDPRowProgress dp_l i (j + 1)) ” &&
  “ (PowerTable power_l) ”
  &&  (intArray.full dp_pre 200 dp_l)
  ** (intArray.full power_pre 20 power_l)
) \/
(
forall (power_l_2 : (List Int)) (dp_l_2 : (List Int)) (k : Int) (j : Int) (i : Int) (PreH1 : (k >= 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j < 10)) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l_2)) = 200)) (PreH9 : (DigitDPCellProgress dp_l_2 i j k)) (PreH10 : (PowerTable power_l_2)) ,
  TT && emp 
|--
  “ (DigitDPRowProgress dp_l_2 i (j + 1)) ”
  &&  emp
)

noncomputable def digits_sum_init_entail_wit_13_split_goal_1 : Prop :=
  forall (power_l_2 : (List Int)) (dp_l_2 : (List Int)) (k : Int) (j : Int) (i : Int) (PreH1 : (k >= 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j < 10)) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l_2)) = 200)) (PreH9 : (DigitDPCellProgress dp_l_2 i j k)) (PreH10 : (PowerTable power_l_2)) ,
  (DigitDPRowProgress dp_l_2 i (j + 1))

noncomputable def digits_sum_init_entail_wit_14 : Prop :=
  (
forall (power_pre : Int) (dp_pre : Int) (power_l_2 : (List Int)) (dp_l_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j >= 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j <= 10)) (PreH6 : ((Zlength (dp_l_2)) = 200)) (PreH7 : (DigitDPRowProgress dp_l_2 i j)) (PreH8 : (PowerTable power_l_2)) ,
  (intArray.full dp_pre 200 dp_l_2)
  ** (intArray.full power_pre 20 power_l_2)
|--
  EX power_l : (List Int), EX dp_l : (List Int),
  “ (2 <= (i + 1)) ” &&
  “ ((i + 1) <= 20) ” &&
  “ ((Zlength (dp_l)) = 200) ” &&
  “ (DigitDPOuterProgress dp_l (i + 1)) ” &&
  “ (PowerTable power_l) ”
  &&  (intArray.full dp_pre 200 dp_l)
  ** (intArray.full power_pre 20 power_l)
) \/
(
forall (power_l_2 : (List Int)) (dp_l_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j >= 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j <= 10)) (PreH6 : ((Zlength (dp_l_2)) = 200)) (PreH7 : (DigitDPRowProgress dp_l_2 i j)) (PreH8 : (PowerTable power_l_2)) ,
  TT && emp 
|--
  “ (DigitDPOuterProgress dp_l_2 (i + 1)) ”
  &&  emp
)

noncomputable def digits_sum_init_entail_wit_14_split_goal_1 : Prop :=
  forall (power_l_2 : (List Int)) (dp_l_2 : (List Int)) (j : Int) (i : Int) (PreH1 : (j >= 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j <= 10)) (PreH6 : ((Zlength (dp_l_2)) = 200)) (PreH7 : (DigitDPRowProgress dp_l_2 i j)) (PreH8 : (PowerTable power_l_2)) ,
  (DigitDPOuterProgress dp_l_2 (i + 1))

noncomputable def digits_sum_init_return_wit_1 : Prop :=
  (
forall (power_pre : Int) (dp_pre : Int) (power_l_2 : (List Int)) (dp_l_2 : (List Int)) (i : Int) (PreH1 : (i >= 20)) (PreH2 : (2 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (dp_l_2)) = 200)) (PreH5 : (DigitDPOuterProgress dp_l_2 i)) (PreH6 : (PowerTable power_l_2)) ,
  (intArray.full dp_pre 200 dp_l_2)
  ** (intArray.full power_pre 20 power_l_2)
|--
  EX power_l : (List Int), EX dp_l : (List Int),
  “ (DigitDPTable dp_l) ” &&
  “ (PowerTable power_l) ”
  &&  (intArray.full dp_pre 200 dp_l)
  ** (intArray.full power_pre 20 power_l)
) \/
(
forall (power_l_2 : (List Int)) (dp_l_2 : (List Int)) (i : Int) (PreH1 : (i >= 20)) (PreH2 : (2 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (dp_l_2)) = 200)) (PreH5 : (DigitDPOuterProgress dp_l_2 i)) (PreH6 : (PowerTable power_l_2)) ,
  TT && emp 
|--
  “ (DigitDPTable dp_l_2) ”
  &&  emp
)

noncomputable def digits_sum_init_return_wit_1_split_goal_1 : Prop :=
  forall (power_l_2 : (List Int)) (dp_l_2 : (List Int)) (i : Int) (PreH1 : (i >= 20)) (PreH2 : (2 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (dp_l_2)) = 200)) (PreH5 : (DigitDPOuterProgress dp_l_2 i)) (PreH6 : (PowerTable power_l_2)) ,
  (DigitDPTable dp_l_2)

noncomputable def digits_sum_init_partial_solve_wit_1 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) ,
  (intArray.undef_full dp_pre 200)
  ** (intArray.undef_full power_pre 20)
|--
  (((power_pre + ((0 : Int) * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg power_pre 1 20)
  ** (intArray.undef_full dp_pre 200)

noncomputable def digits_sum_init_partial_solve_wit_2 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (i : Int) (PreH1 : (i < 20)) (PreH2 : (1 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (power_l)) = i)) (PreH5 : (PowerPrefix power_l i)) ,
  (intArray.undef_full dp_pre 200)
  ** (intArray.seg power_pre (0 : Int) i power_l)
  ** (intArray.undef_seg power_pre i 20)
|--
  “ (i < 20) ” &&
  “ (1 <= i) ” &&
  “ (i <= 20) ” &&
  “ ((Zlength (power_l)) = i) ” &&
  “ (PowerPrefix power_l i) ”
  &&  (((power_pre + ((i - 1) * sizeof(INT)))) # Int |-> ((Znth ((i - 1) - (0 : Int)) power_l (0 : Int))))
  ** (intArray.missing_i power_pre (i - 1) (0 : Int) i power_l)
  ** (intArray.undef_full dp_pre 200)
  ** (intArray.undef_seg power_pre i 20)

noncomputable def digits_sum_init_partial_solve_wit_3 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (i : Int) (PreH1 : (i < 20)) (PreH2 : (1 <= i)) (PreH3 : (i <= 20)) (PreH4 : ((Zlength (power_l)) = i)) (PreH5 : (PowerPrefix power_l i)) ,
  (intArray.seg power_pre (0 : Int) i power_l)
  ** (intArray.undef_full dp_pre 200)
  ** (intArray.undef_seg power_pre i 20)
|--
  “ (i < 20) ” &&
  “ (1 <= i) ” &&
  “ (i <= 20) ” &&
  “ ((Zlength (power_l)) = i) ” &&
  “ (PowerPrefix power_l i) ”
  &&  (((power_pre + (i * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg power_pre (i + 1) 20)
  ** (intArray.seg power_pre (0 : Int) i power_l)
  ** (intArray.undef_full dp_pre 200)

noncomputable def digits_sum_init_partial_solve_wit_4 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (j : Int) (i : Int) (PreH1 : (j < 10)) (PreH2 : ((0 : Int) <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j <= 10)) (PreH6 : ((Zlength (dp_l)) = ((i * 10) + j))) (PreH7 : (Forall (Eq ((0 : Int))) dp_l)) (PreH8 : (PowerTable power_l)) ,
  (intArray.seg dp_pre (0 : Int) ((i * 10) + j) dp_l)
  ** (intArray.undef_seg dp_pre ((i * 10) + j) 200)
  ** (intArray.full power_pre 20 power_l)
|--
  “ (j < 10) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i < 20) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= 10) ” &&
  “ ((Zlength (dp_l)) = ((i * 10) + j)) ” &&
  “ (Forall (Eq ((0 : Int))) dp_l) ” &&
  “ (PowerTable power_l) ”
  &&  (((dp_pre + (((i * 10) + j) * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg dp_pre (((i * 10) + j) + 1) 200)
  ** (intArray.seg dp_pre (0 : Int) ((i * 10) + j) dp_l)
  ** (intArray.full power_pre 20 power_l)

noncomputable def digits_sum_init_partial_solve_wit_5 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (j : Int) (PreH1 : (j < 10)) (PreH2 : ((0 : Int) <= j)) (PreH3 : (j <= 10)) (PreH4 : ((Zlength (dp_l)) = 200)) (PreH5 : (DigitDPBaseProgress dp_l j)) (PreH6 : (PowerTable power_l)) ,
  (intArray.full dp_pre 200 dp_l)
  ** (intArray.full power_pre 20 power_l)
|--
  “ (j < 10) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= 10) ” &&
  “ ((Zlength (dp_l)) = 200) ” &&
  “ (DigitDPBaseProgress dp_l j) ” &&
  “ (PowerTable power_l) ”
  &&  (((dp_pre + ((10 + j) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i dp_pre (10 + j) (0 : Int) 200 dp_l)
  ** (intArray.full power_pre 20 power_l)

noncomputable def digits_sum_init_partial_solve_wit_6 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (k : Int) (j : Int) (i : Int) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j < 10)) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k)) (PreH10 : (PowerTable power_l)) ,
  (intArray.full dp_pre 200 dp_l)
  ** (intArray.full power_pre 20 power_l)
|--
  “ (k < 10) ” &&
  “ (2 <= i) ” &&
  “ (i < 20) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j < 10) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= 10) ” &&
  “ ((Zlength (dp_l)) = 200) ” &&
  “ (DigitDPCellProgress dp_l i j k) ” &&
  “ (PowerTable power_l) ”
  &&  (((power_pre + ((i - 2) * sizeof(INT)))) # Int |-> ((Znth (i - 2) power_l (0 : Int))))
  ** (intArray.missing_i power_pre (i - 2) (0 : Int) 20 power_l)
  ** (intArray.full dp_pre 200 dp_l)

noncomputable def digits_sum_init_partial_solve_wit_7 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (k : Int) (j : Int) (i : Int) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j < 10)) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k)) (PreH10 : (PowerTable power_l)) ,
  (intArray.full power_pre 20 power_l)
  ** (intArray.full dp_pre 200 dp_l)
|--
  “ (k < 10) ” &&
  “ (2 <= i) ” &&
  “ (i < 20) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j < 10) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= 10) ” &&
  “ ((Zlength (dp_l)) = 200) ” &&
  “ (DigitDPCellProgress dp_l i j k) ” &&
  “ (PowerTable power_l) ”
  &&  (((dp_pre + ((((i - 1) * 10) + k) * sizeof(INT)))) # Int |-> ((Znth (((i - 1) * 10) + k) dp_l (0 : Int))))
  ** (intArray.missing_i dp_pre (((i - 1) * 10) + k) (0 : Int) 200 dp_l)
  ** (intArray.full power_pre 20 power_l)

noncomputable def digits_sum_init_partial_solve_wit_8 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (k : Int) (j : Int) (i : Int) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j < 10)) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k)) (PreH10 : (PowerTable power_l)) ,
  (intArray.full dp_pre 200 dp_l)
  ** (intArray.full power_pre 20 power_l)
|--
  “ (k < 10) ” &&
  “ (2 <= i) ” &&
  “ (i < 20) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j < 10) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= 10) ” &&
  “ ((Zlength (dp_l)) = 200) ” &&
  “ (DigitDPCellProgress dp_l i j k) ” &&
  “ (PowerTable power_l) ”
  &&  (((dp_pre + (((i * 10) + j) * sizeof(INT)))) # Int |-> ((Znth ((i * 10) + j) dp_l (0 : Int))))
  ** (intArray.missing_i dp_pre ((i * 10) + j) (0 : Int) 200 dp_l)
  ** (intArray.full power_pre 20 power_l)

noncomputable def digits_sum_init_partial_solve_wit_9 : Prop :=
  forall (power_pre : Int) (dp_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (k : Int) (j : Int) (i : Int) (PreH1 : (k < 10)) (PreH2 : (2 <= i)) (PreH3 : (i < 20)) (PreH4 : ((0 : Int) <= j)) (PreH5 : (j < 10)) (PreH6 : ((0 : Int) <= k)) (PreH7 : (k <= 10)) (PreH8 : ((Zlength (dp_l)) = 200)) (PreH9 : (DigitDPCellProgress dp_l i j k)) (PreH10 : (PowerTable power_l)) ,
  (intArray.full dp_pre 200 dp_l)
  ** (intArray.full power_pre 20 power_l)
|--
  “ (k < 10) ” &&
  “ (2 <= i) ” &&
  “ (i < 20) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j < 10) ” &&
  “ ((0 : Int) <= k) ” &&
  “ (k <= 10) ” &&
  “ ((Zlength (dp_l)) = 200) ” &&
  “ (DigitDPCellProgress dp_l i j k) ” &&
  “ (PowerTable power_l) ”
  &&  (((dp_pre + (((i * 10) + j) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i dp_pre ((i * 10) + j) (0 : Int) 200 dp_l)
  ** (intArray.full power_pre 20 power_l)

noncomputable def prefix_digits_sum_safety_wit_1 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (PreH1 : ((0 : Int) <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (DigitDPTable dp_l)) ,
  ((( &( "m" ) )) # Int |->_)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** (intArray.full dp_pre 200 dp_l)
  ** (intArray.undef_full digits_pre 20)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def prefix_digits_sum_safety_wit_2 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (PreH1 : ((0 : Int) <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (DigitDPTable dp_l)) ,
  ((( &( "ans" ) )) # Int |->_)
  ** ((( &( "m" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** (intArray.full dp_pre 200 dp_l)
  ** (intArray.undef_full digits_pre 20)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def prefix_digits_sum_safety_wit_3 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (PreH1 : ((0 : Int) <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (DigitDPTable dp_l)) ,
  ((( &( "power_ll" ) )) # Int64 |->_)
  ** ((( &( "ans" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "m" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** (intArray.full dp_pre 200 dp_l)
  ** (intArray.undef_full digits_pre 20)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def prefix_digits_sum_safety_wit_4 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (PreH1 : ((0 : Int) <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (DigitDPTable dp_l)) ,
  ((( &( "power_ll" ) )) # Int64 |-> (1))
  ** ((( &( "ans" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "m" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** (intArray.full dp_pre 200 dp_l)
  ** (intArray.undef_full digits_pre 20)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def prefix_digits_sum_safety_wit_5 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (PreH1 : (x_pre < 1)) (PreH2 : ((0 : Int) <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (DigitDPTable dp_l)) ,
  ((( &( "power_ll" ) )) # Int64 |-> (1))
  ** ((( &( "ans" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "m" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** (intArray.full dp_pre 200 dp_l)
  ** (intArray.undef_full digits_pre 20)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def prefix_digits_sum_safety_wit_6 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (PreH1 : (x_pre >= 1)) (PreH2 : ((0 : Int) <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (DigitDPTable dp_l)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "power_ll" ) )) # Int64 |-> (1))
  ** ((( &( "ans" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "m" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** (intArray.full dp_pre 200 dp_l)
  ** (intArray.undef_full digits_pre 20)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def prefix_digits_sum_safety_wit_7 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (digits_l : (List Int)) (i : Int) (power_ll : Int) (ans : Int) (m : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (m = (0 : Int))) (PreH4 : (ans = (0 : Int))) (PreH5 : (power_ll = 1)) (PreH6 : ((0 : Int) <= i)) (PreH7 : (i <= 20)) (PreH8 : ((Zlength (digits_l)) = i)) (PreH9 : (Forall (Eq ((0 : Int))) digits_l)) (PreH10 : (DigitDPTable dp_l)) ,
  ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full dp_pre 200 dp_l)
  ** (intArray.seg digits_pre (0 : Int) i digits_l)
  ** (intArray.undef_seg digits_pre i 20)
|--
  “ (20 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 20) ”

noncomputable def prefix_digits_sum_safety_wit_8 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (digits_l : (List Int)) (i : Int) (power_ll : Int) (ans : Int) (m : Int) (PreH1 : (i < 20)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (m = (0 : Int))) (PreH5 : (ans = (0 : Int))) (PreH6 : (power_ll = 1)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= 20)) (PreH9 : ((Zlength (digits_l)) = i)) (PreH10 : (Forall (Eq ((0 : Int))) digits_l)) (PreH11 : (DigitDPTable dp_l)) ,
  ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full dp_pre 200 dp_l)
  ** (intArray.seg digits_pre (0 : Int) i digits_l)
  ** (intArray.undef_seg digits_pre i 20)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def prefix_digits_sum_safety_wit_9 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (digits_l : (List Int)) (i : Int) (power_ll : Int) (ans : Int) (m : Int) (PreH1 : (i < 20)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (m = (0 : Int))) (PreH5 : (ans = (0 : Int))) (PreH6 : (power_ll = 1)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= 20)) (PreH9 : ((Zlength (digits_l)) = i)) (PreH10 : (Forall (Eq ((0 : Int))) digits_l)) (PreH11 : (DigitDPTable dp_l)) ,
  (intArray.seg digits_pre (0 : Int) (i + 1) (digits_l ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg digits_pre (i + 1) 20)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.full dp_pre 200 dp_l)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def prefix_digits_sum_safety_wit_10 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (digits_l : (List Int)) (tmpx : Int) (m : Int) (power_ll : Int) (ans : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (ans = (0 : Int))) (PreH4 : (power_ll = 1)) (PreH5 : ((0 : Int) <= m)) (PreH6 : (m <= 19)) (PreH7 : (tmpx >= (0 : Int))) (PreH8 : ((tmpx ≠ (0 : Int)) -> (m < 19))) (PreH9 : ((tmpx = (0 : Int)) -> (1 <= m))) (PreH10 : ((tmpx = (0 : Int)) -> (ExtractedDigitCount x_pre m))) (PreH11 : ((Zlength (digits_l)) = 20)) (PreH12 : (ExtractedDigitBuffer x_pre digits_l m tmpx)) (PreH13 : (DigitDPTable dp_l)) (PreH14 : (tmpx ≠ (0 : Int))) ,
  ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** (intArray.full dp_pre 200 dp_l)
  ** (intArray.full digits_pre 20 digits_l)
|--
  “ ((m + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (m + 1)) ”

noncomputable def prefix_digits_sum_safety_wit_11 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (digits_l : (List Int)) (tmpx : Int) (m : Int) (power_ll : Int) (ans : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (ans = (0 : Int))) (PreH4 : (power_ll = 1)) (PreH5 : ((0 : Int) <= m)) (PreH6 : (m <= 19)) (PreH7 : (tmpx >= (0 : Int))) (PreH8 : ((tmpx ≠ (0 : Int)) -> (m < 19))) (PreH9 : ((tmpx = (0 : Int)) -> (1 <= m))) (PreH10 : ((tmpx = (0 : Int)) -> (ExtractedDigitCount x_pre m))) (PreH11 : ((Zlength (digits_l)) = 20)) (PreH12 : (ExtractedDigitBuffer x_pre digits_l m tmpx)) (PreH13 : (DigitDPTable dp_l)) (PreH14 : (tmpx ≠ (0 : Int))) ,
  ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** (intArray.full dp_pre 200 dp_l)
  ** (intArray.full digits_pre 20 digits_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def prefix_digits_sum_safety_wit_12 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (digits_l : (List Int)) (tmpx : Int) (m : Int) (power_ll : Int) (ans : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (ans = (0 : Int))) (PreH4 : (power_ll = 1)) (PreH5 : ((0 : Int) <= m)) (PreH6 : (m <= 19)) (PreH7 : (tmpx >= (0 : Int))) (PreH8 : ((tmpx ≠ (0 : Int)) -> (m < 19))) (PreH9 : ((tmpx = (0 : Int)) -> (1 <= m))) (PreH10 : ((tmpx = (0 : Int)) -> (ExtractedDigitCount x_pre m))) (PreH11 : ((Zlength (digits_l)) = 20)) (PreH12 : (ExtractedDigitBuffer x_pre digits_l m tmpx)) (PreH13 : (DigitDPTable dp_l)) (PreH14 : (tmpx ≠ (0 : Int))) ,
  ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** ((( &( "m" ) )) # Int |-> ((m + 1)))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** (intArray.full dp_pre 200 dp_l)
  ** (intArray.full digits_pre 20 digits_l)
|--
  “ ((tmpx ≠ (-9223372036854775808)) ∨ (10 ≠ (-1))) ” &&
  “ (10 ≠ (0 : Int)) ”

noncomputable def prefix_digits_sum_safety_wit_13 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (digits_l : (List Int)) (tmpx : Int) (m : Int) (power_ll : Int) (ans : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (ans = (0 : Int))) (PreH4 : (power_ll = 1)) (PreH5 : ((0 : Int) <= m)) (PreH6 : (m <= 19)) (PreH7 : (tmpx >= (0 : Int))) (PreH8 : ((tmpx ≠ (0 : Int)) -> (m < 19))) (PreH9 : ((tmpx = (0 : Int)) -> (1 <= m))) (PreH10 : ((tmpx = (0 : Int)) -> (ExtractedDigitCount x_pre m))) (PreH11 : ((Zlength (digits_l)) = 20)) (PreH12 : (ExtractedDigitBuffer x_pre digits_l m tmpx)) (PreH13 : (DigitDPTable dp_l)) (PreH14 : (tmpx ≠ (0 : Int))) ,
  ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** ((( &( "m" ) )) # Int |-> ((m + 1)))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** (intArray.full dp_pre 200 dp_l)
  ** (intArray.full digits_pre 20 digits_l)
|--
  “ (10 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 10) ”

noncomputable def prefix_digits_sum_safety_wit_14 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (digits_l : (List Int)) (tmpx : Int) (m : Int) (power_ll : Int) (ans : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (ans = (0 : Int))) (PreH4 : (power_ll = 1)) (PreH5 : ((0 : Int) <= m)) (PreH6 : (m <= 19)) (PreH7 : (tmpx >= (0 : Int))) (PreH8 : ((tmpx ≠ (0 : Int)) -> (m < 19))) (PreH9 : ((tmpx = (0 : Int)) -> (1 <= m))) (PreH10 : ((tmpx = (0 : Int)) -> (ExtractedDigitCount x_pre m))) (PreH11 : ((Zlength (digits_l)) = 20)) (PreH12 : (ExtractedDigitBuffer x_pre digits_l m tmpx)) (PreH13 : (DigitDPTable dp_l)) (PreH14 : (tmpx ≠ (0 : Int))) ,
  (intArray.full digits_pre 20 (replace_Znth ((m + 1)) ((signed_last_nbits ((Z.rem tmpx 10)) (32))) (digits_l)))
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** ((( &( "m" ) )) # Int |-> ((m + 1)))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** (intArray.full dp_pre 200 dp_l)
|--
  “ ((tmpx ≠ (-9223372036854775808)) ∨ (10 ≠ (-1))) ” &&
  “ (10 ≠ (0 : Int)) ”

noncomputable def prefix_digits_sum_safety_wit_15 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (digits_l : (List Int)) (tmpx : Int) (m : Int) (power_ll : Int) (ans : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (ans = (0 : Int))) (PreH4 : (power_ll = 1)) (PreH5 : ((0 : Int) <= m)) (PreH6 : (m <= 19)) (PreH7 : (tmpx >= (0 : Int))) (PreH8 : ((tmpx ≠ (0 : Int)) -> (m < 19))) (PreH9 : ((tmpx = (0 : Int)) -> (1 <= m))) (PreH10 : ((tmpx = (0 : Int)) -> (ExtractedDigitCount x_pre m))) (PreH11 : ((Zlength (digits_l)) = 20)) (PreH12 : (ExtractedDigitBuffer x_pre digits_l m tmpx)) (PreH13 : (DigitDPTable dp_l)) (PreH14 : (tmpx ≠ (0 : Int))) ,
  (intArray.full digits_pre 20 (replace_Znth ((m + 1)) ((signed_last_nbits ((Z.rem tmpx 10)) (32))) (digits_l)))
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** ((( &( "m" ) )) # Int |-> ((m + 1)))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** (intArray.full dp_pre 200 dp_l)
|--
  “ (10 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 10) ”

noncomputable def prefix_digits_sum_safety_wit_16 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (digits_l : (List Int)) (tmpx : Int) (m : Int) (power_ll : Int) (ans : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (ans = (0 : Int))) (PreH4 : (power_ll = 1)) (PreH5 : ((0 : Int) <= m)) (PreH6 : (m <= 19)) (PreH7 : (tmpx >= (0 : Int))) (PreH8 : ((tmpx ≠ (0 : Int)) -> (m < 19))) (PreH9 : ((tmpx = (0 : Int)) -> (1 <= m))) (PreH10 : ((tmpx = (0 : Int)) -> (ExtractedDigitCount x_pre m))) (PreH11 : ((Zlength (digits_l)) = 20)) (PreH12 : (ExtractedDigitBuffer x_pre digits_l m tmpx)) (PreH13 : (DigitDPTable dp_l)) (PreH14 : (tmpx = (0 : Int))) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** (intArray.full dp_pre 200 dp_l)
  ** (intArray.full digits_pre 20 digits_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def prefix_digits_sum_safety_wit_17 : Prop :=
  (
forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (ans : Int) (PreH1 : (i < m)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (ans = (0 : Int))) (PreH5 : (tmpx = (0 : Int))) (PreH6 : (1 <= i)) (PreH7 : (i <= m)) (PreH8 : (m <= 19)) (PreH9 : ((Zlength (digits_l)) = 20)) (PreH10 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH11 : (ExtractedDigitCount x_pre m)) (PreH12 : (DigitPositionPower i power_ll)) (PreH13 : (AccumulatedDigitSumCorrect x_pre m ans)) (PreH14 : (DigitDPTable dp_l)) ,
  ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** (intArray.full dp_pre 200 dp_l)
  ** (intArray.full digits_pre 20 digits_l)
|--
  “ ((power_ll * 10) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (power_ll * 10)) ”
) \/
(
forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (ans : Int) (PreH1 : (i < m)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (ans = (0 : Int))) (PreH5 : (tmpx = (0 : Int))) (PreH6 : (1 <= i)) (PreH7 : (i <= m)) (PreH8 : (m <= 19)) (PreH9 : ((Zlength (digits_l)) = 20)) (PreH10 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH11 : (ExtractedDigitCount x_pre m)) (PreH12 : (DigitPositionPower i power_ll)) (PreH13 : (AccumulatedDigitSumCorrect x_pre m ans)) (PreH14 : (DigitDPTable dp_l)) ,
  ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** (intArray.full dp_pre 200 dp_l)
  ** (intArray.full digits_pre 20 digits_l)
|--
  “ ((power_ll * 10) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (power_ll * 10)) ”
)

noncomputable def prefix_digits_sum_safety_wit_17_split_goal_1 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (ans : Int) (PreH1 : (i < m)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (ans = (0 : Int))) (PreH5 : (tmpx = (0 : Int))) (PreH6 : (1 <= i)) (PreH7 : (i <= m)) (PreH8 : (m <= 19)) (PreH9 : ((Zlength (digits_l)) = 20)) (PreH10 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH11 : (ExtractedDigitCount x_pre m)) (PreH12 : (DigitPositionPower i power_ll)) (PreH13 : (AccumulatedDigitSumCorrect x_pre m ans)) (PreH14 : (DigitDPTable dp_l)) ,
  ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** (intArray.full dp_pre 200 dp_l)
  ** (intArray.full digits_pre 20 digits_l)
|--
  “ ((power_ll * 10) <= 9223372036854775807) ”

noncomputable def prefix_digits_sum_safety_wit_17_split_goal_2 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (ans : Int) (PreH1 : (i < m)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (ans = (0 : Int))) (PreH5 : (tmpx = (0 : Int))) (PreH6 : (1 <= i)) (PreH7 : (i <= m)) (PreH8 : (m <= 19)) (PreH9 : ((Zlength (digits_l)) = 20)) (PreH10 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH11 : (ExtractedDigitCount x_pre m)) (PreH12 : (DigitPositionPower i power_ll)) (PreH13 : (AccumulatedDigitSumCorrect x_pre m ans)) (PreH14 : (DigitDPTable dp_l)) ,
  ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** (intArray.full dp_pre 200 dp_l)
  ** (intArray.full digits_pre 20 digits_l)
|--
  “ ((-9223372036854775808) <= (power_ll * 10)) ”

noncomputable def prefix_digits_sum_safety_wit_18 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (ans : Int) (PreH1 : (i < m)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (ans = (0 : Int))) (PreH5 : (tmpx = (0 : Int))) (PreH6 : (1 <= i)) (PreH7 : (i <= m)) (PreH8 : (m <= 19)) (PreH9 : ((Zlength (digits_l)) = 20)) (PreH10 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH11 : (ExtractedDigitCount x_pre m)) (PreH12 : (DigitPositionPower i power_ll)) (PreH13 : (AccumulatedDigitSumCorrect x_pre m ans)) (PreH14 : (DigitDPTable dp_l)) ,
  ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** (intArray.full dp_pre 200 dp_l)
  ** (intArray.full digits_pre 20 digits_l)
|--
  “ (10 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 10) ”

noncomputable def prefix_digits_sum_safety_wit_19 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (ans : Int) (PreH1 : (i < m)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (ans = (0 : Int))) (PreH5 : (tmpx = (0 : Int))) (PreH6 : (1 <= i)) (PreH7 : (i <= m)) (PreH8 : (m <= 19)) (PreH9 : ((Zlength (digits_l)) = 20)) (PreH10 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH11 : (ExtractedDigitCount x_pre m)) (PreH12 : (DigitPositionPower i power_ll)) (PreH13 : (AccumulatedDigitSumCorrect x_pre m ans)) (PreH14 : (DigitDPTable dp_l)) ,
  ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "power_ll" ) )) # Int64 |-> ((power_ll * 10)))
  ** (intArray.full dp_pre 200 dp_l)
  ** (intArray.full digits_pre 20 digits_l)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def prefix_digits_sum_safety_wit_20 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (digits_l : (List Int)) (ans : Int) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (tmpx = (0 : Int))) (PreH4 : ((0 : Int) <= i)) (PreH5 : (i <= m)) (PreH6 : (m <= 19)) (PreH7 : ((0 : Int) <= ans)) (PreH8 : (ans < 1000000007)) (PreH9 : ((Zlength (digits_l)) = 20)) (PreH10 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH11 : (ExtractedDigitCount x_pre m)) (PreH12 : (AccumulatedDigitSumCorrect x_pre i ans)) (PreH13 : (OuterDigitPositionPower i power_ll)) (PreH14 : (DigitDPTable dp_l)) ,
  ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** (intArray.full dp_pre 200 dp_l)
  ** (intArray.full digits_pre 20 digits_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def prefix_digits_sum_safety_wit_21 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (digits_l : (List Int)) (ans : Int) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (i > (0 : Int))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= ans)) (PreH9 : (ans < 1000000007)) (PreH10 : ((Zlength (digits_l)) = 20)) (PreH11 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH12 : (ExtractedDigitCount x_pre m)) (PreH13 : (AccumulatedDigitSumCorrect x_pre i ans)) (PreH14 : (OuterDigitPositionPower i power_ll)) (PreH15 : (DigitDPTable dp_l)) ,
  ((( &( "j" ) )) # Int |->_)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** (intArray.full dp_pre 200 dp_l)
  ** (intArray.full digits_pre 20 digits_l)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def prefix_digits_sum_safety_wit_22 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j < (Znth i digits_l (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int)))) (PreH9 : ((Znth i digits_l (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  (intArray.full dp_pre 200 dp_l)
  ** (intArray.full digits_pre 20 digits_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
|--
  “ (((ans + (Znth ((i * 10) + j) dp_l (0 : Int))) ≠ (INT_MIN)) ∨ (1000000007 ≠ (-1))) ” &&
  “ (1000000007 ≠ (0 : Int)) ”

noncomputable def prefix_digits_sum_safety_wit_23 : Prop :=
  (
forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j < (Znth i digits_l (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int)))) (PreH9 : ((Znth i digits_l (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  (intArray.full dp_pre 200 dp_l)
  ** (intArray.full digits_pre 20 digits_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
|--
  “ ((ans + (Znth ((i * 10) + j) dp_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (ans + (Znth ((i * 10) + j) dp_l (0 : Int)))) ”
) \/
(
forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j < (Znth i digits_l (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int)))) (PreH9 : ((Znth i digits_l (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  (intArray.full dp_pre 200 dp_l)
  ** (intArray.full digits_pre 20 digits_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
|--
  “ ((ans + (Znth ((i * 10) + j) dp_l (0 : Int))) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (ans + (Znth ((i * 10) + j) dp_l (0 : Int)))) ”
)

noncomputable def prefix_digits_sum_safety_wit_23_split_goal_1 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j < (Znth i digits_l (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int)))) (PreH9 : ((Znth i digits_l (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  (intArray.full dp_pre 200 dp_l)
  ** (intArray.full digits_pre 20 digits_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
|--
  “ ((ans + (Znth ((i * 10) + j) dp_l (0 : Int))) <= INT_MAX) ”

noncomputable def prefix_digits_sum_safety_wit_23_split_goal_2 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j < (Znth i digits_l (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int)))) (PreH9 : ((Znth i digits_l (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  (intArray.full dp_pre 200 dp_l)
  ** (intArray.full digits_pre 20 digits_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
|--
  “ ((INT_MIN) <= (ans + (Znth ((i * 10) + j) dp_l (0 : Int)))) ”

noncomputable def prefix_digits_sum_safety_wit_24 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j < (Znth i digits_l (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int)))) (PreH9 : ((Znth i digits_l (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  (intArray.full digits_pre 20 digits_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** (intArray.full dp_pre 200 dp_l)
|--
  “ (((i * 10) + j) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((i * 10) + j)) ”

noncomputable def prefix_digits_sum_safety_wit_25 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j < (Znth i digits_l (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int)))) (PreH9 : ((Znth i digits_l (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  (intArray.full digits_pre 20 digits_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** (intArray.full dp_pre 200 dp_l)
|--
  “ ((i * 10) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i * 10)) ”

noncomputable def prefix_digits_sum_safety_wit_26 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j < (Znth i digits_l (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int)))) (PreH9 : ((Znth i digits_l (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  (intArray.full digits_pre 20 digits_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** (intArray.full dp_pre 200 dp_l)
|--
  “ (10 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 10) ”

noncomputable def prefix_digits_sum_safety_wit_27 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j < (Znth i digits_l (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int)))) (PreH9 : ((Znth i digits_l (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  (intArray.full dp_pre 200 dp_l)
  ** (intArray.full digits_pre 20 digits_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
|--
  “ (1000000007 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1000000007) ”

noncomputable def prefix_digits_sum_safety_wit_28 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j < (Znth i digits_l (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int)))) (PreH9 : ((Znth i digits_l (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  (intArray.full dp_pre 200 dp_l)
  ** (intArray.full digits_pre 20 digits_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "j" ) )) # Int |-> (j))
  ** ((( &( "ans" ) )) # Int |-> ((Z.rem (ans + (Znth ((i * 10) + j) dp_l (0 : Int))) 1000000007)))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
|--
  “ ((j + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (j + 1)) ”

noncomputable def prefix_digits_sum_safety_wit_29 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j >= (Znth i digits_l (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int)))) (PreH9 : ((Znth i digits_l (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  ((( &( "current_digit" ) )) # Int64 |->_)
  ** (intArray.full digits_pre 20 digits_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** (intArray.full dp_pre 200 dp_l)
|--
  “ (((Z.quot x_pre power_ll) ≠ (-9223372036854775808)) ∨ (10 ≠ (-1))) ” &&
  “ (10 ≠ (0 : Int)) ”

noncomputable def prefix_digits_sum_safety_wit_30 : Prop :=
  (
forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j >= (Znth i digits_l (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int)))) (PreH9 : ((Znth i digits_l (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  ((( &( "current_digit" ) )) # Int64 |->_)
  ** (intArray.full digits_pre 20 digits_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** (intArray.full dp_pre 200 dp_l)
|--
  “ ((x_pre ≠ (-9223372036854775808)) ∨ (power_ll ≠ (-1))) ” &&
  “ (power_ll ≠ (0 : Int)) ”
) \/
(
forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j >= (Znth i digits_l (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int)))) (PreH9 : ((Znth i digits_l (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  ((( &( "current_digit" ) )) # Int64 |->_)
  ** (intArray.full digits_pre 20 digits_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** (intArray.full dp_pre 200 dp_l)
|--
  “ ((x_pre ≠ (-9223372036854775808)) ∨ (power_ll ≠ (-1))) ” &&
  “ (power_ll ≠ (0 : Int)) ”
)

noncomputable def prefix_digits_sum_safety_wit_30_split_goal_1 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j >= (Znth i digits_l (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int)))) (PreH9 : ((Znth i digits_l (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  ((( &( "current_digit" ) )) # Int64 |->_)
  ** (intArray.full digits_pre 20 digits_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** (intArray.full dp_pre 200 dp_l)
|--
  “ ((x_pre ≠ (-9223372036854775808)) ∨ (power_ll ≠ (-1))) ”

noncomputable def prefix_digits_sum_safety_wit_30_split_goal_2 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j >= (Znth i digits_l (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int)))) (PreH9 : ((Znth i digits_l (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  ((( &( "current_digit" ) )) # Int64 |->_)
  ** (intArray.full digits_pre 20 digits_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** (intArray.full dp_pre 200 dp_l)
|--
  “ (power_ll ≠ (0 : Int)) ”

noncomputable def prefix_digits_sum_safety_wit_31 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j >= (Znth i digits_l (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int)))) (PreH9 : ((Znth i digits_l (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  ((( &( "current_digit" ) )) # Int64 |->_)
  ** (intArray.full digits_pre 20 digits_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** (intArray.full dp_pre 200 dp_l)
|--
  “ (10 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 10) ”

noncomputable def prefix_digits_sum_safety_wit_32 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j >= (Znth i digits_l (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int)))) (PreH9 : ((Znth i digits_l (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  ((( &( "lower_digits" ) )) # Int64 |->_)
  ** ((( &( "current_digit" ) )) # Int64 |-> ((Z.rem (Z.quot x_pre power_ll) 10)))
  ** (intArray.full digits_pre 20 digits_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** (intArray.full dp_pre 200 dp_l)
|--
  “ ((((Z.rem x_pre power_ll) + 1) ≠ (-9223372036854775808)) ∨ (1000000007 ≠ (-1))) ” &&
  “ (1000000007 ≠ (0 : Int)) ”

noncomputable def prefix_digits_sum_safety_wit_33 : Prop :=
  (
forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j >= (Znth i digits_l (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int)))) (PreH9 : ((Znth i digits_l (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  ((( &( "lower_digits" ) )) # Int64 |->_)
  ** ((( &( "current_digit" ) )) # Int64 |-> ((Z.rem (Z.quot x_pre power_ll) 10)))
  ** (intArray.full digits_pre 20 digits_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** (intArray.full dp_pre 200 dp_l)
|--
  “ (((Z.rem x_pre power_ll) + 1) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= ((Z.rem x_pre power_ll) + 1)) ”
) \/
(
forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j >= (Znth i digits_l (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int)))) (PreH9 : ((Znth i digits_l (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  ((( &( "lower_digits" ) )) # Int64 |->_)
  ** ((( &( "current_digit" ) )) # Int64 |-> ((Z.rem (Z.quot x_pre power_ll) 10)))
  ** (intArray.full digits_pre 20 digits_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** (intArray.full dp_pre 200 dp_l)
|--
  “ (((Z.rem x_pre power_ll) + 1) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= ((Z.rem x_pre power_ll) + 1)) ”
)

noncomputable def prefix_digits_sum_safety_wit_33_split_goal_1 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j >= (Znth i digits_l (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int)))) (PreH9 : ((Znth i digits_l (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  ((( &( "lower_digits" ) )) # Int64 |->_)
  ** ((( &( "current_digit" ) )) # Int64 |-> ((Z.rem (Z.quot x_pre power_ll) 10)))
  ** (intArray.full digits_pre 20 digits_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** (intArray.full dp_pre 200 dp_l)
|--
  “ (((Z.rem x_pre power_ll) + 1) <= 9223372036854775807) ”

noncomputable def prefix_digits_sum_safety_wit_33_split_goal_2 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j >= (Znth i digits_l (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int)))) (PreH9 : ((Znth i digits_l (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  ((( &( "lower_digits" ) )) # Int64 |->_)
  ** ((( &( "current_digit" ) )) # Int64 |-> ((Z.rem (Z.quot x_pre power_ll) 10)))
  ** (intArray.full digits_pre 20 digits_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** (intArray.full dp_pre 200 dp_l)
|--
  “ ((-9223372036854775808) <= ((Z.rem x_pre power_ll) + 1)) ”

noncomputable def prefix_digits_sum_safety_wit_34 : Prop :=
  (
forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j >= (Znth i digits_l (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int)))) (PreH9 : ((Znth i digits_l (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  ((( &( "lower_digits" ) )) # Int64 |->_)
  ** ((( &( "current_digit" ) )) # Int64 |-> ((Z.rem (Z.quot x_pre power_ll) 10)))
  ** (intArray.full digits_pre 20 digits_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** (intArray.full dp_pre 200 dp_l)
|--
  “ ((x_pre ≠ (-9223372036854775808)) ∨ (power_ll ≠ (-1))) ” &&
  “ (power_ll ≠ (0 : Int)) ”
) \/
(
forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j >= (Znth i digits_l (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int)))) (PreH9 : ((Znth i digits_l (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  ((( &( "lower_digits" ) )) # Int64 |->_)
  ** ((( &( "current_digit" ) )) # Int64 |-> ((Z.rem (Z.quot x_pre power_ll) 10)))
  ** (intArray.full digits_pre 20 digits_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** (intArray.full dp_pre 200 dp_l)
|--
  “ ((x_pre ≠ (-9223372036854775808)) ∨ (power_ll ≠ (-1))) ” &&
  “ (power_ll ≠ (0 : Int)) ”
)

noncomputable def prefix_digits_sum_safety_wit_34_split_goal_1 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j >= (Znth i digits_l (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int)))) (PreH9 : ((Znth i digits_l (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  ((( &( "lower_digits" ) )) # Int64 |->_)
  ** ((( &( "current_digit" ) )) # Int64 |-> ((Z.rem (Z.quot x_pre power_ll) 10)))
  ** (intArray.full digits_pre 20 digits_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** (intArray.full dp_pre 200 dp_l)
|--
  “ ((x_pre ≠ (-9223372036854775808)) ∨ (power_ll ≠ (-1))) ”

noncomputable def prefix_digits_sum_safety_wit_34_split_goal_2 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j >= (Znth i digits_l (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int)))) (PreH9 : ((Znth i digits_l (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  ((( &( "lower_digits" ) )) # Int64 |->_)
  ** ((( &( "current_digit" ) )) # Int64 |-> ((Z.rem (Z.quot x_pre power_ll) 10)))
  ** (intArray.full digits_pre 20 digits_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** (intArray.full dp_pre 200 dp_l)
|--
  “ (power_ll ≠ (0 : Int)) ”

noncomputable def prefix_digits_sum_safety_wit_35 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j >= (Znth i digits_l (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int)))) (PreH9 : ((Znth i digits_l (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  ((( &( "lower_digits" ) )) # Int64 |->_)
  ** ((( &( "current_digit" ) )) # Int64 |-> ((Z.rem (Z.quot x_pre power_ll) 10)))
  ** (intArray.full digits_pre 20 digits_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** (intArray.full dp_pre 200 dp_l)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def prefix_digits_sum_safety_wit_36 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j >= (Znth i digits_l (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int)))) (PreH9 : ((Znth i digits_l (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  ((( &( "lower_digits" ) )) # Int64 |->_)
  ** ((( &( "current_digit" ) )) # Int64 |-> ((Z.rem (Z.quot x_pre power_ll) 10)))
  ** (intArray.full digits_pre 20 digits_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** (intArray.full dp_pre 200 dp_l)
|--
  “ (1000000007 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1000000007) ”

noncomputable def prefix_digits_sum_safety_wit_37 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j >= (Znth i digits_l (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int)))) (PreH9 : ((Znth i digits_l (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  ((( &( "moving" ) )) # Int64 |->_)
  ** ((( &( "lower_digits" ) )) # Int64 |-> ((Z.rem ((Z.rem x_pre power_ll) + 1) 1000000007)))
  ** ((( &( "current_digit" ) )) # Int64 |-> ((Z.rem (Z.quot x_pre power_ll) 10)))
  ** (intArray.full digits_pre 20 digits_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** (intArray.full dp_pre 200 dp_l)
|--
  “ ((((Z.rem ((Z.rem x_pre power_ll) + 1) 1000000007) * (Z.rem (Z.quot x_pre power_ll) 10)) ≠ (-9223372036854775808)) ∨ (1000000007 ≠ (-1))) ” &&
  “ (1000000007 ≠ (0 : Int)) ”

noncomputable def prefix_digits_sum_safety_wit_38 : Prop :=
  (
forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j >= (Znth i digits_l (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int)))) (PreH9 : ((Znth i digits_l (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  ((( &( "moving" ) )) # Int64 |->_)
  ** ((( &( "lower_digits" ) )) # Int64 |-> ((Z.rem ((Z.rem x_pre power_ll) + 1) 1000000007)))
  ** ((( &( "current_digit" ) )) # Int64 |-> ((Z.rem (Z.quot x_pre power_ll) 10)))
  ** (intArray.full digits_pre 20 digits_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** (intArray.full dp_pre 200 dp_l)
|--
  “ (((Z.rem ((Z.rem x_pre power_ll) + 1) 1000000007) * (Z.rem (Z.quot x_pre power_ll) 10)) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= ((Z.rem ((Z.rem x_pre power_ll) + 1) 1000000007) * (Z.rem (Z.quot x_pre power_ll) 10))) ”
) \/
(
forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j >= (Znth i digits_l (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int)))) (PreH9 : ((Znth i digits_l (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  ((( &( "moving" ) )) # Int64 |->_)
  ** ((( &( "lower_digits" ) )) # Int64 |-> ((Z.rem ((Z.rem x_pre power_ll) + 1) 1000000007)))
  ** ((( &( "current_digit" ) )) # Int64 |-> ((Z.rem (Z.quot x_pre power_ll) 10)))
  ** (intArray.full digits_pre 20 digits_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** (intArray.full dp_pre 200 dp_l)
|--
  “ (((Z.rem ((Z.rem x_pre power_ll) + 1) 1000000007) * (Z.rem (Z.quot x_pre power_ll) 10)) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= ((Z.rem ((Z.rem x_pre power_ll) + 1) 1000000007) * (Z.rem (Z.quot x_pre power_ll) 10))) ”
)

noncomputable def prefix_digits_sum_safety_wit_38_split_goal_1 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j >= (Znth i digits_l (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int)))) (PreH9 : ((Znth i digits_l (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  ((( &( "moving" ) )) # Int64 |->_)
  ** ((( &( "lower_digits" ) )) # Int64 |-> ((Z.rem ((Z.rem x_pre power_ll) + 1) 1000000007)))
  ** ((( &( "current_digit" ) )) # Int64 |-> ((Z.rem (Z.quot x_pre power_ll) 10)))
  ** (intArray.full digits_pre 20 digits_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** (intArray.full dp_pre 200 dp_l)
|--
  “ (((Z.rem ((Z.rem x_pre power_ll) + 1) 1000000007) * (Z.rem (Z.quot x_pre power_ll) 10)) <= 9223372036854775807) ”

noncomputable def prefix_digits_sum_safety_wit_38_split_goal_2 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j >= (Znth i digits_l (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int)))) (PreH9 : ((Znth i digits_l (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  ((( &( "moving" ) )) # Int64 |->_)
  ** ((( &( "lower_digits" ) )) # Int64 |-> ((Z.rem ((Z.rem x_pre power_ll) + 1) 1000000007)))
  ** ((( &( "current_digit" ) )) # Int64 |-> ((Z.rem (Z.quot x_pre power_ll) 10)))
  ** (intArray.full digits_pre 20 digits_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** (intArray.full dp_pre 200 dp_l)
|--
  “ ((-9223372036854775808) <= ((Z.rem ((Z.rem x_pre power_ll) + 1) 1000000007) * (Z.rem (Z.quot x_pre power_ll) 10))) ”

noncomputable def prefix_digits_sum_safety_wit_39 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j >= (Znth i digits_l (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int)))) (PreH9 : ((Znth i digits_l (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  ((( &( "moving" ) )) # Int64 |->_)
  ** ((( &( "lower_digits" ) )) # Int64 |-> ((Z.rem ((Z.rem x_pre power_ll) + 1) 1000000007)))
  ** ((( &( "current_digit" ) )) # Int64 |-> ((Z.rem (Z.quot x_pre power_ll) 10)))
  ** (intArray.full digits_pre 20 digits_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** (intArray.full dp_pre 200 dp_l)
|--
  “ (1000000007 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1000000007) ”

noncomputable def prefix_digits_sum_safety_wit_40 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j >= (Znth i digits_l (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int)))) (PreH9 : ((Znth i digits_l (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  ((( &( "new_ans" ) )) # Int64 |->_)
  ** ((( &( "moving" ) )) # Int64 |-> ((Z.rem ((Z.rem ((Z.rem x_pre power_ll) + 1) 1000000007) * (Z.rem (Z.quot x_pre power_ll) 10)) 1000000007)))
  ** ((( &( "lower_digits" ) )) # Int64 |-> ((Z.rem ((Z.rem x_pre power_ll) + 1) 1000000007)))
  ** ((( &( "current_digit" ) )) # Int64 |-> ((Z.rem (Z.quot x_pre power_ll) 10)))
  ** (intArray.full digits_pre 20 digits_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** (intArray.full dp_pre 200 dp_l)
|--
  “ (((ans + (Z.rem ((Z.rem ((Z.rem x_pre power_ll) + 1) 1000000007) * (Z.rem (Z.quot x_pre power_ll) 10)) 1000000007)) ≠ (-9223372036854775808)) ∨ (1000000007 ≠ (-1))) ” &&
  “ (1000000007 ≠ (0 : Int)) ”

noncomputable def prefix_digits_sum_safety_wit_41 : Prop :=
  (
forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j >= (Znth i digits_l (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int)))) (PreH9 : ((Znth i digits_l (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  ((( &( "new_ans" ) )) # Int64 |->_)
  ** ((( &( "moving" ) )) # Int64 |-> ((Z.rem ((Z.rem ((Z.rem x_pre power_ll) + 1) 1000000007) * (Z.rem (Z.quot x_pre power_ll) 10)) 1000000007)))
  ** ((( &( "lower_digits" ) )) # Int64 |-> ((Z.rem ((Z.rem x_pre power_ll) + 1) 1000000007)))
  ** ((( &( "current_digit" ) )) # Int64 |-> ((Z.rem (Z.quot x_pre power_ll) 10)))
  ** (intArray.full digits_pre 20 digits_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** (intArray.full dp_pre 200 dp_l)
|--
  “ ((ans + (Z.rem ((Z.rem ((Z.rem x_pre power_ll) + 1) 1000000007) * (Z.rem (Z.quot x_pre power_ll) 10)) 1000000007)) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (ans + (Z.rem ((Z.rem ((Z.rem x_pre power_ll) + 1) 1000000007) * (Z.rem (Z.quot x_pre power_ll) 10)) 1000000007))) ”
) \/
(
forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j >= (Znth i digits_l (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int)))) (PreH9 : ((Znth i digits_l (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  ((( &( "new_ans" ) )) # Int64 |->_)
  ** ((( &( "moving" ) )) # Int64 |-> ((Z.rem ((Z.rem ((Z.rem x_pre power_ll) + 1) 1000000007) * (Z.rem (Z.quot x_pre power_ll) 10)) 1000000007)))
  ** ((( &( "lower_digits" ) )) # Int64 |-> ((Z.rem ((Z.rem x_pre power_ll) + 1) 1000000007)))
  ** ((( &( "current_digit" ) )) # Int64 |-> ((Z.rem (Z.quot x_pre power_ll) 10)))
  ** (intArray.full digits_pre 20 digits_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** (intArray.full dp_pre 200 dp_l)
|--
  “ ((ans + (Z.rem ((Z.rem ((Z.rem x_pre power_ll) + 1) 1000000007) * (Z.rem (Z.quot x_pre power_ll) 10)) 1000000007)) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (ans + (Z.rem ((Z.rem ((Z.rem x_pre power_ll) + 1) 1000000007) * (Z.rem (Z.quot x_pre power_ll) 10)) 1000000007))) ”
)

noncomputable def prefix_digits_sum_safety_wit_41_split_goal_1 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j >= (Znth i digits_l (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int)))) (PreH9 : ((Znth i digits_l (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  ((( &( "new_ans" ) )) # Int64 |->_)
  ** ((( &( "moving" ) )) # Int64 |-> ((Z.rem ((Z.rem ((Z.rem x_pre power_ll) + 1) 1000000007) * (Z.rem (Z.quot x_pre power_ll) 10)) 1000000007)))
  ** ((( &( "lower_digits" ) )) # Int64 |-> ((Z.rem ((Z.rem x_pre power_ll) + 1) 1000000007)))
  ** ((( &( "current_digit" ) )) # Int64 |-> ((Z.rem (Z.quot x_pre power_ll) 10)))
  ** (intArray.full digits_pre 20 digits_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** (intArray.full dp_pre 200 dp_l)
|--
  “ ((ans + (Z.rem ((Z.rem ((Z.rem x_pre power_ll) + 1) 1000000007) * (Z.rem (Z.quot x_pre power_ll) 10)) 1000000007)) <= 9223372036854775807) ”

noncomputable def prefix_digits_sum_safety_wit_41_split_goal_2 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j >= (Znth i digits_l (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int)))) (PreH9 : ((Znth i digits_l (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  ((( &( "new_ans" ) )) # Int64 |->_)
  ** ((( &( "moving" ) )) # Int64 |-> ((Z.rem ((Z.rem ((Z.rem x_pre power_ll) + 1) 1000000007) * (Z.rem (Z.quot x_pre power_ll) 10)) 1000000007)))
  ** ((( &( "lower_digits" ) )) # Int64 |-> ((Z.rem ((Z.rem x_pre power_ll) + 1) 1000000007)))
  ** ((( &( "current_digit" ) )) # Int64 |-> ((Z.rem (Z.quot x_pre power_ll) 10)))
  ** (intArray.full digits_pre 20 digits_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** (intArray.full dp_pre 200 dp_l)
|--
  “ ((-9223372036854775808) <= (ans + (Z.rem ((Z.rem ((Z.rem x_pre power_ll) + 1) 1000000007) * (Z.rem (Z.quot x_pre power_ll) 10)) 1000000007))) ”

noncomputable def prefix_digits_sum_safety_wit_42 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j >= (Znth i digits_l (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int)))) (PreH9 : ((Znth i digits_l (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  ((( &( "new_ans" ) )) # Int64 |->_)
  ** ((( &( "moving" ) )) # Int64 |-> ((Z.rem ((Z.rem ((Z.rem x_pre power_ll) + 1) 1000000007) * (Z.rem (Z.quot x_pre power_ll) 10)) 1000000007)))
  ** ((( &( "lower_digits" ) )) # Int64 |-> ((Z.rem ((Z.rem x_pre power_ll) + 1) 1000000007)))
  ** ((( &( "current_digit" ) )) # Int64 |-> ((Z.rem (Z.quot x_pre power_ll) 10)))
  ** (intArray.full digits_pre 20 digits_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "ans" ) )) # Int |-> (ans))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** (intArray.full dp_pre 200 dp_l)
|--
  “ (1000000007 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1000000007) ”

noncomputable def prefix_digits_sum_safety_wit_43 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j >= (Znth i digits_l (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int)))) (PreH9 : ((Znth i digits_l (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  (intArray.full digits_pre 20 digits_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "ans" ) )) # Int |-> ((signed_last_nbits ((Z.rem (ans + (Z.rem ((Z.rem ((Z.rem x_pre power_ll) + 1) 1000000007) * (Z.rem (Z.quot x_pre power_ll) 10)) 1000000007)) 1000000007)) (32))))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** (intArray.full dp_pre 200 dp_l)
|--
  “ ((power_ll ≠ (-9223372036854775808)) ∨ (10 ≠ (-1))) ” &&
  “ (10 ≠ (0 : Int)) ”

noncomputable def prefix_digits_sum_safety_wit_44 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j >= (Znth i digits_l (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int)))) (PreH9 : ((Znth i digits_l (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  (intArray.full digits_pre 20 digits_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "ans" ) )) # Int |-> ((signed_last_nbits ((Z.rem (ans + (Z.rem ((Z.rem ((Z.rem x_pre power_ll) + 1) 1000000007) * (Z.rem (Z.quot x_pre power_ll) 10)) 1000000007)) 1000000007)) (32))))
  ** ((( &( "power_ll" ) )) # Int64 |-> (power_ll))
  ** (intArray.full dp_pre 200 dp_l)
|--
  “ (10 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 10) ”

noncomputable def prefix_digits_sum_safety_wit_45 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j >= (Znth i digits_l (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int)))) (PreH9 : ((Znth i digits_l (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  (intArray.full digits_pre 20 digits_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "dp" ) )) # Ptr |-> (dp_pre))
  ** ((( &( "digits" ) )) # Ptr |-> (digits_pre))
  ** ((( &( "tmpx" ) )) # Int64 |-> (tmpx))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "m" ) )) # Int |-> (m))
  ** ((( &( "ans" ) )) # Int |-> ((signed_last_nbits ((Z.rem (ans + (Z.rem ((Z.rem ((Z.rem x_pre power_ll) + 1) 1000000007) * (Z.rem (Z.quot x_pre power_ll) 10)) 1000000007)) 1000000007)) (32))))
  ** ((( &( "power_ll" ) )) # Int64 |-> ((Z.quot power_ll 10)))
  ** (intArray.full dp_pre 200 dp_l)
|--
  “ ((i - 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i - 1)) ”

noncomputable def prefix_digits_sum_entail_wit_1 : Prop :=
  (
forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (PreH1 : (x_pre >= 1)) (PreH2 : ((0 : Int) <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (DigitDPTable dp_l)) ,
  (intArray.full dp_pre 200 dp_l)
  ** (intArray.undef_full digits_pre 20)
|--
  EX digits_l : (List Int),
  “ (1 <= x_pre) ” &&
  “ (x_pre <= 1000000000000000000) ” &&
  “ ((0 : Int) = (0 : Int)) ” &&
  “ ((0 : Int) = (0 : Int)) ” &&
  “ (1 = 1) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= 20) ” &&
  “ ((Zlength (digits_l)) = (0 : Int)) ” &&
  “ (Forall (Eq ((0 : Int))) digits_l) ” &&
  “ (DigitDPTable dp_l) ”
  &&  (intArray.full dp_pre 200 dp_l)
  ** (intArray.seg digits_pre (0 : Int) (0 : Int) digits_l)
  ** (intArray.undef_seg digits_pre (0 : Int) 20)
) \/
(
forall (x_pre : Int) (dp_l : (List Int)) (PreH1 : (x_pre >= 1)) (PreH2 : ((0 : Int) <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (DigitDPTable dp_l)) ,
  TT && emp 
|--
  “ (Forall (Eq ((0 : Int))) (@List.nil Int)) ” &&
  “ ((Zlength ((@List.nil Int))) = (0 : Int)) ”
  &&  emp
)

noncomputable def prefix_digits_sum_entail_wit_1_split_goal_1 : Prop :=
  forall (x_pre : Int) (dp_l : (List Int)) (PreH1 : (x_pre >= 1)) (PreH2 : ((0 : Int) <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (DigitDPTable dp_l)) ,
  (Forall (Eq ((0 : Int))) (@List.nil Int))

noncomputable def prefix_digits_sum_entail_wit_1_split_goal_2 : Prop :=
  forall (x_pre : Int) (dp_l : (List Int)) (PreH1 : (x_pre >= 1)) (PreH2 : ((0 : Int) <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (DigitDPTable dp_l)) ,
  ((Zlength ((@List.nil Int))) = (0 : Int))

noncomputable def prefix_digits_sum_entail_wit_2 : Prop :=
  (
forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (digits_l_2 : (List Int)) (i : Int) (power_ll : Int) (ans : Int) (m : Int) (PreH1 : (i < 20)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (m = (0 : Int))) (PreH5 : (ans = (0 : Int))) (PreH6 : (power_ll = 1)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= 20)) (PreH9 : ((Zlength (digits_l_2)) = i)) (PreH10 : (Forall (Eq ((0 : Int))) digits_l_2)) (PreH11 : (DigitDPTable dp_l)) ,
  (intArray.seg digits_pre (0 : Int) (i + 1) (digits_l_2 ++ ((0 : Int) :: (@List.nil Int))))
  ** (intArray.undef_seg digits_pre (i + 1) 20)
  ** (intArray.full dp_pre 200 dp_l)
|--
  EX digits_l : (List Int),
  “ (1 <= x_pre) ” &&
  “ (x_pre <= 1000000000000000000) ” &&
  “ (m = (0 : Int)) ” &&
  “ (ans = (0 : Int)) ” &&
  “ (power_ll = 1) ” &&
  “ ((0 : Int) <= (i + 1)) ” &&
  “ ((i + 1) <= 20) ” &&
  “ ((Zlength (digits_l)) = (i + 1)) ” &&
  “ (Forall (Eq ((0 : Int))) digits_l) ” &&
  “ (DigitDPTable dp_l) ”
  &&  (intArray.full dp_pre 200 dp_l)
  ** (intArray.seg digits_pre (0 : Int) (i + 1) digits_l)
  ** (intArray.undef_seg digits_pre (i + 1) 20)
) \/
(
forall (x_pre : Int) (dp_l : (List Int)) (digits_l_2 : (List Int)) (i : Int) (power_ll : Int) (ans : Int) (m : Int) (PreH1 : (i < 20)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (m = (0 : Int))) (PreH5 : (ans = (0 : Int))) (PreH6 : (power_ll = 1)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= 20)) (PreH9 : ((Zlength (digits_l_2)) = i)) (PreH10 : (Forall (Eq ((0 : Int))) digits_l_2)) (PreH11 : (DigitDPTable dp_l)) ,
  TT && emp 
|--
  “ (Forall (Eq ((0 : Int))) (digits_l_2 ++ ((0 : Int) :: (@List.nil Int)))) ” &&
  “ ((Zlength ((digits_l_2 ++ ((0 : Int) :: (@List.nil Int))))) = (i + 1)) ”
  &&  emp
)

noncomputable def prefix_digits_sum_entail_wit_2_split_goal_1 : Prop :=
  forall (x_pre : Int) (dp_l : (List Int)) (digits_l_2 : (List Int)) (i : Int) (power_ll : Int) (ans : Int) (m : Int) (PreH1 : (i < 20)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (m = (0 : Int))) (PreH5 : (ans = (0 : Int))) (PreH6 : (power_ll = 1)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= 20)) (PreH9 : ((Zlength (digits_l_2)) = i)) (PreH10 : (Forall (Eq ((0 : Int))) digits_l_2)) (PreH11 : (DigitDPTable dp_l)) ,
  (Forall (Eq ((0 : Int))) (digits_l_2 ++ ((0 : Int) :: (@List.nil Int))))

noncomputable def prefix_digits_sum_entail_wit_2_split_goal_2 : Prop :=
  forall (x_pre : Int) (dp_l : (List Int)) (digits_l_2 : (List Int)) (i : Int) (power_ll : Int) (ans : Int) (m : Int) (PreH1 : (i < 20)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (m = (0 : Int))) (PreH5 : (ans = (0 : Int))) (PreH6 : (power_ll = 1)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= 20)) (PreH9 : ((Zlength (digits_l_2)) = i)) (PreH10 : (Forall (Eq ((0 : Int))) digits_l_2)) (PreH11 : (DigitDPTable dp_l)) ,
  ((Zlength ((digits_l_2 ++ ((0 : Int) :: (@List.nil Int))))) = (i + 1))

noncomputable def prefix_digits_sum_entail_wit_3 : Prop :=
  (
forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (digits_l_2 : (List Int)) (i : Int) (power_ll : Int) (ans : Int) (m : Int) (PreH1 : (i >= 20)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (m = (0 : Int))) (PreH5 : (ans = (0 : Int))) (PreH6 : (power_ll = 1)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= 20)) (PreH9 : ((Zlength (digits_l_2)) = i)) (PreH10 : (Forall (Eq ((0 : Int))) digits_l_2)) (PreH11 : (DigitDPTable dp_l)) ,
  (intArray.full dp_pre 200 dp_l)
  ** (intArray.seg digits_pre (0 : Int) i digits_l_2)
  ** (intArray.undef_seg digits_pre i 20)
|--
  EX digits_l : (List Int),
  “ (1 <= x_pre) ” &&
  “ (x_pre <= 1000000000000000000) ” &&
  “ (ans = (0 : Int)) ” &&
  “ (power_ll = 1) ” &&
  “ ((0 : Int) <= m) ” &&
  “ (m <= 19) ” &&
  “ (x_pre >= (0 : Int)) ” &&
  “ ((x_pre ≠ (0 : Int)) -> (m < 19)) ” &&
  “ ((x_pre = (0 : Int)) -> (1 <= m)) ” &&
  “ ((x_pre = (0 : Int)) -> (ExtractedDigitCount x_pre m)) ” &&
  “ ((Zlength (digits_l)) = 20) ” &&
  “ (ExtractedDigitBuffer x_pre digits_l m x_pre) ” &&
  “ (DigitDPTable dp_l) ”
  &&  (intArray.full dp_pre 200 dp_l)
  ** (intArray.full digits_pre 20 digits_l)
) \/
(
forall (x_pre : Int) (dp_l : (List Int)) (digits_l_2 : (List Int)) (i : Int) (power_ll : Int) (ans : Int) (m : Int) (PreH1 : (i >= 20)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (m = (0 : Int))) (PreH5 : (ans = (0 : Int))) (PreH6 : (power_ll = 1)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= 20)) (PreH9 : ((Zlength (digits_l_2)) = i)) (PreH10 : (Forall (Eq ((0 : Int))) digits_l_2)) (PreH11 : (DigitDPTable dp_l)) ,
  TT && emp 
|--
  “ (ExtractedDigitBuffer x_pre digits_l_2 (0 : Int) x_pre) ”
  &&  emp
)

noncomputable def prefix_digits_sum_entail_wit_3_split_goal_1 : Prop :=
  forall (x_pre : Int) (dp_l : (List Int)) (digits_l_2 : (List Int)) (i : Int) (power_ll : Int) (ans : Int) (m : Int) (PreH1 : (i >= 20)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (m = (0 : Int))) (PreH5 : (ans = (0 : Int))) (PreH6 : (power_ll = 1)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= 20)) (PreH9 : ((Zlength (digits_l_2)) = i)) (PreH10 : (Forall (Eq ((0 : Int))) digits_l_2)) (PreH11 : (DigitDPTable dp_l)) ,
  (ExtractedDigitBuffer x_pre digits_l_2 (0 : Int) x_pre)

noncomputable def prefix_digits_sum_entail_wit_4 : Prop :=
  (
forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (digits_l_2 : (List Int)) (tmpx : Int) (m : Int) (power_ll : Int) (ans : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (ans = (0 : Int))) (PreH4 : (power_ll = 1)) (PreH5 : ((0 : Int) <= m)) (PreH6 : (m <= 19)) (PreH7 : (tmpx >= (0 : Int))) (PreH8 : ((tmpx ≠ (0 : Int)) -> (m < 19))) (PreH9 : ((tmpx = (0 : Int)) -> (1 <= m))) (PreH10 : ((tmpx = (0 : Int)) -> (ExtractedDigitCount x_pre m))) (PreH11 : ((Zlength (digits_l_2)) = 20)) (PreH12 : (ExtractedDigitBuffer x_pre digits_l_2 m tmpx)) (PreH13 : (DigitDPTable dp_l)) (PreH14 : (tmpx ≠ (0 : Int))) ,
  (intArray.full digits_pre 20 (replace_Znth ((m + 1)) ((signed_last_nbits ((Z.rem tmpx 10)) (32))) (digits_l_2)))
  ** (intArray.full dp_pre 200 dp_l)
|--
  EX digits_l : (List Int),
  “ (1 <= x_pre) ” &&
  “ (x_pre <= 1000000000000000000) ” &&
  “ (ans = (0 : Int)) ” &&
  “ (power_ll = 1) ” &&
  “ ((0 : Int) <= (m + 1)) ” &&
  “ ((m + 1) <= 19) ” &&
  “ ((Z.quot tmpx 10) >= (0 : Int)) ” &&
  “ (((Z.quot tmpx 10) ≠ (0 : Int)) -> ((m + 1) < 19)) ” &&
  “ (((Z.quot tmpx 10) = (0 : Int)) -> (1 <= (m + 1))) ” &&
  “ (((Z.quot tmpx 10) = (0 : Int)) -> (ExtractedDigitCount x_pre (m + 1))) ” &&
  “ ((Zlength (digits_l)) = 20) ” &&
  “ (ExtractedDigitBuffer x_pre digits_l (m + 1) (Z.quot tmpx 10)) ” &&
  “ (DigitDPTable dp_l) ”
  &&  (intArray.full dp_pre 200 dp_l)
  ** (intArray.full digits_pre 20 digits_l)
) \/
(
forall (x_pre : Int) (dp_l : (List Int)) (digits_l_2 : (List Int)) (tmpx : Int) (m : Int) (power_ll : Int) (ans : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (ans = (0 : Int))) (PreH4 : (power_ll = 1)) (PreH5 : ((0 : Int) <= m)) (PreH6 : (m <= 19)) (PreH7 : (tmpx >= (0 : Int))) (PreH8 : ((tmpx ≠ (0 : Int)) -> (m < 19))) (PreH9 : ((tmpx = (0 : Int)) -> (1 <= m))) (PreH10 : ((tmpx = (0 : Int)) -> (ExtractedDigitCount x_pre m))) (PreH11 : ((Zlength (digits_l_2)) = 20)) (PreH12 : (ExtractedDigitBuffer x_pre digits_l_2 m tmpx)) (PreH13 : (DigitDPTable dp_l)) (PreH14 : (tmpx ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (ExtractedDigitBuffer x_pre (replace_Znth ((m + 1)) ((signed_last_nbits ((Z.rem tmpx 10)) (32))) (digits_l_2)) (m + 1) (Z.quot tmpx 10)) ” &&
  “ ((Zlength ((replace_Znth ((m + 1)) ((signed_last_nbits ((Z.rem tmpx 10)) (32))) (digits_l_2)))) = 20) ” &&
  “ (((Z.quot tmpx 10) = (0 : Int)) -> (ExtractedDigitCount x_pre (m + 1))) ” &&
  “ (((Z.quot tmpx 10) ≠ (0 : Int)) -> ((m + 1) < 19)) ” &&
  “ ((Z.quot tmpx 10) >= (0 : Int)) ”
  &&  emp
)

noncomputable def prefix_digits_sum_entail_wit_4_split_goal_1 : Prop :=
  forall (x_pre : Int) (dp_l : (List Int)) (digits_l_2 : (List Int)) (tmpx : Int) (m : Int) (power_ll : Int) (ans : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (ans = (0 : Int))) (PreH4 : (power_ll = 1)) (PreH5 : ((0 : Int) <= m)) (PreH6 : (m <= 19)) (PreH7 : (tmpx >= (0 : Int))) (PreH8 : ((tmpx ≠ (0 : Int)) -> (m < 19))) (PreH9 : ((tmpx = (0 : Int)) -> (1 <= m))) (PreH10 : ((tmpx = (0 : Int)) -> (ExtractedDigitCount x_pre m))) (PreH11 : ((Zlength (digits_l_2)) = 20)) (PreH12 : (ExtractedDigitBuffer x_pre digits_l_2 m tmpx)) (PreH13 : (DigitDPTable dp_l)) (PreH14 : (tmpx ≠ (0 : Int))) ,
  (ExtractedDigitBuffer x_pre (replace_Znth ((m + 1)) ((signed_last_nbits ((Z.rem tmpx 10)) (32))) (digits_l_2)) (m + 1) (Z.quot tmpx 10))

noncomputable def prefix_digits_sum_entail_wit_4_split_goal_2 : Prop :=
  forall (x_pre : Int) (dp_l : (List Int)) (digits_l_2 : (List Int)) (tmpx : Int) (m : Int) (power_ll : Int) (ans : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (ans = (0 : Int))) (PreH4 : (power_ll = 1)) (PreH5 : ((0 : Int) <= m)) (PreH6 : (m <= 19)) (PreH7 : (tmpx >= (0 : Int))) (PreH8 : ((tmpx ≠ (0 : Int)) -> (m < 19))) (PreH9 : ((tmpx = (0 : Int)) -> (1 <= m))) (PreH10 : ((tmpx = (0 : Int)) -> (ExtractedDigitCount x_pre m))) (PreH11 : ((Zlength (digits_l_2)) = 20)) (PreH12 : (ExtractedDigitBuffer x_pre digits_l_2 m tmpx)) (PreH13 : (DigitDPTable dp_l)) (PreH14 : (tmpx ≠ (0 : Int))) ,
  ((Zlength ((replace_Znth ((m + 1)) ((signed_last_nbits ((Z.rem tmpx 10)) (32))) (digits_l_2)))) = 20)

noncomputable def prefix_digits_sum_entail_wit_4_split_goal_3 : Prop :=
  forall (x_pre : Int) (dp_l : (List Int)) (digits_l_2 : (List Int)) (tmpx : Int) (m : Int) (power_ll : Int) (ans : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (ans = (0 : Int))) (PreH4 : (power_ll = 1)) (PreH5 : ((0 : Int) <= m)) (PreH6 : (m <= 19)) (PreH7 : (tmpx >= (0 : Int))) (PreH8 : ((tmpx ≠ (0 : Int)) -> (m < 19))) (PreH9 : ((tmpx = (0 : Int)) -> (1 <= m))) (PreH10 : ((tmpx = (0 : Int)) -> (ExtractedDigitCount x_pre m))) (PreH11 : ((Zlength (digits_l_2)) = 20)) (PreH12 : (ExtractedDigitBuffer x_pre digits_l_2 m tmpx)) (PreH13 : (DigitDPTable dp_l)) (PreH14 : (tmpx ≠ (0 : Int))) ,
  (((Z.quot tmpx 10) = (0 : Int)) -> (ExtractedDigitCount x_pre (m + 1)))

noncomputable def prefix_digits_sum_entail_wit_4_split_goal_4 : Prop :=
  forall (x_pre : Int) (dp_l : (List Int)) (digits_l_2 : (List Int)) (tmpx : Int) (m : Int) (power_ll : Int) (ans : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (ans = (0 : Int))) (PreH4 : (power_ll = 1)) (PreH5 : ((0 : Int) <= m)) (PreH6 : (m <= 19)) (PreH7 : (tmpx >= (0 : Int))) (PreH8 : ((tmpx ≠ (0 : Int)) -> (m < 19))) (PreH9 : ((tmpx = (0 : Int)) -> (1 <= m))) (PreH10 : ((tmpx = (0 : Int)) -> (ExtractedDigitCount x_pre m))) (PreH11 : ((Zlength (digits_l_2)) = 20)) (PreH12 : (ExtractedDigitBuffer x_pre digits_l_2 m tmpx)) (PreH13 : (DigitDPTable dp_l)) (PreH14 : (tmpx ≠ (0 : Int))) ,
  (((Z.quot tmpx 10) ≠ (0 : Int)) -> ((m + 1) < 19))

noncomputable def prefix_digits_sum_entail_wit_4_split_goal_5 : Prop :=
  forall (x_pre : Int) (dp_l : (List Int)) (digits_l_2 : (List Int)) (tmpx : Int) (m : Int) (power_ll : Int) (ans : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (ans = (0 : Int))) (PreH4 : (power_ll = 1)) (PreH5 : ((0 : Int) <= m)) (PreH6 : (m <= 19)) (PreH7 : (tmpx >= (0 : Int))) (PreH8 : ((tmpx ≠ (0 : Int)) -> (m < 19))) (PreH9 : ((tmpx = (0 : Int)) -> (1 <= m))) (PreH10 : ((tmpx = (0 : Int)) -> (ExtractedDigitCount x_pre m))) (PreH11 : ((Zlength (digits_l_2)) = 20)) (PreH12 : (ExtractedDigitBuffer x_pre digits_l_2 m tmpx)) (PreH13 : (DigitDPTable dp_l)) (PreH14 : (tmpx ≠ (0 : Int))) ,
  ((Z.quot tmpx 10) >= (0 : Int))

noncomputable def prefix_digits_sum_entail_wit_5 : Prop :=
  (
forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (digits_l_2 : (List Int)) (tmpx : Int) (m : Int) (power_ll : Int) (ans : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (ans = (0 : Int))) (PreH4 : (power_ll = 1)) (PreH5 : ((0 : Int) <= m)) (PreH6 : (m <= 19)) (PreH7 : (tmpx >= (0 : Int))) (PreH8 : ((tmpx ≠ (0 : Int)) -> (m < 19))) (PreH9 : ((tmpx = (0 : Int)) -> (1 <= m))) (PreH10 : ((tmpx = (0 : Int)) -> (ExtractedDigitCount x_pre m))) (PreH11 : ((Zlength (digits_l_2)) = 20)) (PreH12 : (ExtractedDigitBuffer x_pre digits_l_2 m tmpx)) (PreH13 : (DigitDPTable dp_l)) (PreH14 : (tmpx = (0 : Int))) ,
  (intArray.full dp_pre 200 dp_l)
  ** (intArray.full digits_pre 20 digits_l_2)
|--
  EX digits_l : (List Int),
  “ (1 <= x_pre) ” &&
  “ (x_pre <= 1000000000000000000) ” &&
  “ (ans = (0 : Int)) ” &&
  “ (tmpx = (0 : Int)) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= m) ” &&
  “ (m <= 19) ” &&
  “ ((Zlength (digits_l)) = 20) ” &&
  “ (ExtractedDigitBuffer x_pre digits_l m (0 : Int)) ” &&
  “ (ExtractedDigitCount x_pre m) ” &&
  “ (DigitPositionPower 1 power_ll) ” &&
  “ (AccumulatedDigitSumCorrect x_pre m ans) ” &&
  “ (DigitDPTable dp_l) ”
  &&  (intArray.full dp_pre 200 dp_l)
  ** (intArray.full digits_pre 20 digits_l)
) \/
(
forall (x_pre : Int) (dp_l : (List Int)) (digits_l_2 : (List Int)) (tmpx : Int) (m : Int) (power_ll : Int) (ans : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (ans = (0 : Int))) (PreH4 : (power_ll = 1)) (PreH5 : ((0 : Int) <= m)) (PreH6 : (m <= 19)) (PreH7 : (tmpx >= (0 : Int))) (PreH8 : ((tmpx ≠ (0 : Int)) -> (m < 19))) (PreH9 : ((tmpx = (0 : Int)) -> (1 <= m))) (PreH10 : ((tmpx = (0 : Int)) -> (ExtractedDigitCount x_pre m))) (PreH11 : ((Zlength (digits_l_2)) = 20)) (PreH12 : (ExtractedDigitBuffer x_pre digits_l_2 m tmpx)) (PreH13 : (DigitDPTable dp_l)) (PreH14 : (tmpx = (0 : Int))) ,
  TT && emp 
|--
  “ (AccumulatedDigitSumCorrect x_pre m (0 : Int)) ” &&
  “ (DigitPositionPower 1 1) ”
  &&  emp
)

noncomputable def prefix_digits_sum_entail_wit_5_split_goal_1 : Prop :=
  forall (x_pre : Int) (dp_l : (List Int)) (digits_l_2 : (List Int)) (tmpx : Int) (m : Int) (power_ll : Int) (ans : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (ans = (0 : Int))) (PreH4 : (power_ll = 1)) (PreH5 : ((0 : Int) <= m)) (PreH6 : (m <= 19)) (PreH7 : (tmpx >= (0 : Int))) (PreH8 : ((tmpx ≠ (0 : Int)) -> (m < 19))) (PreH9 : ((tmpx = (0 : Int)) -> (1 <= m))) (PreH10 : ((tmpx = (0 : Int)) -> (ExtractedDigitCount x_pre m))) (PreH11 : ((Zlength (digits_l_2)) = 20)) (PreH12 : (ExtractedDigitBuffer x_pre digits_l_2 m tmpx)) (PreH13 : (DigitDPTable dp_l)) (PreH14 : (tmpx = (0 : Int))) ,
  (AccumulatedDigitSumCorrect x_pre m (0 : Int))

noncomputable def prefix_digits_sum_entail_wit_5_split_goal_2 : Prop :=
  forall (x_pre : Int) (dp_l : (List Int)) (digits_l_2 : (List Int)) (tmpx : Int) (m : Int) (power_ll : Int) (ans : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (ans = (0 : Int))) (PreH4 : (power_ll = 1)) (PreH5 : ((0 : Int) <= m)) (PreH6 : (m <= 19)) (PreH7 : (tmpx >= (0 : Int))) (PreH8 : ((tmpx ≠ (0 : Int)) -> (m < 19))) (PreH9 : ((tmpx = (0 : Int)) -> (1 <= m))) (PreH10 : ((tmpx = (0 : Int)) -> (ExtractedDigitCount x_pre m))) (PreH11 : ((Zlength (digits_l_2)) = 20)) (PreH12 : (ExtractedDigitBuffer x_pre digits_l_2 m tmpx)) (PreH13 : (DigitDPTable dp_l)) (PreH14 : (tmpx = (0 : Int))) ,
  (DigitPositionPower 1 1)

noncomputable def prefix_digits_sum_entail_wit_6 : Prop :=
  (
forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (digits_l_2 : (List Int)) (m : Int) (i : Int) (tmpx : Int) (ans : Int) (PreH1 : (i < m)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (ans = (0 : Int))) (PreH5 : (tmpx = (0 : Int))) (PreH6 : (1 <= i)) (PreH7 : (i <= m)) (PreH8 : (m <= 19)) (PreH9 : ((Zlength (digits_l_2)) = 20)) (PreH10 : (ExtractedDigitBuffer x_pre digits_l_2 m (0 : Int))) (PreH11 : (ExtractedDigitCount x_pre m)) (PreH12 : (DigitPositionPower i power_ll)) (PreH13 : (AccumulatedDigitSumCorrect x_pre m ans)) (PreH14 : (DigitDPTable dp_l)) ,
  (intArray.full dp_pre 200 dp_l)
  ** (intArray.full digits_pre 20 digits_l_2)
|--
  EX digits_l : (List Int),
  “ (1 <= x_pre) ” &&
  “ (x_pre <= 1000000000000000000) ” &&
  “ (ans = (0 : Int)) ” &&
  “ (tmpx = (0 : Int)) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= m) ” &&
  “ (m <= 19) ” &&
  “ ((Zlength (digits_l)) = 20) ” &&
  “ (ExtractedDigitBuffer x_pre digits_l m (0 : Int)) ” &&
  “ (ExtractedDigitCount x_pre m) ” &&
  “ (DigitPositionPower (i + 1) (power_ll * 10)) ” &&
  “ (AccumulatedDigitSumCorrect x_pre m ans) ” &&
  “ (DigitDPTable dp_l) ”
  &&  (intArray.full dp_pre 200 dp_l)
  ** (intArray.full digits_pre 20 digits_l)
) \/
(
forall (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (digits_l_2 : (List Int)) (m : Int) (i : Int) (tmpx : Int) (ans : Int) (PreH1 : (i < m)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (ans = (0 : Int))) (PreH5 : (tmpx = (0 : Int))) (PreH6 : (1 <= i)) (PreH7 : (i <= m)) (PreH8 : (m <= 19)) (PreH9 : ((Zlength (digits_l_2)) = 20)) (PreH10 : (ExtractedDigitBuffer x_pre digits_l_2 m (0 : Int))) (PreH11 : (ExtractedDigitCount x_pre m)) (PreH12 : (DigitPositionPower i power_ll)) (PreH13 : (AccumulatedDigitSumCorrect x_pre m ans)) (PreH14 : (DigitDPTable dp_l)) ,
  TT && emp 
|--
  “ (DigitPositionPower (i + 1) (power_ll * 10)) ”
  &&  emp
)

noncomputable def prefix_digits_sum_entail_wit_6_split_goal_1 : Prop :=
  forall (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (digits_l_2 : (List Int)) (m : Int) (i : Int) (tmpx : Int) (ans : Int) (PreH1 : (i < m)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (ans = (0 : Int))) (PreH5 : (tmpx = (0 : Int))) (PreH6 : (1 <= i)) (PreH7 : (i <= m)) (PreH8 : (m <= 19)) (PreH9 : ((Zlength (digits_l_2)) = 20)) (PreH10 : (ExtractedDigitBuffer x_pre digits_l_2 m (0 : Int))) (PreH11 : (ExtractedDigitCount x_pre m)) (PreH12 : (DigitPositionPower i power_ll)) (PreH13 : (AccumulatedDigitSumCorrect x_pre m ans)) (PreH14 : (DigitDPTable dp_l)) ,
  (DigitPositionPower (i + 1) (power_ll * 10))

noncomputable def prefix_digits_sum_entail_wit_7 : Prop :=
  (
forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (digits_l_2 : (List Int)) (m : Int) (i : Int) (tmpx : Int) (ans : Int) (PreH1 : (i >= m)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (ans = (0 : Int))) (PreH5 : (tmpx = (0 : Int))) (PreH6 : (1 <= i)) (PreH7 : (i <= m)) (PreH8 : (m <= 19)) (PreH9 : ((Zlength (digits_l_2)) = 20)) (PreH10 : (ExtractedDigitBuffer x_pre digits_l_2 m (0 : Int))) (PreH11 : (ExtractedDigitCount x_pre m)) (PreH12 : (DigitPositionPower i power_ll)) (PreH13 : (AccumulatedDigitSumCorrect x_pre m ans)) (PreH14 : (DigitDPTable dp_l)) ,
  (intArray.full dp_pre 200 dp_l)
  ** (intArray.full digits_pre 20 digits_l_2)
|--
  EX digits_l : (List Int),
  “ (1 <= x_pre) ” &&
  “ (x_pre <= 1000000000000000000) ” &&
  “ (tmpx = (0 : Int)) ” &&
  “ ((0 : Int) <= m) ” &&
  “ (m <= m) ” &&
  “ (m <= 19) ” &&
  “ ((0 : Int) <= ans) ” &&
  “ (ans < 1000000007) ” &&
  “ ((Zlength (digits_l)) = 20) ” &&
  “ (ExtractedDigitBuffer x_pre digits_l m (0 : Int)) ” &&
  “ (ExtractedDigitCount x_pre m) ” &&
  “ (AccumulatedDigitSumCorrect x_pre m ans) ” &&
  “ (OuterDigitPositionPower m power_ll) ” &&
  “ (DigitDPTable dp_l) ”
  &&  (intArray.full dp_pre 200 dp_l)
  ** (intArray.full digits_pre 20 digits_l)
) \/
(
forall (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (digits_l_2 : (List Int)) (m : Int) (i : Int) (tmpx : Int) (ans : Int) (PreH1 : (i >= m)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (ans = (0 : Int))) (PreH5 : (tmpx = (0 : Int))) (PreH6 : (1 <= i)) (PreH7 : (i <= m)) (PreH8 : (m <= 19)) (PreH9 : ((Zlength (digits_l_2)) = 20)) (PreH10 : (ExtractedDigitBuffer x_pre digits_l_2 m (0 : Int))) (PreH11 : (ExtractedDigitCount x_pre m)) (PreH12 : (DigitPositionPower i power_ll)) (PreH13 : (AccumulatedDigitSumCorrect x_pre m ans)) (PreH14 : (DigitDPTable dp_l)) ,
  TT && emp 
|--
  “ (OuterDigitPositionPower m power_ll) ”
  &&  emp
)

noncomputable def prefix_digits_sum_entail_wit_7_split_goal_1 : Prop :=
  forall (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (digits_l_2 : (List Int)) (m : Int) (i : Int) (tmpx : Int) (ans : Int) (PreH1 : (i >= m)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (ans = (0 : Int))) (PreH5 : (tmpx = (0 : Int))) (PreH6 : (1 <= i)) (PreH7 : (i <= m)) (PreH8 : (m <= 19)) (PreH9 : ((Zlength (digits_l_2)) = 20)) (PreH10 : (ExtractedDigitBuffer x_pre digits_l_2 m (0 : Int))) (PreH11 : (ExtractedDigitCount x_pre m)) (PreH12 : (DigitPositionPower i power_ll)) (PreH13 : (AccumulatedDigitSumCorrect x_pre m ans)) (PreH14 : (DigitDPTable dp_l)) ,
  (OuterDigitPositionPower m power_ll)

noncomputable def prefix_digits_sum_entail_wit_8 : Prop :=
  (
forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (digits_l_2 : (List Int)) (ans : Int) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (i > (0 : Int))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= ans)) (PreH9 : (ans < 1000000007)) (PreH10 : ((Zlength (digits_l_2)) = 20)) (PreH11 : (ExtractedDigitBuffer x_pre digits_l_2 m (0 : Int))) (PreH12 : (ExtractedDigitCount x_pre m)) (PreH13 : (AccumulatedDigitSumCorrect x_pre i ans)) (PreH14 : (OuterDigitPositionPower i power_ll)) (PreH15 : (DigitDPTable dp_l)) ,
  (intArray.full dp_pre 200 dp_l)
  ** (intArray.full digits_pre 20 digits_l_2)
|--
  EX answer_before : Int, EX digits_l : (List Int),
  “ (1 <= x_pre) ” &&
  “ (x_pre <= 1000000000000000000) ” &&
  “ (tmpx = (0 : Int)) ” &&
  “ (1 <= i) ” &&
  “ (i <= m) ” &&
  “ (m <= 19) ” &&
  “ ((0 : Int) <= (Znth i digits_l (0 : Int))) ” &&
  “ ((Znth i digits_l (0 : Int)) < 10) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (Znth i digits_l (0 : Int))) ” &&
  “ ((0 : Int) <= ans) ” &&
  “ (ans < 1000000007) ” &&
  “ ((Zlength (digits_l)) = 20) ” &&
  “ (ExtractedDigitBuffer x_pre digits_l m (0 : Int)) ” &&
  “ (ExtractedDigitCount x_pre m) ” &&
  “ (InnerCandidateDigitProgress dp_l i (0 : Int) answer_before ans) ” &&
  “ (AccumulatedDigitSumCorrect x_pre i answer_before) ” &&
  “ (OuterDigitPositionPower i power_ll) ” &&
  “ (DigitDPTable dp_l) ”
  &&  (intArray.full dp_pre 200 dp_l)
  ** (intArray.full digits_pre 20 digits_l)
) \/
(
forall (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (digits_l_2 : (List Int)) (ans : Int) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (i > (0 : Int))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= ans)) (PreH9 : (ans < 1000000007)) (PreH10 : ((Zlength (digits_l_2)) = 20)) (PreH11 : (ExtractedDigitBuffer x_pre digits_l_2 m (0 : Int))) (PreH12 : (ExtractedDigitCount x_pre m)) (PreH13 : (AccumulatedDigitSumCorrect x_pre i ans)) (PreH14 : (OuterDigitPositionPower i power_ll)) (PreH15 : (DigitDPTable dp_l)) ,
  TT && emp 
|--
  EX answer_before : Int,
  “ (1 <= i) ” &&
  “ ((0 : Int) <= (Znth i digits_l_2 (0 : Int))) ” &&
  “ ((Znth i digits_l_2 (0 : Int)) < 10) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= (Znth i digits_l_2 (0 : Int))) ” &&
  “ (InnerCandidateDigitProgress dp_l i (0 : Int) answer_before ans) ” &&
  “ (AccumulatedDigitSumCorrect x_pre i answer_before) ”
  &&  emp
)

noncomputable def prefix_digits_sum_entail_wit_9 : Prop :=
  (
forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before_2 : Int) (ans : Int) (j : Int) (digits_l_2 : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j < (Znth i digits_l_2 (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l_2 (0 : Int)))) (PreH9 : ((Znth i digits_l_2 (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l_2 (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l_2)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l_2 m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before_2 ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before_2)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  (intArray.full dp_pre 200 dp_l)
  ** (intArray.full digits_pre 20 digits_l_2)
|--
  EX answer_before : Int, EX digits_l : (List Int),
  “ (1 <= x_pre) ” &&
  “ (x_pre <= 1000000000000000000) ” &&
  “ (tmpx = (0 : Int)) ” &&
  “ (1 <= i) ” &&
  “ (i <= m) ” &&
  “ (m <= 19) ” &&
  “ ((0 : Int) <= (Znth i digits_l (0 : Int))) ” &&
  “ ((Znth i digits_l (0 : Int)) < 10) ” &&
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= (Znth i digits_l (0 : Int))) ” &&
  “ ((0 : Int) <= (Z.rem (ans + (Znth ((i * 10) + j) dp_l (0 : Int))) 1000000007)) ” &&
  “ ((Z.rem (ans + (Znth ((i * 10) + j) dp_l (0 : Int))) 1000000007) < 1000000007) ” &&
  “ ((Zlength (digits_l)) = 20) ” &&
  “ (ExtractedDigitBuffer x_pre digits_l m (0 : Int)) ” &&
  “ (ExtractedDigitCount x_pre m) ” &&
  “ (InnerCandidateDigitProgress dp_l i (j + 1) answer_before (Z.rem (ans + (Znth ((i * 10) + j) dp_l (0 : Int))) 1000000007)) ” &&
  “ (AccumulatedDigitSumCorrect x_pre i answer_before) ” &&
  “ (OuterDigitPositionPower i power_ll) ” &&
  “ (DigitDPTable dp_l) ”
  &&  (intArray.full dp_pre 200 dp_l)
  ** (intArray.full digits_pre 20 digits_l)
) \/
(
forall (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before_2 : Int) (ans : Int) (j : Int) (digits_l_2 : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j < (Znth i digits_l_2 (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l_2 (0 : Int)))) (PreH9 : ((Znth i digits_l_2 (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l_2 (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l_2)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l_2 m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before_2 ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before_2)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  TT && emp 
|--
  EX answer_before : Int,
  “ ((0 : Int) <= (j + 1)) ” &&
  “ ((j + 1) <= (Znth i digits_l_2 (0 : Int))) ” &&
  “ ((0 : Int) <= (Z.rem (ans + (Znth ((i * 10) + j) dp_l (0 : Int))) 1000000007)) ” &&
  “ ((Z.rem (ans + (Znth ((i * 10) + j) dp_l (0 : Int))) 1000000007) < 1000000007) ” &&
  “ (InnerCandidateDigitProgress dp_l i (j + 1) answer_before (Z.rem (ans + (Znth ((i * 10) + j) dp_l (0 : Int))) 1000000007)) ” &&
  “ (AccumulatedDigitSumCorrect x_pre i answer_before) ”
  &&  emp
)

noncomputable def prefix_digits_sum_entail_wit_10 : Prop :=
  (
forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l_2 : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j >= (Znth i digits_l_2 (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l_2 (0 : Int)))) (PreH9 : ((Znth i digits_l_2 (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l_2 (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l_2)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l_2 m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  (intArray.full digits_pre 20 digits_l_2)
  ** (intArray.full dp_pre 200 dp_l)
|--
  EX digits_l : (List Int),
  “ (1 <= x_pre) ” &&
  “ (x_pre <= 1000000000000000000) ” &&
  “ (tmpx = (0 : Int)) ” &&
  “ ((0 : Int) <= (i - 1)) ” &&
  “ ((i - 1) <= m) ” &&
  “ (m <= 19) ” &&
  “ ((0 : Int) <= (signed_last_nbits ((Z.rem (ans + (Z.rem ((Z.rem ((Z.rem x_pre power_ll) + 1) 1000000007) * (Z.rem (Z.quot x_pre power_ll) 10)) 1000000007)) 1000000007)) (32))) ” &&
  “ ((signed_last_nbits ((Z.rem (ans + (Z.rem ((Z.rem ((Z.rem x_pre power_ll) + 1) 1000000007) * (Z.rem (Z.quot x_pre power_ll) 10)) 1000000007)) 1000000007)) (32)) < 1000000007) ” &&
  “ ((Zlength (digits_l)) = 20) ” &&
  “ (ExtractedDigitBuffer x_pre digits_l m (0 : Int)) ” &&
  “ (ExtractedDigitCount x_pre m) ” &&
  “ (AccumulatedDigitSumCorrect x_pre (i - 1) (signed_last_nbits ((Z.rem (ans + (Z.rem ((Z.rem ((Z.rem x_pre power_ll) + 1) 1000000007) * (Z.rem (Z.quot x_pre power_ll) 10)) 1000000007)) 1000000007)) (32))) ” &&
  “ (OuterDigitPositionPower (i - 1) (Z.quot power_ll 10)) ” &&
  “ (DigitDPTable dp_l) ”
  &&  (intArray.full dp_pre 200 dp_l)
  ** (intArray.full digits_pre 20 digits_l)
) \/
(
forall (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l_2 : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j >= (Znth i digits_l_2 (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l_2 (0 : Int)))) (PreH9 : ((Znth i digits_l_2 (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l_2 (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l_2)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l_2 m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  TT && emp 
|--
  “ (OuterDigitPositionPower (i - 1) (Z.quot power_ll 10)) ” &&
  “ (AccumulatedDigitSumCorrect x_pre (i - 1) (signed_last_nbits ((Z.rem (ans + (Z.rem ((Z.rem ((Z.rem x_pre power_ll) + 1) 1000000007) * (Z.rem (Z.quot x_pre power_ll) 10)) 1000000007)) 1000000007)) (32))) ” &&
  “ ((signed_last_nbits ((Z.rem (ans + (Z.rem ((Z.rem ((Z.rem x_pre power_ll) + 1) 1000000007) * (Z.rem (Z.quot x_pre power_ll) 10)) 1000000007)) 1000000007)) (32)) < 1000000007) ” &&
  “ ((0 : Int) <= (signed_last_nbits ((Z.rem (ans + (Z.rem ((Z.rem ((Z.rem x_pre power_ll) + 1) 1000000007) * (Z.rem (Z.quot x_pre power_ll) 10)) 1000000007)) 1000000007)) (32))) ”
  &&  emp
)

noncomputable def prefix_digits_sum_entail_wit_10_split_goal_1 : Prop :=
  forall (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l_2 : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j >= (Znth i digits_l_2 (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l_2 (0 : Int)))) (PreH9 : ((Znth i digits_l_2 (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l_2 (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l_2)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l_2 m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  (OuterDigitPositionPower (i - 1) (Z.quot power_ll 10))

noncomputable def prefix_digits_sum_entail_wit_10_split_goal_2 : Prop :=
  forall (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l_2 : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j >= (Znth i digits_l_2 (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l_2 (0 : Int)))) (PreH9 : ((Znth i digits_l_2 (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l_2 (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l_2)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l_2 m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  (AccumulatedDigitSumCorrect x_pre (i - 1) (signed_last_nbits ((Z.rem (ans + (Z.rem ((Z.rem ((Z.rem x_pre power_ll) + 1) 1000000007) * (Z.rem (Z.quot x_pre power_ll) 10)) 1000000007)) 1000000007)) (32)))

noncomputable def prefix_digits_sum_entail_wit_10_split_goal_3 : Prop :=
  forall (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l_2 : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j >= (Znth i digits_l_2 (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l_2 (0 : Int)))) (PreH9 : ((Znth i digits_l_2 (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l_2 (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l_2)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l_2 m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  ((signed_last_nbits ((Z.rem (ans + (Z.rem ((Z.rem ((Z.rem x_pre power_ll) + 1) 1000000007) * (Z.rem (Z.quot x_pre power_ll) 10)) 1000000007)) 1000000007)) (32)) < 1000000007)

noncomputable def prefix_digits_sum_entail_wit_10_split_goal_4 : Prop :=
  forall (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l_2 : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j >= (Znth i digits_l_2 (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l_2 (0 : Int)))) (PreH9 : ((Znth i digits_l_2 (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l_2 (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l_2)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l_2 m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  ((0 : Int) <= (signed_last_nbits ((Z.rem (ans + (Z.rem ((Z.rem ((Z.rem x_pre power_ll) + 1) 1000000007) * (Z.rem (Z.quot x_pre power_ll) 10)) 1000000007)) 1000000007)) (32)))

noncomputable def prefix_digits_sum_return_wit_1 : Prop :=
  (
forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (digits_l : (List Int)) (ans : Int) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (i <= (0 : Int))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= ans)) (PreH9 : (ans < 1000000007)) (PreH10 : ((Zlength (digits_l)) = 20)) (PreH11 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH12 : (ExtractedDigitCount x_pre m)) (PreH13 : (AccumulatedDigitSumCorrect x_pre i ans)) (PreH14 : (OuterDigitPositionPower i power_ll)) (PreH15 : (DigitDPTable dp_l)) ,
  (intArray.full dp_pre 200 dp_l)
  ** (intArray.full digits_pre 20 digits_l)
|--
  “ (PrefixDigitSum x_pre ans) ”
  &&  (intArray.full dp_pre 200 dp_l)
  ** (intArray.undef_full digits_pre 20)
) \/
(
forall (digits_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (digits_l : (List Int)) (ans : Int) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (i <= (0 : Int))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= ans)) (PreH9 : (ans < 1000000007)) (PreH10 : ((Zlength (digits_l)) = 20)) (PreH11 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH12 : (ExtractedDigitCount x_pre m)) (PreH13 : (AccumulatedDigitSumCorrect x_pre i ans)) (PreH14 : (OuterDigitPositionPower i power_ll)) (PreH15 : (DigitDPTable dp_l)) ,
  (intArray.full digits_pre 20 digits_l)
|--
  “ (PrefixDigitSum x_pre ans) ”
  &&  (intArray.undef_full digits_pre 20)
)

noncomputable def prefix_digits_sum_return_wit_1_split_goal_1 : Prop :=
  forall (digits_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (digits_l : (List Int)) (ans : Int) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (i <= (0 : Int))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= ans)) (PreH9 : (ans < 1000000007)) (PreH10 : ((Zlength (digits_l)) = 20)) (PreH11 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH12 : (ExtractedDigitCount x_pre m)) (PreH13 : (AccumulatedDigitSumCorrect x_pre i ans)) (PreH14 : (OuterDigitPositionPower i power_ll)) (PreH15 : (DigitDPTable dp_l)) ,
  (intArray.full digits_pre 20 digits_l)
|--
  “ (PrefixDigitSum x_pre ans) ”

noncomputable def prefix_digits_sum_return_wit_1_split_goal_spatial : Prop :=
  forall (digits_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (digits_l : (List Int)) (ans : Int) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (i <= (0 : Int))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : ((0 : Int) <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= ans)) (PreH9 : (ans < 1000000007)) (PreH10 : ((Zlength (digits_l)) = 20)) (PreH11 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH12 : (ExtractedDigitCount x_pre m)) (PreH13 : (AccumulatedDigitSumCorrect x_pre i ans)) (PreH14 : (OuterDigitPositionPower i power_ll)) (PreH15 : (DigitDPTable dp_l)) ,
  (intArray.full digits_pre 20 digits_l)
|--
  (intArray.undef_full digits_pre 20)

noncomputable def prefix_digits_sum_return_wit_2 : Prop :=
  (
forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (PreH1 : (x_pre < 1)) (PreH2 : ((0 : Int) <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (DigitDPTable dp_l)) ,
  (intArray.full dp_pre 200 dp_l)
  ** (intArray.undef_full digits_pre 20)
|--
  “ (PrefixDigitSum x_pre (0 : Int)) ”
  &&  (intArray.full dp_pre 200 dp_l)
  ** (intArray.undef_full digits_pre 20)
) \/
(
forall (x_pre : Int) (dp_l : (List Int)) (PreH1 : (x_pre < 1)) (PreH2 : ((0 : Int) <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (DigitDPTable dp_l)) ,
  TT && emp 
|--
  “ (PrefixDigitSum x_pre (0 : Int)) ”
  &&  emp
)

noncomputable def prefix_digits_sum_return_wit_2_split_goal_1 : Prop :=
  forall (x_pre : Int) (dp_l : (List Int)) (PreH1 : (x_pre < 1)) (PreH2 : ((0 : Int) <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (DigitDPTable dp_l)) ,
  (PrefixDigitSum x_pre (0 : Int))

noncomputable def prefix_digits_sum_partial_solve_wit_1 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (digits_l : (List Int)) (i : Int) (power_ll : Int) (ans : Int) (m : Int) (PreH1 : (i < 20)) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (m = (0 : Int))) (PreH5 : (ans = (0 : Int))) (PreH6 : (power_ll = 1)) (PreH7 : ((0 : Int) <= i)) (PreH8 : (i <= 20)) (PreH9 : ((Zlength (digits_l)) = i)) (PreH10 : (Forall (Eq ((0 : Int))) digits_l)) (PreH11 : (DigitDPTable dp_l)) ,
  (intArray.full dp_pre 200 dp_l)
  ** (intArray.seg digits_pre (0 : Int) i digits_l)
  ** (intArray.undef_seg digits_pre i 20)
|--
  “ (i < 20) ” &&
  “ (1 <= x_pre) ” &&
  “ (x_pre <= 1000000000000000000) ” &&
  “ (m = (0 : Int)) ” &&
  “ (ans = (0 : Int)) ” &&
  “ (power_ll = 1) ” &&
  “ ((0 : Int) <= i) ” &&
  “ (i <= 20) ” &&
  “ ((Zlength (digits_l)) = i) ” &&
  “ (Forall (Eq ((0 : Int))) digits_l) ” &&
  “ (DigitDPTable dp_l) ”
  &&  (((digits_pre + (i * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_seg digits_pre (i + 1) 20)
  ** (intArray.full dp_pre 200 dp_l)
  ** (intArray.seg digits_pre (0 : Int) i digits_l)

noncomputable def prefix_digits_sum_partial_solve_wit_2 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (digits_l : (List Int)) (tmpx : Int) (m : Int) (power_ll : Int) (ans : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (ans = (0 : Int))) (PreH4 : (power_ll = 1)) (PreH5 : ((0 : Int) <= m)) (PreH6 : (m <= 19)) (PreH7 : (tmpx >= (0 : Int))) (PreH8 : ((tmpx ≠ (0 : Int)) -> (m < 19))) (PreH9 : ((tmpx = (0 : Int)) -> (1 <= m))) (PreH10 : ((tmpx = (0 : Int)) -> (ExtractedDigitCount x_pre m))) (PreH11 : ((Zlength (digits_l)) = 20)) (PreH12 : (ExtractedDigitBuffer x_pre digits_l m tmpx)) (PreH13 : (DigitDPTable dp_l)) (PreH14 : (tmpx ≠ (0 : Int))) ,
  (intArray.full dp_pre 200 dp_l)
  ** (intArray.full digits_pre 20 digits_l)
|--
  “ (1 <= x_pre) ” &&
  “ (x_pre <= 1000000000000000000) ” &&
  “ (ans = (0 : Int)) ” &&
  “ (power_ll = 1) ” &&
  “ ((0 : Int) <= m) ” &&
  “ (m <= 19) ” &&
  “ (tmpx >= (0 : Int)) ” &&
  “ ((tmpx ≠ (0 : Int)) -> (m < 19)) ” &&
  “ ((tmpx = (0 : Int)) -> (1 <= m)) ” &&
  “ ((tmpx = (0 : Int)) -> (ExtractedDigitCount x_pre m)) ” &&
  “ ((Zlength (digits_l)) = 20) ” &&
  “ (ExtractedDigitBuffer x_pre digits_l m tmpx) ” &&
  “ (DigitDPTable dp_l) ” &&
  “ (tmpx ≠ (0 : Int)) ”
  &&  (((digits_pre + ((m + 1) * sizeof(INT)))) # Int |->_)
  ** (intArray.missing_i digits_pre (m + 1) (0 : Int) 20 digits_l)
  ** (intArray.full dp_pre 200 dp_l)

noncomputable def prefix_digits_sum_partial_solve_wit_3 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= 1000000000000000000)) (PreH3 : (tmpx = (0 : Int))) (PreH4 : (1 <= i)) (PreH5 : (i <= m)) (PreH6 : (m <= 19)) (PreH7 : ((0 : Int) <= (Znth i digits_l (0 : Int)))) (PreH8 : ((Znth i digits_l (0 : Int)) < 10)) (PreH9 : ((0 : Int) <= j)) (PreH10 : (j <= (Znth i digits_l (0 : Int)))) (PreH11 : ((0 : Int) <= ans)) (PreH12 : (ans < 1000000007)) (PreH13 : ((Zlength (digits_l)) = 20)) (PreH14 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH15 : (ExtractedDigitCount x_pre m)) (PreH16 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH17 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH18 : (OuterDigitPositionPower i power_ll)) (PreH19 : (DigitDPTable dp_l)) ,
  (intArray.full dp_pre 200 dp_l)
  ** (intArray.full digits_pre 20 digits_l)
|--
  “ (1 <= x_pre) ” &&
  “ (x_pre <= 1000000000000000000) ” &&
  “ (tmpx = (0 : Int)) ” &&
  “ (1 <= i) ” &&
  “ (i <= m) ” &&
  “ (m <= 19) ” &&
  “ ((0 : Int) <= (Znth i digits_l (0 : Int))) ” &&
  “ ((Znth i digits_l (0 : Int)) < 10) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (Znth i digits_l (0 : Int))) ” &&
  “ ((0 : Int) <= ans) ” &&
  “ (ans < 1000000007) ” &&
  “ ((Zlength (digits_l)) = 20) ” &&
  “ (ExtractedDigitBuffer x_pre digits_l m (0 : Int)) ” &&
  “ (ExtractedDigitCount x_pre m) ” &&
  “ (InnerCandidateDigitProgress dp_l i j answer_before ans) ” &&
  “ (AccumulatedDigitSumCorrect x_pre i answer_before) ” &&
  “ (OuterDigitPositionPower i power_ll) ” &&
  “ (DigitDPTable dp_l) ”
  &&  (((digits_pre + (i * sizeof(INT)))) # Int |-> ((Znth i digits_l (0 : Int))))
  ** (intArray.missing_i digits_pre i (0 : Int) 20 digits_l)
  ** (intArray.full dp_pre 200 dp_l)

noncomputable def prefix_digits_sum_partial_solve_wit_4 : Prop :=
  forall (digits_pre : Int) (dp_pre : Int) (x_pre : Int) (dp_l : (List Int)) (power_ll : Int) (answer_before : Int) (ans : Int) (j : Int) (digits_l : (List Int)) (m : Int) (i : Int) (tmpx : Int) (PreH1 : (j < (Znth i digits_l (0 : Int)))) (PreH2 : (1 <= x_pre)) (PreH3 : (x_pre <= 1000000000000000000)) (PreH4 : (tmpx = (0 : Int))) (PreH5 : (1 <= i)) (PreH6 : (i <= m)) (PreH7 : (m <= 19)) (PreH8 : ((0 : Int) <= (Znth i digits_l (0 : Int)))) (PreH9 : ((Znth i digits_l (0 : Int)) < 10)) (PreH10 : ((0 : Int) <= j)) (PreH11 : (j <= (Znth i digits_l (0 : Int)))) (PreH12 : ((0 : Int) <= ans)) (PreH13 : (ans < 1000000007)) (PreH14 : ((Zlength (digits_l)) = 20)) (PreH15 : (ExtractedDigitBuffer x_pre digits_l m (0 : Int))) (PreH16 : (ExtractedDigitCount x_pre m)) (PreH17 : (InnerCandidateDigitProgress dp_l i j answer_before ans)) (PreH18 : (AccumulatedDigitSumCorrect x_pre i answer_before)) (PreH19 : (OuterDigitPositionPower i power_ll)) (PreH20 : (DigitDPTable dp_l)) ,
  (intArray.full digits_pre 20 digits_l)
  ** (intArray.full dp_pre 200 dp_l)
|--
  “ (j < (Znth i digits_l (0 : Int))) ” &&
  “ (1 <= x_pre) ” &&
  “ (x_pre <= 1000000000000000000) ” &&
  “ (tmpx = (0 : Int)) ” &&
  “ (1 <= i) ” &&
  “ (i <= m) ” &&
  “ (m <= 19) ” &&
  “ ((0 : Int) <= (Znth i digits_l (0 : Int))) ” &&
  “ ((Znth i digits_l (0 : Int)) < 10) ” &&
  “ ((0 : Int) <= j) ” &&
  “ (j <= (Znth i digits_l (0 : Int))) ” &&
  “ ((0 : Int) <= ans) ” &&
  “ (ans < 1000000007) ” &&
  “ ((Zlength (digits_l)) = 20) ” &&
  “ (ExtractedDigitBuffer x_pre digits_l m (0 : Int)) ” &&
  “ (ExtractedDigitCount x_pre m) ” &&
  “ (InnerCandidateDigitProgress dp_l i j answer_before ans) ” &&
  “ (AccumulatedDigitSumCorrect x_pre i answer_before) ” &&
  “ (OuterDigitPositionPower i power_ll) ” &&
  “ (DigitDPTable dp_l) ”
  &&  (((dp_pre + (((i * 10) + j) * sizeof(INT)))) # Int |-> ((Znth ((i * 10) + j) dp_l (0 : Int))))
  ** (intArray.missing_i dp_pre ((i * 10) + j) (0 : Int) 200 dp_l)
  ** (intArray.full digits_pre 20 digits_l)

noncomputable def interval_digits_sum_safety_wit_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= y_pre)) (PreH3 : (y_pre <= 1000000000000000000)) ,
  ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "y" ) )) # Int64 |-> (y_pre))
  ** (intArray.undef_full (( &( "dp" ) ) + ((0 : Int) * sizeof(INT))) 200)
  ** (intArray.undef_full (( &( "power" ) ) + ((0 : Int) * sizeof(INT))) 20)
  ** (intArray.undef_full (( &( "digits" ) ) + ((0 : Int) * sizeof(INT))) 20)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def interval_digits_sum_safety_wit_2 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= y_pre)) (PreH3 : (y_pre <= 1000000000000000000)) ,
  ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "y" ) )) # Int64 |-> (y_pre))
  ** (intArray.undef_full (( &( "dp" ) ) + ((0 : Int) * sizeof(INT))) 200)
  ** (intArray.undef_full (( &( "power" ) ) + ((0 : Int) * sizeof(INT))) 20)
  ** (intArray.undef_full (( &( "digits" ) ) + ((0 : Int) * sizeof(INT))) 20)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def interval_digits_sum_safety_wit_3 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (PreH1 : (DigitDPTable dp_l)) (PreH2 : (PowerTable power_l)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= y_pre)) (PreH5 : (y_pre <= 1000000000000000000)) ,
  ((( &( "ans1" ) )) # Int |->_)
  ** (intArray.full (( &( "dp" ) ) + ((0 : Int) * sizeof(INT))) 200 dp_l)
  ** (intArray.full (( &( "power" ) ) + ((0 : Int) * sizeof(INT))) 20 power_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "y" ) )) # Int64 |-> (y_pre))
  ** (intArray.undef_full (( &( "digits" ) ) + ((0 : Int) * sizeof(INT))) 20)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def interval_digits_sum_safety_wit_4 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (PreH1 : (DigitDPTable dp_l)) (PreH2 : (PowerTable power_l)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= y_pre)) (PreH5 : (y_pre <= 1000000000000000000)) ,
  ((( &( "ans1" ) )) # Int |->_)
  ** (intArray.full (( &( "dp" ) ) + ((0 : Int) * sizeof(INT))) 200 dp_l)
  ** (intArray.full (( &( "power" ) ) + ((0 : Int) * sizeof(INT))) 20 power_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "y" ) )) # Int64 |-> (y_pre))
  ** (intArray.undef_full (( &( "digits" ) ) + ((0 : Int) * sizeof(INT))) 20)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def interval_digits_sum_safety_wit_5 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (retval : Int) (PreH1 : (PrefixDigitSum y_pre retval)) (PreH2 : (DigitDPTable dp_l)) (PreH3 : (PowerTable power_l)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre <= y_pre)) (PreH6 : (y_pre <= 1000000000000000000)) ,
  ((( &( "ans2" ) )) # Int |->_)
  ** (intArray.full (( &( "dp" ) ) + ((0 : Int) * sizeof(INT))) 200 dp_l)
  ** (intArray.undef_full (( &( "digits" ) ) + ((0 : Int) * sizeof(INT))) 20)
  ** ((( &( "ans1" ) )) # Int |-> (retval))
  ** (intArray.full (( &( "power" ) ) + ((0 : Int) * sizeof(INT))) 20 power_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "y" ) )) # Int64 |-> (y_pre))
|--
  “ ((x_pre - 1) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (x_pre - 1)) ”

noncomputable def interval_digits_sum_safety_wit_6 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (retval : Int) (PreH1 : (PrefixDigitSum y_pre retval)) (PreH2 : (DigitDPTable dp_l)) (PreH3 : (PowerTable power_l)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre <= y_pre)) (PreH6 : (y_pre <= 1000000000000000000)) ,
  ((( &( "ans2" ) )) # Int |->_)
  ** (intArray.full (( &( "dp" ) ) + ((0 : Int) * sizeof(INT))) 200 dp_l)
  ** (intArray.undef_full (( &( "digits" ) ) + ((0 : Int) * sizeof(INT))) 20)
  ** ((( &( "ans1" ) )) # Int |-> (retval))
  ** (intArray.full (( &( "power" ) ) + ((0 : Int) * sizeof(INT))) 20 power_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "y" ) )) # Int64 |-> (y_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def interval_digits_sum_safety_wit_7 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (retval : Int) (PreH1 : (PrefixDigitSum y_pre retval)) (PreH2 : (DigitDPTable dp_l)) (PreH3 : (PowerTable power_l)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre <= y_pre)) (PreH6 : (y_pre <= 1000000000000000000)) ,
  ((( &( "ans2" ) )) # Int |->_)
  ** (intArray.full (( &( "dp" ) ) + ((0 : Int) * sizeof(INT))) 200 dp_l)
  ** (intArray.undef_full (( &( "digits" ) ) + ((0 : Int) * sizeof(INT))) 20)
  ** ((( &( "ans1" ) )) # Int |-> (retval))
  ** (intArray.full (( &( "power" ) ) + ((0 : Int) * sizeof(INT))) 20 power_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "y" ) )) # Int64 |-> (y_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def interval_digits_sum_safety_wit_8 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (retval : Int) (PreH1 : (PrefixDigitSum y_pre retval)) (PreH2 : (DigitDPTable dp_l)) (PreH3 : (PowerTable power_l)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre <= y_pre)) (PreH6 : (y_pre <= 1000000000000000000)) ,
  ((( &( "ans2" ) )) # Int |->_)
  ** (intArray.full (( &( "dp" ) ) + ((0 : Int) * sizeof(INT))) 200 dp_l)
  ** (intArray.undef_full (( &( "digits" ) ) + ((0 : Int) * sizeof(INT))) 20)
  ** ((( &( "ans1" ) )) # Int |-> (retval))
  ** (intArray.full (( &( "power" ) ) + ((0 : Int) * sizeof(INT))) 20 power_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "y" ) )) # Int64 |-> (y_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def interval_digits_sum_safety_wit_9 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (ans1 : Int) (ans2 : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= y_pre)) (PreH3 : (y_pre <= 1000000000000000000)) (PreH4 : (PrefixDigitSum y_pre ans1)) (PreH5 : (PrefixDigitSum (x_pre - 1) ans2)) ,
  ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "y" ) )) # Int64 |-> (y_pre))
  ** ((( &( "ans1" ) )) # Int |-> (ans1))
  ** ((( &( "ans2" ) )) # Int |-> (ans2))
  ** (intArray.undef_full ( &( "dp" ) ) 200)
  ** (intArray.undef_full ( &( "power" ) ) 20)
  ** (intArray.undef_full ( &( "digits" ) ) 20)
|--
  “ ((((Z.rem (ans1 - ans2) 1000000007) + 1000000007) ≠ (INT_MIN)) ∨ (1000000007 ≠ (-1))) ” &&
  “ (1000000007 ≠ (0 : Int)) ”

noncomputable def interval_digits_sum_safety_wit_10 : Prop :=
  (
forall (y_pre : Int) (x_pre : Int) (ans1 : Int) (ans2 : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= y_pre)) (PreH3 : (y_pre <= 1000000000000000000)) (PreH4 : (PrefixDigitSum y_pre ans1)) (PreH5 : (PrefixDigitSum (x_pre - 1) ans2)) ,
  ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "y" ) )) # Int64 |-> (y_pre))
  ** ((( &( "ans1" ) )) # Int |-> (ans1))
  ** ((( &( "ans2" ) )) # Int |-> (ans2))
  ** (intArray.undef_full ( &( "dp" ) ) 200)
  ** (intArray.undef_full ( &( "power" ) ) 20)
  ** (intArray.undef_full ( &( "digits" ) ) 20)
|--
  “ (((Z.rem (ans1 - ans2) 1000000007) + 1000000007) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Z.rem (ans1 - ans2) 1000000007) + 1000000007)) ”
) \/
(
forall (y_pre : Int) (x_pre : Int) (ans1 : Int) (ans2 : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= y_pre)) (PreH3 : (y_pre <= 1000000000000000000)) (PreH4 : (PrefixDigitSum y_pre ans1)) (PreH5 : (PrefixDigitSum (x_pre - 1) ans2)) ,
  ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "y" ) )) # Int64 |-> (y_pre))
  ** ((( &( "ans1" ) )) # Int |-> (ans1))
  ** ((( &( "ans2" ) )) # Int |-> (ans2))
  ** (intArray.undef_full ( &( "dp" ) ) 200)
  ** (intArray.undef_full ( &( "power" ) ) 20)
  ** (intArray.undef_full ( &( "digits" ) ) 20)
|--
  “ (((Z.rem (ans1 - ans2) 1000000007) + 1000000007) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((Z.rem (ans1 - ans2) 1000000007) + 1000000007)) ”
)

noncomputable def interval_digits_sum_safety_wit_10_split_goal_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (ans1 : Int) (ans2 : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= y_pre)) (PreH3 : (y_pre <= 1000000000000000000)) (PreH4 : (PrefixDigitSum y_pre ans1)) (PreH5 : (PrefixDigitSum (x_pre - 1) ans2)) ,
  ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "y" ) )) # Int64 |-> (y_pre))
  ** ((( &( "ans1" ) )) # Int |-> (ans1))
  ** ((( &( "ans2" ) )) # Int |-> (ans2))
  ** (intArray.undef_full ( &( "dp" ) ) 200)
  ** (intArray.undef_full ( &( "power" ) ) 20)
  ** (intArray.undef_full ( &( "digits" ) ) 20)
|--
  “ (((Z.rem (ans1 - ans2) 1000000007) + 1000000007) <= INT_MAX) ”

noncomputable def interval_digits_sum_safety_wit_10_split_goal_2 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (ans1 : Int) (ans2 : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= y_pre)) (PreH3 : (y_pre <= 1000000000000000000)) (PreH4 : (PrefixDigitSum y_pre ans1)) (PreH5 : (PrefixDigitSum (x_pre - 1) ans2)) ,
  ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "y" ) )) # Int64 |-> (y_pre))
  ** ((( &( "ans1" ) )) # Int |-> (ans1))
  ** ((( &( "ans2" ) )) # Int |-> (ans2))
  ** (intArray.undef_full ( &( "dp" ) ) 200)
  ** (intArray.undef_full ( &( "power" ) ) 20)
  ** (intArray.undef_full ( &( "digits" ) ) 20)
|--
  “ ((INT_MIN) <= ((Z.rem (ans1 - ans2) 1000000007) + 1000000007)) ”

noncomputable def interval_digits_sum_safety_wit_11 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (ans1 : Int) (ans2 : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= y_pre)) (PreH3 : (y_pre <= 1000000000000000000)) (PreH4 : (PrefixDigitSum y_pre ans1)) (PreH5 : (PrefixDigitSum (x_pre - 1) ans2)) ,
  ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "y" ) )) # Int64 |-> (y_pre))
  ** ((( &( "ans1" ) )) # Int |-> (ans1))
  ** ((( &( "ans2" ) )) # Int |-> (ans2))
  ** (intArray.undef_full ( &( "dp" ) ) 200)
  ** (intArray.undef_full ( &( "power" ) ) 20)
  ** (intArray.undef_full ( &( "digits" ) ) 20)
|--
  “ (((ans1 - ans2) ≠ (INT_MIN)) ∨ (1000000007 ≠ (-1))) ” &&
  “ (1000000007 ≠ (0 : Int)) ”

noncomputable def interval_digits_sum_safety_wit_12 : Prop :=
  (
forall (y_pre : Int) (x_pre : Int) (ans1 : Int) (ans2 : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= y_pre)) (PreH3 : (y_pre <= 1000000000000000000)) (PreH4 : (PrefixDigitSum y_pre ans1)) (PreH5 : (PrefixDigitSum (x_pre - 1) ans2)) ,
  ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "y" ) )) # Int64 |-> (y_pre))
  ** ((( &( "ans1" ) )) # Int |-> (ans1))
  ** ((( &( "ans2" ) )) # Int |-> (ans2))
  ** (intArray.undef_full ( &( "dp" ) ) 200)
  ** (intArray.undef_full ( &( "power" ) ) 20)
  ** (intArray.undef_full ( &( "digits" ) ) 20)
|--
  “ ((ans1 - ans2) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (ans1 - ans2)) ”
) \/
(
forall (y_pre : Int) (x_pre : Int) (ans1 : Int) (ans2 : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= y_pre)) (PreH3 : (y_pre <= 1000000000000000000)) (PreH4 : (PrefixDigitSum y_pre ans1)) (PreH5 : (PrefixDigitSum (x_pre - 1) ans2)) ,
  ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "y" ) )) # Int64 |-> (y_pre))
  ** ((( &( "ans1" ) )) # Int |-> (ans1))
  ** ((( &( "ans2" ) )) # Int |-> (ans2))
  ** (intArray.undef_full ( &( "dp" ) ) 200)
  ** (intArray.undef_full ( &( "power" ) ) 20)
  ** (intArray.undef_full ( &( "digits" ) ) 20)
|--
  “ ((ans1 - ans2) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (ans1 - ans2)) ”
)

noncomputable def interval_digits_sum_safety_wit_12_split_goal_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (ans1 : Int) (ans2 : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= y_pre)) (PreH3 : (y_pre <= 1000000000000000000)) (PreH4 : (PrefixDigitSum y_pre ans1)) (PreH5 : (PrefixDigitSum (x_pre - 1) ans2)) ,
  ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "y" ) )) # Int64 |-> (y_pre))
  ** ((( &( "ans1" ) )) # Int |-> (ans1))
  ** ((( &( "ans2" ) )) # Int |-> (ans2))
  ** (intArray.undef_full ( &( "dp" ) ) 200)
  ** (intArray.undef_full ( &( "power" ) ) 20)
  ** (intArray.undef_full ( &( "digits" ) ) 20)
|--
  “ ((ans1 - ans2) <= INT_MAX) ”

noncomputable def interval_digits_sum_safety_wit_12_split_goal_2 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (ans1 : Int) (ans2 : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= y_pre)) (PreH3 : (y_pre <= 1000000000000000000)) (PreH4 : (PrefixDigitSum y_pre ans1)) (PreH5 : (PrefixDigitSum (x_pre - 1) ans2)) ,
  ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "y" ) )) # Int64 |-> (y_pre))
  ** ((( &( "ans1" ) )) # Int |-> (ans1))
  ** ((( &( "ans2" ) )) # Int |-> (ans2))
  ** (intArray.undef_full ( &( "dp" ) ) 200)
  ** (intArray.undef_full ( &( "power" ) ) 20)
  ** (intArray.undef_full ( &( "digits" ) ) 20)
|--
  “ ((INT_MIN) <= (ans1 - ans2)) ”

noncomputable def interval_digits_sum_safety_wit_13 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (ans1 : Int) (ans2 : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= y_pre)) (PreH3 : (y_pre <= 1000000000000000000)) (PreH4 : (PrefixDigitSum y_pre ans1)) (PreH5 : (PrefixDigitSum (x_pre - 1) ans2)) ,
  ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "y" ) )) # Int64 |-> (y_pre))
  ** ((( &( "ans1" ) )) # Int |-> (ans1))
  ** ((( &( "ans2" ) )) # Int |-> (ans2))
  ** (intArray.undef_full ( &( "dp" ) ) 200)
  ** (intArray.undef_full ( &( "power" ) ) 20)
  ** (intArray.undef_full ( &( "digits" ) ) 20)
|--
  “ (1000000007 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1000000007) ”

noncomputable def interval_digits_sum_safety_wit_14 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (ans1 : Int) (ans2 : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= y_pre)) (PreH3 : (y_pre <= 1000000000000000000)) (PreH4 : (PrefixDigitSum y_pre ans1)) (PreH5 : (PrefixDigitSum (x_pre - 1) ans2)) ,
  ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "y" ) )) # Int64 |-> (y_pre))
  ** ((( &( "ans1" ) )) # Int |-> (ans1))
  ** ((( &( "ans2" ) )) # Int |-> (ans2))
  ** (intArray.undef_full ( &( "dp" ) ) 200)
  ** (intArray.undef_full ( &( "power" ) ) 20)
  ** (intArray.undef_full ( &( "digits" ) ) 20)
|--
  “ (1000000007 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1000000007) ”

noncomputable def interval_digits_sum_safety_wit_15 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (ans1 : Int) (ans2 : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= y_pre)) (PreH3 : (y_pre <= 1000000000000000000)) (PreH4 : (PrefixDigitSum y_pre ans1)) (PreH5 : (PrefixDigitSum (x_pre - 1) ans2)) ,
  ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "y" ) )) # Int64 |-> (y_pre))
  ** ((( &( "ans1" ) )) # Int |-> (ans1))
  ** ((( &( "ans2" ) )) # Int |-> (ans2))
  ** (intArray.undef_full ( &( "dp" ) ) 200)
  ** (intArray.undef_full ( &( "power" ) ) 20)
  ** (intArray.undef_full ( &( "digits" ) ) 20)
|--
  “ (1000000007 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1000000007) ”

noncomputable def interval_digits_sum_entail_wit_1 : Prop :=
  (
forall (y_pre : Int) (x_pre : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= y_pre)) (PreH3 : (y_pre <= 1000000000000000000)) ,
  (intArray.undef_full ( &( "digits" ) ) 20)
  ** (intArray.undef_full ( &( "power" ) ) 20)
  ** (intArray.undef_full ( &( "dp" ) ) 200)
|--
  “ (1 <= x_pre) ” &&
  “ (x_pre <= y_pre) ” &&
  “ (y_pre <= 1000000000000000000) ”
  &&  (intArray.undef_full (( &( "dp" ) ) + ((0 : Int) * sizeof(INT))) 200)
  ** (intArray.undef_full (( &( "power" ) ) + ((0 : Int) * sizeof(INT))) 20)
  ** (intArray.undef_full (( &( "digits" ) ) + ((0 : Int) * sizeof(INT))) 20)
) \/
(
forall (y_pre : Int) (x_pre : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= y_pre)) (PreH3 : (y_pre <= 1000000000000000000)) ,
  (intArray.undef_full ( &( "digits" ) ) 20)
  ** (intArray.undef_full ( &( "power" ) ) 20)
  ** (intArray.undef_full ( &( "dp" ) ) 200)
|--
  (intArray.undef_full (( &( "dp" ) ) + ((0 : Int) * sizeof(INT))) 200)
  ** (intArray.undef_full (( &( "power" ) ) + ((0 : Int) * sizeof(INT))) 20)
  ** (intArray.undef_full (( &( "digits" ) ) + ((0 : Int) * sizeof(INT))) 20)
)

noncomputable def interval_digits_sum_entail_wit_1_split_goal_spatial : Prop :=
  forall (y_pre : Int) (x_pre : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= y_pre)) (PreH3 : (y_pre <= 1000000000000000000)) ,
  (intArray.undef_full ( &( "digits" ) ) 20)
  ** (intArray.undef_full ( &( "power" ) ) 20)
  ** (intArray.undef_full ( &( "dp" ) ) 200)
|--
  (intArray.undef_full (( &( "dp" ) ) + ((0 : Int) * sizeof(INT))) 200)
  ** (intArray.undef_full (( &( "power" ) ) + ((0 : Int) * sizeof(INT))) 20)
  ** (intArray.undef_full (( &( "digits" ) ) + ((0 : Int) * sizeof(INT))) 20)

noncomputable def interval_digits_sum_entail_wit_2 : Prop :=
  (
forall (y_pre : Int) (x_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (retval : Int) (retval_2 : Int) (PreH1 : (PrefixDigitSum (x_pre - 1) retval_2)) (PreH2 : (PrefixDigitSum y_pre retval)) (PreH3 : (DigitDPTable dp_l)) (PreH4 : (PowerTable power_l)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre <= y_pre)) (PreH7 : (y_pre <= 1000000000000000000)) ,
  (intArray.full (( &( "dp" ) ) + ((0 : Int) * sizeof(INT))) 200 dp_l)
  ** (intArray.undef_full (( &( "digits" ) ) + ((0 : Int) * sizeof(INT))) 20)
  ** (intArray.full (( &( "power" ) ) + ((0 : Int) * sizeof(INT))) 20 power_l)
|--
  “ (1 <= x_pre) ” &&
  “ (x_pre <= y_pre) ” &&
  “ (y_pre <= 1000000000000000000) ” &&
  “ (PrefixDigitSum y_pre retval) ” &&
  “ (PrefixDigitSum (x_pre - 1) retval_2) ”
  &&  (intArray.undef_full ( &( "dp" ) ) 200)
  ** (intArray.undef_full ( &( "power" ) ) 20)
  ** (intArray.undef_full ( &( "digits" ) ) 20)
) \/
(
forall (y_pre : Int) (x_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (retval : Int) (retval_2 : Int) (PreH1 : (PrefixDigitSum (x_pre - 1) retval_2)) (PreH2 : (PrefixDigitSum y_pre retval)) (PreH3 : (DigitDPTable dp_l)) (PreH4 : (PowerTable power_l)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre <= y_pre)) (PreH7 : (y_pre <= 1000000000000000000)) ,
  (intArray.full (( &( "dp" ) ) + ((0 : Int) * sizeof(INT))) 200 dp_l)
  ** (intArray.undef_full (( &( "digits" ) ) + ((0 : Int) * sizeof(INT))) 20)
  ** (intArray.full (( &( "power" ) ) + ((0 : Int) * sizeof(INT))) 20 power_l)
|--
  (intArray.undef_full ( &( "dp" ) ) 200)
  ** (intArray.undef_full ( &( "power" ) ) 20)
  ** (intArray.undef_full ( &( "digits" ) ) 20)
)

noncomputable def interval_digits_sum_entail_wit_2_split_goal_spatial : Prop :=
  forall (y_pre : Int) (x_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (retval : Int) (retval_2 : Int) (PreH1 : (PrefixDigitSum (x_pre - 1) retval_2)) (PreH2 : (PrefixDigitSum y_pre retval)) (PreH3 : (DigitDPTable dp_l)) (PreH4 : (PowerTable power_l)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre <= y_pre)) (PreH7 : (y_pre <= 1000000000000000000)) ,
  (intArray.full (( &( "dp" ) ) + ((0 : Int) * sizeof(INT))) 200 dp_l)
  ** (intArray.undef_full (( &( "digits" ) ) + ((0 : Int) * sizeof(INT))) 20)
  ** (intArray.full (( &( "power" ) ) + ((0 : Int) * sizeof(INT))) 20 power_l)
|--
  (intArray.undef_full ( &( "dp" ) ) 200)
  ** (intArray.undef_full ( &( "power" ) ) 20)
  ** (intArray.undef_full ( &( "digits" ) ) 20)

noncomputable def interval_digits_sum_return_wit_1 : Prop :=
  (
forall (y_pre : Int) (x_pre : Int) (ans1 : Int) (ans2 : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= y_pre)) (PreH3 : (y_pre <= 1000000000000000000)) (PreH4 : (PrefixDigitSum y_pre ans1)) (PreH5 : (PrefixDigitSum (x_pre - 1) ans2)) ,
  TT && emp 
|--
  “ (IntervalDigitSum x_pre y_pre (Z.rem ((Z.rem (ans1 - ans2) 1000000007) + 1000000007) 1000000007)) ”
  &&  emp
) \/
(
forall (y_pre : Int) (x_pre : Int) (ans1 : Int) (ans2 : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= y_pre)) (PreH3 : (y_pre <= 1000000000000000000)) (PreH4 : (PrefixDigitSum y_pre ans1)) (PreH5 : (PrefixDigitSum (x_pre - 1) ans2)) ,
  TT && emp 
|--
  “ (IntervalDigitSum x_pre y_pre (Z.rem ((Z.rem (ans1 - ans2) 1000000007) + 1000000007) 1000000007)) ”
  &&  emp
)

noncomputable def interval_digits_sum_return_wit_1_split_goal_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (ans1 : Int) (ans2 : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= y_pre)) (PreH3 : (y_pre <= 1000000000000000000)) (PreH4 : (PrefixDigitSum y_pre ans1)) (PreH5 : (PrefixDigitSum (x_pre - 1) ans2)) ,
  (IntervalDigitSum x_pre y_pre (Z.rem ((Z.rem (ans1 - ans2) 1000000007) + 1000000007) 1000000007))

noncomputable def interval_digits_sum_partial_solve_wit_1 : Prop :=
  forall (y_pre : Int) (x_pre : Int) (PreH1 : (1 <= x_pre)) (PreH2 : (x_pre <= y_pre)) (PreH3 : (y_pre <= 1000000000000000000)) ,
  (intArray.undef_full (( &( "dp" ) ) + ((0 : Int) * sizeof(INT))) 200)
  ** (intArray.undef_full (( &( "power" ) ) + ((0 : Int) * sizeof(INT))) 20)
  ** (intArray.undef_full (( &( "digits" ) ) + ((0 : Int) * sizeof(INT))) 20)
|--
  “ (1 <= x_pre) ” &&
  “ (x_pre <= y_pre) ” &&
  “ (y_pre <= 1000000000000000000) ”
  &&  (intArray.undef_full (( &( "dp" ) ) + ((0 : Int) * sizeof(INT))) 200)
  ** (intArray.undef_full (( &( "power" ) ) + ((0 : Int) * sizeof(INT))) 20)
  ** (intArray.undef_full (( &( "digits" ) ) + ((0 : Int) * sizeof(INT))) 20)

noncomputable def interval_digits_sum_partial_solve_wit_2_pure : Prop :=
  forall (y_pre : Int) (x_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (PreH1 : (DigitDPTable dp_l)) (PreH2 : (PowerTable power_l)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= y_pre)) (PreH5 : (y_pre <= 1000000000000000000)) ,
  ((( &( "ans1" ) )) # Int |->_)
  ** (intArray.full (( &( "dp" ) ) + ((0 : Int) * sizeof(INT))) 200 dp_l)
  ** (intArray.full (( &( "power" ) ) + ((0 : Int) * sizeof(INT))) 20 power_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "y" ) )) # Int64 |-> (y_pre))
  ** (intArray.undef_full (( &( "digits" ) ) + ((0 : Int) * sizeof(INT))) 20)
|--
  “ ((0 : Int) <= y_pre) ” &&
  “ (y_pre <= 1000000000000000000) ” &&
  “ (DigitDPTable dp_l) ”

noncomputable def interval_digits_sum_partial_solve_wit_2_aux : Prop :=
  forall (y_pre : Int) (x_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (PreH1 : (DigitDPTable dp_l)) (PreH2 : (PowerTable power_l)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre <= y_pre)) (PreH5 : (y_pre <= 1000000000000000000)) ,
  (intArray.full (( &( "dp" ) ) + ((0 : Int) * sizeof(INT))) 200 dp_l)
  ** (intArray.full (( &( "power" ) ) + ((0 : Int) * sizeof(INT))) 20 power_l)
  ** (intArray.undef_full (( &( "digits" ) ) + ((0 : Int) * sizeof(INT))) 20)
|--
  “ ((0 : Int) <= y_pre) ” &&
  “ (y_pre <= 1000000000000000000) ” &&
  “ (DigitDPTable dp_l) ” &&
  “ (DigitDPTable dp_l) ” &&
  “ (PowerTable power_l) ” &&
  “ (1 <= x_pre) ” &&
  “ (x_pre <= y_pre) ” &&
  “ (y_pre <= 1000000000000000000) ”
  &&  (intArray.full (( &( "dp" ) ) + ((0 : Int) * sizeof(INT))) 200 dp_l)
  ** (intArray.undef_full (( &( "digits" ) ) + ((0 : Int) * sizeof(INT))) 20)
  ** (intArray.full (( &( "power" ) ) + ((0 : Int) * sizeof(INT))) 20 power_l)

noncomputable def interval_digits_sum_partial_solve_wit_2 : Prop := interval_digits_sum_partial_solve_wit_2_pure -> interval_digits_sum_partial_solve_wit_2_aux

noncomputable def interval_digits_sum_partial_solve_wit_3_pure : Prop :=
  forall (y_pre : Int) (x_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (retval : Int) (PreH1 : (PrefixDigitSum y_pre retval)) (PreH2 : (DigitDPTable dp_l)) (PreH3 : (PowerTable power_l)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre <= y_pre)) (PreH6 : (y_pre <= 1000000000000000000)) ,
  ((( &( "ans2" ) )) # Int |->_)
  ** (intArray.full (( &( "dp" ) ) + ((0 : Int) * sizeof(INT))) 200 dp_l)
  ** (intArray.undef_full (( &( "digits" ) ) + ((0 : Int) * sizeof(INT))) 20)
  ** ((( &( "ans1" ) )) # Int |-> (retval))
  ** (intArray.full (( &( "power" ) ) + ((0 : Int) * sizeof(INT))) 20 power_l)
  ** ((( &( "x" ) )) # Int64 |-> (x_pre))
  ** ((( &( "y" ) )) # Int64 |-> (y_pre))
|--
  “ ((0 : Int) <= (x_pre - 1)) ” &&
  “ ((x_pre - 1) <= 1000000000000000000) ” &&
  “ (DigitDPTable dp_l) ”

noncomputable def interval_digits_sum_partial_solve_wit_3_aux : Prop :=
  forall (y_pre : Int) (x_pre : Int) (power_l : (List Int)) (dp_l : (List Int)) (retval : Int) (PreH1 : (PrefixDigitSum y_pre retval)) (PreH2 : (DigitDPTable dp_l)) (PreH3 : (PowerTable power_l)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre <= y_pre)) (PreH6 : (y_pre <= 1000000000000000000)) ,
  (intArray.full (( &( "dp" ) ) + ((0 : Int) * sizeof(INT))) 200 dp_l)
  ** (intArray.undef_full (( &( "digits" ) ) + ((0 : Int) * sizeof(INT))) 20)
  ** (intArray.full (( &( "power" ) ) + ((0 : Int) * sizeof(INT))) 20 power_l)
|--
  “ ((0 : Int) <= (x_pre - 1)) ” &&
  “ ((x_pre - 1) <= 1000000000000000000) ” &&
  “ (DigitDPTable dp_l) ” &&
  “ (PrefixDigitSum y_pre retval) ” &&
  “ (DigitDPTable dp_l) ” &&
  “ (PowerTable power_l) ” &&
  “ (1 <= x_pre) ” &&
  “ (x_pre <= y_pre) ” &&
  “ (y_pre <= 1000000000000000000) ”
  &&  (intArray.full (( &( "dp" ) ) + ((0 : Int) * sizeof(INT))) 200 dp_l)
  ** (intArray.undef_full (( &( "digits" ) ) + ((0 : Int) * sizeof(INT))) 20)
  ** (intArray.full (( &( "power" ) ) + ((0 : Int) * sizeof(INT))) 20 power_l)

noncomputable def interval_digits_sum_partial_solve_wit_3 : Prop := interval_digits_sum_partial_solve_wit_3_pure -> interval_digits_sum_partial_solve_wit_3_aux


structure VC_Correct : Type where
  proof_of_digits_sum_init_safety_wit_1 : digits_sum_init_safety_wit_1
  proof_of_digits_sum_init_safety_wit_2 : digits_sum_init_safety_wit_2
  proof_of_digits_sum_init_safety_wit_3 : digits_sum_init_safety_wit_3
  proof_of_digits_sum_init_safety_wit_4 : digits_sum_init_safety_wit_4
  proof_of_digits_sum_init_safety_wit_5 : digits_sum_init_safety_wit_5
  proof_of_digits_sum_init_safety_wit_6 : digits_sum_init_safety_wit_6
  proof_of_digits_sum_init_safety_wit_7 : digits_sum_init_safety_wit_7
  proof_of_digits_sum_init_safety_wit_9 : digits_sum_init_safety_wit_9
  proof_of_digits_sum_init_safety_wit_10 : digits_sum_init_safety_wit_10
  proof_of_digits_sum_init_safety_wit_11 : digits_sum_init_safety_wit_11
  proof_of_digits_sum_init_safety_wit_12 : digits_sum_init_safety_wit_12
  proof_of_digits_sum_init_safety_wit_13 : digits_sum_init_safety_wit_13
  proof_of_digits_sum_init_safety_wit_14 : digits_sum_init_safety_wit_14
  proof_of_digits_sum_init_safety_wit_15 : digits_sum_init_safety_wit_15
  proof_of_digits_sum_init_safety_wit_16 : digits_sum_init_safety_wit_16
  proof_of_digits_sum_init_safety_wit_17 : digits_sum_init_safety_wit_17
  proof_of_digits_sum_init_safety_wit_18 : digits_sum_init_safety_wit_18
  proof_of_digits_sum_init_safety_wit_19 : digits_sum_init_safety_wit_19
  proof_of_digits_sum_init_safety_wit_20 : digits_sum_init_safety_wit_20
  proof_of_digits_sum_init_safety_wit_21 : digits_sum_init_safety_wit_21
  proof_of_digits_sum_init_safety_wit_22 : digits_sum_init_safety_wit_22
  proof_of_digits_sum_init_safety_wit_23 : digits_sum_init_safety_wit_23
  proof_of_digits_sum_init_safety_wit_24 : digits_sum_init_safety_wit_24
  proof_of_digits_sum_init_safety_wit_25 : digits_sum_init_safety_wit_25
  proof_of_digits_sum_init_safety_wit_26 : digits_sum_init_safety_wit_26
  proof_of_digits_sum_init_safety_wit_27 : digits_sum_init_safety_wit_27
  proof_of_digits_sum_init_safety_wit_28 : digits_sum_init_safety_wit_28
  proof_of_digits_sum_init_safety_wit_29 : digits_sum_init_safety_wit_29
  proof_of_digits_sum_init_safety_wit_30 : digits_sum_init_safety_wit_30
  proof_of_digits_sum_init_safety_wit_31 : digits_sum_init_safety_wit_31
  proof_of_digits_sum_init_safety_wit_32 : digits_sum_init_safety_wit_32
  proof_of_digits_sum_init_safety_wit_33 : digits_sum_init_safety_wit_33
  proof_of_digits_sum_init_safety_wit_34 : digits_sum_init_safety_wit_34
  proof_of_digits_sum_init_safety_wit_35 : digits_sum_init_safety_wit_35
  proof_of_digits_sum_init_safety_wit_37 : digits_sum_init_safety_wit_37
  proof_of_digits_sum_init_safety_wit_39 : digits_sum_init_safety_wit_39
  proof_of_digits_sum_init_safety_wit_40 : digits_sum_init_safety_wit_40
  proof_of_digits_sum_init_safety_wit_41 : digits_sum_init_safety_wit_41
  proof_of_digits_sum_init_safety_wit_42 : digits_sum_init_safety_wit_42
  proof_of_digits_sum_init_safety_wit_43 : digits_sum_init_safety_wit_43
  proof_of_digits_sum_init_safety_wit_44 : digits_sum_init_safety_wit_44
  proof_of_digits_sum_init_safety_wit_45 : digits_sum_init_safety_wit_45
  proof_of_digits_sum_init_safety_wit_46 : digits_sum_init_safety_wit_46
  proof_of_digits_sum_init_safety_wit_48 : digits_sum_init_safety_wit_48
  proof_of_digits_sum_init_safety_wit_49 : digits_sum_init_safety_wit_49
  proof_of_digits_sum_init_safety_wit_50 : digits_sum_init_safety_wit_50
  proof_of_digits_sum_init_safety_wit_51 : digits_sum_init_safety_wit_51
  proof_of_digits_sum_init_safety_wit_52 : digits_sum_init_safety_wit_52
  proof_of_digits_sum_init_safety_wit_53 : digits_sum_init_safety_wit_53
  proof_of_digits_sum_init_safety_wit_54 : digits_sum_init_safety_wit_54
  proof_of_digits_sum_init_safety_wit_55 : digits_sum_init_safety_wit_55
  proof_of_digits_sum_init_safety_wit_56 : digits_sum_init_safety_wit_56
  proof_of_digits_sum_init_safety_wit_57 : digits_sum_init_safety_wit_57
  proof_of_digits_sum_init_partial_solve_wit_1 : digits_sum_init_partial_solve_wit_1
  proof_of_digits_sum_init_partial_solve_wit_2 : digits_sum_init_partial_solve_wit_2
  proof_of_digits_sum_init_partial_solve_wit_3 : digits_sum_init_partial_solve_wit_3
  proof_of_digits_sum_init_partial_solve_wit_4 : digits_sum_init_partial_solve_wit_4
  proof_of_digits_sum_init_partial_solve_wit_5 : digits_sum_init_partial_solve_wit_5
  proof_of_digits_sum_init_partial_solve_wit_6 : digits_sum_init_partial_solve_wit_6
  proof_of_digits_sum_init_partial_solve_wit_7 : digits_sum_init_partial_solve_wit_7
  proof_of_digits_sum_init_partial_solve_wit_8 : digits_sum_init_partial_solve_wit_8
  proof_of_digits_sum_init_partial_solve_wit_9 : digits_sum_init_partial_solve_wit_9
  proof_of_prefix_digits_sum_safety_wit_1 : prefix_digits_sum_safety_wit_1
  proof_of_prefix_digits_sum_safety_wit_2 : prefix_digits_sum_safety_wit_2
  proof_of_prefix_digits_sum_safety_wit_3 : prefix_digits_sum_safety_wit_3
  proof_of_prefix_digits_sum_safety_wit_4 : prefix_digits_sum_safety_wit_4
  proof_of_prefix_digits_sum_safety_wit_5 : prefix_digits_sum_safety_wit_5
  proof_of_prefix_digits_sum_safety_wit_6 : prefix_digits_sum_safety_wit_6
  proof_of_prefix_digits_sum_safety_wit_7 : prefix_digits_sum_safety_wit_7
  proof_of_prefix_digits_sum_safety_wit_8 : prefix_digits_sum_safety_wit_8
  proof_of_prefix_digits_sum_safety_wit_9 : prefix_digits_sum_safety_wit_9
  proof_of_prefix_digits_sum_safety_wit_10 : prefix_digits_sum_safety_wit_10
  proof_of_prefix_digits_sum_safety_wit_11 : prefix_digits_sum_safety_wit_11
  proof_of_prefix_digits_sum_safety_wit_12 : prefix_digits_sum_safety_wit_12
  proof_of_prefix_digits_sum_safety_wit_13 : prefix_digits_sum_safety_wit_13
  proof_of_prefix_digits_sum_safety_wit_14 : prefix_digits_sum_safety_wit_14
  proof_of_prefix_digits_sum_safety_wit_15 : prefix_digits_sum_safety_wit_15
  proof_of_prefix_digits_sum_safety_wit_16 : prefix_digits_sum_safety_wit_16
  proof_of_prefix_digits_sum_safety_wit_18 : prefix_digits_sum_safety_wit_18
  proof_of_prefix_digits_sum_safety_wit_19 : prefix_digits_sum_safety_wit_19
  proof_of_prefix_digits_sum_safety_wit_20 : prefix_digits_sum_safety_wit_20
  proof_of_prefix_digits_sum_safety_wit_21 : prefix_digits_sum_safety_wit_21
  proof_of_prefix_digits_sum_safety_wit_22 : prefix_digits_sum_safety_wit_22
  proof_of_prefix_digits_sum_safety_wit_24 : prefix_digits_sum_safety_wit_24
  proof_of_prefix_digits_sum_safety_wit_25 : prefix_digits_sum_safety_wit_25
  proof_of_prefix_digits_sum_safety_wit_26 : prefix_digits_sum_safety_wit_26
  proof_of_prefix_digits_sum_safety_wit_27 : prefix_digits_sum_safety_wit_27
  proof_of_prefix_digits_sum_safety_wit_28 : prefix_digits_sum_safety_wit_28
  proof_of_prefix_digits_sum_safety_wit_29 : prefix_digits_sum_safety_wit_29
  proof_of_prefix_digits_sum_safety_wit_31 : prefix_digits_sum_safety_wit_31
  proof_of_prefix_digits_sum_safety_wit_32 : prefix_digits_sum_safety_wit_32
  proof_of_prefix_digits_sum_safety_wit_35 : prefix_digits_sum_safety_wit_35
  proof_of_prefix_digits_sum_safety_wit_36 : prefix_digits_sum_safety_wit_36
  proof_of_prefix_digits_sum_safety_wit_37 : prefix_digits_sum_safety_wit_37
  proof_of_prefix_digits_sum_safety_wit_39 : prefix_digits_sum_safety_wit_39
  proof_of_prefix_digits_sum_safety_wit_40 : prefix_digits_sum_safety_wit_40
  proof_of_prefix_digits_sum_safety_wit_42 : prefix_digits_sum_safety_wit_42
  proof_of_prefix_digits_sum_safety_wit_43 : prefix_digits_sum_safety_wit_43
  proof_of_prefix_digits_sum_safety_wit_44 : prefix_digits_sum_safety_wit_44
  proof_of_prefix_digits_sum_safety_wit_45 : prefix_digits_sum_safety_wit_45
  proof_of_prefix_digits_sum_partial_solve_wit_1 : prefix_digits_sum_partial_solve_wit_1
  proof_of_prefix_digits_sum_partial_solve_wit_2 : prefix_digits_sum_partial_solve_wit_2
  proof_of_prefix_digits_sum_partial_solve_wit_3 : prefix_digits_sum_partial_solve_wit_3
  proof_of_prefix_digits_sum_partial_solve_wit_4 : prefix_digits_sum_partial_solve_wit_4
  proof_of_interval_digits_sum_safety_wit_1 : interval_digits_sum_safety_wit_1
  proof_of_interval_digits_sum_safety_wit_2 : interval_digits_sum_safety_wit_2
  proof_of_interval_digits_sum_safety_wit_3 : interval_digits_sum_safety_wit_3
  proof_of_interval_digits_sum_safety_wit_4 : interval_digits_sum_safety_wit_4
  proof_of_interval_digits_sum_safety_wit_5 : interval_digits_sum_safety_wit_5
  proof_of_interval_digits_sum_safety_wit_6 : interval_digits_sum_safety_wit_6
  proof_of_interval_digits_sum_safety_wit_7 : interval_digits_sum_safety_wit_7
  proof_of_interval_digits_sum_safety_wit_8 : interval_digits_sum_safety_wit_8
  proof_of_interval_digits_sum_safety_wit_9 : interval_digits_sum_safety_wit_9
  proof_of_interval_digits_sum_safety_wit_11 : interval_digits_sum_safety_wit_11
  proof_of_interval_digits_sum_safety_wit_13 : interval_digits_sum_safety_wit_13
  proof_of_interval_digits_sum_safety_wit_14 : interval_digits_sum_safety_wit_14
  proof_of_interval_digits_sum_safety_wit_15 : interval_digits_sum_safety_wit_15
  proof_of_interval_digits_sum_partial_solve_wit_1 : interval_digits_sum_partial_solve_wit_1
  proof_of_interval_digits_sum_partial_solve_wit_2_pure : interval_digits_sum_partial_solve_wit_2_pure
  proof_of_interval_digits_sum_partial_solve_wit_2 : interval_digits_sum_partial_solve_wit_2
  proof_of_interval_digits_sum_partial_solve_wit_3_pure : interval_digits_sum_partial_solve_wit_3_pure
  proof_of_interval_digits_sum_partial_solve_wit_3 : interval_digits_sum_partial_solve_wit_3
  proof_of_digits_sum_init_safety_wit_8 : digits_sum_init_safety_wit_8
  proof_of_digits_sum_init_safety_wit_36 : digits_sum_init_safety_wit_36
  proof_of_digits_sum_init_safety_wit_38 : digits_sum_init_safety_wit_38
  proof_of_digits_sum_init_safety_wit_47 : digits_sum_init_safety_wit_47
  proof_of_digits_sum_init_entail_wit_1 : digits_sum_init_entail_wit_1
  proof_of_digits_sum_init_entail_wit_2 : digits_sum_init_entail_wit_2
  proof_of_digits_sum_init_entail_wit_3 : digits_sum_init_entail_wit_3
  proof_of_digits_sum_init_entail_wit_4 : digits_sum_init_entail_wit_4
  proof_of_digits_sum_init_entail_wit_5 : digits_sum_init_entail_wit_5
  proof_of_digits_sum_init_entail_wit_6 : digits_sum_init_entail_wit_6
  proof_of_digits_sum_init_entail_wit_7 : digits_sum_init_entail_wit_7
  proof_of_digits_sum_init_entail_wit_8 : digits_sum_init_entail_wit_8
  proof_of_digits_sum_init_entail_wit_9 : digits_sum_init_entail_wit_9
  proof_of_digits_sum_init_entail_wit_10 : digits_sum_init_entail_wit_10
  proof_of_digits_sum_init_entail_wit_11 : digits_sum_init_entail_wit_11
  proof_of_digits_sum_init_entail_wit_12 : digits_sum_init_entail_wit_12
  proof_of_digits_sum_init_entail_wit_13 : digits_sum_init_entail_wit_13
  proof_of_digits_sum_init_entail_wit_14 : digits_sum_init_entail_wit_14
  proof_of_digits_sum_init_return_wit_1 : digits_sum_init_return_wit_1
  proof_of_prefix_digits_sum_safety_wit_17 : prefix_digits_sum_safety_wit_17
  proof_of_prefix_digits_sum_safety_wit_23 : prefix_digits_sum_safety_wit_23
  proof_of_prefix_digits_sum_safety_wit_30 : prefix_digits_sum_safety_wit_30
  proof_of_prefix_digits_sum_safety_wit_33 : prefix_digits_sum_safety_wit_33
  proof_of_prefix_digits_sum_safety_wit_34 : prefix_digits_sum_safety_wit_34
  proof_of_prefix_digits_sum_safety_wit_38 : prefix_digits_sum_safety_wit_38
  proof_of_prefix_digits_sum_safety_wit_41 : prefix_digits_sum_safety_wit_41
  proof_of_prefix_digits_sum_entail_wit_1 : prefix_digits_sum_entail_wit_1
  proof_of_prefix_digits_sum_entail_wit_2 : prefix_digits_sum_entail_wit_2
  proof_of_prefix_digits_sum_entail_wit_3 : prefix_digits_sum_entail_wit_3
  proof_of_prefix_digits_sum_entail_wit_4 : prefix_digits_sum_entail_wit_4
  proof_of_prefix_digits_sum_entail_wit_5 : prefix_digits_sum_entail_wit_5
  proof_of_prefix_digits_sum_entail_wit_6 : prefix_digits_sum_entail_wit_6
  proof_of_prefix_digits_sum_entail_wit_7 : prefix_digits_sum_entail_wit_7
  proof_of_prefix_digits_sum_entail_wit_8 : prefix_digits_sum_entail_wit_8
  proof_of_prefix_digits_sum_entail_wit_9 : prefix_digits_sum_entail_wit_9
  proof_of_prefix_digits_sum_entail_wit_10 : prefix_digits_sum_entail_wit_10
  proof_of_prefix_digits_sum_return_wit_1 : prefix_digits_sum_return_wit_1
  proof_of_prefix_digits_sum_return_wit_2 : prefix_digits_sum_return_wit_2
  proof_of_interval_digits_sum_safety_wit_10 : interval_digits_sum_safety_wit_10
  proof_of_interval_digits_sum_safety_wit_12 : interval_digits_sum_safety_wit_12
  proof_of_interval_digits_sum_entail_wit_1 : interval_digits_sum_entail_wit_1
  proof_of_interval_digits_sum_entail_wit_2 : interval_digits_sum_entail_wit_2
  proof_of_interval_digits_sum_return_wit_1 : interval_digits_sum_return_wit_1

end SimpleC.EE.LLM_bench.Algorithms.annoying_math_homework.annoying_math_homework_goal
