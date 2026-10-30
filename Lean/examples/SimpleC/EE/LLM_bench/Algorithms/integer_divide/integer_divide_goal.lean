import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Algorithms.integer_divide.integer_divide_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.integer_divide.integer_divide_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance integer_divide_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def divide_safety_wit_1 : Prop :=
  forall (original : Int) (n_pre : Int) (p_pre : Int) (PreH1 : (n_pre = original)) (PreH2 : (1 <= original)) (PreH3 : (original <= INT_MAX)) ,
  ((( &( "cnt" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** (intArray.undef_full p_pre original)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def divide_safety_wit_2 : Prop :=
  forall (original : Int) (n_pre : Int) (p_pre : Int) (PreH1 : (n_pre = original)) (PreH2 : (1 <= original)) (PreH3 : (original <= INT_MAX)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "cnt" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** (intArray.undef_full p_pre original)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def divide_safety_wit_3 : Prop :=
  forall (original : Int) (p_pre : Int) (factors : (List Int)) (cnt : Int) (i : Int) (n : Int) (PreH1 : (1 <= original)) (PreH2 : (original <= INT_MAX)) (PreH3 : (1 <= n)) (PreH4 : (n <= original)) (PreH5 : (2 <= i)) (PreH6 : (i <= original)) (PreH7 : (i <= n)) (PreH8 : ((0 : Int) <= cnt)) (PreH9 : (cnt < original)) (PreH10 : ((Zlength (factors)) = cnt)) (PreH11 : (FactorizationProgress original factors n i)) ,
  ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** (intArray.undef_seg p_pre (0 : Int) 1)
  ** (intArray.seg p_pre 1 (1 + cnt) factors)
  ** (intArray.undef_seg p_pre (1 + cnt) original)
|--
  “ ((n ≠ (INT_MIN)) ∨ (i ≠ (-1))) ” &&
  “ (i ≠ (0 : Int)) ”

noncomputable def divide_safety_wit_4 : Prop :=
  forall (original : Int) (p_pre : Int) (factors : (List Int)) (cnt : Int) (i : Int) (n : Int) (PreH1 : (1 <= original)) (PreH2 : (original <= INT_MAX)) (PreH3 : (1 <= n)) (PreH4 : (n <= original)) (PreH5 : (2 <= i)) (PreH6 : (i <= original)) (PreH7 : (n = 1)) (PreH8 : ((0 : Int) <= cnt)) (PreH9 : (cnt < original)) (PreH10 : ((Zlength (factors)) = cnt)) (PreH11 : (FactorizationProgress original factors n i)) ,
  ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** (intArray.undef_seg p_pre (0 : Int) 1)
  ** (intArray.seg p_pre 1 (1 + cnt) factors)
  ** (intArray.undef_seg p_pre (1 + cnt) original)
|--
  “ ((n ≠ (INT_MIN)) ∨ (i ≠ (-1))) ” &&
  “ (i ≠ (0 : Int)) ”

noncomputable def divide_safety_wit_5 : Prop :=
  forall (original : Int) (p_pre : Int) (factors : (List Int)) (cnt : Int) (i : Int) (n : Int) (PreH1 : (1 <= original)) (PreH2 : (original <= INT_MAX)) (PreH3 : (1 <= n)) (PreH4 : (n <= original)) (PreH5 : (2 <= i)) (PreH6 : (i <= original)) (PreH7 : (n = 1)) (PreH8 : ((0 : Int) <= cnt)) (PreH9 : (cnt < original)) (PreH10 : ((Zlength (factors)) = cnt)) (PreH11 : (FactorizationProgress original factors n i)) ,
  ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** (intArray.undef_seg p_pre (0 : Int) 1)
  ** (intArray.seg p_pre 1 (1 + cnt) factors)
  ** (intArray.undef_seg p_pre (1 + cnt) original)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def divide_safety_wit_6 : Prop :=
  forall (original : Int) (p_pre : Int) (factors : (List Int)) (cnt : Int) (i : Int) (n : Int) (PreH1 : (1 <= original)) (PreH2 : (original <= INT_MAX)) (PreH3 : (1 <= n)) (PreH4 : (n <= original)) (PreH5 : (2 <= i)) (PreH6 : (i <= original)) (PreH7 : (i <= n)) (PreH8 : ((0 : Int) <= cnt)) (PreH9 : (cnt < original)) (PreH10 : ((Zlength (factors)) = cnt)) (PreH11 : (FactorizationProgress original factors n i)) ,
  ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** (intArray.undef_seg p_pre (0 : Int) 1)
  ** (intArray.seg p_pre 1 (1 + cnt) factors)
  ** (intArray.undef_seg p_pre (1 + cnt) original)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def divide_safety_wit_7 : Prop :=
  forall (original : Int) (p_pre : Int) (factors : (List Int)) (cnt : Int) (i : Int) (n : Int) (PreH1 : ((cnt + 1) < original)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (n >= INT_MIN)) (PreH6 : ((Z.rem n i) = (0 : Int))) (PreH7 : (1 <= original)) (PreH8 : (original <= INT_MAX)) (PreH9 : (1 <= n)) (PreH10 : (n <= original)) (PreH11 : (2 <= i)) (PreH12 : (i <= original)) (PreH13 : (n = 1)) (PreH14 : ((0 : Int) <= cnt)) (PreH15 : (cnt < original)) (PreH16 : ((Zlength (factors)) = cnt)) (PreH17 : (FactorizationProgress original factors n i)) ,
  ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_seg p_pre (0 : Int) 1)
  ** (intArray.seg p_pre 1 (1 + cnt) factors)
  ** (intArray.undef_seg p_pre (1 + cnt) original)
|--
  “ ((cnt + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (cnt + 1)) ”

noncomputable def divide_safety_wit_8 : Prop :=
  forall (original : Int) (p_pre : Int) (factors : (List Int)) (cnt : Int) (i : Int) (n : Int) (PreH1 : ((cnt + 1) < original)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (n >= INT_MIN)) (PreH6 : ((Z.rem n i) = (0 : Int))) (PreH7 : (1 <= original)) (PreH8 : (original <= INT_MAX)) (PreH9 : (1 <= n)) (PreH10 : (n <= original)) (PreH11 : (2 <= i)) (PreH12 : (i <= original)) (PreH13 : (i <= n)) (PreH14 : ((0 : Int) <= cnt)) (PreH15 : (cnt < original)) (PreH16 : ((Zlength (factors)) = cnt)) (PreH17 : (FactorizationProgress original factors n i)) ,
  ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_seg p_pre (0 : Int) 1)
  ** (intArray.seg p_pre 1 (1 + cnt) factors)
  ** (intArray.undef_seg p_pre (1 + cnt) original)
|--
  “ ((cnt + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (cnt + 1)) ”

noncomputable def divide_safety_wit_9 : Prop :=
  forall (original : Int) (p_pre : Int) (factors : (List Int)) (cnt : Int) (i : Int) (n : Int) (PreH1 : ((cnt + 1) < original)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (n >= INT_MIN)) (PreH6 : ((Z.rem n i) = (0 : Int))) (PreH7 : (1 <= original)) (PreH8 : (original <= INT_MAX)) (PreH9 : (1 <= n)) (PreH10 : (n <= original)) (PreH11 : (2 <= i)) (PreH12 : (i <= original)) (PreH13 : (n = 1)) (PreH14 : ((0 : Int) <= cnt)) (PreH15 : (cnt < original)) (PreH16 : ((Zlength (factors)) = cnt)) (PreH17 : (FactorizationProgress original factors n i)) ,
  (intArray.seg p_pre 1 ((1 + cnt) + 1) (factors ++ (i :: (@List.nil Int))))
  ** (intArray.undef_seg p_pre ((1 + cnt) + 1) original)
  ** ((( &( "cnt" ) )) # Int |-> ((cnt + 1)))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_seg p_pre (0 : Int) 1)
|--
  “ ((n ≠ (INT_MIN)) ∨ (i ≠ (-1))) ” &&
  “ (i ≠ (0 : Int)) ”

noncomputable def divide_safety_wit_10 : Prop :=
  forall (original : Int) (p_pre : Int) (factors : (List Int)) (cnt : Int) (i : Int) (n : Int) (PreH1 : ((cnt + 1) < original)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (n >= INT_MIN)) (PreH6 : ((Z.rem n i) = (0 : Int))) (PreH7 : (1 <= original)) (PreH8 : (original <= INT_MAX)) (PreH9 : (1 <= n)) (PreH10 : (n <= original)) (PreH11 : (2 <= i)) (PreH12 : (i <= original)) (PreH13 : (i <= n)) (PreH14 : ((0 : Int) <= cnt)) (PreH15 : (cnt < original)) (PreH16 : ((Zlength (factors)) = cnt)) (PreH17 : (FactorizationProgress original factors n i)) ,
  (intArray.seg p_pre 1 ((1 + cnt) + 1) (factors ++ (i :: (@List.nil Int))))
  ** (intArray.undef_seg p_pre ((1 + cnt) + 1) original)
  ** ((( &( "cnt" ) )) # Int |-> ((cnt + 1)))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_seg p_pre (0 : Int) 1)
|--
  “ ((n ≠ (INT_MIN)) ∨ (i ≠ (-1))) ” &&
  “ (i ≠ (0 : Int)) ”

noncomputable def divide_safety_wit_11 : Prop :=
  forall (original : Int) (p_pre : Int) (factors : (List Int)) (cnt : Int) (i : Int) (n : Int) (PreH1 : ((Z.rem n i) ≠ (0 : Int))) (PreH2 : (1 <= original)) (PreH3 : (original <= INT_MAX)) (PreH4 : (1 <= n)) (PreH5 : (n <= original)) (PreH6 : (2 <= i)) (PreH7 : (i <= original)) (PreH8 : (n = 1)) (PreH9 : ((0 : Int) <= cnt)) (PreH10 : (cnt < original)) (PreH11 : ((Zlength (factors)) = cnt)) (PreH12 : (FactorizationProgress original factors n i)) ,
  ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** (intArray.undef_seg p_pre (0 : Int) 1)
  ** (intArray.seg p_pre 1 (1 + cnt) factors)
  ** (intArray.undef_seg p_pre (1 + cnt) original)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def divide_safety_wit_12 : Prop :=
  forall (original : Int) (p_pre : Int) (factors : (List Int)) (cnt : Int) (i : Int) (n : Int) (PreH1 : ((Z.rem n i) ≠ (0 : Int))) (PreH2 : (1 <= original)) (PreH3 : (original <= INT_MAX)) (PreH4 : (1 <= n)) (PreH5 : (n <= original)) (PreH6 : (2 <= i)) (PreH7 : (i <= original)) (PreH8 : (i <= n)) (PreH9 : ((0 : Int) <= cnt)) (PreH10 : (cnt < original)) (PreH11 : ((Zlength (factors)) = cnt)) (PreH12 : (FactorizationProgress original factors n i)) ,
  ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** (intArray.undef_seg p_pre (0 : Int) 1)
  ** (intArray.seg p_pre 1 (1 + cnt) factors)
  ** (intArray.undef_seg p_pre (1 + cnt) original)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def divide_safety_wit_13 : Prop :=
  forall (original : Int) (p_pre : Int) (factors : (List Int)) (cnt : Int) (i : Int) (n : Int) (PreH1 : (n ≠ 1)) (PreH2 : ((Z.rem n i) ≠ (0 : Int))) (PreH3 : (1 <= original)) (PreH4 : (original <= INT_MAX)) (PreH5 : (1 <= n)) (PreH6 : (n <= original)) (PreH7 : (2 <= i)) (PreH8 : (i <= original)) (PreH9 : (n = 1)) (PreH10 : ((0 : Int) <= cnt)) (PreH11 : (cnt < original)) (PreH12 : ((Zlength (factors)) = cnt)) (PreH13 : (FactorizationProgress original factors n i)) ,
  ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** (intArray.undef_seg p_pre (0 : Int) 1)
  ** (intArray.seg p_pre 1 (1 + cnt) factors)
  ** (intArray.undef_seg p_pre (1 + cnt) original)
|--
  “ False ”

noncomputable def divide_safety_wit_14 : Prop :=
  forall (original : Int) (p_pre : Int) (factors : (List Int)) (cnt : Int) (i : Int) (n : Int) (PreH1 : (n = 1)) (PreH2 : ((Z.rem n i) ≠ (0 : Int))) (PreH3 : (1 <= original)) (PreH4 : (original <= INT_MAX)) (PreH5 : (1 <= n)) (PreH6 : (n <= original)) (PreH7 : (2 <= i)) (PreH8 : (i <= original)) (PreH9 : (i <= n)) (PreH10 : ((0 : Int) <= cnt)) (PreH11 : (cnt < original)) (PreH12 : ((Zlength (factors)) = cnt)) (PreH13 : (FactorizationProgress original factors n i)) ,
  ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** (intArray.undef_seg p_pre (0 : Int) 1)
  ** (intArray.seg p_pre 1 (1 + cnt) factors)
  ** (intArray.undef_seg p_pre (1 + cnt) original)
|--
  “ False ”

noncomputable def divide_safety_wit_15 : Prop :=
  forall (original : Int) (p_pre : Int) (factors : (List Int)) (cnt : Int) (i : Int) (n : Int) (PreH1 : (i < INT_MAX)) (PreH2 : (cnt <= INT_MAX)) (PreH3 : (n <= INT_MAX)) (PreH4 : (cnt >= INT_MIN)) (PreH5 : (n >= INT_MIN)) (PreH6 : (n ≠ 1)) (PreH7 : ((Z.rem n i) ≠ (0 : Int))) (PreH8 : (1 <= original)) (PreH9 : (original <= INT_MAX)) (PreH10 : (1 <= n)) (PreH11 : (n <= original)) (PreH12 : (2 <= i)) (PreH13 : (i <= original)) (PreH14 : (i <= n)) (PreH15 : ((0 : Int) <= cnt)) (PreH16 : (cnt < original)) (PreH17 : ((Zlength (factors)) = cnt)) (PreH18 : (FactorizationProgress original factors n i)) ,
  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** (intArray.undef_seg p_pre (0 : Int) 1)
  ** (intArray.seg p_pre 1 (1 + cnt) factors)
  ** (intArray.undef_seg p_pre (1 + cnt) original)
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def divide_entail_wit_1 : Prop :=
  (
forall (original : Int) (n_pre : Int) (p_pre : Int) (PreH1 : (n_pre = original)) (PreH2 : (1 <= original)) (PreH3 : (original <= INT_MAX)) ,
  (intArray.undef_full p_pre original)
|--
  EX factors : (List Int),
  “ (1 <= original) ” &&
  “ (original <= INT_MAX) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= original) ” &&
  “ (2 <= 2) ” &&
  “ (2 <= INT_MAX) ” &&
  “ (2 <= (original + 1)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) < original) ” &&
  “ ((Zlength (factors)) = (0 : Int)) ” &&
  “ (FactorizationProgress original factors n_pre 2) ”
  &&  (intArray.undef_seg p_pre (0 : Int) 1)
  ** (intArray.seg p_pre 1 (1 + (0 : Int)) factors)
  ** (intArray.undef_seg p_pre (1 + (0 : Int)) original)
) \/
(
forall (original : Int) (n_pre : Int) (p_pre : Int) (PreH1 : (n_pre = original)) (PreH2 : (1 <= original)) (PreH3 : (original <= INT_MAX)) ,
  (intArray.undef_full p_pre original)
|--
  EX factors : (List Int),
  “ (1 <= original) ” &&
  “ (original <= INT_MAX) ” &&
  “ (1 <= n_pre) ” &&
  “ (n_pre <= original) ” &&
  “ (2 <= 2) ” &&
  “ (2 <= INT_MAX) ” &&
  “ (2 <= (original + 1)) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) < original) ” &&
  “ ((Zlength (factors)) = (0 : Int)) ” &&
  “ (FactorizationProgress original factors n_pre 2) ”
  &&  (intArray.undef_seg p_pre (0 : Int) 1)
  ** (intArray.seg p_pre 1 (1 + (0 : Int)) factors)
  ** (intArray.undef_seg p_pre (1 + (0 : Int)) original)
)

noncomputable def divide_entail_wit_2 : Prop :=
  forall (original : Int) (p_pre : Int) (factors_2 : (List Int)) (cnt : Int) (i : Int) (n : Int) (PreH1 : (i <= n)) (PreH2 : (1 <= original)) (PreH3 : (original <= INT_MAX)) (PreH4 : (1 <= n)) (PreH5 : (n <= original)) (PreH6 : (2 <= i)) (PreH7 : (i <= INT_MAX)) (PreH8 : (i <= (original + 1))) (PreH9 : ((0 : Int) <= cnt)) (PreH10 : (cnt < original)) (PreH11 : ((Zlength (factors_2)) = cnt)) (PreH12 : (FactorizationProgress original factors_2 n i)) ,
  (intArray.undef_seg p_pre (0 : Int) 1)
  ** (intArray.seg p_pre 1 (1 + cnt) factors_2)
  ** (intArray.undef_seg p_pre (1 + cnt) original)
|--
  EX factors : (List Int),
  “ (1 <= original) ” &&
  “ (original <= INT_MAX) ” &&
  “ (1 <= n) ” &&
  “ (n <= original) ” &&
  “ (2 <= i) ” &&
  “ (i <= original) ” &&
  “ (i <= n) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt < original) ” &&
  “ ((Zlength (factors)) = cnt) ” &&
  “ (FactorizationProgress original factors n i) ”
  &&  (intArray.undef_seg p_pre (0 : Int) 1)
  ** (intArray.seg p_pre 1 (1 + cnt) factors)
  ** (intArray.undef_seg p_pre (1 + cnt) original)

noncomputable def divide_entail_wit_3_1 : Prop :=
  forall (original : Int) (p_pre : Int) (factors : (List Int)) (cnt : Int) (i : Int) (n : Int) (PreH1 : ((Z.rem n i) = (0 : Int))) (PreH2 : (1 <= original)) (PreH3 : (original <= INT_MAX)) (PreH4 : (1 <= n)) (PreH5 : (n <= original)) (PreH6 : (2 <= i)) (PreH7 : (i <= original)) (PreH8 : (n = 1)) (PreH9 : ((0 : Int) <= cnt)) (PreH10 : (cnt < original)) (PreH11 : ((Zlength (factors)) = cnt)) (PreH12 : (FactorizationProgress original factors n i)) ,
  ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** (intArray.undef_seg p_pre (0 : Int) 1)
  ** (intArray.seg p_pre 1 (1 + cnt) factors)
  ** (intArray.undef_seg p_pre (1 + cnt) original)
|--
  (“ ((cnt + 1) < original) ” &&
  “ (i <= INT_MAX) ” &&
  “ (n <= INT_MAX) ” &&
  “ (i >= INT_MIN) ” &&
  “ (n >= INT_MIN) ” &&
  “ ((Z.rem n i) = (0 : Int)) ” &&
  “ (1 <= original) ” &&
  “ (original <= INT_MAX) ” &&
  “ (1 <= n) ” &&
  “ (n <= original) ” &&
  “ (2 <= i) ” &&
  “ (i <= original) ” &&
  “ (n = 1) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt < original) ” &&
  “ ((Zlength (factors)) = cnt) ” &&
  “ (FactorizationProgress original factors n i) ”
  &&  ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_seg p_pre (0 : Int) 1)
  ** (intArray.seg p_pre 1 (1 + cnt) factors)
  ** (intArray.undef_seg p_pre (1 + cnt) original))
  ||
  (EX factors_2 : (List Int), EX cnt_2 : Int, EX i_2 : Int, EX n_2 : Int,
  “ ((cnt_2 + 1) < original) ” &&
  “ (i_2 <= INT_MAX) ” &&
  “ (n_2 <= INT_MAX) ” &&
  “ (i_2 >= INT_MIN) ” &&
  “ (n_2 >= INT_MIN) ” &&
  “ ((Z.rem n_2 i_2) = (0 : Int)) ” &&
  “ (1 <= original) ” &&
  “ (original <= INT_MAX) ” &&
  “ (1 <= n_2) ” &&
  “ (n_2 <= original) ” &&
  “ (2 <= i_2) ” &&
  “ (i_2 <= original) ” &&
  “ (i_2 <= n_2) ” &&
  “ ((0 : Int) <= cnt_2) ” &&
  “ (cnt_2 < original) ” &&
  “ ((Zlength (factors_2)) = cnt_2) ” &&
  “ (FactorizationProgress original factors_2 n_2 i_2) ”
  &&  ((( &( "cnt" ) )) # Int |-> (cnt_2))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((( &( "n" ) )) # Int |-> (n_2))
  ** ((( &( "i" ) )) # Int |-> (i_2))
  ** (intArray.undef_seg p_pre (0 : Int) 1)
  ** (intArray.seg p_pre 1 (1 + cnt_2) factors_2)
  ** (intArray.undef_seg p_pre (1 + cnt_2) original))

noncomputable def divide_entail_wit_3_2 : Prop :=
  forall (original : Int) (p_pre : Int) (factors_2 : (List Int)) (cnt_2 : Int) (i_2 : Int) (n_2 : Int) (PreH1 : ((Z.rem n_2 i_2) = (0 : Int))) (PreH2 : (1 <= original)) (PreH3 : (original <= INT_MAX)) (PreH4 : (1 <= n_2)) (PreH5 : (n_2 <= original)) (PreH6 : (2 <= i_2)) (PreH7 : (i_2 <= original)) (PreH8 : (i_2 <= n_2)) (PreH9 : ((0 : Int) <= cnt_2)) (PreH10 : (cnt_2 < original)) (PreH11 : ((Zlength (factors_2)) = cnt_2)) (PreH12 : (FactorizationProgress original factors_2 n_2 i_2)) ,
  ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((( &( "n" ) )) # Int |-> (n_2))
  ** ((( &( "i" ) )) # Int |-> (i_2))
  ** ((( &( "cnt" ) )) # Int |-> (cnt_2))
  ** (intArray.undef_seg p_pre (0 : Int) 1)
  ** (intArray.seg p_pre 1 (1 + cnt_2) factors_2)
  ** (intArray.undef_seg p_pre (1 + cnt_2) original)
|--
  (EX factors : (List Int), EX cnt : Int, EX i : Int, EX n : Int,
  “ ((cnt + 1) < original) ” &&
  “ (i <= INT_MAX) ” &&
  “ (n <= INT_MAX) ” &&
  “ (i >= INT_MIN) ” &&
  “ (n >= INT_MIN) ” &&
  “ ((Z.rem n i) = (0 : Int)) ” &&
  “ (1 <= original) ” &&
  “ (original <= INT_MAX) ” &&
  “ (1 <= n) ” &&
  “ (n <= original) ” &&
  “ (2 <= i) ” &&
  “ (i <= original) ” &&
  “ (n = 1) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt < original) ” &&
  “ ((Zlength (factors)) = cnt) ” &&
  “ (FactorizationProgress original factors n i) ”
  &&  ((( &( "cnt" ) )) # Int |-> (cnt))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** (intArray.undef_seg p_pre (0 : Int) 1)
  ** (intArray.seg p_pre 1 (1 + cnt) factors)
  ** (intArray.undef_seg p_pre (1 + cnt) original))
  ||
  (“ ((cnt_2 + 1) < original) ” &&
  “ (i_2 <= INT_MAX) ” &&
  “ (n_2 <= INT_MAX) ” &&
  “ (i_2 >= INT_MIN) ” &&
  “ (n_2 >= INT_MIN) ” &&
  “ ((Z.rem n_2 i_2) = (0 : Int)) ” &&
  “ (1 <= original) ” &&
  “ (original <= INT_MAX) ” &&
  “ (1 <= n_2) ” &&
  “ (n_2 <= original) ” &&
  “ (2 <= i_2) ” &&
  “ (i_2 <= original) ” &&
  “ (i_2 <= n_2) ” &&
  “ ((0 : Int) <= cnt_2) ” &&
  “ (cnt_2 < original) ” &&
  “ ((Zlength (factors_2)) = cnt_2) ” &&
  “ (FactorizationProgress original factors_2 n_2 i_2) ”
  &&  ((( &( "cnt" ) )) # Int |-> (cnt_2))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((( &( "n" ) )) # Int |-> (n_2))
  ** ((( &( "i" ) )) # Int |-> (i_2))
  ** (intArray.undef_seg p_pre (0 : Int) 1)
  ** (intArray.seg p_pre 1 (1 + cnt_2) factors_2)
  ** (intArray.undef_seg p_pre (1 + cnt_2) original))

noncomputable def divide_entail_wit_4_1 : Prop :=
  forall (original : Int) (p_pre : Int) (factors_2 : (List Int)) (cnt : Int) (i : Int) (n : Int) (PreH1 : ((cnt + 1) < original)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (n >= INT_MIN)) (PreH6 : ((Z.rem n i) = (0 : Int))) (PreH7 : (1 <= original)) (PreH8 : (original <= INT_MAX)) (PreH9 : (1 <= n)) (PreH10 : (n <= original)) (PreH11 : (2 <= i)) (PreH12 : (i <= original)) (PreH13 : (n = 1)) (PreH14 : ((0 : Int) <= cnt)) (PreH15 : (cnt < original)) (PreH16 : ((Zlength (factors_2)) = cnt)) (PreH17 : (FactorizationProgress original factors_2 n i)) ,
  (intArray.seg p_pre 1 ((1 + cnt) + 1) (factors_2 ++ (i :: (@List.nil Int))))
  ** (intArray.undef_seg p_pre ((1 + cnt) + 1) original)
  ** (intArray.undef_seg p_pre (0 : Int) 1)
|--
  (EX factors : (List Int),
  “ (1 <= original) ” &&
  “ (original <= INT_MAX) ” &&
  “ (1 <= (Z.quot n i)) ” &&
  “ ((Z.quot n i) <= original) ” &&
  “ (2 <= i) ” &&
  “ (i <= original) ” &&
  “ ((Z.quot n i) = 1) ” &&
  “ ((0 : Int) <= (cnt + 1)) ” &&
  “ ((cnt + 1) < original) ” &&
  “ ((Zlength (factors)) = (cnt + 1)) ” &&
  “ (FactorizationProgress original factors (Z.quot n i) i) ”
  &&  (intArray.undef_seg p_pre (0 : Int) 1)
  ** (intArray.seg p_pre 1 (1 + (cnt + 1)) factors)
  ** (intArray.undef_seg p_pre (1 + (cnt + 1)) original))
  ||
  (EX factors : (List Int),
  “ (1 <= original) ” &&
  “ (original <= INT_MAX) ” &&
  “ (1 <= (Z.quot n i)) ” &&
  “ ((Z.quot n i) <= original) ” &&
  “ (2 <= i) ” &&
  “ (i <= original) ” &&
  “ (i <= (Z.quot n i)) ” &&
  “ ((0 : Int) <= (cnt + 1)) ” &&
  “ ((cnt + 1) < original) ” &&
  “ ((Zlength (factors)) = (cnt + 1)) ” &&
  “ (FactorizationProgress original factors (Z.quot n i) i) ”
  &&  (intArray.undef_seg p_pre (0 : Int) 1)
  ** (intArray.seg p_pre 1 (1 + (cnt + 1)) factors)
  ** (intArray.undef_seg p_pre (1 + (cnt + 1)) original))

noncomputable def divide_entail_wit_4_2 : Prop :=
  forall (original : Int) (p_pre : Int) (factors_2 : (List Int)) (cnt : Int) (i : Int) (n : Int) (PreH1 : ((cnt + 1) < original)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (n >= INT_MIN)) (PreH6 : ((Z.rem n i) = (0 : Int))) (PreH7 : (1 <= original)) (PreH8 : (original <= INT_MAX)) (PreH9 : (1 <= n)) (PreH10 : (n <= original)) (PreH11 : (2 <= i)) (PreH12 : (i <= original)) (PreH13 : (i <= n)) (PreH14 : ((0 : Int) <= cnt)) (PreH15 : (cnt < original)) (PreH16 : ((Zlength (factors_2)) = cnt)) (PreH17 : (FactorizationProgress original factors_2 n i)) ,
  (intArray.seg p_pre 1 ((1 + cnt) + 1) (factors_2 ++ (i :: (@List.nil Int))))
  ** (intArray.undef_seg p_pre ((1 + cnt) + 1) original)
  ** (intArray.undef_seg p_pre (0 : Int) 1)
|--
  (EX factors : (List Int),
  “ (1 <= original) ” &&
  “ (original <= INT_MAX) ” &&
  “ (1 <= (Z.quot n i)) ” &&
  “ ((Z.quot n i) <= original) ” &&
  “ (2 <= i) ” &&
  “ (i <= original) ” &&
  “ ((Z.quot n i) = 1) ” &&
  “ ((0 : Int) <= (cnt + 1)) ” &&
  “ ((cnt + 1) < original) ” &&
  “ ((Zlength (factors)) = (cnt + 1)) ” &&
  “ (FactorizationProgress original factors (Z.quot n i) i) ”
  &&  (intArray.undef_seg p_pre (0 : Int) 1)
  ** (intArray.seg p_pre 1 (1 + (cnt + 1)) factors)
  ** (intArray.undef_seg p_pre (1 + (cnt + 1)) original))
  ||
  (EX factors : (List Int),
  “ (1 <= original) ” &&
  “ (original <= INT_MAX) ” &&
  “ (1 <= (Z.quot n i)) ” &&
  “ ((Z.quot n i) <= original) ” &&
  “ (2 <= i) ” &&
  “ (i <= original) ” &&
  “ (i <= (Z.quot n i)) ” &&
  “ ((0 : Int) <= (cnt + 1)) ” &&
  “ ((cnt + 1) < original) ” &&
  “ ((Zlength (factors)) = (cnt + 1)) ” &&
  “ (FactorizationProgress original factors (Z.quot n i) i) ”
  &&  (intArray.undef_seg p_pre (0 : Int) 1)
  ** (intArray.seg p_pre 1 (1 + (cnt + 1)) factors)
  ** (intArray.undef_seg p_pre (1 + (cnt + 1)) original))

noncomputable def divide_entail_wit_5 : Prop :=
  (
forall (original : Int) (p_pre : Int) (factors : (List Int)) (cnt : Int) (i : Int) (n : Int) (PreH1 : (n ≠ 1)) (PreH2 : ((Z.rem n i) ≠ (0 : Int))) (PreH3 : (1 <= original)) (PreH4 : (original <= INT_MAX)) (PreH5 : (1 <= n)) (PreH6 : (n <= original)) (PreH7 : (2 <= i)) (PreH8 : (i <= original)) (PreH9 : (i <= n)) (PreH10 : ((0 : Int) <= cnt)) (PreH11 : (cnt < original)) (PreH12 : ((Zlength (factors)) = cnt)) (PreH13 : (FactorizationProgress original factors n i)) ,
  ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** (intArray.undef_seg p_pre (0 : Int) 1)
  ** (intArray.seg p_pre 1 (1 + cnt) factors)
  ** (intArray.undef_seg p_pre (1 + cnt) original)
|--
  “ (i < INT_MAX) ” &&
  “ (cnt <= INT_MAX) ” &&
  “ (n <= INT_MAX) ” &&
  “ (cnt >= INT_MIN) ” &&
  “ (n >= INT_MIN) ” &&
  “ (n ≠ 1) ” &&
  “ ((Z.rem n i) ≠ (0 : Int)) ” &&
  “ (1 <= original) ” &&
  “ (original <= INT_MAX) ” &&
  “ (1 <= n) ” &&
  “ (n <= original) ” &&
  “ (2 <= i) ” &&
  “ (i <= original) ” &&
  “ (i <= n) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt < original) ” &&
  “ ((Zlength (factors)) = cnt) ” &&
  “ (FactorizationProgress original factors n i) ”
  &&  ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "p" ) )) # Ptr |-> (p_pre))
  ** ((( &( "n" ) )) # Int |-> (n))
  ** ((( &( "cnt" ) )) # Int |-> (cnt))
  ** (intArray.undef_seg p_pre (0 : Int) 1)
  ** (intArray.seg p_pre 1 (1 + cnt) factors)
  ** (intArray.undef_seg p_pre (1 + cnt) original)
) \/
(
forall (original : Int) (factors : (List Int)) (cnt : Int) (i : Int) (n : Int) (PreH1 : (cnt <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n <= INT_MAX)) (PreH4 : (cnt >= INT_MIN)) (PreH5 : (i >= INT_MIN)) (PreH6 : (n >= INT_MIN)) (PreH7 : (n ≠ 1)) (PreH8 : ((Z.rem n i) ≠ (0 : Int))) (PreH9 : (1 <= original)) (PreH10 : (original <= INT_MAX)) (PreH11 : (1 <= n)) (PreH12 : (n <= original)) (PreH13 : (2 <= i)) (PreH14 : (i <= original)) (PreH15 : (i <= n)) (PreH16 : ((0 : Int) <= cnt)) (PreH17 : (cnt < original)) (PreH18 : ((Zlength (factors)) = cnt)) (PreH19 : (FactorizationProgress original factors n i)) ,
  TT && emp 
|--
  “ (i < INT_MAX) ”
  &&  emp
)

noncomputable def divide_entail_wit_5_split_goal_1 : Prop :=
  forall (original : Int) (factors : (List Int)) (cnt : Int) (i : Int) (n : Int) (PreH1 : (cnt <= INT_MAX)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n <= INT_MAX)) (PreH4 : (cnt >= INT_MIN)) (PreH5 : (i >= INT_MIN)) (PreH6 : (n >= INT_MIN)) (PreH7 : (n ≠ 1)) (PreH8 : ((Z.rem n i) ≠ (0 : Int))) (PreH9 : (1 <= original)) (PreH10 : (original <= INT_MAX)) (PreH11 : (1 <= n)) (PreH12 : (n <= original)) (PreH13 : (2 <= i)) (PreH14 : (i <= original)) (PreH15 : (i <= n)) (PreH16 : ((0 : Int) <= cnt)) (PreH17 : (cnt < original)) (PreH18 : ((Zlength (factors)) = cnt)) (PreH19 : (FactorizationProgress original factors n i)) ,
  (i < INT_MAX)

noncomputable def divide_entail_wit_6 : Prop :=
  (
forall (original : Int) (p_pre : Int) (factors_2 : (List Int)) (cnt : Int) (i : Int) (n : Int) (PreH1 : (i < INT_MAX)) (PreH2 : (cnt <= INT_MAX)) (PreH3 : (n <= INT_MAX)) (PreH4 : (cnt >= INT_MIN)) (PreH5 : (n >= INT_MIN)) (PreH6 : (n ≠ 1)) (PreH7 : ((Z.rem n i) ≠ (0 : Int))) (PreH8 : (1 <= original)) (PreH9 : (original <= INT_MAX)) (PreH10 : (1 <= n)) (PreH11 : (n <= original)) (PreH12 : (2 <= i)) (PreH13 : (i <= original)) (PreH14 : (i <= n)) (PreH15 : ((0 : Int) <= cnt)) (PreH16 : (cnt < original)) (PreH17 : ((Zlength (factors_2)) = cnt)) (PreH18 : (FactorizationProgress original factors_2 n i)) ,
  (intArray.undef_seg p_pre (0 : Int) 1)
  ** (intArray.seg p_pre 1 (1 + cnt) factors_2)
  ** (intArray.undef_seg p_pre (1 + cnt) original)
|--
  EX factors : (List Int),
  “ (1 <= original) ” &&
  “ (original <= INT_MAX) ” &&
  “ (1 <= n) ” &&
  “ (n <= original) ” &&
  “ (2 <= (i + 1)) ” &&
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((i + 1) <= (original + 1)) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt < original) ” &&
  “ ((Zlength (factors)) = cnt) ” &&
  “ (FactorizationProgress original factors n (i + 1)) ”
  &&  (intArray.undef_seg p_pre (0 : Int) 1)
  ** (intArray.seg p_pre 1 (1 + cnt) factors)
  ** (intArray.undef_seg p_pre (1 + cnt) original)
) \/
(
forall (original : Int) (factors_2 : (List Int)) (cnt : Int) (i : Int) (n : Int) (PreH1 : (i < INT_MAX)) (PreH2 : (cnt <= INT_MAX)) (PreH3 : (n <= INT_MAX)) (PreH4 : (cnt >= INT_MIN)) (PreH5 : (n >= INT_MIN)) (PreH6 : (n ≠ 1)) (PreH7 : ((Z.rem n i) ≠ (0 : Int))) (PreH8 : (1 <= original)) (PreH9 : (original <= INT_MAX)) (PreH10 : (1 <= n)) (PreH11 : (n <= original)) (PreH12 : (2 <= i)) (PreH13 : (i <= original)) (PreH14 : (i <= n)) (PreH15 : ((0 : Int) <= cnt)) (PreH16 : (cnt < original)) (PreH17 : ((Zlength (factors_2)) = cnt)) (PreH18 : (FactorizationProgress original factors_2 n i)) ,
  TT && emp 
|--
  “ (FactorizationProgress original factors_2 n (i + 1)) ”
  &&  emp
)

noncomputable def divide_entail_wit_6_split_goal_1 : Prop :=
  forall (original : Int) (factors_2 : (List Int)) (cnt : Int) (i : Int) (n : Int) (PreH1 : (i < INT_MAX)) (PreH2 : (cnt <= INT_MAX)) (PreH3 : (n <= INT_MAX)) (PreH4 : (cnt >= INT_MIN)) (PreH5 : (n >= INT_MIN)) (PreH6 : (n ≠ 1)) (PreH7 : ((Z.rem n i) ≠ (0 : Int))) (PreH8 : (1 <= original)) (PreH9 : (original <= INT_MAX)) (PreH10 : (1 <= n)) (PreH11 : (n <= original)) (PreH12 : (2 <= i)) (PreH13 : (i <= original)) (PreH14 : (i <= n)) (PreH15 : ((0 : Int) <= cnt)) (PreH16 : (cnt < original)) (PreH17 : ((Zlength (factors_2)) = cnt)) (PreH18 : (FactorizationProgress original factors_2 n i)) ,
  (FactorizationProgress original factors_2 n (i + 1))

noncomputable def divide_return_wit_1 : Prop :=
  (
forall (original : Int) (p_pre : Int) (factors_2 : (List Int)) (cnt : Int) (i : Int) (n : Int) (PreH1 : (i > n)) (PreH2 : (1 <= original)) (PreH3 : (original <= INT_MAX)) (PreH4 : (1 <= n)) (PreH5 : (n <= original)) (PreH6 : (2 <= i)) (PreH7 : (i <= INT_MAX)) (PreH8 : (i <= (original + 1))) (PreH9 : ((0 : Int) <= cnt)) (PreH10 : (cnt < original)) (PreH11 : ((Zlength (factors_2)) = cnt)) (PreH12 : (FactorizationProgress original factors_2 n i)) ,
  (intArray.undef_seg p_pre (0 : Int) 1)
  ** (intArray.seg p_pre 1 (1 + cnt) factors_2)
  ** (intArray.undef_seg p_pre (1 + cnt) original)
|--
  EX factors : (List Int),
  “ (PrimeFactorization original factors) ”
  &&  (intArray.undef_seg p_pre (0 : Int) 1)
  ** (intArray.seg p_pre 1 (1 + (Zlength (factors))) factors)
  ** (intArray.undef_seg p_pre (1 + (Zlength (factors))) original)
) \/
(
forall (original : Int) (p_pre : Int) (factors_2 : (List Int)) (cnt : Int) (i : Int) (n : Int) (PreH1 : (i > n)) (PreH2 : (1 <= original)) (PreH3 : (original <= INT_MAX)) (PreH4 : (1 <= n)) (PreH5 : (n <= original)) (PreH6 : (2 <= i)) (PreH7 : (i <= INT_MAX)) (PreH8 : (i <= (original + 1))) (PreH9 : ((0 : Int) <= cnt)) (PreH10 : (cnt < original)) (PreH11 : ((Zlength (factors_2)) = cnt)) (PreH12 : (FactorizationProgress original factors_2 n i)) ,
  (intArray.seg p_pre 1 (1 + cnt) factors_2)
  ** (intArray.undef_seg p_pre (1 + cnt) original)
|--
  EX factors : (List Int),
  “ (PrimeFactorization original factors) ”
  &&  (intArray.seg p_pre 1 (1 + (Zlength (factors))) factors)
  ** (intArray.undef_seg p_pre (1 + (Zlength (factors))) original)
)

noncomputable def divide_return_wit_2 : Prop :=
  (
forall (original : Int) (p_pre : Int) (factors_2 : (List Int)) (cnt : Int) (i : Int) (n : Int) (PreH1 : (n = 1)) (PreH2 : ((Z.rem n i) ≠ (0 : Int))) (PreH3 : (1 <= original)) (PreH4 : (original <= INT_MAX)) (PreH5 : (1 <= n)) (PreH6 : (n <= original)) (PreH7 : (2 <= i)) (PreH8 : (i <= original)) (PreH9 : (n = 1)) (PreH10 : ((0 : Int) <= cnt)) (PreH11 : (cnt < original)) (PreH12 : ((Zlength (factors_2)) = cnt)) (PreH13 : (FactorizationProgress original factors_2 n i)) ,
  (intArray.undef_seg p_pre (0 : Int) 1)
  ** (intArray.seg p_pre 1 (1 + cnt) factors_2)
  ** (intArray.undef_seg p_pre (1 + cnt) original)
|--
  EX factors : (List Int),
  “ (PrimeFactorization original factors) ”
  &&  (intArray.undef_seg p_pre (0 : Int) 1)
  ** (intArray.seg p_pre 1 (1 + (Zlength (factors))) factors)
  ** (intArray.undef_seg p_pre (1 + (Zlength (factors))) original)
) \/
(
forall (original : Int) (p_pre : Int) (factors_2 : (List Int)) (cnt : Int) (i : Int) (n : Int) (PreH1 : (n = 1)) (PreH2 : ((Z.rem n i) ≠ (0 : Int))) (PreH3 : (1 <= original)) (PreH4 : (original <= INT_MAX)) (PreH5 : (1 <= n)) (PreH6 : (n <= original)) (PreH7 : (2 <= i)) (PreH8 : (i <= original)) (PreH9 : (n = 1)) (PreH10 : ((0 : Int) <= cnt)) (PreH11 : (cnt < original)) (PreH12 : ((Zlength (factors_2)) = cnt)) (PreH13 : (FactorizationProgress original factors_2 n i)) ,
  (intArray.seg p_pre 1 (1 + cnt) factors_2)
  ** (intArray.undef_seg p_pre (1 + cnt) original)
|--
  EX factors : (List Int),
  “ (PrimeFactorization original factors) ”
  &&  (intArray.seg p_pre 1 (1 + (Zlength (factors))) factors)
  ** (intArray.undef_seg p_pre (1 + (Zlength (factors))) original)
)

noncomputable def divide_partial_solve_wit_1 : Prop :=
  forall (original : Int) (p_pre : Int) (factors : (List Int)) (cnt : Int) (i : Int) (n : Int) (PreH1 : ((cnt + 1) < original)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (n >= INT_MIN)) (PreH6 : ((Z.rem n i) = (0 : Int))) (PreH7 : (1 <= original)) (PreH8 : (original <= INT_MAX)) (PreH9 : (1 <= n)) (PreH10 : (n <= original)) (PreH11 : (2 <= i)) (PreH12 : (i <= original)) (PreH13 : (n = 1)) (PreH14 : ((0 : Int) <= cnt)) (PreH15 : (cnt < original)) (PreH16 : ((Zlength (factors)) = cnt)) (PreH17 : (FactorizationProgress original factors n i)) ,
  (intArray.undef_seg p_pre (0 : Int) 1)
  ** (intArray.seg p_pre 1 (1 + cnt) factors)
  ** (intArray.undef_seg p_pre (1 + cnt) original)
|--
  “ ((cnt + 1) < original) ” &&
  “ (i <= INT_MAX) ” &&
  “ (n <= INT_MAX) ” &&
  “ (i >= INT_MIN) ” &&
  “ (n >= INT_MIN) ” &&
  “ ((Z.rem n i) = (0 : Int)) ” &&
  “ (1 <= original) ” &&
  “ (original <= INT_MAX) ” &&
  “ (1 <= n) ” &&
  “ (n <= original) ” &&
  “ (2 <= i) ” &&
  “ (i <= original) ” &&
  “ (n = 1) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt < original) ” &&
  “ ((Zlength (factors)) = cnt) ” &&
  “ (FactorizationProgress original factors n i) ”
  &&  (((p_pre + ((cnt + 1) * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_missing_i p_pre (cnt + 1) (1 + cnt) original)
  ** (intArray.undef_seg p_pre (0 : Int) 1)
  ** (intArray.seg p_pre 1 (1 + cnt) factors)

noncomputable def divide_partial_solve_wit_2 : Prop :=
  forall (original : Int) (p_pre : Int) (factors : (List Int)) (cnt : Int) (i : Int) (n : Int) (PreH1 : ((cnt + 1) < original)) (PreH2 : (i <= INT_MAX)) (PreH3 : (n <= INT_MAX)) (PreH4 : (i >= INT_MIN)) (PreH5 : (n >= INT_MIN)) (PreH6 : ((Z.rem n i) = (0 : Int))) (PreH7 : (1 <= original)) (PreH8 : (original <= INT_MAX)) (PreH9 : (1 <= n)) (PreH10 : (n <= original)) (PreH11 : (2 <= i)) (PreH12 : (i <= original)) (PreH13 : (i <= n)) (PreH14 : ((0 : Int) <= cnt)) (PreH15 : (cnt < original)) (PreH16 : ((Zlength (factors)) = cnt)) (PreH17 : (FactorizationProgress original factors n i)) ,
  (intArray.undef_seg p_pre (0 : Int) 1)
  ** (intArray.seg p_pre 1 (1 + cnt) factors)
  ** (intArray.undef_seg p_pre (1 + cnt) original)
|--
  “ ((cnt + 1) < original) ” &&
  “ (i <= INT_MAX) ” &&
  “ (n <= INT_MAX) ” &&
  “ (i >= INT_MIN) ” &&
  “ (n >= INT_MIN) ” &&
  “ ((Z.rem n i) = (0 : Int)) ” &&
  “ (1 <= original) ” &&
  “ (original <= INT_MAX) ” &&
  “ (1 <= n) ” &&
  “ (n <= original) ” &&
  “ (2 <= i) ” &&
  “ (i <= original) ” &&
  “ (i <= n) ” &&
  “ ((0 : Int) <= cnt) ” &&
  “ (cnt < original) ” &&
  “ ((Zlength (factors)) = cnt) ” &&
  “ (FactorizationProgress original factors n i) ”
  &&  (((p_pre + ((cnt + 1) * sizeof(INT)))) # Int |->_)
  ** (intArray.undef_missing_i p_pre (cnt + 1) (1 + cnt) original)
  ** (intArray.undef_seg p_pre (0 : Int) 1)
  ** (intArray.seg p_pre 1 (1 + cnt) factors)


structure VC_Correct : Type where
  proof_of_divide_safety_wit_1 : divide_safety_wit_1
  proof_of_divide_safety_wit_2 : divide_safety_wit_2
  proof_of_divide_safety_wit_3 : divide_safety_wit_3
  proof_of_divide_safety_wit_4 : divide_safety_wit_4
  proof_of_divide_safety_wit_5 : divide_safety_wit_5
  proof_of_divide_safety_wit_6 : divide_safety_wit_6
  proof_of_divide_safety_wit_7 : divide_safety_wit_7
  proof_of_divide_safety_wit_8 : divide_safety_wit_8
  proof_of_divide_safety_wit_9 : divide_safety_wit_9
  proof_of_divide_safety_wit_10 : divide_safety_wit_10
  proof_of_divide_safety_wit_11 : divide_safety_wit_11
  proof_of_divide_safety_wit_12 : divide_safety_wit_12
  proof_of_divide_safety_wit_13 : divide_safety_wit_13
  proof_of_divide_safety_wit_14 : divide_safety_wit_14
  proof_of_divide_safety_wit_15 : divide_safety_wit_15
  proof_of_divide_entail_wit_2 : divide_entail_wit_2
  proof_of_divide_partial_solve_wit_1 : divide_partial_solve_wit_1
  proof_of_divide_partial_solve_wit_2 : divide_partial_solve_wit_2
  proof_of_divide_entail_wit_1 : divide_entail_wit_1
  proof_of_divide_entail_wit_3_1 : divide_entail_wit_3_1
  proof_of_divide_entail_wit_3_2 : divide_entail_wit_3_2
  proof_of_divide_entail_wit_4_1 : divide_entail_wit_4_1
  proof_of_divide_entail_wit_4_2 : divide_entail_wit_4_2
  proof_of_divide_entail_wit_5 : divide_entail_wit_5
  proof_of_divide_entail_wit_6 : divide_entail_wit_6
  proof_of_divide_return_wit_1 : divide_return_wit_1
  proof_of_divide_return_wit_2 : divide_return_wit_2

end SimpleC.EE.LLM_bench.Algorithms.integer_divide.integer_divide_goal
