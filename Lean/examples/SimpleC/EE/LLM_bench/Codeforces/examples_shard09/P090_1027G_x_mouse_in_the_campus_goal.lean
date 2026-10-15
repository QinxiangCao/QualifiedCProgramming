import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance P090_1027G_x_mouse_in_the_campus_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def mulmod_safety_wit_1 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (PreH1 : (a_pre = a0)) (PreH2 : (b_pre = b0)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (1 <= modulus0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : ((0 : Int) <= a0)) (PreH7 : (a0 <= 18446744073709551615)) (PreH8 : ((0 : Int) <= b0)) (PreH9 : (b0 <= 18446744073709551615)) ,
  ((( &( "r" ) )) # UInt64 |->_)
  ** ((( &( "a" ) )) # UInt64 |-> (a_pre))
  ** ((( &( "b" ) )) # UInt64 |-> (b_pre))
  ** ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def mulmod_safety_wit_2 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (PreH1 : (a_pre = a0)) (PreH2 : (b_pre = b0)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (1 <= modulus0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : ((0 : Int) <= a0)) (PreH7 : (a0 <= 18446744073709551615)) (PreH8 : ((0 : Int) <= b0)) (PreH9 : (b0 <= 18446744073709551615)) ,
  ((( &( "r" ) )) # UInt64 |-> ((0 : Int)))
  ** ((( &( "a" ) )) # UInt64 |-> (a_pre))
  ** ((( &( "b" ) )) # UInt64 |-> (b_pre))
  ** ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
|--
  “ (modulus_pre ≠ (0 : Int)) ”

noncomputable def mulmod_safety_wit_3 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (PreH1 : (a_pre = a0)) (PreH2 : (b_pre = b0)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (1 <= modulus0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : ((0 : Int) <= a0)) (PreH7 : (a0 <= 18446744073709551615)) (PreH8 : ((0 : Int) <= b0)) (PreH9 : (b0 <= 18446744073709551615)) ,
  ((( &( "r" ) )) # UInt64 |-> ((0 : Int)))
  ** ((( &( "a" ) )) # UInt64 |-> ((Z.rem a_pre modulus_pre)))
  ** ((( &( "b" ) )) # UInt64 |-> (b_pre))
  ** ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
|--
  “ (modulus_pre ≠ (0 : Int)) ”

noncomputable def mulmod_safety_wit_4 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : (a0 = a_pre)) (PreH2 : (b0 = b_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (1 <= modulus_pre)) (PreH5 : (modulus_pre <= 100000000000000)) (PreH6 : ((0 : Int) <= a_pre)) (PreH7 : ((0 : Int) <= b_pre)) (PreH8 : ((0 : Int) <= a)) (PreH9 : (a < modulus_pre)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b < modulus_pre)) (PreH12 : ((0 : Int) <= r)) (PreH13 : (r < modulus_pre)) (PreH14 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH15 : (b ≠ (0 : Int))) ,
  ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "a" ) )) # UInt64 |-> (a))
  ** ((( &( "b" ) )) # UInt64 |-> (b))
  ** ((( &( "r" ) )) # UInt64 |-> (r))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def mulmod_safety_wit_5 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((r + a) >= modulus_pre)) (PreH2 : (a0 = a_pre)) (PreH3 : (b0 = b_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (1 <= modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : ((0 : Int) <= a_pre)) (PreH8 : ((0 : Int) <= b_pre)) (PreH9 : ((0 : Int) <= a)) (PreH10 : (a < modulus_pre)) (PreH11 : ((0 : Int) <= b)) (PreH12 : (b < modulus_pre)) (PreH13 : ((0 : Int) <= r)) (PreH14 : (r < modulus_pre)) (PreH15 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH16 : (b ≠ (0 : Int))) (PreH17 : ((Z.land b 1) ≠ (0 : Int))) ,
  ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "a" ) )) # UInt64 |-> (a))
  ** ((( &( "b" ) )) # UInt64 |-> (b))
  ** ((( &( "r" ) )) # UInt64 |-> (((r + a) - modulus_pre)))
|--
  “ (1 <= 63) ” &&
  “ ((0 : Int) <= 1) ”

noncomputable def mulmod_safety_wit_6 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((r + a) >= modulus_pre)) (PreH2 : (a0 = a_pre)) (PreH3 : (b0 = b_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (1 <= modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : ((0 : Int) <= a_pre)) (PreH8 : ((0 : Int) <= b_pre)) (PreH9 : ((0 : Int) <= a)) (PreH10 : (a < modulus_pre)) (PreH11 : ((0 : Int) <= b)) (PreH12 : (b < modulus_pre)) (PreH13 : ((0 : Int) <= r)) (PreH14 : (r < modulus_pre)) (PreH15 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH16 : (b ≠ (0 : Int))) (PreH17 : ((Z.land b 1) ≠ (0 : Int))) ,
  ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "a" ) )) # UInt64 |-> (a))
  ** ((( &( "b" ) )) # UInt64 |-> (b))
  ** ((( &( "r" ) )) # UInt64 |-> (((r + a) - modulus_pre)))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def mulmod_safety_wit_7 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((r + a) < modulus_pre)) (PreH2 : (a0 = a_pre)) (PreH3 : (b0 = b_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (1 <= modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : ((0 : Int) <= a_pre)) (PreH8 : ((0 : Int) <= b_pre)) (PreH9 : ((0 : Int) <= a)) (PreH10 : (a < modulus_pre)) (PreH11 : ((0 : Int) <= b)) (PreH12 : (b < modulus_pre)) (PreH13 : ((0 : Int) <= r)) (PreH14 : (r < modulus_pre)) (PreH15 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH16 : (b ≠ (0 : Int))) (PreH17 : ((Z.land b 1) ≠ (0 : Int))) ,
  ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "a" ) )) # UInt64 |-> (a))
  ** ((( &( "b" ) )) # UInt64 |-> (b))
  ** ((( &( "r" ) )) # UInt64 |-> ((r + a)))
|--
  “ (1 <= 63) ” &&
  “ ((0 : Int) <= 1) ”

noncomputable def mulmod_safety_wit_8 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((r + a) < modulus_pre)) (PreH2 : (a0 = a_pre)) (PreH3 : (b0 = b_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (1 <= modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : ((0 : Int) <= a_pre)) (PreH8 : ((0 : Int) <= b_pre)) (PreH9 : ((0 : Int) <= a)) (PreH10 : (a < modulus_pre)) (PreH11 : ((0 : Int) <= b)) (PreH12 : (b < modulus_pre)) (PreH13 : ((0 : Int) <= r)) (PreH14 : (r < modulus_pre)) (PreH15 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH16 : (b ≠ (0 : Int))) (PreH17 : ((Z.land b 1) ≠ (0 : Int))) ,
  ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "a" ) )) # UInt64 |-> (a))
  ** ((( &( "b" ) )) # UInt64 |-> (b))
  ** ((( &( "r" ) )) # UInt64 |-> ((r + a)))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def mulmod_safety_wit_9 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : (a0 = a_pre)) (PreH2 : (b0 = b_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (1 <= modulus_pre)) (PreH5 : (modulus_pre <= 100000000000000)) (PreH6 : ((0 : Int) <= a_pre)) (PreH7 : ((0 : Int) <= b_pre)) (PreH8 : ((0 : Int) <= a)) (PreH9 : (a < modulus_pre)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b < modulus_pre)) (PreH12 : ((0 : Int) <= r)) (PreH13 : (r < modulus_pre)) (PreH14 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH15 : (b ≠ (0 : Int))) (PreH16 : ((Z.land b 1) = (0 : Int))) ,
  ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "a" ) )) # UInt64 |-> (a))
  ** ((( &( "b" ) )) # UInt64 |-> (b))
  ** ((( &( "r" ) )) # UInt64 |-> (r))
|--
  “ (1 <= 63) ” &&
  “ ((0 : Int) <= 1) ”

noncomputable def mulmod_safety_wit_10 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : (a0 = a_pre)) (PreH2 : (b0 = b_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (1 <= modulus_pre)) (PreH5 : (modulus_pre <= 100000000000000)) (PreH6 : ((0 : Int) <= a_pre)) (PreH7 : ((0 : Int) <= b_pre)) (PreH8 : ((0 : Int) <= a)) (PreH9 : (a < modulus_pre)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b < modulus_pre)) (PreH12 : ((0 : Int) <= r)) (PreH13 : (r < modulus_pre)) (PreH14 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH15 : (b ≠ (0 : Int))) (PreH16 : ((Z.land b 1) = (0 : Int))) ,
  ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "a" ) )) # UInt64 |-> (a))
  ** ((( &( "b" ) )) # UInt64 |-> (b))
  ** ((( &( "r" ) )) # UInt64 |-> (r))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def mulmod_safety_wit_11 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : ((r + a) >= modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : ((0 : Int) <= a_pre)) (PreH9 : ((0 : Int) <= b_pre)) (PreH10 : ((0 : Int) <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : ((0 : Int) <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH17 : (b ≠ (0 : Int))) (PreH18 : ((Z.land b 1) ≠ (0 : Int))) ,
  ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "a" ) )) # UInt64 |-> (((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus_pre)))
  ** ((( &( "b" ) )) # UInt64 |-> (b))
  ** ((( &( "r" ) )) # UInt64 |-> (((r + a) - modulus_pre)))
|--
  “ (1 <= 63) ” &&
  “ ((0 : Int) <= 1) ”

noncomputable def mulmod_safety_wit_12 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : ((r + a) >= modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : ((0 : Int) <= a_pre)) (PreH9 : ((0 : Int) <= b_pre)) (PreH10 : ((0 : Int) <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : ((0 : Int) <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH17 : (b ≠ (0 : Int))) (PreH18 : ((Z.land b 1) ≠ (0 : Int))) ,
  ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "a" ) )) # UInt64 |-> (((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus_pre)))
  ** ((( &( "b" ) )) # UInt64 |-> (b))
  ** ((( &( "r" ) )) # UInt64 |-> (((r + a) - modulus_pre)))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def mulmod_safety_wit_13 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : ((r + a) < modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : ((0 : Int) <= a_pre)) (PreH9 : ((0 : Int) <= b_pre)) (PreH10 : ((0 : Int) <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : ((0 : Int) <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH17 : (b ≠ (0 : Int))) (PreH18 : ((Z.land b 1) ≠ (0 : Int))) ,
  ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "a" ) )) # UInt64 |-> (((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus_pre)))
  ** ((( &( "b" ) )) # UInt64 |-> (b))
  ** ((( &( "r" ) )) # UInt64 |-> ((r + a)))
|--
  “ (1 <= 63) ” &&
  “ ((0 : Int) <= 1) ”

noncomputable def mulmod_safety_wit_14 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : ((r + a) < modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : ((0 : Int) <= a_pre)) (PreH9 : ((0 : Int) <= b_pre)) (PreH10 : ((0 : Int) <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : ((0 : Int) <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH17 : (b ≠ (0 : Int))) (PreH18 : ((Z.land b 1) ≠ (0 : Int))) ,
  ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "a" ) )) # UInt64 |-> (((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus_pre)))
  ** ((( &( "b" ) )) # UInt64 |-> (b))
  ** ((( &( "r" ) )) # UInt64 |-> ((r + a)))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def mulmod_safety_wit_15 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : (a0 = a_pre)) (PreH3 : (b0 = b_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (1 <= modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : ((0 : Int) <= a_pre)) (PreH8 : ((0 : Int) <= b_pre)) (PreH9 : ((0 : Int) <= a)) (PreH10 : (a < modulus_pre)) (PreH11 : ((0 : Int) <= b)) (PreH12 : (b < modulus_pre)) (PreH13 : ((0 : Int) <= r)) (PreH14 : (r < modulus_pre)) (PreH15 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH16 : (b ≠ (0 : Int))) (PreH17 : ((Z.land b 1) = (0 : Int))) ,
  ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "a" ) )) # UInt64 |-> (((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus_pre)))
  ** ((( &( "b" ) )) # UInt64 |-> (b))
  ** ((( &( "r" ) )) # UInt64 |-> (r))
|--
  “ (1 <= 63) ” &&
  “ ((0 : Int) <= 1) ”

noncomputable def mulmod_safety_wit_16 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : (a0 = a_pre)) (PreH3 : (b0 = b_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (1 <= modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : ((0 : Int) <= a_pre)) (PreH8 : ((0 : Int) <= b_pre)) (PreH9 : ((0 : Int) <= a)) (PreH10 : (a < modulus_pre)) (PreH11 : ((0 : Int) <= b)) (PreH12 : (b < modulus_pre)) (PreH13 : ((0 : Int) <= r)) (PreH14 : (r < modulus_pre)) (PreH15 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH16 : (b ≠ (0 : Int))) (PreH17 : ((Z.land b 1) = (0 : Int))) ,
  ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "a" ) )) # UInt64 |-> (((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus_pre)))
  ** ((( &( "b" ) )) # UInt64 |-> (b))
  ** ((( &( "r" ) )) # UInt64 |-> (r))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def mulmod_safety_wit_17 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : ((r + a) >= modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : ((0 : Int) <= a_pre)) (PreH9 : ((0 : Int) <= b_pre)) (PreH10 : ((0 : Int) <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : ((0 : Int) <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH17 : (b ≠ (0 : Int))) (PreH18 : ((Z.land b 1) ≠ (0 : Int))) ,
  ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "a" ) )) # UInt64 |-> ((unsigned_last_nbits ((Z.shiftl a 1)) (64))))
  ** ((( &( "b" ) )) # UInt64 |-> (b))
  ** ((( &( "r" ) )) # UInt64 |-> (((r + a) - modulus_pre)))
|--
  “ (1 <= 63) ” &&
  “ ((0 : Int) <= 1) ”

noncomputable def mulmod_safety_wit_18 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : ((r + a) >= modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : ((0 : Int) <= a_pre)) (PreH9 : ((0 : Int) <= b_pre)) (PreH10 : ((0 : Int) <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : ((0 : Int) <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH17 : (b ≠ (0 : Int))) (PreH18 : ((Z.land b 1) ≠ (0 : Int))) ,
  ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "a" ) )) # UInt64 |-> ((unsigned_last_nbits ((Z.shiftl a 1)) (64))))
  ** ((( &( "b" ) )) # UInt64 |-> (b))
  ** ((( &( "r" ) )) # UInt64 |-> (((r + a) - modulus_pre)))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def mulmod_safety_wit_19 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : ((r + a) < modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : ((0 : Int) <= a_pre)) (PreH9 : ((0 : Int) <= b_pre)) (PreH10 : ((0 : Int) <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : ((0 : Int) <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH17 : (b ≠ (0 : Int))) (PreH18 : ((Z.land b 1) ≠ (0 : Int))) ,
  ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "a" ) )) # UInt64 |-> ((unsigned_last_nbits ((Z.shiftl a 1)) (64))))
  ** ((( &( "b" ) )) # UInt64 |-> (b))
  ** ((( &( "r" ) )) # UInt64 |-> ((r + a)))
|--
  “ (1 <= 63) ” &&
  “ ((0 : Int) <= 1) ”

noncomputable def mulmod_safety_wit_20 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : ((r + a) < modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : ((0 : Int) <= a_pre)) (PreH9 : ((0 : Int) <= b_pre)) (PreH10 : ((0 : Int) <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : ((0 : Int) <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH17 : (b ≠ (0 : Int))) (PreH18 : ((Z.land b 1) ≠ (0 : Int))) ,
  ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "a" ) )) # UInt64 |-> ((unsigned_last_nbits ((Z.shiftl a 1)) (64))))
  ** ((( &( "b" ) )) # UInt64 |-> (b))
  ** ((( &( "r" ) )) # UInt64 |-> ((r + a)))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def mulmod_safety_wit_21 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : (a0 = a_pre)) (PreH3 : (b0 = b_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (1 <= modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : ((0 : Int) <= a_pre)) (PreH8 : ((0 : Int) <= b_pre)) (PreH9 : ((0 : Int) <= a)) (PreH10 : (a < modulus_pre)) (PreH11 : ((0 : Int) <= b)) (PreH12 : (b < modulus_pre)) (PreH13 : ((0 : Int) <= r)) (PreH14 : (r < modulus_pre)) (PreH15 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH16 : (b ≠ (0 : Int))) (PreH17 : ((Z.land b 1) = (0 : Int))) ,
  ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "a" ) )) # UInt64 |-> ((unsigned_last_nbits ((Z.shiftl a 1)) (64))))
  ** ((( &( "b" ) )) # UInt64 |-> (b))
  ** ((( &( "r" ) )) # UInt64 |-> (r))
|--
  “ (1 <= 63) ” &&
  “ ((0 : Int) <= 1) ”

noncomputable def mulmod_safety_wit_22 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : (a0 = a_pre)) (PreH3 : (b0 = b_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (1 <= modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : ((0 : Int) <= a_pre)) (PreH8 : ((0 : Int) <= b_pre)) (PreH9 : ((0 : Int) <= a)) (PreH10 : (a < modulus_pre)) (PreH11 : ((0 : Int) <= b)) (PreH12 : (b < modulus_pre)) (PreH13 : ((0 : Int) <= r)) (PreH14 : (r < modulus_pre)) (PreH15 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH16 : (b ≠ (0 : Int))) (PreH17 : ((Z.land b 1) = (0 : Int))) ,
  ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "a" ) )) # UInt64 |-> ((unsigned_last_nbits ((Z.shiftl a 1)) (64))))
  ** ((( &( "b" ) )) # UInt64 |-> (b))
  ** ((( &( "r" ) )) # UInt64 |-> (r))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def mulmod_entail_wit_1 : Prop :=
  (
forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (PreH1 : (a_pre = a0)) (PreH2 : (b_pre = b0)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (1 <= modulus0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : ((0 : Int) <= a0)) (PreH7 : (a0 <= 18446744073709551615)) (PreH8 : ((0 : Int) <= b0)) (PreH9 : (b0 <= 18446744073709551615)) ,
  TT && emp 
|--
  “ (a0 = a_pre) ” &&
  “ (b0 = b_pre) ” &&
  “ (modulus0 = modulus_pre) ” &&
  “ (1 <= modulus_pre) ” &&
  “ (modulus_pre <= 100000000000000) ” &&
  “ ((0 : Int) <= a_pre) ” &&
  “ ((0 : Int) <= b_pre) ” &&
  “ ((0 : Int) <= (Z.rem a_pre modulus_pre)) ” &&
  “ ((Z.rem a_pre modulus_pre) < modulus_pre) ” &&
  “ ((0 : Int) <= (Z.rem b_pre modulus_pre)) ” &&
  “ ((Z.rem b_pre modulus_pre) < modulus_pre) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) < modulus_pre) ” &&
  “ (MulLoopState a_pre b_pre modulus_pre (Z.rem a_pre modulus_pre) (Z.rem b_pre modulus_pre) (0 : Int)) ”
  &&  emp
) \/
(
forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (PreH1 : (a_pre = a0)) (PreH2 : (b_pre = b0)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (1 <= modulus0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : ((0 : Int) <= a0)) (PreH7 : (a0 <= 18446744073709551615)) (PreH8 : ((0 : Int) <= b0)) (PreH9 : (b0 <= 18446744073709551615)) ,
  TT && emp 
|--
  “ (MulLoopState a_pre b_pre modulus_pre (Z.rem a_pre modulus_pre) (Z.rem b_pre modulus_pre) (0 : Int)) ” &&
  “ ((Z.rem b_pre modulus_pre) < modulus_pre) ” &&
  “ ((0 : Int) <= (Z.rem b_pre modulus_pre)) ” &&
  “ ((Z.rem a_pre modulus_pre) < modulus_pre) ” &&
  “ ((0 : Int) <= (Z.rem a_pre modulus_pre)) ”
  &&  emp
)

noncomputable def mulmod_entail_wit_1_split_goal_1 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (PreH1 : (a_pre = a0)) (PreH2 : (b_pre = b0)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (1 <= modulus0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : ((0 : Int) <= a0)) (PreH7 : (a0 <= 18446744073709551615)) (PreH8 : ((0 : Int) <= b0)) (PreH9 : (b0 <= 18446744073709551615)) ,
  (MulLoopState a_pre b_pre modulus_pre (Z.rem a_pre modulus_pre) (Z.rem b_pre modulus_pre) (0 : Int))

noncomputable def mulmod_entail_wit_1_split_goal_2 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (PreH1 : (a_pre = a0)) (PreH2 : (b_pre = b0)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (1 <= modulus0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : ((0 : Int) <= a0)) (PreH7 : (a0 <= 18446744073709551615)) (PreH8 : ((0 : Int) <= b0)) (PreH9 : (b0 <= 18446744073709551615)) ,
  ((Z.rem b_pre modulus_pre) < modulus_pre)

noncomputable def mulmod_entail_wit_1_split_goal_3 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (PreH1 : (a_pre = a0)) (PreH2 : (b_pre = b0)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (1 <= modulus0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : ((0 : Int) <= a0)) (PreH7 : (a0 <= 18446744073709551615)) (PreH8 : ((0 : Int) <= b0)) (PreH9 : (b0 <= 18446744073709551615)) ,
  ((0 : Int) <= (Z.rem b_pre modulus_pre))

noncomputable def mulmod_entail_wit_1_split_goal_4 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (PreH1 : (a_pre = a0)) (PreH2 : (b_pre = b0)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (1 <= modulus0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : ((0 : Int) <= a0)) (PreH7 : (a0 <= 18446744073709551615)) (PreH8 : ((0 : Int) <= b0)) (PreH9 : (b0 <= 18446744073709551615)) ,
  ((Z.rem a_pre modulus_pre) < modulus_pre)

noncomputable def mulmod_entail_wit_1_split_goal_5 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (PreH1 : (a_pre = a0)) (PreH2 : (b_pre = b0)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (1 <= modulus0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : ((0 : Int) <= a0)) (PreH7 : (a0 <= 18446744073709551615)) (PreH8 : ((0 : Int) <= b0)) (PreH9 : (b0 <= 18446744073709551615)) ,
  ((0 : Int) <= (Z.rem a_pre modulus_pre))

noncomputable def mulmod_entail_wit_2_1 : Prop :=
  (
forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : ((r + a) >= modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : ((0 : Int) <= a_pre)) (PreH9 : ((0 : Int) <= b_pre)) (PreH10 : ((0 : Int) <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : ((0 : Int) <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH17 : (b ≠ (0 : Int))) (PreH18 : ((Z.land b 1) ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (a0 = a_pre) ” &&
  “ (b0 = b_pre) ” &&
  “ (modulus0 = modulus_pre) ” &&
  “ (1 <= modulus_pre) ” &&
  “ (modulus_pre <= 100000000000000) ” &&
  “ ((0 : Int) <= a_pre) ” &&
  “ ((0 : Int) <= b_pre) ” &&
  “ ((0 : Int) <= ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus_pre)) ” &&
  “ (((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus_pre) < modulus_pre) ” &&
  “ ((0 : Int) <= (Z.shiftr b 1)) ” &&
  “ ((Z.shiftr b 1) < modulus_pre) ” &&
  “ ((0 : Int) <= ((r + a) - modulus_pre)) ” &&
  “ (((r + a) - modulus_pre) < modulus_pre) ” &&
  “ (MulLoopState a_pre b_pre modulus_pre ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus_pre) (Z.shiftr b 1) ((r + a) - modulus_pre)) ”
  &&  emp
) \/
(
forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : ((r + a) >= modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : ((0 : Int) <= a_pre)) (PreH9 : ((0 : Int) <= b_pre)) (PreH10 : ((0 : Int) <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : ((0 : Int) <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH17 : (b ≠ (0 : Int))) (PreH18 : ((Z.land b 1) ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (MulLoopState a_pre b_pre modulus_pre ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus_pre) (Z.shiftr b 1) ((r + a) - modulus_pre)) ” &&
  “ ((Z.shiftr b 1) < modulus_pre) ” &&
  “ ((0 : Int) <= (Z.shiftr b 1)) ” &&
  “ (((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus_pre) < modulus_pre) ”
  &&  emp
)

noncomputable def mulmod_entail_wit_2_1_split_goal_1 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : ((r + a) >= modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : ((0 : Int) <= a_pre)) (PreH9 : ((0 : Int) <= b_pre)) (PreH10 : ((0 : Int) <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : ((0 : Int) <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH17 : (b ≠ (0 : Int))) (PreH18 : ((Z.land b 1) ≠ (0 : Int))) ,
  (MulLoopState a_pre b_pre modulus_pre ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus_pre) (Z.shiftr b 1) ((r + a) - modulus_pre))

noncomputable def mulmod_entail_wit_2_1_split_goal_2 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : ((r + a) >= modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : ((0 : Int) <= a_pre)) (PreH9 : ((0 : Int) <= b_pre)) (PreH10 : ((0 : Int) <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : ((0 : Int) <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH17 : (b ≠ (0 : Int))) (PreH18 : ((Z.land b 1) ≠ (0 : Int))) ,
  ((Z.shiftr b 1) < modulus_pre)

noncomputable def mulmod_entail_wit_2_1_split_goal_3 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : ((r + a) >= modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : ((0 : Int) <= a_pre)) (PreH9 : ((0 : Int) <= b_pre)) (PreH10 : ((0 : Int) <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : ((0 : Int) <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH17 : (b ≠ (0 : Int))) (PreH18 : ((Z.land b 1) ≠ (0 : Int))) ,
  ((0 : Int) <= (Z.shiftr b 1))

noncomputable def mulmod_entail_wit_2_1_split_goal_4 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : ((r + a) >= modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : ((0 : Int) <= a_pre)) (PreH9 : ((0 : Int) <= b_pre)) (PreH10 : ((0 : Int) <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : ((0 : Int) <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH17 : (b ≠ (0 : Int))) (PreH18 : ((Z.land b 1) ≠ (0 : Int))) ,
  (((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus_pre) < modulus_pre)

noncomputable def mulmod_entail_wit_2_2 : Prop :=
  (
forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : ((r + a) < modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : ((0 : Int) <= a_pre)) (PreH9 : ((0 : Int) <= b_pre)) (PreH10 : ((0 : Int) <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : ((0 : Int) <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH17 : (b ≠ (0 : Int))) (PreH18 : ((Z.land b 1) ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (a0 = a_pre) ” &&
  “ (b0 = b_pre) ” &&
  “ (modulus0 = modulus_pre) ” &&
  “ (1 <= modulus_pre) ” &&
  “ (modulus_pre <= 100000000000000) ” &&
  “ ((0 : Int) <= a_pre) ” &&
  “ ((0 : Int) <= b_pre) ” &&
  “ ((0 : Int) <= ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus_pre)) ” &&
  “ (((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus_pre) < modulus_pre) ” &&
  “ ((0 : Int) <= (Z.shiftr b 1)) ” &&
  “ ((Z.shiftr b 1) < modulus_pre) ” &&
  “ ((0 : Int) <= (r + a)) ” &&
  “ ((r + a) < modulus_pre) ” &&
  “ (MulLoopState a_pre b_pre modulus_pre ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus_pre) (Z.shiftr b 1) (r + a)) ”
  &&  emp
) \/
(
forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : ((r + a) < modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : ((0 : Int) <= a_pre)) (PreH9 : ((0 : Int) <= b_pre)) (PreH10 : ((0 : Int) <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : ((0 : Int) <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH17 : (b ≠ (0 : Int))) (PreH18 : ((Z.land b 1) ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (MulLoopState a_pre b_pre modulus_pre ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus_pre) (Z.shiftr b 1) (r + a)) ” &&
  “ ((Z.shiftr b 1) < modulus_pre) ” &&
  “ ((0 : Int) <= (Z.shiftr b 1)) ” &&
  “ (((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus_pre) < modulus_pre) ”
  &&  emp
)

noncomputable def mulmod_entail_wit_2_2_split_goal_1 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : ((r + a) < modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : ((0 : Int) <= a_pre)) (PreH9 : ((0 : Int) <= b_pre)) (PreH10 : ((0 : Int) <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : ((0 : Int) <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH17 : (b ≠ (0 : Int))) (PreH18 : ((Z.land b 1) ≠ (0 : Int))) ,
  (MulLoopState a_pre b_pre modulus_pre ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus_pre) (Z.shiftr b 1) (r + a))

noncomputable def mulmod_entail_wit_2_2_split_goal_2 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : ((r + a) < modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : ((0 : Int) <= a_pre)) (PreH9 : ((0 : Int) <= b_pre)) (PreH10 : ((0 : Int) <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : ((0 : Int) <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH17 : (b ≠ (0 : Int))) (PreH18 : ((Z.land b 1) ≠ (0 : Int))) ,
  ((Z.shiftr b 1) < modulus_pre)

noncomputable def mulmod_entail_wit_2_2_split_goal_3 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : ((r + a) < modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : ((0 : Int) <= a_pre)) (PreH9 : ((0 : Int) <= b_pre)) (PreH10 : ((0 : Int) <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : ((0 : Int) <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH17 : (b ≠ (0 : Int))) (PreH18 : ((Z.land b 1) ≠ (0 : Int))) ,
  ((0 : Int) <= (Z.shiftr b 1))

noncomputable def mulmod_entail_wit_2_2_split_goal_4 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : ((r + a) < modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : ((0 : Int) <= a_pre)) (PreH9 : ((0 : Int) <= b_pre)) (PreH10 : ((0 : Int) <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : ((0 : Int) <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH17 : (b ≠ (0 : Int))) (PreH18 : ((Z.land b 1) ≠ (0 : Int))) ,
  (((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus_pre) < modulus_pre)

noncomputable def mulmod_entail_wit_2_3 : Prop :=
  (
forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : (a0 = a_pre)) (PreH3 : (b0 = b_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (1 <= modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : ((0 : Int) <= a_pre)) (PreH8 : ((0 : Int) <= b_pre)) (PreH9 : ((0 : Int) <= a)) (PreH10 : (a < modulus_pre)) (PreH11 : ((0 : Int) <= b)) (PreH12 : (b < modulus_pre)) (PreH13 : ((0 : Int) <= r)) (PreH14 : (r < modulus_pre)) (PreH15 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH16 : (b ≠ (0 : Int))) (PreH17 : ((Z.land b 1) = (0 : Int))) ,
  TT && emp 
|--
  “ (a0 = a_pre) ” &&
  “ (b0 = b_pre) ” &&
  “ (modulus0 = modulus_pre) ” &&
  “ (1 <= modulus_pre) ” &&
  “ (modulus_pre <= 100000000000000) ” &&
  “ ((0 : Int) <= a_pre) ” &&
  “ ((0 : Int) <= b_pre) ” &&
  “ ((0 : Int) <= ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus_pre)) ” &&
  “ (((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus_pre) < modulus_pre) ” &&
  “ ((0 : Int) <= (Z.shiftr b 1)) ” &&
  “ ((Z.shiftr b 1) < modulus_pre) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < modulus_pre) ” &&
  “ (MulLoopState a_pre b_pre modulus_pre ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus_pre) (Z.shiftr b 1) r) ”
  &&  emp
) \/
(
forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : (a0 = a_pre)) (PreH3 : (b0 = b_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (1 <= modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : ((0 : Int) <= a_pre)) (PreH8 : ((0 : Int) <= b_pre)) (PreH9 : ((0 : Int) <= a)) (PreH10 : (a < modulus_pre)) (PreH11 : ((0 : Int) <= b)) (PreH12 : (b < modulus_pre)) (PreH13 : ((0 : Int) <= r)) (PreH14 : (r < modulus_pre)) (PreH15 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH16 : (b ≠ (0 : Int))) (PreH17 : ((Z.land b 1) = (0 : Int))) ,
  TT && emp 
|--
  “ (MulLoopState a_pre b_pre modulus_pre ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus_pre) (Z.shiftr b 1) r) ” &&
  “ ((Z.shiftr b 1) < modulus_pre) ” &&
  “ ((0 : Int) <= (Z.shiftr b 1)) ” &&
  “ (((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus_pre) < modulus_pre) ”
  &&  emp
)

noncomputable def mulmod_entail_wit_2_3_split_goal_1 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : (a0 = a_pre)) (PreH3 : (b0 = b_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (1 <= modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : ((0 : Int) <= a_pre)) (PreH8 : ((0 : Int) <= b_pre)) (PreH9 : ((0 : Int) <= a)) (PreH10 : (a < modulus_pre)) (PreH11 : ((0 : Int) <= b)) (PreH12 : (b < modulus_pre)) (PreH13 : ((0 : Int) <= r)) (PreH14 : (r < modulus_pre)) (PreH15 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH16 : (b ≠ (0 : Int))) (PreH17 : ((Z.land b 1) = (0 : Int))) ,
  (MulLoopState a_pre b_pre modulus_pre ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus_pre) (Z.shiftr b 1) r)

noncomputable def mulmod_entail_wit_2_3_split_goal_2 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : (a0 = a_pre)) (PreH3 : (b0 = b_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (1 <= modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : ((0 : Int) <= a_pre)) (PreH8 : ((0 : Int) <= b_pre)) (PreH9 : ((0 : Int) <= a)) (PreH10 : (a < modulus_pre)) (PreH11 : ((0 : Int) <= b)) (PreH12 : (b < modulus_pre)) (PreH13 : ((0 : Int) <= r)) (PreH14 : (r < modulus_pre)) (PreH15 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH16 : (b ≠ (0 : Int))) (PreH17 : ((Z.land b 1) = (0 : Int))) ,
  ((Z.shiftr b 1) < modulus_pre)

noncomputable def mulmod_entail_wit_2_3_split_goal_3 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : (a0 = a_pre)) (PreH3 : (b0 = b_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (1 <= modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : ((0 : Int) <= a_pre)) (PreH8 : ((0 : Int) <= b_pre)) (PreH9 : ((0 : Int) <= a)) (PreH10 : (a < modulus_pre)) (PreH11 : ((0 : Int) <= b)) (PreH12 : (b < modulus_pre)) (PreH13 : ((0 : Int) <= r)) (PreH14 : (r < modulus_pre)) (PreH15 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH16 : (b ≠ (0 : Int))) (PreH17 : ((Z.land b 1) = (0 : Int))) ,
  ((0 : Int) <= (Z.shiftr b 1))

noncomputable def mulmod_entail_wit_2_3_split_goal_4 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) >= modulus_pre)) (PreH2 : (a0 = a_pre)) (PreH3 : (b0 = b_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (1 <= modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : ((0 : Int) <= a_pre)) (PreH8 : ((0 : Int) <= b_pre)) (PreH9 : ((0 : Int) <= a)) (PreH10 : (a < modulus_pre)) (PreH11 : ((0 : Int) <= b)) (PreH12 : (b < modulus_pre)) (PreH13 : ((0 : Int) <= r)) (PreH14 : (r < modulus_pre)) (PreH15 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH16 : (b ≠ (0 : Int))) (PreH17 : ((Z.land b 1) = (0 : Int))) ,
  (((unsigned_last_nbits ((Z.shiftl a 1)) (64)) - modulus_pre) < modulus_pre)

noncomputable def mulmod_entail_wit_2_4 : Prop :=
  (
forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : ((r + a) >= modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : ((0 : Int) <= a_pre)) (PreH9 : ((0 : Int) <= b_pre)) (PreH10 : ((0 : Int) <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : ((0 : Int) <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH17 : (b ≠ (0 : Int))) (PreH18 : ((Z.land b 1) ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (a0 = a_pre) ” &&
  “ (b0 = b_pre) ” &&
  “ (modulus0 = modulus_pre) ” &&
  “ (1 <= modulus_pre) ” &&
  “ (modulus_pre <= 100000000000000) ” &&
  “ ((0 : Int) <= a_pre) ” &&
  “ ((0 : Int) <= b_pre) ” &&
  “ ((0 : Int) <= (unsigned_last_nbits ((Z.shiftl a 1)) (64))) ” &&
  “ ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre) ” &&
  “ ((0 : Int) <= (Z.shiftr b 1)) ” &&
  “ ((Z.shiftr b 1) < modulus_pre) ” &&
  “ ((0 : Int) <= ((r + a) - modulus_pre)) ” &&
  “ (((r + a) - modulus_pre) < modulus_pre) ” &&
  “ (MulLoopState a_pre b_pre modulus_pre (unsigned_last_nbits ((Z.shiftl a 1)) (64)) (Z.shiftr b 1) ((r + a) - modulus_pre)) ”
  &&  emp
) \/
(
forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : ((r + a) >= modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : ((0 : Int) <= a_pre)) (PreH9 : ((0 : Int) <= b_pre)) (PreH10 : ((0 : Int) <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : ((0 : Int) <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH17 : (b ≠ (0 : Int))) (PreH18 : ((Z.land b 1) ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (MulLoopState a_pre b_pre modulus_pre (unsigned_last_nbits ((Z.shiftl a 1)) (64)) (Z.shiftr b 1) ((r + a) - modulus_pre)) ” &&
  “ ((Z.shiftr b 1) < modulus_pre) ” &&
  “ ((0 : Int) <= (Z.shiftr b 1)) ” &&
  “ ((0 : Int) <= (unsigned_last_nbits ((Z.shiftl a 1)) (64))) ”
  &&  emp
)

noncomputable def mulmod_entail_wit_2_4_split_goal_1 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : ((r + a) >= modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : ((0 : Int) <= a_pre)) (PreH9 : ((0 : Int) <= b_pre)) (PreH10 : ((0 : Int) <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : ((0 : Int) <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH17 : (b ≠ (0 : Int))) (PreH18 : ((Z.land b 1) ≠ (0 : Int))) ,
  (MulLoopState a_pre b_pre modulus_pre (unsigned_last_nbits ((Z.shiftl a 1)) (64)) (Z.shiftr b 1) ((r + a) - modulus_pre))

noncomputable def mulmod_entail_wit_2_4_split_goal_2 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : ((r + a) >= modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : ((0 : Int) <= a_pre)) (PreH9 : ((0 : Int) <= b_pre)) (PreH10 : ((0 : Int) <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : ((0 : Int) <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH17 : (b ≠ (0 : Int))) (PreH18 : ((Z.land b 1) ≠ (0 : Int))) ,
  ((Z.shiftr b 1) < modulus_pre)

noncomputable def mulmod_entail_wit_2_4_split_goal_3 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : ((r + a) >= modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : ((0 : Int) <= a_pre)) (PreH9 : ((0 : Int) <= b_pre)) (PreH10 : ((0 : Int) <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : ((0 : Int) <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH17 : (b ≠ (0 : Int))) (PreH18 : ((Z.land b 1) ≠ (0 : Int))) ,
  ((0 : Int) <= (Z.shiftr b 1))

noncomputable def mulmod_entail_wit_2_4_split_goal_4 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : ((r + a) >= modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : ((0 : Int) <= a_pre)) (PreH9 : ((0 : Int) <= b_pre)) (PreH10 : ((0 : Int) <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : ((0 : Int) <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH17 : (b ≠ (0 : Int))) (PreH18 : ((Z.land b 1) ≠ (0 : Int))) ,
  ((0 : Int) <= (unsigned_last_nbits ((Z.shiftl a 1)) (64)))

noncomputable def mulmod_entail_wit_2_5 : Prop :=
  (
forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : ((r + a) < modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : ((0 : Int) <= a_pre)) (PreH9 : ((0 : Int) <= b_pre)) (PreH10 : ((0 : Int) <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : ((0 : Int) <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH17 : (b ≠ (0 : Int))) (PreH18 : ((Z.land b 1) ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (a0 = a_pre) ” &&
  “ (b0 = b_pre) ” &&
  “ (modulus0 = modulus_pre) ” &&
  “ (1 <= modulus_pre) ” &&
  “ (modulus_pre <= 100000000000000) ” &&
  “ ((0 : Int) <= a_pre) ” &&
  “ ((0 : Int) <= b_pre) ” &&
  “ ((0 : Int) <= (unsigned_last_nbits ((Z.shiftl a 1)) (64))) ” &&
  “ ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre) ” &&
  “ ((0 : Int) <= (Z.shiftr b 1)) ” &&
  “ ((Z.shiftr b 1) < modulus_pre) ” &&
  “ ((0 : Int) <= (r + a)) ” &&
  “ ((r + a) < modulus_pre) ” &&
  “ (MulLoopState a_pre b_pre modulus_pre (unsigned_last_nbits ((Z.shiftl a 1)) (64)) (Z.shiftr b 1) (r + a)) ”
  &&  emp
) \/
(
forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : ((r + a) < modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : ((0 : Int) <= a_pre)) (PreH9 : ((0 : Int) <= b_pre)) (PreH10 : ((0 : Int) <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : ((0 : Int) <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH17 : (b ≠ (0 : Int))) (PreH18 : ((Z.land b 1) ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (MulLoopState a_pre b_pre modulus_pre (unsigned_last_nbits ((Z.shiftl a 1)) (64)) (Z.shiftr b 1) (r + a)) ” &&
  “ ((Z.shiftr b 1) < modulus_pre) ” &&
  “ ((0 : Int) <= (Z.shiftr b 1)) ” &&
  “ ((0 : Int) <= (unsigned_last_nbits ((Z.shiftl a 1)) (64))) ”
  &&  emp
)

noncomputable def mulmod_entail_wit_2_5_split_goal_1 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : ((r + a) < modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : ((0 : Int) <= a_pre)) (PreH9 : ((0 : Int) <= b_pre)) (PreH10 : ((0 : Int) <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : ((0 : Int) <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH17 : (b ≠ (0 : Int))) (PreH18 : ((Z.land b 1) ≠ (0 : Int))) ,
  (MulLoopState a_pre b_pre modulus_pre (unsigned_last_nbits ((Z.shiftl a 1)) (64)) (Z.shiftr b 1) (r + a))

noncomputable def mulmod_entail_wit_2_5_split_goal_2 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : ((r + a) < modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : ((0 : Int) <= a_pre)) (PreH9 : ((0 : Int) <= b_pre)) (PreH10 : ((0 : Int) <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : ((0 : Int) <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH17 : (b ≠ (0 : Int))) (PreH18 : ((Z.land b 1) ≠ (0 : Int))) ,
  ((Z.shiftr b 1) < modulus_pre)

noncomputable def mulmod_entail_wit_2_5_split_goal_3 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : ((r + a) < modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : ((0 : Int) <= a_pre)) (PreH9 : ((0 : Int) <= b_pre)) (PreH10 : ((0 : Int) <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : ((0 : Int) <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH17 : (b ≠ (0 : Int))) (PreH18 : ((Z.land b 1) ≠ (0 : Int))) ,
  ((0 : Int) <= (Z.shiftr b 1))

noncomputable def mulmod_entail_wit_2_5_split_goal_4 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : ((r + a) < modulus_pre)) (PreH3 : (a0 = a_pre)) (PreH4 : (b0 = b_pre)) (PreH5 : (modulus0 = modulus_pre)) (PreH6 : (1 <= modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : ((0 : Int) <= a_pre)) (PreH9 : ((0 : Int) <= b_pre)) (PreH10 : ((0 : Int) <= a)) (PreH11 : (a < modulus_pre)) (PreH12 : ((0 : Int) <= b)) (PreH13 : (b < modulus_pre)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH17 : (b ≠ (0 : Int))) (PreH18 : ((Z.land b 1) ≠ (0 : Int))) ,
  ((0 : Int) <= (unsigned_last_nbits ((Z.shiftl a 1)) (64)))

noncomputable def mulmod_entail_wit_2_6 : Prop :=
  (
forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : (a0 = a_pre)) (PreH3 : (b0 = b_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (1 <= modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : ((0 : Int) <= a_pre)) (PreH8 : ((0 : Int) <= b_pre)) (PreH9 : ((0 : Int) <= a)) (PreH10 : (a < modulus_pre)) (PreH11 : ((0 : Int) <= b)) (PreH12 : (b < modulus_pre)) (PreH13 : ((0 : Int) <= r)) (PreH14 : (r < modulus_pre)) (PreH15 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH16 : (b ≠ (0 : Int))) (PreH17 : ((Z.land b 1) = (0 : Int))) ,
  TT && emp 
|--
  “ (a0 = a_pre) ” &&
  “ (b0 = b_pre) ” &&
  “ (modulus0 = modulus_pre) ” &&
  “ (1 <= modulus_pre) ” &&
  “ (modulus_pre <= 100000000000000) ” &&
  “ ((0 : Int) <= a_pre) ” &&
  “ ((0 : Int) <= b_pre) ” &&
  “ ((0 : Int) <= (unsigned_last_nbits ((Z.shiftl a 1)) (64))) ” &&
  “ ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre) ” &&
  “ ((0 : Int) <= (Z.shiftr b 1)) ” &&
  “ ((Z.shiftr b 1) < modulus_pre) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < modulus_pre) ” &&
  “ (MulLoopState a_pre b_pre modulus_pre (unsigned_last_nbits ((Z.shiftl a 1)) (64)) (Z.shiftr b 1) r) ”
  &&  emp
) \/
(
forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : (a0 = a_pre)) (PreH3 : (b0 = b_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (1 <= modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : ((0 : Int) <= a_pre)) (PreH8 : ((0 : Int) <= b_pre)) (PreH9 : ((0 : Int) <= a)) (PreH10 : (a < modulus_pre)) (PreH11 : ((0 : Int) <= b)) (PreH12 : (b < modulus_pre)) (PreH13 : ((0 : Int) <= r)) (PreH14 : (r < modulus_pre)) (PreH15 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH16 : (b ≠ (0 : Int))) (PreH17 : ((Z.land b 1) = (0 : Int))) ,
  TT && emp 
|--
  “ (MulLoopState a_pre b_pre modulus_pre (unsigned_last_nbits ((Z.shiftl a 1)) (64)) (Z.shiftr b 1) r) ” &&
  “ ((Z.shiftr b 1) < modulus_pre) ” &&
  “ ((0 : Int) <= (Z.shiftr b 1)) ” &&
  “ ((0 : Int) <= (unsigned_last_nbits ((Z.shiftl a 1)) (64))) ”
  &&  emp
)

noncomputable def mulmod_entail_wit_2_6_split_goal_1 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : (a0 = a_pre)) (PreH3 : (b0 = b_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (1 <= modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : ((0 : Int) <= a_pre)) (PreH8 : ((0 : Int) <= b_pre)) (PreH9 : ((0 : Int) <= a)) (PreH10 : (a < modulus_pre)) (PreH11 : ((0 : Int) <= b)) (PreH12 : (b < modulus_pre)) (PreH13 : ((0 : Int) <= r)) (PreH14 : (r < modulus_pre)) (PreH15 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH16 : (b ≠ (0 : Int))) (PreH17 : ((Z.land b 1) = (0 : Int))) ,
  (MulLoopState a_pre b_pre modulus_pre (unsigned_last_nbits ((Z.shiftl a 1)) (64)) (Z.shiftr b 1) r)

noncomputable def mulmod_entail_wit_2_6_split_goal_2 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : (a0 = a_pre)) (PreH3 : (b0 = b_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (1 <= modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : ((0 : Int) <= a_pre)) (PreH8 : ((0 : Int) <= b_pre)) (PreH9 : ((0 : Int) <= a)) (PreH10 : (a < modulus_pre)) (PreH11 : ((0 : Int) <= b)) (PreH12 : (b < modulus_pre)) (PreH13 : ((0 : Int) <= r)) (PreH14 : (r < modulus_pre)) (PreH15 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH16 : (b ≠ (0 : Int))) (PreH17 : ((Z.land b 1) = (0 : Int))) ,
  ((Z.shiftr b 1) < modulus_pre)

noncomputable def mulmod_entail_wit_2_6_split_goal_3 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : (a0 = a_pre)) (PreH3 : (b0 = b_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (1 <= modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : ((0 : Int) <= a_pre)) (PreH8 : ((0 : Int) <= b_pre)) (PreH9 : ((0 : Int) <= a)) (PreH10 : (a < modulus_pre)) (PreH11 : ((0 : Int) <= b)) (PreH12 : (b < modulus_pre)) (PreH13 : ((0 : Int) <= r)) (PreH14 : (r < modulus_pre)) (PreH15 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH16 : (b ≠ (0 : Int))) (PreH17 : ((Z.land b 1) = (0 : Int))) ,
  ((0 : Int) <= (Z.shiftr b 1))

noncomputable def mulmod_entail_wit_2_6_split_goal_4 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : ((unsigned_last_nbits ((Z.shiftl a 1)) (64)) < modulus_pre)) (PreH2 : (a0 = a_pre)) (PreH3 : (b0 = b_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (1 <= modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : ((0 : Int) <= a_pre)) (PreH8 : ((0 : Int) <= b_pre)) (PreH9 : ((0 : Int) <= a)) (PreH10 : (a < modulus_pre)) (PreH11 : ((0 : Int) <= b)) (PreH12 : (b < modulus_pre)) (PreH13 : ((0 : Int) <= r)) (PreH14 : (r < modulus_pre)) (PreH15 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH16 : (b ≠ (0 : Int))) (PreH17 : ((Z.land b 1) = (0 : Int))) ,
  ((0 : Int) <= (unsigned_last_nbits ((Z.shiftl a 1)) (64)))

noncomputable def mulmod_return_wit_1 : Prop :=
  (
forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : (a0 = a_pre)) (PreH2 : (b0 = b_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (1 <= modulus_pre)) (PreH5 : (modulus_pre <= 100000000000000)) (PreH6 : ((0 : Int) <= a_pre)) (PreH7 : ((0 : Int) <= b_pre)) (PreH8 : ((0 : Int) <= a)) (PreH9 : (a < modulus_pre)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b < modulus_pre)) (PreH12 : ((0 : Int) <= r)) (PreH13 : (r < modulus_pre)) (PreH14 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH15 : (b = (0 : Int))) ,
  TT && emp 
|--
  “ (r = (Z.rem (a0 * b0) modulus0)) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < modulus0) ”
  &&  emp
) \/
(
forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : (a0 = a_pre)) (PreH2 : (b0 = b_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (1 <= modulus_pre)) (PreH5 : (modulus_pre <= 100000000000000)) (PreH6 : ((0 : Int) <= a_pre)) (PreH7 : ((0 : Int) <= b_pre)) (PreH8 : ((0 : Int) <= a)) (PreH9 : (a < modulus_pre)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b < modulus_pre)) (PreH12 : ((0 : Int) <= r)) (PreH13 : (r < modulus_pre)) (PreH14 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH15 : (b = (0 : Int))) ,
  TT && emp 
|--
  “ (r = (Z.rem (a_pre * b_pre) modulus_pre)) ”
  &&  emp
)

noncomputable def mulmod_return_wit_1_split_goal_1 : Prop :=
  forall (modulus_pre : Int) (b_pre : Int) (a_pre : Int) (modulus0 : Int) (b0 : Int) (a0 : Int) (r : Int) (b : Int) (a : Int) (PreH1 : (a0 = a_pre)) (PreH2 : (b0 = b_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (1 <= modulus_pre)) (PreH5 : (modulus_pre <= 100000000000000)) (PreH6 : ((0 : Int) <= a_pre)) (PreH7 : ((0 : Int) <= b_pre)) (PreH8 : ((0 : Int) <= a)) (PreH9 : (a < modulus_pre)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b < modulus_pre)) (PreH12 : ((0 : Int) <= r)) (PreH13 : (r < modulus_pre)) (PreH14 : (MulLoopState a_pre b_pre modulus_pre a b r)) (PreH15 : (b = (0 : Int))) ,
  (r = (Z.rem (a_pre * b_pre) modulus_pre))

noncomputable def powmod_safety_wit_1 : Prop :=
  forall (modulus_pre : Int) (e_pre : Int) (b_pre : Int) (modulus0 : Int) (exponent : Int) (base : Int) (PreH1 : (b_pre = base)) (PreH2 : (e_pre = exponent)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (1 <= modulus0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : ((0 : Int) <= base)) (PreH7 : (base <= 18446744073709551615)) (PreH8 : ((0 : Int) <= exponent)) (PreH9 : (exponent <= 100000000000000)) ,
  ((( &( "r" ) )) # UInt64 |->_)
  ** ((( &( "b" ) )) # UInt64 |-> (b_pre))
  ** ((( &( "e" ) )) # UInt64 |-> (e_pre))
  ** ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
|--
  “ (modulus_pre ≠ (0 : Int)) ”

noncomputable def powmod_safety_wit_2 : Prop :=
  forall (modulus_pre : Int) (e_pre : Int) (b_pre : Int) (modulus0 : Int) (exponent : Int) (base : Int) (PreH1 : (b_pre = base)) (PreH2 : (e_pre = exponent)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (1 <= modulus0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : ((0 : Int) <= base)) (PreH7 : (base <= 18446744073709551615)) (PreH8 : ((0 : Int) <= exponent)) (PreH9 : (exponent <= 100000000000000)) ,
  ((( &( "r" ) )) # UInt64 |->_)
  ** ((( &( "b" ) )) # UInt64 |-> (b_pre))
  ** ((( &( "e" ) )) # UInt64 |-> (e_pre))
  ** ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def powmod_safety_wit_3 : Prop :=
  forall (modulus_pre : Int) (e_pre : Int) (b_pre : Int) (modulus0 : Int) (exponent : Int) (base : Int) (PreH1 : (b_pre = base)) (PreH2 : (e_pre = exponent)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (1 <= modulus0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : ((0 : Int) <= base)) (PreH7 : (base <= 18446744073709551615)) (PreH8 : ((0 : Int) <= exponent)) (PreH9 : (exponent <= 100000000000000)) ,
  ((( &( "r" ) )) # UInt64 |-> ((Z.rem 1 modulus_pre)))
  ** ((( &( "b" ) )) # UInt64 |-> (b_pre))
  ** ((( &( "e" ) )) # UInt64 |-> (e_pre))
  ** ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
|--
  “ (modulus_pre ≠ (0 : Int)) ”

noncomputable def powmod_safety_wit_4 : Prop :=
  forall (modulus_pre : Int) (e_pre : Int) (b_pre : Int) (modulus0 : Int) (exponent : Int) (base : Int) (r : Int) (e : Int) (b : Int) (PreH1 : (base = b_pre)) (PreH2 : (exponent = e_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (1 <= modulus_pre)) (PreH5 : (modulus_pre <= 100000000000000)) (PreH6 : ((0 : Int) <= base)) (PreH7 : ((0 : Int) <= b)) (PreH8 : (b < modulus_pre)) (PreH9 : ((0 : Int) <= e)) (PreH10 : (e <= exponent)) (PreH11 : ((0 : Int) <= r)) (PreH12 : (r < modulus_pre)) (PreH13 : (PowLoopState base exponent modulus_pre b e r)) (PreH14 : (e ≠ (0 : Int))) ,
  ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "b" ) )) # UInt64 |-> (b))
  ** ((( &( "e" ) )) # UInt64 |-> (e))
  ** ((( &( "r" ) )) # UInt64 |-> (r))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def powmod_safety_wit_5 : Prop :=
  forall (modulus_pre : Int) (e_pre : Int) (b_pre : Int) (modulus0 : Int) (exponent : Int) (base : Int) (r : Int) (e : Int) (b : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (Z.rem (b * b) modulus_pre))) (PreH2 : ((0 : Int) <= retval_2)) (PreH3 : (retval_2 < modulus_pre)) (PreH4 : (retval = (Z.rem (r * b) modulus_pre))) (PreH5 : ((0 : Int) <= retval)) (PreH6 : (retval < modulus_pre)) (PreH7 : (base = b_pre)) (PreH8 : (exponent = e_pre)) (PreH9 : (modulus0 = modulus_pre)) (PreH10 : (1 <= modulus_pre)) (PreH11 : (modulus_pre <= 100000000000000)) (PreH12 : ((0 : Int) <= base)) (PreH13 : ((0 : Int) <= b)) (PreH14 : (b < modulus_pre)) (PreH15 : ((0 : Int) <= e)) (PreH16 : (e <= exponent)) (PreH17 : ((0 : Int) <= r)) (PreH18 : (r < modulus_pre)) (PreH19 : (PowLoopState base exponent modulus_pre b e r)) (PreH20 : (e ≠ (0 : Int))) (PreH21 : ((Z.land e 1) ≠ (0 : Int))) ,
  ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "b" ) )) # UInt64 |-> (retval_2))
  ** ((( &( "e" ) )) # UInt64 |-> (e))
  ** ((( &( "r" ) )) # UInt64 |-> (retval))
|--
  “ (1 <= 63) ” &&
  “ ((0 : Int) <= 1) ”

noncomputable def powmod_safety_wit_6 : Prop :=
  forall (modulus_pre : Int) (e_pre : Int) (b_pre : Int) (modulus0 : Int) (exponent : Int) (base : Int) (r : Int) (e : Int) (b : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (Z.rem (b * b) modulus_pre))) (PreH2 : ((0 : Int) <= retval_2)) (PreH3 : (retval_2 < modulus_pre)) (PreH4 : (retval = (Z.rem (r * b) modulus_pre))) (PreH5 : ((0 : Int) <= retval)) (PreH6 : (retval < modulus_pre)) (PreH7 : (base = b_pre)) (PreH8 : (exponent = e_pre)) (PreH9 : (modulus0 = modulus_pre)) (PreH10 : (1 <= modulus_pre)) (PreH11 : (modulus_pre <= 100000000000000)) (PreH12 : ((0 : Int) <= base)) (PreH13 : ((0 : Int) <= b)) (PreH14 : (b < modulus_pre)) (PreH15 : ((0 : Int) <= e)) (PreH16 : (e <= exponent)) (PreH17 : ((0 : Int) <= r)) (PreH18 : (r < modulus_pre)) (PreH19 : (PowLoopState base exponent modulus_pre b e r)) (PreH20 : (e ≠ (0 : Int))) (PreH21 : ((Z.land e 1) ≠ (0 : Int))) ,
  ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "b" ) )) # UInt64 |-> (retval_2))
  ** ((( &( "e" ) )) # UInt64 |-> (e))
  ** ((( &( "r" ) )) # UInt64 |-> (retval))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def powmod_safety_wit_7 : Prop :=
  forall (modulus_pre : Int) (e_pre : Int) (b_pre : Int) (modulus0 : Int) (exponent : Int) (base : Int) (r : Int) (e : Int) (b : Int) (retval : Int) (PreH1 : (retval = (Z.rem (b * b) modulus_pre))) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval < modulus_pre)) (PreH4 : (base = b_pre)) (PreH5 : (exponent = e_pre)) (PreH6 : (modulus0 = modulus_pre)) (PreH7 : (1 <= modulus_pre)) (PreH8 : (modulus_pre <= 100000000000000)) (PreH9 : ((0 : Int) <= base)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b < modulus_pre)) (PreH12 : ((0 : Int) <= e)) (PreH13 : (e <= exponent)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (PowLoopState base exponent modulus_pre b e r)) (PreH17 : (e ≠ (0 : Int))) (PreH18 : ((Z.land e 1) = (0 : Int))) ,
  ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "b" ) )) # UInt64 |-> (retval))
  ** ((( &( "e" ) )) # UInt64 |-> (e))
  ** ((( &( "r" ) )) # UInt64 |-> (r))
|--
  “ (1 <= 63) ” &&
  “ ((0 : Int) <= 1) ”

noncomputable def powmod_safety_wit_8 : Prop :=
  forall (modulus_pre : Int) (e_pre : Int) (b_pre : Int) (modulus0 : Int) (exponent : Int) (base : Int) (r : Int) (e : Int) (b : Int) (retval : Int) (PreH1 : (retval = (Z.rem (b * b) modulus_pre))) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval < modulus_pre)) (PreH4 : (base = b_pre)) (PreH5 : (exponent = e_pre)) (PreH6 : (modulus0 = modulus_pre)) (PreH7 : (1 <= modulus_pre)) (PreH8 : (modulus_pre <= 100000000000000)) (PreH9 : ((0 : Int) <= base)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b < modulus_pre)) (PreH12 : ((0 : Int) <= e)) (PreH13 : (e <= exponent)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (PowLoopState base exponent modulus_pre b e r)) (PreH17 : (e ≠ (0 : Int))) (PreH18 : ((Z.land e 1) = (0 : Int))) ,
  ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "b" ) )) # UInt64 |-> (retval))
  ** ((( &( "e" ) )) # UInt64 |-> (e))
  ** ((( &( "r" ) )) # UInt64 |-> (r))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def powmod_entail_wit_1 : Prop :=
  (
forall (modulus_pre : Int) (e_pre : Int) (b_pre : Int) (modulus0 : Int) (exponent : Int) (base : Int) (PreH1 : (b_pre = base)) (PreH2 : (e_pre = exponent)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (1 <= modulus0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : ((0 : Int) <= base)) (PreH7 : (base <= 18446744073709551615)) (PreH8 : ((0 : Int) <= exponent)) (PreH9 : (exponent <= 100000000000000)) ,
  TT && emp 
|--
  “ (base = b_pre) ” &&
  “ (exponent = e_pre) ” &&
  “ (modulus0 = modulus_pre) ” &&
  “ (1 <= modulus_pre) ” &&
  “ (modulus_pre <= 100000000000000) ” &&
  “ ((0 : Int) <= base) ” &&
  “ ((0 : Int) <= (Z.rem b_pre modulus_pre)) ” &&
  “ ((Z.rem b_pre modulus_pre) < modulus_pre) ” &&
  “ ((0 : Int) <= e_pre) ” &&
  “ (e_pre <= exponent) ” &&
  “ ((0 : Int) <= (Z.rem 1 modulus_pre)) ” &&
  “ ((Z.rem 1 modulus_pre) < modulus_pre) ” &&
  “ (PowLoopState base exponent modulus_pre (Z.rem b_pre modulus_pre) e_pre (Z.rem 1 modulus_pre)) ”
  &&  emp
) \/
(
forall (modulus_pre : Int) (e_pre : Int) (b_pre : Int) (modulus0 : Int) (exponent : Int) (base : Int) (PreH1 : (b_pre = base)) (PreH2 : (e_pre = exponent)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (1 <= modulus0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : ((0 : Int) <= base)) (PreH7 : (base <= 18446744073709551615)) (PreH8 : ((0 : Int) <= exponent)) (PreH9 : (exponent <= 100000000000000)) ,
  TT && emp 
|--
  “ (PowLoopState b_pre e_pre modulus_pre (Z.rem b_pre modulus_pre) e_pre (Z.rem 1 modulus_pre)) ” &&
  “ ((Z.rem 1 modulus_pre) < modulus_pre) ” &&
  “ ((0 : Int) <= (Z.rem 1 modulus_pre)) ” &&
  “ ((Z.rem b_pre modulus_pre) < modulus_pre) ” &&
  “ ((0 : Int) <= (Z.rem b_pre modulus_pre)) ”
  &&  emp
)

noncomputable def powmod_entail_wit_1_split_goal_1 : Prop :=
  forall (modulus_pre : Int) (e_pre : Int) (b_pre : Int) (modulus0 : Int) (exponent : Int) (base : Int) (PreH1 : (b_pre = base)) (PreH2 : (e_pre = exponent)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (1 <= modulus0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : ((0 : Int) <= base)) (PreH7 : (base <= 18446744073709551615)) (PreH8 : ((0 : Int) <= exponent)) (PreH9 : (exponent <= 100000000000000)) ,
  (PowLoopState b_pre e_pre modulus_pre (Z.rem b_pre modulus_pre) e_pre (Z.rem 1 modulus_pre))

noncomputable def powmod_entail_wit_1_split_goal_2 : Prop :=
  forall (modulus_pre : Int) (e_pre : Int) (b_pre : Int) (modulus0 : Int) (exponent : Int) (base : Int) (PreH1 : (b_pre = base)) (PreH2 : (e_pre = exponent)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (1 <= modulus0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : ((0 : Int) <= base)) (PreH7 : (base <= 18446744073709551615)) (PreH8 : ((0 : Int) <= exponent)) (PreH9 : (exponent <= 100000000000000)) ,
  ((Z.rem 1 modulus_pre) < modulus_pre)

noncomputable def powmod_entail_wit_1_split_goal_3 : Prop :=
  forall (modulus_pre : Int) (e_pre : Int) (b_pre : Int) (modulus0 : Int) (exponent : Int) (base : Int) (PreH1 : (b_pre = base)) (PreH2 : (e_pre = exponent)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (1 <= modulus0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : ((0 : Int) <= base)) (PreH7 : (base <= 18446744073709551615)) (PreH8 : ((0 : Int) <= exponent)) (PreH9 : (exponent <= 100000000000000)) ,
  ((0 : Int) <= (Z.rem 1 modulus_pre))

noncomputable def powmod_entail_wit_1_split_goal_4 : Prop :=
  forall (modulus_pre : Int) (e_pre : Int) (b_pre : Int) (modulus0 : Int) (exponent : Int) (base : Int) (PreH1 : (b_pre = base)) (PreH2 : (e_pre = exponent)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (1 <= modulus0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : ((0 : Int) <= base)) (PreH7 : (base <= 18446744073709551615)) (PreH8 : ((0 : Int) <= exponent)) (PreH9 : (exponent <= 100000000000000)) ,
  ((Z.rem b_pre modulus_pre) < modulus_pre)

noncomputable def powmod_entail_wit_1_split_goal_5 : Prop :=
  forall (modulus_pre : Int) (e_pre : Int) (b_pre : Int) (modulus0 : Int) (exponent : Int) (base : Int) (PreH1 : (b_pre = base)) (PreH2 : (e_pre = exponent)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (1 <= modulus0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : ((0 : Int) <= base)) (PreH7 : (base <= 18446744073709551615)) (PreH8 : ((0 : Int) <= exponent)) (PreH9 : (exponent <= 100000000000000)) ,
  ((0 : Int) <= (Z.rem b_pre modulus_pre))

noncomputable def powmod_entail_wit_2_1 : Prop :=
  (
forall (modulus_pre : Int) (e_pre : Int) (b_pre : Int) (modulus0 : Int) (exponent : Int) (base : Int) (r : Int) (e : Int) (b : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (Z.rem (b * b) modulus_pre))) (PreH2 : ((0 : Int) <= retval_2)) (PreH3 : (retval_2 < modulus_pre)) (PreH4 : (retval = (Z.rem (r * b) modulus_pre))) (PreH5 : ((0 : Int) <= retval)) (PreH6 : (retval < modulus_pre)) (PreH7 : (base = b_pre)) (PreH8 : (exponent = e_pre)) (PreH9 : (modulus0 = modulus_pre)) (PreH10 : (1 <= modulus_pre)) (PreH11 : (modulus_pre <= 100000000000000)) (PreH12 : ((0 : Int) <= base)) (PreH13 : ((0 : Int) <= b)) (PreH14 : (b < modulus_pre)) (PreH15 : ((0 : Int) <= e)) (PreH16 : (e <= exponent)) (PreH17 : ((0 : Int) <= r)) (PreH18 : (r < modulus_pre)) (PreH19 : (PowLoopState base exponent modulus_pre b e r)) (PreH20 : (e ≠ (0 : Int))) (PreH21 : ((Z.land e 1) ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (base = b_pre) ” &&
  “ (exponent = e_pre) ” &&
  “ (modulus0 = modulus_pre) ” &&
  “ (1 <= modulus_pre) ” &&
  “ (modulus_pre <= 100000000000000) ” &&
  “ ((0 : Int) <= base) ” &&
  “ ((0 : Int) <= retval_2) ” &&
  “ (retval_2 < modulus_pre) ” &&
  “ ((0 : Int) <= (Z.shiftr e 1)) ” &&
  “ ((Z.shiftr e 1) <= exponent) ” &&
  “ ((0 : Int) <= retval) ” &&
  “ (retval < modulus_pre) ” &&
  “ (PowLoopState base exponent modulus_pre retval_2 (Z.shiftr e 1) retval) ”
  &&  emp
) \/
(
forall (modulus_pre : Int) (e_pre : Int) (b_pre : Int) (modulus0 : Int) (exponent : Int) (base : Int) (r : Int) (e : Int) (b : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (Z.rem (b * b) modulus_pre))) (PreH2 : ((0 : Int) <= retval_2)) (PreH3 : (retval_2 < modulus_pre)) (PreH4 : (retval = (Z.rem (r * b) modulus_pre))) (PreH5 : ((0 : Int) <= retval)) (PreH6 : (retval < modulus_pre)) (PreH7 : (base = b_pre)) (PreH8 : (exponent = e_pre)) (PreH9 : (modulus0 = modulus_pre)) (PreH10 : (1 <= modulus_pre)) (PreH11 : (modulus_pre <= 100000000000000)) (PreH12 : ((0 : Int) <= base)) (PreH13 : ((0 : Int) <= b)) (PreH14 : (b < modulus_pre)) (PreH15 : ((0 : Int) <= e)) (PreH16 : (e <= exponent)) (PreH17 : ((0 : Int) <= r)) (PreH18 : (r < modulus_pre)) (PreH19 : (PowLoopState base exponent modulus_pre b e r)) (PreH20 : (e ≠ (0 : Int))) (PreH21 : ((Z.land e 1) ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (PowLoopState b_pre e_pre modulus_pre (Z.rem (b * b) modulus_pre) (Z.shiftr e 1) (Z.rem (r * b) modulus_pre)) ” &&
  “ ((Z.shiftr e 1) <= e_pre) ” &&
  “ ((0 : Int) <= (Z.shiftr e 1)) ”
  &&  emp
)

noncomputable def powmod_entail_wit_2_1_split_goal_1 : Prop :=
  forall (modulus_pre : Int) (e_pre : Int) (b_pre : Int) (modulus0 : Int) (exponent : Int) (base : Int) (r : Int) (e : Int) (b : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (Z.rem (b * b) modulus_pre))) (PreH2 : ((0 : Int) <= retval_2)) (PreH3 : (retval_2 < modulus_pre)) (PreH4 : (retval = (Z.rem (r * b) modulus_pre))) (PreH5 : ((0 : Int) <= retval)) (PreH6 : (retval < modulus_pre)) (PreH7 : (base = b_pre)) (PreH8 : (exponent = e_pre)) (PreH9 : (modulus0 = modulus_pre)) (PreH10 : (1 <= modulus_pre)) (PreH11 : (modulus_pre <= 100000000000000)) (PreH12 : ((0 : Int) <= base)) (PreH13 : ((0 : Int) <= b)) (PreH14 : (b < modulus_pre)) (PreH15 : ((0 : Int) <= e)) (PreH16 : (e <= exponent)) (PreH17 : ((0 : Int) <= r)) (PreH18 : (r < modulus_pre)) (PreH19 : (PowLoopState base exponent modulus_pre b e r)) (PreH20 : (e ≠ (0 : Int))) (PreH21 : ((Z.land e 1) ≠ (0 : Int))) ,
  (PowLoopState b_pre e_pre modulus_pre (Z.rem (b * b) modulus_pre) (Z.shiftr e 1) (Z.rem (r * b) modulus_pre))

noncomputable def powmod_entail_wit_2_1_split_goal_2 : Prop :=
  forall (modulus_pre : Int) (e_pre : Int) (b_pre : Int) (modulus0 : Int) (exponent : Int) (base : Int) (r : Int) (e : Int) (b : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (Z.rem (b * b) modulus_pre))) (PreH2 : ((0 : Int) <= retval_2)) (PreH3 : (retval_2 < modulus_pre)) (PreH4 : (retval = (Z.rem (r * b) modulus_pre))) (PreH5 : ((0 : Int) <= retval)) (PreH6 : (retval < modulus_pre)) (PreH7 : (base = b_pre)) (PreH8 : (exponent = e_pre)) (PreH9 : (modulus0 = modulus_pre)) (PreH10 : (1 <= modulus_pre)) (PreH11 : (modulus_pre <= 100000000000000)) (PreH12 : ((0 : Int) <= base)) (PreH13 : ((0 : Int) <= b)) (PreH14 : (b < modulus_pre)) (PreH15 : ((0 : Int) <= e)) (PreH16 : (e <= exponent)) (PreH17 : ((0 : Int) <= r)) (PreH18 : (r < modulus_pre)) (PreH19 : (PowLoopState base exponent modulus_pre b e r)) (PreH20 : (e ≠ (0 : Int))) (PreH21 : ((Z.land e 1) ≠ (0 : Int))) ,
  ((Z.shiftr e 1) <= e_pre)

noncomputable def powmod_entail_wit_2_1_split_goal_3 : Prop :=
  forall (modulus_pre : Int) (e_pre : Int) (b_pre : Int) (modulus0 : Int) (exponent : Int) (base : Int) (r : Int) (e : Int) (b : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (Z.rem (b * b) modulus_pre))) (PreH2 : ((0 : Int) <= retval_2)) (PreH3 : (retval_2 < modulus_pre)) (PreH4 : (retval = (Z.rem (r * b) modulus_pre))) (PreH5 : ((0 : Int) <= retval)) (PreH6 : (retval < modulus_pre)) (PreH7 : (base = b_pre)) (PreH8 : (exponent = e_pre)) (PreH9 : (modulus0 = modulus_pre)) (PreH10 : (1 <= modulus_pre)) (PreH11 : (modulus_pre <= 100000000000000)) (PreH12 : ((0 : Int) <= base)) (PreH13 : ((0 : Int) <= b)) (PreH14 : (b < modulus_pre)) (PreH15 : ((0 : Int) <= e)) (PreH16 : (e <= exponent)) (PreH17 : ((0 : Int) <= r)) (PreH18 : (r < modulus_pre)) (PreH19 : (PowLoopState base exponent modulus_pre b e r)) (PreH20 : (e ≠ (0 : Int))) (PreH21 : ((Z.land e 1) ≠ (0 : Int))) ,
  ((0 : Int) <= (Z.shiftr e 1))

noncomputable def powmod_entail_wit_2_2 : Prop :=
  (
forall (modulus_pre : Int) (e_pre : Int) (b_pre : Int) (modulus0 : Int) (exponent : Int) (base : Int) (r : Int) (e : Int) (b : Int) (retval : Int) (PreH1 : (retval = (Z.rem (b * b) modulus_pre))) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval < modulus_pre)) (PreH4 : (base = b_pre)) (PreH5 : (exponent = e_pre)) (PreH6 : (modulus0 = modulus_pre)) (PreH7 : (1 <= modulus_pre)) (PreH8 : (modulus_pre <= 100000000000000)) (PreH9 : ((0 : Int) <= base)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b < modulus_pre)) (PreH12 : ((0 : Int) <= e)) (PreH13 : (e <= exponent)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (PowLoopState base exponent modulus_pre b e r)) (PreH17 : (e ≠ (0 : Int))) (PreH18 : ((Z.land e 1) = (0 : Int))) ,
  TT && emp 
|--
  “ (base = b_pre) ” &&
  “ (exponent = e_pre) ” &&
  “ (modulus0 = modulus_pre) ” &&
  “ (1 <= modulus_pre) ” &&
  “ (modulus_pre <= 100000000000000) ” &&
  “ ((0 : Int) <= base) ” &&
  “ ((0 : Int) <= retval) ” &&
  “ (retval < modulus_pre) ” &&
  “ ((0 : Int) <= (Z.shiftr e 1)) ” &&
  “ ((Z.shiftr e 1) <= exponent) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < modulus_pre) ” &&
  “ (PowLoopState base exponent modulus_pre retval (Z.shiftr e 1) r) ”
  &&  emp
) \/
(
forall (modulus_pre : Int) (e_pre : Int) (b_pre : Int) (modulus0 : Int) (exponent : Int) (base : Int) (r : Int) (e : Int) (b : Int) (retval : Int) (PreH1 : (retval = (Z.rem (b * b) modulus_pre))) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval < modulus_pre)) (PreH4 : (base = b_pre)) (PreH5 : (exponent = e_pre)) (PreH6 : (modulus0 = modulus_pre)) (PreH7 : (1 <= modulus_pre)) (PreH8 : (modulus_pre <= 100000000000000)) (PreH9 : ((0 : Int) <= base)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b < modulus_pre)) (PreH12 : ((0 : Int) <= e)) (PreH13 : (e <= exponent)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (PowLoopState base exponent modulus_pre b e r)) (PreH17 : (e ≠ (0 : Int))) (PreH18 : ((Z.land e 1) = (0 : Int))) ,
  TT && emp 
|--
  “ (PowLoopState b_pre e_pre modulus_pre (Z.rem (b * b) modulus_pre) (Z.shiftr e 1) r) ” &&
  “ ((Z.shiftr e 1) <= e_pre) ” &&
  “ ((0 : Int) <= (Z.shiftr e 1)) ”
  &&  emp
)

noncomputable def powmod_entail_wit_2_2_split_goal_1 : Prop :=
  forall (modulus_pre : Int) (e_pre : Int) (b_pre : Int) (modulus0 : Int) (exponent : Int) (base : Int) (r : Int) (e : Int) (b : Int) (retval : Int) (PreH1 : (retval = (Z.rem (b * b) modulus_pre))) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval < modulus_pre)) (PreH4 : (base = b_pre)) (PreH5 : (exponent = e_pre)) (PreH6 : (modulus0 = modulus_pre)) (PreH7 : (1 <= modulus_pre)) (PreH8 : (modulus_pre <= 100000000000000)) (PreH9 : ((0 : Int) <= base)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b < modulus_pre)) (PreH12 : ((0 : Int) <= e)) (PreH13 : (e <= exponent)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (PowLoopState base exponent modulus_pre b e r)) (PreH17 : (e ≠ (0 : Int))) (PreH18 : ((Z.land e 1) = (0 : Int))) ,
  (PowLoopState b_pre e_pre modulus_pre (Z.rem (b * b) modulus_pre) (Z.shiftr e 1) r)

noncomputable def powmod_entail_wit_2_2_split_goal_2 : Prop :=
  forall (modulus_pre : Int) (e_pre : Int) (b_pre : Int) (modulus0 : Int) (exponent : Int) (base : Int) (r : Int) (e : Int) (b : Int) (retval : Int) (PreH1 : (retval = (Z.rem (b * b) modulus_pre))) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval < modulus_pre)) (PreH4 : (base = b_pre)) (PreH5 : (exponent = e_pre)) (PreH6 : (modulus0 = modulus_pre)) (PreH7 : (1 <= modulus_pre)) (PreH8 : (modulus_pre <= 100000000000000)) (PreH9 : ((0 : Int) <= base)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b < modulus_pre)) (PreH12 : ((0 : Int) <= e)) (PreH13 : (e <= exponent)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (PowLoopState base exponent modulus_pre b e r)) (PreH17 : (e ≠ (0 : Int))) (PreH18 : ((Z.land e 1) = (0 : Int))) ,
  ((Z.shiftr e 1) <= e_pre)

noncomputable def powmod_entail_wit_2_2_split_goal_3 : Prop :=
  forall (modulus_pre : Int) (e_pre : Int) (b_pre : Int) (modulus0 : Int) (exponent : Int) (base : Int) (r : Int) (e : Int) (b : Int) (retval : Int) (PreH1 : (retval = (Z.rem (b * b) modulus_pre))) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval < modulus_pre)) (PreH4 : (base = b_pre)) (PreH5 : (exponent = e_pre)) (PreH6 : (modulus0 = modulus_pre)) (PreH7 : (1 <= modulus_pre)) (PreH8 : (modulus_pre <= 100000000000000)) (PreH9 : ((0 : Int) <= base)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b < modulus_pre)) (PreH12 : ((0 : Int) <= e)) (PreH13 : (e <= exponent)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (PowLoopState base exponent modulus_pre b e r)) (PreH17 : (e ≠ (0 : Int))) (PreH18 : ((Z.land e 1) = (0 : Int))) ,
  ((0 : Int) <= (Z.shiftr e 1))

noncomputable def powmod_return_wit_1 : Prop :=
  (
forall (modulus_pre : Int) (e_pre : Int) (b_pre : Int) (modulus0 : Int) (exponent : Int) (base : Int) (r : Int) (e : Int) (b : Int) (PreH1 : (base = b_pre)) (PreH2 : (exponent = e_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (1 <= modulus_pre)) (PreH5 : (modulus_pre <= 100000000000000)) (PreH6 : ((0 : Int) <= base)) (PreH7 : ((0 : Int) <= b)) (PreH8 : (b < modulus_pre)) (PreH9 : ((0 : Int) <= e)) (PreH10 : (e <= exponent)) (PreH11 : ((0 : Int) <= r)) (PreH12 : (r < modulus_pre)) (PreH13 : (PowLoopState base exponent modulus_pre b e r)) (PreH14 : (e = (0 : Int))) ,
  TT && emp 
|--
  “ (r = (Z.rem (base ^ exponent) modulus0)) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < modulus0) ”
  &&  emp
) \/
(
forall (modulus_pre : Int) (e_pre : Int) (b_pre : Int) (modulus0 : Int) (exponent : Int) (base : Int) (r : Int) (e : Int) (b : Int) (PreH1 : (base = b_pre)) (PreH2 : (exponent = e_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (1 <= modulus_pre)) (PreH5 : (modulus_pre <= 100000000000000)) (PreH6 : ((0 : Int) <= base)) (PreH7 : ((0 : Int) <= b)) (PreH8 : (b < modulus_pre)) (PreH9 : ((0 : Int) <= e)) (PreH10 : (e <= exponent)) (PreH11 : ((0 : Int) <= r)) (PreH12 : (r < modulus_pre)) (PreH13 : (PowLoopState base exponent modulus_pre b e r)) (PreH14 : (e = (0 : Int))) ,
  TT && emp 
|--
  “ (r = (Z.rem (b_pre ^ e_pre) modulus_pre)) ”
  &&  emp
)

noncomputable def powmod_return_wit_1_split_goal_1 : Prop :=
  forall (modulus_pre : Int) (e_pre : Int) (b_pre : Int) (modulus0 : Int) (exponent : Int) (base : Int) (r : Int) (e : Int) (b : Int) (PreH1 : (base = b_pre)) (PreH2 : (exponent = e_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (1 <= modulus_pre)) (PreH5 : (modulus_pre <= 100000000000000)) (PreH6 : ((0 : Int) <= base)) (PreH7 : ((0 : Int) <= b)) (PreH8 : (b < modulus_pre)) (PreH9 : ((0 : Int) <= e)) (PreH10 : (e <= exponent)) (PreH11 : ((0 : Int) <= r)) (PreH12 : (r < modulus_pre)) (PreH13 : (PowLoopState base exponent modulus_pre b e r)) (PreH14 : (e = (0 : Int))) ,
  (r = (Z.rem (b_pre ^ e_pre) modulus_pre))

noncomputable def powmod_partial_solve_wit_1_pure : Prop :=
  forall (modulus_pre : Int) (e_pre : Int) (b_pre : Int) (modulus0 : Int) (exponent : Int) (base : Int) (r : Int) (e : Int) (b : Int) (PreH1 : (base = b_pre)) (PreH2 : (exponent = e_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (1 <= modulus_pre)) (PreH5 : (modulus_pre <= 100000000000000)) (PreH6 : ((0 : Int) <= base)) (PreH7 : ((0 : Int) <= b)) (PreH8 : (b < modulus_pre)) (PreH9 : ((0 : Int) <= e)) (PreH10 : (e <= exponent)) (PreH11 : ((0 : Int) <= r)) (PreH12 : (r < modulus_pre)) (PreH13 : (PowLoopState base exponent modulus_pre b e r)) (PreH14 : (e ≠ (0 : Int))) (PreH15 : ((Z.land e 1) ≠ (0 : Int))) ,
  ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "b" ) )) # UInt64 |-> (b))
  ** ((( &( "e" ) )) # UInt64 |-> (e))
  ** ((( &( "r" ) )) # UInt64 |-> (r))
|--
  “ (r = r) ” &&
  “ (b = b) ” &&
  “ (modulus_pre = modulus_pre) ” &&
  “ (1 <= modulus_pre) ” &&
  “ (modulus_pre <= 100000000000000) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r <= 18446744073709551615) ” &&
  “ ((0 : Int) <= b) ” &&
  “ (b <= 18446744073709551615) ”

noncomputable def powmod_partial_solve_wit_1_aux : Prop :=
  forall (modulus_pre : Int) (e_pre : Int) (b_pre : Int) (modulus0 : Int) (exponent : Int) (base : Int) (r : Int) (e : Int) (b : Int) (PreH1 : (base = b_pre)) (PreH2 : (exponent = e_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (1 <= modulus_pre)) (PreH5 : (modulus_pre <= 100000000000000)) (PreH6 : ((0 : Int) <= base)) (PreH7 : ((0 : Int) <= b)) (PreH8 : (b < modulus_pre)) (PreH9 : ((0 : Int) <= e)) (PreH10 : (e <= exponent)) (PreH11 : ((0 : Int) <= r)) (PreH12 : (r < modulus_pre)) (PreH13 : (PowLoopState base exponent modulus_pre b e r)) (PreH14 : (e ≠ (0 : Int))) (PreH15 : ((Z.land e 1) ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (r = r) ” &&
  “ (b = b) ” &&
  “ (modulus_pre = modulus_pre) ” &&
  “ (1 <= modulus_pre) ” &&
  “ (modulus_pre <= 100000000000000) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r <= 18446744073709551615) ” &&
  “ ((0 : Int) <= b) ” &&
  “ (b <= 18446744073709551615) ” &&
  “ (base = b_pre) ” &&
  “ (exponent = e_pre) ” &&
  “ (modulus0 = modulus_pre) ” &&
  “ (1 <= modulus_pre) ” &&
  “ (modulus_pre <= 100000000000000) ” &&
  “ ((0 : Int) <= base) ” &&
  “ ((0 : Int) <= b) ” &&
  “ (b < modulus_pre) ” &&
  “ ((0 : Int) <= e) ” &&
  “ (e <= exponent) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < modulus_pre) ” &&
  “ (PowLoopState base exponent modulus_pre b e r) ” &&
  “ (e ≠ (0 : Int)) ” &&
  “ ((Z.land e 1) ≠ (0 : Int)) ”
  &&  emp

noncomputable def powmod_partial_solve_wit_1 : Prop := powmod_partial_solve_wit_1_pure -> powmod_partial_solve_wit_1_aux

noncomputable def powmod_partial_solve_wit_2_pure : Prop :=
  forall (modulus_pre : Int) (e_pre : Int) (b_pre : Int) (modulus0 : Int) (exponent : Int) (base : Int) (r : Int) (e : Int) (b : Int) (retval : Int) (PreH1 : (retval = (Z.rem (r * b) modulus_pre))) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval < modulus_pre)) (PreH4 : (base = b_pre)) (PreH5 : (exponent = e_pre)) (PreH6 : (modulus0 = modulus_pre)) (PreH7 : (1 <= modulus_pre)) (PreH8 : (modulus_pre <= 100000000000000)) (PreH9 : ((0 : Int) <= base)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b < modulus_pre)) (PreH12 : ((0 : Int) <= e)) (PreH13 : (e <= exponent)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (PowLoopState base exponent modulus_pre b e r)) (PreH17 : (e ≠ (0 : Int))) (PreH18 : ((Z.land e 1) ≠ (0 : Int))) ,
  ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "b" ) )) # UInt64 |-> (b))
  ** ((( &( "e" ) )) # UInt64 |-> (e))
  ** ((( &( "r" ) )) # UInt64 |-> (retval))
|--
  “ (b = b) ” &&
  “ (b = b) ” &&
  “ (modulus_pre = modulus_pre) ” &&
  “ (1 <= modulus_pre) ” &&
  “ (modulus_pre <= 100000000000000) ” &&
  “ ((0 : Int) <= b) ” &&
  “ (b <= 18446744073709551615) ” &&
  “ ((0 : Int) <= b) ” &&
  “ (b <= 18446744073709551615) ”

noncomputable def powmod_partial_solve_wit_2_aux : Prop :=
  forall (modulus_pre : Int) (e_pre : Int) (b_pre : Int) (modulus0 : Int) (exponent : Int) (base : Int) (r : Int) (e : Int) (b : Int) (retval : Int) (PreH1 : (retval = (Z.rem (r * b) modulus_pre))) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval < modulus_pre)) (PreH4 : (base = b_pre)) (PreH5 : (exponent = e_pre)) (PreH6 : (modulus0 = modulus_pre)) (PreH7 : (1 <= modulus_pre)) (PreH8 : (modulus_pre <= 100000000000000)) (PreH9 : ((0 : Int) <= base)) (PreH10 : ((0 : Int) <= b)) (PreH11 : (b < modulus_pre)) (PreH12 : ((0 : Int) <= e)) (PreH13 : (e <= exponent)) (PreH14 : ((0 : Int) <= r)) (PreH15 : (r < modulus_pre)) (PreH16 : (PowLoopState base exponent modulus_pre b e r)) (PreH17 : (e ≠ (0 : Int))) (PreH18 : ((Z.land e 1) ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (b = b) ” &&
  “ (b = b) ” &&
  “ (modulus_pre = modulus_pre) ” &&
  “ (1 <= modulus_pre) ” &&
  “ (modulus_pre <= 100000000000000) ” &&
  “ ((0 : Int) <= b) ” &&
  “ (b <= 18446744073709551615) ” &&
  “ ((0 : Int) <= b) ” &&
  “ (b <= 18446744073709551615) ” &&
  “ (retval = (Z.rem (r * b) modulus_pre)) ” &&
  “ ((0 : Int) <= retval) ” &&
  “ (retval < modulus_pre) ” &&
  “ (base = b_pre) ” &&
  “ (exponent = e_pre) ” &&
  “ (modulus0 = modulus_pre) ” &&
  “ (1 <= modulus_pre) ” &&
  “ (modulus_pre <= 100000000000000) ” &&
  “ ((0 : Int) <= base) ” &&
  “ ((0 : Int) <= b) ” &&
  “ (b < modulus_pre) ” &&
  “ ((0 : Int) <= e) ” &&
  “ (e <= exponent) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < modulus_pre) ” &&
  “ (PowLoopState base exponent modulus_pre b e r) ” &&
  “ (e ≠ (0 : Int)) ” &&
  “ ((Z.land e 1) ≠ (0 : Int)) ”
  &&  emp

noncomputable def powmod_partial_solve_wit_2 : Prop := powmod_partial_solve_wit_2_pure -> powmod_partial_solve_wit_2_aux

noncomputable def powmod_partial_solve_wit_3_pure : Prop :=
  forall (modulus_pre : Int) (e_pre : Int) (b_pre : Int) (modulus0 : Int) (exponent : Int) (base : Int) (r : Int) (e : Int) (b : Int) (PreH1 : (base = b_pre)) (PreH2 : (exponent = e_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (1 <= modulus_pre)) (PreH5 : (modulus_pre <= 100000000000000)) (PreH6 : ((0 : Int) <= base)) (PreH7 : ((0 : Int) <= b)) (PreH8 : (b < modulus_pre)) (PreH9 : ((0 : Int) <= e)) (PreH10 : (e <= exponent)) (PreH11 : ((0 : Int) <= r)) (PreH12 : (r < modulus_pre)) (PreH13 : (PowLoopState base exponent modulus_pre b e r)) (PreH14 : (e ≠ (0 : Int))) (PreH15 : ((Z.land e 1) = (0 : Int))) ,
  ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "b" ) )) # UInt64 |-> (b))
  ** ((( &( "e" ) )) # UInt64 |-> (e))
  ** ((( &( "r" ) )) # UInt64 |-> (r))
|--
  “ (b = b) ” &&
  “ (b = b) ” &&
  “ (modulus_pre = modulus_pre) ” &&
  “ (1 <= modulus_pre) ” &&
  “ (modulus_pre <= 100000000000000) ” &&
  “ ((0 : Int) <= b) ” &&
  “ (b <= 18446744073709551615) ” &&
  “ ((0 : Int) <= b) ” &&
  “ (b <= 18446744073709551615) ”

noncomputable def powmod_partial_solve_wit_3_aux : Prop :=
  forall (modulus_pre : Int) (e_pre : Int) (b_pre : Int) (modulus0 : Int) (exponent : Int) (base : Int) (r : Int) (e : Int) (b : Int) (PreH1 : (base = b_pre)) (PreH2 : (exponent = e_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (1 <= modulus_pre)) (PreH5 : (modulus_pre <= 100000000000000)) (PreH6 : ((0 : Int) <= base)) (PreH7 : ((0 : Int) <= b)) (PreH8 : (b < modulus_pre)) (PreH9 : ((0 : Int) <= e)) (PreH10 : (e <= exponent)) (PreH11 : ((0 : Int) <= r)) (PreH12 : (r < modulus_pre)) (PreH13 : (PowLoopState base exponent modulus_pre b e r)) (PreH14 : (e ≠ (0 : Int))) (PreH15 : ((Z.land e 1) = (0 : Int))) ,
  TT && emp 
|--
  “ (b = b) ” &&
  “ (b = b) ” &&
  “ (modulus_pre = modulus_pre) ” &&
  “ (1 <= modulus_pre) ” &&
  “ (modulus_pre <= 100000000000000) ” &&
  “ ((0 : Int) <= b) ” &&
  “ (b <= 18446744073709551615) ” &&
  “ ((0 : Int) <= b) ” &&
  “ (b <= 18446744073709551615) ” &&
  “ (base = b_pre) ” &&
  “ (exponent = e_pre) ” &&
  “ (modulus0 = modulus_pre) ” &&
  “ (1 <= modulus_pre) ” &&
  “ (modulus_pre <= 100000000000000) ” &&
  “ ((0 : Int) <= base) ” &&
  “ ((0 : Int) <= b) ” &&
  “ (b < modulus_pre) ” &&
  “ ((0 : Int) <= e) ” &&
  “ (e <= exponent) ” &&
  “ ((0 : Int) <= r) ” &&
  “ (r < modulus_pre) ” &&
  “ (PowLoopState base exponent modulus_pre b e r) ” &&
  “ (e ≠ (0 : Int)) ” &&
  “ ((Z.land e 1) = (0 : Int)) ”
  &&  emp

noncomputable def powmod_partial_solve_wit_3 : Prop := powmod_partial_solve_wit_3_pure -> powmod_partial_solve_wit_3_aux

noncomputable def gcd__safety_wit_1 : Prop :=
  forall (b_pre : Int) (a_pre : Int) (b0 : Int) (a0 : Int) (b : Int) (a : Int) (PreH1 : (a0 = a_pre)) (PreH2 : (b0 = b_pre)) (PreH3 : ((0 : Int) <= a0)) (PreH4 : ((0 : Int) <= b0)) (PreH5 : ((0 : Int) <= a)) (PreH6 : (a <= 100000000000000)) (PreH7 : ((0 : Int) <= b)) (PreH8 : (b <= 100000000000000)) (PreH9 : (GcdLoopState a0 b0 a b)) (PreH10 : (b ≠ (0 : Int))) ,
  ((( &( "t" ) )) # UInt64 |->_)
  ** ((( &( "a" ) )) # UInt64 |-> (a))
  ** ((( &( "b" ) )) # UInt64 |-> (b))
|--
  “ (b ≠ (0 : Int)) ”

noncomputable def gcd__entail_wit_1 : Prop :=
  (
forall (b_pre : Int) (a_pre : Int) (b0 : Int) (a0 : Int) (PreH1 : (a_pre = a0)) (PreH2 : (b_pre = b0)) (PreH3 : ((0 : Int) <= a0)) (PreH4 : (a0 <= 100000000000000)) (PreH5 : ((0 : Int) <= b0)) (PreH6 : (b0 <= 100000000000000)) ,
  TT && emp 
|--
  “ (a0 = a_pre) ” &&
  “ (b0 = b_pre) ” &&
  “ ((0 : Int) <= a0) ” &&
  “ ((0 : Int) <= b0) ” &&
  “ ((0 : Int) <= a_pre) ” &&
  “ (a_pre <= 100000000000000) ” &&
  “ ((0 : Int) <= b_pre) ” &&
  “ (b_pre <= 100000000000000) ” &&
  “ (GcdLoopState a0 b0 a_pre b_pre) ”
  &&  emp
) \/
(
forall (b_pre : Int) (a_pre : Int) (b0 : Int) (a0 : Int) (PreH1 : (a_pre = a0)) (PreH2 : (b_pre = b0)) (PreH3 : ((0 : Int) <= a0)) (PreH4 : (a0 <= 100000000000000)) (PreH5 : ((0 : Int) <= b0)) (PreH6 : (b0 <= 100000000000000)) ,
  TT && emp 
|--
  “ (GcdLoopState a_pre b_pre a_pre b_pre) ”
  &&  emp
)

noncomputable def gcd__entail_wit_1_split_goal_1 : Prop :=
  forall (b_pre : Int) (a_pre : Int) (b0 : Int) (a0 : Int) (PreH1 : (a_pre = a0)) (PreH2 : (b_pre = b0)) (PreH3 : ((0 : Int) <= a0)) (PreH4 : (a0 <= 100000000000000)) (PreH5 : ((0 : Int) <= b0)) (PreH6 : (b0 <= 100000000000000)) ,
  (GcdLoopState a_pre b_pre a_pre b_pre)

noncomputable def gcd__entail_wit_2 : Prop :=
  (
forall (b_pre : Int) (a_pre : Int) (b0 : Int) (a0 : Int) (b : Int) (a : Int) (PreH1 : (a0 = a_pre)) (PreH2 : (b0 = b_pre)) (PreH3 : ((0 : Int) <= a0)) (PreH4 : ((0 : Int) <= b0)) (PreH5 : ((0 : Int) <= a)) (PreH6 : (a <= 100000000000000)) (PreH7 : ((0 : Int) <= b)) (PreH8 : (b <= 100000000000000)) (PreH9 : (GcdLoopState a0 b0 a b)) (PreH10 : (b ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (a0 = a_pre) ” &&
  “ (b0 = b_pre) ” &&
  “ ((0 : Int) <= a0) ” &&
  “ ((0 : Int) <= b0) ” &&
  “ ((0 : Int) <= b) ” &&
  “ (b <= 100000000000000) ” &&
  “ ((0 : Int) <= (Z.rem a b)) ” &&
  “ ((Z.rem a b) <= 100000000000000) ” &&
  “ (GcdLoopState a0 b0 b (Z.rem a b)) ”
  &&  emp
) \/
(
forall (b_pre : Int) (a_pre : Int) (b0 : Int) (a0 : Int) (b : Int) (a : Int) (PreH1 : (a0 = a_pre)) (PreH2 : (b0 = b_pre)) (PreH3 : ((0 : Int) <= a0)) (PreH4 : ((0 : Int) <= b0)) (PreH5 : ((0 : Int) <= a)) (PreH6 : (a <= 100000000000000)) (PreH7 : ((0 : Int) <= b)) (PreH8 : (b <= 100000000000000)) (PreH9 : (GcdLoopState a0 b0 a b)) (PreH10 : (b ≠ (0 : Int))) ,
  TT && emp 
|--
  “ (GcdLoopState a_pre b_pre b (Z.rem a b)) ” &&
  “ ((Z.rem a b) <= 100000000000000) ” &&
  “ ((0 : Int) <= (Z.rem a b)) ”
  &&  emp
)

noncomputable def gcd__entail_wit_2_split_goal_1 : Prop :=
  forall (b_pre : Int) (a_pre : Int) (b0 : Int) (a0 : Int) (b : Int) (a : Int) (PreH1 : (a0 = a_pre)) (PreH2 : (b0 = b_pre)) (PreH3 : ((0 : Int) <= a0)) (PreH4 : ((0 : Int) <= b0)) (PreH5 : ((0 : Int) <= a)) (PreH6 : (a <= 100000000000000)) (PreH7 : ((0 : Int) <= b)) (PreH8 : (b <= 100000000000000)) (PreH9 : (GcdLoopState a0 b0 a b)) (PreH10 : (b ≠ (0 : Int))) ,
  (GcdLoopState a_pre b_pre b (Z.rem a b))

noncomputable def gcd__entail_wit_2_split_goal_2 : Prop :=
  forall (b_pre : Int) (a_pre : Int) (b0 : Int) (a0 : Int) (b : Int) (a : Int) (PreH1 : (a0 = a_pre)) (PreH2 : (b0 = b_pre)) (PreH3 : ((0 : Int) <= a0)) (PreH4 : ((0 : Int) <= b0)) (PreH5 : ((0 : Int) <= a)) (PreH6 : (a <= 100000000000000)) (PreH7 : ((0 : Int) <= b)) (PreH8 : (b <= 100000000000000)) (PreH9 : (GcdLoopState a0 b0 a b)) (PreH10 : (b ≠ (0 : Int))) ,
  ((Z.rem a b) <= 100000000000000)

noncomputable def gcd__entail_wit_2_split_goal_3 : Prop :=
  forall (b_pre : Int) (a_pre : Int) (b0 : Int) (a0 : Int) (b : Int) (a : Int) (PreH1 : (a0 = a_pre)) (PreH2 : (b0 = b_pre)) (PreH3 : ((0 : Int) <= a0)) (PreH4 : ((0 : Int) <= b0)) (PreH5 : ((0 : Int) <= a)) (PreH6 : (a <= 100000000000000)) (PreH7 : ((0 : Int) <= b)) (PreH8 : (b <= 100000000000000)) (PreH9 : (GcdLoopState a0 b0 a b)) (PreH10 : (b ≠ (0 : Int))) ,
  ((0 : Int) <= (Z.rem a b))

noncomputable def gcd__return_wit_1 : Prop :=
  (
forall (b_pre : Int) (a_pre : Int) (b0 : Int) (a0 : Int) (b : Int) (a : Int) (PreH1 : (a0 = a_pre)) (PreH2 : (b0 = b_pre)) (PreH3 : ((0 : Int) <= a0)) (PreH4 : ((0 : Int) <= b0)) (PreH5 : ((0 : Int) <= a)) (PreH6 : (a <= 100000000000000)) (PreH7 : ((0 : Int) <= b)) (PreH8 : (b <= 100000000000000)) (PreH9 : (GcdLoopState a0 b0 a b)) (PreH10 : (b = (0 : Int))) ,
  TT && emp 
|--
  “ (a = (Zgcd (a0) (b0))) ” &&
  “ ((0 : Int) <= a) ” &&
  “ (a <= (a0 + b0)) ”
  &&  emp
) \/
(
forall (b_pre : Int) (a_pre : Int) (b0 : Int) (a0 : Int) (b : Int) (a : Int) (PreH1 : (a0 = a_pre)) (PreH2 : (b0 = b_pre)) (PreH3 : ((0 : Int) <= a0)) (PreH4 : ((0 : Int) <= b0)) (PreH5 : ((0 : Int) <= a)) (PreH6 : (a <= 100000000000000)) (PreH7 : ((0 : Int) <= b)) (PreH8 : (b <= 100000000000000)) (PreH9 : (GcdLoopState a0 b0 a b)) (PreH10 : (b = (0 : Int))) ,
  TT && emp 
|--
  “ (a <= (a_pre + b_pre)) ” &&
  “ (a = (Zgcd (a_pre) (b_pre))) ”
  &&  emp
)

noncomputable def gcd__return_wit_1_split_goal_1 : Prop :=
  forall (b_pre : Int) (a_pre : Int) (b0 : Int) (a0 : Int) (b : Int) (a : Int) (PreH1 : (a0 = a_pre)) (PreH2 : (b0 = b_pre)) (PreH3 : ((0 : Int) <= a0)) (PreH4 : ((0 : Int) <= b0)) (PreH5 : ((0 : Int) <= a)) (PreH6 : (a <= 100000000000000)) (PreH7 : ((0 : Int) <= b)) (PreH8 : (b <= 100000000000000)) (PreH9 : (GcdLoopState a0 b0 a b)) (PreH10 : (b = (0 : Int))) ,
  (a <= (a_pre + b_pre))

noncomputable def gcd__return_wit_1_split_goal_2 : Prop :=
  forall (b_pre : Int) (a_pre : Int) (b0 : Int) (a0 : Int) (b : Int) (a : Int) (PreH1 : (a0 = a_pre)) (PreH2 : (b0 = b_pre)) (PreH3 : ((0 : Int) <= a0)) (PreH4 : ((0 : Int) <= b0)) (PreH5 : ((0 : Int) <= a)) (PreH6 : (a <= 100000000000000)) (PreH7 : ((0 : Int) <= b)) (PreH8 : (b <= 100000000000000)) (PreH9 : (GcdLoopState a0 b0 a b)) (PreH10 : (b = (0 : Int))) ,
  (a = (Zgcd (a_pre) (b_pre)))

noncomputable def order_safety_wit_1 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (PreH1 : (x_pre = x0)) (PreH2 : (modulus_pre = modulus0)) (PreH3 : (phi_pre = phi0)) (PreH4 : (modulus0 <= 100000000000000)) (PreH5 : (OrderInput x0 modulus0 phi0)) ,
  ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def order_safety_wit_2 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (PreH1 : (modulus_pre = 1)) (PreH2 : (x_pre = x0)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (phi_pre = phi0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : (OrderInput x0 modulus0 phi0)) ,
  ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def order_safety_wit_3 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (PreH1 : (modulus_pre ≠ 1)) (PreH2 : (x_pre = x0)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (phi_pre = phi0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : (OrderInput x0 modulus0 phi0)) ,
  ((( &( "q" ) )) # UInt64 |->_)
  ** ((( &( "t" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "ord" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def order_safety_wit_4 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (PreH1 : ((q * q) <= t)) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (2 <= q)) (PreH8 : (q <= 10000001)) (PreH9 : ((0 : Int) < t)) (PreH10 : (t <= phi_pre)) (PreH11 : ((0 : Int) < ord)) (PreH12 : (ord <= phi_pre)) (PreH13 : (OrderTrialStateEx x_pre modulus_pre phi_pre q t ord)) ,
  ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "q" ) )) # UInt64 |-> (q))
  ** ((( &( "t" ) )) # UInt64 |-> (t))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord))
|--
  “ (q ≠ (0 : Int)) ”

noncomputable def order_safety_wit_5 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (PreH1 : ((q * q) <= t)) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (2 <= q)) (PreH8 : (q <= 10000001)) (PreH9 : ((0 : Int) < t)) (PreH10 : (t <= phi_pre)) (PreH11 : ((0 : Int) < ord)) (PreH12 : (ord <= phi_pre)) (PreH13 : (OrderTrialStateEx x_pre modulus_pre phi_pre q t ord)) ,
  ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "q" ) )) # UInt64 |-> (q))
  ** ((( &( "t" ) )) # UInt64 |-> (t))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def order_safety_wit_6 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (PreH1 : (x0 = x_pre)) (PreH2 : (modulus0 = modulus_pre)) (PreH3 : (phi0 = phi_pre)) (PreH4 : (1 < modulus_pre)) (PreH5 : (modulus_pre <= 100000000000000)) (PreH6 : (2 <= q)) (PreH7 : (q <= 10000000)) (PreH8 : ((0 : Int) < t)) (PreH9 : (t <= phi_pre)) (PreH10 : ((0 : Int) < ord)) (PreH11 : (ord <= phi_pre)) (PreH12 : (OrderFactorStateEx x_pre modulus_pre phi_pre q t ord)) ,
  ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "q" ) )) # UInt64 |-> (q))
  ** ((( &( "t" ) )) # UInt64 |-> (t))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord))
|--
  “ (q ≠ (0 : Int)) ”

noncomputable def order_safety_wit_7 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (PreH1 : (x0 = x_pre)) (PreH2 : (modulus0 = modulus_pre)) (PreH3 : (phi0 = phi_pre)) (PreH4 : (1 < modulus_pre)) (PreH5 : (modulus_pre <= 100000000000000)) (PreH6 : (2 <= q)) (PreH7 : (q <= 10000000)) (PreH8 : ((0 : Int) < t)) (PreH9 : (t <= phi_pre)) (PreH10 : ((0 : Int) < ord)) (PreH11 : (ord <= phi_pre)) (PreH12 : (OrderFactorStateEx x_pre modulus_pre phi_pre q t ord)) ,
  ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "q" ) )) # UInt64 |-> (q))
  ** ((( &( "t" ) )) # UInt64 |-> (t))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def order_safety_wit_8 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (PreH1 : ((Z.rem t q) = (0 : Int))) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (2 <= q)) (PreH8 : (q <= 10000000)) (PreH9 : ((0 : Int) < t)) (PreH10 : (t <= phi_pre)) (PreH11 : ((0 : Int) < ord)) (PreH12 : (ord <= phi_pre)) (PreH13 : (OrderFactorStateEx x_pre modulus_pre phi_pre q t ord)) ,
  ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "q" ) )) # UInt64 |-> (q))
  ** ((( &( "t" ) )) # UInt64 |-> (t))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord))
|--
  “ (q ≠ (0 : Int)) ”

noncomputable def order_safety_wit_9 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (PreH1 : (x0 = x_pre)) (PreH2 : (modulus0 = modulus_pre)) (PreH3 : (phi0 = phi_pre)) (PreH4 : (1 < modulus_pre)) (PreH5 : (modulus_pre <= 100000000000000)) (PreH6 : (2 <= q)) (PreH7 : (q <= 10000000)) (PreH8 : ((0 : Int) < t)) (PreH9 : (t <= phi_pre)) (PreH10 : ((0 : Int) < ord)) (PreH11 : (ord <= phi_pre)) (PreH12 : (OrderStripStateEx x_pre modulus_pre phi_pre q t ord)) ,
  ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "q" ) )) # UInt64 |-> (q))
  ** ((( &( "t" ) )) # UInt64 |-> (t))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord))
|--
  “ (q ≠ (0 : Int)) ”

noncomputable def order_safety_wit_10 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (PreH1 : (x0 = x_pre)) (PreH2 : (modulus0 = modulus_pre)) (PreH3 : (phi0 = phi_pre)) (PreH4 : (1 < modulus_pre)) (PreH5 : (modulus_pre <= 100000000000000)) (PreH6 : (2 <= q)) (PreH7 : (q <= 10000000)) (PreH8 : ((0 : Int) < t)) (PreH9 : (t <= phi_pre)) (PreH10 : ((0 : Int) < ord)) (PreH11 : (ord <= phi_pre)) (PreH12 : (OrderStripStateEx x_pre modulus_pre phi_pre q t ord)) ,
  ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "q" ) )) # UInt64 |-> (q))
  ** ((( &( "t" ) )) # UInt64 |-> (t))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def order_safety_wit_11 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (PreH1 : ((Z.rem ord q) = (0 : Int))) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (2 <= q)) (PreH8 : (q <= 10000000)) (PreH9 : ((0 : Int) < t)) (PreH10 : (t <= phi_pre)) (PreH11 : ((0 : Int) < ord)) (PreH12 : (ord <= phi_pre)) (PreH13 : (OrderStripStateEx x_pre modulus_pre phi_pre q t ord)) ,
  ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "q" ) )) # UInt64 |-> (q))
  ** ((( &( "t" ) )) # UInt64 |-> (t))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord))
|--
  “ (q ≠ (0 : Int)) ”

noncomputable def order_safety_wit_12 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (retval : Int) (PreH1 : (retval = (Z.rem (x_pre ^ (Z.quot ord q)) modulus_pre))) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval < modulus_pre)) (PreH4 : ((Z.rem ord q) = (0 : Int))) (PreH5 : (x0 = x_pre)) (PreH6 : (modulus0 = modulus_pre)) (PreH7 : (phi0 = phi_pre)) (PreH8 : (1 < modulus_pre)) (PreH9 : (modulus_pre <= 100000000000000)) (PreH10 : (2 <= q)) (PreH11 : (q <= 10000000)) (PreH12 : ((0 : Int) < t)) (PreH13 : (t <= phi_pre)) (PreH14 : ((0 : Int) < ord)) (PreH15 : (ord <= phi_pre)) (PreH16 : (OrderStripStateEx x_pre modulus_pre phi_pre q t ord)) ,
  ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "q" ) )) # UInt64 |-> (q))
  ** ((( &( "t" ) )) # UInt64 |-> (t))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def order_safety_wit_13 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (retval : Int) (PreH1 : (retval = 1)) (PreH2 : (retval = (Z.rem (x_pre ^ (Z.quot ord q)) modulus_pre))) (PreH3 : ((0 : Int) <= retval)) (PreH4 : (retval < modulus_pre)) (PreH5 : ((Z.rem ord q) = (0 : Int))) (PreH6 : (x0 = x_pre)) (PreH7 : (modulus0 = modulus_pre)) (PreH8 : (phi0 = phi_pre)) (PreH9 : (1 < modulus_pre)) (PreH10 : (modulus_pre <= 100000000000000)) (PreH11 : (2 <= q)) (PreH12 : (q <= 10000000)) (PreH13 : ((0 : Int) < t)) (PreH14 : (t <= phi_pre)) (PreH15 : ((0 : Int) < ord)) (PreH16 : (ord <= phi_pre)) (PreH17 : (OrderStripStateEx x_pre modulus_pre phi_pre q t ord)) ,
  ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "q" ) )) # UInt64 |-> (q))
  ** ((( &( "t" ) )) # UInt64 |-> (t))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord))
|--
  “ (q ≠ (0 : Int)) ”

noncomputable def order_safety_wit_14 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (PreH1 : ((q * q) > t)) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (2 <= q)) (PreH8 : (q <= 10000001)) (PreH9 : ((0 : Int) < t)) (PreH10 : (t <= phi_pre)) (PreH11 : ((0 : Int) < ord)) (PreH12 : (ord <= phi_pre)) (PreH13 : (OrderTrialStateEx x_pre modulus_pre phi_pre q t ord)) ,
  ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "t" ) )) # UInt64 |-> (t))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def order_safety_wit_15 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (PreH1 : (x0 = x_pre)) (PreH2 : (modulus0 = modulus_pre)) (PreH3 : (phi0 = phi_pre)) (PreH4 : (1 < modulus_pre)) (PreH5 : (modulus_pre <= 100000000000000)) (PreH6 : (1 < t)) (PreH7 : (t <= phi_pre)) (PreH8 : ((0 : Int) < ord)) (PreH9 : (ord <= phi_pre)) (PreH10 : (OrderFinalStateEx x_pre modulus_pre phi_pre t ord)) ,
  ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "t" ) )) # UInt64 |-> (t))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord))
|--
  “ (t ≠ (0 : Int)) ”

noncomputable def order_safety_wit_16 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (PreH1 : (x0 = x_pre)) (PreH2 : (modulus0 = modulus_pre)) (PreH3 : (phi0 = phi_pre)) (PreH4 : (1 < modulus_pre)) (PreH5 : (modulus_pre <= 100000000000000)) (PreH6 : (1 < t)) (PreH7 : (t <= phi_pre)) (PreH8 : ((0 : Int) < ord)) (PreH9 : (ord <= phi_pre)) (PreH10 : (OrderFinalStateEx x_pre modulus_pre phi_pre t ord)) ,
  ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "t" ) )) # UInt64 |-> (t))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def order_safety_wit_17 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (PreH1 : ((Z.rem ord t) = (0 : Int))) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (1 < t)) (PreH8 : (t <= phi_pre)) (PreH9 : ((0 : Int) < ord)) (PreH10 : (ord <= phi_pre)) (PreH11 : (OrderFinalStateEx x_pre modulus_pre phi_pre t ord)) ,
  ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "t" ) )) # UInt64 |-> (t))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord))
|--
  “ (t ≠ (0 : Int)) ”

noncomputable def order_safety_wit_18 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (retval : Int) (PreH1 : (retval = (Z.rem (x_pre ^ (Z.quot ord t)) modulus_pre))) (PreH2 : ((0 : Int) <= retval)) (PreH3 : (retval < modulus_pre)) (PreH4 : ((Z.rem ord t) = (0 : Int))) (PreH5 : (x0 = x_pre)) (PreH6 : (modulus0 = modulus_pre)) (PreH7 : (phi0 = phi_pre)) (PreH8 : (1 < modulus_pre)) (PreH9 : (modulus_pre <= 100000000000000)) (PreH10 : (1 < t)) (PreH11 : (t <= phi_pre)) (PreH12 : ((0 : Int) < ord)) (PreH13 : (ord <= phi_pre)) (PreH14 : (OrderFinalStateEx x_pre modulus_pre phi_pre t ord)) ,
  ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "t" ) )) # UInt64 |-> (t))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def order_safety_wit_19 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (retval : Int) (PreH1 : (retval = 1)) (PreH2 : (retval = (Z.rem (x_pre ^ (Z.quot ord t)) modulus_pre))) (PreH3 : ((0 : Int) <= retval)) (PreH4 : (retval < modulus_pre)) (PreH5 : ((Z.rem ord t) = (0 : Int))) (PreH6 : (x0 = x_pre)) (PreH7 : (modulus0 = modulus_pre)) (PreH8 : (phi0 = phi_pre)) (PreH9 : (1 < modulus_pre)) (PreH10 : (modulus_pre <= 100000000000000)) (PreH11 : (1 < t)) (PreH12 : (t <= phi_pre)) (PreH13 : ((0 : Int) < ord)) (PreH14 : (ord <= phi_pre)) (PreH15 : (OrderFinalStateEx x_pre modulus_pre phi_pre t ord)) ,
  ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "t" ) )) # UInt64 |-> (t))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord))
|--
  “ (t ≠ (0 : Int)) ”

noncomputable def order_entail_wit_1 : Prop :=
  (
forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (PreH1 : (modulus_pre ≠ 1)) (PreH2 : (x_pre = x0)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (phi_pre = phi0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : (OrderInput x0 modulus0 phi0)) ,
  TT && emp 
|--
  “ (x0 = x_pre) ” &&
  “ (modulus0 = modulus_pre) ” &&
  “ (phi0 = phi_pre) ” &&
  “ (1 < modulus_pre) ” &&
  “ (modulus_pre <= 100000000000000) ” &&
  “ (2 <= 2) ” &&
  “ (2 <= 10000001) ” &&
  “ ((0 : Int) < phi_pre) ” &&
  “ (phi_pre <= phi_pre) ” &&
  “ ((0 : Int) < phi_pre) ” &&
  “ (phi_pre <= phi_pre) ” &&
  “ (OrderTrialStateEx x_pre modulus_pre phi_pre 2 phi_pre phi_pre) ”
  &&  emp
) \/
(
forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (PreH1 : (modulus_pre ≠ 1)) (PreH2 : (x_pre = x0)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (phi_pre = phi0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : (OrderInput x0 modulus0 phi0)) ,
  TT && emp 
|--
  “ (OrderTrialStateEx x_pre modulus_pre phi_pre 2 phi_pre phi_pre) ” &&
  “ ((0 : Int) < phi_pre) ” &&
  “ ((0 : Int) < phi_pre) ” &&
  “ (1 < modulus_pre) ”
  &&  emp
)

noncomputable def order_entail_wit_1_split_goal_1 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (PreH1 : (modulus_pre ≠ 1)) (PreH2 : (x_pre = x0)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (phi_pre = phi0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : (OrderInput x0 modulus0 phi0)) ,
  (OrderTrialStateEx x_pre modulus_pre phi_pre 2 phi_pre phi_pre)

noncomputable def order_entail_wit_1_split_goal_2 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (PreH1 : (modulus_pre ≠ 1)) (PreH2 : (x_pre = x0)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (phi_pre = phi0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : (OrderInput x0 modulus0 phi0)) ,
  ((0 : Int) < phi_pre)

noncomputable def order_entail_wit_1_split_goal_3 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (PreH1 : (modulus_pre ≠ 1)) (PreH2 : (x_pre = x0)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (phi_pre = phi0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : (OrderInput x0 modulus0 phi0)) ,
  ((0 : Int) < phi_pre)

noncomputable def order_entail_wit_1_split_goal_4 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (PreH1 : (modulus_pre ≠ 1)) (PreH2 : (x_pre = x0)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (phi_pre = phi0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : (OrderInput x0 modulus0 phi0)) ,
  (1 < modulus_pre)

noncomputable def order_entail_wit_2 : Prop :=
  (
forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (PreH1 : ((Z.rem t q) = (0 : Int))) (PreH2 : ((q * q) <= t)) (PreH3 : (x0 = x_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (phi0 = phi_pre)) (PreH6 : (1 < modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (2 <= q)) (PreH9 : (q <= 10000001)) (PreH10 : ((0 : Int) < t)) (PreH11 : (t <= phi_pre)) (PreH12 : ((0 : Int) < ord)) (PreH13 : (ord <= phi_pre)) (PreH14 : (OrderTrialStateEx x_pre modulus_pre phi_pre q t ord)) ,
  TT && emp 
|--
  “ (x0 = x_pre) ” &&
  “ (modulus0 = modulus_pre) ” &&
  “ (phi0 = phi_pre) ” &&
  “ (1 < modulus_pre) ” &&
  “ (modulus_pre <= 100000000000000) ” &&
  “ (2 <= q) ” &&
  “ (q <= 10000000) ” &&
  “ ((0 : Int) < t) ” &&
  “ (t <= phi_pre) ” &&
  “ ((0 : Int) < ord) ” &&
  “ (ord <= phi_pre) ” &&
  “ (OrderFactorStateEx x_pre modulus_pre phi_pre q t ord) ”
  &&  emp
) \/
(
forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (PreH1 : ((Z.rem t q) = (0 : Int))) (PreH2 : ((q * q) <= t)) (PreH3 : (x0 = x_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (phi0 = phi_pre)) (PreH6 : (1 < modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (2 <= q)) (PreH9 : (q <= 10000001)) (PreH10 : ((0 : Int) < t)) (PreH11 : (t <= phi_pre)) (PreH12 : ((0 : Int) < ord)) (PreH13 : (ord <= phi_pre)) (PreH14 : (OrderTrialStateEx x_pre modulus_pre phi_pre q t ord)) ,
  TT && emp 
|--
  “ (OrderFactorStateEx x_pre modulus_pre phi_pre q t ord) ” &&
  “ (q <= 10000000) ”
  &&  emp
)

noncomputable def order_entail_wit_2_split_goal_1 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (PreH1 : ((Z.rem t q) = (0 : Int))) (PreH2 : ((q * q) <= t)) (PreH3 : (x0 = x_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (phi0 = phi_pre)) (PreH6 : (1 < modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (2 <= q)) (PreH9 : (q <= 10000001)) (PreH10 : ((0 : Int) < t)) (PreH11 : (t <= phi_pre)) (PreH12 : ((0 : Int) < ord)) (PreH13 : (ord <= phi_pre)) (PreH14 : (OrderTrialStateEx x_pre modulus_pre phi_pre q t ord)) ,
  (OrderFactorStateEx x_pre modulus_pre phi_pre q t ord)

noncomputable def order_entail_wit_2_split_goal_2 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (PreH1 : ((Z.rem t q) = (0 : Int))) (PreH2 : ((q * q) <= t)) (PreH3 : (x0 = x_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (phi0 = phi_pre)) (PreH6 : (1 < modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (2 <= q)) (PreH9 : (q <= 10000001)) (PreH10 : ((0 : Int) < t)) (PreH11 : (t <= phi_pre)) (PreH12 : ((0 : Int) < ord)) (PreH13 : (ord <= phi_pre)) (PreH14 : (OrderTrialStateEx x_pre modulus_pre phi_pre q t ord)) ,
  (q <= 10000000)

noncomputable def order_entail_wit_3 : Prop :=
  (
forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (PreH1 : ((Z.rem t q) = (0 : Int))) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (2 <= q)) (PreH8 : (q <= 10000000)) (PreH9 : ((0 : Int) < t)) (PreH10 : (t <= phi_pre)) (PreH11 : ((0 : Int) < ord)) (PreH12 : (ord <= phi_pre)) (PreH13 : (OrderFactorStateEx x_pre modulus_pre phi_pre q t ord)) ,
  TT && emp 
|--
  “ (x0 = x_pre) ” &&
  “ (modulus0 = modulus_pre) ” &&
  “ (phi0 = phi_pre) ” &&
  “ (1 < modulus_pre) ” &&
  “ (modulus_pre <= 100000000000000) ” &&
  “ (2 <= q) ” &&
  “ (q <= 10000000) ” &&
  “ ((0 : Int) < (Z.quot t q)) ” &&
  “ ((Z.quot t q) <= phi_pre) ” &&
  “ ((0 : Int) < ord) ” &&
  “ (ord <= phi_pre) ” &&
  “ (OrderFactorStateEx x_pre modulus_pre phi_pre q (Z.quot t q) ord) ”
  &&  emp
) \/
(
forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (PreH1 : ((Z.rem t q) = (0 : Int))) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (2 <= q)) (PreH8 : (q <= 10000000)) (PreH9 : ((0 : Int) < t)) (PreH10 : (t <= phi_pre)) (PreH11 : ((0 : Int) < ord)) (PreH12 : (ord <= phi_pre)) (PreH13 : (OrderFactorStateEx x_pre modulus_pre phi_pre q t ord)) ,
  TT && emp 
|--
  “ (OrderFactorStateEx x_pre modulus_pre phi_pre q (Z.quot t q) ord) ” &&
  “ ((Z.quot t q) <= phi_pre) ” &&
  “ ((0 : Int) < (Z.quot t q)) ”
  &&  emp
)

noncomputable def order_entail_wit_3_split_goal_1 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (PreH1 : ((Z.rem t q) = (0 : Int))) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (2 <= q)) (PreH8 : (q <= 10000000)) (PreH9 : ((0 : Int) < t)) (PreH10 : (t <= phi_pre)) (PreH11 : ((0 : Int) < ord)) (PreH12 : (ord <= phi_pre)) (PreH13 : (OrderFactorStateEx x_pre modulus_pre phi_pre q t ord)) ,
  (OrderFactorStateEx x_pre modulus_pre phi_pre q (Z.quot t q) ord)

noncomputable def order_entail_wit_3_split_goal_2 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (PreH1 : ((Z.rem t q) = (0 : Int))) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (2 <= q)) (PreH8 : (q <= 10000000)) (PreH9 : ((0 : Int) < t)) (PreH10 : (t <= phi_pre)) (PreH11 : ((0 : Int) < ord)) (PreH12 : (ord <= phi_pre)) (PreH13 : (OrderFactorStateEx x_pre modulus_pre phi_pre q t ord)) ,
  ((Z.quot t q) <= phi_pre)

noncomputable def order_entail_wit_3_split_goal_3 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (PreH1 : ((Z.rem t q) = (0 : Int))) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (2 <= q)) (PreH8 : (q <= 10000000)) (PreH9 : ((0 : Int) < t)) (PreH10 : (t <= phi_pre)) (PreH11 : ((0 : Int) < ord)) (PreH12 : (ord <= phi_pre)) (PreH13 : (OrderFactorStateEx x_pre modulus_pre phi_pre q t ord)) ,
  ((0 : Int) < (Z.quot t q))

noncomputable def order_entail_wit_4 : Prop :=
  (
forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (PreH1 : ((Z.rem t q) ≠ (0 : Int))) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (2 <= q)) (PreH8 : (q <= 10000000)) (PreH9 : ((0 : Int) < t)) (PreH10 : (t <= phi_pre)) (PreH11 : ((0 : Int) < ord)) (PreH12 : (ord <= phi_pre)) (PreH13 : (OrderFactorStateEx x_pre modulus_pre phi_pre q t ord)) ,
  TT && emp 
|--
  “ (x0 = x_pre) ” &&
  “ (modulus0 = modulus_pre) ” &&
  “ (phi0 = phi_pre) ” &&
  “ (1 < modulus_pre) ” &&
  “ (modulus_pre <= 100000000000000) ” &&
  “ (2 <= q) ” &&
  “ (q <= 10000000) ” &&
  “ ((0 : Int) < t) ” &&
  “ (t <= phi_pre) ” &&
  “ ((0 : Int) < ord) ” &&
  “ (ord <= phi_pre) ” &&
  “ (OrderStripStateEx x_pre modulus_pre phi_pre q t ord) ”
  &&  emp
) \/
(
forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (PreH1 : ((Z.rem t q) ≠ (0 : Int))) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (2 <= q)) (PreH8 : (q <= 10000000)) (PreH9 : ((0 : Int) < t)) (PreH10 : (t <= phi_pre)) (PreH11 : ((0 : Int) < ord)) (PreH12 : (ord <= phi_pre)) (PreH13 : (OrderFactorStateEx x_pre modulus_pre phi_pre q t ord)) ,
  TT && emp 
|--
  “ (OrderStripStateEx x_pre modulus_pre phi_pre q t ord) ”
  &&  emp
)

noncomputable def order_entail_wit_4_split_goal_1 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (PreH1 : ((Z.rem t q) ≠ (0 : Int))) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (2 <= q)) (PreH8 : (q <= 10000000)) (PreH9 : ((0 : Int) < t)) (PreH10 : (t <= phi_pre)) (PreH11 : ((0 : Int) < ord)) (PreH12 : (ord <= phi_pre)) (PreH13 : (OrderFactorStateEx x_pre modulus_pre phi_pre q t ord)) ,
  (OrderStripStateEx x_pre modulus_pre phi_pre q t ord)

noncomputable def order_entail_wit_5 : Prop :=
  (
forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (retval : Int) (PreH1 : (retval = 1)) (PreH2 : (retval = (Z.rem (x_pre ^ (Z.quot ord q)) modulus_pre))) (PreH3 : ((0 : Int) <= retval)) (PreH4 : (retval < modulus_pre)) (PreH5 : ((Z.rem ord q) = (0 : Int))) (PreH6 : (x0 = x_pre)) (PreH7 : (modulus0 = modulus_pre)) (PreH8 : (phi0 = phi_pre)) (PreH9 : (1 < modulus_pre)) (PreH10 : (modulus_pre <= 100000000000000)) (PreH11 : (2 <= q)) (PreH12 : (q <= 10000000)) (PreH13 : ((0 : Int) < t)) (PreH14 : (t <= phi_pre)) (PreH15 : ((0 : Int) < ord)) (PreH16 : (ord <= phi_pre)) (PreH17 : (OrderStripStateEx x_pre modulus_pre phi_pre q t ord)) ,
  TT && emp 
|--
  “ (x0 = x_pre) ” &&
  “ (modulus0 = modulus_pre) ” &&
  “ (phi0 = phi_pre) ” &&
  “ (1 < modulus_pre) ” &&
  “ (modulus_pre <= 100000000000000) ” &&
  “ (2 <= q) ” &&
  “ (q <= 10000000) ” &&
  “ ((0 : Int) < t) ” &&
  “ (t <= phi_pre) ” &&
  “ ((0 : Int) < (Z.quot ord q)) ” &&
  “ ((Z.quot ord q) <= phi_pre) ” &&
  “ (OrderStripStateEx x_pre modulus_pre phi_pre q t (Z.quot ord q)) ”
  &&  emp
) \/
(
forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (retval : Int) (PreH1 : (retval = 1)) (PreH2 : (retval = (Z.rem (x_pre ^ (Z.quot ord q)) modulus_pre))) (PreH3 : ((0 : Int) <= retval)) (PreH4 : (retval < modulus_pre)) (PreH5 : ((Z.rem ord q) = (0 : Int))) (PreH6 : (x0 = x_pre)) (PreH7 : (modulus0 = modulus_pre)) (PreH8 : (phi0 = phi_pre)) (PreH9 : (1 < modulus_pre)) (PreH10 : (modulus_pre <= 100000000000000)) (PreH11 : (2 <= q)) (PreH12 : (q <= 10000000)) (PreH13 : ((0 : Int) < t)) (PreH14 : (t <= phi_pre)) (PreH15 : ((0 : Int) < ord)) (PreH16 : (ord <= phi_pre)) (PreH17 : (OrderStripStateEx x_pre modulus_pre phi_pre q t ord)) ,
  TT && emp 
|--
  “ (OrderStripStateEx x_pre modulus_pre phi_pre q t (Z.quot ord q)) ” &&
  “ ((Z.quot ord q) <= phi_pre) ” &&
  “ ((0 : Int) < (Z.quot ord q)) ”
  &&  emp
)

noncomputable def order_entail_wit_5_split_goal_1 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (retval : Int) (PreH1 : (retval = 1)) (PreH2 : (retval = (Z.rem (x_pre ^ (Z.quot ord q)) modulus_pre))) (PreH3 : ((0 : Int) <= retval)) (PreH4 : (retval < modulus_pre)) (PreH5 : ((Z.rem ord q) = (0 : Int))) (PreH6 : (x0 = x_pre)) (PreH7 : (modulus0 = modulus_pre)) (PreH8 : (phi0 = phi_pre)) (PreH9 : (1 < modulus_pre)) (PreH10 : (modulus_pre <= 100000000000000)) (PreH11 : (2 <= q)) (PreH12 : (q <= 10000000)) (PreH13 : ((0 : Int) < t)) (PreH14 : (t <= phi_pre)) (PreH15 : ((0 : Int) < ord)) (PreH16 : (ord <= phi_pre)) (PreH17 : (OrderStripStateEx x_pre modulus_pre phi_pre q t ord)) ,
  (OrderStripStateEx x_pre modulus_pre phi_pre q t (Z.quot ord q))

noncomputable def order_entail_wit_5_split_goal_2 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (retval : Int) (PreH1 : (retval = 1)) (PreH2 : (retval = (Z.rem (x_pre ^ (Z.quot ord q)) modulus_pre))) (PreH3 : ((0 : Int) <= retval)) (PreH4 : (retval < modulus_pre)) (PreH5 : ((Z.rem ord q) = (0 : Int))) (PreH6 : (x0 = x_pre)) (PreH7 : (modulus0 = modulus_pre)) (PreH8 : (phi0 = phi_pre)) (PreH9 : (1 < modulus_pre)) (PreH10 : (modulus_pre <= 100000000000000)) (PreH11 : (2 <= q)) (PreH12 : (q <= 10000000)) (PreH13 : ((0 : Int) < t)) (PreH14 : (t <= phi_pre)) (PreH15 : ((0 : Int) < ord)) (PreH16 : (ord <= phi_pre)) (PreH17 : (OrderStripStateEx x_pre modulus_pre phi_pre q t ord)) ,
  ((Z.quot ord q) <= phi_pre)

noncomputable def order_entail_wit_5_split_goal_3 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (retval : Int) (PreH1 : (retval = 1)) (PreH2 : (retval = (Z.rem (x_pre ^ (Z.quot ord q)) modulus_pre))) (PreH3 : ((0 : Int) <= retval)) (PreH4 : (retval < modulus_pre)) (PreH5 : ((Z.rem ord q) = (0 : Int))) (PreH6 : (x0 = x_pre)) (PreH7 : (modulus0 = modulus_pre)) (PreH8 : (phi0 = phi_pre)) (PreH9 : (1 < modulus_pre)) (PreH10 : (modulus_pre <= 100000000000000)) (PreH11 : (2 <= q)) (PreH12 : (q <= 10000000)) (PreH13 : ((0 : Int) < t)) (PreH14 : (t <= phi_pre)) (PreH15 : ((0 : Int) < ord)) (PreH16 : (ord <= phi_pre)) (PreH17 : (OrderStripStateEx x_pre modulus_pre phi_pre q t ord)) ,
  ((0 : Int) < (Z.quot ord q))

noncomputable def order_entail_wit_6_1 : Prop :=
  (
forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (PreH1 : ((Z.rem ord q) ≠ (0 : Int))) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (2 <= q)) (PreH8 : (q <= 10000000)) (PreH9 : ((0 : Int) < t)) (PreH10 : (t <= phi_pre)) (PreH11 : ((0 : Int) < ord)) (PreH12 : (ord <= phi_pre)) (PreH13 : (OrderStripStateEx x_pre modulus_pre phi_pre q t ord)) ,
  TT && emp 
|--
  “ (x0 = x_pre) ” &&
  “ (modulus0 = modulus_pre) ” &&
  “ (phi0 = phi_pre) ” &&
  “ (1 < modulus_pre) ” &&
  “ (modulus_pre <= 100000000000000) ” &&
  “ (2 <= (q + 1)) ” &&
  “ ((q + 1) <= 10000001) ” &&
  “ ((0 : Int) < t) ” &&
  “ (t <= phi_pre) ” &&
  “ ((0 : Int) < ord) ” &&
  “ (ord <= phi_pre) ” &&
  “ (OrderTrialStateEx x_pre modulus_pre phi_pre (q + 1) t ord) ”
  &&  emp
) \/
(
forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (PreH1 : ((Z.rem ord q) ≠ (0 : Int))) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (2 <= q)) (PreH8 : (q <= 10000000)) (PreH9 : ((0 : Int) < t)) (PreH10 : (t <= phi_pre)) (PreH11 : ((0 : Int) < ord)) (PreH12 : (ord <= phi_pre)) (PreH13 : (OrderStripStateEx x_pre modulus_pre phi_pre q t ord)) ,
  TT && emp 
|--
  “ (OrderTrialStateEx x_pre modulus_pre phi_pre (q + 1) t ord) ”
  &&  emp
)

noncomputable def order_entail_wit_6_1_split_goal_1 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (PreH1 : ((Z.rem ord q) ≠ (0 : Int))) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (2 <= q)) (PreH8 : (q <= 10000000)) (PreH9 : ((0 : Int) < t)) (PreH10 : (t <= phi_pre)) (PreH11 : ((0 : Int) < ord)) (PreH12 : (ord <= phi_pre)) (PreH13 : (OrderStripStateEx x_pre modulus_pre phi_pre q t ord)) ,
  (OrderTrialStateEx x_pre modulus_pre phi_pre (q + 1) t ord)

noncomputable def order_entail_wit_6_2 : Prop :=
  (
forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (retval : Int) (PreH1 : (retval ≠ 1)) (PreH2 : (retval = (Z.rem (x_pre ^ (Z.quot ord q)) modulus_pre))) (PreH3 : ((0 : Int) <= retval)) (PreH4 : (retval < modulus_pre)) (PreH5 : ((Z.rem ord q) = (0 : Int))) (PreH6 : (x0 = x_pre)) (PreH7 : (modulus0 = modulus_pre)) (PreH8 : (phi0 = phi_pre)) (PreH9 : (1 < modulus_pre)) (PreH10 : (modulus_pre <= 100000000000000)) (PreH11 : (2 <= q)) (PreH12 : (q <= 10000000)) (PreH13 : ((0 : Int) < t)) (PreH14 : (t <= phi_pre)) (PreH15 : ((0 : Int) < ord)) (PreH16 : (ord <= phi_pre)) (PreH17 : (OrderStripStateEx x_pre modulus_pre phi_pre q t ord)) ,
  TT && emp 
|--
  “ (x0 = x_pre) ” &&
  “ (modulus0 = modulus_pre) ” &&
  “ (phi0 = phi_pre) ” &&
  “ (1 < modulus_pre) ” &&
  “ (modulus_pre <= 100000000000000) ” &&
  “ (2 <= (q + 1)) ” &&
  “ ((q + 1) <= 10000001) ” &&
  “ ((0 : Int) < t) ” &&
  “ (t <= phi_pre) ” &&
  “ ((0 : Int) < ord) ” &&
  “ (ord <= phi_pre) ” &&
  “ (OrderTrialStateEx x_pre modulus_pre phi_pre (q + 1) t ord) ”
  &&  emp
) \/
(
forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (retval : Int) (PreH1 : (retval ≠ 1)) (PreH2 : (retval = (Z.rem (x_pre ^ (Z.quot ord q)) modulus_pre))) (PreH3 : ((0 : Int) <= retval)) (PreH4 : (retval < modulus_pre)) (PreH5 : ((Z.rem ord q) = (0 : Int))) (PreH6 : (x0 = x_pre)) (PreH7 : (modulus0 = modulus_pre)) (PreH8 : (phi0 = phi_pre)) (PreH9 : (1 < modulus_pre)) (PreH10 : (modulus_pre <= 100000000000000)) (PreH11 : (2 <= q)) (PreH12 : (q <= 10000000)) (PreH13 : ((0 : Int) < t)) (PreH14 : (t <= phi_pre)) (PreH15 : ((0 : Int) < ord)) (PreH16 : (ord <= phi_pre)) (PreH17 : (OrderStripStateEx x_pre modulus_pre phi_pre q t ord)) ,
  TT && emp 
|--
  “ (OrderTrialStateEx x_pre modulus_pre phi_pre (q + 1) t ord) ”
  &&  emp
)

noncomputable def order_entail_wit_6_2_split_goal_1 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (retval : Int) (PreH1 : (retval ≠ 1)) (PreH2 : (retval = (Z.rem (x_pre ^ (Z.quot ord q)) modulus_pre))) (PreH3 : ((0 : Int) <= retval)) (PreH4 : (retval < modulus_pre)) (PreH5 : ((Z.rem ord q) = (0 : Int))) (PreH6 : (x0 = x_pre)) (PreH7 : (modulus0 = modulus_pre)) (PreH8 : (phi0 = phi_pre)) (PreH9 : (1 < modulus_pre)) (PreH10 : (modulus_pre <= 100000000000000)) (PreH11 : (2 <= q)) (PreH12 : (q <= 10000000)) (PreH13 : ((0 : Int) < t)) (PreH14 : (t <= phi_pre)) (PreH15 : ((0 : Int) < ord)) (PreH16 : (ord <= phi_pre)) (PreH17 : (OrderStripStateEx x_pre modulus_pre phi_pre q t ord)) ,
  (OrderTrialStateEx x_pre modulus_pre phi_pre (q + 1) t ord)

noncomputable def order_entail_wit_6_3 : Prop :=
  (
forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (PreH1 : ((Z.rem t q) ≠ (0 : Int))) (PreH2 : ((q * q) <= t)) (PreH3 : (x0 = x_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (phi0 = phi_pre)) (PreH6 : (1 < modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (2 <= q)) (PreH9 : (q <= 10000001)) (PreH10 : ((0 : Int) < t)) (PreH11 : (t <= phi_pre)) (PreH12 : ((0 : Int) < ord)) (PreH13 : (ord <= phi_pre)) (PreH14 : (OrderTrialStateEx x_pre modulus_pre phi_pre q t ord)) ,
  TT && emp 
|--
  “ (x0 = x_pre) ” &&
  “ (modulus0 = modulus_pre) ” &&
  “ (phi0 = phi_pre) ” &&
  “ (1 < modulus_pre) ” &&
  “ (modulus_pre <= 100000000000000) ” &&
  “ (2 <= (q + 1)) ” &&
  “ ((q + 1) <= 10000001) ” &&
  “ ((0 : Int) < t) ” &&
  “ (t <= phi_pre) ” &&
  “ ((0 : Int) < ord) ” &&
  “ (ord <= phi_pre) ” &&
  “ (OrderTrialStateEx x_pre modulus_pre phi_pre (q + 1) t ord) ”
  &&  emp
) \/
(
forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (PreH1 : ((Z.rem t q) ≠ (0 : Int))) (PreH2 : ((q * q) <= t)) (PreH3 : (x0 = x_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (phi0 = phi_pre)) (PreH6 : (1 < modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (2 <= q)) (PreH9 : (q <= 10000001)) (PreH10 : ((0 : Int) < t)) (PreH11 : (t <= phi_pre)) (PreH12 : ((0 : Int) < ord)) (PreH13 : (ord <= phi_pre)) (PreH14 : (OrderTrialStateEx x_pre modulus_pre phi_pre q t ord)) ,
  TT && emp 
|--
  “ (OrderTrialStateEx x_pre modulus_pre phi_pre (q + 1) t ord) ” &&
  “ ((q + 1) <= 10000001) ”
  &&  emp
)

noncomputable def order_entail_wit_6_3_split_goal_1 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (PreH1 : ((Z.rem t q) ≠ (0 : Int))) (PreH2 : ((q * q) <= t)) (PreH3 : (x0 = x_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (phi0 = phi_pre)) (PreH6 : (1 < modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (2 <= q)) (PreH9 : (q <= 10000001)) (PreH10 : ((0 : Int) < t)) (PreH11 : (t <= phi_pre)) (PreH12 : ((0 : Int) < ord)) (PreH13 : (ord <= phi_pre)) (PreH14 : (OrderTrialStateEx x_pre modulus_pre phi_pre q t ord)) ,
  (OrderTrialStateEx x_pre modulus_pre phi_pre (q + 1) t ord)

noncomputable def order_entail_wit_6_3_split_goal_2 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (PreH1 : ((Z.rem t q) ≠ (0 : Int))) (PreH2 : ((q * q) <= t)) (PreH3 : (x0 = x_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (phi0 = phi_pre)) (PreH6 : (1 < modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (2 <= q)) (PreH9 : (q <= 10000001)) (PreH10 : ((0 : Int) < t)) (PreH11 : (t <= phi_pre)) (PreH12 : ((0 : Int) < ord)) (PreH13 : (ord <= phi_pre)) (PreH14 : (OrderTrialStateEx x_pre modulus_pre phi_pre q t ord)) ,
  ((q + 1) <= 10000001)

noncomputable def order_entail_wit_7 : Prop :=
  (
forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (PreH1 : (t > 1)) (PreH2 : ((q * q) > t)) (PreH3 : (x0 = x_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (phi0 = phi_pre)) (PreH6 : (1 < modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (2 <= q)) (PreH9 : (q <= 10000001)) (PreH10 : ((0 : Int) < t)) (PreH11 : (t <= phi_pre)) (PreH12 : ((0 : Int) < ord)) (PreH13 : (ord <= phi_pre)) (PreH14 : (OrderTrialStateEx x_pre modulus_pre phi_pre q t ord)) ,
  TT && emp 
|--
  “ (x0 = x_pre) ” &&
  “ (modulus0 = modulus_pre) ” &&
  “ (phi0 = phi_pre) ” &&
  “ (1 < modulus_pre) ” &&
  “ (modulus_pre <= 100000000000000) ” &&
  “ (1 < t) ” &&
  “ (t <= phi_pre) ” &&
  “ ((0 : Int) < ord) ” &&
  “ (ord <= phi_pre) ” &&
  “ (OrderFinalStateEx x_pre modulus_pre phi_pre t ord) ”
  &&  emp
) \/
(
forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (PreH1 : (t > 1)) (PreH2 : ((q * q) > t)) (PreH3 : (x0 = x_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (phi0 = phi_pre)) (PreH6 : (1 < modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (2 <= q)) (PreH9 : (q <= 10000001)) (PreH10 : ((0 : Int) < t)) (PreH11 : (t <= phi_pre)) (PreH12 : ((0 : Int) < ord)) (PreH13 : (ord <= phi_pre)) (PreH14 : (OrderTrialStateEx x_pre modulus_pre phi_pre q t ord)) ,
  TT && emp 
|--
  “ (OrderFinalStateEx x_pre modulus_pre phi_pre t ord) ”
  &&  emp
)

noncomputable def order_entail_wit_7_split_goal_1 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (PreH1 : (t > 1)) (PreH2 : ((q * q) > t)) (PreH3 : (x0 = x_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (phi0 = phi_pre)) (PreH6 : (1 < modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (2 <= q)) (PreH9 : (q <= 10000001)) (PreH10 : ((0 : Int) < t)) (PreH11 : (t <= phi_pre)) (PreH12 : ((0 : Int) < ord)) (PreH13 : (ord <= phi_pre)) (PreH14 : (OrderTrialStateEx x_pre modulus_pre phi_pre q t ord)) ,
  (OrderFinalStateEx x_pre modulus_pre phi_pre t ord)

noncomputable def order_entail_wit_8 : Prop :=
  (
forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (retval : Int) (PreH1 : (retval = 1)) (PreH2 : (retval = (Z.rem (x_pre ^ (Z.quot ord t)) modulus_pre))) (PreH3 : ((0 : Int) <= retval)) (PreH4 : (retval < modulus_pre)) (PreH5 : ((Z.rem ord t) = (0 : Int))) (PreH6 : (x0 = x_pre)) (PreH7 : (modulus0 = modulus_pre)) (PreH8 : (phi0 = phi_pre)) (PreH9 : (1 < modulus_pre)) (PreH10 : (modulus_pre <= 100000000000000)) (PreH11 : (1 < t)) (PreH12 : (t <= phi_pre)) (PreH13 : ((0 : Int) < ord)) (PreH14 : (ord <= phi_pre)) (PreH15 : (OrderFinalStateEx x_pre modulus_pre phi_pre t ord)) ,
  TT && emp 
|--
  “ (x0 = x_pre) ” &&
  “ (modulus0 = modulus_pre) ” &&
  “ (phi0 = phi_pre) ” &&
  “ (1 < modulus_pre) ” &&
  “ (modulus_pre <= 100000000000000) ” &&
  “ (1 < t) ” &&
  “ (t <= phi_pre) ” &&
  “ ((0 : Int) < (Z.quot ord t)) ” &&
  “ ((Z.quot ord t) <= phi_pre) ” &&
  “ (OrderFinalStateEx x_pre modulus_pre phi_pre t (Z.quot ord t)) ”
  &&  emp
) \/
(
forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (retval : Int) (PreH1 : (retval = 1)) (PreH2 : (retval = (Z.rem (x_pre ^ (Z.quot ord t)) modulus_pre))) (PreH3 : ((0 : Int) <= retval)) (PreH4 : (retval < modulus_pre)) (PreH5 : ((Z.rem ord t) = (0 : Int))) (PreH6 : (x0 = x_pre)) (PreH7 : (modulus0 = modulus_pre)) (PreH8 : (phi0 = phi_pre)) (PreH9 : (1 < modulus_pre)) (PreH10 : (modulus_pre <= 100000000000000)) (PreH11 : (1 < t)) (PreH12 : (t <= phi_pre)) (PreH13 : ((0 : Int) < ord)) (PreH14 : (ord <= phi_pre)) (PreH15 : (OrderFinalStateEx x_pre modulus_pre phi_pre t ord)) ,
  TT && emp 
|--
  “ (OrderFinalStateEx x_pre modulus_pre phi_pre t (Z.quot ord t)) ” &&
  “ ((Z.quot ord t) <= phi_pre) ” &&
  “ ((0 : Int) < (Z.quot ord t)) ”
  &&  emp
)

noncomputable def order_entail_wit_8_split_goal_1 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (retval : Int) (PreH1 : (retval = 1)) (PreH2 : (retval = (Z.rem (x_pre ^ (Z.quot ord t)) modulus_pre))) (PreH3 : ((0 : Int) <= retval)) (PreH4 : (retval < modulus_pre)) (PreH5 : ((Z.rem ord t) = (0 : Int))) (PreH6 : (x0 = x_pre)) (PreH7 : (modulus0 = modulus_pre)) (PreH8 : (phi0 = phi_pre)) (PreH9 : (1 < modulus_pre)) (PreH10 : (modulus_pre <= 100000000000000)) (PreH11 : (1 < t)) (PreH12 : (t <= phi_pre)) (PreH13 : ((0 : Int) < ord)) (PreH14 : (ord <= phi_pre)) (PreH15 : (OrderFinalStateEx x_pre modulus_pre phi_pre t ord)) ,
  (OrderFinalStateEx x_pre modulus_pre phi_pre t (Z.quot ord t))

noncomputable def order_entail_wit_8_split_goal_2 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (retval : Int) (PreH1 : (retval = 1)) (PreH2 : (retval = (Z.rem (x_pre ^ (Z.quot ord t)) modulus_pre))) (PreH3 : ((0 : Int) <= retval)) (PreH4 : (retval < modulus_pre)) (PreH5 : ((Z.rem ord t) = (0 : Int))) (PreH6 : (x0 = x_pre)) (PreH7 : (modulus0 = modulus_pre)) (PreH8 : (phi0 = phi_pre)) (PreH9 : (1 < modulus_pre)) (PreH10 : (modulus_pre <= 100000000000000)) (PreH11 : (1 < t)) (PreH12 : (t <= phi_pre)) (PreH13 : ((0 : Int) < ord)) (PreH14 : (ord <= phi_pre)) (PreH15 : (OrderFinalStateEx x_pre modulus_pre phi_pre t ord)) ,
  ((Z.quot ord t) <= phi_pre)

noncomputable def order_entail_wit_8_split_goal_3 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (retval : Int) (PreH1 : (retval = 1)) (PreH2 : (retval = (Z.rem (x_pre ^ (Z.quot ord t)) modulus_pre))) (PreH3 : ((0 : Int) <= retval)) (PreH4 : (retval < modulus_pre)) (PreH5 : ((Z.rem ord t) = (0 : Int))) (PreH6 : (x0 = x_pre)) (PreH7 : (modulus0 = modulus_pre)) (PreH8 : (phi0 = phi_pre)) (PreH9 : (1 < modulus_pre)) (PreH10 : (modulus_pre <= 100000000000000)) (PreH11 : (1 < t)) (PreH12 : (t <= phi_pre)) (PreH13 : ((0 : Int) < ord)) (PreH14 : (ord <= phi_pre)) (PreH15 : (OrderFinalStateEx x_pre modulus_pre phi_pre t ord)) ,
  ((0 : Int) < (Z.quot ord t))

noncomputable def order_return_wit_1 : Prop :=
  (
forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (PreH1 : ((Z.rem ord t) ≠ (0 : Int))) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (1 < t)) (PreH8 : (t <= phi_pre)) (PreH9 : ((0 : Int) < ord)) (PreH10 : (ord <= phi_pre)) (PreH11 : (OrderFinalStateEx x_pre modulus_pre phi_pre t ord)) ,
  TT && emp 
|--
  “ (OrderResult x0 modulus0 ord) ”
  &&  emp
) \/
(
forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (PreH1 : ((Z.rem ord t) ≠ (0 : Int))) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (1 < t)) (PreH8 : (t <= phi_pre)) (PreH9 : ((0 : Int) < ord)) (PreH10 : (ord <= phi_pre)) (PreH11 : (OrderFinalStateEx x_pre modulus_pre phi_pre t ord)) ,
  TT && emp 
|--
  “ (OrderResult x_pre modulus_pre ord) ”
  &&  emp
)

noncomputable def order_return_wit_1_split_goal_1 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (PreH1 : ((Z.rem ord t) ≠ (0 : Int))) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (1 < t)) (PreH8 : (t <= phi_pre)) (PreH9 : ((0 : Int) < ord)) (PreH10 : (ord <= phi_pre)) (PreH11 : (OrderFinalStateEx x_pre modulus_pre phi_pre t ord)) ,
  (OrderResult x_pre modulus_pre ord)

noncomputable def order_return_wit_2 : Prop :=
  (
forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (retval : Int) (PreH1 : (retval ≠ 1)) (PreH2 : (retval = (Z.rem (x_pre ^ (Z.quot ord t)) modulus_pre))) (PreH3 : ((0 : Int) <= retval)) (PreH4 : (retval < modulus_pre)) (PreH5 : ((Z.rem ord t) = (0 : Int))) (PreH6 : (x0 = x_pre)) (PreH7 : (modulus0 = modulus_pre)) (PreH8 : (phi0 = phi_pre)) (PreH9 : (1 < modulus_pre)) (PreH10 : (modulus_pre <= 100000000000000)) (PreH11 : (1 < t)) (PreH12 : (t <= phi_pre)) (PreH13 : ((0 : Int) < ord)) (PreH14 : (ord <= phi_pre)) (PreH15 : (OrderFinalStateEx x_pre modulus_pre phi_pre t ord)) ,
  TT && emp 
|--
  “ (OrderResult x0 modulus0 ord) ”
  &&  emp
) \/
(
forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (retval : Int) (PreH1 : (retval ≠ 1)) (PreH2 : (retval = (Z.rem (x_pre ^ (Z.quot ord t)) modulus_pre))) (PreH3 : ((0 : Int) <= retval)) (PreH4 : (retval < modulus_pre)) (PreH5 : ((Z.rem ord t) = (0 : Int))) (PreH6 : (x0 = x_pre)) (PreH7 : (modulus0 = modulus_pre)) (PreH8 : (phi0 = phi_pre)) (PreH9 : (1 < modulus_pre)) (PreH10 : (modulus_pre <= 100000000000000)) (PreH11 : (1 < t)) (PreH12 : (t <= phi_pre)) (PreH13 : ((0 : Int) < ord)) (PreH14 : (ord <= phi_pre)) (PreH15 : (OrderFinalStateEx x_pre modulus_pre phi_pre t ord)) ,
  TT && emp 
|--
  “ (OrderResult x_pre modulus_pre ord) ”
  &&  emp
)

noncomputable def order_return_wit_2_split_goal_1 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (retval : Int) (PreH1 : (retval ≠ 1)) (PreH2 : (retval = (Z.rem (x_pre ^ (Z.quot ord t)) modulus_pre))) (PreH3 : ((0 : Int) <= retval)) (PreH4 : (retval < modulus_pre)) (PreH5 : ((Z.rem ord t) = (0 : Int))) (PreH6 : (x0 = x_pre)) (PreH7 : (modulus0 = modulus_pre)) (PreH8 : (phi0 = phi_pre)) (PreH9 : (1 < modulus_pre)) (PreH10 : (modulus_pre <= 100000000000000)) (PreH11 : (1 < t)) (PreH12 : (t <= phi_pre)) (PreH13 : ((0 : Int) < ord)) (PreH14 : (ord <= phi_pre)) (PreH15 : (OrderFinalStateEx x_pre modulus_pre phi_pre t ord)) ,
  (OrderResult x_pre modulus_pre ord)

noncomputable def order_return_wit_3 : Prop :=
  (
forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (PreH1 : (t <= 1)) (PreH2 : ((q * q) > t)) (PreH3 : (x0 = x_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (phi0 = phi_pre)) (PreH6 : (1 < modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (2 <= q)) (PreH9 : (q <= 10000001)) (PreH10 : ((0 : Int) < t)) (PreH11 : (t <= phi_pre)) (PreH12 : ((0 : Int) < ord)) (PreH13 : (ord <= phi_pre)) (PreH14 : (OrderTrialStateEx x_pre modulus_pre phi_pre q t ord)) ,
  TT && emp 
|--
  “ (OrderResult x0 modulus0 ord) ”
  &&  emp
) \/
(
forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (PreH1 : (t <= 1)) (PreH2 : ((q * q) > t)) (PreH3 : (x0 = x_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (phi0 = phi_pre)) (PreH6 : (1 < modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (2 <= q)) (PreH9 : (q <= 10000001)) (PreH10 : ((0 : Int) < t)) (PreH11 : (t <= phi_pre)) (PreH12 : ((0 : Int) < ord)) (PreH13 : (ord <= phi_pre)) (PreH14 : (OrderTrialStateEx x_pre modulus_pre phi_pre q t ord)) ,
  TT && emp 
|--
  “ (OrderResult x_pre modulus_pre ord) ”
  &&  emp
)

noncomputable def order_return_wit_3_split_goal_1 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (PreH1 : (t <= 1)) (PreH2 : ((q * q) > t)) (PreH3 : (x0 = x_pre)) (PreH4 : (modulus0 = modulus_pre)) (PreH5 : (phi0 = phi_pre)) (PreH6 : (1 < modulus_pre)) (PreH7 : (modulus_pre <= 100000000000000)) (PreH8 : (2 <= q)) (PreH9 : (q <= 10000001)) (PreH10 : ((0 : Int) < t)) (PreH11 : (t <= phi_pre)) (PreH12 : ((0 : Int) < ord)) (PreH13 : (ord <= phi_pre)) (PreH14 : (OrderTrialStateEx x_pre modulus_pre phi_pre q t ord)) ,
  (OrderResult x_pre modulus_pre ord)

noncomputable def order_return_wit_4 : Prop :=
  (
forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (PreH1 : (modulus_pre = 1)) (PreH2 : (x_pre = x0)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (phi_pre = phi0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : (OrderInput x0 modulus0 phi0)) ,
  TT && emp 
|--
  “ (OrderResult x0 modulus0 1) ”
  &&  emp
) \/
(
forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (PreH1 : (modulus_pre = 1)) (PreH2 : (x_pre = x0)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (phi_pre = phi0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : (OrderInput x0 modulus0 phi0)) ,
  TT && emp 
|--
  “ (OrderResult x_pre modulus_pre 1) ”
  &&  emp
)

noncomputable def order_return_wit_4_split_goal_1 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (PreH1 : (modulus_pre = 1)) (PreH2 : (x_pre = x0)) (PreH3 : (modulus_pre = modulus0)) (PreH4 : (phi_pre = phi0)) (PreH5 : (modulus0 <= 100000000000000)) (PreH6 : (OrderInput x0 modulus0 phi0)) ,
  (OrderResult x_pre modulus_pre 1)

noncomputable def order_partial_solve_wit_1_pure : Prop :=
  (
forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (PreH1 : ((Z.rem ord q) = (0 : Int))) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (2 <= q)) (PreH8 : (q <= 10000000)) (PreH9 : ((0 : Int) < t)) (PreH10 : (t <= phi_pre)) (PreH11 : ((0 : Int) < ord)) (PreH12 : (ord <= phi_pre)) (PreH13 : (OrderStripStateEx x_pre modulus_pre phi_pre q t ord)) ,
  ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "q" ) )) # UInt64 |-> (q))
  ** ((( &( "t" ) )) # UInt64 |-> (t))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord))
|--
  “ (x_pre = x_pre) ” &&
  “ ((Z.quot ord q) = (Z.quot ord q)) ” &&
  “ (modulus_pre = modulus_pre) ” &&
  “ (1 <= modulus_pre) ” &&
  “ (modulus_pre <= 100000000000000) ” &&
  “ ((Z.quot ord q) <= 100000000000000) ” &&
  “ ((0 : Int) <= (Z.quot ord q)) ” &&
  “ (x_pre <= 18446744073709551615) ” &&
  “ ((0 : Int) <= x_pre) ”
) \/
(
forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (PreH1 : (ord <= 18446744073709551615)) (PreH2 : (t <= 18446744073709551615)) (PreH3 : (q <= 18446744073709551615)) (PreH4 : (phi_pre <= 18446744073709551615)) (PreH5 : (modulus_pre <= 18446744073709551615)) (PreH6 : (x_pre <= 18446744073709551615)) (PreH7 : (ord >= (0 : Int))) (PreH8 : (t >= (0 : Int))) (PreH9 : (q >= (0 : Int))) (PreH10 : (phi_pre >= (0 : Int))) (PreH11 : (modulus_pre >= (0 : Int))) (PreH12 : (x_pre >= (0 : Int))) (PreH13 : ((Z.rem ord q) = (0 : Int))) (PreH14 : (x0 = x_pre)) (PreH15 : (modulus0 = modulus_pre)) (PreH16 : (phi0 = phi_pre)) (PreH17 : (1 < modulus_pre)) (PreH18 : (modulus_pre <= 100000000000000)) (PreH19 : (2 <= q)) (PreH20 : (q <= 10000000)) (PreH21 : ((0 : Int) < t)) (PreH22 : (t <= phi_pre)) (PreH23 : ((0 : Int) < ord)) (PreH24 : (ord <= phi_pre)) (PreH25 : (OrderStripStateEx x_pre modulus_pre phi_pre q t ord)) ,
  ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "q" ) )) # UInt64 |-> (q))
  ** ((( &( "t" ) )) # UInt64 |-> (t))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord))
|--
  “ ((0 : Int) <= (Z.quot ord q)) ” &&
  “ ((Z.quot ord q) <= 100000000000000) ”
)

noncomputable def order_partial_solve_wit_1_pure_split_goal_1 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (PreH1 : (ord <= 18446744073709551615)) (PreH2 : (t <= 18446744073709551615)) (PreH3 : (q <= 18446744073709551615)) (PreH4 : (phi_pre <= 18446744073709551615)) (PreH5 : (modulus_pre <= 18446744073709551615)) (PreH6 : (x_pre <= 18446744073709551615)) (PreH7 : (ord >= (0 : Int))) (PreH8 : (t >= (0 : Int))) (PreH9 : (q >= (0 : Int))) (PreH10 : (phi_pre >= (0 : Int))) (PreH11 : (modulus_pre >= (0 : Int))) (PreH12 : (x_pre >= (0 : Int))) (PreH13 : ((Z.rem ord q) = (0 : Int))) (PreH14 : (x0 = x_pre)) (PreH15 : (modulus0 = modulus_pre)) (PreH16 : (phi0 = phi_pre)) (PreH17 : (1 < modulus_pre)) (PreH18 : (modulus_pre <= 100000000000000)) (PreH19 : (2 <= q)) (PreH20 : (q <= 10000000)) (PreH21 : ((0 : Int) < t)) (PreH22 : (t <= phi_pre)) (PreH23 : ((0 : Int) < ord)) (PreH24 : (ord <= phi_pre)) (PreH25 : (OrderStripStateEx x_pre modulus_pre phi_pre q t ord)) ,
  ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "q" ) )) # UInt64 |-> (q))
  ** ((( &( "t" ) )) # UInt64 |-> (t))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord))
|--
  “ ((0 : Int) <= (Z.quot ord q)) ”

noncomputable def order_partial_solve_wit_1_pure_split_goal_2 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (PreH1 : (ord <= 18446744073709551615)) (PreH2 : (t <= 18446744073709551615)) (PreH3 : (q <= 18446744073709551615)) (PreH4 : (phi_pre <= 18446744073709551615)) (PreH5 : (modulus_pre <= 18446744073709551615)) (PreH6 : (x_pre <= 18446744073709551615)) (PreH7 : (ord >= (0 : Int))) (PreH8 : (t >= (0 : Int))) (PreH9 : (q >= (0 : Int))) (PreH10 : (phi_pre >= (0 : Int))) (PreH11 : (modulus_pre >= (0 : Int))) (PreH12 : (x_pre >= (0 : Int))) (PreH13 : ((Z.rem ord q) = (0 : Int))) (PreH14 : (x0 = x_pre)) (PreH15 : (modulus0 = modulus_pre)) (PreH16 : (phi0 = phi_pre)) (PreH17 : (1 < modulus_pre)) (PreH18 : (modulus_pre <= 100000000000000)) (PreH19 : (2 <= q)) (PreH20 : (q <= 10000000)) (PreH21 : ((0 : Int) < t)) (PreH22 : (t <= phi_pre)) (PreH23 : ((0 : Int) < ord)) (PreH24 : (ord <= phi_pre)) (PreH25 : (OrderStripStateEx x_pre modulus_pre phi_pre q t ord)) ,
  ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "q" ) )) # UInt64 |-> (q))
  ** ((( &( "t" ) )) # UInt64 |-> (t))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord))
|--
  “ ((Z.quot ord q) <= 100000000000000) ”

noncomputable def order_partial_solve_wit_1_aux : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (q : Int) (PreH1 : ((Z.rem ord q) = (0 : Int))) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (2 <= q)) (PreH8 : (q <= 10000000)) (PreH9 : ((0 : Int) < t)) (PreH10 : (t <= phi_pre)) (PreH11 : ((0 : Int) < ord)) (PreH12 : (ord <= phi_pre)) (PreH13 : (OrderStripStateEx x_pre modulus_pre phi_pre q t ord)) ,
  TT && emp 
|--
  “ (x_pre = x_pre) ” &&
  “ ((Z.quot ord q) = (Z.quot ord q)) ” &&
  “ (modulus_pre = modulus_pre) ” &&
  “ (1 <= modulus_pre) ” &&
  “ (modulus_pre <= 100000000000000) ” &&
  “ ((Z.quot ord q) <= 100000000000000) ” &&
  “ ((0 : Int) <= (Z.quot ord q)) ” &&
  “ (x_pre <= 18446744073709551615) ” &&
  “ ((0 : Int) <= x_pre) ” &&
  “ ((Z.rem ord q) = (0 : Int)) ” &&
  “ (x0 = x_pre) ” &&
  “ (modulus0 = modulus_pre) ” &&
  “ (phi0 = phi_pre) ” &&
  “ (1 < modulus_pre) ” &&
  “ (modulus_pre <= 100000000000000) ” &&
  “ (2 <= q) ” &&
  “ (q <= 10000000) ” &&
  “ ((0 : Int) < t) ” &&
  “ (t <= phi_pre) ” &&
  “ ((0 : Int) < ord) ” &&
  “ (ord <= phi_pre) ” &&
  “ (OrderStripStateEx x_pre modulus_pre phi_pre q t ord) ”
  &&  emp

noncomputable def order_partial_solve_wit_1 : Prop := order_partial_solve_wit_1_pure -> order_partial_solve_wit_1_aux

noncomputable def order_partial_solve_wit_2_pure : Prop :=
  (
forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (PreH1 : ((Z.rem ord t) = (0 : Int))) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (1 < t)) (PreH8 : (t <= phi_pre)) (PreH9 : ((0 : Int) < ord)) (PreH10 : (ord <= phi_pre)) (PreH11 : (OrderFinalStateEx x_pre modulus_pre phi_pre t ord)) ,
  ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "t" ) )) # UInt64 |-> (t))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord))
|--
  “ (x_pre = x_pre) ” &&
  “ ((Z.quot ord t) = (Z.quot ord t)) ” &&
  “ (modulus_pre = modulus_pre) ” &&
  “ (1 <= modulus_pre) ” &&
  “ (modulus_pre <= 100000000000000) ” &&
  “ ((Z.quot ord t) <= 100000000000000) ” &&
  “ ((0 : Int) <= (Z.quot ord t)) ” &&
  “ (x_pre <= 18446744073709551615) ” &&
  “ ((0 : Int) <= x_pre) ”
) \/
(
forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (PreH1 : (ord <= 18446744073709551615)) (PreH2 : (t <= 18446744073709551615)) (PreH3 : (phi_pre <= 18446744073709551615)) (PreH4 : (modulus_pre <= 18446744073709551615)) (PreH5 : (x_pre <= 18446744073709551615)) (PreH6 : (ord >= (0 : Int))) (PreH7 : (t >= (0 : Int))) (PreH8 : (phi_pre >= (0 : Int))) (PreH9 : (modulus_pre >= (0 : Int))) (PreH10 : (x_pre >= (0 : Int))) (PreH11 : ((Z.rem ord t) = (0 : Int))) (PreH12 : (x0 = x_pre)) (PreH13 : (modulus0 = modulus_pre)) (PreH14 : (phi0 = phi_pre)) (PreH15 : (1 < modulus_pre)) (PreH16 : (modulus_pre <= 100000000000000)) (PreH17 : (1 < t)) (PreH18 : (t <= phi_pre)) (PreH19 : ((0 : Int) < ord)) (PreH20 : (ord <= phi_pre)) (PreH21 : (OrderFinalStateEx x_pre modulus_pre phi_pre t ord)) ,
  ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "t" ) )) # UInt64 |-> (t))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord))
|--
  “ ((0 : Int) <= (Z.quot ord t)) ” &&
  “ ((Z.quot ord t) <= 100000000000000) ”
)

noncomputable def order_partial_solve_wit_2_pure_split_goal_1 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (PreH1 : (ord <= 18446744073709551615)) (PreH2 : (t <= 18446744073709551615)) (PreH3 : (phi_pre <= 18446744073709551615)) (PreH4 : (modulus_pre <= 18446744073709551615)) (PreH5 : (x_pre <= 18446744073709551615)) (PreH6 : (ord >= (0 : Int))) (PreH7 : (t >= (0 : Int))) (PreH8 : (phi_pre >= (0 : Int))) (PreH9 : (modulus_pre >= (0 : Int))) (PreH10 : (x_pre >= (0 : Int))) (PreH11 : ((Z.rem ord t) = (0 : Int))) (PreH12 : (x0 = x_pre)) (PreH13 : (modulus0 = modulus_pre)) (PreH14 : (phi0 = phi_pre)) (PreH15 : (1 < modulus_pre)) (PreH16 : (modulus_pre <= 100000000000000)) (PreH17 : (1 < t)) (PreH18 : (t <= phi_pre)) (PreH19 : ((0 : Int) < ord)) (PreH20 : (ord <= phi_pre)) (PreH21 : (OrderFinalStateEx x_pre modulus_pre phi_pre t ord)) ,
  ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "t" ) )) # UInt64 |-> (t))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord))
|--
  “ ((0 : Int) <= (Z.quot ord t)) ”

noncomputable def order_partial_solve_wit_2_pure_split_goal_2 : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (PreH1 : (ord <= 18446744073709551615)) (PreH2 : (t <= 18446744073709551615)) (PreH3 : (phi_pre <= 18446744073709551615)) (PreH4 : (modulus_pre <= 18446744073709551615)) (PreH5 : (x_pre <= 18446744073709551615)) (PreH6 : (ord >= (0 : Int))) (PreH7 : (t >= (0 : Int))) (PreH8 : (phi_pre >= (0 : Int))) (PreH9 : (modulus_pre >= (0 : Int))) (PreH10 : (x_pre >= (0 : Int))) (PreH11 : ((Z.rem ord t) = (0 : Int))) (PreH12 : (x0 = x_pre)) (PreH13 : (modulus0 = modulus_pre)) (PreH14 : (phi0 = phi_pre)) (PreH15 : (1 < modulus_pre)) (PreH16 : (modulus_pre <= 100000000000000)) (PreH17 : (1 < t)) (PreH18 : (t <= phi_pre)) (PreH19 : ((0 : Int) < ord)) (PreH20 : (ord <= phi_pre)) (PreH21 : (OrderFinalStateEx x_pre modulus_pre phi_pre t ord)) ,
  ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "modulus" ) )) # UInt64 |-> (modulus_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "t" ) )) # UInt64 |-> (t))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord))
|--
  “ ((Z.quot ord t) <= 100000000000000) ”

noncomputable def order_partial_solve_wit_2_aux : Prop :=
  forall (phi_pre : Int) (modulus_pre : Int) (x_pre : Int) (phi0 : Int) (modulus0 : Int) (x0 : Int) (ord : Int) (t : Int) (PreH1 : ((Z.rem ord t) = (0 : Int))) (PreH2 : (x0 = x_pre)) (PreH3 : (modulus0 = modulus_pre)) (PreH4 : (phi0 = phi_pre)) (PreH5 : (1 < modulus_pre)) (PreH6 : (modulus_pre <= 100000000000000)) (PreH7 : (1 < t)) (PreH8 : (t <= phi_pre)) (PreH9 : ((0 : Int) < ord)) (PreH10 : (ord <= phi_pre)) (PreH11 : (OrderFinalStateEx x_pre modulus_pre phi_pre t ord)) ,
  TT && emp 
|--
  “ (x_pre = x_pre) ” &&
  “ ((Z.quot ord t) = (Z.quot ord t)) ” &&
  “ (modulus_pre = modulus_pre) ” &&
  “ (1 <= modulus_pre) ” &&
  “ (modulus_pre <= 100000000000000) ” &&
  “ ((Z.quot ord t) <= 100000000000000) ” &&
  “ ((0 : Int) <= (Z.quot ord t)) ” &&
  “ (x_pre <= 18446744073709551615) ” &&
  “ ((0 : Int) <= x_pre) ” &&
  “ ((Z.rem ord t) = (0 : Int)) ” &&
  “ (x0 = x_pre) ” &&
  “ (modulus0 = modulus_pre) ” &&
  “ (phi0 = phi_pre) ” &&
  “ (1 < modulus_pre) ” &&
  “ (modulus_pre <= 100000000000000) ” &&
  “ (1 < t) ” &&
  “ (t <= phi_pre) ” &&
  “ ((0 : Int) < ord) ” &&
  “ (ord <= phi_pre) ” &&
  “ (OrderFinalStateEx x_pre modulus_pre phi_pre t ord) ”
  &&  emp

noncomputable def order_partial_solve_wit_2 : Prop := order_partial_solve_wit_2_pure -> order_partial_solve_wit_2_aux

noncomputable def walk_safety_wit_1 : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (PreH1 : (i_pre = factor_count)) (PreH2 : ((Zlength (pr_values)) = factor_count)) (PreH3 : ((Zlength (pe_values)) = factor_count)) (PreH4 : ((0 : Int) <= i_pre)) (PreH5 : (i_pre <= factor_count)) (PreH6 : (WalkGlobalBounds m x_value)) (PreH7 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH8 : ((0 : Int) < ord_pre)) (PreH9 : (ValidFactorTable m pr_values pe_values)) (PreH10 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH11 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)))) ,
  ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "d" ) )) # UInt64 |-> (d_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord_pre))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (before))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def walk_safety_wit_2 : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (PreH1 : (d_pre > 1)) (PreH2 : (i_pre = factor_count)) (PreH3 : ((Zlength (pr_values)) = factor_count)) (PreH4 : ((Zlength (pe_values)) = factor_count)) (PreH5 : ((0 : Int) <= i_pre)) (PreH6 : (i_pre <= factor_count)) (PreH7 : (WalkGlobalBounds m x_value)) (PreH8 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH9 : ((0 : Int) < ord_pre)) (PreH10 : (ValidFactorTable m pr_values pe_values)) (PreH11 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH12 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)))) ,
  ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "d" ) )) # UInt64 |-> (d_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord_pre))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (before))
|--
  “ (ord_pre ≠ (0 : Int)) ”

noncomputable def walk_safety_wit_3 : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : ((0 : Int) <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (WalkGlobalBounds m x_value)) (PreH6 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH7 : ((0 : Int) < ord_pre)) (PreH8 : (ValidFactorTable m pr_values pe_values)) (PreH9 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH10 : (PrefixChoice pr_values pe_values x_value (i_pre + 1) d_pre phi_pre ord_pre)) (PreH11 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)))) (PreH12 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) (d_pre)))) ,
  ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "d" ) )) # UInt64 |-> (d_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord_pre))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (before))
|--
  “ ((i_pre + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i_pre + 1)) ”

noncomputable def walk_safety_wit_4 : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : ((0 : Int) <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (WalkGlobalBounds m x_value)) (PreH6 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH7 : ((0 : Int) < ord_pre)) (PreH8 : (ValidFactorTable m pr_values pe_values)) (PreH9 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH10 : (PrefixChoice pr_values pe_values x_value (i_pre + 1) d_pre phi_pre ord_pre)) (PreH11 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)))) (PreH12 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) (d_pre)))) ,
  ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "d" ) )) # UInt64 |-> (d_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord_pre))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (before))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def walk_safety_wit_5 : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : ((0 : Int) <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (WalkGlobalBounds m x_value)) (PreH6 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH7 : ((0 : Int) < ord_pre)) (PreH8 : (ValidFactorTable m pr_values pe_values)) (PreH9 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH10 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)))) (PreH11 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before (before + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) (d_pre))) 1)) ,
  ((( &( "ph" ) )) # UInt64 |->_)
  ** ((( &( "pk" ) )) # UInt64 |-> (1))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** ((( &( "p" ) )) # UInt64 |-> ((Znth (i_pre - (0 : Int)) pr_values (0 : Int))))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "d" ) )) # UInt64 |-> (d_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord_pre))
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> ((before + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) (d_pre)))))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def walk_safety_wit_6 : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : ((0 : Int) <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (WalkGlobalBounds m x_value)) (PreH6 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH7 : ((0 : Int) < ord_pre)) (PreH8 : (ValidFactorTable m pr_values pe_values)) (PreH9 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH10 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)))) (PreH11 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before (before + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) (d_pre))) 1)) ,
  ((( &( "pk" ) )) # UInt64 |->_)
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** ((( &( "p" ) )) # UInt64 |-> ((Znth (i_pre - (0 : Int)) pr_values (0 : Int))))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "d" ) )) # UInt64 |-> (d_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord_pre))
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> ((before + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) (d_pre)))))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def walk_safety_wit_7 : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : ((0 : Int) <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (WalkGlobalBounds m x_value)) (PreH6 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH7 : ((0 : Int) < ord_pre)) (PreH8 : (ValidFactorTable m pr_values pe_values)) (PreH9 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH10 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)))) (PreH11 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before (before + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) (d_pre))) 1)) ,
  ((( &( "e" ) )) # UInt64 |->_)
  ** ((( &( "ph" ) )) # UInt64 |-> (1))
  ** ((( &( "pk" ) )) # UInt64 |-> (1))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** ((( &( "p" ) )) # UInt64 |-> ((Znth (i_pre - (0 : Int)) pr_values (0 : Int))))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "d" ) )) # UInt64 |-> (d_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord_pre))
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> ((before + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) (d_pre)))))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def walk_safety_wit_8 : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current : Int) (pk : Int) (ph : Int) (p : Int) (e : Int) (PreH1 : (e <= (Znth (i_pre - (0 : Int)) pe_values (0 : Int)))) (PreH2 : ((Zlength (pr_values)) = factor_count)) (PreH3 : ((Zlength (pe_values)) = factor_count)) (PreH4 : ((0 : Int) <= i_pre)) (PreH5 : (i_pre < factor_count)) (PreH6 : (1 <= e)) (PreH7 : (e <= ((Znth i_pre pe_values (0 : Int)) + 1))) (PreH8 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH9 : (WalkExponentState m p e (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH10 : (WalkGlobalBounds m x_value)) (PreH11 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH12 : ((0 : Int) < ord_pre)) (PreH13 : (ValidFactorTable m pr_values pe_values)) (PreH14 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH15 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e)) ,
  (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "d" ) )) # UInt64 |-> (d_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord_pre))
  ** ((( &( "e" ) )) # UInt64 |-> (e))
  ** ((( &( "p" ) )) # UInt64 |-> (p))
  ** ((( &( "ph" ) )) # UInt64 |-> (ph))
  ** ((( &( "pk" ) )) # UInt64 |-> ((unsigned_last_nbits ((pk * p)) (64))))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (current))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def walk_safety_wit_9 : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current : Int) (pk : Int) (ph : Int) (p : Int) (e : Int) (PreH1 : (e = 1)) (PreH2 : (e <= (Znth (i_pre - (0 : Int)) pe_values (0 : Int)))) (PreH3 : ((Zlength (pr_values)) = factor_count)) (PreH4 : ((Zlength (pe_values)) = factor_count)) (PreH5 : ((0 : Int) <= i_pre)) (PreH6 : (i_pre < factor_count)) (PreH7 : (1 <= e)) (PreH8 : (e <= ((Znth i_pre pe_values (0 : Int)) + 1))) (PreH9 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH10 : (WalkExponentState m p e (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH11 : (WalkGlobalBounds m x_value)) (PreH12 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH13 : ((0 : Int) < ord_pre)) (PreH14 : (ValidFactorTable m pr_values pe_values)) (PreH15 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH16 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e)) ,
  (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "d" ) )) # UInt64 |-> (d_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord_pre))
  ** ((( &( "e" ) )) # UInt64 |-> (e))
  ** ((( &( "p" ) )) # UInt64 |-> (p))
  ** ((( &( "ph" ) )) # UInt64 |-> (ph))
  ** ((( &( "pk" ) )) # UInt64 |-> ((unsigned_last_nbits ((pk * p)) (64))))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (current))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def walk_safety_wit_10 : Prop :=
  (
forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current : Int) (e : Int) (p : Int) (ph : Int) (pk : Int) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : ((0 : Int) <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (1 <= e)) (PreH6 : (e <= (Znth i_pre pe_values (0 : Int)))) (PreH7 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH8 : (WalkExponentState m p (e + 1) (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH9 : (OrderInput (Z.rem x_value pk) pk ph)) (PreH10 : (WalkGlobalBounds m x_value)) (PreH11 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH12 : ((0 : Int) < ord_pre)) (PreH13 : (ValidFactorTable m pr_values pe_values)) (PreH14 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH15 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e)) ,
  ((( &( "o" ) )) # UInt64 |->_)
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "d" ) )) # UInt64 |-> (d_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord_pre))
  ** ((( &( "e" ) )) # UInt64 |-> (e))
  ** ((( &( "p" ) )) # UInt64 |-> (p))
  ** ((( &( "ph" ) )) # UInt64 |-> (ph))
  ** ((( &( "pk" ) )) # UInt64 |-> (pk))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (current))
|--
  “ (pk ≠ (0 : Int)) ”
) \/
(
forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current : Int) (e : Int) (p : Int) (ph : Int) (pk : Int) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : ((0 : Int) <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (1 <= e)) (PreH6 : (e <= (Znth i_pre pe_values (0 : Int)))) (PreH7 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH8 : (WalkExponentState m p (e + 1) (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH9 : (OrderInput (Z.rem x_value pk) pk ph)) (PreH10 : (WalkGlobalBounds m x_value)) (PreH11 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH12 : ((0 : Int) < ord_pre)) (PreH13 : (ValidFactorTable m pr_values pe_values)) (PreH14 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH15 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e)) ,
  ((( &( "o" ) )) # UInt64 |->_)
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "d" ) )) # UInt64 |-> (d_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord_pre))
  ** ((( &( "e" ) )) # UInt64 |-> (e))
  ** ((( &( "p" ) )) # UInt64 |-> (p))
  ** ((( &( "ph" ) )) # UInt64 |-> (ph))
  ** ((( &( "pk" ) )) # UInt64 |-> (pk))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (current))
|--
  “ (pk ≠ (0 : Int)) ”
)

noncomputable def walk_safety_wit_10_split_goal_1 : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current : Int) (e : Int) (p : Int) (ph : Int) (pk : Int) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : ((0 : Int) <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (1 <= e)) (PreH6 : (e <= (Znth i_pre pe_values (0 : Int)))) (PreH7 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH8 : (WalkExponentState m p (e + 1) (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH9 : (OrderInput (Z.rem x_value pk) pk ph)) (PreH10 : (WalkGlobalBounds m x_value)) (PreH11 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH12 : ((0 : Int) < ord_pre)) (PreH13 : (ValidFactorTable m pr_values pe_values)) (PreH14 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH15 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e)) ,
  ((( &( "o" ) )) # UInt64 |->_)
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "d" ) )) # UInt64 |-> (d_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord_pre))
  ** ((( &( "e" ) )) # UInt64 |-> (e))
  ** ((( &( "p" ) )) # UInt64 |-> (p))
  ** ((( &( "ph" ) )) # UInt64 |-> (ph))
  ** ((( &( "pk" ) )) # UInt64 |-> (pk))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (current))
|--
  “ (pk ≠ (0 : Int)) ”

noncomputable def walk_safety_wit_11 : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current : Int) (e : Int) (p : Int) (g : Int) (ph : Int) (pk : Int) (o : Int) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : ((0 : Int) <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (1 <= e)) (PreH6 : (e <= (Znth i_pre pe_values (0 : Int)))) (PreH7 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH8 : ((0 : Int) < g)) (PreH9 : (WalkGlobalBounds m x_value)) (PreH10 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH11 : ((0 : Int) < ord_pre)) (PreH12 : (ValidFactorTable m pr_values pe_values)) (PreH13 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH14 : (WalkExponentState m p (e + 1) (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH15 : (WalkMachineBounds m (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH16 : (PrimePowerTransition x_value d_pre phi_pre ord_pre p e pk ph o g (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH17 : (PrefixChoice pr_values pe_values x_value (i_pre + 1) (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH18 : (WalkBudget m current (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) ((d_pre * pk))))) (PreH19 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e)) ,
  ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "d" ) )) # UInt64 |-> (d_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord_pre))
  ** ((( &( "e" ) )) # UInt64 |-> (e))
  ** ((( &( "p" ) )) # UInt64 |-> (p))
  ** ((( &( "g" ) )) # UInt64 |-> (g))
  ** ((( &( "ph" ) )) # UInt64 |-> (ph))
  ** ((( &( "pk" ) )) # UInt64 |-> (pk))
  ** ((( &( "o" ) )) # UInt64 |-> (o))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (current))
|--
  “ (g ≠ (0 : Int)) ”

noncomputable def walk_safety_wit_12 : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current : Int) (e : Int) (p : Int) (g : Int) (ph : Int) (pk : Int) (o : Int) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : ((0 : Int) <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (1 <= e)) (PreH6 : (e <= (Znth i_pre pe_values (0 : Int)))) (PreH7 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH8 : ((0 : Int) < g)) (PreH9 : (WalkGlobalBounds m x_value)) (PreH10 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH11 : ((0 : Int) < ord_pre)) (PreH12 : (ValidFactorTable m pr_values pe_values)) (PreH13 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH14 : (WalkExponentState m p (e + 1) (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH15 : (WalkMachineBounds m (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH16 : (PrimePowerTransition x_value d_pre phi_pre ord_pre p e pk ph o g (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH17 : (PrefixChoice pr_values pe_values x_value (i_pre + 1) (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH18 : (WalkBudget m current (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) ((d_pre * pk))))) (PreH19 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e)) ,
  ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "d" ) )) # UInt64 |-> (d_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord_pre))
  ** ((( &( "e" ) )) # UInt64 |-> (e))
  ** ((( &( "p" ) )) # UInt64 |-> (p))
  ** ((( &( "g" ) )) # UInt64 |-> (g))
  ** ((( &( "ph" ) )) # UInt64 |-> (ph))
  ** ((( &( "pk" ) )) # UInt64 |-> (pk))
  ** ((( &( "o" ) )) # UInt64 |-> (o))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (current))
|--
  “ ((i_pre + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i_pre + 1)) ”

noncomputable def walk_safety_wit_13 : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current : Int) (e : Int) (p : Int) (g : Int) (ph : Int) (pk : Int) (o : Int) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : ((0 : Int) <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (1 <= e)) (PreH6 : (e <= (Znth i_pre pe_values (0 : Int)))) (PreH7 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH8 : ((0 : Int) < g)) (PreH9 : (WalkGlobalBounds m x_value)) (PreH10 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH11 : ((0 : Int) < ord_pre)) (PreH12 : (ValidFactorTable m pr_values pe_values)) (PreH13 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH14 : (WalkExponentState m p (e + 1) (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH15 : (WalkMachineBounds m (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH16 : (PrimePowerTransition x_value d_pre phi_pre ord_pre p e pk ph o g (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH17 : (PrefixChoice pr_values pe_values x_value (i_pre + 1) (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH18 : (WalkBudget m current (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) ((d_pre * pk))))) (PreH19 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e)) ,
  ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "d" ) )) # UInt64 |-> (d_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord_pre))
  ** ((( &( "e" ) )) # UInt64 |-> (e))
  ** ((( &( "p" ) )) # UInt64 |-> (p))
  ** ((( &( "g" ) )) # UInt64 |-> (g))
  ** ((( &( "ph" ) )) # UInt64 |-> (ph))
  ** ((( &( "pk" ) )) # UInt64 |-> (pk))
  ** ((( &( "o" ) )) # UInt64 |-> (o))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (current))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def walk_entail_wit_1 : Prop :=
  (
forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (PreH1 : (i_pre ≠ factor_count)) (PreH2 : ((Zlength (pr_values)) = factor_count)) (PreH3 : ((Zlength (pe_values)) = factor_count)) (PreH4 : ((0 : Int) <= i_pre)) (PreH5 : (i_pre <= factor_count)) (PreH6 : (WalkGlobalBounds m x_value)) (PreH7 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH8 : ((0 : Int) < ord_pre)) (PreH9 : (ValidFactorTable m pr_values pe_values)) (PreH10 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH11 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)))) ,
  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (before))
|--
  “ ((Zlength (pr_values)) = factor_count) ” &&
  “ ((Zlength (pe_values)) = factor_count) ” &&
  “ ((0 : Int) <= i_pre) ” &&
  “ (i_pre < factor_count) ” &&
  “ (WalkGlobalBounds m x_value) ” &&
  “ (WalkMachineBounds m d_pre phi_pre ord_pre) ” &&
  “ ((0 : Int) < ord_pre) ” &&
  “ (ValidFactorTable m pr_values pe_values) ” &&
  “ (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre) ” &&
  “ (PrefixChoice pr_values pe_values x_value (i_pre + 1) d_pre phi_pre ord_pre) ” &&
  “ (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre))) ” &&
  “ (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) (d_pre))) ”
  &&  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (before))
) \/
(
forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (PreH1 : (i_pre ≠ factor_count)) (PreH2 : ((Zlength (pr_values)) = factor_count)) (PreH3 : ((Zlength (pe_values)) = factor_count)) (PreH4 : ((0 : Int) <= i_pre)) (PreH5 : (i_pre <= factor_count)) (PreH6 : (WalkGlobalBounds m x_value)) (PreH7 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH8 : ((0 : Int) < ord_pre)) (PreH9 : (ValidFactorTable m pr_values pe_values)) (PreH10 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH11 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)))) ,
  TT && emp 
|--
  “ (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) (d_pre))) ” &&
  “ (PrefixChoice pr_values pe_values x_value (i_pre + 1) d_pre phi_pre ord_pre) ”
  &&  emp
)

noncomputable def walk_entail_wit_1_split_goal_1 : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (PreH1 : (i_pre ≠ factor_count)) (PreH2 : ((Zlength (pr_values)) = factor_count)) (PreH3 : ((Zlength (pe_values)) = factor_count)) (PreH4 : ((0 : Int) <= i_pre)) (PreH5 : (i_pre <= factor_count)) (PreH6 : (WalkGlobalBounds m x_value)) (PreH7 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH8 : ((0 : Int) < ord_pre)) (PreH9 : (ValidFactorTable m pr_values pe_values)) (PreH10 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH11 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)))) ,
  (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) (d_pre)))

noncomputable def walk_entail_wit_1_split_goal_2 : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (PreH1 : (i_pre ≠ factor_count)) (PreH2 : ((Zlength (pr_values)) = factor_count)) (PreH3 : ((Zlength (pe_values)) = factor_count)) (PreH4 : ((0 : Int) <= i_pre)) (PreH5 : (i_pre <= factor_count)) (PreH6 : (WalkGlobalBounds m x_value)) (PreH7 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH8 : ((0 : Int) < ord_pre)) (PreH9 : (ValidFactorTable m pr_values pe_values)) (PreH10 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH11 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)))) ,
  (PrefixChoice pr_values pe_values x_value (i_pre + 1) d_pre phi_pre ord_pre)

noncomputable def walk_entail_wit_2 : Prop :=
  (
forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : ((0 : Int) <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (WalkGlobalBounds m x_value)) (PreH6 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH7 : ((0 : Int) < ord_pre)) (PreH8 : (ValidFactorTable m pr_values pe_values)) (PreH9 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH10 : (PrefixChoice pr_values pe_values x_value (i_pre + 1) d_pre phi_pre ord_pre)) (PreH11 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)))) (PreH12 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) (d_pre)))) ,
  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> ((before + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) (d_pre)))))
|--
  “ ((Zlength (pr_values)) = factor_count) ” &&
  “ ((Zlength (pe_values)) = factor_count) ” &&
  “ ((0 : Int) <= i_pre) ” &&
  “ (i_pre < factor_count) ” &&
  “ (WalkGlobalBounds m x_value) ” &&
  “ (WalkMachineBounds m d_pre phi_pre ord_pre) ” &&
  “ ((0 : Int) < ord_pre) ” &&
  “ (ValidFactorTable m pr_values pe_values) ” &&
  “ (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre) ” &&
  “ (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre))) ” &&
  “ (WalkPendingState pr_values pe_values m x_value i_pre d_pre before (before + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) (d_pre))) 1) ”
  &&  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> ((before + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) (d_pre)))))
) \/
(
forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : ((0 : Int) <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (WalkGlobalBounds m x_value)) (PreH6 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH7 : ((0 : Int) < ord_pre)) (PreH8 : (ValidFactorTable m pr_values pe_values)) (PreH9 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH10 : (PrefixChoice pr_values pe_values x_value (i_pre + 1) d_pre phi_pre ord_pre)) (PreH11 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)))) (PreH12 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) (d_pre)))) ,
  TT && emp 
|--
  “ (WalkPendingState pr_values pe_values m x_value i_pre d_pre before (before + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) (d_pre))) 1) ”
  &&  emp
)

noncomputable def walk_entail_wit_2_split_goal_1 : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : ((0 : Int) <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (WalkGlobalBounds m x_value)) (PreH6 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH7 : ((0 : Int) < ord_pre)) (PreH8 : (ValidFactorTable m pr_values pe_values)) (PreH9 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH10 : (PrefixChoice pr_values pe_values x_value (i_pre + 1) d_pre phi_pre ord_pre)) (PreH11 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)))) (PreH12 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) (d_pre)))) ,
  (WalkPendingState pr_values pe_values m x_value i_pre d_pre before (before + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) (d_pre))) 1)

noncomputable def walk_entail_wit_3 : Prop :=
  (
forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : ((0 : Int) <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (WalkGlobalBounds m x_value)) (PreH6 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH7 : ((0 : Int) < ord_pre)) (PreH8 : (ValidFactorTable m pr_values pe_values)) (PreH9 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH10 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)))) (PreH11 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before (before + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) (d_pre))) 1)) ,
  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> ((before + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) (d_pre)))))
|--
  EX current : Int,
  “ ((Zlength (pr_values)) = factor_count) ” &&
  “ ((Zlength (pe_values)) = factor_count) ” &&
  “ ((0 : Int) <= i_pre) ” &&
  “ (i_pre < factor_count) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= ((Znth i_pre pe_values (0 : Int)) + 1)) ” &&
  “ ((Znth (i_pre - (0 : Int)) pr_values (0 : Int)) = (Znth i_pre pr_values (0 : Int))) ” &&
  “ (WalkExponentState m (Znth (i_pre - (0 : Int)) pr_values (0 : Int)) 1 (Znth i_pre pe_values (0 : Int)) 1 1) ” &&
  “ (WalkGlobalBounds m x_value) ” &&
  “ (WalkMachineBounds m d_pre phi_pre ord_pre) ” &&
  “ ((0 : Int) < ord_pre) ” &&
  “ (ValidFactorTable m pr_values pe_values) ” &&
  “ (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre) ” &&
  “ (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current 1) ”
  &&  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (current))
) \/
(
forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : ((0 : Int) <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (WalkGlobalBounds m x_value)) (PreH6 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH7 : ((0 : Int) < ord_pre)) (PreH8 : (ValidFactorTable m pr_values pe_values)) (PreH9 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH10 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)))) (PreH11 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before (before + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) (d_pre))) 1)) ,
  TT && emp 
|--
  “ (WalkExponentState m (Znth (i_pre - (0 : Int)) pr_values (0 : Int)) 1 (Znth i_pre pe_values (0 : Int)) 1 1) ” &&
  “ ((Znth (i_pre - (0 : Int)) pr_values (0 : Int)) = (Znth i_pre pr_values (0 : Int))) ” &&
  “ (1 <= ((Znth i_pre pe_values (0 : Int)) + 1)) ”
  &&  emp
)

noncomputable def walk_entail_wit_3_split_goal_1 : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : ((0 : Int) <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (WalkGlobalBounds m x_value)) (PreH6 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH7 : ((0 : Int) < ord_pre)) (PreH8 : (ValidFactorTable m pr_values pe_values)) (PreH9 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH10 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)))) (PreH11 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before (before + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) (d_pre))) 1)) ,
  (WalkExponentState m (Znth (i_pre - (0 : Int)) pr_values (0 : Int)) 1 (Znth i_pre pe_values (0 : Int)) 1 1)

noncomputable def walk_entail_wit_3_split_goal_2 : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : ((0 : Int) <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (WalkGlobalBounds m x_value)) (PreH6 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH7 : ((0 : Int) < ord_pre)) (PreH8 : (ValidFactorTable m pr_values pe_values)) (PreH9 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH10 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)))) (PreH11 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before (before + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) (d_pre))) 1)) ,
  ((Znth (i_pre - (0 : Int)) pr_values (0 : Int)) = (Znth i_pre pr_values (0 : Int)))

noncomputable def walk_entail_wit_3_split_goal_3 : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : ((0 : Int) <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (WalkGlobalBounds m x_value)) (PreH6 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH7 : ((0 : Int) < ord_pre)) (PreH8 : (ValidFactorTable m pr_values pe_values)) (PreH9 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH10 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)))) (PreH11 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before (before + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) (d_pre))) 1)) ,
  (1 <= ((Znth i_pre pe_values (0 : Int)) + 1))

noncomputable def walk_entail_wit_4_1 : Prop :=
  (
forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current_2 : Int) (pk : Int) (ph : Int) (p : Int) (e : Int) (PreH1 : (e = 1)) (PreH2 : (e <= (Znth (i_pre - (0 : Int)) pe_values (0 : Int)))) (PreH3 : ((Zlength (pr_values)) = factor_count)) (PreH4 : ((Zlength (pe_values)) = factor_count)) (PreH5 : ((0 : Int) <= i_pre)) (PreH6 : (i_pre < factor_count)) (PreH7 : (1 <= e)) (PreH8 : (e <= ((Znth i_pre pe_values (0 : Int)) + 1))) (PreH9 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH10 : (WalkExponentState m p e (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH11 : (WalkGlobalBounds m x_value)) (PreH12 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH13 : ((0 : Int) < ord_pre)) (PreH14 : (ValidFactorTable m pr_values pe_values)) (PreH15 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH16 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current_2 e)) ,
  (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (current_2))
|--
  EX current : Int,
  “ ((Zlength (pr_values)) = factor_count) ” &&
  “ ((Zlength (pe_values)) = factor_count) ” &&
  “ ((0 : Int) <= i_pre) ” &&
  “ (i_pre < factor_count) ” &&
  “ (1 <= e) ” &&
  “ (e <= (Znth i_pre pe_values (0 : Int))) ” &&
  “ (p = (Znth i_pre pr_values (0 : Int))) ” &&
  “ (WalkExponentState m p (e + 1) (Znth i_pre pe_values (0 : Int)) (unsigned_last_nbits ((pk * p)) (64)) (unsigned_last_nbits ((p - 1)) (64))) ” &&
  “ (OrderInput (Z.rem x_value (unsigned_last_nbits ((pk * p)) (64))) (unsigned_last_nbits ((pk * p)) (64)) (unsigned_last_nbits ((p - 1)) (64))) ” &&
  “ (WalkGlobalBounds m x_value) ” &&
  “ (WalkMachineBounds m d_pre phi_pre ord_pre) ” &&
  “ ((0 : Int) < ord_pre) ” &&
  “ (ValidFactorTable m pr_values pe_values) ” &&
  “ (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre) ” &&
  “ (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e) ”
  &&  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (current))
) \/
(
forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current_2 : Int) (pk : Int) (ph : Int) (p : Int) (e : Int) (PreH1 : (e = 1)) (PreH2 : (e <= (Znth (i_pre - (0 : Int)) pe_values (0 : Int)))) (PreH3 : ((Zlength (pr_values)) = factor_count)) (PreH4 : ((Zlength (pe_values)) = factor_count)) (PreH5 : ((0 : Int) <= i_pre)) (PreH6 : (i_pre < factor_count)) (PreH7 : (1 <= e)) (PreH8 : (e <= ((Znth i_pre pe_values (0 : Int)) + 1))) (PreH9 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH10 : (WalkExponentState m p e (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH11 : (WalkGlobalBounds m x_value)) (PreH12 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH13 : ((0 : Int) < ord_pre)) (PreH14 : (ValidFactorTable m pr_values pe_values)) (PreH15 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH16 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current_2 e)) ,
  TT && emp 
|--
  “ (OrderInput (Z.rem x_value (unsigned_last_nbits ((pk * p)) (64))) (unsigned_last_nbits ((pk * p)) (64)) (unsigned_last_nbits ((p - 1)) (64))) ” &&
  “ (WalkExponentState m p (1 + 1) (Znth i_pre pe_values (0 : Int)) (unsigned_last_nbits ((pk * p)) (64)) (unsigned_last_nbits ((p - 1)) (64))) ” &&
  “ (1 <= (Znth i_pre pe_values (0 : Int))) ”
  &&  emp
)

noncomputable def walk_entail_wit_4_1_split_goal_1 : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current_2 : Int) (pk : Int) (ph : Int) (p : Int) (e : Int) (PreH1 : (e = 1)) (PreH2 : (e <= (Znth (i_pre - (0 : Int)) pe_values (0 : Int)))) (PreH3 : ((Zlength (pr_values)) = factor_count)) (PreH4 : ((Zlength (pe_values)) = factor_count)) (PreH5 : ((0 : Int) <= i_pre)) (PreH6 : (i_pre < factor_count)) (PreH7 : (1 <= e)) (PreH8 : (e <= ((Znth i_pre pe_values (0 : Int)) + 1))) (PreH9 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH10 : (WalkExponentState m p e (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH11 : (WalkGlobalBounds m x_value)) (PreH12 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH13 : ((0 : Int) < ord_pre)) (PreH14 : (ValidFactorTable m pr_values pe_values)) (PreH15 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH16 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current_2 e)) ,
  (OrderInput (Z.rem x_value (unsigned_last_nbits ((pk * p)) (64))) (unsigned_last_nbits ((pk * p)) (64)) (unsigned_last_nbits ((p - 1)) (64)))

noncomputable def walk_entail_wit_4_1_split_goal_2 : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current_2 : Int) (pk : Int) (ph : Int) (p : Int) (e : Int) (PreH1 : (e = 1)) (PreH2 : (e <= (Znth (i_pre - (0 : Int)) pe_values (0 : Int)))) (PreH3 : ((Zlength (pr_values)) = factor_count)) (PreH4 : ((Zlength (pe_values)) = factor_count)) (PreH5 : ((0 : Int) <= i_pre)) (PreH6 : (i_pre < factor_count)) (PreH7 : (1 <= e)) (PreH8 : (e <= ((Znth i_pre pe_values (0 : Int)) + 1))) (PreH9 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH10 : (WalkExponentState m p e (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH11 : (WalkGlobalBounds m x_value)) (PreH12 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH13 : ((0 : Int) < ord_pre)) (PreH14 : (ValidFactorTable m pr_values pe_values)) (PreH15 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH16 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current_2 e)) ,
  (WalkExponentState m p (1 + 1) (Znth i_pre pe_values (0 : Int)) (unsigned_last_nbits ((pk * p)) (64)) (unsigned_last_nbits ((p - 1)) (64)))

noncomputable def walk_entail_wit_4_1_split_goal_3 : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current_2 : Int) (pk : Int) (ph : Int) (p : Int) (e : Int) (PreH1 : (e = 1)) (PreH2 : (e <= (Znth (i_pre - (0 : Int)) pe_values (0 : Int)))) (PreH3 : ((Zlength (pr_values)) = factor_count)) (PreH4 : ((Zlength (pe_values)) = factor_count)) (PreH5 : ((0 : Int) <= i_pre)) (PreH6 : (i_pre < factor_count)) (PreH7 : (1 <= e)) (PreH8 : (e <= ((Znth i_pre pe_values (0 : Int)) + 1))) (PreH9 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH10 : (WalkExponentState m p e (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH11 : (WalkGlobalBounds m x_value)) (PreH12 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH13 : ((0 : Int) < ord_pre)) (PreH14 : (ValidFactorTable m pr_values pe_values)) (PreH15 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH16 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current_2 e)) ,
  (1 <= (Znth i_pre pe_values (0 : Int)))

noncomputable def walk_entail_wit_4_2 : Prop :=
  (
forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current_2 : Int) (pk : Int) (ph : Int) (p : Int) (e : Int) (PreH1 : (e ≠ 1)) (PreH2 : (e <= (Znth (i_pre - (0 : Int)) pe_values (0 : Int)))) (PreH3 : ((Zlength (pr_values)) = factor_count)) (PreH4 : ((Zlength (pe_values)) = factor_count)) (PreH5 : ((0 : Int) <= i_pre)) (PreH6 : (i_pre < factor_count)) (PreH7 : (1 <= e)) (PreH8 : (e <= ((Znth i_pre pe_values (0 : Int)) + 1))) (PreH9 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH10 : (WalkExponentState m p e (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH11 : (WalkGlobalBounds m x_value)) (PreH12 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH13 : ((0 : Int) < ord_pre)) (PreH14 : (ValidFactorTable m pr_values pe_values)) (PreH15 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH16 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current_2 e)) ,
  (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (current_2))
|--
  EX current : Int,
  “ ((Zlength (pr_values)) = factor_count) ” &&
  “ ((Zlength (pe_values)) = factor_count) ” &&
  “ ((0 : Int) <= i_pre) ” &&
  “ (i_pre < factor_count) ” &&
  “ (1 <= e) ” &&
  “ (e <= (Znth i_pre pe_values (0 : Int))) ” &&
  “ (p = (Znth i_pre pr_values (0 : Int))) ” &&
  “ (WalkExponentState m p (e + 1) (Znth i_pre pe_values (0 : Int)) (unsigned_last_nbits ((pk * p)) (64)) (unsigned_last_nbits ((ph * p)) (64))) ” &&
  “ (OrderInput (Z.rem x_value (unsigned_last_nbits ((pk * p)) (64))) (unsigned_last_nbits ((pk * p)) (64)) (unsigned_last_nbits ((ph * p)) (64))) ” &&
  “ (WalkGlobalBounds m x_value) ” &&
  “ (WalkMachineBounds m d_pre phi_pre ord_pre) ” &&
  “ ((0 : Int) < ord_pre) ” &&
  “ (ValidFactorTable m pr_values pe_values) ” &&
  “ (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre) ” &&
  “ (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e) ”
  &&  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (current))
) \/
(
forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current_2 : Int) (pk : Int) (ph : Int) (p : Int) (e : Int) (PreH1 : (e ≠ 1)) (PreH2 : (e <= (Znth (i_pre - (0 : Int)) pe_values (0 : Int)))) (PreH3 : ((Zlength (pr_values)) = factor_count)) (PreH4 : ((Zlength (pe_values)) = factor_count)) (PreH5 : ((0 : Int) <= i_pre)) (PreH6 : (i_pre < factor_count)) (PreH7 : (1 <= e)) (PreH8 : (e <= ((Znth i_pre pe_values (0 : Int)) + 1))) (PreH9 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH10 : (WalkExponentState m p e (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH11 : (WalkGlobalBounds m x_value)) (PreH12 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH13 : ((0 : Int) < ord_pre)) (PreH14 : (ValidFactorTable m pr_values pe_values)) (PreH15 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH16 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current_2 e)) ,
  TT && emp 
|--
  “ (OrderInput (Z.rem x_value (unsigned_last_nbits ((pk * p)) (64))) (unsigned_last_nbits ((pk * p)) (64)) (unsigned_last_nbits ((ph * p)) (64))) ” &&
  “ (WalkExponentState m p (e + 1) (Znth i_pre pe_values (0 : Int)) (unsigned_last_nbits ((pk * p)) (64)) (unsigned_last_nbits ((ph * p)) (64))) ” &&
  “ (e <= (Znth i_pre pe_values (0 : Int))) ”
  &&  emp
)

noncomputable def walk_entail_wit_4_2_split_goal_1 : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current_2 : Int) (pk : Int) (ph : Int) (p : Int) (e : Int) (PreH1 : (e ≠ 1)) (PreH2 : (e <= (Znth (i_pre - (0 : Int)) pe_values (0 : Int)))) (PreH3 : ((Zlength (pr_values)) = factor_count)) (PreH4 : ((Zlength (pe_values)) = factor_count)) (PreH5 : ((0 : Int) <= i_pre)) (PreH6 : (i_pre < factor_count)) (PreH7 : (1 <= e)) (PreH8 : (e <= ((Znth i_pre pe_values (0 : Int)) + 1))) (PreH9 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH10 : (WalkExponentState m p e (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH11 : (WalkGlobalBounds m x_value)) (PreH12 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH13 : ((0 : Int) < ord_pre)) (PreH14 : (ValidFactorTable m pr_values pe_values)) (PreH15 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH16 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current_2 e)) ,
  (OrderInput (Z.rem x_value (unsigned_last_nbits ((pk * p)) (64))) (unsigned_last_nbits ((pk * p)) (64)) (unsigned_last_nbits ((ph * p)) (64)))

noncomputable def walk_entail_wit_4_2_split_goal_2 : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current_2 : Int) (pk : Int) (ph : Int) (p : Int) (e : Int) (PreH1 : (e ≠ 1)) (PreH2 : (e <= (Znth (i_pre - (0 : Int)) pe_values (0 : Int)))) (PreH3 : ((Zlength (pr_values)) = factor_count)) (PreH4 : ((Zlength (pe_values)) = factor_count)) (PreH5 : ((0 : Int) <= i_pre)) (PreH6 : (i_pre < factor_count)) (PreH7 : (1 <= e)) (PreH8 : (e <= ((Znth i_pre pe_values (0 : Int)) + 1))) (PreH9 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH10 : (WalkExponentState m p e (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH11 : (WalkGlobalBounds m x_value)) (PreH12 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH13 : ((0 : Int) < ord_pre)) (PreH14 : (ValidFactorTable m pr_values pe_values)) (PreH15 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH16 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current_2 e)) ,
  (WalkExponentState m p (e + 1) (Znth i_pre pe_values (0 : Int)) (unsigned_last_nbits ((pk * p)) (64)) (unsigned_last_nbits ((ph * p)) (64)))

noncomputable def walk_entail_wit_4_2_split_goal_3 : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current_2 : Int) (pk : Int) (ph : Int) (p : Int) (e : Int) (PreH1 : (e ≠ 1)) (PreH2 : (e <= (Znth (i_pre - (0 : Int)) pe_values (0 : Int)))) (PreH3 : ((Zlength (pr_values)) = factor_count)) (PreH4 : ((Zlength (pe_values)) = factor_count)) (PreH5 : ((0 : Int) <= i_pre)) (PreH6 : (i_pre < factor_count)) (PreH7 : (1 <= e)) (PreH8 : (e <= ((Znth i_pre pe_values (0 : Int)) + 1))) (PreH9 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH10 : (WalkExponentState m p e (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH11 : (WalkGlobalBounds m x_value)) (PreH12 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH13 : ((0 : Int) < ord_pre)) (PreH14 : (ValidFactorTable m pr_values pe_values)) (PreH15 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH16 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current_2 e)) ,
  (e <= (Znth i_pre pe_values (0 : Int)))

noncomputable def walk_entail_wit_5 : Prop :=
  (
forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current_2 : Int) (e : Int) (p : Int) (ph : Int) (pk : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (Zgcd (ord_pre) (retval)))) (PreH2 : ((0 : Int) <= retval_2)) (PreH3 : (retval_2 <= (ord_pre + retval))) (PreH4 : (OrderResult (Z.rem x_value pk) pk retval)) (PreH5 : ((Zlength (pr_values)) = factor_count)) (PreH6 : ((Zlength (pe_values)) = factor_count)) (PreH7 : ((0 : Int) <= i_pre)) (PreH8 : (i_pre < factor_count)) (PreH9 : (1 <= e)) (PreH10 : (e <= (Znth i_pre pe_values (0 : Int)))) (PreH11 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH12 : (WalkExponentState m p (e + 1) (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH13 : (OrderInput (Z.rem x_value pk) pk ph)) (PreH14 : (WalkGlobalBounds m x_value)) (PreH15 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH16 : ((0 : Int) < ord_pre)) (PreH17 : (ValidFactorTable m pr_values pe_values)) (PreH18 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH19 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current_2 e)) ,
  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (current_2))
|--
  EX current : Int,
  “ ((Zlength (pr_values)) = factor_count) ” &&
  “ ((Zlength (pe_values)) = factor_count) ” &&
  “ ((0 : Int) <= i_pre) ” &&
  “ (i_pre < factor_count) ” &&
  “ (1 <= e) ” &&
  “ (e <= (Znth i_pre pe_values (0 : Int))) ” &&
  “ (p = (Znth i_pre pr_values (0 : Int))) ” &&
  “ ((0 : Int) < retval_2) ” &&
  “ (WalkGlobalBounds m x_value) ” &&
  “ (WalkMachineBounds m d_pre phi_pre ord_pre) ” &&
  “ ((0 : Int) < ord_pre) ” &&
  “ (ValidFactorTable m pr_values pe_values) ” &&
  “ (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre) ” &&
  “ (WalkExponentState m p (e + 1) (Znth i_pre pe_values (0 : Int)) pk ph) ” &&
  “ (WalkMachineBounds m (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre retval_2) * retval)) ” &&
  “ (PrimePowerTransition x_value d_pre phi_pre ord_pre p e pk ph retval retval_2 (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre retval_2) * retval)) ” &&
  “ (PrefixChoice pr_values pe_values x_value (i_pre + 1) (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre retval_2) * retval)) ” &&
  “ (WalkBudget m current (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) ((d_pre * pk)))) ” &&
  “ (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e) ”
  &&  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (current))
) \/
(
forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current_2 : Int) (e : Int) (p : Int) (ph : Int) (pk : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (Zgcd (ord_pre) (retval)))) (PreH2 : ((0 : Int) <= retval_2)) (PreH3 : (retval_2 <= (ord_pre + retval))) (PreH4 : (OrderResult (Z.rem x_value pk) pk retval)) (PreH5 : ((Zlength (pr_values)) = factor_count)) (PreH6 : ((Zlength (pe_values)) = factor_count)) (PreH7 : ((0 : Int) <= i_pre)) (PreH8 : (i_pre < factor_count)) (PreH9 : (1 <= e)) (PreH10 : (e <= (Znth i_pre pe_values (0 : Int)))) (PreH11 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH12 : (WalkExponentState m p (e + 1) (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH13 : (OrderInput (Z.rem x_value pk) pk ph)) (PreH14 : (WalkGlobalBounds m x_value)) (PreH15 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH16 : ((0 : Int) < ord_pre)) (PreH17 : (ValidFactorTable m pr_values pe_values)) (PreH18 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH19 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current_2 e)) ,
  TT && emp 
|--
  “ (WalkBudget m current_2 (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) ((d_pre * pk)))) ” &&
  “ (PrefixChoice pr_values pe_values x_value (i_pre + 1) (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre retval_2) * retval)) ” &&
  “ (PrimePowerTransition x_value d_pre phi_pre ord_pre p e pk ph retval retval_2 (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre retval_2) * retval)) ” &&
  “ (WalkMachineBounds m (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre retval_2) * retval)) ” &&
  “ ((0 : Int) < retval_2) ”
  &&  emp
)

noncomputable def walk_entail_wit_5_split_goal_1 : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current_2 : Int) (e : Int) (p : Int) (ph : Int) (pk : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (Zgcd (ord_pre) (retval)))) (PreH2 : ((0 : Int) <= retval_2)) (PreH3 : (retval_2 <= (ord_pre + retval))) (PreH4 : (OrderResult (Z.rem x_value pk) pk retval)) (PreH5 : ((Zlength (pr_values)) = factor_count)) (PreH6 : ((Zlength (pe_values)) = factor_count)) (PreH7 : ((0 : Int) <= i_pre)) (PreH8 : (i_pre < factor_count)) (PreH9 : (1 <= e)) (PreH10 : (e <= (Znth i_pre pe_values (0 : Int)))) (PreH11 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH12 : (WalkExponentState m p (e + 1) (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH13 : (OrderInput (Z.rem x_value pk) pk ph)) (PreH14 : (WalkGlobalBounds m x_value)) (PreH15 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH16 : ((0 : Int) < ord_pre)) (PreH17 : (ValidFactorTable m pr_values pe_values)) (PreH18 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH19 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current_2 e)) ,
  (WalkBudget m current_2 (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) ((d_pre * pk))))

noncomputable def walk_entail_wit_5_split_goal_2 : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current_2 : Int) (e : Int) (p : Int) (ph : Int) (pk : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (Zgcd (ord_pre) (retval)))) (PreH2 : ((0 : Int) <= retval_2)) (PreH3 : (retval_2 <= (ord_pre + retval))) (PreH4 : (OrderResult (Z.rem x_value pk) pk retval)) (PreH5 : ((Zlength (pr_values)) = factor_count)) (PreH6 : ((Zlength (pe_values)) = factor_count)) (PreH7 : ((0 : Int) <= i_pre)) (PreH8 : (i_pre < factor_count)) (PreH9 : (1 <= e)) (PreH10 : (e <= (Znth i_pre pe_values (0 : Int)))) (PreH11 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH12 : (WalkExponentState m p (e + 1) (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH13 : (OrderInput (Z.rem x_value pk) pk ph)) (PreH14 : (WalkGlobalBounds m x_value)) (PreH15 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH16 : ((0 : Int) < ord_pre)) (PreH17 : (ValidFactorTable m pr_values pe_values)) (PreH18 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH19 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current_2 e)) ,
  (PrefixChoice pr_values pe_values x_value (i_pre + 1) (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre retval_2) * retval))

noncomputable def walk_entail_wit_5_split_goal_3 : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current_2 : Int) (e : Int) (p : Int) (ph : Int) (pk : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (Zgcd (ord_pre) (retval)))) (PreH2 : ((0 : Int) <= retval_2)) (PreH3 : (retval_2 <= (ord_pre + retval))) (PreH4 : (OrderResult (Z.rem x_value pk) pk retval)) (PreH5 : ((Zlength (pr_values)) = factor_count)) (PreH6 : ((Zlength (pe_values)) = factor_count)) (PreH7 : ((0 : Int) <= i_pre)) (PreH8 : (i_pre < factor_count)) (PreH9 : (1 <= e)) (PreH10 : (e <= (Znth i_pre pe_values (0 : Int)))) (PreH11 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH12 : (WalkExponentState m p (e + 1) (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH13 : (OrderInput (Z.rem x_value pk) pk ph)) (PreH14 : (WalkGlobalBounds m x_value)) (PreH15 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH16 : ((0 : Int) < ord_pre)) (PreH17 : (ValidFactorTable m pr_values pe_values)) (PreH18 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH19 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current_2 e)) ,
  (PrimePowerTransition x_value d_pre phi_pre ord_pre p e pk ph retval retval_2 (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre retval_2) * retval))

noncomputable def walk_entail_wit_5_split_goal_4 : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current_2 : Int) (e : Int) (p : Int) (ph : Int) (pk : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (Zgcd (ord_pre) (retval)))) (PreH2 : ((0 : Int) <= retval_2)) (PreH3 : (retval_2 <= (ord_pre + retval))) (PreH4 : (OrderResult (Z.rem x_value pk) pk retval)) (PreH5 : ((Zlength (pr_values)) = factor_count)) (PreH6 : ((Zlength (pe_values)) = factor_count)) (PreH7 : ((0 : Int) <= i_pre)) (PreH8 : (i_pre < factor_count)) (PreH9 : (1 <= e)) (PreH10 : (e <= (Znth i_pre pe_values (0 : Int)))) (PreH11 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH12 : (WalkExponentState m p (e + 1) (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH13 : (OrderInput (Z.rem x_value pk) pk ph)) (PreH14 : (WalkGlobalBounds m x_value)) (PreH15 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH16 : ((0 : Int) < ord_pre)) (PreH17 : (ValidFactorTable m pr_values pe_values)) (PreH18 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH19 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current_2 e)) ,
  (WalkMachineBounds m (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre retval_2) * retval))

noncomputable def walk_entail_wit_5_split_goal_5 : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current_2 : Int) (e : Int) (p : Int) (ph : Int) (pk : Int) (retval : Int) (retval_2 : Int) (PreH1 : (retval_2 = (Zgcd (ord_pre) (retval)))) (PreH2 : ((0 : Int) <= retval_2)) (PreH3 : (retval_2 <= (ord_pre + retval))) (PreH4 : (OrderResult (Z.rem x_value pk) pk retval)) (PreH5 : ((Zlength (pr_values)) = factor_count)) (PreH6 : ((Zlength (pe_values)) = factor_count)) (PreH7 : ((0 : Int) <= i_pre)) (PreH8 : (i_pre < factor_count)) (PreH9 : (1 <= e)) (PreH10 : (e <= (Znth i_pre pe_values (0 : Int)))) (PreH11 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH12 : (WalkExponentState m p (e + 1) (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH13 : (OrderInput (Z.rem x_value pk) pk ph)) (PreH14 : (WalkGlobalBounds m x_value)) (PreH15 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH16 : ((0 : Int) < ord_pre)) (PreH17 : (ValidFactorTable m pr_values pe_values)) (PreH18 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH19 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current_2 e)) ,
  ((0 : Int) < retval_2)

noncomputable def walk_entail_wit_6 : Prop :=
  (
forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current_2 : Int) (e : Int) (p : Int) (g : Int) (ph : Int) (pk : Int) (o : Int) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : ((0 : Int) <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (1 <= e)) (PreH6 : (e <= (Znth i_pre pe_values (0 : Int)))) (PreH7 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH8 : ((0 : Int) < g)) (PreH9 : (WalkGlobalBounds m x_value)) (PreH10 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH11 : ((0 : Int) < ord_pre)) (PreH12 : (ValidFactorTable m pr_values pe_values)) (PreH13 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH14 : (WalkExponentState m p (e + 1) (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH15 : (WalkMachineBounds m (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH16 : (PrimePowerTransition x_value d_pre phi_pre ord_pre p e pk ph o g (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH17 : (PrefixChoice pr_values pe_values x_value (i_pre + 1) (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH18 : (WalkBudget m current_2 (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) ((d_pre * pk))))) (PreH19 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current_2 e)) ,
  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> ((current_2 + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) ((unsigned_last_nbits ((d_pre * pk)) (64)))))))
|--
  EX current : Int,
  “ ((Zlength (pr_values)) = factor_count) ” &&
  “ ((Zlength (pe_values)) = factor_count) ” &&
  “ ((0 : Int) <= i_pre) ” &&
  “ (i_pre < factor_count) ” &&
  “ (1 <= (unsigned_last_nbits ((e + 1)) (64))) ” &&
  “ ((unsigned_last_nbits ((e + 1)) (64)) <= ((Znth i_pre pe_values (0 : Int)) + 1)) ” &&
  “ (p = (Znth i_pre pr_values (0 : Int))) ” &&
  “ (WalkExponentState m p (unsigned_last_nbits ((e + 1)) (64)) (Znth i_pre pe_values (0 : Int)) pk ph) ” &&
  “ (WalkGlobalBounds m x_value) ” &&
  “ (WalkMachineBounds m d_pre phi_pre ord_pre) ” &&
  “ ((0 : Int) < ord_pre) ” &&
  “ (ValidFactorTable m pr_values pe_values) ” &&
  “ (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre) ” &&
  “ (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current (unsigned_last_nbits ((e + 1)) (64))) ”
  &&  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (current))
) \/
(
forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current_2 : Int) (e : Int) (p : Int) (g : Int) (ph : Int) (pk : Int) (o : Int) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : ((0 : Int) <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (1 <= e)) (PreH6 : (e <= (Znth i_pre pe_values (0 : Int)))) (PreH7 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH8 : ((0 : Int) < g)) (PreH9 : (WalkGlobalBounds m x_value)) (PreH10 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH11 : ((0 : Int) < ord_pre)) (PreH12 : (ValidFactorTable m pr_values pe_values)) (PreH13 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH14 : (WalkExponentState m p (e + 1) (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH15 : (WalkMachineBounds m (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH16 : (PrimePowerTransition x_value d_pre phi_pre ord_pre p e pk ph o g (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH17 : (PrefixChoice pr_values pe_values x_value (i_pre + 1) (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH18 : (WalkBudget m current_2 (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) ((d_pre * pk))))) (PreH19 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current_2 e)) ,
  TT && emp 
|--
  “ (WalkPendingState pr_values pe_values m x_value i_pre d_pre before (current_2 + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) ((unsigned_last_nbits ((d_pre * pk)) (64))))) (unsigned_last_nbits ((e + 1)) (64))) ” &&
  “ (WalkExponentState m p (unsigned_last_nbits ((e + 1)) (64)) (Znth i_pre pe_values (0 : Int)) pk ph) ” &&
  “ ((unsigned_last_nbits ((e + 1)) (64)) <= ((Znth i_pre pe_values (0 : Int)) + 1)) ” &&
  “ (1 <= (unsigned_last_nbits ((e + 1)) (64))) ”
  &&  emp
)

noncomputable def walk_entail_wit_6_split_goal_1 : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current_2 : Int) (e : Int) (p : Int) (g : Int) (ph : Int) (pk : Int) (o : Int) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : ((0 : Int) <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (1 <= e)) (PreH6 : (e <= (Znth i_pre pe_values (0 : Int)))) (PreH7 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH8 : ((0 : Int) < g)) (PreH9 : (WalkGlobalBounds m x_value)) (PreH10 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH11 : ((0 : Int) < ord_pre)) (PreH12 : (ValidFactorTable m pr_values pe_values)) (PreH13 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH14 : (WalkExponentState m p (e + 1) (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH15 : (WalkMachineBounds m (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH16 : (PrimePowerTransition x_value d_pre phi_pre ord_pre p e pk ph o g (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH17 : (PrefixChoice pr_values pe_values x_value (i_pre + 1) (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH18 : (WalkBudget m current_2 (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) ((d_pre * pk))))) (PreH19 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current_2 e)) ,
  (WalkPendingState pr_values pe_values m x_value i_pre d_pre before (current_2 + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) ((unsigned_last_nbits ((d_pre * pk)) (64))))) (unsigned_last_nbits ((e + 1)) (64)))

noncomputable def walk_entail_wit_6_split_goal_2 : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current_2 : Int) (e : Int) (p : Int) (g : Int) (ph : Int) (pk : Int) (o : Int) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : ((0 : Int) <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (1 <= e)) (PreH6 : (e <= (Znth i_pre pe_values (0 : Int)))) (PreH7 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH8 : ((0 : Int) < g)) (PreH9 : (WalkGlobalBounds m x_value)) (PreH10 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH11 : ((0 : Int) < ord_pre)) (PreH12 : (ValidFactorTable m pr_values pe_values)) (PreH13 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH14 : (WalkExponentState m p (e + 1) (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH15 : (WalkMachineBounds m (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH16 : (PrimePowerTransition x_value d_pre phi_pre ord_pre p e pk ph o g (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH17 : (PrefixChoice pr_values pe_values x_value (i_pre + 1) (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH18 : (WalkBudget m current_2 (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) ((d_pre * pk))))) (PreH19 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current_2 e)) ,
  (WalkExponentState m p (unsigned_last_nbits ((e + 1)) (64)) (Znth i_pre pe_values (0 : Int)) pk ph)

noncomputable def walk_entail_wit_6_split_goal_3 : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current_2 : Int) (e : Int) (p : Int) (g : Int) (ph : Int) (pk : Int) (o : Int) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : ((0 : Int) <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (1 <= e)) (PreH6 : (e <= (Znth i_pre pe_values (0 : Int)))) (PreH7 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH8 : ((0 : Int) < g)) (PreH9 : (WalkGlobalBounds m x_value)) (PreH10 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH11 : ((0 : Int) < ord_pre)) (PreH12 : (ValidFactorTable m pr_values pe_values)) (PreH13 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH14 : (WalkExponentState m p (e + 1) (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH15 : (WalkMachineBounds m (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH16 : (PrimePowerTransition x_value d_pre phi_pre ord_pre p e pk ph o g (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH17 : (PrefixChoice pr_values pe_values x_value (i_pre + 1) (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH18 : (WalkBudget m current_2 (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) ((d_pre * pk))))) (PreH19 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current_2 e)) ,
  ((unsigned_last_nbits ((e + 1)) (64)) <= ((Znth i_pre pe_values (0 : Int)) + 1))

noncomputable def walk_entail_wit_6_split_goal_4 : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current_2 : Int) (e : Int) (p : Int) (g : Int) (ph : Int) (pk : Int) (o : Int) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : ((0 : Int) <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (1 <= e)) (PreH6 : (e <= (Znth i_pre pe_values (0 : Int)))) (PreH7 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH8 : ((0 : Int) < g)) (PreH9 : (WalkGlobalBounds m x_value)) (PreH10 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH11 : ((0 : Int) < ord_pre)) (PreH12 : (ValidFactorTable m pr_values pe_values)) (PreH13 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH14 : (WalkExponentState m p (e + 1) (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH15 : (WalkMachineBounds m (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH16 : (PrimePowerTransition x_value d_pre phi_pre ord_pre p e pk ph o g (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH17 : (PrefixChoice pr_values pe_values x_value (i_pre + 1) (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH18 : (WalkBudget m current_2 (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) ((d_pre * pk))))) (PreH19 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current_2 e)) ,
  (1 <= (unsigned_last_nbits ((e + 1)) (64)))

noncomputable def walk_return_wit_1 : Prop :=
  (
forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (PreH1 : (d_pre > 1)) (PreH2 : (i_pre = factor_count)) (PreH3 : ((Zlength (pr_values)) = factor_count)) (PreH4 : ((Zlength (pe_values)) = factor_count)) (PreH5 : ((0 : Int) <= i_pre)) (PreH6 : (i_pre <= factor_count)) (PreH7 : (WalkGlobalBounds m x_value)) (PreH8 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH9 : ((0 : Int) < ord_pre)) (PreH10 : (ValidFactorTable m pr_values pe_values)) (PreH11 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH12 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)))) ,
  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> ((unsigned_last_nbits ((before + (Z.quot phi_pre ord_pre))) (64))))
|--
  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> ((before + (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)))))
) \/
(
forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (PreH1 : (d_pre > 1)) (PreH2 : (i_pre = factor_count)) (PreH3 : ((Zlength (pr_values)) = factor_count)) (PreH4 : ((Zlength (pe_values)) = factor_count)) (PreH5 : ((0 : Int) <= i_pre)) (PreH6 : (i_pre <= factor_count)) (PreH7 : (WalkGlobalBounds m x_value)) (PreH8 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH9 : ((0 : Int) < ord_pre)) (PreH10 : (ValidFactorTable m pr_values pe_values)) (PreH11 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH12 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)))) ,
  TT && emp 
|--
  “ ((unsigned_last_nbits ((before + (Z.quot phi_pre ord_pre))) (64)) = (before + (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)))) ”
  &&  emp
)

noncomputable def walk_return_wit_1_split_goal_1 : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (PreH1 : (d_pre > 1)) (PreH2 : (i_pre = factor_count)) (PreH3 : ((Zlength (pr_values)) = factor_count)) (PreH4 : ((Zlength (pe_values)) = factor_count)) (PreH5 : ((0 : Int) <= i_pre)) (PreH6 : (i_pre <= factor_count)) (PreH7 : (WalkGlobalBounds m x_value)) (PreH8 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH9 : ((0 : Int) < ord_pre)) (PreH10 : (ValidFactorTable m pr_values pe_values)) (PreH11 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH12 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)))) ,
  ((unsigned_last_nbits ((before + (Z.quot phi_pre ord_pre))) (64)) = (before + (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre))))

noncomputable def walk_return_wit_2 : Prop :=
  (
forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (PreH1 : (d_pre <= 1)) (PreH2 : (i_pre = factor_count)) (PreH3 : ((Zlength (pr_values)) = factor_count)) (PreH4 : ((Zlength (pe_values)) = factor_count)) (PreH5 : ((0 : Int) <= i_pre)) (PreH6 : (i_pre <= factor_count)) (PreH7 : (WalkGlobalBounds m x_value)) (PreH8 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH9 : ((0 : Int) < ord_pre)) (PreH10 : (ValidFactorTable m pr_values pe_values)) (PreH11 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH12 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)))) ,
  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (before))
|--
  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> ((before + (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)))))
) \/
(
forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (PreH1 : (d_pre <= 1)) (PreH2 : (i_pre = factor_count)) (PreH3 : ((Zlength (pr_values)) = factor_count)) (PreH4 : ((Zlength (pe_values)) = factor_count)) (PreH5 : ((0 : Int) <= i_pre)) (PreH6 : (i_pre <= factor_count)) (PreH7 : (WalkGlobalBounds m x_value)) (PreH8 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH9 : ((0 : Int) < ord_pre)) (PreH10 : (ValidFactorTable m pr_values pe_values)) (PreH11 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH12 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)))) ,
  TT && emp 
|--
  “ (before = (before + (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)))) ”
  &&  emp
)

noncomputable def walk_return_wit_2_split_goal_1 : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (PreH1 : (d_pre <= 1)) (PreH2 : (i_pre = factor_count)) (PreH3 : ((Zlength (pr_values)) = factor_count)) (PreH4 : ((Zlength (pe_values)) = factor_count)) (PreH5 : ((0 : Int) <= i_pre)) (PreH6 : (i_pre <= factor_count)) (PreH7 : (WalkGlobalBounds m x_value)) (PreH8 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH9 : ((0 : Int) < ord_pre)) (PreH10 : (ValidFactorTable m pr_values pe_values)) (PreH11 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH12 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)))) ,
  (before = (before + (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre))))

noncomputable def walk_return_wit_3 : Prop :=
  (
forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current : Int) (pk : Int) (ph : Int) (p : Int) (e : Int) (PreH1 : (e > (Znth (i_pre - (0 : Int)) pe_values (0 : Int)))) (PreH2 : ((Zlength (pr_values)) = factor_count)) (PreH3 : ((Zlength (pe_values)) = factor_count)) (PreH4 : ((0 : Int) <= i_pre)) (PreH5 : (i_pre < factor_count)) (PreH6 : (1 <= e)) (PreH7 : (e <= ((Znth i_pre pe_values (0 : Int)) + 1))) (PreH8 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH9 : (WalkExponentState m p e (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH10 : (WalkGlobalBounds m x_value)) (PreH11 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH12 : ((0 : Int) < ord_pre)) (PreH13 : (ValidFactorTable m pr_values pe_values)) (PreH14 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH15 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e)) ,
  (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (current))
|--
  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> ((before + (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)))))
) \/
(
forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current : Int) (pk : Int) (ph : Int) (p : Int) (e : Int) (PreH1 : (e > (Znth (i_pre - (0 : Int)) pe_values (0 : Int)))) (PreH2 : ((Zlength (pr_values)) = factor_count)) (PreH3 : ((Zlength (pe_values)) = factor_count)) (PreH4 : ((0 : Int) <= i_pre)) (PreH5 : (i_pre < factor_count)) (PreH6 : (1 <= e)) (PreH7 : (e <= ((Znth i_pre pe_values (0 : Int)) + 1))) (PreH8 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH9 : (WalkExponentState m p e (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH10 : (WalkGlobalBounds m x_value)) (PreH11 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH12 : ((0 : Int) < ord_pre)) (PreH13 : (ValidFactorTable m pr_values pe_values)) (PreH14 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH15 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e)) ,
  TT && emp 
|--
  “ (current = (before + (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)))) ”
  &&  emp
)

noncomputable def walk_return_wit_3_split_goal_1 : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current : Int) (pk : Int) (ph : Int) (p : Int) (e : Int) (PreH1 : (e > (Znth (i_pre - (0 : Int)) pe_values (0 : Int)))) (PreH2 : ((Zlength (pr_values)) = factor_count)) (PreH3 : ((Zlength (pe_values)) = factor_count)) (PreH4 : ((0 : Int) <= i_pre)) (PreH5 : (i_pre < factor_count)) (PreH6 : (1 <= e)) (PreH7 : (e <= ((Znth i_pre pe_values (0 : Int)) + 1))) (PreH8 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH9 : (WalkExponentState m p e (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH10 : (WalkGlobalBounds m x_value)) (PreH11 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH12 : ((0 : Int) < ord_pre)) (PreH13 : (ValidFactorTable m pr_values pe_values)) (PreH14 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH15 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e)) ,
  (current = (before + (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre))))

noncomputable def walk_partial_solve_wit_1_pure : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : ((0 : Int) <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (WalkGlobalBounds m x_value)) (PreH6 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH7 : ((0 : Int) < ord_pre)) (PreH8 : (ValidFactorTable m pr_values pe_values)) (PreH9 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH10 : (PrefixChoice pr_values pe_values x_value (i_pre + 1) d_pre phi_pre ord_pre)) (PreH11 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)))) (PreH12 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) (d_pre)))) ,
  ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "d" ) )) # UInt64 |-> (d_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord_pre))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (before))
|--
  “ ((Zlength (pr_values)) = factor_count) ” &&
  “ ((Zlength (pe_values)) = factor_count) ” &&
  “ ((0 : Int) <= (i_pre + 1)) ” &&
  “ ((i_pre + 1) <= factor_count) ” &&
  “ (WalkGlobalBounds m x_value) ” &&
  “ (WalkMachineBounds m d_pre phi_pre ord_pre) ” &&
  “ ((0 : Int) < ord_pre) ” &&
  “ (ValidFactorTable m pr_values pe_values) ” &&
  “ (PrefixChoice pr_values pe_values x_value (i_pre + 1) d_pre phi_pre ord_pre) ” &&
  “ (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) (d_pre))) ”

noncomputable def walk_partial_solve_wit_1_aux : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : ((0 : Int) <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (WalkGlobalBounds m x_value)) (PreH6 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH7 : ((0 : Int) < ord_pre)) (PreH8 : (ValidFactorTable m pr_values pe_values)) (PreH9 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH10 : (PrefixChoice pr_values pe_values x_value (i_pre + 1) d_pre phi_pre ord_pre)) (PreH11 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)))) (PreH12 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) (d_pre)))) ,
  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (before))
|--
  “ ((Zlength (pr_values)) = factor_count) ” &&
  “ ((Zlength (pe_values)) = factor_count) ” &&
  “ ((0 : Int) <= (i_pre + 1)) ” &&
  “ ((i_pre + 1) <= factor_count) ” &&
  “ (WalkGlobalBounds m x_value) ” &&
  “ (WalkMachineBounds m d_pre phi_pre ord_pre) ” &&
  “ ((0 : Int) < ord_pre) ” &&
  “ (ValidFactorTable m pr_values pe_values) ” &&
  “ (PrefixChoice pr_values pe_values x_value (i_pre + 1) d_pre phi_pre ord_pre) ” &&
  “ (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) (d_pre))) ” &&
  “ ((Zlength (pr_values)) = factor_count) ” &&
  “ ((Zlength (pe_values)) = factor_count) ” &&
  “ ((0 : Int) <= i_pre) ” &&
  “ (i_pre < factor_count) ” &&
  “ (WalkGlobalBounds m x_value) ” &&
  “ (WalkMachineBounds m d_pre phi_pre ord_pre) ” &&
  “ ((0 : Int) < ord_pre) ” &&
  “ (ValidFactorTable m pr_values pe_values) ” &&
  “ (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre) ” &&
  “ (PrefixChoice pr_values pe_values x_value (i_pre + 1) d_pre phi_pre ord_pre) ” &&
  “ (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre))) ” &&
  “ (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) (d_pre))) ”
  &&  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (before))

noncomputable def walk_partial_solve_wit_1 : Prop := walk_partial_solve_wit_1_pure -> walk_partial_solve_wit_1_aux

noncomputable def walk_partial_solve_wit_2 : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : ((0 : Int) <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (WalkGlobalBounds m x_value)) (PreH6 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH7 : ((0 : Int) < ord_pre)) (PreH8 : (ValidFactorTable m pr_values pe_values)) (PreH9 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH10 : (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre)))) (PreH11 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before (before + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) (d_pre))) 1)) ,
  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> ((before + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) (d_pre)))))
|--
  “ ((Zlength (pr_values)) = factor_count) ” &&
  “ ((Zlength (pe_values)) = factor_count) ” &&
  “ ((0 : Int) <= i_pre) ” &&
  “ (i_pre < factor_count) ” &&
  “ (WalkGlobalBounds m x_value) ” &&
  “ (WalkMachineBounds m d_pre phi_pre ord_pre) ” &&
  “ ((0 : Int) < ord_pre) ” &&
  “ (ValidFactorTable m pr_values pe_values) ” &&
  “ (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre) ” &&
  “ (WalkBudget m before (WalkSuffix (pr_values) (pe_values) (x_value) (i_pre) (d_pre))) ” &&
  “ (WalkPendingState pr_values pe_values m x_value i_pre d_pre before (before + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) (d_pre))) 1) ”
  &&  (((( &( "pr" ) ) + (i_pre * sizeof(UINT64)))) # UInt64 |-> ((Znth (i_pre - (0 : Int)) pr_values (0 : Int))))
  ** (uint64Array.missing_i ( &( "pr" ) ) i_pre (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> ((before + (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) (d_pre)))))

noncomputable def walk_partial_solve_wit_3 : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current : Int) (pk : Int) (ph : Int) (p : Int) (e : Int) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : ((0 : Int) <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (1 <= e)) (PreH6 : (e <= ((Znth i_pre pe_values (0 : Int)) + 1))) (PreH7 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH8 : (WalkExponentState m p e (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH9 : (WalkGlobalBounds m x_value)) (PreH10 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH11 : ((0 : Int) < ord_pre)) (PreH12 : (ValidFactorTable m pr_values pe_values)) (PreH13 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH14 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e)) ,
  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (current))
|--
  “ ((Zlength (pr_values)) = factor_count) ” &&
  “ ((Zlength (pe_values)) = factor_count) ” &&
  “ ((0 : Int) <= i_pre) ” &&
  “ (i_pre < factor_count) ” &&
  “ (1 <= e) ” &&
  “ (e <= ((Znth i_pre pe_values (0 : Int)) + 1)) ” &&
  “ (p = (Znth i_pre pr_values (0 : Int))) ” &&
  “ (WalkExponentState m p e (Znth i_pre pe_values (0 : Int)) pk ph) ” &&
  “ (WalkGlobalBounds m x_value) ” &&
  “ (WalkMachineBounds m d_pre phi_pre ord_pre) ” &&
  “ ((0 : Int) < ord_pre) ” &&
  “ (ValidFactorTable m pr_values pe_values) ” &&
  “ (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre) ” &&
  “ (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e) ”
  &&  (((( &( "pe" ) ) + (i_pre * sizeof(UINT64)))) # UInt64 |-> ((Znth (i_pre - (0 : Int)) pe_values (0 : Int))))
  ** (uint64Array.missing_i ( &( "pe" ) ) i_pre (0 : Int) factor_count pe_values)
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (current))

noncomputable def walk_partial_solve_wit_4_pure : Prop :=
  (
forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current : Int) (e : Int) (p : Int) (ph : Int) (pk : Int) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : ((0 : Int) <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (1 <= e)) (PreH6 : (e <= (Znth i_pre pe_values (0 : Int)))) (PreH7 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH8 : (WalkExponentState m p (e + 1) (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH9 : (OrderInput (Z.rem x_value pk) pk ph)) (PreH10 : (WalkGlobalBounds m x_value)) (PreH11 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH12 : ((0 : Int) < ord_pre)) (PreH13 : (ValidFactorTable m pr_values pe_values)) (PreH14 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH15 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e)) ,
  ((( &( "o" ) )) # UInt64 |->_)
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "d" ) )) # UInt64 |-> (d_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord_pre))
  ** ((( &( "e" ) )) # UInt64 |-> (e))
  ** ((( &( "p" ) )) # UInt64 |-> (p))
  ** ((( &( "ph" ) )) # UInt64 |-> (ph))
  ** ((( &( "pk" ) )) # UInt64 |-> (pk))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (current))
|--
  “ ((Z.rem x_value pk) = (Z.rem x_value pk)) ” &&
  “ (pk = pk) ” &&
  “ (ph = ph) ” &&
  “ (OrderInput (Z.rem x_value pk) pk ph) ” &&
  “ (pk <= 100000000000000) ”
) \/
(
forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current : Int) (e : Int) (p : Int) (ph : Int) (pk : Int) (PreH1 : (current <= 18446744073709551615)) (PreH2 : (x_value <= 18446744073709551615)) (PreH3 : (pk <= 18446744073709551615)) (PreH4 : (ph <= 18446744073709551615)) (PreH5 : (p <= 18446744073709551615)) (PreH6 : (e <= 18446744073709551615)) (PreH7 : (ord_pre <= 18446744073709551615)) (PreH8 : (phi_pre <= 18446744073709551615)) (PreH9 : (d_pre <= 18446744073709551615)) (PreH10 : (current >= (0 : Int))) (PreH11 : (x_value >= (0 : Int))) (PreH12 : (pk >= (0 : Int))) (PreH13 : (ph >= (0 : Int))) (PreH14 : (p >= (0 : Int))) (PreH15 : (e >= (0 : Int))) (PreH16 : (ord_pre >= (0 : Int))) (PreH17 : (phi_pre >= (0 : Int))) (PreH18 : (d_pre >= (0 : Int))) (PreH19 : (factor_count <= INT_MAX)) (PreH20 : (i_pre <= INT_MAX)) (PreH21 : (factor_count >= INT_MIN)) (PreH22 : (i_pre >= INT_MIN)) (PreH23 : ((Zlength (pr_values)) = factor_count)) (PreH24 : ((Zlength (pe_values)) = factor_count)) (PreH25 : ((0 : Int) <= i_pre)) (PreH26 : (i_pre < factor_count)) (PreH27 : (1 <= e)) (PreH28 : (e <= (Znth i_pre pe_values (0 : Int)))) (PreH29 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH30 : (WalkExponentState m p (e + 1) (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH31 : (OrderInput (Z.rem x_value pk) pk ph)) (PreH32 : (WalkGlobalBounds m x_value)) (PreH33 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH34 : ((0 : Int) < ord_pre)) (PreH35 : (ValidFactorTable m pr_values pe_values)) (PreH36 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH37 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e)) ,
  ((( &( "o" ) )) # UInt64 |->_)
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "d" ) )) # UInt64 |-> (d_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord_pre))
  ** ((( &( "e" ) )) # UInt64 |-> (e))
  ** ((( &( "p" ) )) # UInt64 |-> (p))
  ** ((( &( "ph" ) )) # UInt64 |-> (ph))
  ** ((( &( "pk" ) )) # UInt64 |-> (pk))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (current))
|--
  “ (pk <= 100000000000000) ”
)

noncomputable def walk_partial_solve_wit_4_pure_split_goal_1 : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current : Int) (e : Int) (p : Int) (ph : Int) (pk : Int) (PreH1 : (current <= 18446744073709551615)) (PreH2 : (x_value <= 18446744073709551615)) (PreH3 : (pk <= 18446744073709551615)) (PreH4 : (ph <= 18446744073709551615)) (PreH5 : (p <= 18446744073709551615)) (PreH6 : (e <= 18446744073709551615)) (PreH7 : (ord_pre <= 18446744073709551615)) (PreH8 : (phi_pre <= 18446744073709551615)) (PreH9 : (d_pre <= 18446744073709551615)) (PreH10 : (current >= (0 : Int))) (PreH11 : (x_value >= (0 : Int))) (PreH12 : (pk >= (0 : Int))) (PreH13 : (ph >= (0 : Int))) (PreH14 : (p >= (0 : Int))) (PreH15 : (e >= (0 : Int))) (PreH16 : (ord_pre >= (0 : Int))) (PreH17 : (phi_pre >= (0 : Int))) (PreH18 : (d_pre >= (0 : Int))) (PreH19 : (factor_count <= INT_MAX)) (PreH20 : (i_pre <= INT_MAX)) (PreH21 : (factor_count >= INT_MIN)) (PreH22 : (i_pre >= INT_MIN)) (PreH23 : ((Zlength (pr_values)) = factor_count)) (PreH24 : ((Zlength (pe_values)) = factor_count)) (PreH25 : ((0 : Int) <= i_pre)) (PreH26 : (i_pre < factor_count)) (PreH27 : (1 <= e)) (PreH28 : (e <= (Znth i_pre pe_values (0 : Int)))) (PreH29 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH30 : (WalkExponentState m p (e + 1) (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH31 : (OrderInput (Z.rem x_value pk) pk ph)) (PreH32 : (WalkGlobalBounds m x_value)) (PreH33 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH34 : ((0 : Int) < ord_pre)) (PreH35 : (ValidFactorTable m pr_values pe_values)) (PreH36 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH37 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e)) ,
  ((( &( "o" ) )) # UInt64 |->_)
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "d" ) )) # UInt64 |-> (d_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord_pre))
  ** ((( &( "e" ) )) # UInt64 |-> (e))
  ** ((( &( "p" ) )) # UInt64 |-> (p))
  ** ((( &( "ph" ) )) # UInt64 |-> (ph))
  ** ((( &( "pk" ) )) # UInt64 |-> (pk))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (current))
|--
  “ (pk <= 100000000000000) ”

noncomputable def walk_partial_solve_wit_4_aux : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current : Int) (e : Int) (p : Int) (ph : Int) (pk : Int) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : ((0 : Int) <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (1 <= e)) (PreH6 : (e <= (Znth i_pre pe_values (0 : Int)))) (PreH7 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH8 : (WalkExponentState m p (e + 1) (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH9 : (OrderInput (Z.rem x_value pk) pk ph)) (PreH10 : (WalkGlobalBounds m x_value)) (PreH11 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH12 : ((0 : Int) < ord_pre)) (PreH13 : (ValidFactorTable m pr_values pe_values)) (PreH14 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH15 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e)) ,
  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (current))
|--
  “ ((Z.rem x_value pk) = (Z.rem x_value pk)) ” &&
  “ (pk = pk) ” &&
  “ (ph = ph) ” &&
  “ (OrderInput (Z.rem x_value pk) pk ph) ” &&
  “ (pk <= 100000000000000) ” &&
  “ ((Zlength (pr_values)) = factor_count) ” &&
  “ ((Zlength (pe_values)) = factor_count) ” &&
  “ ((0 : Int) <= i_pre) ” &&
  “ (i_pre < factor_count) ” &&
  “ (1 <= e) ” &&
  “ (e <= (Znth i_pre pe_values (0 : Int))) ” &&
  “ (p = (Znth i_pre pr_values (0 : Int))) ” &&
  “ (WalkExponentState m p (e + 1) (Znth i_pre pe_values (0 : Int)) pk ph) ” &&
  “ (OrderInput (Z.rem x_value pk) pk ph) ” &&
  “ (WalkGlobalBounds m x_value) ” &&
  “ (WalkMachineBounds m d_pre phi_pre ord_pre) ” &&
  “ ((0 : Int) < ord_pre) ” &&
  “ (ValidFactorTable m pr_values pe_values) ” &&
  “ (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre) ” &&
  “ (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e) ”
  &&  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (current))

noncomputable def walk_partial_solve_wit_4 : Prop := walk_partial_solve_wit_4_pure -> walk_partial_solve_wit_4_aux

noncomputable def walk_partial_solve_wit_5_pure : Prop :=
  (
forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current : Int) (e : Int) (p : Int) (ph : Int) (pk : Int) (retval : Int) (PreH1 : (OrderResult (Z.rem x_value pk) pk retval)) (PreH2 : ((Zlength (pr_values)) = factor_count)) (PreH3 : ((Zlength (pe_values)) = factor_count)) (PreH4 : ((0 : Int) <= i_pre)) (PreH5 : (i_pre < factor_count)) (PreH6 : (1 <= e)) (PreH7 : (e <= (Znth i_pre pe_values (0 : Int)))) (PreH8 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH9 : (WalkExponentState m p (e + 1) (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH10 : (OrderInput (Z.rem x_value pk) pk ph)) (PreH11 : (WalkGlobalBounds m x_value)) (PreH12 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH13 : ((0 : Int) < ord_pre)) (PreH14 : (ValidFactorTable m pr_values pe_values)) (PreH15 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH16 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e)) ,
  ((( &( "g" ) )) # UInt64 |->_)
  ** ((( &( "o" ) )) # UInt64 |-> (retval))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "d" ) )) # UInt64 |-> (d_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord_pre))
  ** ((( &( "e" ) )) # UInt64 |-> (e))
  ** ((( &( "p" ) )) # UInt64 |-> (p))
  ** ((( &( "ph" ) )) # UInt64 |-> (ph))
  ** ((( &( "pk" ) )) # UInt64 |-> (pk))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (current))
|--
  “ (ord_pre = ord_pre) ” &&
  “ (retval = retval) ” &&
  “ ((0 : Int) <= ord_pre) ” &&
  “ (retval <= 100000000000000) ” &&
  “ ((0 : Int) <= retval) ” &&
  “ (ord_pre <= 100000000000000) ”
) \/
(
forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current : Int) (e : Int) (p : Int) (ph : Int) (pk : Int) (retval : Int) (PreH1 : (current <= 18446744073709551615)) (PreH2 : (x_value <= 18446744073709551615)) (PreH3 : (pk <= 18446744073709551615)) (PreH4 : (ph <= 18446744073709551615)) (PreH5 : (p <= 18446744073709551615)) (PreH6 : (e <= 18446744073709551615)) (PreH7 : (ord_pre <= 18446744073709551615)) (PreH8 : (phi_pre <= 18446744073709551615)) (PreH9 : (d_pre <= 18446744073709551615)) (PreH10 : (retval <= 18446744073709551615)) (PreH11 : (current >= (0 : Int))) (PreH12 : (x_value >= (0 : Int))) (PreH13 : (pk >= (0 : Int))) (PreH14 : (ph >= (0 : Int))) (PreH15 : (p >= (0 : Int))) (PreH16 : (e >= (0 : Int))) (PreH17 : (ord_pre >= (0 : Int))) (PreH18 : (phi_pre >= (0 : Int))) (PreH19 : (d_pre >= (0 : Int))) (PreH20 : (retval >= (0 : Int))) (PreH21 : (factor_count <= INT_MAX)) (PreH22 : (i_pre <= INT_MAX)) (PreH23 : (factor_count >= INT_MIN)) (PreH24 : (i_pre >= INT_MIN)) (PreH25 : (OrderResult (Z.rem x_value pk) pk retval)) (PreH26 : ((Zlength (pr_values)) = factor_count)) (PreH27 : ((Zlength (pe_values)) = factor_count)) (PreH28 : ((0 : Int) <= i_pre)) (PreH29 : (i_pre < factor_count)) (PreH30 : (1 <= e)) (PreH31 : (e <= (Znth i_pre pe_values (0 : Int)))) (PreH32 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH33 : (WalkExponentState m p (e + 1) (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH34 : (OrderInput (Z.rem x_value pk) pk ph)) (PreH35 : (WalkGlobalBounds m x_value)) (PreH36 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH37 : ((0 : Int) < ord_pre)) (PreH38 : (ValidFactorTable m pr_values pe_values)) (PreH39 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH40 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e)) ,
  ((( &( "g" ) )) # UInt64 |->_)
  ** ((( &( "o" ) )) # UInt64 |-> (retval))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "d" ) )) # UInt64 |-> (d_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord_pre))
  ** ((( &( "e" ) )) # UInt64 |-> (e))
  ** ((( &( "p" ) )) # UInt64 |-> (p))
  ** ((( &( "ph" ) )) # UInt64 |-> (ph))
  ** ((( &( "pk" ) )) # UInt64 |-> (pk))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (current))
|--
  “ (ord_pre <= 100000000000000) ” &&
  “ (retval <= 100000000000000) ”
)

noncomputable def walk_partial_solve_wit_5_pure_split_goal_1 : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current : Int) (e : Int) (p : Int) (ph : Int) (pk : Int) (retval : Int) (PreH1 : (current <= 18446744073709551615)) (PreH2 : (x_value <= 18446744073709551615)) (PreH3 : (pk <= 18446744073709551615)) (PreH4 : (ph <= 18446744073709551615)) (PreH5 : (p <= 18446744073709551615)) (PreH6 : (e <= 18446744073709551615)) (PreH7 : (ord_pre <= 18446744073709551615)) (PreH8 : (phi_pre <= 18446744073709551615)) (PreH9 : (d_pre <= 18446744073709551615)) (PreH10 : (retval <= 18446744073709551615)) (PreH11 : (current >= (0 : Int))) (PreH12 : (x_value >= (0 : Int))) (PreH13 : (pk >= (0 : Int))) (PreH14 : (ph >= (0 : Int))) (PreH15 : (p >= (0 : Int))) (PreH16 : (e >= (0 : Int))) (PreH17 : (ord_pre >= (0 : Int))) (PreH18 : (phi_pre >= (0 : Int))) (PreH19 : (d_pre >= (0 : Int))) (PreH20 : (retval >= (0 : Int))) (PreH21 : (factor_count <= INT_MAX)) (PreH22 : (i_pre <= INT_MAX)) (PreH23 : (factor_count >= INT_MIN)) (PreH24 : (i_pre >= INT_MIN)) (PreH25 : (OrderResult (Z.rem x_value pk) pk retval)) (PreH26 : ((Zlength (pr_values)) = factor_count)) (PreH27 : ((Zlength (pe_values)) = factor_count)) (PreH28 : ((0 : Int) <= i_pre)) (PreH29 : (i_pre < factor_count)) (PreH30 : (1 <= e)) (PreH31 : (e <= (Znth i_pre pe_values (0 : Int)))) (PreH32 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH33 : (WalkExponentState m p (e + 1) (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH34 : (OrderInput (Z.rem x_value pk) pk ph)) (PreH35 : (WalkGlobalBounds m x_value)) (PreH36 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH37 : ((0 : Int) < ord_pre)) (PreH38 : (ValidFactorTable m pr_values pe_values)) (PreH39 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH40 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e)) ,
  ((( &( "g" ) )) # UInt64 |->_)
  ** ((( &( "o" ) )) # UInt64 |-> (retval))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "d" ) )) # UInt64 |-> (d_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord_pre))
  ** ((( &( "e" ) )) # UInt64 |-> (e))
  ** ((( &( "p" ) )) # UInt64 |-> (p))
  ** ((( &( "ph" ) )) # UInt64 |-> (ph))
  ** ((( &( "pk" ) )) # UInt64 |-> (pk))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (current))
|--
  “ (ord_pre <= 100000000000000) ”

noncomputable def walk_partial_solve_wit_5_pure_split_goal_2 : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current : Int) (e : Int) (p : Int) (ph : Int) (pk : Int) (retval : Int) (PreH1 : (current <= 18446744073709551615)) (PreH2 : (x_value <= 18446744073709551615)) (PreH3 : (pk <= 18446744073709551615)) (PreH4 : (ph <= 18446744073709551615)) (PreH5 : (p <= 18446744073709551615)) (PreH6 : (e <= 18446744073709551615)) (PreH7 : (ord_pre <= 18446744073709551615)) (PreH8 : (phi_pre <= 18446744073709551615)) (PreH9 : (d_pre <= 18446744073709551615)) (PreH10 : (retval <= 18446744073709551615)) (PreH11 : (current >= (0 : Int))) (PreH12 : (x_value >= (0 : Int))) (PreH13 : (pk >= (0 : Int))) (PreH14 : (ph >= (0 : Int))) (PreH15 : (p >= (0 : Int))) (PreH16 : (e >= (0 : Int))) (PreH17 : (ord_pre >= (0 : Int))) (PreH18 : (phi_pre >= (0 : Int))) (PreH19 : (d_pre >= (0 : Int))) (PreH20 : (retval >= (0 : Int))) (PreH21 : (factor_count <= INT_MAX)) (PreH22 : (i_pre <= INT_MAX)) (PreH23 : (factor_count >= INT_MIN)) (PreH24 : (i_pre >= INT_MIN)) (PreH25 : (OrderResult (Z.rem x_value pk) pk retval)) (PreH26 : ((Zlength (pr_values)) = factor_count)) (PreH27 : ((Zlength (pe_values)) = factor_count)) (PreH28 : ((0 : Int) <= i_pre)) (PreH29 : (i_pre < factor_count)) (PreH30 : (1 <= e)) (PreH31 : (e <= (Znth i_pre pe_values (0 : Int)))) (PreH32 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH33 : (WalkExponentState m p (e + 1) (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH34 : (OrderInput (Z.rem x_value pk) pk ph)) (PreH35 : (WalkGlobalBounds m x_value)) (PreH36 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH37 : ((0 : Int) < ord_pre)) (PreH38 : (ValidFactorTable m pr_values pe_values)) (PreH39 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH40 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e)) ,
  ((( &( "g" ) )) # UInt64 |->_)
  ** ((( &( "o" ) )) # UInt64 |-> (retval))
  ** ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "d" ) )) # UInt64 |-> (d_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord_pre))
  ** ((( &( "e" ) )) # UInt64 |-> (e))
  ** ((( &( "p" ) )) # UInt64 |-> (p))
  ** ((( &( "ph" ) )) # UInt64 |-> (ph))
  ** ((( &( "pk" ) )) # UInt64 |-> (pk))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (current))
|--
  “ (retval <= 100000000000000) ”

noncomputable def walk_partial_solve_wit_5_aux : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current : Int) (e : Int) (p : Int) (ph : Int) (pk : Int) (retval : Int) (PreH1 : (OrderResult (Z.rem x_value pk) pk retval)) (PreH2 : ((Zlength (pr_values)) = factor_count)) (PreH3 : ((Zlength (pe_values)) = factor_count)) (PreH4 : ((0 : Int) <= i_pre)) (PreH5 : (i_pre < factor_count)) (PreH6 : (1 <= e)) (PreH7 : (e <= (Znth i_pre pe_values (0 : Int)))) (PreH8 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH9 : (WalkExponentState m p (e + 1) (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH10 : (OrderInput (Z.rem x_value pk) pk ph)) (PreH11 : (WalkGlobalBounds m x_value)) (PreH12 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH13 : ((0 : Int) < ord_pre)) (PreH14 : (ValidFactorTable m pr_values pe_values)) (PreH15 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH16 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e)) ,
  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (current))
|--
  “ (ord_pre = ord_pre) ” &&
  “ (retval = retval) ” &&
  “ ((0 : Int) <= ord_pre) ” &&
  “ (retval <= 100000000000000) ” &&
  “ ((0 : Int) <= retval) ” &&
  “ (ord_pre <= 100000000000000) ” &&
  “ (OrderResult (Z.rem x_value pk) pk retval) ” &&
  “ ((Zlength (pr_values)) = factor_count) ” &&
  “ ((Zlength (pe_values)) = factor_count) ” &&
  “ ((0 : Int) <= i_pre) ” &&
  “ (i_pre < factor_count) ” &&
  “ (1 <= e) ” &&
  “ (e <= (Znth i_pre pe_values (0 : Int))) ” &&
  “ (p = (Znth i_pre pr_values (0 : Int))) ” &&
  “ (WalkExponentState m p (e + 1) (Znth i_pre pe_values (0 : Int)) pk ph) ” &&
  “ (OrderInput (Z.rem x_value pk) pk ph) ” &&
  “ (WalkGlobalBounds m x_value) ” &&
  “ (WalkMachineBounds m d_pre phi_pre ord_pre) ” &&
  “ ((0 : Int) < ord_pre) ” &&
  “ (ValidFactorTable m pr_values pe_values) ” &&
  “ (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre) ” &&
  “ (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e) ”
  &&  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (current))

noncomputable def walk_partial_solve_wit_5 : Prop := walk_partial_solve_wit_5_pure -> walk_partial_solve_wit_5_aux

noncomputable def walk_partial_solve_wit_6_pure : Prop :=
  (
forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current : Int) (e : Int) (p : Int) (g : Int) (ph : Int) (pk : Int) (o : Int) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : ((0 : Int) <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (1 <= e)) (PreH6 : (e <= (Znth i_pre pe_values (0 : Int)))) (PreH7 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH8 : ((0 : Int) < g)) (PreH9 : (WalkGlobalBounds m x_value)) (PreH10 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH11 : ((0 : Int) < ord_pre)) (PreH12 : (ValidFactorTable m pr_values pe_values)) (PreH13 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH14 : (WalkExponentState m p (e + 1) (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH15 : (WalkMachineBounds m (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH16 : (PrimePowerTransition x_value d_pre phi_pre ord_pre p e pk ph o g (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH17 : (PrefixChoice pr_values pe_values x_value (i_pre + 1) (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH18 : (WalkBudget m current (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) ((d_pre * pk))))) (PreH19 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e)) ,
  ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "d" ) )) # UInt64 |-> (d_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord_pre))
  ** ((( &( "e" ) )) # UInt64 |-> (e))
  ** ((( &( "p" ) )) # UInt64 |-> (p))
  ** ((( &( "g" ) )) # UInt64 |-> (g))
  ** ((( &( "ph" ) )) # UInt64 |-> (ph))
  ** ((( &( "pk" ) )) # UInt64 |-> (pk))
  ** ((( &( "o" ) )) # UInt64 |-> (o))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (current))
|--
  “ ((Zlength (pr_values)) = factor_count) ” &&
  “ ((Zlength (pe_values)) = factor_count) ” &&
  “ ((0 : Int) <= (i_pre + 1)) ” &&
  “ ((i_pre + 1) <= factor_count) ” &&
  “ (WalkGlobalBounds m x_value) ” &&
  “ (ValidFactorTable m pr_values pe_values) ” &&
  “ (WalkBudget m current (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) ((unsigned_last_nbits ((d_pre * pk)) (64))))) ” &&
  “ (PrefixChoice pr_values pe_values x_value (i_pre + 1) (unsigned_last_nbits ((d_pre * pk)) (64)) (unsigned_last_nbits ((phi_pre * ph)) (64)) (unsigned_last_nbits (((Z.quot ord_pre g) * o)) (64))) ” &&
  “ ((0 : Int) < (unsigned_last_nbits (((Z.quot ord_pre g) * o)) (64))) ” &&
  “ (WalkMachineBounds m (unsigned_last_nbits ((d_pre * pk)) (64)) (unsigned_last_nbits ((phi_pre * ph)) (64)) (unsigned_last_nbits (((Z.quot ord_pre g) * o)) (64))) ”
) \/
(
forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current : Int) (e : Int) (p : Int) (g : Int) (ph : Int) (pk : Int) (o : Int) (PreH1 : (current <= 18446744073709551615)) (PreH2 : (x_value <= 18446744073709551615)) (PreH3 : (o <= 18446744073709551615)) (PreH4 : (pk <= 18446744073709551615)) (PreH5 : (ph <= 18446744073709551615)) (PreH6 : (g <= 18446744073709551615)) (PreH7 : (p <= 18446744073709551615)) (PreH8 : (e <= 18446744073709551615)) (PreH9 : (ord_pre <= 18446744073709551615)) (PreH10 : (phi_pre <= 18446744073709551615)) (PreH11 : (d_pre <= 18446744073709551615)) (PreH12 : (current >= (0 : Int))) (PreH13 : (x_value >= (0 : Int))) (PreH14 : (o >= (0 : Int))) (PreH15 : (pk >= (0 : Int))) (PreH16 : (ph >= (0 : Int))) (PreH17 : (g >= (0 : Int))) (PreH18 : (p >= (0 : Int))) (PreH19 : (e >= (0 : Int))) (PreH20 : (ord_pre >= (0 : Int))) (PreH21 : (phi_pre >= (0 : Int))) (PreH22 : (d_pre >= (0 : Int))) (PreH23 : (factor_count <= INT_MAX)) (PreH24 : (i_pre <= INT_MAX)) (PreH25 : (factor_count >= INT_MIN)) (PreH26 : (i_pre >= INT_MIN)) (PreH27 : ((Zlength (pr_values)) = factor_count)) (PreH28 : ((Zlength (pe_values)) = factor_count)) (PreH29 : ((0 : Int) <= i_pre)) (PreH30 : (i_pre < factor_count)) (PreH31 : (1 <= e)) (PreH32 : (e <= (Znth i_pre pe_values (0 : Int)))) (PreH33 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH34 : ((0 : Int) < g)) (PreH35 : (WalkGlobalBounds m x_value)) (PreH36 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH37 : ((0 : Int) < ord_pre)) (PreH38 : (ValidFactorTable m pr_values pe_values)) (PreH39 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH40 : (WalkExponentState m p (e + 1) (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH41 : (WalkMachineBounds m (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH42 : (PrimePowerTransition x_value d_pre phi_pre ord_pre p e pk ph o g (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH43 : (PrefixChoice pr_values pe_values x_value (i_pre + 1) (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH44 : (WalkBudget m current (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) ((d_pre * pk))))) (PreH45 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e)) ,
  ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "d" ) )) # UInt64 |-> (d_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord_pre))
  ** ((( &( "e" ) )) # UInt64 |-> (e))
  ** ((( &( "p" ) )) # UInt64 |-> (p))
  ** ((( &( "g" ) )) # UInt64 |-> (g))
  ** ((( &( "ph" ) )) # UInt64 |-> (ph))
  ** ((( &( "pk" ) )) # UInt64 |-> (pk))
  ** ((( &( "o" ) )) # UInt64 |-> (o))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (current))
|--
  “ (WalkMachineBounds m (unsigned_last_nbits ((d_pre * pk)) (64)) (unsigned_last_nbits ((phi_pre * ph)) (64)) (unsigned_last_nbits (((Z.quot ord_pre g) * o)) (64))) ” &&
  “ ((0 : Int) < (unsigned_last_nbits (((Z.quot ord_pre g) * o)) (64))) ” &&
  “ (PrefixChoice pr_values pe_values x_value (i_pre + 1) (unsigned_last_nbits ((d_pre * pk)) (64)) (unsigned_last_nbits ((phi_pre * ph)) (64)) (unsigned_last_nbits (((Z.quot ord_pre g) * o)) (64))) ” &&
  “ (WalkBudget m current (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) ((unsigned_last_nbits ((d_pre * pk)) (64))))) ”
)

noncomputable def walk_partial_solve_wit_6_pure_split_goal_1 : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current : Int) (e : Int) (p : Int) (g : Int) (ph : Int) (pk : Int) (o : Int) (PreH1 : (current <= 18446744073709551615)) (PreH2 : (x_value <= 18446744073709551615)) (PreH3 : (o <= 18446744073709551615)) (PreH4 : (pk <= 18446744073709551615)) (PreH5 : (ph <= 18446744073709551615)) (PreH6 : (g <= 18446744073709551615)) (PreH7 : (p <= 18446744073709551615)) (PreH8 : (e <= 18446744073709551615)) (PreH9 : (ord_pre <= 18446744073709551615)) (PreH10 : (phi_pre <= 18446744073709551615)) (PreH11 : (d_pre <= 18446744073709551615)) (PreH12 : (current >= (0 : Int))) (PreH13 : (x_value >= (0 : Int))) (PreH14 : (o >= (0 : Int))) (PreH15 : (pk >= (0 : Int))) (PreH16 : (ph >= (0 : Int))) (PreH17 : (g >= (0 : Int))) (PreH18 : (p >= (0 : Int))) (PreH19 : (e >= (0 : Int))) (PreH20 : (ord_pre >= (0 : Int))) (PreH21 : (phi_pre >= (0 : Int))) (PreH22 : (d_pre >= (0 : Int))) (PreH23 : (factor_count <= INT_MAX)) (PreH24 : (i_pre <= INT_MAX)) (PreH25 : (factor_count >= INT_MIN)) (PreH26 : (i_pre >= INT_MIN)) (PreH27 : ((Zlength (pr_values)) = factor_count)) (PreH28 : ((Zlength (pe_values)) = factor_count)) (PreH29 : ((0 : Int) <= i_pre)) (PreH30 : (i_pre < factor_count)) (PreH31 : (1 <= e)) (PreH32 : (e <= (Znth i_pre pe_values (0 : Int)))) (PreH33 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH34 : ((0 : Int) < g)) (PreH35 : (WalkGlobalBounds m x_value)) (PreH36 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH37 : ((0 : Int) < ord_pre)) (PreH38 : (ValidFactorTable m pr_values pe_values)) (PreH39 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH40 : (WalkExponentState m p (e + 1) (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH41 : (WalkMachineBounds m (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH42 : (PrimePowerTransition x_value d_pre phi_pre ord_pre p e pk ph o g (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH43 : (PrefixChoice pr_values pe_values x_value (i_pre + 1) (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH44 : (WalkBudget m current (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) ((d_pre * pk))))) (PreH45 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e)) ,
  ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "d" ) )) # UInt64 |-> (d_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord_pre))
  ** ((( &( "e" ) )) # UInt64 |-> (e))
  ** ((( &( "p" ) )) # UInt64 |-> (p))
  ** ((( &( "g" ) )) # UInt64 |-> (g))
  ** ((( &( "ph" ) )) # UInt64 |-> (ph))
  ** ((( &( "pk" ) )) # UInt64 |-> (pk))
  ** ((( &( "o" ) )) # UInt64 |-> (o))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (current))
|--
  “ (WalkMachineBounds m (unsigned_last_nbits ((d_pre * pk)) (64)) (unsigned_last_nbits ((phi_pre * ph)) (64)) (unsigned_last_nbits (((Z.quot ord_pre g) * o)) (64))) ”

noncomputable def walk_partial_solve_wit_6_pure_split_goal_2 : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current : Int) (e : Int) (p : Int) (g : Int) (ph : Int) (pk : Int) (o : Int) (PreH1 : (current <= 18446744073709551615)) (PreH2 : (x_value <= 18446744073709551615)) (PreH3 : (o <= 18446744073709551615)) (PreH4 : (pk <= 18446744073709551615)) (PreH5 : (ph <= 18446744073709551615)) (PreH6 : (g <= 18446744073709551615)) (PreH7 : (p <= 18446744073709551615)) (PreH8 : (e <= 18446744073709551615)) (PreH9 : (ord_pre <= 18446744073709551615)) (PreH10 : (phi_pre <= 18446744073709551615)) (PreH11 : (d_pre <= 18446744073709551615)) (PreH12 : (current >= (0 : Int))) (PreH13 : (x_value >= (0 : Int))) (PreH14 : (o >= (0 : Int))) (PreH15 : (pk >= (0 : Int))) (PreH16 : (ph >= (0 : Int))) (PreH17 : (g >= (0 : Int))) (PreH18 : (p >= (0 : Int))) (PreH19 : (e >= (0 : Int))) (PreH20 : (ord_pre >= (0 : Int))) (PreH21 : (phi_pre >= (0 : Int))) (PreH22 : (d_pre >= (0 : Int))) (PreH23 : (factor_count <= INT_MAX)) (PreH24 : (i_pre <= INT_MAX)) (PreH25 : (factor_count >= INT_MIN)) (PreH26 : (i_pre >= INT_MIN)) (PreH27 : ((Zlength (pr_values)) = factor_count)) (PreH28 : ((Zlength (pe_values)) = factor_count)) (PreH29 : ((0 : Int) <= i_pre)) (PreH30 : (i_pre < factor_count)) (PreH31 : (1 <= e)) (PreH32 : (e <= (Znth i_pre pe_values (0 : Int)))) (PreH33 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH34 : ((0 : Int) < g)) (PreH35 : (WalkGlobalBounds m x_value)) (PreH36 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH37 : ((0 : Int) < ord_pre)) (PreH38 : (ValidFactorTable m pr_values pe_values)) (PreH39 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH40 : (WalkExponentState m p (e + 1) (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH41 : (WalkMachineBounds m (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH42 : (PrimePowerTransition x_value d_pre phi_pre ord_pre p e pk ph o g (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH43 : (PrefixChoice pr_values pe_values x_value (i_pre + 1) (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH44 : (WalkBudget m current (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) ((d_pre * pk))))) (PreH45 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e)) ,
  ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "d" ) )) # UInt64 |-> (d_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord_pre))
  ** ((( &( "e" ) )) # UInt64 |-> (e))
  ** ((( &( "p" ) )) # UInt64 |-> (p))
  ** ((( &( "g" ) )) # UInt64 |-> (g))
  ** ((( &( "ph" ) )) # UInt64 |-> (ph))
  ** ((( &( "pk" ) )) # UInt64 |-> (pk))
  ** ((( &( "o" ) )) # UInt64 |-> (o))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (current))
|--
  “ ((0 : Int) < (unsigned_last_nbits (((Z.quot ord_pre g) * o)) (64))) ”

noncomputable def walk_partial_solve_wit_6_pure_split_goal_3 : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current : Int) (e : Int) (p : Int) (g : Int) (ph : Int) (pk : Int) (o : Int) (PreH1 : (current <= 18446744073709551615)) (PreH2 : (x_value <= 18446744073709551615)) (PreH3 : (o <= 18446744073709551615)) (PreH4 : (pk <= 18446744073709551615)) (PreH5 : (ph <= 18446744073709551615)) (PreH6 : (g <= 18446744073709551615)) (PreH7 : (p <= 18446744073709551615)) (PreH8 : (e <= 18446744073709551615)) (PreH9 : (ord_pre <= 18446744073709551615)) (PreH10 : (phi_pre <= 18446744073709551615)) (PreH11 : (d_pre <= 18446744073709551615)) (PreH12 : (current >= (0 : Int))) (PreH13 : (x_value >= (0 : Int))) (PreH14 : (o >= (0 : Int))) (PreH15 : (pk >= (0 : Int))) (PreH16 : (ph >= (0 : Int))) (PreH17 : (g >= (0 : Int))) (PreH18 : (p >= (0 : Int))) (PreH19 : (e >= (0 : Int))) (PreH20 : (ord_pre >= (0 : Int))) (PreH21 : (phi_pre >= (0 : Int))) (PreH22 : (d_pre >= (0 : Int))) (PreH23 : (factor_count <= INT_MAX)) (PreH24 : (i_pre <= INT_MAX)) (PreH25 : (factor_count >= INT_MIN)) (PreH26 : (i_pre >= INT_MIN)) (PreH27 : ((Zlength (pr_values)) = factor_count)) (PreH28 : ((Zlength (pe_values)) = factor_count)) (PreH29 : ((0 : Int) <= i_pre)) (PreH30 : (i_pre < factor_count)) (PreH31 : (1 <= e)) (PreH32 : (e <= (Znth i_pre pe_values (0 : Int)))) (PreH33 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH34 : ((0 : Int) < g)) (PreH35 : (WalkGlobalBounds m x_value)) (PreH36 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH37 : ((0 : Int) < ord_pre)) (PreH38 : (ValidFactorTable m pr_values pe_values)) (PreH39 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH40 : (WalkExponentState m p (e + 1) (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH41 : (WalkMachineBounds m (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH42 : (PrimePowerTransition x_value d_pre phi_pre ord_pre p e pk ph o g (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH43 : (PrefixChoice pr_values pe_values x_value (i_pre + 1) (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH44 : (WalkBudget m current (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) ((d_pre * pk))))) (PreH45 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e)) ,
  ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "d" ) )) # UInt64 |-> (d_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord_pre))
  ** ((( &( "e" ) )) # UInt64 |-> (e))
  ** ((( &( "p" ) )) # UInt64 |-> (p))
  ** ((( &( "g" ) )) # UInt64 |-> (g))
  ** ((( &( "ph" ) )) # UInt64 |-> (ph))
  ** ((( &( "pk" ) )) # UInt64 |-> (pk))
  ** ((( &( "o" ) )) # UInt64 |-> (o))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (current))
|--
  “ (PrefixChoice pr_values pe_values x_value (i_pre + 1) (unsigned_last_nbits ((d_pre * pk)) (64)) (unsigned_last_nbits ((phi_pre * ph)) (64)) (unsigned_last_nbits (((Z.quot ord_pre g) * o)) (64))) ”

noncomputable def walk_partial_solve_wit_6_pure_split_goal_4 : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current : Int) (e : Int) (p : Int) (g : Int) (ph : Int) (pk : Int) (o : Int) (PreH1 : (current <= 18446744073709551615)) (PreH2 : (x_value <= 18446744073709551615)) (PreH3 : (o <= 18446744073709551615)) (PreH4 : (pk <= 18446744073709551615)) (PreH5 : (ph <= 18446744073709551615)) (PreH6 : (g <= 18446744073709551615)) (PreH7 : (p <= 18446744073709551615)) (PreH8 : (e <= 18446744073709551615)) (PreH9 : (ord_pre <= 18446744073709551615)) (PreH10 : (phi_pre <= 18446744073709551615)) (PreH11 : (d_pre <= 18446744073709551615)) (PreH12 : (current >= (0 : Int))) (PreH13 : (x_value >= (0 : Int))) (PreH14 : (o >= (0 : Int))) (PreH15 : (pk >= (0 : Int))) (PreH16 : (ph >= (0 : Int))) (PreH17 : (g >= (0 : Int))) (PreH18 : (p >= (0 : Int))) (PreH19 : (e >= (0 : Int))) (PreH20 : (ord_pre >= (0 : Int))) (PreH21 : (phi_pre >= (0 : Int))) (PreH22 : (d_pre >= (0 : Int))) (PreH23 : (factor_count <= INT_MAX)) (PreH24 : (i_pre <= INT_MAX)) (PreH25 : (factor_count >= INT_MIN)) (PreH26 : (i_pre >= INT_MIN)) (PreH27 : ((Zlength (pr_values)) = factor_count)) (PreH28 : ((Zlength (pe_values)) = factor_count)) (PreH29 : ((0 : Int) <= i_pre)) (PreH30 : (i_pre < factor_count)) (PreH31 : (1 <= e)) (PreH32 : (e <= (Znth i_pre pe_values (0 : Int)))) (PreH33 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH34 : ((0 : Int) < g)) (PreH35 : (WalkGlobalBounds m x_value)) (PreH36 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH37 : ((0 : Int) < ord_pre)) (PreH38 : (ValidFactorTable m pr_values pe_values)) (PreH39 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH40 : (WalkExponentState m p (e + 1) (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH41 : (WalkMachineBounds m (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH42 : (PrimePowerTransition x_value d_pre phi_pre ord_pre p e pk ph o g (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH43 : (PrefixChoice pr_values pe_values x_value (i_pre + 1) (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH44 : (WalkBudget m current (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) ((d_pre * pk))))) (PreH45 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e)) ,
  ((( &( "i" ) )) # Int |-> (i_pre))
  ** ((( &( "d" ) )) # UInt64 |-> (d_pre))
  ** ((( &( "phi" ) )) # UInt64 |-> (phi_pre))
  ** ((( &( "ord" ) )) # UInt64 |-> (ord_pre))
  ** ((( &( "e" ) )) # UInt64 |-> (e))
  ** ((( &( "p" ) )) # UInt64 |-> (p))
  ** ((( &( "g" ) )) # UInt64 |-> (g))
  ** ((( &( "ph" ) )) # UInt64 |-> (ph))
  ** ((( &( "pk" ) )) # UInt64 |-> (pk))
  ** ((( &( "o" ) )) # UInt64 |-> (o))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (current))
|--
  “ (WalkBudget m current (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) ((unsigned_last_nbits ((d_pre * pk)) (64))))) ”

noncomputable def walk_partial_solve_wit_6_aux : Prop :=
  forall (ord_pre : Int) (phi_pre : Int) (d_pre : Int) (i_pre : Int) (pe_values : (List Int)) (pr_values : (List Int)) (before : Int) (factor_count : Int) (x_value : Int) (m : Int) (current : Int) (e : Int) (p : Int) (g : Int) (ph : Int) (pk : Int) (o : Int) (PreH1 : ((Zlength (pr_values)) = factor_count)) (PreH2 : ((Zlength (pe_values)) = factor_count)) (PreH3 : ((0 : Int) <= i_pre)) (PreH4 : (i_pre < factor_count)) (PreH5 : (1 <= e)) (PreH6 : (e <= (Znth i_pre pe_values (0 : Int)))) (PreH7 : (p = (Znth i_pre pr_values (0 : Int)))) (PreH8 : ((0 : Int) < g)) (PreH9 : (WalkGlobalBounds m x_value)) (PreH10 : (WalkMachineBounds m d_pre phi_pre ord_pre)) (PreH11 : ((0 : Int) < ord_pre)) (PreH12 : (ValidFactorTable m pr_values pe_values)) (PreH13 : (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre)) (PreH14 : (WalkExponentState m p (e + 1) (Znth i_pre pe_values (0 : Int)) pk ph)) (PreH15 : (WalkMachineBounds m (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH16 : (PrimePowerTransition x_value d_pre phi_pre ord_pre p e pk ph o g (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH17 : (PrefixChoice pr_values pe_values x_value (i_pre + 1) (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o))) (PreH18 : (WalkBudget m current (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) ((d_pre * pk))))) (PreH19 : (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e)) ,
  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (current))
|--
  “ ((Zlength (pr_values)) = factor_count) ” &&
  “ ((Zlength (pe_values)) = factor_count) ” &&
  “ ((0 : Int) <= (i_pre + 1)) ” &&
  “ ((i_pre + 1) <= factor_count) ” &&
  “ (WalkGlobalBounds m x_value) ” &&
  “ (ValidFactorTable m pr_values pe_values) ” &&
  “ (WalkBudget m current (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) ((unsigned_last_nbits ((d_pre * pk)) (64))))) ” &&
  “ (PrefixChoice pr_values pe_values x_value (i_pre + 1) (unsigned_last_nbits ((d_pre * pk)) (64)) (unsigned_last_nbits ((phi_pre * ph)) (64)) (unsigned_last_nbits (((Z.quot ord_pre g) * o)) (64))) ” &&
  “ ((0 : Int) < (unsigned_last_nbits (((Z.quot ord_pre g) * o)) (64))) ” &&
  “ (WalkMachineBounds m (unsigned_last_nbits ((d_pre * pk)) (64)) (unsigned_last_nbits ((phi_pre * ph)) (64)) (unsigned_last_nbits (((Z.quot ord_pre g) * o)) (64))) ” &&
  “ ((Zlength (pr_values)) = factor_count) ” &&
  “ ((Zlength (pe_values)) = factor_count) ” &&
  “ ((0 : Int) <= i_pre) ” &&
  “ (i_pre < factor_count) ” &&
  “ (1 <= e) ” &&
  “ (e <= (Znth i_pre pe_values (0 : Int))) ” &&
  “ (p = (Znth i_pre pr_values (0 : Int))) ” &&
  “ ((0 : Int) < g) ” &&
  “ (WalkGlobalBounds m x_value) ” &&
  “ (WalkMachineBounds m d_pre phi_pre ord_pre) ” &&
  “ ((0 : Int) < ord_pre) ” &&
  “ (ValidFactorTable m pr_values pe_values) ” &&
  “ (PrefixChoice pr_values pe_values x_value i_pre d_pre phi_pre ord_pre) ” &&
  “ (WalkExponentState m p (e + 1) (Znth i_pre pe_values (0 : Int)) pk ph) ” &&
  “ (WalkMachineBounds m (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o)) ” &&
  “ (PrimePowerTransition x_value d_pre phi_pre ord_pre p e pk ph o g (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o)) ” &&
  “ (PrefixChoice pr_values pe_values x_value (i_pre + 1) (d_pre * pk) (phi_pre * ph) ((Z.quot ord_pre g) * o)) ” &&
  “ (WalkBudget m current (WalkSuffix (pr_values) (pe_values) (x_value) ((i_pre + 1)) ((d_pre * pk)))) ” &&
  “ (WalkPendingState pr_values pe_values m x_value i_pre d_pre before current e) ”
  &&  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_value))
  ** ((( &( "total_" ) )) # UInt64 |-> (current))

noncomputable def walk_partial_solve_wit_6 : Prop := walk_partial_solve_wit_6_pure -> walk_partial_solve_wit_6_aux

noncomputable def solver_safety_wit_1 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre)) ,
  ((( &( "t" ) )) # UInt64 |-> (m_pre))
  ** ((( &( "m" ) )) # UInt64 |-> (m_pre))
  ** ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** (uint64Array.undef_full ( &( "pr" ) ) 64)
  ** (uint64Array.undef_full ( &( "pe" ) ) 64)
  ** ((( &( "nf" ) )) # Int |->_)
  ** ((( &( "x_" ) )) # UInt64 |->_)
  ** ((( &( "total_" ) )) # UInt64 |->_)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_2 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre)) ,
  ((( &( "p" ) )) # UInt64 |->_)
  ** ((( &( "t" ) )) # UInt64 |-> (m_pre))
  ** ((( &( "m" ) )) # UInt64 |-> (m_pre))
  ** ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** (uint64Array.undef_full ( &( "pr" ) ) 64)
  ** (uint64Array.undef_full ( &( "pe" ) ) 64)
  ** ((( &( "nf" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "x_" ) )) # UInt64 |->_)
  ** ((( &( "total_" ) )) # UInt64 |->_)
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def solver_safety_wit_3 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (remainder : Int) (pe_values : (List Int)) (pr_values : (List Int)) (factor_count : Int) (p : Int) (PreH1 : ((p * p) <= remainder)) (PreH2 : (2 <= m_pre)) (PreH3 : (m_pre <= 100000000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre < m_pre)) (PreH6 : (Pre m_pre x_pre)) (PreH7 : (2 <= p)) (PreH8 : (p <= 10000001)) (PreH9 : ((0 : Int) <= factor_count)) (PreH10 : (factor_count < 64)) (PreH11 : ((Zlength (pr_values)) = factor_count)) (PreH12 : ((Zlength (pe_values)) = factor_count)) (PreH13 : ((0 : Int) < remainder)) (PreH14 : (remainder <= m_pre)) (PreH15 : (FactorMachineTrialState m_pre p remainder pr_values pe_values)) ,
  ((( &( "m" ) )) # UInt64 |-> (m_pre))
  ** ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "p" ) )) # UInt64 |-> (p))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "t" ) )) # UInt64 |-> (remainder))
  ** ((( &( "x_" ) )) # UInt64 |->_)
  ** ((( &( "total_" ) )) # UInt64 |->_)
|--
  “ (p ≠ (0 : Int)) ”

noncomputable def solver_safety_wit_4 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (remainder : Int) (pe_values : (List Int)) (pr_values : (List Int)) (factor_count : Int) (p : Int) (PreH1 : ((p * p) <= remainder)) (PreH2 : (2 <= m_pre)) (PreH3 : (m_pre <= 100000000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre < m_pre)) (PreH6 : (Pre m_pre x_pre)) (PreH7 : (2 <= p)) (PreH8 : (p <= 10000001)) (PreH9 : ((0 : Int) <= factor_count)) (PreH10 : (factor_count < 64)) (PreH11 : ((Zlength (pr_values)) = factor_count)) (PreH12 : ((Zlength (pe_values)) = factor_count)) (PreH13 : ((0 : Int) < remainder)) (PreH14 : (remainder <= m_pre)) (PreH15 : (FactorMachineTrialState m_pre p remainder pr_values pe_values)) ,
  ((( &( "m" ) )) # UInt64 |-> (m_pre))
  ** ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "p" ) )) # UInt64 |-> (p))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "t" ) )) # UInt64 |-> (remainder))
  ** ((( &( "x_" ) )) # UInt64 |->_)
  ** ((( &( "total_" ) )) # UInt64 |->_)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_5 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (remainder : Int) (pe_values : (List Int)) (pr_values : (List Int)) (factor_count : Int) (p : Int) (PreH1 : ((Z.rem remainder p) = (0 : Int))) (PreH2 : ((p * p) <= remainder)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100000000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre < m_pre)) (PreH7 : (Pre m_pre x_pre)) (PreH8 : (2 <= p)) (PreH9 : (p <= 10000001)) (PreH10 : ((0 : Int) <= factor_count)) (PreH11 : (factor_count < 64)) (PreH12 : ((Zlength (pr_values)) = factor_count)) (PreH13 : ((Zlength (pe_values)) = factor_count)) (PreH14 : ((0 : Int) < remainder)) (PreH15 : (remainder <= m_pre)) (PreH16 : (FactorMachineTrialState m_pre p remainder pr_values pe_values)) ,
  (uint64Array.seg ( &( "pr" ) ) (0 : Int) (factor_count + 1) (pr_values ++ (p :: (@List.nil Int))))
  ** (uint64Array.undef_seg ( &( "pr" ) ) (factor_count + 1) 64)
  ** ((( &( "m" ) )) # UInt64 |-> (m_pre))
  ** ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "p" ) )) # UInt64 |-> (p))
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "t" ) )) # UInt64 |-> (remainder))
  ** ((( &( "x_" ) )) # UInt64 |->_)
  ** ((( &( "total_" ) )) # UInt64 |->_)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_6 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (original_remainder : Int) (remainder : Int) (exponent : Int) (pe_values : (List Int)) (pr_values : (List Int)) (factor_count : Int) (p : Int) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre)) (PreH6 : (2 <= p)) (PreH7 : (p <= 10000000)) (PreH8 : ((0 : Int) <= factor_count)) (PreH9 : (factor_count < 64)) (PreH10 : ((Zlength (pr_values)) = factor_count)) (PreH11 : ((Zlength (pe_values)) = factor_count)) (PreH12 : ((0 : Int) <= exponent)) (PreH13 : (exponent <= 47)) (PreH14 : (FactorMachineAtPrime m_pre p original_remainder remainder exponent pr_values pe_values)) ,
  ((( &( "m" ) )) # UInt64 |-> (m_pre))
  ** ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "p" ) )) # UInt64 |-> (p))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.seg ( &( "pr" ) ) factor_count (factor_count + 1) (p :: (@List.nil Int)))
  ** (uint64Array.undef_seg ( &( "pr" ) ) (factor_count + 1) 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.seg ( &( "pe" ) ) factor_count (factor_count + 1) (exponent :: (@List.nil Int)))
  ** (uint64Array.undef_seg ( &( "pe" ) ) (factor_count + 1) 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "t" ) )) # UInt64 |-> (remainder))
  ** ((( &( "x_" ) )) # UInt64 |->_)
  ** ((( &( "total_" ) )) # UInt64 |->_)
|--
  “ (p ≠ (0 : Int)) ”

noncomputable def solver_safety_wit_7 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (original_remainder : Int) (remainder : Int) (exponent : Int) (pe_values : (List Int)) (pr_values : (List Int)) (factor_count : Int) (p : Int) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre)) (PreH6 : (2 <= p)) (PreH7 : (p <= 10000000)) (PreH8 : ((0 : Int) <= factor_count)) (PreH9 : (factor_count < 64)) (PreH10 : ((Zlength (pr_values)) = factor_count)) (PreH11 : ((Zlength (pe_values)) = factor_count)) (PreH12 : ((0 : Int) <= exponent)) (PreH13 : (exponent <= 47)) (PreH14 : (FactorMachineAtPrime m_pre p original_remainder remainder exponent pr_values pe_values)) ,
  ((( &( "m" ) )) # UInt64 |-> (m_pre))
  ** ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "p" ) )) # UInt64 |-> (p))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.seg ( &( "pr" ) ) factor_count (factor_count + 1) (p :: (@List.nil Int)))
  ** (uint64Array.undef_seg ( &( "pr" ) ) (factor_count + 1) 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.seg ( &( "pe" ) ) factor_count (factor_count + 1) (exponent :: (@List.nil Int)))
  ** (uint64Array.undef_seg ( &( "pe" ) ) (factor_count + 1) 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "t" ) )) # UInt64 |-> (remainder))
  ** ((( &( "x_" ) )) # UInt64 |->_)
  ** ((( &( "total_" ) )) # UInt64 |->_)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_8 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (original_remainder : Int) (remainder : Int) (exponent : Int) (pe_values : (List Int)) (pr_values : (List Int)) (factor_count : Int) (p : Int) (PreH1 : ((Z.rem remainder p) = (0 : Int))) (PreH2 : (2 <= m_pre)) (PreH3 : (m_pre <= 100000000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre < m_pre)) (PreH6 : (Pre m_pre x_pre)) (PreH7 : (2 <= p)) (PreH8 : (p <= 10000000)) (PreH9 : ((0 : Int) <= factor_count)) (PreH10 : (factor_count < 64)) (PreH11 : ((Zlength (pr_values)) = factor_count)) (PreH12 : ((Zlength (pe_values)) = factor_count)) (PreH13 : ((0 : Int) <= exponent)) (PreH14 : (exponent <= 47)) (PreH15 : (FactorMachineAtPrime m_pre p original_remainder remainder exponent pr_values pe_values)) ,
  ((( &( "m" ) )) # UInt64 |-> (m_pre))
  ** ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "p" ) )) # UInt64 |-> (p))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.seg ( &( "pr" ) ) factor_count (factor_count + 1) (p :: (@List.nil Int)))
  ** (uint64Array.undef_seg ( &( "pr" ) ) (factor_count + 1) 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.seg ( &( "pe" ) ) factor_count (factor_count + 1) (exponent :: (@List.nil Int)))
  ** (uint64Array.undef_seg ( &( "pe" ) ) (factor_count + 1) 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "t" ) )) # UInt64 |-> (remainder))
  ** ((( &( "x_" ) )) # UInt64 |->_)
  ** ((( &( "total_" ) )) # UInt64 |->_)
|--
  “ (p ≠ (0 : Int)) ”

noncomputable def solver_safety_wit_9 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (original_remainder : Int) (remainder : Int) (exponent : Int) (pe_values : (List Int)) (pr_values : (List Int)) (factor_count : Int) (p : Int) (PreH1 : ((Z.rem remainder p) = (0 : Int))) (PreH2 : (2 <= m_pre)) (PreH3 : (m_pre <= 100000000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre < m_pre)) (PreH6 : (Pre m_pre x_pre)) (PreH7 : (2 <= p)) (PreH8 : (p <= 10000000)) (PreH9 : ((0 : Int) <= factor_count)) (PreH10 : (factor_count < 64)) (PreH11 : ((Zlength (pr_values)) = factor_count)) (PreH12 : ((Zlength (pe_values)) = factor_count)) (PreH13 : ((0 : Int) <= exponent)) (PreH14 : (exponent <= 47)) (PreH15 : (FactorMachineAtPrime m_pre p original_remainder remainder exponent pr_values pe_values)) ,
  (uint64Array.seg ( &( "pe" ) ) factor_count (factor_count + 1) (exponent :: (@List.nil Int)))
  ** ((( &( "m" ) )) # UInt64 |-> (m_pre))
  ** ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "p" ) )) # UInt64 |-> (p))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.seg ( &( "pr" ) ) factor_count (factor_count + 1) (p :: (@List.nil Int)))
  ** (uint64Array.undef_seg ( &( "pr" ) ) (factor_count + 1) 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) (factor_count + 1) 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "t" ) )) # UInt64 |-> ((Z.quot remainder p)))
  ** ((( &( "x_" ) )) # UInt64 |->_)
  ** ((( &( "total_" ) )) # UInt64 |->_)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_10 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (original_remainder : Int) (remainder : Int) (exponent : Int) (pe_values : (List Int)) (pr_values : (List Int)) (factor_count : Int) (p : Int) (PreH1 : ((Z.rem remainder p) ≠ (0 : Int))) (PreH2 : (2 <= m_pre)) (PreH3 : (m_pre <= 100000000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre < m_pre)) (PreH6 : (Pre m_pre x_pre)) (PreH7 : (2 <= p)) (PreH8 : (p <= 10000000)) (PreH9 : ((0 : Int) <= factor_count)) (PreH10 : (factor_count < 64)) (PreH11 : ((Zlength (pr_values)) = factor_count)) (PreH12 : ((Zlength (pe_values)) = factor_count)) (PreH13 : ((0 : Int) <= exponent)) (PreH14 : (exponent <= 47)) (PreH15 : (FactorMachineAtPrime m_pre p original_remainder remainder exponent pr_values pe_values)) ,
  ((( &( "m" ) )) # UInt64 |-> (m_pre))
  ** ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "p" ) )) # UInt64 |-> (p))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.seg ( &( "pr" ) ) factor_count (factor_count + 1) (p :: (@List.nil Int)))
  ** (uint64Array.undef_seg ( &( "pr" ) ) (factor_count + 1) 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.seg ( &( "pe" ) ) factor_count (factor_count + 1) (exponent :: (@List.nil Int)))
  ** (uint64Array.undef_seg ( &( "pe" ) ) (factor_count + 1) 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "t" ) )) # UInt64 |-> (remainder))
  ** ((( &( "x_" ) )) # UInt64 |->_)
  ** ((( &( "total_" ) )) # UInt64 |->_)
|--
  “ ((factor_count + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (factor_count + 1)) ”

noncomputable def solver_safety_wit_11 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (remainder : Int) (pe_values : (List Int)) (pr_values : (List Int)) (factor_count : Int) (p : Int) (PreH1 : ((p * p) > remainder)) (PreH2 : (2 <= m_pre)) (PreH3 : (m_pre <= 100000000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre < m_pre)) (PreH6 : (Pre m_pre x_pre)) (PreH7 : (2 <= p)) (PreH8 : (p <= 10000001)) (PreH9 : ((0 : Int) <= factor_count)) (PreH10 : (factor_count < 64)) (PreH11 : ((Zlength (pr_values)) = factor_count)) (PreH12 : ((Zlength (pe_values)) = factor_count)) (PreH13 : ((0 : Int) < remainder)) (PreH14 : (remainder <= m_pre)) (PreH15 : (FactorMachineTrialState m_pre p remainder pr_values pe_values)) ,
  ((( &( "m" ) )) # UInt64 |-> (m_pre))
  ** ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "t" ) )) # UInt64 |-> (remainder))
  ** ((( &( "x_" ) )) # UInt64 |->_)
  ** ((( &( "total_" ) )) # UInt64 |->_)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_12 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (remainder : Int) (pe_values : (List Int)) (pr_values : (List Int)) (factor_count : Int) (p : Int) (PreH1 : (remainder > 1)) (PreH2 : ((p * p) > remainder)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100000000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre < m_pre)) (PreH7 : (Pre m_pre x_pre)) (PreH8 : (2 <= p)) (PreH9 : (p <= 10000001)) (PreH10 : ((0 : Int) <= factor_count)) (PreH11 : (factor_count < 64)) (PreH12 : ((Zlength (pr_values)) = factor_count)) (PreH13 : ((Zlength (pe_values)) = factor_count)) (PreH14 : ((0 : Int) < remainder)) (PreH15 : (remainder <= m_pre)) (PreH16 : (FactorMachineTrialState m_pre p remainder pr_values pe_values)) ,
  (uint64Array.seg ( &( "pr" ) ) (0 : Int) (factor_count + 1) (pr_values ++ (remainder :: (@List.nil Int))))
  ** (uint64Array.undef_seg ( &( "pr" ) ) (factor_count + 1) 64)
  ** ((( &( "m" ) )) # UInt64 |-> (m_pre))
  ** ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "t" ) )) # UInt64 |-> (remainder))
  ** ((( &( "x_" ) )) # UInt64 |->_)
  ** ((( &( "total_" ) )) # UInt64 |->_)
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_13 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (remainder : Int) (pe_values : (List Int)) (pr_values : (List Int)) (factor_count : Int) (p : Int) (PreH1 : (remainder > 1)) (PreH2 : ((p * p) > remainder)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100000000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre < m_pre)) (PreH7 : (Pre m_pre x_pre)) (PreH8 : (2 <= p)) (PreH9 : (p <= 10000001)) (PreH10 : ((0 : Int) <= factor_count)) (PreH11 : (factor_count < 64)) (PreH12 : ((Zlength (pr_values)) = factor_count)) (PreH13 : ((Zlength (pe_values)) = factor_count)) (PreH14 : ((0 : Int) < remainder)) (PreH15 : (remainder <= m_pre)) (PreH16 : (FactorMachineTrialState m_pre p remainder pr_values pe_values)) ,
  (uint64Array.seg ( &( "pe" ) ) (0 : Int) (factor_count + 1) (pe_values ++ (1 :: (@List.nil Int))))
  ** (uint64Array.undef_seg ( &( "pe" ) ) (factor_count + 1) 64)
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) (factor_count + 1) (pr_values ++ (remainder :: (@List.nil Int))))
  ** (uint64Array.undef_seg ( &( "pr" ) ) (factor_count + 1) 64)
  ** ((( &( "m" ) )) # UInt64 |-> (m_pre))
  ** ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "t" ) )) # UInt64 |-> (remainder))
  ** ((( &( "x_" ) )) # UInt64 |->_)
  ** ((( &( "total_" ) )) # UInt64 |->_)
|--
  “ ((factor_count + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (factor_count + 1)) ”

noncomputable def solver_safety_wit_14 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (factor_count : Int) (remainder : Int) (pr_values : (List Int)) (pe_values : (List Int)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre)) (PreH6 : ((0 : Int) <= factor_count)) (PreH7 : (factor_count <= 64)) (PreH8 : ((Zlength (pr_values)) = factor_count)) (PreH9 : ((Zlength (pe_values)) = factor_count)) (PreH10 : (ValidFactorTable m_pre pr_values pe_values)) (PreH11 : (PrefixChoice pr_values pe_values x_pre (0 : Int) 1 1 1)) (PreH12 : ((0 : Int) <= (WalkSuffix (pr_values) (pe_values) (x_pre) ((0 : Int)) (1)))) (PreH13 : ((WalkSuffix (pr_values) (pe_values) (x_pre) ((0 : Int)) (1)) <= m_pre)) ,
  ((( &( "m" ) )) # UInt64 |-> (m_pre))
  ** ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "t" ) )) # UInt64 |-> (remainder))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "total_" ) )) # UInt64 |->_)
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_15 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (factor_count : Int) (remainder : Int) (pr_values : (List Int)) (pe_values : (List Int)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre)) (PreH6 : ((0 : Int) <= factor_count)) (PreH7 : (factor_count <= 64)) (PreH8 : ((Zlength (pr_values)) = factor_count)) (PreH9 : ((Zlength (pe_values)) = factor_count)) (PreH10 : (ValidFactorTable m_pre pr_values pe_values)) (PreH11 : (PrefixChoice pr_values pe_values x_pre (0 : Int) 1 1 1)) (PreH12 : ((0 : Int) <= (WalkSuffix (pr_values) (pe_values) (x_pre) ((0 : Int)) (1)))) (PreH13 : ((WalkSuffix (pr_values) (pe_values) (x_pre) ((0 : Int)) (1)) <= m_pre)) ,
  ((( &( "m" ) )) # UInt64 |-> (m_pre))
  ** ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "t" ) )) # UInt64 |-> (remainder))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "total_" ) )) # UInt64 |-> ((0 : Int)))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def solver_safety_wit_16 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (factor_count : Int) (remainder : Int) (pr_values : (List Int)) (pe_values : (List Int)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre)) (PreH6 : ((0 : Int) <= factor_count)) (PreH7 : (factor_count <= 64)) (PreH8 : ((Zlength (pr_values)) = factor_count)) (PreH9 : ((Zlength (pe_values)) = factor_count)) (PreH10 : (ValidFactorTable m_pre pr_values pe_values)) (PreH11 : (PrefixChoice pr_values pe_values x_pre (0 : Int) 1 1 1)) (PreH12 : ((0 : Int) <= (WalkSuffix (pr_values) (pe_values) (x_pre) ((0 : Int)) (1)))) (PreH13 : ((WalkSuffix (pr_values) (pe_values) (x_pre) ((0 : Int)) (1)) <= m_pre)) ,
  ((( &( "m" ) )) # UInt64 |-> (m_pre))
  ** ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "t" ) )) # UInt64 |-> (remainder))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "total_" ) )) # UInt64 |-> ((0 : Int)))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_17 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (factor_count : Int) (remainder : Int) (pr_values : (List Int)) (pe_values : (List Int)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre)) (PreH6 : ((0 : Int) <= factor_count)) (PreH7 : (factor_count <= 64)) (PreH8 : ((Zlength (pr_values)) = factor_count)) (PreH9 : ((Zlength (pe_values)) = factor_count)) (PreH10 : (ValidFactorTable m_pre pr_values pe_values)) (PreH11 : (PrefixChoice pr_values pe_values x_pre (0 : Int) 1 1 1)) (PreH12 : ((0 : Int) <= (WalkSuffix (pr_values) (pe_values) (x_pre) ((0 : Int)) (1)))) (PreH13 : ((WalkSuffix (pr_values) (pe_values) (x_pre) ((0 : Int)) (1)) <= m_pre)) ,
  ((( &( "m" ) )) # UInt64 |-> (m_pre))
  ** ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "t" ) )) # UInt64 |-> (remainder))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "total_" ) )) # UInt64 |-> ((0 : Int)))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_18 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (factor_count : Int) (remainder : Int) (pr_values : (List Int)) (pe_values : (List Int)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre)) (PreH6 : ((0 : Int) <= factor_count)) (PreH7 : (factor_count <= 64)) (PreH8 : ((Zlength (pr_values)) = factor_count)) (PreH9 : ((Zlength (pe_values)) = factor_count)) (PreH10 : (ValidFactorTable m_pre pr_values pe_values)) (PreH11 : (PrefixChoice pr_values pe_values x_pre (0 : Int) 1 1 1)) (PreH12 : ((0 : Int) <= (WalkSuffix (pr_values) (pe_values) (x_pre) ((0 : Int)) (1)))) (PreH13 : ((WalkSuffix (pr_values) (pe_values) (x_pre) ((0 : Int)) (1)) <= m_pre)) ,
  ((( &( "m" ) )) # UInt64 |-> (m_pre))
  ** ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "t" ) )) # UInt64 |-> (remainder))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "total_" ) )) # UInt64 |-> ((0 : Int)))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_safety_wit_19 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (factor_count : Int) (remainder : Int) (accumulator : Int) (pr_values : (List Int)) (pe_values : (List Int)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre)) (PreH6 : ((0 : Int) <= factor_count)) (PreH7 : (factor_count <= 64)) (PreH8 : ((Zlength (pr_values)) = factor_count)) (PreH9 : ((Zlength (pe_values)) = factor_count)) (PreH10 : (ValidFactorTable m_pre pr_values pe_values)) (PreH11 : (accumulator = (WalkSuffix (pr_values) (pe_values) (x_pre) ((0 : Int)) (1)))) (PreH12 : (CycleAnswer m_pre x_pre accumulator)) ,
  ((( &( "m" ) )) # UInt64 |-> (m_pre))
  ** ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "t" ) )) # UInt64 |-> (remainder))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "total_" ) )) # UInt64 |-> (accumulator))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def solver_entail_wit_1 : Prop :=
  (
forall (x_pre : Int) (m_pre : Int) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre)) ,
  (uint64Array.undef_full ( &( "pr" ) ) 64)
  ** (uint64Array.undef_full ( &( "pe" ) ) 64)
  ** ((( &( "nf" ) )) # Int |-> ((0 : Int)))
  ** ((( &( "x_" ) )) # UInt64 |->_)
  ** ((( &( "total_" ) )) # UInt64 |->_)
|--
  EX pe_values : (List Int), EX pr_values : (List Int), EX factor_count : Int,
  “ (2 <= m_pre) ” &&
  “ (m_pre <= 100000000000000) ” &&
  “ (1 <= x_pre) ” &&
  “ (x_pre < m_pre) ” &&
  “ (Pre m_pre x_pre) ” &&
  “ (2 <= 2) ” &&
  “ (2 <= 10000001) ” &&
  “ ((0 : Int) <= factor_count) ” &&
  “ (factor_count < 64) ” &&
  “ ((Zlength (pr_values)) = factor_count) ” &&
  “ ((Zlength (pe_values)) = factor_count) ” &&
  “ ((0 : Int) < m_pre) ” &&
  “ (m_pre <= m_pre) ” &&
  “ (FactorMachineTrialState m_pre 2 m_pre pr_values pe_values) ”
  &&  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |->_)
  ** ((( &( "total_" ) )) # UInt64 |->_)
) \/
(
forall (x_pre : Int) (m_pre : Int) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre)) ,
  TT && emp 
|--
  “ (FactorMachineTrialState m_pre 2 m_pre (@List.nil Int) (@List.nil Int)) ” &&
  “ ((Zlength ((@List.nil Int))) = (0 : Int)) ” &&
  “ ((Zlength ((@List.nil Int))) = (0 : Int)) ”
  &&  emp
)

noncomputable def solver_entail_wit_1_split_goal_1 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre)) ,
  (FactorMachineTrialState m_pre 2 m_pre (@List.nil Int) (@List.nil Int))

noncomputable def solver_entail_wit_1_split_goal_2 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre)) ,
  ((Zlength ((@List.nil Int))) = (0 : Int))

noncomputable def solver_entail_wit_1_split_goal_3 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre)) ,
  ((Zlength ((@List.nil Int))) = (0 : Int))

noncomputable def solver_entail_wit_2 : Prop :=
  (
forall (x_pre : Int) (m_pre : Int) (remainder : Int) (pe_values_2 : (List Int)) (pr_values_2 : (List Int)) (factor_count_2 : Int) (p : Int) (PreH1 : ((Z.rem remainder p) = (0 : Int))) (PreH2 : ((p * p) <= remainder)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100000000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre < m_pre)) (PreH7 : (Pre m_pre x_pre)) (PreH8 : (2 <= p)) (PreH9 : (p <= 10000001)) (PreH10 : ((0 : Int) <= factor_count_2)) (PreH11 : (factor_count_2 < 64)) (PreH12 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH13 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH14 : ((0 : Int) < remainder)) (PreH15 : (remainder <= m_pre)) (PreH16 : (FactorMachineTrialState m_pre p remainder pr_values_2 pe_values_2)) ,
  (uint64Array.seg ( &( "pe" ) ) (0 : Int) (factor_count_2 + 1) (pe_values_2 ++ ((0 : Int) :: (@List.nil Int))))
  ** (uint64Array.undef_seg ( &( "pe" ) ) (factor_count_2 + 1) 64)
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) (factor_count_2 + 1) (pr_values_2 ++ (p :: (@List.nil Int))))
  ** (uint64Array.undef_seg ( &( "pr" ) ) (factor_count_2 + 1) 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count_2))
  ** ((( &( "x_" ) )) # UInt64 |->_)
  ** ((( &( "total_" ) )) # UInt64 |->_)
|--
  EX original_remainder : Int, EX exponent : Int, EX pe_values : (List Int), EX pr_values : (List Int), EX factor_count : Int,
  “ (2 <= m_pre) ” &&
  “ (m_pre <= 100000000000000) ” &&
  “ (1 <= x_pre) ” &&
  “ (x_pre < m_pre) ” &&
  “ (Pre m_pre x_pre) ” &&
  “ (2 <= p) ” &&
  “ (p <= 10000000) ” &&
  “ ((0 : Int) <= factor_count) ” &&
  “ (factor_count < 64) ” &&
  “ ((Zlength (pr_values)) = factor_count) ” &&
  “ ((Zlength (pe_values)) = factor_count) ” &&
  “ ((0 : Int) <= exponent) ” &&
  “ (exponent <= 47) ” &&
  “ (FactorMachineAtPrime m_pre p original_remainder remainder exponent pr_values pe_values) ”
  &&  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.seg ( &( "pr" ) ) factor_count (factor_count + 1) (p :: (@List.nil Int)))
  ** (uint64Array.undef_seg ( &( "pr" ) ) (factor_count + 1) 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.seg ( &( "pe" ) ) factor_count (factor_count + 1) (exponent :: (@List.nil Int)))
  ** (uint64Array.undef_seg ( &( "pe" ) ) (factor_count + 1) 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |->_)
  ** ((( &( "total_" ) )) # UInt64 |->_)
) \/
(
forall (x_pre : Int) (m_pre : Int) (remainder : Int) (pe_values_2 : (List Int)) (pr_values_2 : (List Int)) (factor_count_2 : Int) (p : Int) (PreH1 : ((Z.rem remainder p) = (0 : Int))) (PreH2 : ((p * p) <= remainder)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100000000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre < m_pre)) (PreH7 : (Pre m_pre x_pre)) (PreH8 : (2 <= p)) (PreH9 : (p <= 10000001)) (PreH10 : ((0 : Int) <= factor_count_2)) (PreH11 : (factor_count_2 < 64)) (PreH12 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH13 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH14 : ((0 : Int) < remainder)) (PreH15 : (remainder <= m_pre)) (PreH16 : (FactorMachineTrialState m_pre p remainder pr_values_2 pe_values_2)) ,
  TT && emp 
|--
  EX original_remainder : Int, EX exponent : Int, EX pe_values : (List Int), EX pr_values : (List Int),
  “ ((Zlength (pr_values)) = ((Zlength (pr_values_2)) - (0 : Int))) ” &&
  “ ((pr_values_2 ++ (p :: (@List.nil Int))) = (pr_values ++ (p :: (@List.nil Int)))) ” &&
  “ ((Zlength (pe_values)) = ((Zlength (pr_values_2)) - (0 : Int))) ” &&
  “ ((pe_values_2 ++ ((0 : Int) :: (@List.nil Int))) = (pe_values ++ (exponent :: (@List.nil Int)))) ” &&
  “ (p <= 10000000) ” &&
  “ ((Zlength (pr_values)) = (Zlength (pr_values_2))) ” &&
  “ ((Zlength (pe_values)) = (Zlength (pr_values_2))) ” &&
  “ ((0 : Int) <= exponent) ” &&
  “ (exponent <= 47) ” &&
  “ (FactorMachineAtPrime m_pre p original_remainder remainder exponent pr_values pe_values) ”
  &&  emp
)

noncomputable def solver_entail_wit_3 : Prop :=
  (
forall (x_pre : Int) (m_pre : Int) (original_remainder_2 : Int) (remainder : Int) (exponent_2 : Int) (pe_values_2 : (List Int)) (pr_values_2 : (List Int)) (factor_count_2 : Int) (p : Int) (PreH1 : ((Z.rem remainder p) = (0 : Int))) (PreH2 : (2 <= m_pre)) (PreH3 : (m_pre <= 100000000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre < m_pre)) (PreH6 : (Pre m_pre x_pre)) (PreH7 : (2 <= p)) (PreH8 : (p <= 10000000)) (PreH9 : ((0 : Int) <= factor_count_2)) (PreH10 : (factor_count_2 < 64)) (PreH11 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH12 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH13 : ((0 : Int) <= exponent_2)) (PreH14 : (exponent_2 <= 47)) (PreH15 : (FactorMachineAtPrime m_pre p original_remainder_2 remainder exponent_2 pr_values_2 pe_values_2)) ,
  (uint64Array.seg ( &( "pe" ) ) factor_count_2 (factor_count_2 + 1) (replace_Znth ((factor_count_2 - factor_count_2)) ((unsigned_last_nbits (((Znth (factor_count_2 - factor_count_2) (exponent_2 :: (@List.nil Int)) (0 : Int)) + 1)) (64))) ((exponent_2 :: (@List.nil Int)))))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count_2 pr_values_2)
  ** (uint64Array.seg ( &( "pr" ) ) factor_count_2 (factor_count_2 + 1) (p :: (@List.nil Int)))
  ** (uint64Array.undef_seg ( &( "pr" ) ) (factor_count_2 + 1) 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count_2 pe_values_2)
  ** (uint64Array.undef_seg ( &( "pe" ) ) (factor_count_2 + 1) 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count_2))
  ** ((( &( "x_" ) )) # UInt64 |->_)
  ** ((( &( "total_" ) )) # UInt64 |->_)
|--
  EX original_remainder : Int, EX exponent : Int, EX pe_values : (List Int), EX pr_values : (List Int), EX factor_count : Int,
  “ (2 <= m_pre) ” &&
  “ (m_pre <= 100000000000000) ” &&
  “ (1 <= x_pre) ” &&
  “ (x_pre < m_pre) ” &&
  “ (Pre m_pre x_pre) ” &&
  “ (2 <= p) ” &&
  “ (p <= 10000000) ” &&
  “ ((0 : Int) <= factor_count) ” &&
  “ (factor_count < 64) ” &&
  “ ((Zlength (pr_values)) = factor_count) ” &&
  “ ((Zlength (pe_values)) = factor_count) ” &&
  “ ((0 : Int) <= exponent) ” &&
  “ (exponent <= 47) ” &&
  “ (FactorMachineAtPrime m_pre p original_remainder (Z.quot remainder p) exponent pr_values pe_values) ”
  &&  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.seg ( &( "pr" ) ) factor_count (factor_count + 1) (p :: (@List.nil Int)))
  ** (uint64Array.undef_seg ( &( "pr" ) ) (factor_count + 1) 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.seg ( &( "pe" ) ) factor_count (factor_count + 1) (exponent :: (@List.nil Int)))
  ** (uint64Array.undef_seg ( &( "pe" ) ) (factor_count + 1) 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |->_)
  ** ((( &( "total_" ) )) # UInt64 |->_)
) \/
(
forall (x_pre : Int) (m_pre : Int) (original_remainder_2 : Int) (remainder : Int) (exponent_2 : Int) (pe_values_2 : (List Int)) (pr_values_2 : (List Int)) (factor_count_2 : Int) (p : Int) (PreH1 : ((Z.rem remainder p) = (0 : Int))) (PreH2 : (2 <= m_pre)) (PreH3 : (m_pre <= 100000000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre < m_pre)) (PreH6 : (Pre m_pre x_pre)) (PreH7 : (2 <= p)) (PreH8 : (p <= 10000000)) (PreH9 : ((0 : Int) <= factor_count_2)) (PreH10 : (factor_count_2 < 64)) (PreH11 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH12 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH13 : ((0 : Int) <= exponent_2)) (PreH14 : (exponent_2 <= 47)) (PreH15 : (FactorMachineAtPrime m_pre p original_remainder_2 remainder exponent_2 pr_values_2 pe_values_2)) ,
  TT && emp 
|--
  EX original_remainder : Int, EX exponent : Int,
  “ ((replace_Znth (((Zlength (pr_values_2)) - (Zlength (pr_values_2)))) ((unsigned_last_nbits (((Znth ((Zlength (pr_values_2)) - (Zlength (pr_values_2))) (exponent_2 :: (@List.nil Int)) (0 : Int)) + 1)) (64))) ((exponent_2 :: (@List.nil Int)))) = (exponent :: (@List.nil Int))) ” &&
  “ ((0 : Int) <= exponent) ” &&
  “ (exponent <= 47) ” &&
  “ (FactorMachineAtPrime m_pre p original_remainder (Z.quot remainder p) exponent pr_values_2 pe_values_2) ”
  &&  emp
)

noncomputable def solver_entail_wit_4_1 : Prop :=
  (
forall (x_pre : Int) (m_pre : Int) (original_remainder : Int) (remainder : Int) (exponent : Int) (pe_values_2 : (List Int)) (pr_values_2 : (List Int)) (factor_count_2 : Int) (p : Int) (PreH1 : ((Z.rem remainder p) ≠ (0 : Int))) (PreH2 : (2 <= m_pre)) (PreH3 : (m_pre <= 100000000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre < m_pre)) (PreH6 : (Pre m_pre x_pre)) (PreH7 : (2 <= p)) (PreH8 : (p <= 10000000)) (PreH9 : ((0 : Int) <= factor_count_2)) (PreH10 : (factor_count_2 < 64)) (PreH11 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH12 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH13 : ((0 : Int) <= exponent)) (PreH14 : (exponent <= 47)) (PreH15 : (FactorMachineAtPrime m_pre p original_remainder remainder exponent pr_values_2 pe_values_2)) ,
  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count_2 pr_values_2)
  ** (uint64Array.seg ( &( "pr" ) ) factor_count_2 (factor_count_2 + 1) (p :: (@List.nil Int)))
  ** (uint64Array.undef_seg ( &( "pr" ) ) (factor_count_2 + 1) 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count_2 pe_values_2)
  ** (uint64Array.seg ( &( "pe" ) ) factor_count_2 (factor_count_2 + 1) (exponent :: (@List.nil Int)))
  ** (uint64Array.undef_seg ( &( "pe" ) ) (factor_count_2 + 1) 64)
  ** ((( &( "nf" ) )) # Int |-> ((factor_count_2 + 1)))
  ** ((( &( "x_" ) )) # UInt64 |->_)
  ** ((( &( "total_" ) )) # UInt64 |->_)
|--
  EX pe_values : (List Int), EX pr_values : (List Int), EX factor_count : Int,
  “ (2 <= m_pre) ” &&
  “ (m_pre <= 100000000000000) ” &&
  “ (1 <= x_pre) ” &&
  “ (x_pre < m_pre) ” &&
  “ (Pre m_pre x_pre) ” &&
  “ (2 <= (p + 1)) ” &&
  “ ((p + 1) <= 10000001) ” &&
  “ ((0 : Int) <= factor_count) ” &&
  “ (factor_count < 64) ” &&
  “ ((Zlength (pr_values)) = factor_count) ” &&
  “ ((Zlength (pe_values)) = factor_count) ” &&
  “ ((0 : Int) < remainder) ” &&
  “ (remainder <= m_pre) ” &&
  “ (FactorMachineTrialState m_pre (p + 1) remainder pr_values pe_values) ”
  &&  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |->_)
  ** ((( &( "total_" ) )) # UInt64 |->_)
) \/
(
forall (x_pre : Int) (m_pre : Int) (original_remainder : Int) (remainder : Int) (exponent : Int) (pe_values_2 : (List Int)) (pr_values_2 : (List Int)) (factor_count_2 : Int) (p : Int) (PreH1 : ((Z.rem remainder p) ≠ (0 : Int))) (PreH2 : (2 <= m_pre)) (PreH3 : (m_pre <= 100000000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre < m_pre)) (PreH6 : (Pre m_pre x_pre)) (PreH7 : (2 <= p)) (PreH8 : (p <= 10000000)) (PreH9 : ((0 : Int) <= factor_count_2)) (PreH10 : (factor_count_2 < 64)) (PreH11 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH12 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH13 : ((0 : Int) <= exponent)) (PreH14 : (exponent <= 47)) (PreH15 : (FactorMachineAtPrime m_pre p original_remainder remainder exponent pr_values_2 pe_values_2)) ,
  TT && emp 
|--
  “ (FactorMachineTrialState m_pre (p + 1) remainder (pr_values_2 ++ (p :: (@List.nil Int))) (pe_values_2 ++ (exponent :: (@List.nil Int)))) ” &&
  “ (remainder <= m_pre) ” &&
  “ ((0 : Int) < remainder) ” &&
  “ ((Zlength ((pe_values_2 ++ (exponent :: (@List.nil Int))))) = (factor_count_2 + 1)) ” &&
  “ ((Zlength ((pr_values_2 ++ (p :: (@List.nil Int))))) = (factor_count_2 + 1)) ” &&
  “ ((factor_count_2 + 1) < 64) ”
  &&  emp
)

noncomputable def solver_entail_wit_4_1_split_goal_1 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (original_remainder : Int) (remainder : Int) (exponent : Int) (pe_values_2 : (List Int)) (pr_values_2 : (List Int)) (factor_count_2 : Int) (p : Int) (PreH1 : ((Z.rem remainder p) ≠ (0 : Int))) (PreH2 : (2 <= m_pre)) (PreH3 : (m_pre <= 100000000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre < m_pre)) (PreH6 : (Pre m_pre x_pre)) (PreH7 : (2 <= p)) (PreH8 : (p <= 10000000)) (PreH9 : ((0 : Int) <= factor_count_2)) (PreH10 : (factor_count_2 < 64)) (PreH11 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH12 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH13 : ((0 : Int) <= exponent)) (PreH14 : (exponent <= 47)) (PreH15 : (FactorMachineAtPrime m_pre p original_remainder remainder exponent pr_values_2 pe_values_2)) ,
  (FactorMachineTrialState m_pre (p + 1) remainder (pr_values_2 ++ (p :: (@List.nil Int))) (pe_values_2 ++ (exponent :: (@List.nil Int))))

noncomputable def solver_entail_wit_4_1_split_goal_2 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (original_remainder : Int) (remainder : Int) (exponent : Int) (pe_values_2 : (List Int)) (pr_values_2 : (List Int)) (factor_count_2 : Int) (p : Int) (PreH1 : ((Z.rem remainder p) ≠ (0 : Int))) (PreH2 : (2 <= m_pre)) (PreH3 : (m_pre <= 100000000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre < m_pre)) (PreH6 : (Pre m_pre x_pre)) (PreH7 : (2 <= p)) (PreH8 : (p <= 10000000)) (PreH9 : ((0 : Int) <= factor_count_2)) (PreH10 : (factor_count_2 < 64)) (PreH11 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH12 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH13 : ((0 : Int) <= exponent)) (PreH14 : (exponent <= 47)) (PreH15 : (FactorMachineAtPrime m_pre p original_remainder remainder exponent pr_values_2 pe_values_2)) ,
  (remainder <= m_pre)

noncomputable def solver_entail_wit_4_1_split_goal_3 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (original_remainder : Int) (remainder : Int) (exponent : Int) (pe_values_2 : (List Int)) (pr_values_2 : (List Int)) (factor_count_2 : Int) (p : Int) (PreH1 : ((Z.rem remainder p) ≠ (0 : Int))) (PreH2 : (2 <= m_pre)) (PreH3 : (m_pre <= 100000000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre < m_pre)) (PreH6 : (Pre m_pre x_pre)) (PreH7 : (2 <= p)) (PreH8 : (p <= 10000000)) (PreH9 : ((0 : Int) <= factor_count_2)) (PreH10 : (factor_count_2 < 64)) (PreH11 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH12 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH13 : ((0 : Int) <= exponent)) (PreH14 : (exponent <= 47)) (PreH15 : (FactorMachineAtPrime m_pre p original_remainder remainder exponent pr_values_2 pe_values_2)) ,
  ((0 : Int) < remainder)

noncomputable def solver_entail_wit_4_1_split_goal_4 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (original_remainder : Int) (remainder : Int) (exponent : Int) (pe_values_2 : (List Int)) (pr_values_2 : (List Int)) (factor_count_2 : Int) (p : Int) (PreH1 : ((Z.rem remainder p) ≠ (0 : Int))) (PreH2 : (2 <= m_pre)) (PreH3 : (m_pre <= 100000000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre < m_pre)) (PreH6 : (Pre m_pre x_pre)) (PreH7 : (2 <= p)) (PreH8 : (p <= 10000000)) (PreH9 : ((0 : Int) <= factor_count_2)) (PreH10 : (factor_count_2 < 64)) (PreH11 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH12 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH13 : ((0 : Int) <= exponent)) (PreH14 : (exponent <= 47)) (PreH15 : (FactorMachineAtPrime m_pre p original_remainder remainder exponent pr_values_2 pe_values_2)) ,
  ((Zlength ((pe_values_2 ++ (exponent :: (@List.nil Int))))) = (factor_count_2 + 1))

noncomputable def solver_entail_wit_4_1_split_goal_5 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (original_remainder : Int) (remainder : Int) (exponent : Int) (pe_values_2 : (List Int)) (pr_values_2 : (List Int)) (factor_count_2 : Int) (p : Int) (PreH1 : ((Z.rem remainder p) ≠ (0 : Int))) (PreH2 : (2 <= m_pre)) (PreH3 : (m_pre <= 100000000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre < m_pre)) (PreH6 : (Pre m_pre x_pre)) (PreH7 : (2 <= p)) (PreH8 : (p <= 10000000)) (PreH9 : ((0 : Int) <= factor_count_2)) (PreH10 : (factor_count_2 < 64)) (PreH11 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH12 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH13 : ((0 : Int) <= exponent)) (PreH14 : (exponent <= 47)) (PreH15 : (FactorMachineAtPrime m_pre p original_remainder remainder exponent pr_values_2 pe_values_2)) ,
  ((Zlength ((pr_values_2 ++ (p :: (@List.nil Int))))) = (factor_count_2 + 1))

noncomputable def solver_entail_wit_4_1_split_goal_6 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (original_remainder : Int) (remainder : Int) (exponent : Int) (pe_values_2 : (List Int)) (pr_values_2 : (List Int)) (factor_count_2 : Int) (p : Int) (PreH1 : ((Z.rem remainder p) ≠ (0 : Int))) (PreH2 : (2 <= m_pre)) (PreH3 : (m_pre <= 100000000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre < m_pre)) (PreH6 : (Pre m_pre x_pre)) (PreH7 : (2 <= p)) (PreH8 : (p <= 10000000)) (PreH9 : ((0 : Int) <= factor_count_2)) (PreH10 : (factor_count_2 < 64)) (PreH11 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH12 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH13 : ((0 : Int) <= exponent)) (PreH14 : (exponent <= 47)) (PreH15 : (FactorMachineAtPrime m_pre p original_remainder remainder exponent pr_values_2 pe_values_2)) ,
  ((factor_count_2 + 1) < 64)

noncomputable def solver_entail_wit_4_2 : Prop :=
  (
forall (x_pre : Int) (m_pre : Int) (remainder : Int) (pe_values_2 : (List Int)) (pr_values_2 : (List Int)) (factor_count_2 : Int) (p : Int) (PreH1 : ((Z.rem remainder p) ≠ (0 : Int))) (PreH2 : ((p * p) <= remainder)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100000000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre < m_pre)) (PreH7 : (Pre m_pre x_pre)) (PreH8 : (2 <= p)) (PreH9 : (p <= 10000001)) (PreH10 : ((0 : Int) <= factor_count_2)) (PreH11 : (factor_count_2 < 64)) (PreH12 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH13 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH14 : ((0 : Int) < remainder)) (PreH15 : (remainder <= m_pre)) (PreH16 : (FactorMachineTrialState m_pre p remainder pr_values_2 pe_values_2)) ,
  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count_2 pr_values_2)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count_2 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count_2 pe_values_2)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count_2 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count_2))
  ** ((( &( "x_" ) )) # UInt64 |->_)
  ** ((( &( "total_" ) )) # UInt64 |->_)
|--
  EX pe_values : (List Int), EX pr_values : (List Int), EX factor_count : Int,
  “ (2 <= m_pre) ” &&
  “ (m_pre <= 100000000000000) ” &&
  “ (1 <= x_pre) ” &&
  “ (x_pre < m_pre) ” &&
  “ (Pre m_pre x_pre) ” &&
  “ (2 <= (p + 1)) ” &&
  “ ((p + 1) <= 10000001) ” &&
  “ ((0 : Int) <= factor_count) ” &&
  “ (factor_count < 64) ” &&
  “ ((Zlength (pr_values)) = factor_count) ” &&
  “ ((Zlength (pe_values)) = factor_count) ” &&
  “ ((0 : Int) < remainder) ” &&
  “ (remainder <= m_pre) ” &&
  “ (FactorMachineTrialState m_pre (p + 1) remainder pr_values pe_values) ”
  &&  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |->_)
  ** ((( &( "total_" ) )) # UInt64 |->_)
) \/
(
forall (x_pre : Int) (m_pre : Int) (remainder : Int) (pe_values_2 : (List Int)) (pr_values_2 : (List Int)) (factor_count_2 : Int) (p : Int) (PreH1 : ((Z.rem remainder p) ≠ (0 : Int))) (PreH2 : ((p * p) <= remainder)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100000000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre < m_pre)) (PreH7 : (Pre m_pre x_pre)) (PreH8 : (2 <= p)) (PreH9 : (p <= 10000001)) (PreH10 : ((0 : Int) <= factor_count_2)) (PreH11 : (factor_count_2 < 64)) (PreH12 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH13 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH14 : ((0 : Int) < remainder)) (PreH15 : (remainder <= m_pre)) (PreH16 : (FactorMachineTrialState m_pre p remainder pr_values_2 pe_values_2)) ,
  TT && emp 
|--
  “ (FactorMachineTrialState m_pre (p + 1) remainder pr_values_2 pe_values_2) ”
  &&  emp
)

noncomputable def solver_entail_wit_4_2_split_goal_1 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (remainder : Int) (pe_values_2 : (List Int)) (pr_values_2 : (List Int)) (factor_count_2 : Int) (p : Int) (PreH1 : ((Z.rem remainder p) ≠ (0 : Int))) (PreH2 : ((p * p) <= remainder)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100000000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre < m_pre)) (PreH7 : (Pre m_pre x_pre)) (PreH8 : (2 <= p)) (PreH9 : (p <= 10000001)) (PreH10 : ((0 : Int) <= factor_count_2)) (PreH11 : (factor_count_2 < 64)) (PreH12 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH13 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH14 : ((0 : Int) < remainder)) (PreH15 : (remainder <= m_pre)) (PreH16 : (FactorMachineTrialState m_pre p remainder pr_values_2 pe_values_2)) ,
  (FactorMachineTrialState m_pre (p + 1) remainder pr_values_2 pe_values_2)

noncomputable def solver_entail_wit_5_1 : Prop :=
  (
forall (x_pre : Int) (m_pre : Int) (remainder : Int) (pe_values_2 : (List Int)) (pr_values_2 : (List Int)) (factor_count_2 : Int) (p : Int) (PreH1 : (remainder > 1)) (PreH2 : ((p * p) > remainder)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100000000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre < m_pre)) (PreH7 : (Pre m_pre x_pre)) (PreH8 : (2 <= p)) (PreH9 : (p <= 10000001)) (PreH10 : ((0 : Int) <= factor_count_2)) (PreH11 : (factor_count_2 < 64)) (PreH12 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH13 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH14 : ((0 : Int) < remainder)) (PreH15 : (remainder <= m_pre)) (PreH16 : (FactorMachineTrialState m_pre p remainder pr_values_2 pe_values_2)) ,
  (uint64Array.seg ( &( "pe" ) ) (0 : Int) (factor_count_2 + 1) (pe_values_2 ++ (1 :: (@List.nil Int))))
  ** (uint64Array.undef_seg ( &( "pe" ) ) (factor_count_2 + 1) 64)
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) (factor_count_2 + 1) (pr_values_2 ++ (remainder :: (@List.nil Int))))
  ** (uint64Array.undef_seg ( &( "pr" ) ) (factor_count_2 + 1) 64)
  ** ((( &( "nf" ) )) # Int |-> ((factor_count_2 + 1)))
  ** ((( &( "x_" ) )) # UInt64 |->_)
  ** ((( &( "total_" ) )) # UInt64 |->_)
|--
  EX pe_values : (List Int), EX pr_values : (List Int), EX factor_count : Int,
  “ (2 <= m_pre) ” &&
  “ (m_pre <= 100000000000000) ” &&
  “ (1 <= x_pre) ” &&
  “ (x_pre < m_pre) ” &&
  “ (Pre m_pre x_pre) ” &&
  “ ((0 : Int) <= factor_count) ” &&
  “ (factor_count <= 64) ” &&
  “ ((Zlength (pr_values)) = factor_count) ” &&
  “ ((Zlength (pe_values)) = factor_count) ” &&
  “ (ValidFactorTable m_pre pr_values pe_values) ”
  &&  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |->_)
  ** ((( &( "total_" ) )) # UInt64 |->_)
) \/
(
forall (x_pre : Int) (m_pre : Int) (remainder : Int) (pe_values_2 : (List Int)) (pr_values_2 : (List Int)) (factor_count_2 : Int) (p : Int) (PreH1 : (remainder > 1)) (PreH2 : ((p * p) > remainder)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100000000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre < m_pre)) (PreH7 : (Pre m_pre x_pre)) (PreH8 : (2 <= p)) (PreH9 : (p <= 10000001)) (PreH10 : ((0 : Int) <= factor_count_2)) (PreH11 : (factor_count_2 < 64)) (PreH12 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH13 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH14 : ((0 : Int) < remainder)) (PreH15 : (remainder <= m_pre)) (PreH16 : (FactorMachineTrialState m_pre p remainder pr_values_2 pe_values_2)) ,
  TT && emp 
|--
  “ (ValidFactorTable m_pre (pr_values_2 ++ (remainder :: (@List.nil Int))) (pe_values_2 ++ (1 :: (@List.nil Int)))) ” &&
  “ ((Zlength ((pe_values_2 ++ (1 :: (@List.nil Int))))) = (factor_count_2 + 1)) ” &&
  “ ((Zlength ((pr_values_2 ++ (remainder :: (@List.nil Int))))) = (factor_count_2 + 1)) ”
  &&  emp
)

noncomputable def solver_entail_wit_5_1_split_goal_1 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (remainder : Int) (pe_values_2 : (List Int)) (pr_values_2 : (List Int)) (factor_count_2 : Int) (p : Int) (PreH1 : (remainder > 1)) (PreH2 : ((p * p) > remainder)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100000000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre < m_pre)) (PreH7 : (Pre m_pre x_pre)) (PreH8 : (2 <= p)) (PreH9 : (p <= 10000001)) (PreH10 : ((0 : Int) <= factor_count_2)) (PreH11 : (factor_count_2 < 64)) (PreH12 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH13 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH14 : ((0 : Int) < remainder)) (PreH15 : (remainder <= m_pre)) (PreH16 : (FactorMachineTrialState m_pre p remainder pr_values_2 pe_values_2)) ,
  (ValidFactorTable m_pre (pr_values_2 ++ (remainder :: (@List.nil Int))) (pe_values_2 ++ (1 :: (@List.nil Int))))

noncomputable def solver_entail_wit_5_1_split_goal_2 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (remainder : Int) (pe_values_2 : (List Int)) (pr_values_2 : (List Int)) (factor_count_2 : Int) (p : Int) (PreH1 : (remainder > 1)) (PreH2 : ((p * p) > remainder)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100000000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre < m_pre)) (PreH7 : (Pre m_pre x_pre)) (PreH8 : (2 <= p)) (PreH9 : (p <= 10000001)) (PreH10 : ((0 : Int) <= factor_count_2)) (PreH11 : (factor_count_2 < 64)) (PreH12 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH13 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH14 : ((0 : Int) < remainder)) (PreH15 : (remainder <= m_pre)) (PreH16 : (FactorMachineTrialState m_pre p remainder pr_values_2 pe_values_2)) ,
  ((Zlength ((pe_values_2 ++ (1 :: (@List.nil Int))))) = (factor_count_2 + 1))

noncomputable def solver_entail_wit_5_1_split_goal_3 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (remainder : Int) (pe_values_2 : (List Int)) (pr_values_2 : (List Int)) (factor_count_2 : Int) (p : Int) (PreH1 : (remainder > 1)) (PreH2 : ((p * p) > remainder)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100000000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre < m_pre)) (PreH7 : (Pre m_pre x_pre)) (PreH8 : (2 <= p)) (PreH9 : (p <= 10000001)) (PreH10 : ((0 : Int) <= factor_count_2)) (PreH11 : (factor_count_2 < 64)) (PreH12 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH13 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH14 : ((0 : Int) < remainder)) (PreH15 : (remainder <= m_pre)) (PreH16 : (FactorMachineTrialState m_pre p remainder pr_values_2 pe_values_2)) ,
  ((Zlength ((pr_values_2 ++ (remainder :: (@List.nil Int))))) = (factor_count_2 + 1))

noncomputable def solver_entail_wit_5_2 : Prop :=
  (
forall (x_pre : Int) (m_pre : Int) (remainder : Int) (pe_values_2 : (List Int)) (pr_values_2 : (List Int)) (factor_count_2 : Int) (p : Int) (PreH1 : (remainder <= 1)) (PreH2 : ((p * p) > remainder)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100000000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre < m_pre)) (PreH7 : (Pre m_pre x_pre)) (PreH8 : (2 <= p)) (PreH9 : (p <= 10000001)) (PreH10 : ((0 : Int) <= factor_count_2)) (PreH11 : (factor_count_2 < 64)) (PreH12 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH13 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH14 : ((0 : Int) < remainder)) (PreH15 : (remainder <= m_pre)) (PreH16 : (FactorMachineTrialState m_pre p remainder pr_values_2 pe_values_2)) ,
  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count_2 pr_values_2)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count_2 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count_2 pe_values_2)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count_2 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count_2))
  ** ((( &( "x_" ) )) # UInt64 |->_)
  ** ((( &( "total_" ) )) # UInt64 |->_)
|--
  EX pe_values : (List Int), EX pr_values : (List Int), EX factor_count : Int,
  “ (2 <= m_pre) ” &&
  “ (m_pre <= 100000000000000) ” &&
  “ (1 <= x_pre) ” &&
  “ (x_pre < m_pre) ” &&
  “ (Pre m_pre x_pre) ” &&
  “ ((0 : Int) <= factor_count) ” &&
  “ (factor_count <= 64) ” &&
  “ ((Zlength (pr_values)) = factor_count) ” &&
  “ ((Zlength (pe_values)) = factor_count) ” &&
  “ (ValidFactorTable m_pre pr_values pe_values) ”
  &&  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |->_)
  ** ((( &( "total_" ) )) # UInt64 |->_)
) \/
(
forall (x_pre : Int) (m_pre : Int) (remainder : Int) (pe_values_2 : (List Int)) (pr_values_2 : (List Int)) (factor_count_2 : Int) (p : Int) (PreH1 : (remainder <= 1)) (PreH2 : ((p * p) > remainder)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100000000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre < m_pre)) (PreH7 : (Pre m_pre x_pre)) (PreH8 : (2 <= p)) (PreH9 : (p <= 10000001)) (PreH10 : ((0 : Int) <= factor_count_2)) (PreH11 : (factor_count_2 < 64)) (PreH12 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH13 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH14 : ((0 : Int) < remainder)) (PreH15 : (remainder <= m_pre)) (PreH16 : (FactorMachineTrialState m_pre p remainder pr_values_2 pe_values_2)) ,
  TT && emp 
|--
  “ (ValidFactorTable m_pre pr_values_2 pe_values_2) ”
  &&  emp
)

noncomputable def solver_entail_wit_5_2_split_goal_1 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (remainder : Int) (pe_values_2 : (List Int)) (pr_values_2 : (List Int)) (factor_count_2 : Int) (p : Int) (PreH1 : (remainder <= 1)) (PreH2 : ((p * p) > remainder)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100000000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre < m_pre)) (PreH7 : (Pre m_pre x_pre)) (PreH8 : (2 <= p)) (PreH9 : (p <= 10000001)) (PreH10 : ((0 : Int) <= factor_count_2)) (PreH11 : (factor_count_2 < 64)) (PreH12 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH13 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH14 : ((0 : Int) < remainder)) (PreH15 : (remainder <= m_pre)) (PreH16 : (FactorMachineTrialState m_pre p remainder pr_values_2 pe_values_2)) ,
  (ValidFactorTable m_pre pr_values_2 pe_values_2)

noncomputable def solver_entail_wit_6 : Prop :=
  (
forall (x_pre : Int) (m_pre : Int) (factor_count_2 : Int) (pr_values_2 : (List Int)) (pe_values_2 : (List Int)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre)) (PreH6 : ((0 : Int) <= factor_count_2)) (PreH7 : (factor_count_2 <= 64)) (PreH8 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH9 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH10 : (ValidFactorTable m_pre pr_values_2 pe_values_2)) ,
  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count_2 pr_values_2)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count_2 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count_2 pe_values_2)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count_2 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count_2))
  ** ((( &( "x_" ) )) # UInt64 |->_)
  ** ((( &( "total_" ) )) # UInt64 |->_)
|--
  EX pe_values : (List Int), EX pr_values : (List Int), EX factor_count : Int,
  “ (2 <= m_pre) ” &&
  “ (m_pre <= 100000000000000) ” &&
  “ (1 <= x_pre) ” &&
  “ (x_pre < m_pre) ” &&
  “ (Pre m_pre x_pre) ” &&
  “ ((0 : Int) <= factor_count) ” &&
  “ (factor_count <= 64) ” &&
  “ ((Zlength (pr_values)) = factor_count) ” &&
  “ ((Zlength (pe_values)) = factor_count) ” &&
  “ (ValidFactorTable m_pre pr_values pe_values) ” &&
  “ (PrefixChoice pr_values pe_values x_pre (0 : Int) 1 1 1) ” &&
  “ ((0 : Int) <= (WalkSuffix (pr_values) (pe_values) (x_pre) ((0 : Int)) (1))) ” &&
  “ ((WalkSuffix (pr_values) (pe_values) (x_pre) ((0 : Int)) (1)) <= m_pre) ”
  &&  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |->_)
  ** ((( &( "total_" ) )) # UInt64 |->_)
) \/
(
forall (x_pre : Int) (m_pre : Int) (factor_count_2 : Int) (pr_values_2 : (List Int)) (pe_values_2 : (List Int)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre)) (PreH6 : ((0 : Int) <= factor_count_2)) (PreH7 : (factor_count_2 <= 64)) (PreH8 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH9 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH10 : (ValidFactorTable m_pre pr_values_2 pe_values_2)) ,
  TT && emp 
|--
  “ ((WalkSuffix (pr_values_2) (pe_values_2) (x_pre) ((0 : Int)) (1)) <= m_pre) ” &&
  “ ((0 : Int) <= (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) ((0 : Int)) (1))) ” &&
  “ (PrefixChoice pr_values_2 pe_values_2 x_pre (0 : Int) 1 1 1) ”
  &&  emp
)

noncomputable def solver_entail_wit_6_split_goal_1 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (factor_count_2 : Int) (pr_values_2 : (List Int)) (pe_values_2 : (List Int)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre)) (PreH6 : ((0 : Int) <= factor_count_2)) (PreH7 : (factor_count_2 <= 64)) (PreH8 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH9 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH10 : (ValidFactorTable m_pre pr_values_2 pe_values_2)) ,
  ((WalkSuffix (pr_values_2) (pe_values_2) (x_pre) ((0 : Int)) (1)) <= m_pre)

noncomputable def solver_entail_wit_6_split_goal_2 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (factor_count_2 : Int) (pr_values_2 : (List Int)) (pe_values_2 : (List Int)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre)) (PreH6 : ((0 : Int) <= factor_count_2)) (PreH7 : (factor_count_2 <= 64)) (PreH8 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH9 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH10 : (ValidFactorTable m_pre pr_values_2 pe_values_2)) ,
  ((0 : Int) <= (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) ((0 : Int)) (1)))

noncomputable def solver_entail_wit_6_split_goal_3 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (factor_count_2 : Int) (pr_values_2 : (List Int)) (pe_values_2 : (List Int)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre)) (PreH6 : ((0 : Int) <= factor_count_2)) (PreH7 : (factor_count_2 <= 64)) (PreH8 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH9 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH10 : (ValidFactorTable m_pre pr_values_2 pe_values_2)) ,
  (PrefixChoice pr_values_2 pe_values_2 x_pre (0 : Int) 1 1 1)

noncomputable def solver_entail_wit_7 : Prop :=
  (
forall (x_pre : Int) (m_pre : Int) (factor_count_2 : Int) (pr_values_2 : (List Int)) (pe_values_2 : (List Int)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre)) (PreH6 : ((0 : Int) <= factor_count_2)) (PreH7 : (factor_count_2 <= 64)) (PreH8 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH9 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH10 : (ValidFactorTable m_pre pr_values_2 pe_values_2)) (PreH11 : (PrefixChoice pr_values_2 pe_values_2 x_pre (0 : Int) 1 1 1)) (PreH12 : ((0 : Int) <= (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) ((0 : Int)) (1)))) (PreH13 : ((WalkSuffix (pr_values_2) (pe_values_2) (x_pre) ((0 : Int)) (1)) <= m_pre)) ,
  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count_2 pr_values_2)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count_2 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count_2 pe_values_2)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count_2 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count_2))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "total_" ) )) # UInt64 |-> (((0 : Int) + (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) ((0 : Int)) (1)))))
|--
  EX accumulator : Int, EX pe_values : (List Int), EX pr_values : (List Int), EX factor_count : Int,
  “ (2 <= m_pre) ” &&
  “ (m_pre <= 100000000000000) ” &&
  “ (1 <= x_pre) ” &&
  “ (x_pre < m_pre) ” &&
  “ (Pre m_pre x_pre) ” &&
  “ ((0 : Int) <= factor_count) ” &&
  “ (factor_count <= 64) ” &&
  “ ((Zlength (pr_values)) = factor_count) ” &&
  “ ((Zlength (pe_values)) = factor_count) ” &&
  “ (ValidFactorTable m_pre pr_values pe_values) ” &&
  “ (accumulator = (WalkSuffix (pr_values) (pe_values) (x_pre) ((0 : Int)) (1))) ” &&
  “ (CycleAnswer m_pre x_pre accumulator) ”
  &&  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "total_" ) )) # UInt64 |-> (accumulator))
) \/
(
forall (x_pre : Int) (m_pre : Int) (factor_count_2 : Int) (pr_values_2 : (List Int)) (pe_values_2 : (List Int)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre)) (PreH6 : ((0 : Int) <= factor_count_2)) (PreH7 : (factor_count_2 <= 64)) (PreH8 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH9 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH10 : (ValidFactorTable m_pre pr_values_2 pe_values_2)) (PreH11 : (PrefixChoice pr_values_2 pe_values_2 x_pre (0 : Int) 1 1 1)) (PreH12 : ((0 : Int) <= (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) ((0 : Int)) (1)))) (PreH13 : ((WalkSuffix (pr_values_2) (pe_values_2) (x_pre) ((0 : Int)) (1)) <= m_pre)) ,
  TT && emp 
|--
  “ (CycleAnswer m_pre x_pre (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) ((0 : Int)) (1))) ” &&
  “ (((0 : Int) + (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) ((0 : Int)) (1))) = (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) ((0 : Int)) (1))) ” &&
  “ (((0 : Int) + (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) ((0 : Int)) (1))) = (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) ((0 : Int)) (1))) ” &&
  “ (((0 : Int) + (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) ((0 : Int)) (1))) = (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) ((0 : Int)) (1))) ” &&
  “ (((0 : Int) + (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) ((0 : Int)) (1))) = (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) ((0 : Int)) (1))) ”
  &&  emp
)

noncomputable def solver_entail_wit_7_split_goal_1 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (factor_count_2 : Int) (pr_values_2 : (List Int)) (pe_values_2 : (List Int)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre)) (PreH6 : ((0 : Int) <= factor_count_2)) (PreH7 : (factor_count_2 <= 64)) (PreH8 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH9 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH10 : (ValidFactorTable m_pre pr_values_2 pe_values_2)) (PreH11 : (PrefixChoice pr_values_2 pe_values_2 x_pre (0 : Int) 1 1 1)) (PreH12 : ((0 : Int) <= (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) ((0 : Int)) (1)))) (PreH13 : ((WalkSuffix (pr_values_2) (pe_values_2) (x_pre) ((0 : Int)) (1)) <= m_pre)) ,
  (CycleAnswer m_pre x_pre (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) ((0 : Int)) (1)))

noncomputable def solver_entail_wit_7_split_goal_2 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (factor_count_2 : Int) (pr_values_2 : (List Int)) (pe_values_2 : (List Int)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre)) (PreH6 : ((0 : Int) <= factor_count_2)) (PreH7 : (factor_count_2 <= 64)) (PreH8 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH9 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH10 : (ValidFactorTable m_pre pr_values_2 pe_values_2)) (PreH11 : (PrefixChoice pr_values_2 pe_values_2 x_pre (0 : Int) 1 1 1)) (PreH12 : ((0 : Int) <= (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) ((0 : Int)) (1)))) (PreH13 : ((WalkSuffix (pr_values_2) (pe_values_2) (x_pre) ((0 : Int)) (1)) <= m_pre)) ,
  (((0 : Int) + (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) ((0 : Int)) (1))) = (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) ((0 : Int)) (1)))

noncomputable def solver_entail_wit_7_split_goal_3 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (factor_count_2 : Int) (pr_values_2 : (List Int)) (pe_values_2 : (List Int)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre)) (PreH6 : ((0 : Int) <= factor_count_2)) (PreH7 : (factor_count_2 <= 64)) (PreH8 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH9 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH10 : (ValidFactorTable m_pre pr_values_2 pe_values_2)) (PreH11 : (PrefixChoice pr_values_2 pe_values_2 x_pre (0 : Int) 1 1 1)) (PreH12 : ((0 : Int) <= (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) ((0 : Int)) (1)))) (PreH13 : ((WalkSuffix (pr_values_2) (pe_values_2) (x_pre) ((0 : Int)) (1)) <= m_pre)) ,
  (((0 : Int) + (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) ((0 : Int)) (1))) = (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) ((0 : Int)) (1)))

noncomputable def solver_entail_wit_7_split_goal_4 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (factor_count_2 : Int) (pr_values_2 : (List Int)) (pe_values_2 : (List Int)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre)) (PreH6 : ((0 : Int) <= factor_count_2)) (PreH7 : (factor_count_2 <= 64)) (PreH8 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH9 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH10 : (ValidFactorTable m_pre pr_values_2 pe_values_2)) (PreH11 : (PrefixChoice pr_values_2 pe_values_2 x_pre (0 : Int) 1 1 1)) (PreH12 : ((0 : Int) <= (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) ((0 : Int)) (1)))) (PreH13 : ((WalkSuffix (pr_values_2) (pe_values_2) (x_pre) ((0 : Int)) (1)) <= m_pre)) ,
  (((0 : Int) + (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) ((0 : Int)) (1))) = (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) ((0 : Int)) (1)))

noncomputable def solver_entail_wit_7_split_goal_5 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (factor_count_2 : Int) (pr_values_2 : (List Int)) (pe_values_2 : (List Int)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre)) (PreH6 : ((0 : Int) <= factor_count_2)) (PreH7 : (factor_count_2 <= 64)) (PreH8 : ((Zlength (pr_values_2)) = factor_count_2)) (PreH9 : ((Zlength (pe_values_2)) = factor_count_2)) (PreH10 : (ValidFactorTable m_pre pr_values_2 pe_values_2)) (PreH11 : (PrefixChoice pr_values_2 pe_values_2 x_pre (0 : Int) 1 1 1)) (PreH12 : ((0 : Int) <= (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) ((0 : Int)) (1)))) (PreH13 : ((WalkSuffix (pr_values_2) (pe_values_2) (x_pre) ((0 : Int)) (1)) <= m_pre)) ,
  (((0 : Int) + (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) ((0 : Int)) (1))) = (WalkSuffix (pr_values_2) (pe_values_2) (x_pre) ((0 : Int)) (1)))

noncomputable def solver_return_wit_1 : Prop :=
  (
forall (x_pre : Int) (m_pre : Int) (factor_count_2 : Int) (accumulator_2 : Int) (pr_values : (List Int)) (pe_values : (List Int)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre)) (PreH6 : ((0 : Int) <= factor_count_2)) (PreH7 : (factor_count_2 <= 64)) (PreH8 : ((Zlength (pr_values)) = factor_count_2)) (PreH9 : ((Zlength (pe_values)) = factor_count_2)) (PreH10 : (ValidFactorTable m_pre pr_values pe_values)) (PreH11 : (accumulator_2 = (WalkSuffix (pr_values) (pe_values) (x_pre) ((0 : Int)) (1)))) (PreH12 : (CycleAnswer m_pre x_pre accumulator_2)) ,
  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count_2 pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count_2 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count_2 pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count_2 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count_2))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "total_" ) )) # UInt64 |-> (accumulator_2))
|--
  EX accumulator : Int, EX base : Int, EX factor_count : Int,
  “ (Spec m_pre x_pre (unsigned_last_nbits ((accumulator_2 + 1)) (64))) ” &&
  “ ((0 : Int) <= factor_count) ” &&
  “ (factor_count <= 64) ”
  &&  (uint64Array.seg_shape ( &( "pr" ) ) (0 : Int) factor_count)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg_shape ( &( "pe" ) ) (0 : Int) factor_count)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (base))
  ** ((( &( "total_" ) )) # UInt64 |-> (accumulator))
) \/
(
forall (x_pre : Int) (m_pre : Int) (factor_count_2 : Int) (accumulator_2 : Int) (pr_values : (List Int)) (pe_values : (List Int)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre)) (PreH6 : ((0 : Int) <= factor_count_2)) (PreH7 : (factor_count_2 <= 64)) (PreH8 : ((Zlength (pr_values)) = factor_count_2)) (PreH9 : ((Zlength (pe_values)) = factor_count_2)) (PreH10 : (ValidFactorTable m_pre pr_values pe_values)) (PreH11 : (accumulator_2 = (WalkSuffix (pr_values) (pe_values) (x_pre) ((0 : Int)) (1)))) (PreH12 : (CycleAnswer m_pre x_pre accumulator_2)) ,
  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count_2 pr_values)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count_2 pe_values)
|--
  “ (Spec m_pre x_pre (unsigned_last_nbits ((accumulator_2 + 1)) (64))) ”
  &&  (uint64Array.seg_shape ( &( "pr" ) ) (0 : Int) factor_count_2)
  ** (uint64Array.seg_shape ( &( "pe" ) ) (0 : Int) factor_count_2)
)

noncomputable def solver_return_wit_1_split_goal_1 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (factor_count_2 : Int) (accumulator_2 : Int) (pr_values : (List Int)) (pe_values : (List Int)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre)) (PreH6 : ((0 : Int) <= factor_count_2)) (PreH7 : (factor_count_2 <= 64)) (PreH8 : ((Zlength (pr_values)) = factor_count_2)) (PreH9 : ((Zlength (pe_values)) = factor_count_2)) (PreH10 : (ValidFactorTable m_pre pr_values pe_values)) (PreH11 : (accumulator_2 = (WalkSuffix (pr_values) (pe_values) (x_pre) ((0 : Int)) (1)))) (PreH12 : (CycleAnswer m_pre x_pre accumulator_2)) ,
  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count_2 pr_values)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count_2 pe_values)
|--
  “ (Spec m_pre x_pre (unsigned_last_nbits ((accumulator_2 + 1)) (64))) ”

noncomputable def solver_return_wit_1_split_goal_spatial : Prop :=
  forall (x_pre : Int) (m_pre : Int) (factor_count_2 : Int) (accumulator_2 : Int) (pr_values : (List Int)) (pe_values : (List Int)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre)) (PreH6 : ((0 : Int) <= factor_count_2)) (PreH7 : (factor_count_2 <= 64)) (PreH8 : ((Zlength (pr_values)) = factor_count_2)) (PreH9 : ((Zlength (pe_values)) = factor_count_2)) (PreH10 : (ValidFactorTable m_pre pr_values pe_values)) (PreH11 : (accumulator_2 = (WalkSuffix (pr_values) (pe_values) (x_pre) ((0 : Int)) (1)))) (PreH12 : (CycleAnswer m_pre x_pre accumulator_2)) ,
  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count_2 pr_values)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count_2 pe_values)
|--
  (uint64Array.seg_shape ( &( "pr" ) ) (0 : Int) factor_count_2)
  ** (uint64Array.seg_shape ( &( "pe" ) ) (0 : Int) factor_count_2)

noncomputable def solver_partial_solve_wit_1 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (remainder : Int) (pe_values : (List Int)) (pr_values : (List Int)) (factor_count : Int) (p : Int) (PreH1 : ((Z.rem remainder p) = (0 : Int))) (PreH2 : ((p * p) <= remainder)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100000000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre < m_pre)) (PreH7 : (Pre m_pre x_pre)) (PreH8 : (2 <= p)) (PreH9 : (p <= 10000001)) (PreH10 : ((0 : Int) <= factor_count)) (PreH11 : (factor_count < 64)) (PreH12 : ((Zlength (pr_values)) = factor_count)) (PreH13 : ((Zlength (pe_values)) = factor_count)) (PreH14 : ((0 : Int) < remainder)) (PreH15 : (remainder <= m_pre)) (PreH16 : (FactorMachineTrialState m_pre p remainder pr_values pe_values)) ,
  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |->_)
  ** ((( &( "total_" ) )) # UInt64 |->_)
|--
  “ ((Z.rem remainder p) = (0 : Int)) ” &&
  “ ((p * p) <= remainder) ” &&
  “ (2 <= m_pre) ” &&
  “ (m_pre <= 100000000000000) ” &&
  “ (1 <= x_pre) ” &&
  “ (x_pre < m_pre) ” &&
  “ (Pre m_pre x_pre) ” &&
  “ (2 <= p) ” &&
  “ (p <= 10000001) ” &&
  “ ((0 : Int) <= factor_count) ” &&
  “ (factor_count < 64) ” &&
  “ ((Zlength (pr_values)) = factor_count) ” &&
  “ ((Zlength (pe_values)) = factor_count) ” &&
  “ ((0 : Int) < remainder) ” &&
  “ (remainder <= m_pre) ” &&
  “ (FactorMachineTrialState m_pre p remainder pr_values pe_values) ”
  &&  (((( &( "pr" ) ) + (factor_count * sizeof(UINT64)))) # UInt64 |->_)
  ** (uint64Array.undef_seg ( &( "pr" ) ) (factor_count + 1) 64)
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |->_)
  ** ((( &( "total_" ) )) # UInt64 |->_)

noncomputable def solver_partial_solve_wit_2 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (remainder : Int) (pe_values : (List Int)) (pr_values : (List Int)) (factor_count : Int) (p : Int) (PreH1 : ((Z.rem remainder p) = (0 : Int))) (PreH2 : ((p * p) <= remainder)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100000000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre < m_pre)) (PreH7 : (Pre m_pre x_pre)) (PreH8 : (2 <= p)) (PreH9 : (p <= 10000001)) (PreH10 : ((0 : Int) <= factor_count)) (PreH11 : (factor_count < 64)) (PreH12 : ((Zlength (pr_values)) = factor_count)) (PreH13 : ((Zlength (pe_values)) = factor_count)) (PreH14 : ((0 : Int) < remainder)) (PreH15 : (remainder <= m_pre)) (PreH16 : (FactorMachineTrialState m_pre p remainder pr_values pe_values)) ,
  (uint64Array.seg ( &( "pr" ) ) (0 : Int) (factor_count + 1) (pr_values ++ (p :: (@List.nil Int))))
  ** (uint64Array.undef_seg ( &( "pr" ) ) (factor_count + 1) 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |->_)
  ** ((( &( "total_" ) )) # UInt64 |->_)
|--
  “ ((Z.rem remainder p) = (0 : Int)) ” &&
  “ ((p * p) <= remainder) ” &&
  “ (2 <= m_pre) ” &&
  “ (m_pre <= 100000000000000) ” &&
  “ (1 <= x_pre) ” &&
  “ (x_pre < m_pre) ” &&
  “ (Pre m_pre x_pre) ” &&
  “ (2 <= p) ” &&
  “ (p <= 10000001) ” &&
  “ ((0 : Int) <= factor_count) ” &&
  “ (factor_count < 64) ” &&
  “ ((Zlength (pr_values)) = factor_count) ” &&
  “ ((Zlength (pe_values)) = factor_count) ” &&
  “ ((0 : Int) < remainder) ” &&
  “ (remainder <= m_pre) ” &&
  “ (FactorMachineTrialState m_pre p remainder pr_values pe_values) ”
  &&  (((( &( "pe" ) ) + (factor_count * sizeof(UINT64)))) # UInt64 |->_)
  ** (uint64Array.undef_seg ( &( "pe" ) ) (factor_count + 1) 64)
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) (factor_count + 1) (pr_values ++ (p :: (@List.nil Int))))
  ** (uint64Array.undef_seg ( &( "pr" ) ) (factor_count + 1) 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |->_)
  ** ((( &( "total_" ) )) # UInt64 |->_)

noncomputable def solver_partial_solve_wit_3 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (original_remainder : Int) (remainder : Int) (exponent : Int) (pe_values : (List Int)) (pr_values : (List Int)) (factor_count : Int) (p : Int) (PreH1 : ((Z.rem remainder p) = (0 : Int))) (PreH2 : (2 <= m_pre)) (PreH3 : (m_pre <= 100000000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre < m_pre)) (PreH6 : (Pre m_pre x_pre)) (PreH7 : (2 <= p)) (PreH8 : (p <= 10000000)) (PreH9 : ((0 : Int) <= factor_count)) (PreH10 : (factor_count < 64)) (PreH11 : ((Zlength (pr_values)) = factor_count)) (PreH12 : ((Zlength (pe_values)) = factor_count)) (PreH13 : ((0 : Int) <= exponent)) (PreH14 : (exponent <= 47)) (PreH15 : (FactorMachineAtPrime m_pre p original_remainder remainder exponent pr_values pe_values)) ,
  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.seg ( &( "pr" ) ) factor_count (factor_count + 1) (p :: (@List.nil Int)))
  ** (uint64Array.undef_seg ( &( "pr" ) ) (factor_count + 1) 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.seg ( &( "pe" ) ) factor_count (factor_count + 1) (exponent :: (@List.nil Int)))
  ** (uint64Array.undef_seg ( &( "pe" ) ) (factor_count + 1) 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |->_)
  ** ((( &( "total_" ) )) # UInt64 |->_)
|--
  “ ((Z.rem remainder p) = (0 : Int)) ” &&
  “ (2 <= m_pre) ” &&
  “ (m_pre <= 100000000000000) ” &&
  “ (1 <= x_pre) ” &&
  “ (x_pre < m_pre) ” &&
  “ (Pre m_pre x_pre) ” &&
  “ (2 <= p) ” &&
  “ (p <= 10000000) ” &&
  “ ((0 : Int) <= factor_count) ” &&
  “ (factor_count < 64) ” &&
  “ ((Zlength (pr_values)) = factor_count) ” &&
  “ ((Zlength (pe_values)) = factor_count) ” &&
  “ ((0 : Int) <= exponent) ” &&
  “ (exponent <= 47) ” &&
  “ (FactorMachineAtPrime m_pre p original_remainder remainder exponent pr_values pe_values) ”
  &&  (((( &( "pe" ) ) + (factor_count * sizeof(UINT64)))) # UInt64 |-> ((Znth (factor_count - factor_count) (exponent :: (@List.nil Int)) (0 : Int))))
  ** (uint64Array.missing_i ( &( "pe" ) ) factor_count factor_count (factor_count + 1) (exponent :: (@List.nil Int)))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.seg ( &( "pr" ) ) factor_count (factor_count + 1) (p :: (@List.nil Int)))
  ** (uint64Array.undef_seg ( &( "pr" ) ) (factor_count + 1) 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) (factor_count + 1) 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |->_)
  ** ((( &( "total_" ) )) # UInt64 |->_)

noncomputable def solver_partial_solve_wit_4 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (original_remainder : Int) (remainder : Int) (exponent : Int) (pe_values : (List Int)) (pr_values : (List Int)) (factor_count : Int) (p : Int) (PreH1 : ((Z.rem remainder p) = (0 : Int))) (PreH2 : (2 <= m_pre)) (PreH3 : (m_pre <= 100000000000000)) (PreH4 : (1 <= x_pre)) (PreH5 : (x_pre < m_pre)) (PreH6 : (Pre m_pre x_pre)) (PreH7 : (2 <= p)) (PreH8 : (p <= 10000000)) (PreH9 : ((0 : Int) <= factor_count)) (PreH10 : (factor_count < 64)) (PreH11 : ((Zlength (pr_values)) = factor_count)) (PreH12 : ((Zlength (pe_values)) = factor_count)) (PreH13 : ((0 : Int) <= exponent)) (PreH14 : (exponent <= 47)) (PreH15 : (FactorMachineAtPrime m_pre p original_remainder remainder exponent pr_values pe_values)) ,
  (uint64Array.seg ( &( "pe" ) ) factor_count (factor_count + 1) (exponent :: (@List.nil Int)))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.seg ( &( "pr" ) ) factor_count (factor_count + 1) (p :: (@List.nil Int)))
  ** (uint64Array.undef_seg ( &( "pr" ) ) (factor_count + 1) 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) (factor_count + 1) 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |->_)
  ** ((( &( "total_" ) )) # UInt64 |->_)
|--
  “ ((Z.rem remainder p) = (0 : Int)) ” &&
  “ (2 <= m_pre) ” &&
  “ (m_pre <= 100000000000000) ” &&
  “ (1 <= x_pre) ” &&
  “ (x_pre < m_pre) ” &&
  “ (Pre m_pre x_pre) ” &&
  “ (2 <= p) ” &&
  “ (p <= 10000000) ” &&
  “ ((0 : Int) <= factor_count) ” &&
  “ (factor_count < 64) ” &&
  “ ((Zlength (pr_values)) = factor_count) ” &&
  “ ((Zlength (pe_values)) = factor_count) ” &&
  “ ((0 : Int) <= exponent) ” &&
  “ (exponent <= 47) ” &&
  “ (FactorMachineAtPrime m_pre p original_remainder remainder exponent pr_values pe_values) ”
  &&  (((( &( "pe" ) ) + (factor_count * sizeof(UINT64)))) # UInt64 |->_)
  ** (uint64Array.missing_i ( &( "pe" ) ) factor_count factor_count (factor_count + 1) (exponent :: (@List.nil Int)))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.seg ( &( "pr" ) ) factor_count (factor_count + 1) (p :: (@List.nil Int)))
  ** (uint64Array.undef_seg ( &( "pr" ) ) (factor_count + 1) 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) (factor_count + 1) 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |->_)
  ** ((( &( "total_" ) )) # UInt64 |->_)

noncomputable def solver_partial_solve_wit_5 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (remainder : Int) (pe_values : (List Int)) (pr_values : (List Int)) (factor_count : Int) (p : Int) (PreH1 : (remainder > 1)) (PreH2 : ((p * p) > remainder)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100000000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre < m_pre)) (PreH7 : (Pre m_pre x_pre)) (PreH8 : (2 <= p)) (PreH9 : (p <= 10000001)) (PreH10 : ((0 : Int) <= factor_count)) (PreH11 : (factor_count < 64)) (PreH12 : ((Zlength (pr_values)) = factor_count)) (PreH13 : ((Zlength (pe_values)) = factor_count)) (PreH14 : ((0 : Int) < remainder)) (PreH15 : (remainder <= m_pre)) (PreH16 : (FactorMachineTrialState m_pre p remainder pr_values pe_values)) ,
  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |->_)
  ** ((( &( "total_" ) )) # UInt64 |->_)
|--
  “ (remainder > 1) ” &&
  “ ((p * p) > remainder) ” &&
  “ (2 <= m_pre) ” &&
  “ (m_pre <= 100000000000000) ” &&
  “ (1 <= x_pre) ” &&
  “ (x_pre < m_pre) ” &&
  “ (Pre m_pre x_pre) ” &&
  “ (2 <= p) ” &&
  “ (p <= 10000001) ” &&
  “ ((0 : Int) <= factor_count) ” &&
  “ (factor_count < 64) ” &&
  “ ((Zlength (pr_values)) = factor_count) ” &&
  “ ((Zlength (pe_values)) = factor_count) ” &&
  “ ((0 : Int) < remainder) ” &&
  “ (remainder <= m_pre) ” &&
  “ (FactorMachineTrialState m_pre p remainder pr_values pe_values) ”
  &&  (((( &( "pr" ) ) + (factor_count * sizeof(UINT64)))) # UInt64 |->_)
  ** (uint64Array.undef_seg ( &( "pr" ) ) (factor_count + 1) 64)
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |->_)
  ** ((( &( "total_" ) )) # UInt64 |->_)

noncomputable def solver_partial_solve_wit_6 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (remainder : Int) (pe_values : (List Int)) (pr_values : (List Int)) (factor_count : Int) (p : Int) (PreH1 : (remainder > 1)) (PreH2 : ((p * p) > remainder)) (PreH3 : (2 <= m_pre)) (PreH4 : (m_pre <= 100000000000000)) (PreH5 : (1 <= x_pre)) (PreH6 : (x_pre < m_pre)) (PreH7 : (Pre m_pre x_pre)) (PreH8 : (2 <= p)) (PreH9 : (p <= 10000001)) (PreH10 : ((0 : Int) <= factor_count)) (PreH11 : (factor_count < 64)) (PreH12 : ((Zlength (pr_values)) = factor_count)) (PreH13 : ((Zlength (pe_values)) = factor_count)) (PreH14 : ((0 : Int) < remainder)) (PreH15 : (remainder <= m_pre)) (PreH16 : (FactorMachineTrialState m_pre p remainder pr_values pe_values)) ,
  (uint64Array.seg ( &( "pr" ) ) (0 : Int) (factor_count + 1) (pr_values ++ (remainder :: (@List.nil Int))))
  ** (uint64Array.undef_seg ( &( "pr" ) ) (factor_count + 1) 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |->_)
  ** ((( &( "total_" ) )) # UInt64 |->_)
|--
  “ (remainder > 1) ” &&
  “ ((p * p) > remainder) ” &&
  “ (2 <= m_pre) ” &&
  “ (m_pre <= 100000000000000) ” &&
  “ (1 <= x_pre) ” &&
  “ (x_pre < m_pre) ” &&
  “ (Pre m_pre x_pre) ” &&
  “ (2 <= p) ” &&
  “ (p <= 10000001) ” &&
  “ ((0 : Int) <= factor_count) ” &&
  “ (factor_count < 64) ” &&
  “ ((Zlength (pr_values)) = factor_count) ” &&
  “ ((Zlength (pe_values)) = factor_count) ” &&
  “ ((0 : Int) < remainder) ” &&
  “ (remainder <= m_pre) ” &&
  “ (FactorMachineTrialState m_pre p remainder pr_values pe_values) ”
  &&  (((( &( "pe" ) ) + (factor_count * sizeof(UINT64)))) # UInt64 |->_)
  ** (uint64Array.undef_seg ( &( "pe" ) ) (factor_count + 1) 64)
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) (factor_count + 1) (pr_values ++ (remainder :: (@List.nil Int))))
  ** (uint64Array.undef_seg ( &( "pr" ) ) (factor_count + 1) 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |->_)
  ** ((( &( "total_" ) )) # UInt64 |->_)

noncomputable def solver_partial_solve_wit_7_pure : Prop :=
  (
forall (x_pre : Int) (m_pre : Int) (factor_count : Int) (remainder : Int) (pr_values : (List Int)) (pe_values : (List Int)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre)) (PreH6 : ((0 : Int) <= factor_count)) (PreH7 : (factor_count <= 64)) (PreH8 : ((Zlength (pr_values)) = factor_count)) (PreH9 : ((Zlength (pe_values)) = factor_count)) (PreH10 : (ValidFactorTable m_pre pr_values pe_values)) (PreH11 : (PrefixChoice pr_values pe_values x_pre (0 : Int) 1 1 1)) (PreH12 : ((0 : Int) <= (WalkSuffix (pr_values) (pe_values) (x_pre) ((0 : Int)) (1)))) (PreH13 : ((WalkSuffix (pr_values) (pe_values) (x_pre) ((0 : Int)) (1)) <= m_pre)) ,
  ((( &( "m" ) )) # UInt64 |-> (m_pre))
  ** ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "t" ) )) # UInt64 |-> (remainder))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "total_" ) )) # UInt64 |-> ((0 : Int)))
|--
  “ ((Zlength (pr_values)) = factor_count) ” &&
  “ ((Zlength (pe_values)) = factor_count) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= factor_count) ” &&
  “ ((0 : Int) < 1) ” &&
  “ (ValidFactorTable m_pre pr_values pe_values) ” &&
  “ (PrefixChoice pr_values pe_values x_pre (0 : Int) 1 1 1) ” &&
  “ (WalkBudget m_pre (0 : Int) (WalkSuffix (pr_values) (pe_values) (x_pre) ((0 : Int)) (1))) ” &&
  “ (WalkMachineBounds m_pre 1 1 1) ” &&
  “ (WalkGlobalBounds m_pre x_pre) ”
) \/
(
forall (x_pre : Int) (m_pre : Int) (factor_count : Int) (remainder : Int) (pr_values : (List Int)) (pe_values : (List Int)) (PreH1 : ((0 : Int) <= 18446744073709551615)) (PreH2 : (remainder <= 18446744073709551615)) (PreH3 : (x_pre <= 18446744073709551615)) (PreH4 : (m_pre <= 18446744073709551615)) (PreH5 : ((0 : Int) >= (0 : Int))) (PreH6 : (remainder >= (0 : Int))) (PreH7 : (x_pre >= (0 : Int))) (PreH8 : (m_pre >= (0 : Int))) (PreH9 : (factor_count <= INT_MAX)) (PreH10 : (factor_count >= INT_MIN)) (PreH11 : (2 <= m_pre)) (PreH12 : (m_pre <= 100000000000000)) (PreH13 : (1 <= x_pre)) (PreH14 : (x_pre < m_pre)) (PreH15 : (Pre m_pre x_pre)) (PreH16 : ((0 : Int) <= factor_count)) (PreH17 : (factor_count <= 64)) (PreH18 : ((Zlength (pr_values)) = factor_count)) (PreH19 : ((Zlength (pe_values)) = factor_count)) (PreH20 : (ValidFactorTable m_pre pr_values pe_values)) (PreH21 : (PrefixChoice pr_values pe_values x_pre (0 : Int) 1 1 1)) (PreH22 : ((0 : Int) <= (WalkSuffix (pr_values) (pe_values) (x_pre) ((0 : Int)) (1)))) (PreH23 : ((WalkSuffix (pr_values) (pe_values) (x_pre) ((0 : Int)) (1)) <= m_pre)) ,
  ((( &( "m" ) )) # UInt64 |-> (m_pre))
  ** ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "t" ) )) # UInt64 |-> (remainder))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "total_" ) )) # UInt64 |-> ((0 : Int)))
|--
  “ (WalkGlobalBounds m_pre x_pre) ” &&
  “ (WalkMachineBounds m_pre 1 1 1) ” &&
  “ (WalkBudget m_pre (0 : Int) (WalkSuffix (pr_values) (pe_values) (x_pre) ((0 : Int)) (1))) ”
)

noncomputable def solver_partial_solve_wit_7_pure_split_goal_1 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (factor_count : Int) (remainder : Int) (pr_values : (List Int)) (pe_values : (List Int)) (PreH1 : ((0 : Int) <= 18446744073709551615)) (PreH2 : (remainder <= 18446744073709551615)) (PreH3 : (x_pre <= 18446744073709551615)) (PreH4 : (m_pre <= 18446744073709551615)) (PreH5 : ((0 : Int) >= (0 : Int))) (PreH6 : (remainder >= (0 : Int))) (PreH7 : (x_pre >= (0 : Int))) (PreH8 : (m_pre >= (0 : Int))) (PreH9 : (factor_count <= INT_MAX)) (PreH10 : (factor_count >= INT_MIN)) (PreH11 : (2 <= m_pre)) (PreH12 : (m_pre <= 100000000000000)) (PreH13 : (1 <= x_pre)) (PreH14 : (x_pre < m_pre)) (PreH15 : (Pre m_pre x_pre)) (PreH16 : ((0 : Int) <= factor_count)) (PreH17 : (factor_count <= 64)) (PreH18 : ((Zlength (pr_values)) = factor_count)) (PreH19 : ((Zlength (pe_values)) = factor_count)) (PreH20 : (ValidFactorTable m_pre pr_values pe_values)) (PreH21 : (PrefixChoice pr_values pe_values x_pre (0 : Int) 1 1 1)) (PreH22 : ((0 : Int) <= (WalkSuffix (pr_values) (pe_values) (x_pre) ((0 : Int)) (1)))) (PreH23 : ((WalkSuffix (pr_values) (pe_values) (x_pre) ((0 : Int)) (1)) <= m_pre)) ,
  ((( &( "m" ) )) # UInt64 |-> (m_pre))
  ** ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "t" ) )) # UInt64 |-> (remainder))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "total_" ) )) # UInt64 |-> ((0 : Int)))
|--
  “ (WalkGlobalBounds m_pre x_pre) ”

noncomputable def solver_partial_solve_wit_7_pure_split_goal_2 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (factor_count : Int) (remainder : Int) (pr_values : (List Int)) (pe_values : (List Int)) (PreH1 : ((0 : Int) <= 18446744073709551615)) (PreH2 : (remainder <= 18446744073709551615)) (PreH3 : (x_pre <= 18446744073709551615)) (PreH4 : (m_pre <= 18446744073709551615)) (PreH5 : ((0 : Int) >= (0 : Int))) (PreH6 : (remainder >= (0 : Int))) (PreH7 : (x_pre >= (0 : Int))) (PreH8 : (m_pre >= (0 : Int))) (PreH9 : (factor_count <= INT_MAX)) (PreH10 : (factor_count >= INT_MIN)) (PreH11 : (2 <= m_pre)) (PreH12 : (m_pre <= 100000000000000)) (PreH13 : (1 <= x_pre)) (PreH14 : (x_pre < m_pre)) (PreH15 : (Pre m_pre x_pre)) (PreH16 : ((0 : Int) <= factor_count)) (PreH17 : (factor_count <= 64)) (PreH18 : ((Zlength (pr_values)) = factor_count)) (PreH19 : ((Zlength (pe_values)) = factor_count)) (PreH20 : (ValidFactorTable m_pre pr_values pe_values)) (PreH21 : (PrefixChoice pr_values pe_values x_pre (0 : Int) 1 1 1)) (PreH22 : ((0 : Int) <= (WalkSuffix (pr_values) (pe_values) (x_pre) ((0 : Int)) (1)))) (PreH23 : ((WalkSuffix (pr_values) (pe_values) (x_pre) ((0 : Int)) (1)) <= m_pre)) ,
  ((( &( "m" ) )) # UInt64 |-> (m_pre))
  ** ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "t" ) )) # UInt64 |-> (remainder))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "total_" ) )) # UInt64 |-> ((0 : Int)))
|--
  “ (WalkMachineBounds m_pre 1 1 1) ”

noncomputable def solver_partial_solve_wit_7_pure_split_goal_3 : Prop :=
  forall (x_pre : Int) (m_pre : Int) (factor_count : Int) (remainder : Int) (pr_values : (List Int)) (pe_values : (List Int)) (PreH1 : ((0 : Int) <= 18446744073709551615)) (PreH2 : (remainder <= 18446744073709551615)) (PreH3 : (x_pre <= 18446744073709551615)) (PreH4 : (m_pre <= 18446744073709551615)) (PreH5 : ((0 : Int) >= (0 : Int))) (PreH6 : (remainder >= (0 : Int))) (PreH7 : (x_pre >= (0 : Int))) (PreH8 : (m_pre >= (0 : Int))) (PreH9 : (factor_count <= INT_MAX)) (PreH10 : (factor_count >= INT_MIN)) (PreH11 : (2 <= m_pre)) (PreH12 : (m_pre <= 100000000000000)) (PreH13 : (1 <= x_pre)) (PreH14 : (x_pre < m_pre)) (PreH15 : (Pre m_pre x_pre)) (PreH16 : ((0 : Int) <= factor_count)) (PreH17 : (factor_count <= 64)) (PreH18 : ((Zlength (pr_values)) = factor_count)) (PreH19 : ((Zlength (pe_values)) = factor_count)) (PreH20 : (ValidFactorTable m_pre pr_values pe_values)) (PreH21 : (PrefixChoice pr_values pe_values x_pre (0 : Int) 1 1 1)) (PreH22 : ((0 : Int) <= (WalkSuffix (pr_values) (pe_values) (x_pre) ((0 : Int)) (1)))) (PreH23 : ((WalkSuffix (pr_values) (pe_values) (x_pre) ((0 : Int)) (1)) <= m_pre)) ,
  ((( &( "m" ) )) # UInt64 |-> (m_pre))
  ** ((( &( "x" ) )) # UInt64 |-> (x_pre))
  ** (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "t" ) )) # UInt64 |-> (remainder))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "total_" ) )) # UInt64 |-> ((0 : Int)))
|--
  “ (WalkBudget m_pre (0 : Int) (WalkSuffix (pr_values) (pe_values) (x_pre) ((0 : Int)) (1))) ”

noncomputable def solver_partial_solve_wit_7_aux : Prop :=
  forall (x_pre : Int) (m_pre : Int) (factor_count : Int) (pr_values : (List Int)) (pe_values : (List Int)) (PreH1 : (2 <= m_pre)) (PreH2 : (m_pre <= 100000000000000)) (PreH3 : (1 <= x_pre)) (PreH4 : (x_pre < m_pre)) (PreH5 : (Pre m_pre x_pre)) (PreH6 : ((0 : Int) <= factor_count)) (PreH7 : (factor_count <= 64)) (PreH8 : ((Zlength (pr_values)) = factor_count)) (PreH9 : ((Zlength (pe_values)) = factor_count)) (PreH10 : (ValidFactorTable m_pre pr_values pe_values)) (PreH11 : (PrefixChoice pr_values pe_values x_pre (0 : Int) 1 1 1)) (PreH12 : ((0 : Int) <= (WalkSuffix (pr_values) (pe_values) (x_pre) ((0 : Int)) (1)))) (PreH13 : ((WalkSuffix (pr_values) (pe_values) (x_pre) ((0 : Int)) (1)) <= m_pre)) ,
  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "total_" ) )) # UInt64 |-> ((0 : Int)))
|--
  “ ((Zlength (pr_values)) = factor_count) ” &&
  “ ((Zlength (pe_values)) = factor_count) ” &&
  “ ((0 : Int) <= (0 : Int)) ” &&
  “ ((0 : Int) <= factor_count) ” &&
  “ ((0 : Int) < 1) ” &&
  “ (ValidFactorTable m_pre pr_values pe_values) ” &&
  “ (PrefixChoice pr_values pe_values x_pre (0 : Int) 1 1 1) ” &&
  “ (WalkBudget m_pre (0 : Int) (WalkSuffix (pr_values) (pe_values) (x_pre) ((0 : Int)) (1))) ” &&
  “ (WalkMachineBounds m_pre 1 1 1) ” &&
  “ (WalkGlobalBounds m_pre x_pre) ” &&
  “ (2 <= m_pre) ” &&
  “ (m_pre <= 100000000000000) ” &&
  “ (1 <= x_pre) ” &&
  “ (x_pre < m_pre) ” &&
  “ (Pre m_pre x_pre) ” &&
  “ ((0 : Int) <= factor_count) ” &&
  “ (factor_count <= 64) ” &&
  “ ((Zlength (pr_values)) = factor_count) ” &&
  “ ((Zlength (pe_values)) = factor_count) ” &&
  “ (ValidFactorTable m_pre pr_values pe_values) ” &&
  “ (PrefixChoice pr_values pe_values x_pre (0 : Int) 1 1 1) ” &&
  “ ((0 : Int) <= (WalkSuffix (pr_values) (pe_values) (x_pre) ((0 : Int)) (1))) ” &&
  “ ((WalkSuffix (pr_values) (pe_values) (x_pre) ((0 : Int)) (1)) <= m_pre) ”
  &&  (uint64Array.seg ( &( "pr" ) ) (0 : Int) factor_count pr_values)
  ** (uint64Array.undef_seg ( &( "pr" ) ) factor_count 64)
  ** (uint64Array.seg ( &( "pe" ) ) (0 : Int) factor_count pe_values)
  ** (uint64Array.undef_seg ( &( "pe" ) ) factor_count 64)
  ** ((( &( "nf" ) )) # Int |-> (factor_count))
  ** ((( &( "x_" ) )) # UInt64 |-> (x_pre))
  ** ((( &( "total_" ) )) # UInt64 |-> ((0 : Int)))

noncomputable def solver_partial_solve_wit_7 : Prop := solver_partial_solve_wit_7_pure -> solver_partial_solve_wit_7_aux


structure VC_Correct : Type where
  proof_of_mulmod_safety_wit_1 : mulmod_safety_wit_1
  proof_of_mulmod_safety_wit_2 : mulmod_safety_wit_2
  proof_of_mulmod_safety_wit_3 : mulmod_safety_wit_3
  proof_of_mulmod_safety_wit_4 : mulmod_safety_wit_4
  proof_of_mulmod_safety_wit_5 : mulmod_safety_wit_5
  proof_of_mulmod_safety_wit_6 : mulmod_safety_wit_6
  proof_of_mulmod_safety_wit_7 : mulmod_safety_wit_7
  proof_of_mulmod_safety_wit_8 : mulmod_safety_wit_8
  proof_of_mulmod_safety_wit_9 : mulmod_safety_wit_9
  proof_of_mulmod_safety_wit_10 : mulmod_safety_wit_10
  proof_of_mulmod_safety_wit_11 : mulmod_safety_wit_11
  proof_of_mulmod_safety_wit_12 : mulmod_safety_wit_12
  proof_of_mulmod_safety_wit_13 : mulmod_safety_wit_13
  proof_of_mulmod_safety_wit_14 : mulmod_safety_wit_14
  proof_of_mulmod_safety_wit_15 : mulmod_safety_wit_15
  proof_of_mulmod_safety_wit_16 : mulmod_safety_wit_16
  proof_of_mulmod_safety_wit_17 : mulmod_safety_wit_17
  proof_of_mulmod_safety_wit_18 : mulmod_safety_wit_18
  proof_of_mulmod_safety_wit_19 : mulmod_safety_wit_19
  proof_of_mulmod_safety_wit_20 : mulmod_safety_wit_20
  proof_of_mulmod_safety_wit_21 : mulmod_safety_wit_21
  proof_of_mulmod_safety_wit_22 : mulmod_safety_wit_22
  proof_of_powmod_safety_wit_1 : powmod_safety_wit_1
  proof_of_powmod_safety_wit_2 : powmod_safety_wit_2
  proof_of_powmod_safety_wit_3 : powmod_safety_wit_3
  proof_of_powmod_safety_wit_4 : powmod_safety_wit_4
  proof_of_powmod_safety_wit_5 : powmod_safety_wit_5
  proof_of_powmod_safety_wit_6 : powmod_safety_wit_6
  proof_of_powmod_safety_wit_7 : powmod_safety_wit_7
  proof_of_powmod_safety_wit_8 : powmod_safety_wit_8
  proof_of_powmod_partial_solve_wit_1_pure : powmod_partial_solve_wit_1_pure
  proof_of_powmod_partial_solve_wit_1 : powmod_partial_solve_wit_1
  proof_of_powmod_partial_solve_wit_2_pure : powmod_partial_solve_wit_2_pure
  proof_of_powmod_partial_solve_wit_2 : powmod_partial_solve_wit_2
  proof_of_powmod_partial_solve_wit_3_pure : powmod_partial_solve_wit_3_pure
  proof_of_powmod_partial_solve_wit_3 : powmod_partial_solve_wit_3
  proof_of_gcd__safety_wit_1 : gcd__safety_wit_1
  proof_of_order_safety_wit_1 : order_safety_wit_1
  proof_of_order_safety_wit_2 : order_safety_wit_2
  proof_of_order_safety_wit_3 : order_safety_wit_3
  proof_of_order_safety_wit_4 : order_safety_wit_4
  proof_of_order_safety_wit_5 : order_safety_wit_5
  proof_of_order_safety_wit_6 : order_safety_wit_6
  proof_of_order_safety_wit_7 : order_safety_wit_7
  proof_of_order_safety_wit_8 : order_safety_wit_8
  proof_of_order_safety_wit_9 : order_safety_wit_9
  proof_of_order_safety_wit_10 : order_safety_wit_10
  proof_of_order_safety_wit_11 : order_safety_wit_11
  proof_of_order_safety_wit_12 : order_safety_wit_12
  proof_of_order_safety_wit_13 : order_safety_wit_13
  proof_of_order_safety_wit_14 : order_safety_wit_14
  proof_of_order_safety_wit_15 : order_safety_wit_15
  proof_of_order_safety_wit_16 : order_safety_wit_16
  proof_of_order_safety_wit_17 : order_safety_wit_17
  proof_of_order_safety_wit_18 : order_safety_wit_18
  proof_of_order_safety_wit_19 : order_safety_wit_19
  proof_of_order_partial_solve_wit_1 : order_partial_solve_wit_1
  proof_of_order_partial_solve_wit_2 : order_partial_solve_wit_2
  proof_of_walk_safety_wit_1 : walk_safety_wit_1
  proof_of_walk_safety_wit_2 : walk_safety_wit_2
  proof_of_walk_safety_wit_3 : walk_safety_wit_3
  proof_of_walk_safety_wit_4 : walk_safety_wit_4
  proof_of_walk_safety_wit_5 : walk_safety_wit_5
  proof_of_walk_safety_wit_6 : walk_safety_wit_6
  proof_of_walk_safety_wit_7 : walk_safety_wit_7
  proof_of_walk_safety_wit_8 : walk_safety_wit_8
  proof_of_walk_safety_wit_9 : walk_safety_wit_9
  proof_of_walk_safety_wit_11 : walk_safety_wit_11
  proof_of_walk_safety_wit_12 : walk_safety_wit_12
  proof_of_walk_safety_wit_13 : walk_safety_wit_13
  proof_of_walk_partial_solve_wit_1_pure : walk_partial_solve_wit_1_pure
  proof_of_walk_partial_solve_wit_1 : walk_partial_solve_wit_1
  proof_of_walk_partial_solve_wit_2 : walk_partial_solve_wit_2
  proof_of_walk_partial_solve_wit_3 : walk_partial_solve_wit_3
  proof_of_walk_partial_solve_wit_4 : walk_partial_solve_wit_4
  proof_of_walk_partial_solve_wit_5 : walk_partial_solve_wit_5
  proof_of_walk_partial_solve_wit_6 : walk_partial_solve_wit_6
  proof_of_solver_safety_wit_1 : solver_safety_wit_1
  proof_of_solver_safety_wit_2 : solver_safety_wit_2
  proof_of_solver_safety_wit_3 : solver_safety_wit_3
  proof_of_solver_safety_wit_4 : solver_safety_wit_4
  proof_of_solver_safety_wit_5 : solver_safety_wit_5
  proof_of_solver_safety_wit_6 : solver_safety_wit_6
  proof_of_solver_safety_wit_7 : solver_safety_wit_7
  proof_of_solver_safety_wit_8 : solver_safety_wit_8
  proof_of_solver_safety_wit_9 : solver_safety_wit_9
  proof_of_solver_safety_wit_10 : solver_safety_wit_10
  proof_of_solver_safety_wit_11 : solver_safety_wit_11
  proof_of_solver_safety_wit_12 : solver_safety_wit_12
  proof_of_solver_safety_wit_13 : solver_safety_wit_13
  proof_of_solver_safety_wit_14 : solver_safety_wit_14
  proof_of_solver_safety_wit_15 : solver_safety_wit_15
  proof_of_solver_safety_wit_16 : solver_safety_wit_16
  proof_of_solver_safety_wit_17 : solver_safety_wit_17
  proof_of_solver_safety_wit_18 : solver_safety_wit_18
  proof_of_solver_safety_wit_19 : solver_safety_wit_19
  proof_of_solver_partial_solve_wit_1 : solver_partial_solve_wit_1
  proof_of_solver_partial_solve_wit_2 : solver_partial_solve_wit_2
  proof_of_solver_partial_solve_wit_3 : solver_partial_solve_wit_3
  proof_of_solver_partial_solve_wit_4 : solver_partial_solve_wit_4
  proof_of_solver_partial_solve_wit_5 : solver_partial_solve_wit_5
  proof_of_solver_partial_solve_wit_6 : solver_partial_solve_wit_6
  proof_of_solver_partial_solve_wit_7 : solver_partial_solve_wit_7
  proof_of_mulmod_entail_wit_1 : mulmod_entail_wit_1
  proof_of_mulmod_entail_wit_2_1 : mulmod_entail_wit_2_1
  proof_of_mulmod_entail_wit_2_2 : mulmod_entail_wit_2_2
  proof_of_mulmod_entail_wit_2_3 : mulmod_entail_wit_2_3
  proof_of_mulmod_entail_wit_2_4 : mulmod_entail_wit_2_4
  proof_of_mulmod_entail_wit_2_5 : mulmod_entail_wit_2_5
  proof_of_mulmod_entail_wit_2_6 : mulmod_entail_wit_2_6
  proof_of_mulmod_return_wit_1 : mulmod_return_wit_1
  proof_of_powmod_entail_wit_1 : powmod_entail_wit_1
  proof_of_powmod_entail_wit_2_1 : powmod_entail_wit_2_1
  proof_of_powmod_entail_wit_2_2 : powmod_entail_wit_2_2
  proof_of_powmod_return_wit_1 : powmod_return_wit_1
  proof_of_gcd__entail_wit_1 : gcd__entail_wit_1
  proof_of_gcd__entail_wit_2 : gcd__entail_wit_2
  proof_of_gcd__return_wit_1 : gcd__return_wit_1
  proof_of_order_entail_wit_1 : order_entail_wit_1
  proof_of_order_entail_wit_2 : order_entail_wit_2
  proof_of_order_entail_wit_3 : order_entail_wit_3
  proof_of_order_entail_wit_4 : order_entail_wit_4
  proof_of_order_entail_wit_5 : order_entail_wit_5
  proof_of_order_entail_wit_6_1 : order_entail_wit_6_1
  proof_of_order_entail_wit_6_2 : order_entail_wit_6_2
  proof_of_order_entail_wit_6_3 : order_entail_wit_6_3
  proof_of_order_entail_wit_7 : order_entail_wit_7
  proof_of_order_entail_wit_8 : order_entail_wit_8
  proof_of_order_return_wit_1 : order_return_wit_1
  proof_of_order_return_wit_2 : order_return_wit_2
  proof_of_order_return_wit_3 : order_return_wit_3
  proof_of_order_return_wit_4 : order_return_wit_4
  proof_of_order_partial_solve_wit_1_pure : order_partial_solve_wit_1_pure
  proof_of_order_partial_solve_wit_2_pure : order_partial_solve_wit_2_pure
  proof_of_walk_safety_wit_10 : walk_safety_wit_10
  proof_of_walk_entail_wit_1 : walk_entail_wit_1
  proof_of_walk_entail_wit_2 : walk_entail_wit_2
  proof_of_walk_entail_wit_3 : walk_entail_wit_3
  proof_of_walk_entail_wit_4_1 : walk_entail_wit_4_1
  proof_of_walk_entail_wit_4_2 : walk_entail_wit_4_2
  proof_of_walk_entail_wit_5 : walk_entail_wit_5
  proof_of_walk_entail_wit_6 : walk_entail_wit_6
  proof_of_walk_return_wit_1 : walk_return_wit_1
  proof_of_walk_return_wit_2 : walk_return_wit_2
  proof_of_walk_return_wit_3 : walk_return_wit_3
  proof_of_walk_partial_solve_wit_4_pure : walk_partial_solve_wit_4_pure
  proof_of_walk_partial_solve_wit_5_pure : walk_partial_solve_wit_5_pure
  proof_of_walk_partial_solve_wit_6_pure : walk_partial_solve_wit_6_pure
  proof_of_solver_entail_wit_1 : solver_entail_wit_1
  proof_of_solver_entail_wit_2 : solver_entail_wit_2
  proof_of_solver_entail_wit_3 : solver_entail_wit_3
  proof_of_solver_entail_wit_4_1 : solver_entail_wit_4_1
  proof_of_solver_entail_wit_4_2 : solver_entail_wit_4_2
  proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1
  proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2
  proof_of_solver_entail_wit_6 : solver_entail_wit_6
  proof_of_solver_entail_wit_7 : solver_entail_wit_7
  proof_of_solver_return_wit_1 : solver_return_wit_1
  proof_of_solver_partial_solve_wit_7_pure : solver_partial_solve_wit_7_pure

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_goal
