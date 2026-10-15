import SimpleC.SL.LeanPrinterPrelude

import SimpleC.EE.LLM_bench.Algorithms.lucas_theorem.lucas_theorem_lib

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.lucas_theorem.lucas_theorem_goal

open AUXLib
open SimpleC.SL.CNotation
open SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig
open SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib
open SimpleC.SL.SeparationLogic
open scoped SimpleC.SL.SAC CoqZ

local instance lucas_theorem_goalSacContext : SacContext := ⟨naive_C_Rules⟩

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

noncomputable def binomial_digit_mod_prime_safety_wit_1 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (PreH1 : (lower_pre > upper_pre)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) ,
  ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
|--
  “ False ”

noncomputable def binomial_digit_mod_prime_safety_wit_2 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (PreH1 : (lower_pre <= upper_pre)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) ,
  ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
|--
  “ ((upper_pre - lower_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (upper_pre - lower_pre)) ”

noncomputable def binomial_digit_mod_prime_safety_wit_3 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (PreH1 : (lower_pre > (upper_pre - lower_pre))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre)) (PreH4 : ((0 : Int) <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) ,
  ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
|--
  “ ((upper_pre - lower_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (upper_pre - lower_pre)) ”

noncomputable def binomial_digit_mod_prime_safety_wit_4 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (PreH1 : (lower_pre > (upper_pre - lower_pre))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre)) (PreH4 : ((0 : Int) <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) ,
  ((( &( "numerator" ) )) # Int |->_)
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "lower" ) )) # Int |-> ((upper_pre - lower_pre)))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def binomial_digit_mod_prime_safety_wit_5 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (PreH1 : (lower_pre <= (upper_pre - lower_pre))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre)) (PreH4 : ((0 : Int) <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) ,
  ((( &( "numerator" ) )) # Int |->_)
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def binomial_digit_mod_prime_safety_wit_6 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (PreH1 : (lower_pre > (upper_pre - lower_pre))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre)) (PreH4 : ((0 : Int) <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) ,
  ((( &( "denominator" ) )) # Int |->_)
  ** ((( &( "numerator" ) )) # Int |-> (1))
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "lower" ) )) # Int |-> ((upper_pre - lower_pre)))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def binomial_digit_mod_prime_safety_wit_7 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (PreH1 : (lower_pre <= (upper_pre - lower_pre))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre)) (PreH4 : ((0 : Int) <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) ,
  ((( &( "denominator" ) )) # Int |->_)
  ** ((( &( "numerator" ) )) # Int |-> (1))
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def binomial_digit_mod_prime_safety_wit_8 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (PreH1 : (lower_pre > (upper_pre - lower_pre))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre)) (PreH4 : ((0 : Int) <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "denominator" ) )) # Int |-> (1))
  ** ((( &( "numerator" ) )) # Int |-> (1))
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "lower" ) )) # Int |-> ((upper_pre - lower_pre)))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def binomial_digit_mod_prime_safety_wit_9 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (PreH1 : (lower_pre <= (upper_pre - lower_pre))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre)) (PreH4 : ((0 : Int) <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) ,
  ((( &( "i" ) )) # Int |->_)
  ** ((( &( "denominator" ) )) # Int |-> (1))
  ** ((( &( "numerator" ) )) # Int |-> (1))
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def binomial_digit_mod_prime_safety_wit_10 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (lower : Int) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = ((min (α := Int)) (lower_pre) ((upper_pre - lower_pre))))) (PreH9 : ((0 : Int) <= lower)) (PreH10 : (lower <= (upper_pre - lower))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower + 1))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator)) ,
  ((( &( "factor" ) )) # Int |->_)
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ (((upper_pre - lower) + i) <= INT_MAX) ” &&
  “ ((INT_MIN) <= ((upper_pre - lower) + i)) ”

noncomputable def binomial_digit_mod_prime_safety_wit_11 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (lower : Int) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = ((min (α := Int)) (lower_pre) ((upper_pre - lower_pre))))) (PreH9 : ((0 : Int) <= lower)) (PreH10 : (lower <= (upper_pre - lower))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower + 1))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator)) ,
  ((( &( "factor" ) )) # Int |->_)
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ ((upper_pre - lower) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (upper_pre - lower)) ”

noncomputable def binomial_digit_mod_prime_safety_wit_12 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (lower : Int) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = ((min (α := Int)) (lower_pre) ((upper_pre - lower_pre))))) (PreH9 : ((0 : Int) <= lower)) (PreH10 : (lower <= (upper_pre - lower))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower + 1))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator)) ,
  ((( &( "numerator_product" ) )) # Int64 |->_)
  ** ((( &( "factor" ) )) # Int |-> (((upper_pre - lower) + i)))
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ ((numerator * ((upper_pre - lower) + i)) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (numerator * ((upper_pre - lower) + i))) ”

noncomputable def binomial_digit_mod_prime_safety_wit_13 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (lower : Int) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = ((min (α := Int)) (lower_pre) ((upper_pre - lower_pre))))) (PreH9 : ((0 : Int) <= lower)) (PreH10 : (lower <= (upper_pre - lower))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower + 1))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator)) ,
  ((( &( "denominator_product" ) )) # Int64 |->_)
  ** ((( &( "numerator_product" ) )) # Int64 |-> ((numerator * ((upper_pre - lower) + i))))
  ** ((( &( "factor" ) )) # Int |-> (((upper_pre - lower) + i)))
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ ((denominator * i) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (denominator * i)) ”

noncomputable def binomial_digit_mod_prime_safety_wit_14 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (lower : Int) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = ((min (α := Int)) (lower_pre) ((upper_pre - lower_pre))))) (PreH9 : ((0 : Int) <= lower)) (PreH10 : (lower <= (upper_pre - lower))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower + 1))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator)) ,
  ((( &( "denominator_product" ) )) # Int64 |-> ((denominator * i)))
  ** ((( &( "numerator_product" ) )) # Int64 |-> ((numerator * ((upper_pre - lower) + i))))
  ** ((( &( "factor" ) )) # Int |-> (((upper_pre - lower) + i)))
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ (((numerator * ((upper_pre - lower) + i)) ≠ (-9223372036854775808)) ∨ (prime_pre ≠ (-1))) ” &&
  “ (prime_pre ≠ (0 : Int)) ”

noncomputable def binomial_digit_mod_prime_safety_wit_15 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (lower : Int) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = ((min (α := Int)) (lower_pre) ((upper_pre - lower_pre))))) (PreH9 : ((0 : Int) <= lower)) (PreH10 : (lower <= (upper_pre - lower))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower + 1))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator)) ,
  ((( &( "denominator_product" ) )) # Int64 |-> ((denominator * i)))
  ** ((( &( "numerator_product" ) )) # Int64 |-> ((numerator * ((upper_pre - lower) + i))))
  ** ((( &( "factor" ) )) # Int |-> (((upper_pre - lower) + i)))
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "numerator" ) )) # Int |-> ((signed_last_nbits ((Z.rem (numerator * ((upper_pre - lower) + i)) prime_pre)) (32))))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ (((denominator * i) ≠ (-9223372036854775808)) ∨ (prime_pre ≠ (-1))) ” &&
  “ (prime_pre ≠ (0 : Int)) ”

noncomputable def binomial_digit_mod_prime_safety_wit_16 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (lower : Int) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = ((min (α := Int)) (lower_pre) ((upper_pre - lower_pre))))) (PreH9 : ((0 : Int) <= lower)) (PreH10 : (lower <= (upper_pre - lower))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower + 1))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator)) ,
  ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "i" ) )) # Int |-> (i))
  ** ((( &( "numerator" ) )) # Int |-> ((signed_last_nbits ((Z.rem (numerator * ((upper_pre - lower) + i)) prime_pre)) (32))))
  ** ((( &( "denominator" ) )) # Int |-> ((signed_last_nbits ((Z.rem (denominator * i) prime_pre)) (32))))
|--
  “ ((i + 1) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (i + 1)) ”

noncomputable def binomial_digit_mod_prime_safety_wit_17 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (lower : Int) (PreH1 : (i > lower)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = ((min (α := Int)) (lower_pre) ((upper_pre - lower_pre))))) (PreH9 : ((0 : Int) <= lower)) (PreH10 : (lower <= (upper_pre - lower))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower + 1))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator)) ,
  ((( &( "inverse" ) )) # Int |->_)
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ ((prime_pre - 2) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (prime_pre - 2)) ”

noncomputable def binomial_digit_mod_prime_safety_wit_18 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (lower : Int) (PreH1 : (i > lower)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = ((min (α := Int)) (lower_pre) ((upper_pre - lower_pre))))) (PreH9 : ((0 : Int) <= lower)) (PreH10 : (lower <= (upper_pre - lower))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower + 1))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator)) ,
  ((( &( "inverse" ) )) # Int |->_)
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ (2 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 2) ”

noncomputable def binomial_digit_mod_prime_safety_wit_19 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (lower : Int) (retval : Int) (PreH1 : (ModularPower denominator (prime_pre - 2) prime_pre retval)) (PreH2 : (i > lower)) (PreH3 : (PrimeForLucas prime_pre)) (PreH4 : ((0 : Int) <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (lower = ((min (α := Int)) (lower_pre) ((upper_pre - lower_pre))))) (PreH10 : ((0 : Int) <= lower)) (PreH11 : (lower <= (upper_pre - lower))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1))) (PreH14 : ((0 : Int) <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : ((0 : Int) <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator)) ,
  ((( &( "answer" ) )) # Int64 |->_)
  ** ((( &( "inverse" ) )) # Int |-> (retval))
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ ((numerator * retval) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (numerator * retval)) ”

noncomputable def binomial_digit_mod_prime_safety_wit_20 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (lower : Int) (retval : Int) (PreH1 : (ModularPower denominator (prime_pre - 2) prime_pre retval)) (PreH2 : (i > lower)) (PreH3 : (PrimeForLucas prime_pre)) (PreH4 : ((0 : Int) <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (lower = ((min (α := Int)) (lower_pre) ((upper_pre - lower_pre))))) (PreH10 : ((0 : Int) <= lower)) (PreH11 : (lower <= (upper_pre - lower))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1))) (PreH14 : ((0 : Int) <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : ((0 : Int) <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator)) ,
  ((( &( "answer" ) )) # Int64 |-> ((numerator * retval)))
  ** ((( &( "inverse" ) )) # Int |-> (retval))
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ (((numerator * retval) ≠ (-9223372036854775808)) ∨ (prime_pre ≠ (-1))) ” &&
  “ (prime_pre ≠ (0 : Int)) ”

noncomputable def binomial_digit_mod_prime_entail_wit_1_1 : Prop :=
  (
forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (PreH1 : (lower_pre > (upper_pre - lower_pre))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre)) (PreH4 : ((0 : Int) <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) ,
  TT && emp 
|--
  “ (PrimeForLucas prime_pre) ” &&
  “ ((0 : Int) <= lower_pre) ” &&
  “ (lower_pre <= upper_pre) ” &&
  “ (upper_pre < prime_pre) ” &&
  “ (2 <= prime_pre) ” &&
  “ (prime_pre <= 100000) ” &&
  “ ((upper_pre - lower_pre) = ((min (α := Int)) (lower_pre) ((upper_pre - lower_pre)))) ” &&
  “ ((0 : Int) <= (upper_pre - lower_pre)) ” &&
  “ ((upper_pre - lower_pre) <= (upper_pre - (upper_pre - lower_pre))) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= ((upper_pre - lower_pre) + 1)) ” &&
  “ ((0 : Int) <= 1) ” &&
  “ (1 < prime_pre) ” &&
  “ ((0 : Int) <= 1) ” &&
  “ (1 < prime_pre) ” &&
  “ (DigitProductProgress upper_pre (upper_pre - lower_pre) prime_pre 1 1 1) ”
  &&  emp
) \/
(
forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (PreH1 : (lower_pre > (upper_pre - lower_pre))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre)) (PreH4 : ((0 : Int) <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) ,
  TT && emp 
|--
  “ (DigitProductProgress upper_pre (upper_pre - lower_pre) prime_pre 1 1 1) ” &&
  “ ((upper_pre - lower_pre) = ((min (α := Int)) (lower_pre) ((upper_pre - lower_pre)))) ”
  &&  emp
)

noncomputable def binomial_digit_mod_prime_entail_wit_1_1_split_goal_1 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (PreH1 : (lower_pre > (upper_pre - lower_pre))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre)) (PreH4 : ((0 : Int) <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) ,
  (DigitProductProgress upper_pre (upper_pre - lower_pre) prime_pre 1 1 1)

noncomputable def binomial_digit_mod_prime_entail_wit_1_1_split_goal_2 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (PreH1 : (lower_pre > (upper_pre - lower_pre))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre)) (PreH4 : ((0 : Int) <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) ,
  ((upper_pre - lower_pre) = ((min (α := Int)) (lower_pre) ((upper_pre - lower_pre))))

noncomputable def binomial_digit_mod_prime_entail_wit_1_2 : Prop :=
  (
forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (PreH1 : (lower_pre <= (upper_pre - lower_pre))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre)) (PreH4 : ((0 : Int) <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) ,
  TT && emp 
|--
  “ (PrimeForLucas prime_pre) ” &&
  “ ((0 : Int) <= lower_pre) ” &&
  “ (lower_pre <= upper_pre) ” &&
  “ (upper_pre < prime_pre) ” &&
  “ (2 <= prime_pre) ” &&
  “ (prime_pre <= 100000) ” &&
  “ (lower_pre = ((min (α := Int)) (lower_pre) ((upper_pre - lower_pre)))) ” &&
  “ ((0 : Int) <= lower_pre) ” &&
  “ (lower_pre <= (upper_pre - lower_pre)) ” &&
  “ (1 <= 1) ” &&
  “ (1 <= (lower_pre + 1)) ” &&
  “ ((0 : Int) <= 1) ” &&
  “ (1 < prime_pre) ” &&
  “ ((0 : Int) <= 1) ” &&
  “ (1 < prime_pre) ” &&
  “ (DigitProductProgress upper_pre lower_pre prime_pre 1 1 1) ”
  &&  emp
) \/
(
forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (PreH1 : (lower_pre <= (upper_pre - lower_pre))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre)) (PreH4 : ((0 : Int) <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) ,
  TT && emp 
|--
  “ (DigitProductProgress upper_pre lower_pre prime_pre 1 1 1) ” &&
  “ (lower_pre = ((min (α := Int)) (lower_pre) ((upper_pre - lower_pre)))) ”
  &&  emp
)

noncomputable def binomial_digit_mod_prime_entail_wit_1_2_split_goal_1 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (PreH1 : (lower_pre <= (upper_pre - lower_pre))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre)) (PreH4 : ((0 : Int) <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) ,
  (DigitProductProgress upper_pre lower_pre prime_pre 1 1 1)

noncomputable def binomial_digit_mod_prime_entail_wit_1_2_split_goal_2 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (PreH1 : (lower_pre <= (upper_pre - lower_pre))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre)) (PreH4 : ((0 : Int) <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) ,
  (lower_pre = ((min (α := Int)) (lower_pre) ((upper_pre - lower_pre))))

noncomputable def binomial_digit_mod_prime_entail_wit_2 : Prop :=
  (
forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (lower : Int) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = ((min (α := Int)) (lower_pre) ((upper_pre - lower_pre))))) (PreH9 : ((0 : Int) <= lower)) (PreH10 : (lower <= (upper_pre - lower))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower + 1))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator)) ,
  TT && emp 
|--
  “ (PrimeForLucas prime_pre) ” &&
  “ ((0 : Int) <= lower_pre) ” &&
  “ (lower_pre <= upper_pre) ” &&
  “ (upper_pre < prime_pre) ” &&
  “ (2 <= prime_pre) ” &&
  “ (prime_pre <= 100000) ” &&
  “ (lower = ((min (α := Int)) (lower_pre) ((upper_pre - lower_pre)))) ” &&
  “ ((0 : Int) <= lower) ” &&
  “ (lower <= (upper_pre - lower)) ” &&
  “ (1 <= (i + 1)) ” &&
  “ ((i + 1) <= (lower + 1)) ” &&
  “ ((0 : Int) <= (signed_last_nbits ((Z.rem (numerator * ((upper_pre - lower) + i)) prime_pre)) (32))) ” &&
  “ ((signed_last_nbits ((Z.rem (numerator * ((upper_pre - lower) + i)) prime_pre)) (32)) < prime_pre) ” &&
  “ ((0 : Int) <= (signed_last_nbits ((Z.rem (denominator * i) prime_pre)) (32))) ” &&
  “ ((signed_last_nbits ((Z.rem (denominator * i) prime_pre)) (32)) < prime_pre) ” &&
  “ (DigitProductProgress upper_pre lower prime_pre (i + 1) (signed_last_nbits ((Z.rem (numerator * ((upper_pre - lower) + i)) prime_pre)) (32)) (signed_last_nbits ((Z.rem (denominator * i) prime_pre)) (32))) ”
  &&  emp
) \/
(
forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (lower : Int) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = ((min (α := Int)) (lower_pre) ((upper_pre - lower_pre))))) (PreH9 : ((0 : Int) <= lower)) (PreH10 : (lower <= (upper_pre - lower))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower + 1))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator)) ,
  TT && emp 
|--
  “ (DigitProductProgress upper_pre lower prime_pre (i + 1) (signed_last_nbits ((Z.rem (numerator * ((upper_pre - lower) + i)) prime_pre)) (32)) (signed_last_nbits ((Z.rem (denominator * i) prime_pre)) (32))) ” &&
  “ ((signed_last_nbits ((Z.rem (denominator * i) prime_pre)) (32)) < prime_pre) ” &&
  “ ((0 : Int) <= (signed_last_nbits ((Z.rem (denominator * i) prime_pre)) (32))) ” &&
  “ ((signed_last_nbits ((Z.rem (numerator * ((upper_pre - lower) + i)) prime_pre)) (32)) < prime_pre) ” &&
  “ ((0 : Int) <= (signed_last_nbits ((Z.rem (numerator * ((upper_pre - lower) + i)) prime_pre)) (32))) ”
  &&  emp
)

noncomputable def binomial_digit_mod_prime_entail_wit_2_split_goal_1 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (lower : Int) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = ((min (α := Int)) (lower_pre) ((upper_pre - lower_pre))))) (PreH9 : ((0 : Int) <= lower)) (PreH10 : (lower <= (upper_pre - lower))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower + 1))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator)) ,
  (DigitProductProgress upper_pre lower prime_pre (i + 1) (signed_last_nbits ((Z.rem (numerator * ((upper_pre - lower) + i)) prime_pre)) (32)) (signed_last_nbits ((Z.rem (denominator * i) prime_pre)) (32)))

noncomputable def binomial_digit_mod_prime_entail_wit_2_split_goal_2 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (lower : Int) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = ((min (α := Int)) (lower_pre) ((upper_pre - lower_pre))))) (PreH9 : ((0 : Int) <= lower)) (PreH10 : (lower <= (upper_pre - lower))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower + 1))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator)) ,
  ((signed_last_nbits ((Z.rem (denominator * i) prime_pre)) (32)) < prime_pre)

noncomputable def binomial_digit_mod_prime_entail_wit_2_split_goal_3 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (lower : Int) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = ((min (α := Int)) (lower_pre) ((upper_pre - lower_pre))))) (PreH9 : ((0 : Int) <= lower)) (PreH10 : (lower <= (upper_pre - lower))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower + 1))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator)) ,
  ((0 : Int) <= (signed_last_nbits ((Z.rem (denominator * i) prime_pre)) (32)))

noncomputable def binomial_digit_mod_prime_entail_wit_2_split_goal_4 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (lower : Int) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = ((min (α := Int)) (lower_pre) ((upper_pre - lower_pre))))) (PreH9 : ((0 : Int) <= lower)) (PreH10 : (lower <= (upper_pre - lower))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower + 1))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator)) ,
  ((signed_last_nbits ((Z.rem (numerator * ((upper_pre - lower) + i)) prime_pre)) (32)) < prime_pre)

noncomputable def binomial_digit_mod_prime_entail_wit_2_split_goal_5 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (lower : Int) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = ((min (α := Int)) (lower_pre) ((upper_pre - lower_pre))))) (PreH9 : ((0 : Int) <= lower)) (PreH10 : (lower <= (upper_pre - lower))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower + 1))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator)) ,
  ((0 : Int) <= (signed_last_nbits ((Z.rem (numerator * ((upper_pre - lower) + i)) prime_pre)) (32)))

noncomputable def binomial_digit_mod_prime_return_wit_1 : Prop :=
  (
forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (lower : Int) (retval : Int) (PreH1 : (ModularPower denominator (prime_pre - 2) prime_pre retval)) (PreH2 : (i > lower)) (PreH3 : (PrimeForLucas prime_pre)) (PreH4 : ((0 : Int) <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (lower = ((min (α := Int)) (lower_pre) ((upper_pre - lower_pre))))) (PreH10 : ((0 : Int) <= lower)) (PreH11 : (lower <= (upper_pre - lower))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1))) (PreH14 : ((0 : Int) <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : ((0 : Int) <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator)) ,
  TT && emp 
|--
  “ (BinomialDigitResidue upper_pre lower_pre prime_pre (signed_last_nbits ((Z.rem (numerator * retval) prime_pre)) (32))) ”
  &&  emp
) \/
(
forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (lower : Int) (retval : Int) (PreH1 : (ModularPower denominator (prime_pre - 2) prime_pre retval)) (PreH2 : (i > lower)) (PreH3 : (PrimeForLucas prime_pre)) (PreH4 : ((0 : Int) <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (lower = ((min (α := Int)) (lower_pre) ((upper_pre - lower_pre))))) (PreH10 : ((0 : Int) <= lower)) (PreH11 : (lower <= (upper_pre - lower))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1))) (PreH14 : ((0 : Int) <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : ((0 : Int) <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator)) ,
  TT && emp 
|--
  “ (BinomialDigitResidue upper_pre lower_pre prime_pre (signed_last_nbits ((Z.rem (numerator * retval) prime_pre)) (32))) ”
  &&  emp
)

noncomputable def binomial_digit_mod_prime_return_wit_1_split_goal_1 : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (lower : Int) (retval : Int) (PreH1 : (ModularPower denominator (prime_pre - 2) prime_pre retval)) (PreH2 : (i > lower)) (PreH3 : (PrimeForLucas prime_pre)) (PreH4 : ((0 : Int) <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (lower = ((min (α := Int)) (lower_pre) ((upper_pre - lower_pre))))) (PreH10 : ((0 : Int) <= lower)) (PreH11 : (lower <= (upper_pre - lower))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1))) (PreH14 : ((0 : Int) <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : ((0 : Int) <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator)) ,
  (BinomialDigitResidue upper_pre lower_pre prime_pre (signed_last_nbits ((Z.rem (numerator * retval) prime_pre)) (32)))

noncomputable def binomial_digit_mod_prime_partial_solve_wit_1_pure : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (lower : Int) (PreH1 : (i > lower)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = ((min (α := Int)) (lower_pre) ((upper_pre - lower_pre))))) (PreH9 : ((0 : Int) <= lower)) (PreH10 : (lower <= (upper_pre - lower))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower + 1))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator)) ,
  ((( &( "inverse" ) )) # Int |->_)
  ** ((( &( "upper" ) )) # Int |-> (upper_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "numerator" ) )) # Int |-> (numerator))
  ** ((( &( "denominator" ) )) # Int |-> (denominator))
|--
  “ ((0 : Int) <= denominator) ” &&
  “ (denominator < prime_pre) ” &&
  “ ((0 : Int) <= (prime_pre - 2)) ” &&
  “ (2 <= prime_pre) ” &&
  “ (prime_pre <= 100000) ”

noncomputable def binomial_digit_mod_prime_partial_solve_wit_1_aux : Prop :=
  forall (prime_pre : Int) (lower_pre : Int) (upper_pre : Int) (denominator : Int) (numerator : Int) (i : Int) (lower : Int) (PreH1 : (i > lower)) (PreH2 : (PrimeForLucas prime_pre)) (PreH3 : ((0 : Int) <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = ((min (α := Int)) (lower_pre) ((upper_pre - lower_pre))))) (PreH9 : ((0 : Int) <= lower)) (PreH10 : (lower <= (upper_pre - lower))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower + 1))) (PreH13 : ((0 : Int) <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : ((0 : Int) <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator)) ,
  TT && emp 
|--
  “ ((0 : Int) <= denominator) ” &&
  “ (denominator < prime_pre) ” &&
  “ ((0 : Int) <= (prime_pre - 2)) ” &&
  “ (2 <= prime_pre) ” &&
  “ (prime_pre <= 100000) ” &&
  “ (i > lower) ” &&
  “ (PrimeForLucas prime_pre) ” &&
  “ ((0 : Int) <= lower_pre) ” &&
  “ (lower_pre <= upper_pre) ” &&
  “ (upper_pre < prime_pre) ” &&
  “ (2 <= prime_pre) ” &&
  “ (prime_pre <= 100000) ” &&
  “ (lower = ((min (α := Int)) (lower_pre) ((upper_pre - lower_pre)))) ” &&
  “ ((0 : Int) <= lower) ” &&
  “ (lower <= (upper_pre - lower)) ” &&
  “ (1 <= i) ” &&
  “ (i <= (lower + 1)) ” &&
  “ ((0 : Int) <= numerator) ” &&
  “ (numerator < prime_pre) ” &&
  “ ((0 : Int) <= denominator) ” &&
  “ (denominator < prime_pre) ” &&
  “ (DigitProductProgress upper_pre lower prime_pre i numerator denominator) ”
  &&  emp

noncomputable def binomial_digit_mod_prime_partial_solve_wit_1 : Prop := binomial_digit_mod_prime_partial_solve_wit_1_pure -> binomial_digit_mod_prime_partial_solve_wit_1_aux

noncomputable def lucas_theorem_safety_wit_1 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (PrimeForLucas prime_pre)) ,
  ((( &( "upper" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
|--
  “ ((n_pre + m_pre) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (n_pre + m_pre)) ”

noncomputable def lucas_theorem_safety_wit_2 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (PrimeForLucas prime_pre)) ,
  ((( &( "result" ) )) # Int |->_)
  ** ((( &( "lower" ) )) # Int |-> (n_pre))
  ** ((( &( "upper" ) )) # Int |-> ((n_pre + m_pre)))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
|--
  “ (1 <= INT_MAX) ” &&
  “ ((INT_MIN) <= 1) ”

noncomputable def lucas_theorem_safety_wit_3 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (result : Int) (upper : Int) (lower : Int) (PreH1 : ((0 : Int) <= n_pre)) (PreH2 : ((0 : Int) <= m_pre)) (PreH3 : (2 <= prime_pre)) (PreH4 : (prime_pre <= 100000)) (PreH5 : (PrimeForLucas prime_pre)) (PreH6 : ((0 : Int) <= lower)) (PreH7 : (lower <= upper)) (PreH8 : ((0 : Int) <= result)) (PreH9 : (result < prime_pre)) (PreH10 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "upper" ) )) # Int |-> (upper))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def lucas_theorem_safety_wit_4 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (result : Int) (upper : Int) (lower : Int) (PreH1 : (upper <= (0 : Int))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : ((0 : Int) <= m_pre)) (PreH4 : (2 <= prime_pre)) (PreH5 : (prime_pre <= 100000)) (PreH6 : (PrimeForLucas prime_pre)) (PreH7 : ((0 : Int) <= lower)) (PreH8 : (lower <= upper)) (PreH9 : ((0 : Int) <= result)) (PreH10 : (result < prime_pre)) (PreH11 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "upper" ) )) # Int |-> (upper))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def lucas_theorem_safety_wit_5 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (result : Int) (upper : Int) (lower : Int) (PreH1 : (lower > (0 : Int))) (PreH2 : (upper <= (0 : Int))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (PrimeForLucas prime_pre)) (PreH8 : ((0 : Int) <= lower)) (PreH9 : (lower <= upper)) (PreH10 : ((0 : Int) <= result)) (PreH11 : (result < prime_pre)) (PreH12 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "upper" ) )) # Int |-> (upper))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ False ”

noncomputable def lucas_theorem_safety_wit_6 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (result : Int) (upper : Int) (lower : Int) (PreH1 : (upper > (0 : Int))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : ((0 : Int) <= m_pre)) (PreH4 : (2 <= prime_pre)) (PreH5 : (prime_pre <= 100000)) (PreH6 : (PrimeForLucas prime_pre)) (PreH7 : ((0 : Int) <= lower)) (PreH8 : (lower <= upper)) (PreH9 : ((0 : Int) <= result)) (PreH10 : (result < prime_pre)) (PreH11 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  ((( &( "upper_digit" ) )) # Int |->_)
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "upper" ) )) # Int |-> (upper))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ ((upper ≠ (INT_MIN)) ∨ (prime_pre ≠ (-1))) ” &&
  “ (prime_pre ≠ (0 : Int)) ”

noncomputable def lucas_theorem_safety_wit_7 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (result : Int) (upper : Int) (lower : Int) (PreH1 : (upper > (0 : Int))) (PreH2 : ((0 : Int) <= n_pre)) (PreH3 : ((0 : Int) <= m_pre)) (PreH4 : (2 <= prime_pre)) (PreH5 : (prime_pre <= 100000)) (PreH6 : (PrimeForLucas prime_pre)) (PreH7 : ((0 : Int) <= lower)) (PreH8 : (lower <= upper)) (PreH9 : ((0 : Int) <= result)) (PreH10 : (result < prime_pre)) (PreH11 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  ((( &( "lower_digit" ) )) # Int |->_)
  ** ((( &( "upper_digit" ) )) # Int |-> ((Z.rem upper prime_pre)))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "upper" ) )) # Int |-> (upper))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ ((lower ≠ (INT_MIN)) ∨ (prime_pre ≠ (-1))) ” &&
  “ (prime_pre ≠ (0 : Int)) ”

noncomputable def lucas_theorem_safety_wit_8 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (result : Int) (upper : Int) (lower : Int) (PreH1 : ((Z.rem lower prime_pre) > (Z.rem upper prime_pre))) (PreH2 : (upper > (0 : Int))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (PrimeForLucas prime_pre)) (PreH8 : ((0 : Int) <= lower)) (PreH9 : (lower <= upper)) (PreH10 : ((0 : Int) <= result)) (PreH11 : (result < prime_pre)) (PreH12 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  ((( &( "lower_digit" ) )) # Int |-> ((Z.rem lower prime_pre)))
  ** ((( &( "upper_digit" ) )) # Int |-> ((Z.rem upper prime_pre)))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "upper" ) )) # Int |-> (upper))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ ((0 : Int) <= INT_MAX) ” &&
  “ ((INT_MIN) <= (0 : Int)) ”

noncomputable def lucas_theorem_safety_wit_9 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (result : Int) (upper : Int) (lower : Int) (retval : Int) (PreH1 : (BinomialDigitResidue (Z.rem upper prime_pre) (Z.rem lower prime_pre) prime_pre retval)) (PreH2 : ((Z.rem lower prime_pre) <= (Z.rem upper prime_pre))) (PreH3 : (upper > (0 : Int))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (PrimeForLucas prime_pre)) (PreH9 : ((0 : Int) <= lower)) (PreH10 : (lower <= upper)) (PreH11 : ((0 : Int) <= result)) (PreH12 : (result < prime_pre)) (PreH13 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  ((( &( "product" ) )) # Int64 |->_)
  ** ((( &( "digit_binomial" ) )) # Int |-> (retval))
  ** ((( &( "lower_digit" ) )) # Int |-> ((Z.rem lower prime_pre)))
  ** ((( &( "upper_digit" ) )) # Int |-> ((Z.rem upper prime_pre)))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "upper" ) )) # Int |-> (upper))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ ((result * retval) <= 9223372036854775807) ” &&
  “ ((-9223372036854775808) <= (result * retval)) ”

noncomputable def lucas_theorem_safety_wit_10 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (result : Int) (upper : Int) (lower : Int) (retval : Int) (PreH1 : (BinomialDigitResidue (Z.rem upper prime_pre) (Z.rem lower prime_pre) prime_pre retval)) (PreH2 : ((Z.rem lower prime_pre) <= (Z.rem upper prime_pre))) (PreH3 : (upper > (0 : Int))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (PrimeForLucas prime_pre)) (PreH9 : ((0 : Int) <= lower)) (PreH10 : (lower <= upper)) (PreH11 : ((0 : Int) <= result)) (PreH12 : (result < prime_pre)) (PreH13 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  ((( &( "product" ) )) # Int64 |-> ((result * retval)))
  ** ((( &( "digit_binomial" ) )) # Int |-> (retval))
  ** ((( &( "lower_digit" ) )) # Int |-> ((Z.rem lower prime_pre)))
  ** ((( &( "upper_digit" ) )) # Int |-> ((Z.rem upper prime_pre)))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "upper" ) )) # Int |-> (upper))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ (((result * retval) ≠ (-9223372036854775808)) ∨ (prime_pre ≠ (-1))) ” &&
  “ (prime_pre ≠ (0 : Int)) ”

noncomputable def lucas_theorem_safety_wit_11 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (result : Int) (upper : Int) (lower : Int) (retval : Int) (PreH1 : (BinomialDigitResidue (Z.rem upper prime_pre) (Z.rem lower prime_pre) prime_pre retval)) (PreH2 : ((Z.rem lower prime_pre) <= (Z.rem upper prime_pre))) (PreH3 : (upper > (0 : Int))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (PrimeForLucas prime_pre)) (PreH9 : ((0 : Int) <= lower)) (PreH10 : (lower <= upper)) (PreH11 : ((0 : Int) <= result)) (PreH12 : (result < prime_pre)) (PreH13 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  ((( &( "product" ) )) # Int64 |-> ((result * retval)))
  ** ((( &( "digit_binomial" ) )) # Int |-> (retval))
  ** ((( &( "lower_digit" ) )) # Int |-> ((Z.rem lower prime_pre)))
  ** ((( &( "upper_digit" ) )) # Int |-> ((Z.rem upper prime_pre)))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "upper" ) )) # Int |-> (upper))
  ** ((( &( "result" ) )) # Int |-> ((signed_last_nbits ((Z.rem (result * retval) prime_pre)) (32))))
|--
  “ ((upper ≠ (INT_MIN)) ∨ (prime_pre ≠ (-1))) ” &&
  “ (prime_pre ≠ (0 : Int)) ”

noncomputable def lucas_theorem_safety_wit_12 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (result : Int) (upper : Int) (lower : Int) (retval : Int) (PreH1 : (BinomialDigitResidue (Z.rem upper prime_pre) (Z.rem lower prime_pre) prime_pre retval)) (PreH2 : ((Z.rem lower prime_pre) <= (Z.rem upper prime_pre))) (PreH3 : (upper > (0 : Int))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (PrimeForLucas prime_pre)) (PreH9 : ((0 : Int) <= lower)) (PreH10 : (lower <= upper)) (PreH11 : ((0 : Int) <= result)) (PreH12 : (result < prime_pre)) (PreH13 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  ((( &( "product" ) )) # Int64 |-> ((result * retval)))
  ** ((( &( "digit_binomial" ) )) # Int |-> (retval))
  ** ((( &( "lower_digit" ) )) # Int |-> ((Z.rem lower prime_pre)))
  ** ((( &( "upper_digit" ) )) # Int |-> ((Z.rem upper prime_pre)))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "upper" ) )) # Int |-> ((Z.quot upper prime_pre)))
  ** ((( &( "result" ) )) # Int |-> ((signed_last_nbits ((Z.rem (result * retval) prime_pre)) (32))))
|--
  “ ((lower ≠ (INT_MIN)) ∨ (prime_pre ≠ (-1))) ” &&
  “ (prime_pre ≠ (0 : Int)) ”

noncomputable def lucas_theorem_entail_wit_1 : Prop :=
  (
forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (PrimeForLucas prime_pre)) ,
  TT && emp 
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (2 <= prime_pre) ” &&
  “ (prime_pre <= 100000) ” &&
  “ (PrimeForLucas prime_pre) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ (n_pre <= (n_pre + m_pre)) ” &&
  “ ((0 : Int) <= 1) ” &&
  “ (1 < prime_pre) ” &&
  “ (LucasProgress (n_pre + m_pre) n_pre prime_pre (n_pre + m_pre) n_pre 1) ”
  &&  emp
) \/
(
forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (PrimeForLucas prime_pre)) ,
  TT && emp 
|--
  “ (LucasProgress (n_pre + m_pre) n_pre prime_pre (n_pre + m_pre) n_pre 1) ”
  &&  emp
)

noncomputable def lucas_theorem_entail_wit_1_split_goal_1 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (PrimeForLucas prime_pre)) ,
  (LucasProgress (n_pre + m_pre) n_pre prime_pre (n_pre + m_pre) n_pre 1)

noncomputable def lucas_theorem_entail_wit_2 : Prop :=
  (
forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (result : Int) (upper : Int) (lower : Int) (retval : Int) (PreH1 : (BinomialDigitResidue (Z.rem upper prime_pre) (Z.rem lower prime_pre) prime_pre retval)) (PreH2 : ((Z.rem lower prime_pre) <= (Z.rem upper prime_pre))) (PreH3 : (upper > (0 : Int))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (PrimeForLucas prime_pre)) (PreH9 : ((0 : Int) <= lower)) (PreH10 : (lower <= upper)) (PreH11 : ((0 : Int) <= result)) (PreH12 : (result < prime_pre)) (PreH13 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  TT && emp 
|--
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (2 <= prime_pre) ” &&
  “ (prime_pre <= 100000) ” &&
  “ (PrimeForLucas prime_pre) ” &&
  “ ((0 : Int) <= (Z.quot lower prime_pre)) ” &&
  “ ((Z.quot lower prime_pre) <= (Z.quot upper prime_pre)) ” &&
  “ ((0 : Int) <= (signed_last_nbits ((Z.rem (result * retval) prime_pre)) (32))) ” &&
  “ ((signed_last_nbits ((Z.rem (result * retval) prime_pre)) (32)) < prime_pre) ” &&
  “ (LucasProgress (n_pre + m_pre) n_pre prime_pre (Z.quot upper prime_pre) (Z.quot lower prime_pre) (signed_last_nbits ((Z.rem (result * retval) prime_pre)) (32))) ”
  &&  emp
) \/
(
forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (result : Int) (upper : Int) (lower : Int) (retval : Int) (PreH1 : (BinomialDigitResidue (Z.rem upper prime_pre) (Z.rem lower prime_pre) prime_pre retval)) (PreH2 : ((Z.rem lower prime_pre) <= (Z.rem upper prime_pre))) (PreH3 : (upper > (0 : Int))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (PrimeForLucas prime_pre)) (PreH9 : ((0 : Int) <= lower)) (PreH10 : (lower <= upper)) (PreH11 : ((0 : Int) <= result)) (PreH12 : (result < prime_pre)) (PreH13 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  TT && emp 
|--
  “ (LucasProgress (n_pre + m_pre) n_pre prime_pre (Z.quot upper prime_pre) (Z.quot lower prime_pre) (signed_last_nbits ((Z.rem (result * retval) prime_pre)) (32))) ” &&
  “ ((signed_last_nbits ((Z.rem (result * retval) prime_pre)) (32)) < prime_pre) ” &&
  “ ((0 : Int) <= (signed_last_nbits ((Z.rem (result * retval) prime_pre)) (32))) ” &&
  “ ((Z.quot lower prime_pre) <= (Z.quot upper prime_pre)) ” &&
  “ ((0 : Int) <= (Z.quot lower prime_pre)) ”
  &&  emp
)

noncomputable def lucas_theorem_entail_wit_2_split_goal_1 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (result : Int) (upper : Int) (lower : Int) (retval : Int) (PreH1 : (BinomialDigitResidue (Z.rem upper prime_pre) (Z.rem lower prime_pre) prime_pre retval)) (PreH2 : ((Z.rem lower prime_pre) <= (Z.rem upper prime_pre))) (PreH3 : (upper > (0 : Int))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (PrimeForLucas prime_pre)) (PreH9 : ((0 : Int) <= lower)) (PreH10 : (lower <= upper)) (PreH11 : ((0 : Int) <= result)) (PreH12 : (result < prime_pre)) (PreH13 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  (LucasProgress (n_pre + m_pre) n_pre prime_pre (Z.quot upper prime_pre) (Z.quot lower prime_pre) (signed_last_nbits ((Z.rem (result * retval) prime_pre)) (32)))

noncomputable def lucas_theorem_entail_wit_2_split_goal_2 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (result : Int) (upper : Int) (lower : Int) (retval : Int) (PreH1 : (BinomialDigitResidue (Z.rem upper prime_pre) (Z.rem lower prime_pre) prime_pre retval)) (PreH2 : ((Z.rem lower prime_pre) <= (Z.rem upper prime_pre))) (PreH3 : (upper > (0 : Int))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (PrimeForLucas prime_pre)) (PreH9 : ((0 : Int) <= lower)) (PreH10 : (lower <= upper)) (PreH11 : ((0 : Int) <= result)) (PreH12 : (result < prime_pre)) (PreH13 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  ((signed_last_nbits ((Z.rem (result * retval) prime_pre)) (32)) < prime_pre)

noncomputable def lucas_theorem_entail_wit_2_split_goal_3 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (result : Int) (upper : Int) (lower : Int) (retval : Int) (PreH1 : (BinomialDigitResidue (Z.rem upper prime_pre) (Z.rem lower prime_pre) prime_pre retval)) (PreH2 : ((Z.rem lower prime_pre) <= (Z.rem upper prime_pre))) (PreH3 : (upper > (0 : Int))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (PrimeForLucas prime_pre)) (PreH9 : ((0 : Int) <= lower)) (PreH10 : (lower <= upper)) (PreH11 : ((0 : Int) <= result)) (PreH12 : (result < prime_pre)) (PreH13 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  ((0 : Int) <= (signed_last_nbits ((Z.rem (result * retval) prime_pre)) (32)))

noncomputable def lucas_theorem_entail_wit_2_split_goal_4 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (result : Int) (upper : Int) (lower : Int) (retval : Int) (PreH1 : (BinomialDigitResidue (Z.rem upper prime_pre) (Z.rem lower prime_pre) prime_pre retval)) (PreH2 : ((Z.rem lower prime_pre) <= (Z.rem upper prime_pre))) (PreH3 : (upper > (0 : Int))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (PrimeForLucas prime_pre)) (PreH9 : ((0 : Int) <= lower)) (PreH10 : (lower <= upper)) (PreH11 : ((0 : Int) <= result)) (PreH12 : (result < prime_pre)) (PreH13 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  ((Z.quot lower prime_pre) <= (Z.quot upper prime_pre))

noncomputable def lucas_theorem_entail_wit_2_split_goal_5 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (result : Int) (upper : Int) (lower : Int) (retval : Int) (PreH1 : (BinomialDigitResidue (Z.rem upper prime_pre) (Z.rem lower prime_pre) prime_pre retval)) (PreH2 : ((Z.rem lower prime_pre) <= (Z.rem upper prime_pre))) (PreH3 : (upper > (0 : Int))) (PreH4 : ((0 : Int) <= n_pre)) (PreH5 : ((0 : Int) <= m_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (PrimeForLucas prime_pre)) (PreH9 : ((0 : Int) <= lower)) (PreH10 : (lower <= upper)) (PreH11 : ((0 : Int) <= result)) (PreH12 : (result < prime_pre)) (PreH13 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  ((0 : Int) <= (Z.quot lower prime_pre))

noncomputable def lucas_theorem_return_wit_1 : Prop :=
  (
forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (result : Int) (upper : Int) (lower : Int) (PreH1 : (lower <= (0 : Int))) (PreH2 : (upper <= (0 : Int))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (PrimeForLucas prime_pre)) (PreH8 : ((0 : Int) <= lower)) (PreH9 : (lower <= upper)) (PreH10 : ((0 : Int) <= result)) (PreH11 : (result < prime_pre)) (PreH12 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  TT && emp 
|--
  “ (LucasBinomialResidue n_pre m_pre prime_pre result) ”
  &&  emp
) \/
(
forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (result : Int) (upper : Int) (lower : Int) (PreH1 : (lower <= (0 : Int))) (PreH2 : (upper <= (0 : Int))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (PrimeForLucas prime_pre)) (PreH8 : ((0 : Int) <= lower)) (PreH9 : (lower <= upper)) (PreH10 : ((0 : Int) <= result)) (PreH11 : (result < prime_pre)) (PreH12 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  TT && emp 
|--
  “ (LucasBinomialResidue n_pre m_pre prime_pre result) ”
  &&  emp
)

noncomputable def lucas_theorem_return_wit_1_split_goal_1 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (result : Int) (upper : Int) (lower : Int) (PreH1 : (lower <= (0 : Int))) (PreH2 : (upper <= (0 : Int))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (PrimeForLucas prime_pre)) (PreH8 : ((0 : Int) <= lower)) (PreH9 : (lower <= upper)) (PreH10 : ((0 : Int) <= result)) (PreH11 : (result < prime_pre)) (PreH12 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  (LucasBinomialResidue n_pre m_pre prime_pre result)

noncomputable def lucas_theorem_return_wit_2 : Prop :=
  (
forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (result : Int) (upper : Int) (lower : Int) (PreH1 : ((Z.rem lower prime_pre) > (Z.rem upper prime_pre))) (PreH2 : (upper > (0 : Int))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (PrimeForLucas prime_pre)) (PreH8 : ((0 : Int) <= lower)) (PreH9 : (lower <= upper)) (PreH10 : ((0 : Int) <= result)) (PreH11 : (result < prime_pre)) (PreH12 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  TT && emp 
|--
  “ (LucasBinomialResidue n_pre m_pre prime_pre (0 : Int)) ”
  &&  emp
) \/
(
forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (result : Int) (upper : Int) (lower : Int) (PreH1 : ((Z.rem lower prime_pre) > (Z.rem upper prime_pre))) (PreH2 : (upper > (0 : Int))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (PrimeForLucas prime_pre)) (PreH8 : ((0 : Int) <= lower)) (PreH9 : (lower <= upper)) (PreH10 : ((0 : Int) <= result)) (PreH11 : (result < prime_pre)) (PreH12 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  TT && emp 
|--
  “ (LucasBinomialResidue n_pre m_pre prime_pre (0 : Int)) ”
  &&  emp
)

noncomputable def lucas_theorem_return_wit_2_split_goal_1 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (result : Int) (upper : Int) (lower : Int) (PreH1 : ((Z.rem lower prime_pre) > (Z.rem upper prime_pre))) (PreH2 : (upper > (0 : Int))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (PrimeForLucas prime_pre)) (PreH8 : ((0 : Int) <= lower)) (PreH9 : (lower <= upper)) (PreH10 : ((0 : Int) <= result)) (PreH11 : (result < prime_pre)) (PreH12 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  (LucasBinomialResidue n_pre m_pre prime_pre (0 : Int))

noncomputable def lucas_theorem_partial_solve_wit_1_pure : Prop :=
  (
forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (result : Int) (upper : Int) (lower : Int) (PreH1 : ((Z.rem lower prime_pre) <= (Z.rem upper prime_pre))) (PreH2 : (upper > (0 : Int))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (PrimeForLucas prime_pre)) (PreH8 : ((0 : Int) <= lower)) (PreH9 : (lower <= upper)) (PreH10 : ((0 : Int) <= result)) (PreH11 : (result < prime_pre)) (PreH12 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  ((( &( "digit_binomial" ) )) # Int |->_)
  ** ((( &( "lower_digit" ) )) # Int |-> ((Z.rem lower prime_pre)))
  ** ((( &( "upper_digit" ) )) # Int |-> ((Z.rem upper prime_pre)))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "upper" ) )) # Int |-> (upper))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ (PrimeForLucas prime_pre) ” &&
  “ ((Z.rem lower prime_pre) <= (Z.rem upper prime_pre)) ” &&
  “ (2 <= prime_pre) ” &&
  “ (prime_pre <= 100000) ” &&
  “ ((Z.rem upper prime_pre) < prime_pre) ” &&
  “ ((0 : Int) <= (Z.rem lower prime_pre)) ”
) \/
(
forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (result : Int) (upper : Int) (lower : Int) (PreH1 : (result <= INT_MAX)) (PreH2 : (upper <= INT_MAX)) (PreH3 : (lower <= INT_MAX)) (PreH4 : (prime_pre <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((Z.rem upper prime_pre) <= INT_MAX)) (PreH8 : ((Z.rem lower prime_pre) <= INT_MAX)) (PreH9 : (result >= INT_MIN)) (PreH10 : (upper >= INT_MIN)) (PreH11 : (lower >= INT_MIN)) (PreH12 : (prime_pre >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : ((Z.rem upper prime_pre) >= INT_MIN)) (PreH16 : ((Z.rem lower prime_pre) >= INT_MIN)) (PreH17 : ((Z.rem lower prime_pre) <= (Z.rem upper prime_pre))) (PreH18 : (upper > (0 : Int))) (PreH19 : ((0 : Int) <= n_pre)) (PreH20 : ((0 : Int) <= m_pre)) (PreH21 : (2 <= prime_pre)) (PreH22 : (prime_pre <= 100000)) (PreH23 : (PrimeForLucas prime_pre)) (PreH24 : ((0 : Int) <= lower)) (PreH25 : (lower <= upper)) (PreH26 : ((0 : Int) <= result)) (PreH27 : (result < prime_pre)) (PreH28 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  ((( &( "digit_binomial" ) )) # Int |->_)
  ** ((( &( "lower_digit" ) )) # Int |-> ((Z.rem lower prime_pre)))
  ** ((( &( "upper_digit" ) )) # Int |-> ((Z.rem upper prime_pre)))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "upper" ) )) # Int |-> (upper))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ ((0 : Int) <= (Z.rem lower prime_pre)) ” &&
  “ ((Z.rem upper prime_pre) < prime_pre) ”
)

noncomputable def lucas_theorem_partial_solve_wit_1_pure_split_goal_1 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (result : Int) (upper : Int) (lower : Int) (PreH1 : (result <= INT_MAX)) (PreH2 : (upper <= INT_MAX)) (PreH3 : (lower <= INT_MAX)) (PreH4 : (prime_pre <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((Z.rem upper prime_pre) <= INT_MAX)) (PreH8 : ((Z.rem lower prime_pre) <= INT_MAX)) (PreH9 : (result >= INT_MIN)) (PreH10 : (upper >= INT_MIN)) (PreH11 : (lower >= INT_MIN)) (PreH12 : (prime_pre >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : ((Z.rem upper prime_pre) >= INT_MIN)) (PreH16 : ((Z.rem lower prime_pre) >= INT_MIN)) (PreH17 : ((Z.rem lower prime_pre) <= (Z.rem upper prime_pre))) (PreH18 : (upper > (0 : Int))) (PreH19 : ((0 : Int) <= n_pre)) (PreH20 : ((0 : Int) <= m_pre)) (PreH21 : (2 <= prime_pre)) (PreH22 : (prime_pre <= 100000)) (PreH23 : (PrimeForLucas prime_pre)) (PreH24 : ((0 : Int) <= lower)) (PreH25 : (lower <= upper)) (PreH26 : ((0 : Int) <= result)) (PreH27 : (result < prime_pre)) (PreH28 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  ((( &( "digit_binomial" ) )) # Int |->_)
  ** ((( &( "lower_digit" ) )) # Int |-> ((Z.rem lower prime_pre)))
  ** ((( &( "upper_digit" ) )) # Int |-> ((Z.rem upper prime_pre)))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "upper" ) )) # Int |-> (upper))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ ((0 : Int) <= (Z.rem lower prime_pre)) ”

noncomputable def lucas_theorem_partial_solve_wit_1_pure_split_goal_2 : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (result : Int) (upper : Int) (lower : Int) (PreH1 : (result <= INT_MAX)) (PreH2 : (upper <= INT_MAX)) (PreH3 : (lower <= INT_MAX)) (PreH4 : (prime_pre <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((Z.rem upper prime_pre) <= INT_MAX)) (PreH8 : ((Z.rem lower prime_pre) <= INT_MAX)) (PreH9 : (result >= INT_MIN)) (PreH10 : (upper >= INT_MIN)) (PreH11 : (lower >= INT_MIN)) (PreH12 : (prime_pre >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : ((Z.rem upper prime_pre) >= INT_MIN)) (PreH16 : ((Z.rem lower prime_pre) >= INT_MIN)) (PreH17 : ((Z.rem lower prime_pre) <= (Z.rem upper prime_pre))) (PreH18 : (upper > (0 : Int))) (PreH19 : ((0 : Int) <= n_pre)) (PreH20 : ((0 : Int) <= m_pre)) (PreH21 : (2 <= prime_pre)) (PreH22 : (prime_pre <= 100000)) (PreH23 : (PrimeForLucas prime_pre)) (PreH24 : ((0 : Int) <= lower)) (PreH25 : (lower <= upper)) (PreH26 : ((0 : Int) <= result)) (PreH27 : (result < prime_pre)) (PreH28 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  ((( &( "digit_binomial" ) )) # Int |->_)
  ** ((( &( "lower_digit" ) )) # Int |-> ((Z.rem lower prime_pre)))
  ** ((( &( "upper_digit" ) )) # Int |-> ((Z.rem upper prime_pre)))
  ** ((( &( "n" ) )) # Int |-> (n_pre))
  ** ((( &( "m" ) )) # Int |-> (m_pre))
  ** ((( &( "prime" ) )) # Int |-> (prime_pre))
  ** ((( &( "lower" ) )) # Int |-> (lower))
  ** ((( &( "upper" ) )) # Int |-> (upper))
  ** ((( &( "result" ) )) # Int |-> (result))
|--
  “ ((Z.rem upper prime_pre) < prime_pre) ”

noncomputable def lucas_theorem_partial_solve_wit_1_aux : Prop :=
  forall (prime_pre : Int) (m_pre : Int) (n_pre : Int) (result : Int) (upper : Int) (lower : Int) (PreH1 : ((Z.rem lower prime_pre) <= (Z.rem upper prime_pre))) (PreH2 : (upper > (0 : Int))) (PreH3 : ((0 : Int) <= n_pre)) (PreH4 : ((0 : Int) <= m_pre)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (PrimeForLucas prime_pre)) (PreH8 : ((0 : Int) <= lower)) (PreH9 : (lower <= upper)) (PreH10 : ((0 : Int) <= result)) (PreH11 : (result < prime_pre)) (PreH12 : (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result)) ,
  TT && emp 
|--
  “ (PrimeForLucas prime_pre) ” &&
  “ ((Z.rem lower prime_pre) <= (Z.rem upper prime_pre)) ” &&
  “ (2 <= prime_pre) ” &&
  “ (prime_pre <= 100000) ” &&
  “ ((Z.rem upper prime_pre) < prime_pre) ” &&
  “ ((0 : Int) <= (Z.rem lower prime_pre)) ” &&
  “ ((Z.rem lower prime_pre) <= (Z.rem upper prime_pre)) ” &&
  “ (upper > (0 : Int)) ” &&
  “ ((0 : Int) <= n_pre) ” &&
  “ ((0 : Int) <= m_pre) ” &&
  “ (2 <= prime_pre) ” &&
  “ (prime_pre <= 100000) ” &&
  “ (PrimeForLucas prime_pre) ” &&
  “ ((0 : Int) <= lower) ” &&
  “ (lower <= upper) ” &&
  “ ((0 : Int) <= result) ” &&
  “ (result < prime_pre) ” &&
  “ (LucasProgress (n_pre + m_pre) n_pre prime_pre upper lower result) ”
  &&  emp

noncomputable def lucas_theorem_partial_solve_wit_1 : Prop := lucas_theorem_partial_solve_wit_1_pure -> lucas_theorem_partial_solve_wit_1_aux


structure VC_Correct : Type where
  proof_of_binomial_digit_mod_prime_safety_wit_1 : binomial_digit_mod_prime_safety_wit_1
  proof_of_binomial_digit_mod_prime_safety_wit_2 : binomial_digit_mod_prime_safety_wit_2
  proof_of_binomial_digit_mod_prime_safety_wit_3 : binomial_digit_mod_prime_safety_wit_3
  proof_of_binomial_digit_mod_prime_safety_wit_4 : binomial_digit_mod_prime_safety_wit_4
  proof_of_binomial_digit_mod_prime_safety_wit_5 : binomial_digit_mod_prime_safety_wit_5
  proof_of_binomial_digit_mod_prime_safety_wit_6 : binomial_digit_mod_prime_safety_wit_6
  proof_of_binomial_digit_mod_prime_safety_wit_7 : binomial_digit_mod_prime_safety_wit_7
  proof_of_binomial_digit_mod_prime_safety_wit_8 : binomial_digit_mod_prime_safety_wit_8
  proof_of_binomial_digit_mod_prime_safety_wit_9 : binomial_digit_mod_prime_safety_wit_9
  proof_of_binomial_digit_mod_prime_safety_wit_10 : binomial_digit_mod_prime_safety_wit_10
  proof_of_binomial_digit_mod_prime_safety_wit_11 : binomial_digit_mod_prime_safety_wit_11
  proof_of_binomial_digit_mod_prime_safety_wit_12 : binomial_digit_mod_prime_safety_wit_12
  proof_of_binomial_digit_mod_prime_safety_wit_13 : binomial_digit_mod_prime_safety_wit_13
  proof_of_binomial_digit_mod_prime_safety_wit_14 : binomial_digit_mod_prime_safety_wit_14
  proof_of_binomial_digit_mod_prime_safety_wit_15 : binomial_digit_mod_prime_safety_wit_15
  proof_of_binomial_digit_mod_prime_safety_wit_16 : binomial_digit_mod_prime_safety_wit_16
  proof_of_binomial_digit_mod_prime_safety_wit_17 : binomial_digit_mod_prime_safety_wit_17
  proof_of_binomial_digit_mod_prime_safety_wit_18 : binomial_digit_mod_prime_safety_wit_18
  proof_of_binomial_digit_mod_prime_safety_wit_19 : binomial_digit_mod_prime_safety_wit_19
  proof_of_binomial_digit_mod_prime_safety_wit_20 : binomial_digit_mod_prime_safety_wit_20
  proof_of_binomial_digit_mod_prime_partial_solve_wit_1_pure : binomial_digit_mod_prime_partial_solve_wit_1_pure
  proof_of_binomial_digit_mod_prime_partial_solve_wit_1 : binomial_digit_mod_prime_partial_solve_wit_1
  proof_of_lucas_theorem_safety_wit_1 : lucas_theorem_safety_wit_1
  proof_of_lucas_theorem_safety_wit_2 : lucas_theorem_safety_wit_2
  proof_of_lucas_theorem_safety_wit_3 : lucas_theorem_safety_wit_3
  proof_of_lucas_theorem_safety_wit_4 : lucas_theorem_safety_wit_4
  proof_of_lucas_theorem_safety_wit_5 : lucas_theorem_safety_wit_5
  proof_of_lucas_theorem_safety_wit_6 : lucas_theorem_safety_wit_6
  proof_of_lucas_theorem_safety_wit_7 : lucas_theorem_safety_wit_7
  proof_of_lucas_theorem_safety_wit_8 : lucas_theorem_safety_wit_8
  proof_of_lucas_theorem_safety_wit_9 : lucas_theorem_safety_wit_9
  proof_of_lucas_theorem_safety_wit_10 : lucas_theorem_safety_wit_10
  proof_of_lucas_theorem_safety_wit_11 : lucas_theorem_safety_wit_11
  proof_of_lucas_theorem_safety_wit_12 : lucas_theorem_safety_wit_12
  proof_of_lucas_theorem_partial_solve_wit_1 : lucas_theorem_partial_solve_wit_1
  proof_of_binomial_digit_mod_prime_entail_wit_1_1 : binomial_digit_mod_prime_entail_wit_1_1
  proof_of_binomial_digit_mod_prime_entail_wit_1_2 : binomial_digit_mod_prime_entail_wit_1_2
  proof_of_binomial_digit_mod_prime_entail_wit_2 : binomial_digit_mod_prime_entail_wit_2
  proof_of_binomial_digit_mod_prime_return_wit_1 : binomial_digit_mod_prime_return_wit_1
  proof_of_lucas_theorem_entail_wit_1 : lucas_theorem_entail_wit_1
  proof_of_lucas_theorem_entail_wit_2 : lucas_theorem_entail_wit_2
  proof_of_lucas_theorem_return_wit_1 : lucas_theorem_return_wit_1
  proof_of_lucas_theorem_return_wit_2 : lucas_theorem_return_wit_2
  proof_of_lucas_theorem_partial_solve_wit_1_pure : lucas_theorem_partial_solve_wit_1_pure

end SimpleC.EE.LLM_bench.Algorithms.lucas_theorem.lucas_theorem_goal
