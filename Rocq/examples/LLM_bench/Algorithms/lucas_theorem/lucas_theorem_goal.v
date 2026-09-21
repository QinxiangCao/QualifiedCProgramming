Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents ListLib VMap.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem SeparationLogic.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string_scope.
Local Open Scope list.
Import naive_C_Rules.
Require Import SimpleC.EE.LLM_bench.Algorithms.lucas_theorem.lucas_theorem_lib.
Local Open Scope sac.

(*----- Function binomial_digit_mod_prime -----*)

Definition binomial_digit_mod_prime_safety_wit_1 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (PreH1 : (lower_pre > upper_pre)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) ,
  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
|--
  “ False ”
.

Definition binomial_digit_mod_prime_safety_wit_2 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (PreH1 : (lower_pre <= upper_pre)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) ,
  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
|--
  “ ((upper_pre - lower_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (upper_pre - lower_pre )) ”
.

Definition binomial_digit_mod_prime_safety_wit_3 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (PreH1 : (lower_pre > (upper_pre - lower_pre ))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre )) (PreH4 : (0 <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) ,
  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
|--
  “ ((upper_pre - lower_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (upper_pre - lower_pre )) ”
.

Definition binomial_digit_mod_prime_safety_wit_4 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (PreH1 : (lower_pre > (upper_pre - lower_pre ))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre )) (PreH4 : (0 <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) ,
  ((( &( "numerator" ) )) # Int  |->_)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "lower" ) )) # Int  |-> (upper_pre - lower_pre ))
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition binomial_digit_mod_prime_safety_wit_5 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (PreH1 : (lower_pre <= (upper_pre - lower_pre ))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre )) (PreH4 : (0 <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) ,
  ((( &( "numerator" ) )) # Int  |->_)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition binomial_digit_mod_prime_safety_wit_6 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (PreH1 : (lower_pre > (upper_pre - lower_pre ))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre )) (PreH4 : (0 <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) ,
  ((( &( "denominator" ) )) # Int  |->_)
  **  ((( &( "numerator" ) )) # Int  |-> 1)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "lower" ) )) # Int  |-> (upper_pre - lower_pre ))
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition binomial_digit_mod_prime_safety_wit_7 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (PreH1 : (lower_pre <= (upper_pre - lower_pre ))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre )) (PreH4 : (0 <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) ,
  ((( &( "denominator" ) )) # Int  |->_)
  **  ((( &( "numerator" ) )) # Int  |-> 1)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition binomial_digit_mod_prime_safety_wit_8 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (PreH1 : (lower_pre > (upper_pre - lower_pre ))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre )) (PreH4 : (0 <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "denominator" ) )) # Int  |-> 1)
  **  ((( &( "numerator" ) )) # Int  |-> 1)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "lower" ) )) # Int  |-> (upper_pre - lower_pre ))
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition binomial_digit_mod_prime_safety_wit_9 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (PreH1 : (lower_pre <= (upper_pre - lower_pre ))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre )) (PreH4 : (0 <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  ((( &( "denominator" ) )) # Int  |-> 1)
  **  ((( &( "numerator" ) )) # Int  |-> 1)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition binomial_digit_mod_prime_safety_wit_10 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (lower: Z) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (Z.min (lower_pre) ((upper_pre - lower_pre ))))) (PreH9 : (0 <= lower)) (PreH10 : (lower <= (upper_pre - lower ))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower + 1 ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator )) ,
  ((( &( "factor" ) )) # Int  |->_)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numerator" ) )) # Int  |-> numerator)
  **  ((( &( "denominator" ) )) # Int  |-> denominator)
|--
  “ (((upper_pre - lower ) + i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((upper_pre - lower ) + i )) ”
.

Definition binomial_digit_mod_prime_safety_wit_11 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (lower: Z) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (Z.min (lower_pre) ((upper_pre - lower_pre ))))) (PreH9 : (0 <= lower)) (PreH10 : (lower <= (upper_pre - lower ))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower + 1 ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator )) ,
  ((( &( "factor" ) )) # Int  |->_)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numerator" ) )) # Int  |-> numerator)
  **  ((( &( "denominator" ) )) # Int  |-> denominator)
|--
  “ ((upper_pre - lower ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (upper_pre - lower )) ”
.

Definition binomial_digit_mod_prime_safety_wit_12 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (lower: Z) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (Z.min (lower_pre) ((upper_pre - lower_pre ))))) (PreH9 : (0 <= lower)) (PreH10 : (lower <= (upper_pre - lower ))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower + 1 ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator )) ,
  ((( &( "numerator_product" ) )) # Int64  |->_)
  **  ((( &( "factor" ) )) # Int  |-> ((upper_pre - lower ) + i ))
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numerator" ) )) # Int  |-> numerator)
  **  ((( &( "denominator" ) )) # Int  |-> denominator)
|--
  “ ((numerator * ((upper_pre - lower ) + i ) ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (numerator * ((upper_pre - lower ) + i ) )) ”
.

Definition binomial_digit_mod_prime_safety_wit_13 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (lower: Z) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (Z.min (lower_pre) ((upper_pre - lower_pre ))))) (PreH9 : (0 <= lower)) (PreH10 : (lower <= (upper_pre - lower ))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower + 1 ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator )) ,
  ((( &( "denominator_product" ) )) # Int64  |->_)
  **  ((( &( "numerator_product" ) )) # Int64  |-> (numerator * ((upper_pre - lower ) + i ) ))
  **  ((( &( "factor" ) )) # Int  |-> ((upper_pre - lower ) + i ))
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numerator" ) )) # Int  |-> numerator)
  **  ((( &( "denominator" ) )) # Int  |-> denominator)
|--
  “ ((denominator * i ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (denominator * i )) ”
.

Definition binomial_digit_mod_prime_safety_wit_14 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (lower: Z) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (Z.min (lower_pre) ((upper_pre - lower_pre ))))) (PreH9 : (0 <= lower)) (PreH10 : (lower <= (upper_pre - lower ))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower + 1 ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator )) ,
  ((( &( "denominator_product" ) )) # Int64  |-> (denominator * i ))
  **  ((( &( "numerator_product" ) )) # Int64  |-> (numerator * ((upper_pre - lower ) + i ) ))
  **  ((( &( "factor" ) )) # Int  |-> ((upper_pre - lower ) + i ))
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numerator" ) )) # Int  |-> numerator)
  **  ((( &( "denominator" ) )) # Int  |-> denominator)
|--
  “ (((numerator * ((upper_pre - lower ) + i ) ) <> (INT64_MIN)) \/ (prime_pre <> (-1))) ” 
  &&  “ (prime_pre <> 0) ”
.

Definition binomial_digit_mod_prime_safety_wit_15 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (lower: Z) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (Z.min (lower_pre) ((upper_pre - lower_pre ))))) (PreH9 : (0 <= lower)) (PreH10 : (lower <= (upper_pre - lower ))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower + 1 ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator )) ,
  ((( &( "denominator_product" ) )) # Int64  |-> (denominator * i ))
  **  ((( &( "numerator_product" ) )) # Int64  |-> (numerator * ((upper_pre - lower ) + i ) ))
  **  ((( &( "factor" ) )) # Int  |-> ((upper_pre - lower ) + i ))
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numerator" ) )) # Int  |-> (signed_last_nbits (((numerator * ((upper_pre - lower ) + i ) ) % ( prime_pre ) )) (32)))
  **  ((( &( "denominator" ) )) # Int  |-> denominator)
|--
  “ (((denominator * i ) <> (INT64_MIN)) \/ (prime_pre <> (-1))) ” 
  &&  “ (prime_pre <> 0) ”
.

Definition binomial_digit_mod_prime_safety_wit_16 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (lower: Z) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (Z.min (lower_pre) ((upper_pre - lower_pre ))))) (PreH9 : (0 <= lower)) (PreH10 : (lower <= (upper_pre - lower ))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower + 1 ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator )) ,
  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numerator" ) )) # Int  |-> (signed_last_nbits (((numerator * ((upper_pre - lower ) + i ) ) % ( prime_pre ) )) (32)))
  **  ((( &( "denominator" ) )) # Int  |-> (signed_last_nbits (((denominator * i ) % ( prime_pre ) )) (32)))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition binomial_digit_mod_prime_safety_wit_17 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (lower: Z) (PreH1 : (i > lower)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (Z.min (lower_pre) ((upper_pre - lower_pre ))))) (PreH9 : (0 <= lower)) (PreH10 : (lower <= (upper_pre - lower ))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower + 1 ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator )) ,
  ((( &( "inverse" ) )) # Int  |->_)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "numerator" ) )) # Int  |-> numerator)
  **  ((( &( "denominator" ) )) # Int  |-> denominator)
|--
  “ ((prime_pre - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (prime_pre - 2 )) ”
.

Definition binomial_digit_mod_prime_safety_wit_18 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (lower: Z) (PreH1 : (i > lower)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (Z.min (lower_pre) ((upper_pre - lower_pre ))))) (PreH9 : (0 <= lower)) (PreH10 : (lower <= (upper_pre - lower ))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower + 1 ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator )) ,
  ((( &( "inverse" ) )) # Int  |->_)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "numerator" ) )) # Int  |-> numerator)
  **  ((( &( "denominator" ) )) # Int  |-> denominator)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition binomial_digit_mod_prime_safety_wit_19 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (lower: Z) (retval: Z) (PreH1 : (ModularPower denominator (prime_pre - 2 ) prime_pre retval )) (PreH2 : (i > lower)) (PreH3 : (PrimeForLucas prime_pre )) (PreH4 : (0 <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (lower = (Z.min (lower_pre) ((upper_pre - lower_pre ))))) (PreH10 : (0 <= lower)) (PreH11 : (lower <= (upper_pre - lower ))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1 ))) (PreH14 : (0 <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : (0 <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator )) ,
  ((( &( "answer" ) )) # Int64  |->_)
  **  ((( &( "inverse" ) )) # Int  |-> retval)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "numerator" ) )) # Int  |-> numerator)
  **  ((( &( "denominator" ) )) # Int  |-> denominator)
|--
  “ ((numerator * retval ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (numerator * retval )) ”
.

Definition binomial_digit_mod_prime_safety_wit_20 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (lower: Z) (retval: Z) (PreH1 : (ModularPower denominator (prime_pre - 2 ) prime_pre retval )) (PreH2 : (i > lower)) (PreH3 : (PrimeForLucas prime_pre )) (PreH4 : (0 <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (lower = (Z.min (lower_pre) ((upper_pre - lower_pre ))))) (PreH10 : (0 <= lower)) (PreH11 : (lower <= (upper_pre - lower ))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1 ))) (PreH14 : (0 <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : (0 <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator )) ,
  ((( &( "answer" ) )) # Int64  |-> (numerator * retval ))
  **  ((( &( "inverse" ) )) # Int  |-> retval)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "numerator" ) )) # Int  |-> numerator)
  **  ((( &( "denominator" ) )) # Int  |-> denominator)
|--
  “ (((numerator * retval ) <> (INT64_MIN)) \/ (prime_pre <> (-1))) ” 
  &&  “ (prime_pre <> 0) ”
.

Definition binomial_digit_mod_prime_entail_wit_1_1 := 
(
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (PreH1 : (lower_pre > (upper_pre - lower_pre ))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre )) (PreH4 : (0 <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) ,
  TT && emp 
|--
  “ (PrimeForLucas prime_pre ) ” 
  &&  “ (0 <= lower_pre) ” 
  &&  “ (lower_pre <= upper_pre) ” 
  &&  “ (upper_pre < prime_pre) ” 
  &&  “ (2 <= prime_pre) ” 
  &&  “ (prime_pre <= 100000) ” 
  &&  “ ((upper_pre - lower_pre ) = (Z.min (lower_pre) ((upper_pre - lower_pre )))) ” 
  &&  “ (0 <= (upper_pre - lower_pre )) ” 
  &&  “ ((upper_pre - lower_pre ) <= (upper_pre - (upper_pre - lower_pre ) )) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= ((upper_pre - lower_pre ) + 1 )) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 < prime_pre) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 < prime_pre) ” 
  &&  “ (DigitProductProgress upper_pre (upper_pre - lower_pre ) prime_pre 1 1 1 ) ”
  &&  emp
) \/
(
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (PreH1 : (lower_pre > (upper_pre - lower_pre ))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre )) (PreH4 : (0 <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) ,
  TT && emp 
|--
  “ (DigitProductProgress upper_pre (upper_pre - lower_pre ) prime_pre 1 1 1 ) ” 
  &&  “ ((upper_pre - lower_pre ) = (Z.min (lower_pre) ((upper_pre - lower_pre )))) ”
  &&  emp
).

Definition binomial_digit_mod_prime_entail_wit_1_1_split_goal_1 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (PreH1 : (lower_pre > (upper_pre - lower_pre ))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre )) (PreH4 : (0 <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) ,
  (DigitProductProgress upper_pre (upper_pre - lower_pre ) prime_pre 1 1 1 )
.

Definition binomial_digit_mod_prime_entail_wit_1_1_split_goal_2 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (PreH1 : (lower_pre > (upper_pre - lower_pre ))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre )) (PreH4 : (0 <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) ,
  ((upper_pre - lower_pre ) = (Z.min (lower_pre) ((upper_pre - lower_pre ))))
.

Definition binomial_digit_mod_prime_entail_wit_1_2 := 
(
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (PreH1 : (lower_pre <= (upper_pre - lower_pre ))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre )) (PreH4 : (0 <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) ,
  TT && emp 
|--
  “ (PrimeForLucas prime_pre ) ” 
  &&  “ (0 <= lower_pre) ” 
  &&  “ (lower_pre <= upper_pre) ” 
  &&  “ (upper_pre < prime_pre) ” 
  &&  “ (2 <= prime_pre) ” 
  &&  “ (prime_pre <= 100000) ” 
  &&  “ (lower_pre = (Z.min (lower_pre) ((upper_pre - lower_pre )))) ” 
  &&  “ (0 <= lower_pre) ” 
  &&  “ (lower_pre <= (upper_pre - lower_pre )) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (lower_pre + 1 )) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 < prime_pre) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 < prime_pre) ” 
  &&  “ (DigitProductProgress upper_pre lower_pre prime_pre 1 1 1 ) ”
  &&  emp
) \/
(
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (PreH1 : (lower_pre <= (upper_pre - lower_pre ))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre )) (PreH4 : (0 <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) ,
  TT && emp 
|--
  “ (DigitProductProgress upper_pre lower_pre prime_pre 1 1 1 ) ” 
  &&  “ (lower_pre = (Z.min (lower_pre) ((upper_pre - lower_pre )))) ”
  &&  emp
).

Definition binomial_digit_mod_prime_entail_wit_1_2_split_goal_1 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (PreH1 : (lower_pre <= (upper_pre - lower_pre ))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre )) (PreH4 : (0 <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) ,
  (DigitProductProgress upper_pre lower_pre prime_pre 1 1 1 )
.

Definition binomial_digit_mod_prime_entail_wit_1_2_split_goal_2 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (PreH1 : (lower_pre <= (upper_pre - lower_pre ))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre )) (PreH4 : (0 <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) ,
  (lower_pre = (Z.min (lower_pre) ((upper_pre - lower_pre ))))
.

Definition binomial_digit_mod_prime_entail_wit_2 := 
(
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (lower: Z) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (Z.min (lower_pre) ((upper_pre - lower_pre ))))) (PreH9 : (0 <= lower)) (PreH10 : (lower <= (upper_pre - lower ))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower + 1 ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator )) ,
  TT && emp 
|--
  “ (PrimeForLucas prime_pre ) ” 
  &&  “ (0 <= lower_pre) ” 
  &&  “ (lower_pre <= upper_pre) ” 
  &&  “ (upper_pre < prime_pre) ” 
  &&  “ (2 <= prime_pre) ” 
  &&  “ (prime_pre <= 100000) ” 
  &&  “ (lower = (Z.min (lower_pre) ((upper_pre - lower_pre )))) ” 
  &&  “ (0 <= lower) ” 
  &&  “ (lower <= (upper_pre - lower )) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (lower + 1 )) ” 
  &&  “ (0 <= (signed_last_nbits (((numerator * ((upper_pre - lower ) + i ) ) % ( prime_pre ) )) (32))) ” 
  &&  “ ((signed_last_nbits (((numerator * ((upper_pre - lower ) + i ) ) % ( prime_pre ) )) (32)) < prime_pre) ” 
  &&  “ (0 <= (signed_last_nbits (((denominator * i ) % ( prime_pre ) )) (32))) ” 
  &&  “ ((signed_last_nbits (((denominator * i ) % ( prime_pre ) )) (32)) < prime_pre) ” 
  &&  “ (DigitProductProgress upper_pre lower prime_pre (i + 1 ) (signed_last_nbits (((numerator * ((upper_pre - lower ) + i ) ) % ( prime_pre ) )) (32)) (signed_last_nbits (((denominator * i ) % ( prime_pre ) )) (32)) ) ”
  &&  emp
) \/
(
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (lower: Z) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (Z.min (lower_pre) ((upper_pre - lower_pre ))))) (PreH9 : (0 <= lower)) (PreH10 : (lower <= (upper_pre - lower ))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower + 1 ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator )) ,
  TT && emp 
|--
  “ (DigitProductProgress upper_pre lower prime_pre (i + 1 ) (signed_last_nbits (((numerator * ((upper_pre - lower ) + i ) ) % ( prime_pre ) )) (32)) (signed_last_nbits (((denominator * i ) % ( prime_pre ) )) (32)) ) ” 
  &&  “ ((signed_last_nbits (((denominator * i ) % ( prime_pre ) )) (32)) < prime_pre) ” 
  &&  “ (0 <= (signed_last_nbits (((denominator * i ) % ( prime_pre ) )) (32))) ” 
  &&  “ ((signed_last_nbits (((numerator * ((upper_pre - lower ) + i ) ) % ( prime_pre ) )) (32)) < prime_pre) ” 
  &&  “ (0 <= (signed_last_nbits (((numerator * ((upper_pre - lower ) + i ) ) % ( prime_pre ) )) (32))) ”
  &&  emp
).

Definition binomial_digit_mod_prime_entail_wit_2_split_goal_1 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (lower: Z) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (Z.min (lower_pre) ((upper_pre - lower_pre ))))) (PreH9 : (0 <= lower)) (PreH10 : (lower <= (upper_pre - lower ))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower + 1 ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator )) ,
  (DigitProductProgress upper_pre lower prime_pre (i + 1 ) (signed_last_nbits (((numerator * ((upper_pre - lower ) + i ) ) % ( prime_pre ) )) (32)) (signed_last_nbits (((denominator * i ) % ( prime_pre ) )) (32)) )
.

Definition binomial_digit_mod_prime_entail_wit_2_split_goal_2 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (lower: Z) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (Z.min (lower_pre) ((upper_pre - lower_pre ))))) (PreH9 : (0 <= lower)) (PreH10 : (lower <= (upper_pre - lower ))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower + 1 ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator )) ,
  ((signed_last_nbits (((denominator * i ) % ( prime_pre ) )) (32)) < prime_pre)
.

Definition binomial_digit_mod_prime_entail_wit_2_split_goal_3 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (lower: Z) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (Z.min (lower_pre) ((upper_pre - lower_pre ))))) (PreH9 : (0 <= lower)) (PreH10 : (lower <= (upper_pre - lower ))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower + 1 ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator )) ,
  (0 <= (signed_last_nbits (((denominator * i ) % ( prime_pre ) )) (32)))
.

Definition binomial_digit_mod_prime_entail_wit_2_split_goal_4 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (lower: Z) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (Z.min (lower_pre) ((upper_pre - lower_pre ))))) (PreH9 : (0 <= lower)) (PreH10 : (lower <= (upper_pre - lower ))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower + 1 ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator )) ,
  ((signed_last_nbits (((numerator * ((upper_pre - lower ) + i ) ) % ( prime_pre ) )) (32)) < prime_pre)
.

Definition binomial_digit_mod_prime_entail_wit_2_split_goal_5 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (lower: Z) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (Z.min (lower_pre) ((upper_pre - lower_pre ))))) (PreH9 : (0 <= lower)) (PreH10 : (lower <= (upper_pre - lower ))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower + 1 ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator )) ,
  (0 <= (signed_last_nbits (((numerator * ((upper_pre - lower ) + i ) ) % ( prime_pre ) )) (32)))
.

Definition binomial_digit_mod_prime_return_wit_1 := 
(
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (lower: Z) (retval: Z) (PreH1 : (ModularPower denominator (prime_pre - 2 ) prime_pre retval )) (PreH2 : (i > lower)) (PreH3 : (PrimeForLucas prime_pre )) (PreH4 : (0 <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (lower = (Z.min (lower_pre) ((upper_pre - lower_pre ))))) (PreH10 : (0 <= lower)) (PreH11 : (lower <= (upper_pre - lower ))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1 ))) (PreH14 : (0 <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : (0 <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator )) ,
  TT && emp 
|--
  “ (BinomialDigitResidue upper_pre lower_pre prime_pre (signed_last_nbits (((numerator * retval ) % ( prime_pre ) )) (32)) ) ”
  &&  emp
) \/
(
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (lower: Z) (retval: Z) (PreH1 : (ModularPower denominator (prime_pre - 2 ) prime_pre retval )) (PreH2 : (i > lower)) (PreH3 : (PrimeForLucas prime_pre )) (PreH4 : (0 <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (lower = (Z.min (lower_pre) ((upper_pre - lower_pre ))))) (PreH10 : (0 <= lower)) (PreH11 : (lower <= (upper_pre - lower ))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1 ))) (PreH14 : (0 <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : (0 <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator )) ,
  TT && emp 
|--
  “ (BinomialDigitResidue upper_pre lower_pre prime_pre (signed_last_nbits (((numerator * retval ) % ( prime_pre ) )) (32)) ) ”
  &&  emp
).

Definition binomial_digit_mod_prime_return_wit_1_split_goal_1 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (lower: Z) (retval: Z) (PreH1 : (ModularPower denominator (prime_pre - 2 ) prime_pre retval )) (PreH2 : (i > lower)) (PreH3 : (PrimeForLucas prime_pre )) (PreH4 : (0 <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (lower = (Z.min (lower_pre) ((upper_pre - lower_pre ))))) (PreH10 : (0 <= lower)) (PreH11 : (lower <= (upper_pre - lower ))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1 ))) (PreH14 : (0 <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : (0 <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator )) ,
  (BinomialDigitResidue upper_pre lower_pre prime_pre (signed_last_nbits (((numerator * retval ) % ( prime_pre ) )) (32)) )
.

Definition binomial_digit_mod_prime_partial_solve_wit_1_pure := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (lower: Z) (PreH1 : (i > lower)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (Z.min (lower_pre) ((upper_pre - lower_pre ))))) (PreH9 : (0 <= lower)) (PreH10 : (lower <= (upper_pre - lower ))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower + 1 ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator )) ,
  ((( &( "inverse" ) )) # Int  |->_)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "numerator" ) )) # Int  |-> numerator)
  **  ((( &( "denominator" ) )) # Int  |-> denominator)
|--
  “ (0 <= denominator) ” 
  &&  “ (denominator < prime_pre) ” 
  &&  “ (0 <= (prime_pre - 2 )) ” 
  &&  “ (2 <= prime_pre) ” 
  &&  “ (prime_pre <= 100000) ”
.

Definition binomial_digit_mod_prime_partial_solve_wit_1_aux := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (lower: Z) (PreH1 : (i > lower)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (Z.min (lower_pre) ((upper_pre - lower_pre ))))) (PreH9 : (0 <= lower)) (PreH10 : (lower <= (upper_pre - lower ))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower + 1 ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator )) ,
  TT && emp 
|--
  “ (0 <= denominator) ” 
  &&  “ (denominator < prime_pre) ” 
  &&  “ (0 <= (prime_pre - 2 )) ” 
  &&  “ (2 <= prime_pre) ” 
  &&  “ (prime_pre <= 100000) ” 
  &&  “ (i > lower) ” 
  &&  “ (PrimeForLucas prime_pre ) ” 
  &&  “ (0 <= lower_pre) ” 
  &&  “ (lower_pre <= upper_pre) ” 
  &&  “ (upper_pre < prime_pre) ” 
  &&  “ (2 <= prime_pre) ” 
  &&  “ (prime_pre <= 100000) ” 
  &&  “ (lower = (Z.min (lower_pre) ((upper_pre - lower_pre )))) ” 
  &&  “ (0 <= lower) ” 
  &&  “ (lower <= (upper_pre - lower )) ” 
  &&  “ (1 <= i) ” 
  &&  “ (i <= (lower + 1 )) ” 
  &&  “ (0 <= numerator) ” 
  &&  “ (numerator < prime_pre) ” 
  &&  “ (0 <= denominator) ” 
  &&  “ (denominator < prime_pre) ” 
  &&  “ (DigitProductProgress upper_pre lower prime_pre i numerator denominator ) ”
  &&  emp
.

Definition binomial_digit_mod_prime_partial_solve_wit_1 := binomial_digit_mod_prime_partial_solve_wit_1_pure -> binomial_digit_mod_prime_partial_solve_wit_1_aux.

(*----- Function lucas_theorem -----*)

Definition lucas_theorem_safety_wit_1 := 
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (PrimeForLucas prime_pre )) ,
  ((( &( "upper" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
|--
  “ ((n_pre + m_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre + m_pre )) ”
.

Definition lucas_theorem_safety_wit_2 := 
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (PrimeForLucas prime_pre )) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "lower" ) )) # Int  |-> n_pre)
  **  ((( &( "upper" ) )) # Int  |-> (n_pre + m_pre ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition lucas_theorem_safety_wit_3 := 
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (result: Z) (upper: Z) (lower: Z) (PreH1 : (0 <= n_pre)) (PreH2 : (0 <= m_pre)) (PreH3 : (2 <= prime_pre)) (PreH4 : (prime_pre <= 100000)) (PreH5 : (PrimeForLucas prime_pre )) (PreH6 : (0 <= lower)) (PreH7 : (lower <= upper)) (PreH8 : (0 <= result)) (PreH9 : (result < prime_pre)) (PreH10 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "upper" ) )) # Int  |-> upper)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition lucas_theorem_safety_wit_4 := 
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (result: Z) (upper: Z) (lower: Z) (PreH1 : (upper <= 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (0 <= m_pre)) (PreH4 : (2 <= prime_pre)) (PreH5 : (prime_pre <= 100000)) (PreH6 : (PrimeForLucas prime_pre )) (PreH7 : (0 <= lower)) (PreH8 : (lower <= upper)) (PreH9 : (0 <= result)) (PreH10 : (result < prime_pre)) (PreH11 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "upper" ) )) # Int  |-> upper)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition lucas_theorem_safety_wit_5 := 
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (result: Z) (upper: Z) (lower: Z) (PreH1 : (lower > 0)) (PreH2 : (upper <= 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (0 <= m_pre)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (PrimeForLucas prime_pre )) (PreH8 : (0 <= lower)) (PreH9 : (lower <= upper)) (PreH10 : (0 <= result)) (PreH11 : (result < prime_pre)) (PreH12 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "upper" ) )) # Int  |-> upper)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ False ”
.

Definition lucas_theorem_safety_wit_6 := 
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (result: Z) (upper: Z) (lower: Z) (PreH1 : (upper > 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (0 <= m_pre)) (PreH4 : (2 <= prime_pre)) (PreH5 : (prime_pre <= 100000)) (PreH6 : (PrimeForLucas prime_pre )) (PreH7 : (0 <= lower)) (PreH8 : (lower <= upper)) (PreH9 : (0 <= result)) (PreH10 : (result < prime_pre)) (PreH11 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  ((( &( "upper_digit" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "upper" ) )) # Int  |-> upper)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ ((upper <> (INT_MIN)) \/ (prime_pre <> (-1))) ” 
  &&  “ (prime_pre <> 0) ”
.

Definition lucas_theorem_safety_wit_7 := 
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (result: Z) (upper: Z) (lower: Z) (PreH1 : (upper > 0)) (PreH2 : (0 <= n_pre)) (PreH3 : (0 <= m_pre)) (PreH4 : (2 <= prime_pre)) (PreH5 : (prime_pre <= 100000)) (PreH6 : (PrimeForLucas prime_pre )) (PreH7 : (0 <= lower)) (PreH8 : (lower <= upper)) (PreH9 : (0 <= result)) (PreH10 : (result < prime_pre)) (PreH11 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  ((( &( "lower_digit" ) )) # Int  |->_)
  **  ((( &( "upper_digit" ) )) # Int  |-> (upper % ( prime_pre ) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "upper" ) )) # Int  |-> upper)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ ((lower <> (INT_MIN)) \/ (prime_pre <> (-1))) ” 
  &&  “ (prime_pre <> 0) ”
.

Definition lucas_theorem_safety_wit_8 := 
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (result: Z) (upper: Z) (lower: Z) (PreH1 : ((lower % ( prime_pre ) ) > (upper % ( prime_pre ) ))) (PreH2 : (upper > 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (0 <= m_pre)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (PrimeForLucas prime_pre )) (PreH8 : (0 <= lower)) (PreH9 : (lower <= upper)) (PreH10 : (0 <= result)) (PreH11 : (result < prime_pre)) (PreH12 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  ((( &( "lower_digit" ) )) # Int  |-> (lower % ( prime_pre ) ))
  **  ((( &( "upper_digit" ) )) # Int  |-> (upper % ( prime_pre ) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "upper" ) )) # Int  |-> upper)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition lucas_theorem_safety_wit_9 := 
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (result: Z) (upper: Z) (lower: Z) (retval: Z) (PreH1 : (BinomialDigitResidue (upper % ( prime_pre ) ) (lower % ( prime_pre ) ) prime_pre retval )) (PreH2 : ((lower % ( prime_pre ) ) <= (upper % ( prime_pre ) ))) (PreH3 : (upper > 0)) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= m_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (PrimeForLucas prime_pre )) (PreH9 : (0 <= lower)) (PreH10 : (lower <= upper)) (PreH11 : (0 <= result)) (PreH12 : (result < prime_pre)) (PreH13 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  ((( &( "product" ) )) # Int64  |->_)
  **  ((( &( "digit_binomial" ) )) # Int  |-> retval)
  **  ((( &( "lower_digit" ) )) # Int  |-> (lower % ( prime_pre ) ))
  **  ((( &( "upper_digit" ) )) # Int  |-> (upper % ( prime_pre ) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "upper" ) )) # Int  |-> upper)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ ((result * retval ) <= INT64_MAX) ” 
  &&  “ ((INT64_MIN) <= (result * retval )) ”
.

Definition lucas_theorem_safety_wit_10 := 
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (result: Z) (upper: Z) (lower: Z) (retval: Z) (PreH1 : (BinomialDigitResidue (upper % ( prime_pre ) ) (lower % ( prime_pre ) ) prime_pre retval )) (PreH2 : ((lower % ( prime_pre ) ) <= (upper % ( prime_pre ) ))) (PreH3 : (upper > 0)) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= m_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (PrimeForLucas prime_pre )) (PreH9 : (0 <= lower)) (PreH10 : (lower <= upper)) (PreH11 : (0 <= result)) (PreH12 : (result < prime_pre)) (PreH13 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  ((( &( "product" ) )) # Int64  |-> (result * retval ))
  **  ((( &( "digit_binomial" ) )) # Int  |-> retval)
  **  ((( &( "lower_digit" ) )) # Int  |-> (lower % ( prime_pre ) ))
  **  ((( &( "upper_digit" ) )) # Int  |-> (upper % ( prime_pre ) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "upper" ) )) # Int  |-> upper)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ (((result * retval ) <> (INT64_MIN)) \/ (prime_pre <> (-1))) ” 
  &&  “ (prime_pre <> 0) ”
.

Definition lucas_theorem_safety_wit_11 := 
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (result: Z) (upper: Z) (lower: Z) (retval: Z) (PreH1 : (BinomialDigitResidue (upper % ( prime_pre ) ) (lower % ( prime_pre ) ) prime_pre retval )) (PreH2 : ((lower % ( prime_pre ) ) <= (upper % ( prime_pre ) ))) (PreH3 : (upper > 0)) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= m_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (PrimeForLucas prime_pre )) (PreH9 : (0 <= lower)) (PreH10 : (lower <= upper)) (PreH11 : (0 <= result)) (PreH12 : (result < prime_pre)) (PreH13 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  ((( &( "product" ) )) # Int64  |-> (result * retval ))
  **  ((( &( "digit_binomial" ) )) # Int  |-> retval)
  **  ((( &( "lower_digit" ) )) # Int  |-> (lower % ( prime_pre ) ))
  **  ((( &( "upper_digit" ) )) # Int  |-> (upper % ( prime_pre ) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "upper" ) )) # Int  |-> upper)
  **  ((( &( "result" ) )) # Int  |-> (signed_last_nbits (((result * retval ) % ( prime_pre ) )) (32)))
|--
  “ ((upper <> (INT_MIN)) \/ (prime_pre <> (-1))) ” 
  &&  “ (prime_pre <> 0) ”
.

Definition lucas_theorem_safety_wit_12 := 
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (result: Z) (upper: Z) (lower: Z) (retval: Z) (PreH1 : (BinomialDigitResidue (upper % ( prime_pre ) ) (lower % ( prime_pre ) ) prime_pre retval )) (PreH2 : ((lower % ( prime_pre ) ) <= (upper % ( prime_pre ) ))) (PreH3 : (upper > 0)) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= m_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (PrimeForLucas prime_pre )) (PreH9 : (0 <= lower)) (PreH10 : (lower <= upper)) (PreH11 : (0 <= result)) (PreH12 : (result < prime_pre)) (PreH13 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  ((( &( "product" ) )) # Int64  |-> (result * retval ))
  **  ((( &( "digit_binomial" ) )) # Int  |-> retval)
  **  ((( &( "lower_digit" ) )) # Int  |-> (lower % ( prime_pre ) ))
  **  ((( &( "upper_digit" ) )) # Int  |-> (upper % ( prime_pre ) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "upper" ) )) # Int  |-> (upper ÷ prime_pre ))
  **  ((( &( "result" ) )) # Int  |-> (signed_last_nbits (((result * retval ) % ( prime_pre ) )) (32)))
|--
  “ ((lower <> (INT_MIN)) \/ (prime_pre <> (-1))) ” 
  &&  “ (prime_pre <> 0) ”
.

Definition lucas_theorem_entail_wit_1 := 
(
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (PrimeForLucas prime_pre )) ,
  TT && emp 
|--
  “ (0 <= n_pre) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (2 <= prime_pre) ” 
  &&  “ (prime_pre <= 100000) ” 
  &&  “ (PrimeForLucas prime_pre ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= (n_pre + m_pre )) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 < prime_pre) ” 
  &&  “ (LucasProgress (n_pre + m_pre ) n_pre prime_pre (n_pre + m_pre ) n_pre 1 ) ”
  &&  emp
) \/
(
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (PrimeForLucas prime_pre )) ,
  TT && emp 
|--
  “ (LucasProgress (n_pre + m_pre ) n_pre prime_pre (n_pre + m_pre ) n_pre 1 ) ”
  &&  emp
).

Definition lucas_theorem_entail_wit_1_split_goal_1 := 
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (PrimeForLucas prime_pre )) ,
  (LucasProgress (n_pre + m_pre ) n_pre prime_pre (n_pre + m_pre ) n_pre 1 )
.

Definition lucas_theorem_entail_wit_2 := 
(
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (result: Z) (upper: Z) (lower: Z) (retval: Z) (PreH1 : (BinomialDigitResidue (upper % ( prime_pre ) ) (lower % ( prime_pre ) ) prime_pre retval )) (PreH2 : ((lower % ( prime_pre ) ) <= (upper % ( prime_pre ) ))) (PreH3 : (upper > 0)) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= m_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (PrimeForLucas prime_pre )) (PreH9 : (0 <= lower)) (PreH10 : (lower <= upper)) (PreH11 : (0 <= result)) (PreH12 : (result < prime_pre)) (PreH13 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  TT && emp 
|--
  “ (0 <= n_pre) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (2 <= prime_pre) ” 
  &&  “ (prime_pre <= 100000) ” 
  &&  “ (PrimeForLucas prime_pre ) ” 
  &&  “ (0 <= (lower ÷ prime_pre )) ” 
  &&  “ ((lower ÷ prime_pre ) <= (upper ÷ prime_pre )) ” 
  &&  “ (0 <= (signed_last_nbits (((result * retval ) % ( prime_pre ) )) (32))) ” 
  &&  “ ((signed_last_nbits (((result * retval ) % ( prime_pre ) )) (32)) < prime_pre) ” 
  &&  “ (LucasProgress (n_pre + m_pre ) n_pre prime_pre (upper ÷ prime_pre ) (lower ÷ prime_pre ) (signed_last_nbits (((result * retval ) % ( prime_pre ) )) (32)) ) ”
  &&  emp
) \/
(
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (result: Z) (upper: Z) (lower: Z) (retval: Z) (PreH1 : (BinomialDigitResidue (upper % ( prime_pre ) ) (lower % ( prime_pre ) ) prime_pre retval )) (PreH2 : ((lower % ( prime_pre ) ) <= (upper % ( prime_pre ) ))) (PreH3 : (upper > 0)) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= m_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (PrimeForLucas prime_pre )) (PreH9 : (0 <= lower)) (PreH10 : (lower <= upper)) (PreH11 : (0 <= result)) (PreH12 : (result < prime_pre)) (PreH13 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  TT && emp 
|--
  “ (LucasProgress (n_pre + m_pre ) n_pre prime_pre (upper ÷ prime_pre ) (lower ÷ prime_pre ) (signed_last_nbits (((result * retval ) % ( prime_pre ) )) (32)) ) ” 
  &&  “ ((signed_last_nbits (((result * retval ) % ( prime_pre ) )) (32)) < prime_pre) ” 
  &&  “ (0 <= (signed_last_nbits (((result * retval ) % ( prime_pre ) )) (32))) ” 
  &&  “ ((lower ÷ prime_pre ) <= (upper ÷ prime_pre )) ” 
  &&  “ (0 <= (lower ÷ prime_pre )) ”
  &&  emp
).

Definition lucas_theorem_entail_wit_2_split_goal_1 := 
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (result: Z) (upper: Z) (lower: Z) (retval: Z) (PreH1 : (BinomialDigitResidue (upper % ( prime_pre ) ) (lower % ( prime_pre ) ) prime_pre retval )) (PreH2 : ((lower % ( prime_pre ) ) <= (upper % ( prime_pre ) ))) (PreH3 : (upper > 0)) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= m_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (PrimeForLucas prime_pre )) (PreH9 : (0 <= lower)) (PreH10 : (lower <= upper)) (PreH11 : (0 <= result)) (PreH12 : (result < prime_pre)) (PreH13 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  (LucasProgress (n_pre + m_pre ) n_pre prime_pre (upper ÷ prime_pre ) (lower ÷ prime_pre ) (signed_last_nbits (((result * retval ) % ( prime_pre ) )) (32)) )
.

Definition lucas_theorem_entail_wit_2_split_goal_2 := 
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (result: Z) (upper: Z) (lower: Z) (retval: Z) (PreH1 : (BinomialDigitResidue (upper % ( prime_pre ) ) (lower % ( prime_pre ) ) prime_pre retval )) (PreH2 : ((lower % ( prime_pre ) ) <= (upper % ( prime_pre ) ))) (PreH3 : (upper > 0)) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= m_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (PrimeForLucas prime_pre )) (PreH9 : (0 <= lower)) (PreH10 : (lower <= upper)) (PreH11 : (0 <= result)) (PreH12 : (result < prime_pre)) (PreH13 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  ((signed_last_nbits (((result * retval ) % ( prime_pre ) )) (32)) < prime_pre)
.

Definition lucas_theorem_entail_wit_2_split_goal_3 := 
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (result: Z) (upper: Z) (lower: Z) (retval: Z) (PreH1 : (BinomialDigitResidue (upper % ( prime_pre ) ) (lower % ( prime_pre ) ) prime_pre retval )) (PreH2 : ((lower % ( prime_pre ) ) <= (upper % ( prime_pre ) ))) (PreH3 : (upper > 0)) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= m_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (PrimeForLucas prime_pre )) (PreH9 : (0 <= lower)) (PreH10 : (lower <= upper)) (PreH11 : (0 <= result)) (PreH12 : (result < prime_pre)) (PreH13 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  (0 <= (signed_last_nbits (((result * retval ) % ( prime_pre ) )) (32)))
.

Definition lucas_theorem_entail_wit_2_split_goal_4 := 
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (result: Z) (upper: Z) (lower: Z) (retval: Z) (PreH1 : (BinomialDigitResidue (upper % ( prime_pre ) ) (lower % ( prime_pre ) ) prime_pre retval )) (PreH2 : ((lower % ( prime_pre ) ) <= (upper % ( prime_pre ) ))) (PreH3 : (upper > 0)) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= m_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (PrimeForLucas prime_pre )) (PreH9 : (0 <= lower)) (PreH10 : (lower <= upper)) (PreH11 : (0 <= result)) (PreH12 : (result < prime_pre)) (PreH13 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  ((lower ÷ prime_pre ) <= (upper ÷ prime_pre ))
.

Definition lucas_theorem_entail_wit_2_split_goal_5 := 
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (result: Z) (upper: Z) (lower: Z) (retval: Z) (PreH1 : (BinomialDigitResidue (upper % ( prime_pre ) ) (lower % ( prime_pre ) ) prime_pre retval )) (PreH2 : ((lower % ( prime_pre ) ) <= (upper % ( prime_pre ) ))) (PreH3 : (upper > 0)) (PreH4 : (0 <= n_pre)) (PreH5 : (0 <= m_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (PrimeForLucas prime_pre )) (PreH9 : (0 <= lower)) (PreH10 : (lower <= upper)) (PreH11 : (0 <= result)) (PreH12 : (result < prime_pre)) (PreH13 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  (0 <= (lower ÷ prime_pre ))
.

Definition lucas_theorem_return_wit_1 := 
(
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (result: Z) (upper: Z) (lower: Z) (PreH1 : (lower <= 0)) (PreH2 : (upper <= 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (0 <= m_pre)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (PrimeForLucas prime_pre )) (PreH8 : (0 <= lower)) (PreH9 : (lower <= upper)) (PreH10 : (0 <= result)) (PreH11 : (result < prime_pre)) (PreH12 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  TT && emp 
|--
  “ (LucasBinomialResidue n_pre m_pre prime_pre result ) ”
  &&  emp
) \/
(
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (result: Z) (upper: Z) (lower: Z) (PreH1 : (lower <= 0)) (PreH2 : (upper <= 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (0 <= m_pre)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (PrimeForLucas prime_pre )) (PreH8 : (0 <= lower)) (PreH9 : (lower <= upper)) (PreH10 : (0 <= result)) (PreH11 : (result < prime_pre)) (PreH12 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  TT && emp 
|--
  “ (LucasBinomialResidue n_pre m_pre prime_pre result ) ”
  &&  emp
).

Definition lucas_theorem_return_wit_1_split_goal_1 := 
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (result: Z) (upper: Z) (lower: Z) (PreH1 : (lower <= 0)) (PreH2 : (upper <= 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (0 <= m_pre)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (PrimeForLucas prime_pre )) (PreH8 : (0 <= lower)) (PreH9 : (lower <= upper)) (PreH10 : (0 <= result)) (PreH11 : (result < prime_pre)) (PreH12 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  (LucasBinomialResidue n_pre m_pre prime_pre result )
.

Definition lucas_theorem_return_wit_2 := 
(
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (result: Z) (upper: Z) (lower: Z) (PreH1 : ((lower % ( prime_pre ) ) > (upper % ( prime_pre ) ))) (PreH2 : (upper > 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (0 <= m_pre)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (PrimeForLucas prime_pre )) (PreH8 : (0 <= lower)) (PreH9 : (lower <= upper)) (PreH10 : (0 <= result)) (PreH11 : (result < prime_pre)) (PreH12 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  TT && emp 
|--
  “ (LucasBinomialResidue n_pre m_pre prime_pre 0 ) ”
  &&  emp
) \/
(
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (result: Z) (upper: Z) (lower: Z) (PreH1 : ((lower % ( prime_pre ) ) > (upper % ( prime_pre ) ))) (PreH2 : (upper > 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (0 <= m_pre)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (PrimeForLucas prime_pre )) (PreH8 : (0 <= lower)) (PreH9 : (lower <= upper)) (PreH10 : (0 <= result)) (PreH11 : (result < prime_pre)) (PreH12 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  TT && emp 
|--
  “ (LucasBinomialResidue n_pre m_pre prime_pre 0 ) ”
  &&  emp
).

Definition lucas_theorem_return_wit_2_split_goal_1 := 
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (result: Z) (upper: Z) (lower: Z) (PreH1 : ((lower % ( prime_pre ) ) > (upper % ( prime_pre ) ))) (PreH2 : (upper > 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (0 <= m_pre)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (PrimeForLucas prime_pre )) (PreH8 : (0 <= lower)) (PreH9 : (lower <= upper)) (PreH10 : (0 <= result)) (PreH11 : (result < prime_pre)) (PreH12 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  (LucasBinomialResidue n_pre m_pre prime_pre 0 )
.

Definition lucas_theorem_partial_solve_wit_1_pure := 
(
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (result: Z) (upper: Z) (lower: Z) (PreH1 : ((lower % ( prime_pre ) ) <= (upper % ( prime_pre ) ))) (PreH2 : (upper > 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (0 <= m_pre)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (PrimeForLucas prime_pre )) (PreH8 : (0 <= lower)) (PreH9 : (lower <= upper)) (PreH10 : (0 <= result)) (PreH11 : (result < prime_pre)) (PreH12 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  ((( &( "digit_binomial" ) )) # Int  |->_)
  **  ((( &( "lower_digit" ) )) # Int  |-> (lower % ( prime_pre ) ))
  **  ((( &( "upper_digit" ) )) # Int  |-> (upper % ( prime_pre ) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "upper" ) )) # Int  |-> upper)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ (PrimeForLucas prime_pre ) ” 
  &&  “ ((lower % ( prime_pre ) ) <= (upper % ( prime_pre ) )) ” 
  &&  “ (2 <= prime_pre) ” 
  &&  “ (prime_pre <= 100000) ” 
  &&  “ ((upper % ( prime_pre ) ) < prime_pre) ” 
  &&  “ (0 <= (lower % ( prime_pre ) )) ”
) \/
(
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (result: Z) (upper: Z) (lower: Z) (PreH1 : (result <= INT_MAX)) (PreH2 : (upper <= INT_MAX)) (PreH3 : (lower <= INT_MAX)) (PreH4 : (prime_pre <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((upper % ( prime_pre ) ) <= INT_MAX)) (PreH8 : ((lower % ( prime_pre ) ) <= INT_MAX)) (PreH9 : (result >= INT_MIN)) (PreH10 : (upper >= INT_MIN)) (PreH11 : (lower >= INT_MIN)) (PreH12 : (prime_pre >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : ((upper % ( prime_pre ) ) >= INT_MIN)) (PreH16 : ((lower % ( prime_pre ) ) >= INT_MIN)) (PreH17 : ((lower % ( prime_pre ) ) <= (upper % ( prime_pre ) ))) (PreH18 : (upper > 0)) (PreH19 : (0 <= n_pre)) (PreH20 : (0 <= m_pre)) (PreH21 : (2 <= prime_pre)) (PreH22 : (prime_pre <= 100000)) (PreH23 : (PrimeForLucas prime_pre )) (PreH24 : (0 <= lower)) (PreH25 : (lower <= upper)) (PreH26 : (0 <= result)) (PreH27 : (result < prime_pre)) (PreH28 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  ((( &( "digit_binomial" ) )) # Int  |->_)
  **  ((( &( "lower_digit" ) )) # Int  |-> (lower % ( prime_pre ) ))
  **  ((( &( "upper_digit" ) )) # Int  |-> (upper % ( prime_pre ) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "upper" ) )) # Int  |-> upper)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ (0 <= (lower % ( prime_pre ) )) ” 
  &&  “ ((upper % ( prime_pre ) ) < prime_pre) ”
).

Definition lucas_theorem_partial_solve_wit_1_pure_split_goal_1 := 
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (result: Z) (upper: Z) (lower: Z) (PreH1 : (result <= INT_MAX)) (PreH2 : (upper <= INT_MAX)) (PreH3 : (lower <= INT_MAX)) (PreH4 : (prime_pre <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((upper % ( prime_pre ) ) <= INT_MAX)) (PreH8 : ((lower % ( prime_pre ) ) <= INT_MAX)) (PreH9 : (result >= INT_MIN)) (PreH10 : (upper >= INT_MIN)) (PreH11 : (lower >= INT_MIN)) (PreH12 : (prime_pre >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : ((upper % ( prime_pre ) ) >= INT_MIN)) (PreH16 : ((lower % ( prime_pre ) ) >= INT_MIN)) (PreH17 : ((lower % ( prime_pre ) ) <= (upper % ( prime_pre ) ))) (PreH18 : (upper > 0)) (PreH19 : (0 <= n_pre)) (PreH20 : (0 <= m_pre)) (PreH21 : (2 <= prime_pre)) (PreH22 : (prime_pre <= 100000)) (PreH23 : (PrimeForLucas prime_pre )) (PreH24 : (0 <= lower)) (PreH25 : (lower <= upper)) (PreH26 : (0 <= result)) (PreH27 : (result < prime_pre)) (PreH28 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  ((( &( "digit_binomial" ) )) # Int  |->_)
  **  ((( &( "lower_digit" ) )) # Int  |-> (lower % ( prime_pre ) ))
  **  ((( &( "upper_digit" ) )) # Int  |-> (upper % ( prime_pre ) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "upper" ) )) # Int  |-> upper)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ (0 <= (lower % ( prime_pre ) )) ”
.

Definition lucas_theorem_partial_solve_wit_1_pure_split_goal_2 := 
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (result: Z) (upper: Z) (lower: Z) (PreH1 : (result <= INT_MAX)) (PreH2 : (upper <= INT_MAX)) (PreH3 : (lower <= INT_MAX)) (PreH4 : (prime_pre <= INT_MAX)) (PreH5 : (m_pre <= INT_MAX)) (PreH6 : (n_pre <= INT_MAX)) (PreH7 : ((upper % ( prime_pre ) ) <= INT_MAX)) (PreH8 : ((lower % ( prime_pre ) ) <= INT_MAX)) (PreH9 : (result >= INT_MIN)) (PreH10 : (upper >= INT_MIN)) (PreH11 : (lower >= INT_MIN)) (PreH12 : (prime_pre >= INT_MIN)) (PreH13 : (m_pre >= INT_MIN)) (PreH14 : (n_pre >= INT_MIN)) (PreH15 : ((upper % ( prime_pre ) ) >= INT_MIN)) (PreH16 : ((lower % ( prime_pre ) ) >= INT_MIN)) (PreH17 : ((lower % ( prime_pre ) ) <= (upper % ( prime_pre ) ))) (PreH18 : (upper > 0)) (PreH19 : (0 <= n_pre)) (PreH20 : (0 <= m_pre)) (PreH21 : (2 <= prime_pre)) (PreH22 : (prime_pre <= 100000)) (PreH23 : (PrimeForLucas prime_pre )) (PreH24 : (0 <= lower)) (PreH25 : (lower <= upper)) (PreH26 : (0 <= result)) (PreH27 : (result < prime_pre)) (PreH28 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  ((( &( "digit_binomial" ) )) # Int  |->_)
  **  ((( &( "lower_digit" ) )) # Int  |-> (lower % ( prime_pre ) ))
  **  ((( &( "upper_digit" ) )) # Int  |-> (upper % ( prime_pre ) ))
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "upper" ) )) # Int  |-> upper)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ ((upper % ( prime_pre ) ) < prime_pre) ”
.

Definition lucas_theorem_partial_solve_wit_1_aux := 
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (result: Z) (upper: Z) (lower: Z) (PreH1 : ((lower % ( prime_pre ) ) <= (upper % ( prime_pre ) ))) (PreH2 : (upper > 0)) (PreH3 : (0 <= n_pre)) (PreH4 : (0 <= m_pre)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (PrimeForLucas prime_pre )) (PreH8 : (0 <= lower)) (PreH9 : (lower <= upper)) (PreH10 : (0 <= result)) (PreH11 : (result < prime_pre)) (PreH12 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  TT && emp 
|--
  “ (PrimeForLucas prime_pre ) ” 
  &&  “ ((lower % ( prime_pre ) ) <= (upper % ( prime_pre ) )) ” 
  &&  “ (2 <= prime_pre) ” 
  &&  “ (prime_pre <= 100000) ” 
  &&  “ ((upper % ( prime_pre ) ) < prime_pre) ” 
  &&  “ (0 <= (lower % ( prime_pre ) )) ” 
  &&  “ ((lower % ( prime_pre ) ) <= (upper % ( prime_pre ) )) ” 
  &&  “ (upper > 0) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (0 <= m_pre) ” 
  &&  “ (2 <= prime_pre) ” 
  &&  “ (prime_pre <= 100000) ” 
  &&  “ (PrimeForLucas prime_pre ) ” 
  &&  “ (0 <= lower) ” 
  &&  “ (lower <= upper) ” 
  &&  “ (0 <= result) ” 
  &&  “ (result < prime_pre) ” 
  &&  “ (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result ) ”
  &&  emp
.

Definition lucas_theorem_partial_solve_wit_1 := lucas_theorem_partial_solve_wit_1_pure -> lucas_theorem_partial_solve_wit_1_aux.

Module Type VC_Correct.


Axiom proof_of_binomial_digit_mod_prime_safety_wit_1 : binomial_digit_mod_prime_safety_wit_1.
Axiom proof_of_binomial_digit_mod_prime_safety_wit_2 : binomial_digit_mod_prime_safety_wit_2.
Axiom proof_of_binomial_digit_mod_prime_safety_wit_3 : binomial_digit_mod_prime_safety_wit_3.
Axiom proof_of_binomial_digit_mod_prime_safety_wit_4 : binomial_digit_mod_prime_safety_wit_4.
Axiom proof_of_binomial_digit_mod_prime_safety_wit_5 : binomial_digit_mod_prime_safety_wit_5.
Axiom proof_of_binomial_digit_mod_prime_safety_wit_6 : binomial_digit_mod_prime_safety_wit_6.
Axiom proof_of_binomial_digit_mod_prime_safety_wit_7 : binomial_digit_mod_prime_safety_wit_7.
Axiom proof_of_binomial_digit_mod_prime_safety_wit_8 : binomial_digit_mod_prime_safety_wit_8.
Axiom proof_of_binomial_digit_mod_prime_safety_wit_9 : binomial_digit_mod_prime_safety_wit_9.
Axiom proof_of_binomial_digit_mod_prime_safety_wit_10 : binomial_digit_mod_prime_safety_wit_10.
Axiom proof_of_binomial_digit_mod_prime_safety_wit_11 : binomial_digit_mod_prime_safety_wit_11.
Axiom proof_of_binomial_digit_mod_prime_safety_wit_12 : binomial_digit_mod_prime_safety_wit_12.
Axiom proof_of_binomial_digit_mod_prime_safety_wit_13 : binomial_digit_mod_prime_safety_wit_13.
Axiom proof_of_binomial_digit_mod_prime_safety_wit_14 : binomial_digit_mod_prime_safety_wit_14.
Axiom proof_of_binomial_digit_mod_prime_safety_wit_15 : binomial_digit_mod_prime_safety_wit_15.
Axiom proof_of_binomial_digit_mod_prime_safety_wit_16 : binomial_digit_mod_prime_safety_wit_16.
Axiom proof_of_binomial_digit_mod_prime_safety_wit_17 : binomial_digit_mod_prime_safety_wit_17.
Axiom proof_of_binomial_digit_mod_prime_safety_wit_18 : binomial_digit_mod_prime_safety_wit_18.
Axiom proof_of_binomial_digit_mod_prime_safety_wit_19 : binomial_digit_mod_prime_safety_wit_19.
Axiom proof_of_binomial_digit_mod_prime_safety_wit_20 : binomial_digit_mod_prime_safety_wit_20.
Axiom proof_of_binomial_digit_mod_prime_entail_wit_1_1 : binomial_digit_mod_prime_entail_wit_1_1.
Axiom proof_of_binomial_digit_mod_prime_entail_wit_1_2 : binomial_digit_mod_prime_entail_wit_1_2.
Axiom proof_of_binomial_digit_mod_prime_entail_wit_2 : binomial_digit_mod_prime_entail_wit_2.
Axiom proof_of_binomial_digit_mod_prime_return_wit_1 : binomial_digit_mod_prime_return_wit_1.
Axiom proof_of_binomial_digit_mod_prime_partial_solve_wit_1_pure : binomial_digit_mod_prime_partial_solve_wit_1_pure.
Axiom proof_of_binomial_digit_mod_prime_partial_solve_wit_1 : binomial_digit_mod_prime_partial_solve_wit_1.
Axiom proof_of_lucas_theorem_safety_wit_1 : lucas_theorem_safety_wit_1.
Axiom proof_of_lucas_theorem_safety_wit_2 : lucas_theorem_safety_wit_2.
Axiom proof_of_lucas_theorem_safety_wit_3 : lucas_theorem_safety_wit_3.
Axiom proof_of_lucas_theorem_safety_wit_4 : lucas_theorem_safety_wit_4.
Axiom proof_of_lucas_theorem_safety_wit_5 : lucas_theorem_safety_wit_5.
Axiom proof_of_lucas_theorem_safety_wit_6 : lucas_theorem_safety_wit_6.
Axiom proof_of_lucas_theorem_safety_wit_7 : lucas_theorem_safety_wit_7.
Axiom proof_of_lucas_theorem_safety_wit_8 : lucas_theorem_safety_wit_8.
Axiom proof_of_lucas_theorem_safety_wit_9 : lucas_theorem_safety_wit_9.
Axiom proof_of_lucas_theorem_safety_wit_10 : lucas_theorem_safety_wit_10.
Axiom proof_of_lucas_theorem_safety_wit_11 : lucas_theorem_safety_wit_11.
Axiom proof_of_lucas_theorem_safety_wit_12 : lucas_theorem_safety_wit_12.
Axiom proof_of_lucas_theorem_entail_wit_1 : lucas_theorem_entail_wit_1.
Axiom proof_of_lucas_theorem_entail_wit_2 : lucas_theorem_entail_wit_2.
Axiom proof_of_lucas_theorem_return_wit_1 : lucas_theorem_return_wit_1.
Axiom proof_of_lucas_theorem_return_wit_2 : lucas_theorem_return_wit_2.
Axiom proof_of_lucas_theorem_partial_solve_wit_1_pure : lucas_theorem_partial_solve_wit_1_pure.
Axiom proof_of_lucas_theorem_partial_solve_wit_1 : lucas_theorem_partial_solve_wit_1.

End VC_Correct.
