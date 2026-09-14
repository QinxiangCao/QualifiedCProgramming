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
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (PreH1 : (lower_pre > upper_pre)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) ,
  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
|--
  “ False ”
.

Definition binomial_digit_mod_prime_safety_wit_2 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (PreH1 : (lower_pre <= upper_pre)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) ,
  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
|--
  “ ((upper_pre - lower_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (upper_pre - lower_pre )) ”
.

Definition binomial_digit_mod_prime_safety_wit_3 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (PreH1 : (lower_pre > (upper_pre - lower_pre ))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre )) (PreH4 : (0 <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) ,
  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
|--
  “ ((upper_pre - lower_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (upper_pre - lower_pre )) ”
.

Definition binomial_digit_mod_prime_safety_wit_4 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (PreH1 : (lower_pre > (upper_pre - lower_pre ))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre )) (PreH4 : (0 <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) ,
  ((( &( "numerator" ) )) # Int  |->_)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "lower" ) )) # Int  |-> (upper_pre - lower_pre ))
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition binomial_digit_mod_prime_safety_wit_5 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (PreH1 : (lower_pre <= (upper_pre - lower_pre ))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre )) (PreH4 : (0 <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) ,
  ((( &( "numerator" ) )) # Int  |->_)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition binomial_digit_mod_prime_safety_wit_6 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (PreH1 : (lower_pre > (upper_pre - lower_pre ))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre )) (PreH4 : (0 <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) ,
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
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (PreH1 : (lower_pre <= (upper_pre - lower_pre ))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre )) (PreH4 : (0 <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) ,
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
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (PreH1 : (lower_pre > (upper_pre - lower_pre ))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre )) (PreH4 : (0 <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) ,
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
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (PreH1 : (lower_pre <= (upper_pre - lower_pre ))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre )) (PreH4 : (0 <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) ,
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
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (PreH1 : (i <= lower_pre)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_pre <= (upper_pre - lower_pre ))) (PreH9 : (0 <= lower_pre)) (PreH10 : (lower_pre <= (upper_pre - lower_pre ))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower_pre + 1 ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH18 : (DigitProductProgress upper_pre lower_pre prime_pre i numerator denominator )) ,
  ((( &( "factor" ) )) # Int  |->_)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numerator" ) )) # Int  |-> numerator)
  **  ((( &( "denominator" ) )) # Int  |-> denominator)
|--
  “ (((upper_pre - lower_pre ) + i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((upper_pre - lower_pre ) + i )) ”
.

Definition binomial_digit_mod_prime_safety_wit_11 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (PreH1 : (i <= lower_pre)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_pre <= (upper_pre - lower_pre ))) (PreH9 : (0 <= lower_pre)) (PreH10 : (lower_pre <= (upper_pre - lower_pre ))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower_pre + 1 ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH18 : (DigitProductProgress upper_pre lower_pre prime_pre i numerator denominator )) ,
  ((( &( "factor" ) )) # Int  |->_)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numerator" ) )) # Int  |-> numerator)
  **  ((( &( "denominator" ) )) # Int  |-> denominator)
|--
  “ ((upper_pre - lower_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (upper_pre - lower_pre )) ”
.

Definition binomial_digit_mod_prime_safety_wit_12 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (lower: Z) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (upper_pre - lower_pre ))) (PreH9 : (lower_pre > (upper_pre - lower_pre ))) (PreH10 : (0 <= lower)) (PreH11 : (lower <= (upper_pre - lower ))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1 ))) (PreH14 : (0 <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : (0 <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH19 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator )) ,
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

Definition binomial_digit_mod_prime_safety_wit_13 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (lower: Z) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (upper_pre - lower_pre ))) (PreH9 : (lower_pre > (upper_pre - lower_pre ))) (PreH10 : (0 <= lower)) (PreH11 : (lower <= (upper_pre - lower ))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1 ))) (PreH14 : (0 <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : (0 <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH19 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator )) ,
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

Definition binomial_digit_mod_prime_safety_wit_14 := 
(
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (PreH1 : (i <= lower_pre)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_pre <= (upper_pre - lower_pre ))) (PreH9 : (0 <= lower_pre)) (PreH10 : (lower_pre <= (upper_pre - lower_pre ))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower_pre + 1 ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH18 : (DigitProductProgress upper_pre lower_pre prime_pre i numerator denominator )) ,
  ((( &( "numerator_product" ) )) # Int  |->_)
  **  ((( &( "factor" ) )) # Int  |-> ((upper_pre - lower_pre ) + i ))
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numerator" ) )) # Int  |-> numerator)
  **  ((( &( "denominator" ) )) # Int  |-> denominator)
|--
  “ ((numerator * ((upper_pre - lower_pre ) + i ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (numerator * ((upper_pre - lower_pre ) + i ) )) ”
) \/
(
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (PreH1 : (i <= lower_pre)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_pre <= (upper_pre - lower_pre ))) (PreH9 : (0 <= lower_pre)) (PreH10 : (lower_pre <= (upper_pre - lower_pre ))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower_pre + 1 ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH18 : (DigitProductProgress upper_pre lower_pre prime_pre i numerator denominator )) ,
  ((( &( "numerator_product" ) )) # Int  |->_)
  **  ((( &( "factor" ) )) # Int  |-> ((upper_pre - lower_pre ) + i ))
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numerator" ) )) # Int  |-> numerator)
  **  ((( &( "denominator" ) )) # Int  |-> denominator)
|--
  “ ((numerator * ((upper_pre - lower_pre ) + i ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (numerator * ((upper_pre - lower_pre ) + i ) )) ”
).

Definition binomial_digit_mod_prime_safety_wit_14_split_goal_1 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (PreH1 : (i <= lower_pre)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_pre <= (upper_pre - lower_pre ))) (PreH9 : (0 <= lower_pre)) (PreH10 : (lower_pre <= (upper_pre - lower_pre ))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower_pre + 1 ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH18 : (DigitProductProgress upper_pre lower_pre prime_pre i numerator denominator )) ,
  ((( &( "numerator_product" ) )) # Int  |->_)
  **  ((( &( "factor" ) )) # Int  |-> ((upper_pre - lower_pre ) + i ))
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numerator" ) )) # Int  |-> numerator)
  **  ((( &( "denominator" ) )) # Int  |-> denominator)
|--
  “ ((numerator * ((upper_pre - lower_pre ) + i ) ) <= INT_MAX) ”
.

Definition binomial_digit_mod_prime_safety_wit_14_split_goal_2 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (PreH1 : (i <= lower_pre)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_pre <= (upper_pre - lower_pre ))) (PreH9 : (0 <= lower_pre)) (PreH10 : (lower_pre <= (upper_pre - lower_pre ))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower_pre + 1 ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH18 : (DigitProductProgress upper_pre lower_pre prime_pre i numerator denominator )) ,
  ((( &( "numerator_product" ) )) # Int  |->_)
  **  ((( &( "factor" ) )) # Int  |-> ((upper_pre - lower_pre ) + i ))
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numerator" ) )) # Int  |-> numerator)
  **  ((( &( "denominator" ) )) # Int  |-> denominator)
|--
  “ ((INT_MIN) <= (numerator * ((upper_pre - lower_pre ) + i ) )) ”
.

Definition binomial_digit_mod_prime_safety_wit_15 := 
(
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (lower: Z) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (upper_pre - lower_pre ))) (PreH9 : (lower_pre > (upper_pre - lower_pre ))) (PreH10 : (0 <= lower)) (PreH11 : (lower <= (upper_pre - lower ))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1 ))) (PreH14 : (0 <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : (0 <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH19 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator )) ,
  ((( &( "numerator_product" ) )) # Int  |->_)
  **  ((( &( "factor" ) )) # Int  |-> ((upper_pre - lower ) + i ))
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numerator" ) )) # Int  |-> numerator)
  **  ((( &( "denominator" ) )) # Int  |-> denominator)
|--
  “ ((numerator * ((upper_pre - lower ) + i ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (numerator * ((upper_pre - lower ) + i ) )) ”
) \/
(
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (lower: Z) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (upper_pre - lower_pre ))) (PreH9 : (lower_pre > (upper_pre - lower_pre ))) (PreH10 : (0 <= lower)) (PreH11 : (lower <= (upper_pre - lower ))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1 ))) (PreH14 : (0 <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : (0 <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH19 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator )) ,
  ((( &( "numerator_product" ) )) # Int  |->_)
  **  ((( &( "factor" ) )) # Int  |-> ((upper_pre - lower ) + i ))
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numerator" ) )) # Int  |-> numerator)
  **  ((( &( "denominator" ) )) # Int  |-> denominator)
|--
  “ ((numerator * ((upper_pre - lower ) + i ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (numerator * ((upper_pre - lower ) + i ) )) ”
).

Definition binomial_digit_mod_prime_safety_wit_15_split_goal_1 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (lower: Z) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (upper_pre - lower_pre ))) (PreH9 : (lower_pre > (upper_pre - lower_pre ))) (PreH10 : (0 <= lower)) (PreH11 : (lower <= (upper_pre - lower ))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1 ))) (PreH14 : (0 <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : (0 <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH19 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator )) ,
  ((( &( "numerator_product" ) )) # Int  |->_)
  **  ((( &( "factor" ) )) # Int  |-> ((upper_pre - lower ) + i ))
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numerator" ) )) # Int  |-> numerator)
  **  ((( &( "denominator" ) )) # Int  |-> denominator)
|--
  “ ((numerator * ((upper_pre - lower ) + i ) ) <= INT_MAX) ”
.

Definition binomial_digit_mod_prime_safety_wit_15_split_goal_2 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (lower: Z) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (upper_pre - lower_pre ))) (PreH9 : (lower_pre > (upper_pre - lower_pre ))) (PreH10 : (0 <= lower)) (PreH11 : (lower <= (upper_pre - lower ))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1 ))) (PreH14 : (0 <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : (0 <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH19 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator )) ,
  ((( &( "numerator_product" ) )) # Int  |->_)
  **  ((( &( "factor" ) )) # Int  |-> ((upper_pre - lower ) + i ))
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numerator" ) )) # Int  |-> numerator)
  **  ((( &( "denominator" ) )) # Int  |-> denominator)
|--
  “ ((INT_MIN) <= (numerator * ((upper_pre - lower ) + i ) )) ”
.

Definition binomial_digit_mod_prime_safety_wit_16 := 
(
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (PreH1 : (i <= lower_pre)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_pre <= (upper_pre - lower_pre ))) (PreH9 : (0 <= lower_pre)) (PreH10 : (lower_pre <= (upper_pre - lower_pre ))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower_pre + 1 ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH18 : (DigitProductProgress upper_pre lower_pre prime_pre i numerator denominator )) ,
  ((( &( "denominator_product" ) )) # Int  |->_)
  **  ((( &( "numerator_product" ) )) # Int  |-> (numerator * ((upper_pre - lower_pre ) + i ) ))
  **  ((( &( "factor" ) )) # Int  |-> ((upper_pre - lower_pre ) + i ))
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numerator" ) )) # Int  |-> numerator)
  **  ((( &( "denominator" ) )) # Int  |-> denominator)
|--
  “ ((denominator * i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (denominator * i )) ”
) \/
(
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (PreH1 : (i <= lower_pre)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_pre <= (upper_pre - lower_pre ))) (PreH9 : (0 <= lower_pre)) (PreH10 : (lower_pre <= (upper_pre - lower_pre ))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower_pre + 1 ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH18 : (DigitProductProgress upper_pre lower_pre prime_pre i numerator denominator )) ,
  ((( &( "denominator_product" ) )) # Int  |->_)
  **  ((( &( "numerator_product" ) )) # Int  |-> (numerator * ((upper_pre - lower_pre ) + i ) ))
  **  ((( &( "factor" ) )) # Int  |-> ((upper_pre - lower_pre ) + i ))
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numerator" ) )) # Int  |-> numerator)
  **  ((( &( "denominator" ) )) # Int  |-> denominator)
|--
  “ ((denominator * i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (denominator * i )) ”
).

Definition binomial_digit_mod_prime_safety_wit_16_split_goal_1 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (PreH1 : (i <= lower_pre)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_pre <= (upper_pre - lower_pre ))) (PreH9 : (0 <= lower_pre)) (PreH10 : (lower_pre <= (upper_pre - lower_pre ))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower_pre + 1 ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH18 : (DigitProductProgress upper_pre lower_pre prime_pre i numerator denominator )) ,
  ((( &( "denominator_product" ) )) # Int  |->_)
  **  ((( &( "numerator_product" ) )) # Int  |-> (numerator * ((upper_pre - lower_pre ) + i ) ))
  **  ((( &( "factor" ) )) # Int  |-> ((upper_pre - lower_pre ) + i ))
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numerator" ) )) # Int  |-> numerator)
  **  ((( &( "denominator" ) )) # Int  |-> denominator)
|--
  “ ((denominator * i ) <= INT_MAX) ”
.

Definition binomial_digit_mod_prime_safety_wit_16_split_goal_2 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (PreH1 : (i <= lower_pre)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_pre <= (upper_pre - lower_pre ))) (PreH9 : (0 <= lower_pre)) (PreH10 : (lower_pre <= (upper_pre - lower_pre ))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower_pre + 1 ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH18 : (DigitProductProgress upper_pre lower_pre prime_pre i numerator denominator )) ,
  ((( &( "denominator_product" ) )) # Int  |->_)
  **  ((( &( "numerator_product" ) )) # Int  |-> (numerator * ((upper_pre - lower_pre ) + i ) ))
  **  ((( &( "factor" ) )) # Int  |-> ((upper_pre - lower_pre ) + i ))
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numerator" ) )) # Int  |-> numerator)
  **  ((( &( "denominator" ) )) # Int  |-> denominator)
|--
  “ ((INT_MIN) <= (denominator * i )) ”
.

Definition binomial_digit_mod_prime_safety_wit_17 := 
(
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (lower: Z) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (upper_pre - lower_pre ))) (PreH9 : (lower_pre > (upper_pre - lower_pre ))) (PreH10 : (0 <= lower)) (PreH11 : (lower <= (upper_pre - lower ))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1 ))) (PreH14 : (0 <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : (0 <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH19 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator )) ,
  ((( &( "denominator_product" ) )) # Int  |->_)
  **  ((( &( "numerator_product" ) )) # Int  |-> (numerator * ((upper_pre - lower ) + i ) ))
  **  ((( &( "factor" ) )) # Int  |-> ((upper_pre - lower ) + i ))
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numerator" ) )) # Int  |-> numerator)
  **  ((( &( "denominator" ) )) # Int  |-> denominator)
|--
  “ ((denominator * i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (denominator * i )) ”
) \/
(
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (lower: Z) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (upper_pre - lower_pre ))) (PreH9 : (lower_pre > (upper_pre - lower_pre ))) (PreH10 : (0 <= lower)) (PreH11 : (lower <= (upper_pre - lower ))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1 ))) (PreH14 : (0 <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : (0 <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH19 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator )) ,
  ((( &( "denominator_product" ) )) # Int  |->_)
  **  ((( &( "numerator_product" ) )) # Int  |-> (numerator * ((upper_pre - lower ) + i ) ))
  **  ((( &( "factor" ) )) # Int  |-> ((upper_pre - lower ) + i ))
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numerator" ) )) # Int  |-> numerator)
  **  ((( &( "denominator" ) )) # Int  |-> denominator)
|--
  “ ((denominator * i ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (denominator * i )) ”
).

Definition binomial_digit_mod_prime_safety_wit_17_split_goal_1 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (lower: Z) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (upper_pre - lower_pre ))) (PreH9 : (lower_pre > (upper_pre - lower_pre ))) (PreH10 : (0 <= lower)) (PreH11 : (lower <= (upper_pre - lower ))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1 ))) (PreH14 : (0 <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : (0 <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH19 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator )) ,
  ((( &( "denominator_product" ) )) # Int  |->_)
  **  ((( &( "numerator_product" ) )) # Int  |-> (numerator * ((upper_pre - lower ) + i ) ))
  **  ((( &( "factor" ) )) # Int  |-> ((upper_pre - lower ) + i ))
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numerator" ) )) # Int  |-> numerator)
  **  ((( &( "denominator" ) )) # Int  |-> denominator)
|--
  “ ((denominator * i ) <= INT_MAX) ”
.

Definition binomial_digit_mod_prime_safety_wit_17_split_goal_2 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (lower: Z) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (upper_pre - lower_pre ))) (PreH9 : (lower_pre > (upper_pre - lower_pre ))) (PreH10 : (0 <= lower)) (PreH11 : (lower <= (upper_pre - lower ))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1 ))) (PreH14 : (0 <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : (0 <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH19 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator )) ,
  ((( &( "denominator_product" ) )) # Int  |->_)
  **  ((( &( "numerator_product" ) )) # Int  |-> (numerator * ((upper_pre - lower ) + i ) ))
  **  ((( &( "factor" ) )) # Int  |-> ((upper_pre - lower ) + i ))
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numerator" ) )) # Int  |-> numerator)
  **  ((( &( "denominator" ) )) # Int  |-> denominator)
|--
  “ ((INT_MIN) <= (denominator * i )) ”
.

Definition binomial_digit_mod_prime_safety_wit_18 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (PreH1 : (i <= lower_pre)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_pre <= (upper_pre - lower_pre ))) (PreH9 : (0 <= lower_pre)) (PreH10 : (lower_pre <= (upper_pre - lower_pre ))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower_pre + 1 ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH18 : (DigitProductProgress upper_pre lower_pre prime_pre i numerator denominator )) ,
  ((( &( "denominator_product" ) )) # Int  |-> (denominator * i ))
  **  ((( &( "numerator_product" ) )) # Int  |-> (numerator * ((upper_pre - lower_pre ) + i ) ))
  **  ((( &( "factor" ) )) # Int  |-> ((upper_pre - lower_pre ) + i ))
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numerator" ) )) # Int  |-> numerator)
  **  ((( &( "denominator" ) )) # Int  |-> denominator)
|--
  “ (((numerator * ((upper_pre - lower_pre ) + i ) ) <> (INT_MIN)) \/ (prime_pre <> (-1))) ” 
  &&  “ (prime_pre <> 0) ”
.

Definition binomial_digit_mod_prime_safety_wit_19 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (lower: Z) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (upper_pre - lower_pre ))) (PreH9 : (lower_pre > (upper_pre - lower_pre ))) (PreH10 : (0 <= lower)) (PreH11 : (lower <= (upper_pre - lower ))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1 ))) (PreH14 : (0 <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : (0 <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH19 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator )) ,
  ((( &( "denominator_product" ) )) # Int  |-> (denominator * i ))
  **  ((( &( "numerator_product" ) )) # Int  |-> (numerator * ((upper_pre - lower ) + i ) ))
  **  ((( &( "factor" ) )) # Int  |-> ((upper_pre - lower ) + i ))
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numerator" ) )) # Int  |-> numerator)
  **  ((( &( "denominator" ) )) # Int  |-> denominator)
|--
  “ (((numerator * ((upper_pre - lower ) + i ) ) <> (INT_MIN)) \/ (prime_pre <> (-1))) ” 
  &&  “ (prime_pre <> 0) ”
.

Definition binomial_digit_mod_prime_safety_wit_20 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (PreH1 : (i <= lower_pre)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_pre <= (upper_pre - lower_pre ))) (PreH9 : (0 <= lower_pre)) (PreH10 : (lower_pre <= (upper_pre - lower_pre ))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower_pre + 1 ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH18 : (DigitProductProgress upper_pre lower_pre prime_pre i numerator denominator )) ,
  ((( &( "denominator_product" ) )) # Int  |-> (denominator * i ))
  **  ((( &( "numerator_product" ) )) # Int  |-> (numerator * ((upper_pre - lower_pre ) + i ) ))
  **  ((( &( "factor" ) )) # Int  |-> ((upper_pre - lower_pre ) + i ))
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numerator" ) )) # Int  |-> ((numerator * ((upper_pre - lower_pre ) + i ) ) % ( prime_pre ) ))
  **  ((( &( "denominator" ) )) # Int  |-> denominator)
|--
  “ (((denominator * i ) <> (INT_MIN)) \/ (prime_pre <> (-1))) ” 
  &&  “ (prime_pre <> 0) ”
.

Definition binomial_digit_mod_prime_safety_wit_21 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (lower: Z) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (upper_pre - lower_pre ))) (PreH9 : (lower_pre > (upper_pre - lower_pre ))) (PreH10 : (0 <= lower)) (PreH11 : (lower <= (upper_pre - lower ))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1 ))) (PreH14 : (0 <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : (0 <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH19 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator )) ,
  ((( &( "denominator_product" ) )) # Int  |-> (denominator * i ))
  **  ((( &( "numerator_product" ) )) # Int  |-> (numerator * ((upper_pre - lower ) + i ) ))
  **  ((( &( "factor" ) )) # Int  |-> ((upper_pre - lower ) + i ))
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numerator" ) )) # Int  |-> ((numerator * ((upper_pre - lower ) + i ) ) % ( prime_pre ) ))
  **  ((( &( "denominator" ) )) # Int  |-> denominator)
|--
  “ (((denominator * i ) <> (INT_MIN)) \/ (prime_pre <> (-1))) ” 
  &&  “ (prime_pre <> 0) ”
.

Definition binomial_digit_mod_prime_safety_wit_22 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (PreH1 : (i <= lower_pre)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_pre <= (upper_pre - lower_pre ))) (PreH9 : (0 <= lower_pre)) (PreH10 : (lower_pre <= (upper_pre - lower_pre ))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower_pre + 1 ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH18 : (DigitProductProgress upper_pre lower_pre prime_pre i numerator denominator )) ,
  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numerator" ) )) # Int  |-> ((numerator * ((upper_pre - lower_pre ) + i ) ) % ( prime_pre ) ))
  **  ((( &( "denominator" ) )) # Int  |-> ((denominator * i ) % ( prime_pre ) ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition binomial_digit_mod_prime_safety_wit_23 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (lower: Z) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (upper_pre - lower_pre ))) (PreH9 : (lower_pre > (upper_pre - lower_pre ))) (PreH10 : (0 <= lower)) (PreH11 : (lower <= (upper_pre - lower ))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1 ))) (PreH14 : (0 <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : (0 <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH19 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator )) ,
  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "numerator" ) )) # Int  |-> ((numerator * ((upper_pre - lower ) + i ) ) % ( prime_pre ) ))
  **  ((( &( "denominator" ) )) # Int  |-> ((denominator * i ) % ( prime_pre ) ))
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition binomial_digit_mod_prime_safety_wit_24 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (lower: Z) (numerator: Z) (denominator: Z) (PreH1 : (PrimeForLucas prime_pre )) (PreH2 : (0 <= lower_pre)) (PreH3 : (lower_pre <= upper_pre)) (PreH4 : (upper_pre < prime_pre)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (lower = (upper_pre - lower_pre ))) (PreH8 : (lower_pre > (upper_pre - lower_pre ))) (PreH9 : (0 <= lower)) (PreH10 : (lower <= (upper_pre - lower ))) (PreH11 : (0 <= numerator)) (PreH12 : (numerator < prime_pre)) (PreH13 : (0 <= denominator)) (PreH14 : (denominator < prime_pre)) (PreH15 : (0 <= (prime_pre - 2 ))) (PreH16 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH17 : (DigitProductProgress upper_pre lower prime_pre (lower + 1 ) numerator denominator )) ,
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

Definition binomial_digit_mod_prime_safety_wit_25 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (lower: Z) (numerator: Z) (denominator: Z) (PreH1 : (PrimeForLucas prime_pre )) (PreH2 : (0 <= lower_pre)) (PreH3 : (lower_pre <= upper_pre)) (PreH4 : (upper_pre < prime_pre)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (lower = (upper_pre - lower_pre ))) (PreH8 : (lower_pre > (upper_pre - lower_pre ))) (PreH9 : (0 <= lower)) (PreH10 : (lower <= (upper_pre - lower ))) (PreH11 : (0 <= numerator)) (PreH12 : (numerator < prime_pre)) (PreH13 : (0 <= denominator)) (PreH14 : (denominator < prime_pre)) (PreH15 : (0 <= (prime_pre - 2 ))) (PreH16 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH17 : (DigitProductProgress upper_pre lower prime_pre (lower + 1 ) numerator denominator )) ,
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

Definition binomial_digit_mod_prime_safety_wit_26 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (numerator: Z) (denominator: Z) (PreH1 : (PrimeForLucas prime_pre )) (PreH2 : (0 <= lower_pre)) (PreH3 : (lower_pre <= upper_pre)) (PreH4 : (upper_pre < prime_pre)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (lower_pre <= (upper_pre - lower_pre ))) (PreH8 : (0 <= lower_pre)) (PreH9 : (lower_pre <= (upper_pre - lower_pre ))) (PreH10 : (0 <= numerator)) (PreH11 : (numerator < prime_pre)) (PreH12 : (0 <= denominator)) (PreH13 : (denominator < prime_pre)) (PreH14 : (0 <= (prime_pre - 2 ))) (PreH15 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH16 : (DigitProductProgress upper_pre lower_pre prime_pre (lower_pre + 1 ) numerator denominator )) ,
  ((( &( "inverse" ) )) # Int  |->_)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower_pre)
  **  ((( &( "numerator" ) )) # Int  |-> numerator)
  **  ((( &( "denominator" ) )) # Int  |-> denominator)
|--
  “ ((prime_pre - 2 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (prime_pre - 2 )) ”
.

Definition binomial_digit_mod_prime_safety_wit_27 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (numerator: Z) (denominator: Z) (PreH1 : (PrimeForLucas prime_pre )) (PreH2 : (0 <= lower_pre)) (PreH3 : (lower_pre <= upper_pre)) (PreH4 : (upper_pre < prime_pre)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (lower_pre <= (upper_pre - lower_pre ))) (PreH8 : (0 <= lower_pre)) (PreH9 : (lower_pre <= (upper_pre - lower_pre ))) (PreH10 : (0 <= numerator)) (PreH11 : (numerator < prime_pre)) (PreH12 : (0 <= denominator)) (PreH13 : (denominator < prime_pre)) (PreH14 : (0 <= (prime_pre - 2 ))) (PreH15 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH16 : (DigitProductProgress upper_pre lower_pre prime_pre (lower_pre + 1 ) numerator denominator )) ,
  ((( &( "inverse" ) )) # Int  |->_)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower_pre)
  **  ((( &( "numerator" ) )) # Int  |-> numerator)
  **  ((( &( "denominator" ) )) # Int  |-> denominator)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition binomial_digit_mod_prime_safety_wit_28 := 
(
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (lower: Z) (numerator: Z) (denominator: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (ModularPower denominator (prime_pre - 2 ) prime_pre retval )) (PreH4 : (PrimeForLucas prime_pre )) (PreH5 : (0 <= lower_pre)) (PreH6 : (lower_pre <= upper_pre)) (PreH7 : (upper_pre < prime_pre)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (lower = (upper_pre - lower_pre ))) (PreH11 : (lower_pre > (upper_pre - lower_pre ))) (PreH12 : (0 <= lower)) (PreH13 : (lower <= (upper_pre - lower ))) (PreH14 : (0 <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : (0 <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (0 <= (prime_pre - 2 ))) (PreH19 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH20 : (DigitProductProgress upper_pre lower prime_pre (lower + 1 ) numerator denominator )) ,
  ((( &( "answer" ) )) # Int  |->_)
  **  ((( &( "inverse" ) )) # Int  |-> retval)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "numerator" ) )) # Int  |-> numerator)
  **  ((( &( "denominator" ) )) # Int  |-> denominator)
|--
  “ ((numerator * retval ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (numerator * retval )) ”
) \/
(
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (lower: Z) (numerator: Z) (denominator: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (ModularPower denominator (prime_pre - 2 ) prime_pre retval )) (PreH4 : (PrimeForLucas prime_pre )) (PreH5 : (0 <= lower_pre)) (PreH6 : (lower_pre <= upper_pre)) (PreH7 : (upper_pre < prime_pre)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (lower = (upper_pre - lower_pre ))) (PreH11 : (lower_pre > (upper_pre - lower_pre ))) (PreH12 : (0 <= lower)) (PreH13 : (lower <= (upper_pre - lower ))) (PreH14 : (0 <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : (0 <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (0 <= (prime_pre - 2 ))) (PreH19 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH20 : (DigitProductProgress upper_pre lower prime_pre (lower + 1 ) numerator denominator )) ,
  ((( &( "answer" ) )) # Int  |->_)
  **  ((( &( "inverse" ) )) # Int  |-> retval)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "numerator" ) )) # Int  |-> numerator)
  **  ((( &( "denominator" ) )) # Int  |-> denominator)
|--
  “ ((numerator * retval ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (numerator * retval )) ”
).

Definition binomial_digit_mod_prime_safety_wit_28_split_goal_1 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (lower: Z) (numerator: Z) (denominator: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (ModularPower denominator (prime_pre - 2 ) prime_pre retval )) (PreH4 : (PrimeForLucas prime_pre )) (PreH5 : (0 <= lower_pre)) (PreH6 : (lower_pre <= upper_pre)) (PreH7 : (upper_pre < prime_pre)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (lower = (upper_pre - lower_pre ))) (PreH11 : (lower_pre > (upper_pre - lower_pre ))) (PreH12 : (0 <= lower)) (PreH13 : (lower <= (upper_pre - lower ))) (PreH14 : (0 <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : (0 <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (0 <= (prime_pre - 2 ))) (PreH19 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH20 : (DigitProductProgress upper_pre lower prime_pre (lower + 1 ) numerator denominator )) ,
  ((( &( "answer" ) )) # Int  |->_)
  **  ((( &( "inverse" ) )) # Int  |-> retval)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "numerator" ) )) # Int  |-> numerator)
  **  ((( &( "denominator" ) )) # Int  |-> denominator)
|--
  “ ((numerator * retval ) <= INT_MAX) ”
.

Definition binomial_digit_mod_prime_safety_wit_28_split_goal_2 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (lower: Z) (numerator: Z) (denominator: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (ModularPower denominator (prime_pre - 2 ) prime_pre retval )) (PreH4 : (PrimeForLucas prime_pre )) (PreH5 : (0 <= lower_pre)) (PreH6 : (lower_pre <= upper_pre)) (PreH7 : (upper_pre < prime_pre)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (lower = (upper_pre - lower_pre ))) (PreH11 : (lower_pre > (upper_pre - lower_pre ))) (PreH12 : (0 <= lower)) (PreH13 : (lower <= (upper_pre - lower ))) (PreH14 : (0 <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : (0 <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (0 <= (prime_pre - 2 ))) (PreH19 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH20 : (DigitProductProgress upper_pre lower prime_pre (lower + 1 ) numerator denominator )) ,
  ((( &( "answer" ) )) # Int  |->_)
  **  ((( &( "inverse" ) )) # Int  |-> retval)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "numerator" ) )) # Int  |-> numerator)
  **  ((( &( "denominator" ) )) # Int  |-> denominator)
|--
  “ ((INT_MIN) <= (numerator * retval )) ”
.

Definition binomial_digit_mod_prime_safety_wit_29 := 
(
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (numerator: Z) (denominator: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (ModularPower denominator (prime_pre - 2 ) prime_pre retval )) (PreH4 : (PrimeForLucas prime_pre )) (PreH5 : (0 <= lower_pre)) (PreH6 : (lower_pre <= upper_pre)) (PreH7 : (upper_pre < prime_pre)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (lower_pre <= (upper_pre - lower_pre ))) (PreH11 : (0 <= lower_pre)) (PreH12 : (lower_pre <= (upper_pre - lower_pre ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (0 <= (prime_pre - 2 ))) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH19 : (DigitProductProgress upper_pre lower_pre prime_pre (lower_pre + 1 ) numerator denominator )) ,
  ((( &( "answer" ) )) # Int  |->_)
  **  ((( &( "inverse" ) )) # Int  |-> retval)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower_pre)
  **  ((( &( "numerator" ) )) # Int  |-> numerator)
  **  ((( &( "denominator" ) )) # Int  |-> denominator)
|--
  “ ((numerator * retval ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (numerator * retval )) ”
) \/
(
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (numerator: Z) (denominator: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (ModularPower denominator (prime_pre - 2 ) prime_pre retval )) (PreH4 : (PrimeForLucas prime_pre )) (PreH5 : (0 <= lower_pre)) (PreH6 : (lower_pre <= upper_pre)) (PreH7 : (upper_pre < prime_pre)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (lower_pre <= (upper_pre - lower_pre ))) (PreH11 : (0 <= lower_pre)) (PreH12 : (lower_pre <= (upper_pre - lower_pre ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (0 <= (prime_pre - 2 ))) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH19 : (DigitProductProgress upper_pre lower_pre prime_pre (lower_pre + 1 ) numerator denominator )) ,
  ((( &( "answer" ) )) # Int  |->_)
  **  ((( &( "inverse" ) )) # Int  |-> retval)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower_pre)
  **  ((( &( "numerator" ) )) # Int  |-> numerator)
  **  ((( &( "denominator" ) )) # Int  |-> denominator)
|--
  “ ((numerator * retval ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (numerator * retval )) ”
).

Definition binomial_digit_mod_prime_safety_wit_29_split_goal_1 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (numerator: Z) (denominator: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (ModularPower denominator (prime_pre - 2 ) prime_pre retval )) (PreH4 : (PrimeForLucas prime_pre )) (PreH5 : (0 <= lower_pre)) (PreH6 : (lower_pre <= upper_pre)) (PreH7 : (upper_pre < prime_pre)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (lower_pre <= (upper_pre - lower_pre ))) (PreH11 : (0 <= lower_pre)) (PreH12 : (lower_pre <= (upper_pre - lower_pre ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (0 <= (prime_pre - 2 ))) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH19 : (DigitProductProgress upper_pre lower_pre prime_pre (lower_pre + 1 ) numerator denominator )) ,
  ((( &( "answer" ) )) # Int  |->_)
  **  ((( &( "inverse" ) )) # Int  |-> retval)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower_pre)
  **  ((( &( "numerator" ) )) # Int  |-> numerator)
  **  ((( &( "denominator" ) )) # Int  |-> denominator)
|--
  “ ((numerator * retval ) <= INT_MAX) ”
.

Definition binomial_digit_mod_prime_safety_wit_29_split_goal_2 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (numerator: Z) (denominator: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (ModularPower denominator (prime_pre - 2 ) prime_pre retval )) (PreH4 : (PrimeForLucas prime_pre )) (PreH5 : (0 <= lower_pre)) (PreH6 : (lower_pre <= upper_pre)) (PreH7 : (upper_pre < prime_pre)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (lower_pre <= (upper_pre - lower_pre ))) (PreH11 : (0 <= lower_pre)) (PreH12 : (lower_pre <= (upper_pre - lower_pre ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (0 <= (prime_pre - 2 ))) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH19 : (DigitProductProgress upper_pre lower_pre prime_pre (lower_pre + 1 ) numerator denominator )) ,
  ((( &( "answer" ) )) # Int  |->_)
  **  ((( &( "inverse" ) )) # Int  |-> retval)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower_pre)
  **  ((( &( "numerator" ) )) # Int  |-> numerator)
  **  ((( &( "denominator" ) )) # Int  |-> denominator)
|--
  “ ((INT_MIN) <= (numerator * retval )) ”
.

Definition binomial_digit_mod_prime_safety_wit_30 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (numerator: Z) (denominator: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (ModularPower denominator (prime_pre - 2 ) prime_pre retval )) (PreH4 : (PrimeForLucas prime_pre )) (PreH5 : (0 <= lower_pre)) (PreH6 : (lower_pre <= upper_pre)) (PreH7 : (upper_pre < prime_pre)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (lower_pre <= (upper_pre - lower_pre ))) (PreH11 : (0 <= lower_pre)) (PreH12 : (lower_pre <= (upper_pre - lower_pre ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (0 <= (prime_pre - 2 ))) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH19 : (DigitProductProgress upper_pre lower_pre prime_pre (lower_pre + 1 ) numerator denominator )) ,
  ((( &( "answer" ) )) # Int  |-> (numerator * retval ))
  **  ((( &( "inverse" ) )) # Int  |-> retval)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower_pre)
  **  ((( &( "numerator" ) )) # Int  |-> numerator)
  **  ((( &( "denominator" ) )) # Int  |-> denominator)
|--
  “ (((numerator * retval ) <> (INT_MIN)) \/ (prime_pre <> (-1))) ” 
  &&  “ (prime_pre <> 0) ”
.

Definition binomial_digit_mod_prime_safety_wit_31 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (lower: Z) (numerator: Z) (denominator: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (ModularPower denominator (prime_pre - 2 ) prime_pre retval )) (PreH4 : (PrimeForLucas prime_pre )) (PreH5 : (0 <= lower_pre)) (PreH6 : (lower_pre <= upper_pre)) (PreH7 : (upper_pre < prime_pre)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (lower = (upper_pre - lower_pre ))) (PreH11 : (lower_pre > (upper_pre - lower_pre ))) (PreH12 : (0 <= lower)) (PreH13 : (lower <= (upper_pre - lower ))) (PreH14 : (0 <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : (0 <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (0 <= (prime_pre - 2 ))) (PreH19 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH20 : (DigitProductProgress upper_pre lower prime_pre (lower + 1 ) numerator denominator )) ,
  ((( &( "answer" ) )) # Int  |-> (numerator * retval ))
  **  ((( &( "inverse" ) )) # Int  |-> retval)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "numerator" ) )) # Int  |-> numerator)
  **  ((( &( "denominator" ) )) # Int  |-> denominator)
|--
  “ (((numerator * retval ) <> (INT_MIN)) \/ (prime_pre <> (-1))) ” 
  &&  “ (prime_pre <> 0) ”
.

Definition binomial_digit_mod_prime_entail_wit_1_1 := 
(
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (PreH1 : (lower_pre > (upper_pre - lower_pre ))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre )) (PreH4 : (0 <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) ,
  ((( &( "lower" ) )) # Int  |-> (upper_pre - lower_pre ))
|--
  EX (lower: Z) ,
  “ (PrimeForLucas prime_pre ) ” 
  &&  “ (0 <= lower_pre) ” 
  &&  “ (lower_pre <= upper_pre) ” 
  &&  “ (upper_pre < prime_pre) ” 
  &&  “ (2 <= prime_pre) ” 
  &&  “ (prime_pre <= 100000) ” 
  &&  “ (lower = (upper_pre - lower_pre )) ” 
  &&  “ (lower_pre > (upper_pre - lower_pre )) ” 
  &&  “ (0 <= lower) ” 
  &&  “ (lower <= (upper_pre - lower )) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (lower + 1 )) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 < prime_pre) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 < prime_pre) ” 
  &&  “ (DigitBinomialMachineSafe upper_pre lower_pre prime_pre ) ” 
  &&  “ (DigitProductProgress upper_pre lower prime_pre 1 1 1 ) ”
  &&  ((( &( "lower" ) )) # Int  |-> lower)
) \/
(
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (PreH1 : (lower_pre > (upper_pre - lower_pre ))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre )) (PreH4 : (0 <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) ,
  TT && emp 
|--
  “ (DigitProductProgress upper_pre (upper_pre - lower_pre ) prime_pre 1 1 1 ) ”
  &&  emp
).

Definition binomial_digit_mod_prime_entail_wit_1_1_split_goal_1 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (PreH1 : (lower_pre > (upper_pre - lower_pre ))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre )) (PreH4 : (0 <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) ,
  (DigitProductProgress upper_pre (upper_pre - lower_pre ) prime_pre 1 1 1 )
.

Definition binomial_digit_mod_prime_entail_wit_1_2 := 
(
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (PreH1 : (lower_pre <= (upper_pre - lower_pre ))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre )) (PreH4 : (0 <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) ,
  TT && emp 
|--
  “ (PrimeForLucas prime_pre ) ” 
  &&  “ (0 <= lower_pre) ” 
  &&  “ (lower_pre <= upper_pre) ” 
  &&  “ (upper_pre < prime_pre) ” 
  &&  “ (2 <= prime_pre) ” 
  &&  “ (prime_pre <= 100000) ” 
  &&  “ (lower_pre <= (upper_pre - lower_pre )) ” 
  &&  “ (0 <= lower_pre) ” 
  &&  “ (lower_pre <= (upper_pre - lower_pre )) ” 
  &&  “ (1 <= 1) ” 
  &&  “ (1 <= (lower_pre + 1 )) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 < prime_pre) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 < prime_pre) ” 
  &&  “ (DigitBinomialMachineSafe upper_pre lower_pre prime_pre ) ” 
  &&  “ (DigitProductProgress upper_pre lower_pre prime_pre 1 1 1 ) ”
  &&  emp
) \/
(
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (PreH1 : (lower_pre <= (upper_pre - lower_pre ))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre )) (PreH4 : (0 <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) ,
  TT && emp 
|--
  “ (DigitProductProgress upper_pre lower_pre prime_pre 1 1 1 ) ”
  &&  emp
).

Definition binomial_digit_mod_prime_entail_wit_1_2_split_goal_1 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (PreH1 : (lower_pre <= (upper_pre - lower_pre ))) (PreH2 : (lower_pre <= upper_pre)) (PreH3 : (PrimeForLucas prime_pre )) (PreH4 : (0 <= lower_pre)) (PreH5 : (lower_pre <= upper_pre)) (PreH6 : (upper_pre < prime_pre)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) ,
  (DigitProductProgress upper_pre lower_pre prime_pre 1 1 1 )
.

Definition binomial_digit_mod_prime_entail_wit_2_1 := 
(
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (PreH1 : (i <= lower_pre)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_pre <= (upper_pre - lower_pre ))) (PreH9 : (0 <= lower_pre)) (PreH10 : (lower_pre <= (upper_pre - lower_pre ))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower_pre + 1 ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH18 : (DigitProductProgress upper_pre lower_pre prime_pre i numerator denominator )) ,
  TT && emp 
|--
  “ (PrimeForLucas prime_pre ) ” 
  &&  “ (0 <= lower_pre) ” 
  &&  “ (lower_pre <= upper_pre) ” 
  &&  “ (upper_pre < prime_pre) ” 
  &&  “ (2 <= prime_pre) ” 
  &&  “ (prime_pre <= 100000) ” 
  &&  “ (lower_pre <= (upper_pre - lower_pre )) ” 
  &&  “ (0 <= lower_pre) ” 
  &&  “ (lower_pre <= (upper_pre - lower_pre )) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (lower_pre + 1 )) ” 
  &&  “ (0 <= ((numerator * ((upper_pre - lower_pre ) + i ) ) % ( prime_pre ) )) ” 
  &&  “ (((numerator * ((upper_pre - lower_pre ) + i ) ) % ( prime_pre ) ) < prime_pre) ” 
  &&  “ (0 <= ((denominator * i ) % ( prime_pre ) )) ” 
  &&  “ (((denominator * i ) % ( prime_pre ) ) < prime_pre) ” 
  &&  “ (DigitBinomialMachineSafe upper_pre lower_pre prime_pre ) ” 
  &&  “ (DigitProductProgress upper_pre lower_pre prime_pre (i + 1 ) ((numerator * ((upper_pre - lower_pre ) + i ) ) % ( prime_pre ) ) ((denominator * i ) % ( prime_pre ) ) ) ”
  &&  emp
) \/
(
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (PreH1 : (i <= lower_pre)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_pre <= (upper_pre - lower_pre ))) (PreH9 : (0 <= lower_pre)) (PreH10 : (lower_pre <= (upper_pre - lower_pre ))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower_pre + 1 ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH18 : (DigitProductProgress upper_pre lower_pre prime_pre i numerator denominator )) ,
  TT && emp 
|--
  “ (DigitProductProgress upper_pre lower_pre prime_pre (i + 1 ) ((numerator * ((upper_pre - lower_pre ) + i ) ) % ( prime_pre ) ) ((denominator * i ) % ( prime_pre ) ) ) ” 
  &&  “ (((denominator * i ) % ( prime_pre ) ) < prime_pre) ” 
  &&  “ (0 <= ((denominator * i ) % ( prime_pre ) )) ” 
  &&  “ (((numerator * ((upper_pre - lower_pre ) + i ) ) % ( prime_pre ) ) < prime_pre) ” 
  &&  “ (0 <= ((numerator * ((upper_pre - lower_pre ) + i ) ) % ( prime_pre ) )) ”
  &&  emp
).

Definition binomial_digit_mod_prime_entail_wit_2_1_split_goal_1 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (PreH1 : (i <= lower_pre)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_pre <= (upper_pre - lower_pre ))) (PreH9 : (0 <= lower_pre)) (PreH10 : (lower_pre <= (upper_pre - lower_pre ))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower_pre + 1 ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH18 : (DigitProductProgress upper_pre lower_pre prime_pre i numerator denominator )) ,
  (DigitProductProgress upper_pre lower_pre prime_pre (i + 1 ) ((numerator * ((upper_pre - lower_pre ) + i ) ) % ( prime_pre ) ) ((denominator * i ) % ( prime_pre ) ) )
.

Definition binomial_digit_mod_prime_entail_wit_2_1_split_goal_2 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (PreH1 : (i <= lower_pre)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_pre <= (upper_pre - lower_pre ))) (PreH9 : (0 <= lower_pre)) (PreH10 : (lower_pre <= (upper_pre - lower_pre ))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower_pre + 1 ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH18 : (DigitProductProgress upper_pre lower_pre prime_pre i numerator denominator )) ,
  (((denominator * i ) % ( prime_pre ) ) < prime_pre)
.

Definition binomial_digit_mod_prime_entail_wit_2_1_split_goal_3 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (PreH1 : (i <= lower_pre)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_pre <= (upper_pre - lower_pre ))) (PreH9 : (0 <= lower_pre)) (PreH10 : (lower_pre <= (upper_pre - lower_pre ))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower_pre + 1 ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH18 : (DigitProductProgress upper_pre lower_pre prime_pre i numerator denominator )) ,
  (0 <= ((denominator * i ) % ( prime_pre ) ))
.

Definition binomial_digit_mod_prime_entail_wit_2_1_split_goal_4 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (PreH1 : (i <= lower_pre)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_pre <= (upper_pre - lower_pre ))) (PreH9 : (0 <= lower_pre)) (PreH10 : (lower_pre <= (upper_pre - lower_pre ))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower_pre + 1 ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH18 : (DigitProductProgress upper_pre lower_pre prime_pre i numerator denominator )) ,
  (((numerator * ((upper_pre - lower_pre ) + i ) ) % ( prime_pre ) ) < prime_pre)
.

Definition binomial_digit_mod_prime_entail_wit_2_1_split_goal_5 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (PreH1 : (i <= lower_pre)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_pre <= (upper_pre - lower_pre ))) (PreH9 : (0 <= lower_pre)) (PreH10 : (lower_pre <= (upper_pre - lower_pre ))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower_pre + 1 ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH18 : (DigitProductProgress upper_pre lower_pre prime_pre i numerator denominator )) ,
  (0 <= ((numerator * ((upper_pre - lower_pre ) + i ) ) % ( prime_pre ) ))
.

Definition binomial_digit_mod_prime_entail_wit_2_2 := 
(
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (lower: Z) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (upper_pre - lower_pre ))) (PreH9 : (lower_pre > (upper_pre - lower_pre ))) (PreH10 : (0 <= lower)) (PreH11 : (lower <= (upper_pre - lower ))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1 ))) (PreH14 : (0 <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : (0 <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH19 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator )) ,
  ((( &( "lower" ) )) # Int  |-> lower)
|--
  EX (lower_2: Z) ,
  “ (PrimeForLucas prime_pre ) ” 
  &&  “ (0 <= lower_pre) ” 
  &&  “ (lower_pre <= upper_pre) ” 
  &&  “ (upper_pre < prime_pre) ” 
  &&  “ (2 <= prime_pre) ” 
  &&  “ (prime_pre <= 100000) ” 
  &&  “ (lower_2 = (upper_pre - lower_pre )) ” 
  &&  “ (lower_pre > (upper_pre - lower_pre )) ” 
  &&  “ (0 <= lower_2) ” 
  &&  “ (lower_2 <= (upper_pre - lower_2 )) ” 
  &&  “ (1 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= (lower_2 + 1 )) ” 
  &&  “ (0 <= ((numerator * ((upper_pre - lower ) + i ) ) % ( prime_pre ) )) ” 
  &&  “ (((numerator * ((upper_pre - lower ) + i ) ) % ( prime_pre ) ) < prime_pre) ” 
  &&  “ (0 <= ((denominator * i ) % ( prime_pre ) )) ” 
  &&  “ (((denominator * i ) % ( prime_pre ) ) < prime_pre) ” 
  &&  “ (DigitBinomialMachineSafe upper_pre lower_pre prime_pre ) ” 
  &&  “ (DigitProductProgress upper_pre lower_2 prime_pre (i + 1 ) ((numerator * ((upper_pre - lower ) + i ) ) % ( prime_pre ) ) ((denominator * i ) % ( prime_pre ) ) ) ”
  &&  ((( &( "lower" ) )) # Int  |-> lower_2)
) \/
(
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (lower: Z) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (upper_pre - lower_pre ))) (PreH9 : (lower_pre > (upper_pre - lower_pre ))) (PreH10 : (0 <= lower)) (PreH11 : (lower <= (upper_pre - lower ))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1 ))) (PreH14 : (0 <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : (0 <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH19 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator )) ,
  TT && emp 
|--
  “ (DigitProductProgress upper_pre (upper_pre - lower_pre ) prime_pre (i + 1 ) ((numerator * ((upper_pre - (upper_pre - lower_pre ) ) + i ) ) % ( prime_pre ) ) ((denominator * i ) % ( prime_pre ) ) ) ” 
  &&  “ (((denominator * i ) % ( prime_pre ) ) < prime_pre) ” 
  &&  “ (0 <= ((denominator * i ) % ( prime_pre ) )) ” 
  &&  “ (((numerator * ((upper_pre - (upper_pre - lower_pre ) ) + i ) ) % ( prime_pre ) ) < prime_pre) ” 
  &&  “ (0 <= ((numerator * ((upper_pre - (upper_pre - lower_pre ) ) + i ) ) % ( prime_pre ) )) ”
  &&  emp
).

Definition binomial_digit_mod_prime_entail_wit_2_2_split_goal_1 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (lower: Z) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (upper_pre - lower_pre ))) (PreH9 : (lower_pre > (upper_pre - lower_pre ))) (PreH10 : (0 <= lower)) (PreH11 : (lower <= (upper_pre - lower ))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1 ))) (PreH14 : (0 <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : (0 <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH19 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator )) ,
  (DigitProductProgress upper_pre (upper_pre - lower_pre ) prime_pre (i + 1 ) ((numerator * ((upper_pre - (upper_pre - lower_pre ) ) + i ) ) % ( prime_pre ) ) ((denominator * i ) % ( prime_pre ) ) )
.

Definition binomial_digit_mod_prime_entail_wit_2_2_split_goal_2 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (lower: Z) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (upper_pre - lower_pre ))) (PreH9 : (lower_pre > (upper_pre - lower_pre ))) (PreH10 : (0 <= lower)) (PreH11 : (lower <= (upper_pre - lower ))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1 ))) (PreH14 : (0 <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : (0 <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH19 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator )) ,
  (((denominator * i ) % ( prime_pre ) ) < prime_pre)
.

Definition binomial_digit_mod_prime_entail_wit_2_2_split_goal_3 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (lower: Z) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (upper_pre - lower_pre ))) (PreH9 : (lower_pre > (upper_pre - lower_pre ))) (PreH10 : (0 <= lower)) (PreH11 : (lower <= (upper_pre - lower ))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1 ))) (PreH14 : (0 <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : (0 <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH19 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator )) ,
  (0 <= ((denominator * i ) % ( prime_pre ) ))
.

Definition binomial_digit_mod_prime_entail_wit_2_2_split_goal_4 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (lower: Z) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (upper_pre - lower_pre ))) (PreH9 : (lower_pre > (upper_pre - lower_pre ))) (PreH10 : (0 <= lower)) (PreH11 : (lower <= (upper_pre - lower ))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1 ))) (PreH14 : (0 <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : (0 <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH19 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator )) ,
  (((numerator * ((upper_pre - (upper_pre - lower_pre ) ) + i ) ) % ( prime_pre ) ) < prime_pre)
.

Definition binomial_digit_mod_prime_entail_wit_2_2_split_goal_5 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (lower: Z) (PreH1 : (i <= lower)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower = (upper_pre - lower_pre ))) (PreH9 : (lower_pre > (upper_pre - lower_pre ))) (PreH10 : (0 <= lower)) (PreH11 : (lower <= (upper_pre - lower ))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower + 1 ))) (PreH14 : (0 <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : (0 <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH19 : (DigitProductProgress upper_pre lower prime_pre i numerator denominator )) ,
  (0 <= ((numerator * ((upper_pre - (upper_pre - lower_pre ) ) + i ) ) % ( prime_pre ) ))
.

Definition binomial_digit_mod_prime_entail_wit_3_1 := 
(
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (PreH1 : (i > lower_pre)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_pre <= (upper_pre - lower_pre ))) (PreH9 : (0 <= lower_pre)) (PreH10 : (lower_pre <= (upper_pre - lower_pre ))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower_pre + 1 ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH18 : (DigitProductProgress upper_pre lower_pre prime_pre i numerator denominator )) ,
  TT && emp 
|--
  “ (PrimeForLucas prime_pre ) ” 
  &&  “ (0 <= lower_pre) ” 
  &&  “ (lower_pre <= upper_pre) ” 
  &&  “ (upper_pre < prime_pre) ” 
  &&  “ (2 <= prime_pre) ” 
  &&  “ (prime_pre <= 100000) ” 
  &&  “ (lower_pre <= (upper_pre - lower_pre )) ” 
  &&  “ (0 <= lower_pre) ” 
  &&  “ (lower_pre <= (upper_pre - lower_pre )) ” 
  &&  “ (0 <= numerator) ” 
  &&  “ (numerator < prime_pre) ” 
  &&  “ (0 <= denominator) ” 
  &&  “ (denominator < prime_pre) ” 
  &&  “ (0 <= (prime_pre - 2 )) ” 
  &&  “ (DigitBinomialMachineSafe upper_pre lower_pre prime_pre ) ” 
  &&  “ (DigitProductProgress upper_pre lower_pre prime_pre (lower_pre + 1 ) numerator denominator ) ”
  &&  emp
) \/
(
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (PreH1 : (i > lower_pre)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_pre <= (upper_pre - lower_pre ))) (PreH9 : (0 <= lower_pre)) (PreH10 : (lower_pre <= (upper_pre - lower_pre ))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower_pre + 1 ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH18 : (DigitProductProgress upper_pre lower_pre prime_pre i numerator denominator )) ,
  TT && emp 
|--
  “ (DigitProductProgress upper_pre lower_pre prime_pre (lower_pre + 1 ) numerator denominator ) ”
  &&  emp
).

Definition binomial_digit_mod_prime_entail_wit_3_1_split_goal_1 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (PreH1 : (i > lower_pre)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_pre <= (upper_pre - lower_pre ))) (PreH9 : (0 <= lower_pre)) (PreH10 : (lower_pre <= (upper_pre - lower_pre ))) (PreH11 : (1 <= i)) (PreH12 : (i <= (lower_pre + 1 ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH18 : (DigitProductProgress upper_pre lower_pre prime_pre i numerator denominator )) ,
  (DigitProductProgress upper_pre lower_pre prime_pre (lower_pre + 1 ) numerator denominator )
.

Definition binomial_digit_mod_prime_entail_wit_3_2 := 
(
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (lower_2: Z) (PreH1 : (i > lower_2)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_2 = (upper_pre - lower_pre ))) (PreH9 : (lower_pre > (upper_pre - lower_pre ))) (PreH10 : (0 <= lower_2)) (PreH11 : (lower_2 <= (upper_pre - lower_2 ))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower_2 + 1 ))) (PreH14 : (0 <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : (0 <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH19 : (DigitProductProgress upper_pre lower_2 prime_pre i numerator denominator )) ,
  ((( &( "lower" ) )) # Int  |-> lower_2)
|--
  EX (lower: Z) ,
  “ (PrimeForLucas prime_pre ) ” 
  &&  “ (0 <= lower_pre) ” 
  &&  “ (lower_pre <= upper_pre) ” 
  &&  “ (upper_pre < prime_pre) ” 
  &&  “ (2 <= prime_pre) ” 
  &&  “ (prime_pre <= 100000) ” 
  &&  “ (lower = (upper_pre - lower_pre )) ” 
  &&  “ (lower_pre > (upper_pre - lower_pre )) ” 
  &&  “ (0 <= lower) ” 
  &&  “ (lower <= (upper_pre - lower )) ” 
  &&  “ (0 <= numerator) ” 
  &&  “ (numerator < prime_pre) ” 
  &&  “ (0 <= denominator) ” 
  &&  “ (denominator < prime_pre) ” 
  &&  “ (0 <= (prime_pre - 2 )) ” 
  &&  “ (DigitBinomialMachineSafe upper_pre lower_pre prime_pre ) ” 
  &&  “ (DigitProductProgress upper_pre lower prime_pre (lower + 1 ) numerator denominator ) ”
  &&  ((( &( "lower" ) )) # Int  |-> lower)
) \/
(
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (lower_2: Z) (PreH1 : (i > lower_2)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_2 = (upper_pre - lower_pre ))) (PreH9 : (lower_pre > (upper_pre - lower_pre ))) (PreH10 : (0 <= lower_2)) (PreH11 : (lower_2 <= (upper_pre - lower_2 ))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower_2 + 1 ))) (PreH14 : (0 <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : (0 <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH19 : (DigitProductProgress upper_pre lower_2 prime_pre i numerator denominator )) ,
  TT && emp 
|--
  “ (DigitProductProgress upper_pre (upper_pre - lower_pre ) prime_pre ((upper_pre - lower_pre ) + 1 ) numerator denominator ) ”
  &&  emp
).

Definition binomial_digit_mod_prime_entail_wit_3_2_split_goal_1 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (denominator: Z) (numerator: Z) (i: Z) (lower_2: Z) (PreH1 : (i > lower_2)) (PreH2 : (PrimeForLucas prime_pre )) (PreH3 : (0 <= lower_pre)) (PreH4 : (lower_pre <= upper_pre)) (PreH5 : (upper_pre < prime_pre)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (lower_2 = (upper_pre - lower_pre ))) (PreH9 : (lower_pre > (upper_pre - lower_pre ))) (PreH10 : (0 <= lower_2)) (PreH11 : (lower_2 <= (upper_pre - lower_2 ))) (PreH12 : (1 <= i)) (PreH13 : (i <= (lower_2 + 1 ))) (PreH14 : (0 <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : (0 <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH19 : (DigitProductProgress upper_pre lower_2 prime_pre i numerator denominator )) ,
  (DigitProductProgress upper_pre (upper_pre - lower_pre ) prime_pre ((upper_pre - lower_pre ) + 1 ) numerator denominator )
.

Definition binomial_digit_mod_prime_return_wit_1 := 
(
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (lower: Z) (numerator: Z) (denominator: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (ModularPower denominator (prime_pre - 2 ) prime_pre retval )) (PreH4 : (PrimeForLucas prime_pre )) (PreH5 : (0 <= lower_pre)) (PreH6 : (lower_pre <= upper_pre)) (PreH7 : (upper_pre < prime_pre)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (lower = (upper_pre - lower_pre ))) (PreH11 : (lower_pre > (upper_pre - lower_pre ))) (PreH12 : (0 <= lower)) (PreH13 : (lower <= (upper_pre - lower ))) (PreH14 : (0 <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : (0 <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (0 <= (prime_pre - 2 ))) (PreH19 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH20 : (DigitProductProgress upper_pre lower prime_pre (lower + 1 ) numerator denominator )) ,
  TT && emp 
|--
  “ (0 <= ((numerator * retval ) % ( prime_pre ) )) ” 
  &&  “ (((numerator * retval ) % ( prime_pre ) ) < prime_pre) ” 
  &&  “ (BinomialDigitResidue upper_pre lower_pre prime_pre ((numerator * retval ) % ( prime_pre ) ) ) ”
  &&  emp
) \/
(
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (lower: Z) (numerator: Z) (denominator: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (ModularPower denominator (prime_pre - 2 ) prime_pre retval )) (PreH4 : (PrimeForLucas prime_pre )) (PreH5 : (0 <= lower_pre)) (PreH6 : (lower_pre <= upper_pre)) (PreH7 : (upper_pre < prime_pre)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (lower = (upper_pre - lower_pre ))) (PreH11 : (lower_pre > (upper_pre - lower_pre ))) (PreH12 : (0 <= lower)) (PreH13 : (lower <= (upper_pre - lower ))) (PreH14 : (0 <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : (0 <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (0 <= (prime_pre - 2 ))) (PreH19 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH20 : (DigitProductProgress upper_pre lower prime_pre (lower + 1 ) numerator denominator )) ,
  TT && emp 
|--
  “ (BinomialDigitResidue upper_pre lower_pre prime_pre ((numerator * retval ) % ( prime_pre ) ) ) ” 
  &&  “ (((numerator * retval ) % ( prime_pre ) ) < prime_pre) ” 
  &&  “ (0 <= ((numerator * retval ) % ( prime_pre ) )) ”
  &&  emp
).

Definition binomial_digit_mod_prime_return_wit_1_split_goal_1 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (lower: Z) (numerator: Z) (denominator: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (ModularPower denominator (prime_pre - 2 ) prime_pre retval )) (PreH4 : (PrimeForLucas prime_pre )) (PreH5 : (0 <= lower_pre)) (PreH6 : (lower_pre <= upper_pre)) (PreH7 : (upper_pre < prime_pre)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (lower = (upper_pre - lower_pre ))) (PreH11 : (lower_pre > (upper_pre - lower_pre ))) (PreH12 : (0 <= lower)) (PreH13 : (lower <= (upper_pre - lower ))) (PreH14 : (0 <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : (0 <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (0 <= (prime_pre - 2 ))) (PreH19 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH20 : (DigitProductProgress upper_pre lower prime_pre (lower + 1 ) numerator denominator )) ,
  (BinomialDigitResidue upper_pre lower_pre prime_pre ((numerator * retval ) % ( prime_pre ) ) )
.

Definition binomial_digit_mod_prime_return_wit_1_split_goal_2 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (lower: Z) (numerator: Z) (denominator: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (ModularPower denominator (prime_pre - 2 ) prime_pre retval )) (PreH4 : (PrimeForLucas prime_pre )) (PreH5 : (0 <= lower_pre)) (PreH6 : (lower_pre <= upper_pre)) (PreH7 : (upper_pre < prime_pre)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (lower = (upper_pre - lower_pre ))) (PreH11 : (lower_pre > (upper_pre - lower_pre ))) (PreH12 : (0 <= lower)) (PreH13 : (lower <= (upper_pre - lower ))) (PreH14 : (0 <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : (0 <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (0 <= (prime_pre - 2 ))) (PreH19 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH20 : (DigitProductProgress upper_pre lower prime_pre (lower + 1 ) numerator denominator )) ,
  (((numerator * retval ) % ( prime_pre ) ) < prime_pre)
.

Definition binomial_digit_mod_prime_return_wit_1_split_goal_3 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (lower: Z) (numerator: Z) (denominator: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (ModularPower denominator (prime_pre - 2 ) prime_pre retval )) (PreH4 : (PrimeForLucas prime_pre )) (PreH5 : (0 <= lower_pre)) (PreH6 : (lower_pre <= upper_pre)) (PreH7 : (upper_pre < prime_pre)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (lower = (upper_pre - lower_pre ))) (PreH11 : (lower_pre > (upper_pre - lower_pre ))) (PreH12 : (0 <= lower)) (PreH13 : (lower <= (upper_pre - lower ))) (PreH14 : (0 <= numerator)) (PreH15 : (numerator < prime_pre)) (PreH16 : (0 <= denominator)) (PreH17 : (denominator < prime_pre)) (PreH18 : (0 <= (prime_pre - 2 ))) (PreH19 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH20 : (DigitProductProgress upper_pre lower prime_pre (lower + 1 ) numerator denominator )) ,
  (0 <= ((numerator * retval ) % ( prime_pre ) ))
.

Definition binomial_digit_mod_prime_return_wit_2 := 
(
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (numerator: Z) (denominator: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (ModularPower denominator (prime_pre - 2 ) prime_pre retval )) (PreH4 : (PrimeForLucas prime_pre )) (PreH5 : (0 <= lower_pre)) (PreH6 : (lower_pre <= upper_pre)) (PreH7 : (upper_pre < prime_pre)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (lower_pre <= (upper_pre - lower_pre ))) (PreH11 : (0 <= lower_pre)) (PreH12 : (lower_pre <= (upper_pre - lower_pre ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (0 <= (prime_pre - 2 ))) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH19 : (DigitProductProgress upper_pre lower_pre prime_pre (lower_pre + 1 ) numerator denominator )) ,
  TT && emp 
|--
  “ (0 <= ((numerator * retval ) % ( prime_pre ) )) ” 
  &&  “ (((numerator * retval ) % ( prime_pre ) ) < prime_pre) ” 
  &&  “ (BinomialDigitResidue upper_pre lower_pre prime_pre ((numerator * retval ) % ( prime_pre ) ) ) ”
  &&  emp
) \/
(
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (numerator: Z) (denominator: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (ModularPower denominator (prime_pre - 2 ) prime_pre retval )) (PreH4 : (PrimeForLucas prime_pre )) (PreH5 : (0 <= lower_pre)) (PreH6 : (lower_pre <= upper_pre)) (PreH7 : (upper_pre < prime_pre)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (lower_pre <= (upper_pre - lower_pre ))) (PreH11 : (0 <= lower_pre)) (PreH12 : (lower_pre <= (upper_pre - lower_pre ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (0 <= (prime_pre - 2 ))) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH19 : (DigitProductProgress upper_pre lower_pre prime_pre (lower_pre + 1 ) numerator denominator )) ,
  TT && emp 
|--
  “ (BinomialDigitResidue upper_pre lower_pre prime_pre ((numerator * retval ) % ( prime_pre ) ) ) ” 
  &&  “ (((numerator * retval ) % ( prime_pre ) ) < prime_pre) ” 
  &&  “ (0 <= ((numerator * retval ) % ( prime_pre ) )) ”
  &&  emp
).

Definition binomial_digit_mod_prime_return_wit_2_split_goal_1 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (numerator: Z) (denominator: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (ModularPower denominator (prime_pre - 2 ) prime_pre retval )) (PreH4 : (PrimeForLucas prime_pre )) (PreH5 : (0 <= lower_pre)) (PreH6 : (lower_pre <= upper_pre)) (PreH7 : (upper_pre < prime_pre)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (lower_pre <= (upper_pre - lower_pre ))) (PreH11 : (0 <= lower_pre)) (PreH12 : (lower_pre <= (upper_pre - lower_pre ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (0 <= (prime_pre - 2 ))) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH19 : (DigitProductProgress upper_pre lower_pre prime_pre (lower_pre + 1 ) numerator denominator )) ,
  (BinomialDigitResidue upper_pre lower_pre prime_pre ((numerator * retval ) % ( prime_pre ) ) )
.

Definition binomial_digit_mod_prime_return_wit_2_split_goal_2 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (numerator: Z) (denominator: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (ModularPower denominator (prime_pre - 2 ) prime_pre retval )) (PreH4 : (PrimeForLucas prime_pre )) (PreH5 : (0 <= lower_pre)) (PreH6 : (lower_pre <= upper_pre)) (PreH7 : (upper_pre < prime_pre)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (lower_pre <= (upper_pre - lower_pre ))) (PreH11 : (0 <= lower_pre)) (PreH12 : (lower_pre <= (upper_pre - lower_pre ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (0 <= (prime_pre - 2 ))) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH19 : (DigitProductProgress upper_pre lower_pre prime_pre (lower_pre + 1 ) numerator denominator )) ,
  (((numerator * retval ) % ( prime_pre ) ) < prime_pre)
.

Definition binomial_digit_mod_prime_return_wit_2_split_goal_3 := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (numerator: Z) (denominator: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (ModularPower denominator (prime_pre - 2 ) prime_pre retval )) (PreH4 : (PrimeForLucas prime_pre )) (PreH5 : (0 <= lower_pre)) (PreH6 : (lower_pre <= upper_pre)) (PreH7 : (upper_pre < prime_pre)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (lower_pre <= (upper_pre - lower_pre ))) (PreH11 : (0 <= lower_pre)) (PreH12 : (lower_pre <= (upper_pre - lower_pre ))) (PreH13 : (0 <= numerator)) (PreH14 : (numerator < prime_pre)) (PreH15 : (0 <= denominator)) (PreH16 : (denominator < prime_pre)) (PreH17 : (0 <= (prime_pre - 2 ))) (PreH18 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH19 : (DigitProductProgress upper_pre lower_pre prime_pre (lower_pre + 1 ) numerator denominator )) ,
  (0 <= ((numerator * retval ) % ( prime_pre ) ))
.

Definition binomial_digit_mod_prime_partial_solve_wit_1_pure := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (lower: Z) (numerator: Z) (denominator: Z) (PreH1 : (PrimeForLucas prime_pre )) (PreH2 : (0 <= lower_pre)) (PreH3 : (lower_pre <= upper_pre)) (PreH4 : (upper_pre < prime_pre)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (lower = (upper_pre - lower_pre ))) (PreH8 : (lower_pre > (upper_pre - lower_pre ))) (PreH9 : (0 <= lower)) (PreH10 : (lower <= (upper_pre - lower ))) (PreH11 : (0 <= numerator)) (PreH12 : (numerator < prime_pre)) (PreH13 : (0 <= denominator)) (PreH14 : (denominator < prime_pre)) (PreH15 : (0 <= (prime_pre - 2 ))) (PreH16 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH17 : (DigitProductProgress upper_pre lower prime_pre (lower + 1 ) numerator denominator )) ,
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
.

Definition binomial_digit_mod_prime_partial_solve_wit_1_aux := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (lower: Z) (numerator: Z) (denominator: Z) (PreH1 : (PrimeForLucas prime_pre )) (PreH2 : (0 <= lower_pre)) (PreH3 : (lower_pre <= upper_pre)) (PreH4 : (upper_pre < prime_pre)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (lower = (upper_pre - lower_pre ))) (PreH8 : (lower_pre > (upper_pre - lower_pre ))) (PreH9 : (0 <= lower)) (PreH10 : (lower <= (upper_pre - lower ))) (PreH11 : (0 <= numerator)) (PreH12 : (numerator < prime_pre)) (PreH13 : (0 <= denominator)) (PreH14 : (denominator < prime_pre)) (PreH15 : (0 <= (prime_pre - 2 ))) (PreH16 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH17 : (DigitProductProgress upper_pre lower prime_pre (lower + 1 ) numerator denominator )) ,
  TT && emp 
|--
  “ (0 <= denominator) ” 
  &&  “ (denominator < prime_pre) ” 
  &&  “ (0 <= (prime_pre - 2 )) ” 
  &&  “ (2 <= prime_pre) ” 
  &&  “ (PrimeForLucas prime_pre ) ” 
  &&  “ (0 <= lower_pre) ” 
  &&  “ (lower_pre <= upper_pre) ” 
  &&  “ (upper_pre < prime_pre) ” 
  &&  “ (2 <= prime_pre) ” 
  &&  “ (prime_pre <= 100000) ” 
  &&  “ (lower = (upper_pre - lower_pre )) ” 
  &&  “ (lower_pre > (upper_pre - lower_pre )) ” 
  &&  “ (0 <= lower) ” 
  &&  “ (lower <= (upper_pre - lower )) ” 
  &&  “ (0 <= numerator) ” 
  &&  “ (numerator < prime_pre) ” 
  &&  “ (0 <= denominator) ” 
  &&  “ (denominator < prime_pre) ” 
  &&  “ (0 <= (prime_pre - 2 )) ” 
  &&  “ (DigitBinomialMachineSafe upper_pre lower_pre prime_pre ) ” 
  &&  “ (DigitProductProgress upper_pre lower prime_pre (lower + 1 ) numerator denominator ) ”
  &&  emp
.

Definition binomial_digit_mod_prime_partial_solve_wit_1 := binomial_digit_mod_prime_partial_solve_wit_1_pure -> binomial_digit_mod_prime_partial_solve_wit_1_aux.

Definition binomial_digit_mod_prime_partial_solve_wit_2_pure := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (numerator: Z) (denominator: Z) (PreH1 : (PrimeForLucas prime_pre )) (PreH2 : (0 <= lower_pre)) (PreH3 : (lower_pre <= upper_pre)) (PreH4 : (upper_pre < prime_pre)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (lower_pre <= (upper_pre - lower_pre ))) (PreH8 : (0 <= lower_pre)) (PreH9 : (lower_pre <= (upper_pre - lower_pre ))) (PreH10 : (0 <= numerator)) (PreH11 : (numerator < prime_pre)) (PreH12 : (0 <= denominator)) (PreH13 : (denominator < prime_pre)) (PreH14 : (0 <= (prime_pre - 2 ))) (PreH15 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH16 : (DigitProductProgress upper_pre lower_pre prime_pre (lower_pre + 1 ) numerator denominator )) ,
  ((( &( "inverse" ) )) # Int  |->_)
  **  ((( &( "upper" ) )) # Int  |-> upper_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "lower" ) )) # Int  |-> lower_pre)
  **  ((( &( "numerator" ) )) # Int  |-> numerator)
  **  ((( &( "denominator" ) )) # Int  |-> denominator)
|--
  “ (0 <= denominator) ” 
  &&  “ (denominator < prime_pre) ” 
  &&  “ (0 <= (prime_pre - 2 )) ” 
  &&  “ (2 <= prime_pre) ”
.

Definition binomial_digit_mod_prime_partial_solve_wit_2_aux := 
forall (prime_pre: Z) (lower_pre: Z) (upper_pre: Z) (numerator: Z) (denominator: Z) (PreH1 : (PrimeForLucas prime_pre )) (PreH2 : (0 <= lower_pre)) (PreH3 : (lower_pre <= upper_pre)) (PreH4 : (upper_pre < prime_pre)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (lower_pre <= (upper_pre - lower_pre ))) (PreH8 : (0 <= lower_pre)) (PreH9 : (lower_pre <= (upper_pre - lower_pre ))) (PreH10 : (0 <= numerator)) (PreH11 : (numerator < prime_pre)) (PreH12 : (0 <= denominator)) (PreH13 : (denominator < prime_pre)) (PreH14 : (0 <= (prime_pre - 2 ))) (PreH15 : (DigitBinomialMachineSafe upper_pre lower_pre prime_pre )) (PreH16 : (DigitProductProgress upper_pre lower_pre prime_pre (lower_pre + 1 ) numerator denominator )) ,
  TT && emp 
|--
  “ (0 <= denominator) ” 
  &&  “ (denominator < prime_pre) ” 
  &&  “ (0 <= (prime_pre - 2 )) ” 
  &&  “ (2 <= prime_pre) ” 
  &&  “ (PrimeForLucas prime_pre ) ” 
  &&  “ (0 <= lower_pre) ” 
  &&  “ (lower_pre <= upper_pre) ” 
  &&  “ (upper_pre < prime_pre) ” 
  &&  “ (2 <= prime_pre) ” 
  &&  “ (prime_pre <= 100000) ” 
  &&  “ (lower_pre <= (upper_pre - lower_pre )) ” 
  &&  “ (0 <= lower_pre) ” 
  &&  “ (lower_pre <= (upper_pre - lower_pre )) ” 
  &&  “ (0 <= numerator) ” 
  &&  “ (numerator < prime_pre) ” 
  &&  “ (0 <= denominator) ” 
  &&  “ (denominator < prime_pre) ” 
  &&  “ (0 <= (prime_pre - 2 )) ” 
  &&  “ (DigitBinomialMachineSafe upper_pre lower_pre prime_pre ) ” 
  &&  “ (DigitProductProgress upper_pre lower_pre prime_pre (lower_pre + 1 ) numerator denominator ) ”
  &&  emp
.

Definition binomial_digit_mod_prime_partial_solve_wit_2 := binomial_digit_mod_prime_partial_solve_wit_2_pure -> binomial_digit_mod_prime_partial_solve_wit_2_aux.

(*----- Function lucas_theorem -----*)

Definition lucas_theorem_safety_wit_1 := 
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (PrimeForLucas prime_pre )) (PreH8 : (LucasMachineSafe n_pre m_pre prime_pre )) ,
  ((( &( "upper" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
|--
  “ ((n_pre + m_pre ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (n_pre + m_pre )) ”
.

Definition lucas_theorem_safety_wit_2 := 
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (PrimeForLucas prime_pre )) (PreH8 : (LucasMachineSafe n_pre m_pre prime_pre )) ,
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
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (result: Z) (upper: Z) (lower: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (PrimeForLucas prime_pre )) (PreH8 : (LucasMachineSafe n_pre m_pre prime_pre )) (PreH9 : (0 <= lower)) (PreH10 : (lower <= upper)) (PreH11 : (upper <= (n_pre + m_pre ))) (PreH12 : ((n_pre + m_pre ) <= 200000)) (PreH13 : (0 <= result)) (PreH14 : (result < prime_pre)) (PreH15 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
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
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (result: Z) (upper: Z) (lower: Z) (PreH1 : (upper <= 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100000)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (PrimeForLucas prime_pre )) (PreH9 : (LucasMachineSafe n_pre m_pre prime_pre )) (PreH10 : (0 <= lower)) (PreH11 : (lower <= upper)) (PreH12 : (upper <= (n_pre + m_pre ))) (PreH13 : ((n_pre + m_pre ) <= 200000)) (PreH14 : (0 <= result)) (PreH15 : (result < prime_pre)) (PreH16 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
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
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (result: Z) (upper: Z) (lower: Z) (PreH1 : (lower > 0)) (PreH2 : (upper <= 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (PrimeForLucas prime_pre )) (PreH10 : (LucasMachineSafe n_pre m_pre prime_pre )) (PreH11 : (0 <= lower)) (PreH12 : (lower <= upper)) (PreH13 : (upper <= (n_pre + m_pre ))) (PreH14 : ((n_pre + m_pre ) <= 200000)) (PreH15 : (0 <= result)) (PreH16 : (result < prime_pre)) (PreH17 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
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
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (result: Z) (upper: Z) (lower: Z) (PreH1 : (upper > 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100000)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (PrimeForLucas prime_pre )) (PreH9 : (LucasMachineSafe n_pre m_pre prime_pre )) (PreH10 : (0 <= lower)) (PreH11 : (lower <= upper)) (PreH12 : (upper <= (n_pre + m_pre ))) (PreH13 : ((n_pre + m_pre ) <= 200000)) (PreH14 : (0 <= result)) (PreH15 : (result < prime_pre)) (PreH16 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
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
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (result: Z) (upper: Z) (lower: Z) (PreH1 : (upper > 0)) (PreH2 : (1 <= n_pre)) (PreH3 : (n_pre <= 100000)) (PreH4 : (1 <= m_pre)) (PreH5 : (m_pre <= 100000)) (PreH6 : (2 <= prime_pre)) (PreH7 : (prime_pre <= 100000)) (PreH8 : (PrimeForLucas prime_pre )) (PreH9 : (LucasMachineSafe n_pre m_pre prime_pre )) (PreH10 : (0 <= lower)) (PreH11 : (lower <= upper)) (PreH12 : (upper <= (n_pre + m_pre ))) (PreH13 : ((n_pre + m_pre ) <= 200000)) (PreH14 : (0 <= result)) (PreH15 : (result < prime_pre)) (PreH16 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
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
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (result: Z) (upper: Z) (lower: Z) (PreH1 : ((lower % ( prime_pre ) ) > (upper % ( prime_pre ) ))) (PreH2 : (upper > 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (PrimeForLucas prime_pre )) (PreH10 : (LucasMachineSafe n_pre m_pre prime_pre )) (PreH11 : (0 <= lower)) (PreH12 : (lower <= upper)) (PreH13 : (upper <= (n_pre + m_pre ))) (PreH14 : ((n_pre + m_pre ) <= 200000)) (PreH15 : (0 <= result)) (PreH16 : (result < prime_pre)) (PreH17 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
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
(
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (upper: Z) (lower: Z) (upper_digit: Z) (lower_digit: Z) (result: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (BinomialDigitResidue upper_digit lower_digit prime_pre retval )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100000)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (PrimeForLucas prime_pre )) (PreH11 : (LucasMachineSafe n_pre m_pre prime_pre )) (PreH12 : (0 < upper)) (PreH13 : (0 <= lower)) (PreH14 : (lower <= upper)) (PreH15 : (upper <= (n_pre + m_pre ))) (PreH16 : ((n_pre + m_pre ) <= 200000)) (PreH17 : (upper_digit = (upper % ( prime_pre ) ))) (PreH18 : (lower_digit = (lower % ( prime_pre ) ))) (PreH19 : (0 <= lower_digit)) (PreH20 : (lower_digit <= upper_digit)) (PreH21 : (upper_digit < prime_pre)) (PreH22 : (0 <= result)) (PreH23 : (result < prime_pre)) (PreH24 : (DigitBinomialMachineSafe upper_digit lower_digit prime_pre )) (PreH25 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  ((( &( "product" ) )) # Int  |->_)
  **  ((( &( "digit_binomial" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "upper" ) )) # Int  |-> upper)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "upper_digit" ) )) # Int  |-> upper_digit)
  **  ((( &( "lower_digit" ) )) # Int  |-> lower_digit)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ ((result * retval ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (result * retval )) ”
) \/
(
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (upper: Z) (lower: Z) (upper_digit: Z) (lower_digit: Z) (result: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (BinomialDigitResidue upper_digit lower_digit prime_pre retval )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100000)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (PrimeForLucas prime_pre )) (PreH11 : (LucasMachineSafe n_pre m_pre prime_pre )) (PreH12 : (0 < upper)) (PreH13 : (0 <= lower)) (PreH14 : (lower <= upper)) (PreH15 : (upper <= (n_pre + m_pre ))) (PreH16 : ((n_pre + m_pre ) <= 200000)) (PreH17 : (upper_digit = (upper % ( prime_pre ) ))) (PreH18 : (lower_digit = (lower % ( prime_pre ) ))) (PreH19 : (0 <= lower_digit)) (PreH20 : (lower_digit <= upper_digit)) (PreH21 : (upper_digit < prime_pre)) (PreH22 : (0 <= result)) (PreH23 : (result < prime_pre)) (PreH24 : (DigitBinomialMachineSafe upper_digit lower_digit prime_pre )) (PreH25 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  ((( &( "product" ) )) # Int  |->_)
  **  ((( &( "digit_binomial" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "upper" ) )) # Int  |-> upper)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "upper_digit" ) )) # Int  |-> upper_digit)
  **  ((( &( "lower_digit" ) )) # Int  |-> lower_digit)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ ((result * retval ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (result * retval )) ”
).

Definition lucas_theorem_safety_wit_9_split_goal_1 := 
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (upper: Z) (lower: Z) (upper_digit: Z) (lower_digit: Z) (result: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (BinomialDigitResidue upper_digit lower_digit prime_pre retval )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100000)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (PrimeForLucas prime_pre )) (PreH11 : (LucasMachineSafe n_pre m_pre prime_pre )) (PreH12 : (0 < upper)) (PreH13 : (0 <= lower)) (PreH14 : (lower <= upper)) (PreH15 : (upper <= (n_pre + m_pre ))) (PreH16 : ((n_pre + m_pre ) <= 200000)) (PreH17 : (upper_digit = (upper % ( prime_pre ) ))) (PreH18 : (lower_digit = (lower % ( prime_pre ) ))) (PreH19 : (0 <= lower_digit)) (PreH20 : (lower_digit <= upper_digit)) (PreH21 : (upper_digit < prime_pre)) (PreH22 : (0 <= result)) (PreH23 : (result < prime_pre)) (PreH24 : (DigitBinomialMachineSafe upper_digit lower_digit prime_pre )) (PreH25 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  ((( &( "product" ) )) # Int  |->_)
  **  ((( &( "digit_binomial" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "upper" ) )) # Int  |-> upper)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "upper_digit" ) )) # Int  |-> upper_digit)
  **  ((( &( "lower_digit" ) )) # Int  |-> lower_digit)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ ((result * retval ) <= INT_MAX) ”
.

Definition lucas_theorem_safety_wit_9_split_goal_2 := 
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (upper: Z) (lower: Z) (upper_digit: Z) (lower_digit: Z) (result: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (BinomialDigitResidue upper_digit lower_digit prime_pre retval )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100000)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (PrimeForLucas prime_pre )) (PreH11 : (LucasMachineSafe n_pre m_pre prime_pre )) (PreH12 : (0 < upper)) (PreH13 : (0 <= lower)) (PreH14 : (lower <= upper)) (PreH15 : (upper <= (n_pre + m_pre ))) (PreH16 : ((n_pre + m_pre ) <= 200000)) (PreH17 : (upper_digit = (upper % ( prime_pre ) ))) (PreH18 : (lower_digit = (lower % ( prime_pre ) ))) (PreH19 : (0 <= lower_digit)) (PreH20 : (lower_digit <= upper_digit)) (PreH21 : (upper_digit < prime_pre)) (PreH22 : (0 <= result)) (PreH23 : (result < prime_pre)) (PreH24 : (DigitBinomialMachineSafe upper_digit lower_digit prime_pre )) (PreH25 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  ((( &( "product" ) )) # Int  |->_)
  **  ((( &( "digit_binomial" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "upper" ) )) # Int  |-> upper)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "upper_digit" ) )) # Int  |-> upper_digit)
  **  ((( &( "lower_digit" ) )) # Int  |-> lower_digit)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ ((INT_MIN) <= (result * retval )) ”
.

Definition lucas_theorem_safety_wit_10 := 
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (upper: Z) (lower: Z) (upper_digit: Z) (lower_digit: Z) (result: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (BinomialDigitResidue upper_digit lower_digit prime_pre retval )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100000)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (PrimeForLucas prime_pre )) (PreH11 : (LucasMachineSafe n_pre m_pre prime_pre )) (PreH12 : (0 < upper)) (PreH13 : (0 <= lower)) (PreH14 : (lower <= upper)) (PreH15 : (upper <= (n_pre + m_pre ))) (PreH16 : ((n_pre + m_pre ) <= 200000)) (PreH17 : (upper_digit = (upper % ( prime_pre ) ))) (PreH18 : (lower_digit = (lower % ( prime_pre ) ))) (PreH19 : (0 <= lower_digit)) (PreH20 : (lower_digit <= upper_digit)) (PreH21 : (upper_digit < prime_pre)) (PreH22 : (0 <= result)) (PreH23 : (result < prime_pre)) (PreH24 : (DigitBinomialMachineSafe upper_digit lower_digit prime_pre )) (PreH25 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  ((( &( "product" ) )) # Int  |-> (result * retval ))
  **  ((( &( "digit_binomial" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "upper" ) )) # Int  |-> upper)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "upper_digit" ) )) # Int  |-> upper_digit)
  **  ((( &( "lower_digit" ) )) # Int  |-> lower_digit)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ (((result * retval ) <> (INT_MIN)) \/ (prime_pre <> (-1))) ” 
  &&  “ (prime_pre <> 0) ”
.

Definition lucas_theorem_safety_wit_11 := 
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (upper: Z) (lower: Z) (upper_digit: Z) (lower_digit: Z) (result: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (BinomialDigitResidue upper_digit lower_digit prime_pre retval )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100000)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (PrimeForLucas prime_pre )) (PreH11 : (LucasMachineSafe n_pre m_pre prime_pre )) (PreH12 : (0 < upper)) (PreH13 : (0 <= lower)) (PreH14 : (lower <= upper)) (PreH15 : (upper <= (n_pre + m_pre ))) (PreH16 : ((n_pre + m_pre ) <= 200000)) (PreH17 : (upper_digit = (upper % ( prime_pre ) ))) (PreH18 : (lower_digit = (lower % ( prime_pre ) ))) (PreH19 : (0 <= lower_digit)) (PreH20 : (lower_digit <= upper_digit)) (PreH21 : (upper_digit < prime_pre)) (PreH22 : (0 <= result)) (PreH23 : (result < prime_pre)) (PreH24 : (DigitBinomialMachineSafe upper_digit lower_digit prime_pre )) (PreH25 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  ((( &( "product" ) )) # Int  |-> (result * retval ))
  **  ((( &( "digit_binomial" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "upper" ) )) # Int  |-> upper)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "upper_digit" ) )) # Int  |-> upper_digit)
  **  ((( &( "lower_digit" ) )) # Int  |-> lower_digit)
  **  ((( &( "result" ) )) # Int  |-> ((result * retval ) % ( prime_pre ) ))
|--
  “ ((upper <> (INT_MIN)) \/ (prime_pre <> (-1))) ” 
  &&  “ (prime_pre <> 0) ”
.

Definition lucas_theorem_safety_wit_12 := 
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (upper: Z) (lower: Z) (upper_digit: Z) (lower_digit: Z) (result: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (BinomialDigitResidue upper_digit lower_digit prime_pre retval )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100000)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (PrimeForLucas prime_pre )) (PreH11 : (LucasMachineSafe n_pre m_pre prime_pre )) (PreH12 : (0 < upper)) (PreH13 : (0 <= lower)) (PreH14 : (lower <= upper)) (PreH15 : (upper <= (n_pre + m_pre ))) (PreH16 : ((n_pre + m_pre ) <= 200000)) (PreH17 : (upper_digit = (upper % ( prime_pre ) ))) (PreH18 : (lower_digit = (lower % ( prime_pre ) ))) (PreH19 : (0 <= lower_digit)) (PreH20 : (lower_digit <= upper_digit)) (PreH21 : (upper_digit < prime_pre)) (PreH22 : (0 <= result)) (PreH23 : (result < prime_pre)) (PreH24 : (DigitBinomialMachineSafe upper_digit lower_digit prime_pre )) (PreH25 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  ((( &( "product" ) )) # Int  |-> (result * retval ))
  **  ((( &( "digit_binomial" ) )) # Int  |-> retval)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "upper" ) )) # Int  |-> (upper ÷ prime_pre ))
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "upper_digit" ) )) # Int  |-> upper_digit)
  **  ((( &( "lower_digit" ) )) # Int  |-> lower_digit)
  **  ((( &( "result" ) )) # Int  |-> ((result * retval ) % ( prime_pre ) ))
|--
  “ ((lower <> (INT_MIN)) \/ (prime_pre <> (-1))) ” 
  &&  “ (prime_pre <> 0) ”
.

Definition lucas_theorem_entail_wit_1 := 
(
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (PrimeForLucas prime_pre )) (PreH8 : (LucasMachineSafe n_pre m_pre prime_pre )) ,
  TT && emp 
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (2 <= prime_pre) ” 
  &&  “ (prime_pre <= 100000) ” 
  &&  “ (PrimeForLucas prime_pre ) ” 
  &&  “ (LucasMachineSafe n_pre m_pre prime_pre ) ” 
  &&  “ (0 <= n_pre) ” 
  &&  “ (n_pre <= (n_pre + m_pre )) ” 
  &&  “ ((n_pre + m_pre ) <= (n_pre + m_pre )) ” 
  &&  “ ((n_pre + m_pre ) <= 200000) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 < prime_pre) ” 
  &&  “ (LucasProgress (n_pre + m_pre ) n_pre prime_pre (n_pre + m_pre ) n_pre 1 ) ”
  &&  emp
) \/
(
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (PrimeForLucas prime_pre )) (PreH8 : (LucasMachineSafe n_pre m_pre prime_pre )) ,
  TT && emp 
|--
  “ (LucasProgress (n_pre + m_pre ) n_pre prime_pre (n_pre + m_pre ) n_pre 1 ) ”
  &&  emp
).

Definition lucas_theorem_entail_wit_1_split_goal_1 := 
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (PrimeForLucas prime_pre )) (PreH8 : (LucasMachineSafe n_pre m_pre prime_pre )) ,
  (LucasProgress (n_pre + m_pre ) n_pre prime_pre (n_pre + m_pre ) n_pre 1 )
.

Definition lucas_theorem_entail_wit_2 := 
(
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (result: Z) (upper: Z) (lower: Z) (PreH1 : ((lower % ( prime_pre ) ) <= (upper % ( prime_pre ) ))) (PreH2 : (upper > 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (PrimeForLucas prime_pre )) (PreH10 : (LucasMachineSafe n_pre m_pre prime_pre )) (PreH11 : (0 <= lower)) (PreH12 : (lower <= upper)) (PreH13 : (upper <= (n_pre + m_pre ))) (PreH14 : ((n_pre + m_pre ) <= 200000)) (PreH15 : (0 <= result)) (PreH16 : (result < prime_pre)) (PreH17 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  TT && emp 
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (2 <= prime_pre) ” 
  &&  “ (prime_pre <= 100000) ” 
  &&  “ (PrimeForLucas prime_pre ) ” 
  &&  “ (LucasMachineSafe n_pre m_pre prime_pre ) ” 
  &&  “ (0 < upper) ” 
  &&  “ (0 <= lower) ” 
  &&  “ (lower <= upper) ” 
  &&  “ (upper <= (n_pre + m_pre )) ” 
  &&  “ ((n_pre + m_pre ) <= 200000) ” 
  &&  “ ((upper % ( prime_pre ) ) = (upper % ( prime_pre ) )) ” 
  &&  “ ((lower % ( prime_pre ) ) = (lower % ( prime_pre ) )) ” 
  &&  “ (0 <= (lower % ( prime_pre ) )) ” 
  &&  “ ((lower % ( prime_pre ) ) <= (upper % ( prime_pre ) )) ” 
  &&  “ ((upper % ( prime_pre ) ) < prime_pre) ” 
  &&  “ (0 <= result) ” 
  &&  “ (result < prime_pre) ” 
  &&  “ (DigitBinomialMachineSafe (upper % ( prime_pre ) ) (lower % ( prime_pre ) ) prime_pre ) ” 
  &&  “ (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result ) ”
  &&  emp
) \/
(
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (result: Z) (upper: Z) (lower: Z) (PreH1 : ((lower % ( prime_pre ) ) <= (upper % ( prime_pre ) ))) (PreH2 : (upper > 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (PrimeForLucas prime_pre )) (PreH10 : (LucasMachineSafe n_pre m_pre prime_pre )) (PreH11 : (0 <= lower)) (PreH12 : (lower <= upper)) (PreH13 : (upper <= (n_pre + m_pre ))) (PreH14 : ((n_pre + m_pre ) <= 200000)) (PreH15 : (0 <= result)) (PreH16 : (result < prime_pre)) (PreH17 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  TT && emp 
|--
  “ (DigitBinomialMachineSafe (upper % ( prime_pre ) ) (lower % ( prime_pre ) ) prime_pre ) ” 
  &&  “ ((upper % ( prime_pre ) ) < prime_pre) ” 
  &&  “ (0 <= (lower % ( prime_pre ) )) ”
  &&  emp
).

Definition lucas_theorem_entail_wit_2_split_goal_1 := 
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (result: Z) (upper: Z) (lower: Z) (PreH1 : ((lower % ( prime_pre ) ) <= (upper % ( prime_pre ) ))) (PreH2 : (upper > 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (PrimeForLucas prime_pre )) (PreH10 : (LucasMachineSafe n_pre m_pre prime_pre )) (PreH11 : (0 <= lower)) (PreH12 : (lower <= upper)) (PreH13 : (upper <= (n_pre + m_pre ))) (PreH14 : ((n_pre + m_pre ) <= 200000)) (PreH15 : (0 <= result)) (PreH16 : (result < prime_pre)) (PreH17 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  (DigitBinomialMachineSafe (upper % ( prime_pre ) ) (lower % ( prime_pre ) ) prime_pre )
.

Definition lucas_theorem_entail_wit_2_split_goal_2 := 
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (result: Z) (upper: Z) (lower: Z) (PreH1 : ((lower % ( prime_pre ) ) <= (upper % ( prime_pre ) ))) (PreH2 : (upper > 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (PrimeForLucas prime_pre )) (PreH10 : (LucasMachineSafe n_pre m_pre prime_pre )) (PreH11 : (0 <= lower)) (PreH12 : (lower <= upper)) (PreH13 : (upper <= (n_pre + m_pre ))) (PreH14 : ((n_pre + m_pre ) <= 200000)) (PreH15 : (0 <= result)) (PreH16 : (result < prime_pre)) (PreH17 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  ((upper % ( prime_pre ) ) < prime_pre)
.

Definition lucas_theorem_entail_wit_2_split_goal_3 := 
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (result: Z) (upper: Z) (lower: Z) (PreH1 : ((lower % ( prime_pre ) ) <= (upper % ( prime_pre ) ))) (PreH2 : (upper > 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (PrimeForLucas prime_pre )) (PreH10 : (LucasMachineSafe n_pre m_pre prime_pre )) (PreH11 : (0 <= lower)) (PreH12 : (lower <= upper)) (PreH13 : (upper <= (n_pre + m_pre ))) (PreH14 : ((n_pre + m_pre ) <= 200000)) (PreH15 : (0 <= result)) (PreH16 : (result < prime_pre)) (PreH17 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  (0 <= (lower % ( prime_pre ) ))
.

Definition lucas_theorem_entail_wit_3 := 
(
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (upper: Z) (lower: Z) (upper_digit: Z) (lower_digit: Z) (result: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (BinomialDigitResidue upper_digit lower_digit prime_pre retval )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100000)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (PrimeForLucas prime_pre )) (PreH11 : (LucasMachineSafe n_pre m_pre prime_pre )) (PreH12 : (0 < upper)) (PreH13 : (0 <= lower)) (PreH14 : (lower <= upper)) (PreH15 : (upper <= (n_pre + m_pre ))) (PreH16 : ((n_pre + m_pre ) <= 200000)) (PreH17 : (upper_digit = (upper % ( prime_pre ) ))) (PreH18 : (lower_digit = (lower % ( prime_pre ) ))) (PreH19 : (0 <= lower_digit)) (PreH20 : (lower_digit <= upper_digit)) (PreH21 : (upper_digit < prime_pre)) (PreH22 : (0 <= result)) (PreH23 : (result < prime_pre)) (PreH24 : (DigitBinomialMachineSafe upper_digit lower_digit prime_pre )) (PreH25 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  TT && emp 
|--
  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (2 <= prime_pre) ” 
  &&  “ (prime_pre <= 100000) ” 
  &&  “ (PrimeForLucas prime_pre ) ” 
  &&  “ (LucasMachineSafe n_pre m_pre prime_pre ) ” 
  &&  “ (0 <= (lower ÷ prime_pre )) ” 
  &&  “ ((lower ÷ prime_pre ) <= (upper ÷ prime_pre )) ” 
  &&  “ ((upper ÷ prime_pre ) <= (n_pre + m_pre )) ” 
  &&  “ ((n_pre + m_pre ) <= 200000) ” 
  &&  “ (0 <= ((result * retval ) % ( prime_pre ) )) ” 
  &&  “ (((result * retval ) % ( prime_pre ) ) < prime_pre) ” 
  &&  “ (LucasProgress (n_pre + m_pre ) n_pre prime_pre (upper ÷ prime_pre ) (lower ÷ prime_pre ) ((result * retval ) % ( prime_pre ) ) ) ”
  &&  emp
) \/
(
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (upper: Z) (lower: Z) (upper_digit: Z) (lower_digit: Z) (result: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (BinomialDigitResidue upper_digit lower_digit prime_pre retval )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100000)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (PrimeForLucas prime_pre )) (PreH11 : (LucasMachineSafe n_pre m_pre prime_pre )) (PreH12 : (0 < upper)) (PreH13 : (0 <= lower)) (PreH14 : (lower <= upper)) (PreH15 : (upper <= (n_pre + m_pre ))) (PreH16 : ((n_pre + m_pre ) <= 200000)) (PreH17 : (upper_digit = (upper % ( prime_pre ) ))) (PreH18 : (lower_digit = (lower % ( prime_pre ) ))) (PreH19 : (0 <= lower_digit)) (PreH20 : (lower_digit <= upper_digit)) (PreH21 : (upper_digit < prime_pre)) (PreH22 : (0 <= result)) (PreH23 : (result < prime_pre)) (PreH24 : (DigitBinomialMachineSafe upper_digit lower_digit prime_pre )) (PreH25 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  TT && emp 
|--
  “ (LucasProgress (n_pre + m_pre ) n_pre prime_pre (upper ÷ prime_pre ) (lower ÷ prime_pre ) ((result * retval ) % ( prime_pre ) ) ) ” 
  &&  “ (((result * retval ) % ( prime_pre ) ) < prime_pre) ” 
  &&  “ (0 <= ((result * retval ) % ( prime_pre ) )) ” 
  &&  “ ((upper ÷ prime_pre ) <= (n_pre + m_pre )) ” 
  &&  “ ((lower ÷ prime_pre ) <= (upper ÷ prime_pre )) ” 
  &&  “ (0 <= (lower ÷ prime_pre )) ”
  &&  emp
).

Definition lucas_theorem_entail_wit_3_split_goal_1 := 
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (upper: Z) (lower: Z) (upper_digit: Z) (lower_digit: Z) (result: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (BinomialDigitResidue upper_digit lower_digit prime_pre retval )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100000)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (PrimeForLucas prime_pre )) (PreH11 : (LucasMachineSafe n_pre m_pre prime_pre )) (PreH12 : (0 < upper)) (PreH13 : (0 <= lower)) (PreH14 : (lower <= upper)) (PreH15 : (upper <= (n_pre + m_pre ))) (PreH16 : ((n_pre + m_pre ) <= 200000)) (PreH17 : (upper_digit = (upper % ( prime_pre ) ))) (PreH18 : (lower_digit = (lower % ( prime_pre ) ))) (PreH19 : (0 <= lower_digit)) (PreH20 : (lower_digit <= upper_digit)) (PreH21 : (upper_digit < prime_pre)) (PreH22 : (0 <= result)) (PreH23 : (result < prime_pre)) (PreH24 : (DigitBinomialMachineSafe upper_digit lower_digit prime_pre )) (PreH25 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  (LucasProgress (n_pre + m_pre ) n_pre prime_pre (upper ÷ prime_pre ) (lower ÷ prime_pre ) ((result * retval ) % ( prime_pre ) ) )
.

Definition lucas_theorem_entail_wit_3_split_goal_2 := 
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (upper: Z) (lower: Z) (upper_digit: Z) (lower_digit: Z) (result: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (BinomialDigitResidue upper_digit lower_digit prime_pre retval )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100000)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (PrimeForLucas prime_pre )) (PreH11 : (LucasMachineSafe n_pre m_pre prime_pre )) (PreH12 : (0 < upper)) (PreH13 : (0 <= lower)) (PreH14 : (lower <= upper)) (PreH15 : (upper <= (n_pre + m_pre ))) (PreH16 : ((n_pre + m_pre ) <= 200000)) (PreH17 : (upper_digit = (upper % ( prime_pre ) ))) (PreH18 : (lower_digit = (lower % ( prime_pre ) ))) (PreH19 : (0 <= lower_digit)) (PreH20 : (lower_digit <= upper_digit)) (PreH21 : (upper_digit < prime_pre)) (PreH22 : (0 <= result)) (PreH23 : (result < prime_pre)) (PreH24 : (DigitBinomialMachineSafe upper_digit lower_digit prime_pre )) (PreH25 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  (((result * retval ) % ( prime_pre ) ) < prime_pre)
.

Definition lucas_theorem_entail_wit_3_split_goal_3 := 
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (upper: Z) (lower: Z) (upper_digit: Z) (lower_digit: Z) (result: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (BinomialDigitResidue upper_digit lower_digit prime_pre retval )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100000)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (PrimeForLucas prime_pre )) (PreH11 : (LucasMachineSafe n_pre m_pre prime_pre )) (PreH12 : (0 < upper)) (PreH13 : (0 <= lower)) (PreH14 : (lower <= upper)) (PreH15 : (upper <= (n_pre + m_pre ))) (PreH16 : ((n_pre + m_pre ) <= 200000)) (PreH17 : (upper_digit = (upper % ( prime_pre ) ))) (PreH18 : (lower_digit = (lower % ( prime_pre ) ))) (PreH19 : (0 <= lower_digit)) (PreH20 : (lower_digit <= upper_digit)) (PreH21 : (upper_digit < prime_pre)) (PreH22 : (0 <= result)) (PreH23 : (result < prime_pre)) (PreH24 : (DigitBinomialMachineSafe upper_digit lower_digit prime_pre )) (PreH25 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  (0 <= ((result * retval ) % ( prime_pre ) ))
.

Definition lucas_theorem_entail_wit_3_split_goal_4 := 
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (upper: Z) (lower: Z) (upper_digit: Z) (lower_digit: Z) (result: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (BinomialDigitResidue upper_digit lower_digit prime_pre retval )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100000)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (PrimeForLucas prime_pre )) (PreH11 : (LucasMachineSafe n_pre m_pre prime_pre )) (PreH12 : (0 < upper)) (PreH13 : (0 <= lower)) (PreH14 : (lower <= upper)) (PreH15 : (upper <= (n_pre + m_pre ))) (PreH16 : ((n_pre + m_pre ) <= 200000)) (PreH17 : (upper_digit = (upper % ( prime_pre ) ))) (PreH18 : (lower_digit = (lower % ( prime_pre ) ))) (PreH19 : (0 <= lower_digit)) (PreH20 : (lower_digit <= upper_digit)) (PreH21 : (upper_digit < prime_pre)) (PreH22 : (0 <= result)) (PreH23 : (result < prime_pre)) (PreH24 : (DigitBinomialMachineSafe upper_digit lower_digit prime_pre )) (PreH25 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  ((upper ÷ prime_pre ) <= (n_pre + m_pre ))
.

Definition lucas_theorem_entail_wit_3_split_goal_5 := 
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (upper: Z) (lower: Z) (upper_digit: Z) (lower_digit: Z) (result: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (BinomialDigitResidue upper_digit lower_digit prime_pre retval )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100000)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (PrimeForLucas prime_pre )) (PreH11 : (LucasMachineSafe n_pre m_pre prime_pre )) (PreH12 : (0 < upper)) (PreH13 : (0 <= lower)) (PreH14 : (lower <= upper)) (PreH15 : (upper <= (n_pre + m_pre ))) (PreH16 : ((n_pre + m_pre ) <= 200000)) (PreH17 : (upper_digit = (upper % ( prime_pre ) ))) (PreH18 : (lower_digit = (lower % ( prime_pre ) ))) (PreH19 : (0 <= lower_digit)) (PreH20 : (lower_digit <= upper_digit)) (PreH21 : (upper_digit < prime_pre)) (PreH22 : (0 <= result)) (PreH23 : (result < prime_pre)) (PreH24 : (DigitBinomialMachineSafe upper_digit lower_digit prime_pre )) (PreH25 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  ((lower ÷ prime_pre ) <= (upper ÷ prime_pre ))
.

Definition lucas_theorem_entail_wit_3_split_goal_6 := 
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (upper: Z) (lower: Z) (upper_digit: Z) (lower_digit: Z) (result: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < prime_pre)) (PreH3 : (BinomialDigitResidue upper_digit lower_digit prime_pre retval )) (PreH4 : (1 <= n_pre)) (PreH5 : (n_pre <= 100000)) (PreH6 : (1 <= m_pre)) (PreH7 : (m_pre <= 100000)) (PreH8 : (2 <= prime_pre)) (PreH9 : (prime_pre <= 100000)) (PreH10 : (PrimeForLucas prime_pre )) (PreH11 : (LucasMachineSafe n_pre m_pre prime_pre )) (PreH12 : (0 < upper)) (PreH13 : (0 <= lower)) (PreH14 : (lower <= upper)) (PreH15 : (upper <= (n_pre + m_pre ))) (PreH16 : ((n_pre + m_pre ) <= 200000)) (PreH17 : (upper_digit = (upper % ( prime_pre ) ))) (PreH18 : (lower_digit = (lower % ( prime_pre ) ))) (PreH19 : (0 <= lower_digit)) (PreH20 : (lower_digit <= upper_digit)) (PreH21 : (upper_digit < prime_pre)) (PreH22 : (0 <= result)) (PreH23 : (result < prime_pre)) (PreH24 : (DigitBinomialMachineSafe upper_digit lower_digit prime_pre )) (PreH25 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  (0 <= (lower ÷ prime_pre ))
.

Definition lucas_theorem_return_wit_1 := 
(
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (result: Z) (upper: Z) (lower: Z) (PreH1 : (lower <= 0)) (PreH2 : (upper <= 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (PrimeForLucas prime_pre )) (PreH10 : (LucasMachineSafe n_pre m_pre prime_pre )) (PreH11 : (0 <= lower)) (PreH12 : (lower <= upper)) (PreH13 : (upper <= (n_pre + m_pre ))) (PreH14 : ((n_pre + m_pre ) <= 200000)) (PreH15 : (0 <= result)) (PreH16 : (result < prime_pre)) (PreH17 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  TT && emp 
|--
  “ (0 <= result) ” 
  &&  “ (result < prime_pre) ” 
  &&  “ (LucasBinomialResidue n_pre m_pre prime_pre result ) ”
  &&  emp
) \/
(
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (result: Z) (upper: Z) (lower: Z) (PreH1 : (lower <= 0)) (PreH2 : (upper <= 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (PrimeForLucas prime_pre )) (PreH10 : (LucasMachineSafe n_pre m_pre prime_pre )) (PreH11 : (0 <= lower)) (PreH12 : (lower <= upper)) (PreH13 : (upper <= (n_pre + m_pre ))) (PreH14 : ((n_pre + m_pre ) <= 200000)) (PreH15 : (0 <= result)) (PreH16 : (result < prime_pre)) (PreH17 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  TT && emp 
|--
  “ (LucasBinomialResidue n_pre m_pre prime_pre result ) ”
  &&  emp
).

Definition lucas_theorem_return_wit_1_split_goal_1 := 
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (result: Z) (upper: Z) (lower: Z) (PreH1 : (lower <= 0)) (PreH2 : (upper <= 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (PrimeForLucas prime_pre )) (PreH10 : (LucasMachineSafe n_pre m_pre prime_pre )) (PreH11 : (0 <= lower)) (PreH12 : (lower <= upper)) (PreH13 : (upper <= (n_pre + m_pre ))) (PreH14 : ((n_pre + m_pre ) <= 200000)) (PreH15 : (0 <= result)) (PreH16 : (result < prime_pre)) (PreH17 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  (LucasBinomialResidue n_pre m_pre prime_pre result )
.

Definition lucas_theorem_return_wit_2 := 
(
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (result: Z) (upper: Z) (lower: Z) (PreH1 : ((lower % ( prime_pre ) ) > (upper % ( prime_pre ) ))) (PreH2 : (upper > 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (PrimeForLucas prime_pre )) (PreH10 : (LucasMachineSafe n_pre m_pre prime_pre )) (PreH11 : (0 <= lower)) (PreH12 : (lower <= upper)) (PreH13 : (upper <= (n_pre + m_pre ))) (PreH14 : ((n_pre + m_pre ) <= 200000)) (PreH15 : (0 <= result)) (PreH16 : (result < prime_pre)) (PreH17 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  TT && emp 
|--
  “ (0 <= 0) ” 
  &&  “ (0 < prime_pre) ” 
  &&  “ (LucasBinomialResidue n_pre m_pre prime_pre 0 ) ”
  &&  emp
) \/
(
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (result: Z) (upper: Z) (lower: Z) (PreH1 : ((lower % ( prime_pre ) ) > (upper % ( prime_pre ) ))) (PreH2 : (upper > 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (PrimeForLucas prime_pre )) (PreH10 : (LucasMachineSafe n_pre m_pre prime_pre )) (PreH11 : (0 <= lower)) (PreH12 : (lower <= upper)) (PreH13 : (upper <= (n_pre + m_pre ))) (PreH14 : ((n_pre + m_pre ) <= 200000)) (PreH15 : (0 <= result)) (PreH16 : (result < prime_pre)) (PreH17 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  TT && emp 
|--
  “ (LucasBinomialResidue n_pre m_pre prime_pre 0 ) ”
  &&  emp
).

Definition lucas_theorem_return_wit_2_split_goal_1 := 
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (result: Z) (upper: Z) (lower: Z) (PreH1 : ((lower % ( prime_pre ) ) > (upper % ( prime_pre ) ))) (PreH2 : (upper > 0)) (PreH3 : (1 <= n_pre)) (PreH4 : (n_pre <= 100000)) (PreH5 : (1 <= m_pre)) (PreH6 : (m_pre <= 100000)) (PreH7 : (2 <= prime_pre)) (PreH8 : (prime_pre <= 100000)) (PreH9 : (PrimeForLucas prime_pre )) (PreH10 : (LucasMachineSafe n_pre m_pre prime_pre )) (PreH11 : (0 <= lower)) (PreH12 : (lower <= upper)) (PreH13 : (upper <= (n_pre + m_pre ))) (PreH14 : ((n_pre + m_pre ) <= 200000)) (PreH15 : (0 <= result)) (PreH16 : (result < prime_pre)) (PreH17 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  (LucasBinomialResidue n_pre m_pre prime_pre 0 )
.

Definition lucas_theorem_partial_solve_wit_1_pure := 
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (upper: Z) (lower: Z) (upper_digit: Z) (lower_digit: Z) (result: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (PrimeForLucas prime_pre )) (PreH8 : (LucasMachineSafe n_pre m_pre prime_pre )) (PreH9 : (0 < upper)) (PreH10 : (0 <= lower)) (PreH11 : (lower <= upper)) (PreH12 : (upper <= (n_pre + m_pre ))) (PreH13 : ((n_pre + m_pre ) <= 200000)) (PreH14 : (upper_digit = (upper % ( prime_pre ) ))) (PreH15 : (lower_digit = (lower % ( prime_pre ) ))) (PreH16 : (0 <= lower_digit)) (PreH17 : (lower_digit <= upper_digit)) (PreH18 : (upper_digit < prime_pre)) (PreH19 : (0 <= result)) (PreH20 : (result < prime_pre)) (PreH21 : (DigitBinomialMachineSafe upper_digit lower_digit prime_pre )) (PreH22 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  ((( &( "digit_binomial" ) )) # Int  |->_)
  **  ((( &( "n" ) )) # Int  |-> n_pre)
  **  ((( &( "m" ) )) # Int  |-> m_pre)
  **  ((( &( "prime" ) )) # Int  |-> prime_pre)
  **  ((( &( "upper" ) )) # Int  |-> upper)
  **  ((( &( "lower" ) )) # Int  |-> lower)
  **  ((( &( "upper_digit" ) )) # Int  |-> upper_digit)
  **  ((( &( "lower_digit" ) )) # Int  |-> lower_digit)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ (PrimeForLucas prime_pre ) ” 
  &&  “ (0 <= lower_digit) ” 
  &&  “ (lower_digit <= upper_digit) ” 
  &&  “ (upper_digit < prime_pre) ” 
  &&  “ (2 <= prime_pre) ” 
  &&  “ (prime_pre <= 100000) ” 
  &&  “ (DigitBinomialMachineSafe upper_digit lower_digit prime_pre ) ”
.

Definition lucas_theorem_partial_solve_wit_1_aux := 
forall (prime_pre: Z) (m_pre: Z) (n_pre: Z) (upper: Z) (lower: Z) (upper_digit: Z) (lower_digit: Z) (result: Z) (PreH1 : (1 <= n_pre)) (PreH2 : (n_pre <= 100000)) (PreH3 : (1 <= m_pre)) (PreH4 : (m_pre <= 100000)) (PreH5 : (2 <= prime_pre)) (PreH6 : (prime_pre <= 100000)) (PreH7 : (PrimeForLucas prime_pre )) (PreH8 : (LucasMachineSafe n_pre m_pre prime_pre )) (PreH9 : (0 < upper)) (PreH10 : (0 <= lower)) (PreH11 : (lower <= upper)) (PreH12 : (upper <= (n_pre + m_pre ))) (PreH13 : ((n_pre + m_pre ) <= 200000)) (PreH14 : (upper_digit = (upper % ( prime_pre ) ))) (PreH15 : (lower_digit = (lower % ( prime_pre ) ))) (PreH16 : (0 <= lower_digit)) (PreH17 : (lower_digit <= upper_digit)) (PreH18 : (upper_digit < prime_pre)) (PreH19 : (0 <= result)) (PreH20 : (result < prime_pre)) (PreH21 : (DigitBinomialMachineSafe upper_digit lower_digit prime_pre )) (PreH22 : (LucasProgress (n_pre + m_pre ) n_pre prime_pre upper lower result )) ,
  TT && emp 
|--
  “ (PrimeForLucas prime_pre ) ” 
  &&  “ (0 <= lower_digit) ” 
  &&  “ (lower_digit <= upper_digit) ” 
  &&  “ (upper_digit < prime_pre) ” 
  &&  “ (2 <= prime_pre) ” 
  &&  “ (prime_pre <= 100000) ” 
  &&  “ (DigitBinomialMachineSafe upper_digit lower_digit prime_pre ) ” 
  &&  “ (1 <= n_pre) ” 
  &&  “ (n_pre <= 100000) ” 
  &&  “ (1 <= m_pre) ” 
  &&  “ (m_pre <= 100000) ” 
  &&  “ (2 <= prime_pre) ” 
  &&  “ (prime_pre <= 100000) ” 
  &&  “ (PrimeForLucas prime_pre ) ” 
  &&  “ (LucasMachineSafe n_pre m_pre prime_pre ) ” 
  &&  “ (0 < upper) ” 
  &&  “ (0 <= lower) ” 
  &&  “ (lower <= upper) ” 
  &&  “ (upper <= (n_pre + m_pre )) ” 
  &&  “ ((n_pre + m_pre ) <= 200000) ” 
  &&  “ (upper_digit = (upper % ( prime_pre ) )) ” 
  &&  “ (lower_digit = (lower % ( prime_pre ) )) ” 
  &&  “ (0 <= lower_digit) ” 
  &&  “ (lower_digit <= upper_digit) ” 
  &&  “ (upper_digit < prime_pre) ” 
  &&  “ (0 <= result) ” 
  &&  “ (result < prime_pre) ” 
  &&  “ (DigitBinomialMachineSafe upper_digit lower_digit prime_pre ) ” 
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
Axiom proof_of_binomial_digit_mod_prime_safety_wit_21 : binomial_digit_mod_prime_safety_wit_21.
Axiom proof_of_binomial_digit_mod_prime_safety_wit_22 : binomial_digit_mod_prime_safety_wit_22.
Axiom proof_of_binomial_digit_mod_prime_safety_wit_23 : binomial_digit_mod_prime_safety_wit_23.
Axiom proof_of_binomial_digit_mod_prime_safety_wit_24 : binomial_digit_mod_prime_safety_wit_24.
Axiom proof_of_binomial_digit_mod_prime_safety_wit_25 : binomial_digit_mod_prime_safety_wit_25.
Axiom proof_of_binomial_digit_mod_prime_safety_wit_26 : binomial_digit_mod_prime_safety_wit_26.
Axiom proof_of_binomial_digit_mod_prime_safety_wit_27 : binomial_digit_mod_prime_safety_wit_27.
Axiom proof_of_binomial_digit_mod_prime_safety_wit_28 : binomial_digit_mod_prime_safety_wit_28.
Axiom proof_of_binomial_digit_mod_prime_safety_wit_29 : binomial_digit_mod_prime_safety_wit_29.
Axiom proof_of_binomial_digit_mod_prime_safety_wit_30 : binomial_digit_mod_prime_safety_wit_30.
Axiom proof_of_binomial_digit_mod_prime_safety_wit_31 : binomial_digit_mod_prime_safety_wit_31.
Axiom proof_of_binomial_digit_mod_prime_entail_wit_1_1 : binomial_digit_mod_prime_entail_wit_1_1.
Axiom proof_of_binomial_digit_mod_prime_entail_wit_1_2 : binomial_digit_mod_prime_entail_wit_1_2.
Axiom proof_of_binomial_digit_mod_prime_entail_wit_2_1 : binomial_digit_mod_prime_entail_wit_2_1.
Axiom proof_of_binomial_digit_mod_prime_entail_wit_2_2 : binomial_digit_mod_prime_entail_wit_2_2.
Axiom proof_of_binomial_digit_mod_prime_entail_wit_3_1 : binomial_digit_mod_prime_entail_wit_3_1.
Axiom proof_of_binomial_digit_mod_prime_entail_wit_3_2 : binomial_digit_mod_prime_entail_wit_3_2.
Axiom proof_of_binomial_digit_mod_prime_return_wit_1 : binomial_digit_mod_prime_return_wit_1.
Axiom proof_of_binomial_digit_mod_prime_return_wit_2 : binomial_digit_mod_prime_return_wit_2.
Axiom proof_of_binomial_digit_mod_prime_partial_solve_wit_1_pure : binomial_digit_mod_prime_partial_solve_wit_1_pure.
Axiom proof_of_binomial_digit_mod_prime_partial_solve_wit_1 : binomial_digit_mod_prime_partial_solve_wit_1.
Axiom proof_of_binomial_digit_mod_prime_partial_solve_wit_2_pure : binomial_digit_mod_prime_partial_solve_wit_2_pure.
Axiom proof_of_binomial_digit_mod_prime_partial_solve_wit_2 : binomial_digit_mod_prime_partial_solve_wit_2.
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
Axiom proof_of_lucas_theorem_entail_wit_3 : lucas_theorem_entail_wit_3.
Axiom proof_of_lucas_theorem_return_wit_1 : lucas_theorem_return_wit_1.
Axiom proof_of_lucas_theorem_return_wit_2 : lucas_theorem_return_wit_2.
Axiom proof_of_lucas_theorem_partial_solve_wit_1_pure : lucas_theorem_partial_solve_wit_1_pure.
Axiom proof_of_lucas_theorem_partial_solve_wit_1 : lucas_theorem_partial_solve_wit_1.

End VC_Correct.
