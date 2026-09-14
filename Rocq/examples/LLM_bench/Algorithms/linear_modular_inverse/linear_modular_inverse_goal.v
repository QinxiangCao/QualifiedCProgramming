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
Require Import SimpleC.EE.LLM_bench.Algorithms.linear_modular_inverse.linear_modular_inverse_lib.
Local Open Scope sac.

(*----- Function linear_modular_inverse -----*)

Definition linear_modular_inverse_safety_wit_1 := 
forall (inverse_pre: Z) (p_pre: Z) (PreH1 : (PrimeForLinearInverse p_pre )) (PreH2 : (2 <= p_pre)) (PreH3 : (p_pre <= 46340)) ,
  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "inverse" ) )) # Ptr  |-> inverse_pre)
  **  (IntArray.undef_seg inverse_pre 1 p_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition linear_modular_inverse_safety_wit_2 := 
forall (inverse_pre: Z) (p_pre: Z) (PreH1 : (PrimeForLinearInverse p_pre )) (PreH2 : (2 <= p_pre)) (PreH3 : (p_pre <= 46340)) ,
  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "inverse" ) )) # Ptr  |-> inverse_pre)
  **  (IntArray.undef_seg inverse_pre 1 p_pre )
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition linear_modular_inverse_safety_wit_3 := 
forall (inverse_pre: Z) (p_pre: Z) (PreH1 : (PrimeForLinearInverse p_pre )) (PreH2 : (2 <= p_pre)) (PreH3 : (p_pre <= 46340)) ,
  ((( &( "i" ) )) # Int  |->_)
  **  (((inverse_pre + (1 * sizeof(INT)))) # Int  |-> 1)
  **  (IntArray.undef_seg inverse_pre (1 + 1 ) p_pre )
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "inverse" ) )) # Ptr  |-> inverse_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition linear_modular_inverse_safety_wit_4 := 
forall (inverse_pre: Z) (p_pre: Z) (values: (@list Z)) (i: Z) (PreH1 : (i < p_pre)) (PreH2 : (PrimeForLinearInverse p_pre )) (PreH3 : (2 <= p_pre)) (PreH4 : (p_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= p_pre)) (PreH7 : (ModularInversePrefix p_pre i values )) ,
  ((( &( "quotient" ) )) # Int  |->_)
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "inverse" ) )) # Ptr  |-> inverse_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg inverse_pre 1 i values )
  **  (IntArray.undef_seg inverse_pre i p_pre )
|--
  “ ((p_pre <> (INT_MIN)) \/ (i <> (-1))) ” 
  &&  “ (i <> 0) ”
.

Definition linear_modular_inverse_safety_wit_5 := 
forall (inverse_pre: Z) (p_pre: Z) (values: (@list Z)) (i: Z) (PreH1 : (i < p_pre)) (PreH2 : (PrimeForLinearInverse p_pre )) (PreH3 : (2 <= p_pre)) (PreH4 : (p_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= p_pre)) (PreH7 : (ModularInversePrefix p_pre i values )) ,
  ((( &( "remainder" ) )) # Int  |->_)
  **  ((( &( "quotient" ) )) # Int  |-> (p_pre ÷ i ))
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "inverse" ) )) # Ptr  |-> inverse_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  (IntArray.seg inverse_pre 1 i values )
  **  (IntArray.undef_seg inverse_pre i p_pre )
|--
  “ ((p_pre <> (INT_MIN)) \/ (i <> (-1))) ” 
  &&  “ (i <> 0) ”
.

Definition linear_modular_inverse_safety_wit_6 := 
forall (inverse_pre: Z) (p_pre: Z) (values: (@list Z)) (i: Z) (quotient: Z) (remainder: Z) (PreH1 : (PrimeForLinearInverse p_pre )) (PreH2 : (2 <= p_pre)) (PreH3 : (p_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i < p_pre)) (PreH6 : (quotient = (p_pre ÷ i ))) (PreH7 : (remainder = (p_pre % ( i ) ))) (PreH8 : (p_pre = ((quotient * i ) + remainder ))) (PreH9 : (1 <= quotient)) (PreH10 : (1 <= remainder)) (PreH11 : (remainder < i)) (PreH12 : (0 < (p_pre - quotient ))) (PreH13 : ((p_pre - quotient ) < p_pre)) (PreH14 : (0 < (Znth (remainder - 1 ) values 0))) (PreH15 : ((Znth (remainder - 1 ) values 0) < p_pre)) (PreH16 : (0 < ((p_pre - quotient ) * (Znth (remainder - 1 ) values 0) ))) (PreH17 : (((p_pre - quotient ) * (Znth (remainder - 1 ) values 0) ) <= INT_MAX)) (PreH18 : (ModularInversePrefix p_pre i values )) ,
  (IntArray.seg inverse_pre 1 i values )
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "inverse" ) )) # Ptr  |-> inverse_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "quotient" ) )) # Int  |-> quotient)
  **  ((( &( "remainder" ) )) # Int  |-> remainder)
  **  (IntArray.undef_seg inverse_pre i p_pre )
|--
  “ ((((p_pre - quotient ) * (Znth (remainder - 1 ) values 0) ) <> (INT_MIN)) \/ (p_pre <> (-1))) ” 
  &&  “ (p_pre <> 0) ”
.

Definition linear_modular_inverse_safety_wit_7 := 
forall (inverse_pre: Z) (p_pre: Z) (values: (@list Z)) (i: Z) (quotient: Z) (remainder: Z) (PreH1 : (PrimeForLinearInverse p_pre )) (PreH2 : (2 <= p_pre)) (PreH3 : (p_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i < p_pre)) (PreH6 : (quotient = (p_pre ÷ i ))) (PreH7 : (remainder = (p_pre % ( i ) ))) (PreH8 : (p_pre = ((quotient * i ) + remainder ))) (PreH9 : (1 <= quotient)) (PreH10 : (1 <= remainder)) (PreH11 : (remainder < i)) (PreH12 : (0 < (p_pre - quotient ))) (PreH13 : ((p_pre - quotient ) < p_pre)) (PreH14 : (0 < (Znth (remainder - 1 ) values 0))) (PreH15 : ((Znth (remainder - 1 ) values 0) < p_pre)) (PreH16 : (0 < ((p_pre - quotient ) * (Znth (remainder - 1 ) values 0) ))) (PreH17 : (((p_pre - quotient ) * (Znth (remainder - 1 ) values 0) ) <= INT_MAX)) (PreH18 : (ModularInversePrefix p_pre i values )) ,
  (IntArray.seg inverse_pre 1 i values )
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "inverse" ) )) # Ptr  |-> inverse_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "quotient" ) )) # Int  |-> quotient)
  **  ((( &( "remainder" ) )) # Int  |-> remainder)
  **  (IntArray.undef_seg inverse_pre i p_pre )
|--
  “ (((p_pre - quotient ) * (Znth (remainder - 1 ) values 0) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((p_pre - quotient ) * (Znth (remainder - 1 ) values 0) )) ”
.

Definition linear_modular_inverse_safety_wit_8 := 
forall (inverse_pre: Z) (p_pre: Z) (values: (@list Z)) (i: Z) (quotient: Z) (remainder: Z) (PreH1 : (PrimeForLinearInverse p_pre )) (PreH2 : (2 <= p_pre)) (PreH3 : (p_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i < p_pre)) (PreH6 : (quotient = (p_pre ÷ i ))) (PreH7 : (remainder = (p_pre % ( i ) ))) (PreH8 : (p_pre = ((quotient * i ) + remainder ))) (PreH9 : (1 <= quotient)) (PreH10 : (1 <= remainder)) (PreH11 : (remainder < i)) (PreH12 : (0 < (p_pre - quotient ))) (PreH13 : ((p_pre - quotient ) < p_pre)) (PreH14 : (0 < (Znth (remainder - 1 ) values 0))) (PreH15 : ((Znth (remainder - 1 ) values 0) < p_pre)) (PreH16 : (0 < ((p_pre - quotient ) * (Znth (remainder - 1 ) values 0) ))) (PreH17 : (((p_pre - quotient ) * (Znth (remainder - 1 ) values 0) ) <= INT_MAX)) (PreH18 : (ModularInversePrefix p_pre i values )) ,
  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "inverse" ) )) # Ptr  |-> inverse_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
  **  ((( &( "quotient" ) )) # Int  |-> quotient)
  **  ((( &( "remainder" ) )) # Int  |-> remainder)
  **  (IntArray.seg inverse_pre 1 i values )
  **  (IntArray.undef_seg inverse_pre i p_pre )
|--
  “ ((p_pre - quotient ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (p_pre - quotient )) ”
.

Definition linear_modular_inverse_safety_wit_9 := 
forall (inverse_pre: Z) (p_pre: Z) (values: (@list Z)) (i: Z) (quotient: Z) (remainder: Z) (PreH1 : (PrimeForLinearInverse p_pre )) (PreH2 : (2 <= p_pre)) (PreH3 : (p_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i < p_pre)) (PreH6 : (quotient = (p_pre ÷ i ))) (PreH7 : (remainder = (p_pre % ( i ) ))) (PreH8 : (p_pre = ((quotient * i ) + remainder ))) (PreH9 : (1 <= quotient)) (PreH10 : (1 <= remainder)) (PreH11 : (remainder < i)) (PreH12 : (0 < (p_pre - quotient ))) (PreH13 : ((p_pre - quotient ) < p_pre)) (PreH14 : (0 < (Znth (remainder - 1 ) values 0))) (PreH15 : ((Znth (remainder - 1 ) values 0) < p_pre)) (PreH16 : (0 < ((p_pre - quotient ) * (Znth (remainder - 1 ) values 0) ))) (PreH17 : (((p_pre - quotient ) * (Znth (remainder - 1 ) values 0) ) <= INT_MAX)) (PreH18 : (ModularInversePrefix p_pre i values )) ,
  (IntArray.seg inverse_pre 1 (i + 1 ) (app (values) ((cons ((((p_pre - quotient ) * (Znth (remainder - 1 ) values 0) ) % ( p_pre ) )) ((@nil Z))))) )
  **  (IntArray.undef_seg inverse_pre (i + 1 ) p_pre )
  **  ((( &( "p" ) )) # Int  |-> p_pre)
  **  ((( &( "inverse" ) )) # Ptr  |-> inverse_pre)
  **  ((( &( "i" ) )) # Int  |-> i)
|--
  “ ((i + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (i + 1 )) ”
.

Definition linear_modular_inverse_entail_wit_1 := 
(
forall (inverse_pre: Z) (p_pre: Z) (PreH1 : (PrimeForLinearInverse p_pre )) (PreH2 : (2 <= p_pre)) (PreH3 : (p_pre <= 46340)) ,
  (((inverse_pre + (1 * sizeof(INT)))) # Int  |-> 1)
  **  (IntArray.undef_seg inverse_pre (1 + 1 ) p_pre )
|--
  EX (values: (@list Z)) ,
  “ (PrimeForLinearInverse p_pre ) ” 
  &&  “ (2 <= p_pre) ” 
  &&  “ (p_pre <= 46340) ” 
  &&  “ (2 <= 2) ” 
  &&  “ (2 <= p_pre) ” 
  &&  “ (ModularInversePrefix p_pre 2 values ) ”
  &&  (IntArray.seg inverse_pre 1 2 values )
  **  (IntArray.undef_seg inverse_pre 2 p_pre )
) \/
(
forall (inverse_pre: Z) (p_pre: Z) (PreH1 : (1 <= INT_MAX)) (PreH2 : (1 >= INT_MIN)) (PreH3 : (PrimeForLinearInverse p_pre )) (PreH4 : (2 <= p_pre)) (PreH5 : (p_pre <= 46340)) ,
  (((inverse_pre + (1 * sizeof(INT)))) # Int  |-> 1)
|--
  EX (values: (@list Z)) ,
  “ (PrimeForLinearInverse p_pre ) ” 
  &&  “ (2 <= p_pre) ” 
  &&  “ (p_pre <= 46340) ” 
  &&  “ (2 <= 2) ” 
  &&  “ (2 <= p_pre) ” 
  &&  “ (ModularInversePrefix p_pre 2 values ) ”
  &&  (IntArray.seg inverse_pre 1 2 values )
).

Definition linear_modular_inverse_entail_wit_2 := 
(
forall (inverse_pre: Z) (p_pre: Z) (values_2: (@list Z)) (i: Z) (PreH1 : (i < p_pre)) (PreH2 : (PrimeForLinearInverse p_pre )) (PreH3 : (2 <= p_pre)) (PreH4 : (p_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= p_pre)) (PreH7 : (ModularInversePrefix p_pre i values_2 )) ,
  (IntArray.seg inverse_pre 1 i values_2 )
  **  (IntArray.undef_seg inverse_pre i p_pre )
|--
  EX (values: (@list Z)) ,
  “ (PrimeForLinearInverse p_pre ) ” 
  &&  “ (2 <= p_pre) ” 
  &&  “ (p_pre <= 46340) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i < p_pre) ” 
  &&  “ ((p_pre ÷ i ) = (p_pre ÷ i )) ” 
  &&  “ ((p_pre % ( i ) ) = (p_pre % ( i ) )) ” 
  &&  “ (p_pre = (((p_pre ÷ i ) * i ) + (p_pre % ( i ) ) )) ” 
  &&  “ (1 <= (p_pre ÷ i )) ” 
  &&  “ (1 <= (p_pre % ( i ) )) ” 
  &&  “ ((p_pre % ( i ) ) < i) ” 
  &&  “ (0 < (p_pre - (p_pre ÷ i ) )) ” 
  &&  “ ((p_pre - (p_pre ÷ i ) ) < p_pre) ” 
  &&  “ (0 < (Znth ((p_pre % ( i ) ) - 1 ) values 0)) ” 
  &&  “ ((Znth ((p_pre % ( i ) ) - 1 ) values 0) < p_pre) ” 
  &&  “ (0 < ((p_pre - (p_pre ÷ i ) ) * (Znth ((p_pre % ( i ) ) - 1 ) values 0) )) ” 
  &&  “ (((p_pre - (p_pre ÷ i ) ) * (Znth ((p_pre % ( i ) ) - 1 ) values 0) ) <= INT_MAX) ” 
  &&  “ (ModularInversePrefix p_pre i values ) ”
  &&  (IntArray.seg inverse_pre 1 i values )
  **  (IntArray.undef_seg inverse_pre i p_pre )
) \/
(
forall (p_pre: Z) (values_2: (@list Z)) (i: Z) (PreH1 : (i < p_pre)) (PreH2 : (PrimeForLinearInverse p_pre )) (PreH3 : (2 <= p_pre)) (PreH4 : (p_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= p_pre)) (PreH7 : (ModularInversePrefix p_pre i values_2 )) ,
  TT && emp 
|--
  “ (((p_pre - (p_pre ÷ i ) ) * (Znth ((p_pre % ( i ) ) - 1 ) values_2 0) ) <= INT_MAX) ” 
  &&  “ (0 < ((p_pre - (p_pre ÷ i ) ) * (Znth ((p_pre % ( i ) ) - 1 ) values_2 0) )) ” 
  &&  “ ((Znth ((p_pre % ( i ) ) - 1 ) values_2 0) < p_pre) ” 
  &&  “ (0 < (Znth ((p_pre % ( i ) ) - 1 ) values_2 0)) ” 
  &&  “ ((p_pre - (p_pre ÷ i ) ) < p_pre) ” 
  &&  “ (0 < (p_pre - (p_pre ÷ i ) )) ” 
  &&  “ ((p_pre % ( i ) ) < i) ” 
  &&  “ (1 <= (p_pre % ( i ) )) ” 
  &&  “ (1 <= (p_pre ÷ i )) ” 
  &&  “ (p_pre = (((p_pre ÷ i ) * i ) + (p_pre % ( i ) ) )) ”
  &&  emp
).

Definition linear_modular_inverse_entail_wit_2_split_goal_1 := 
forall (p_pre: Z) (values_2: (@list Z)) (i: Z) (PreH1 : (i < p_pre)) (PreH2 : (PrimeForLinearInverse p_pre )) (PreH3 : (2 <= p_pre)) (PreH4 : (p_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= p_pre)) (PreH7 : (ModularInversePrefix p_pre i values_2 )) ,
  (((p_pre - (p_pre ÷ i ) ) * (Znth ((p_pre % ( i ) ) - 1 ) values_2 0) ) <= INT_MAX)
.

Definition linear_modular_inverse_entail_wit_2_split_goal_2 := 
forall (p_pre: Z) (values_2: (@list Z)) (i: Z) (PreH1 : (i < p_pre)) (PreH2 : (PrimeForLinearInverse p_pre )) (PreH3 : (2 <= p_pre)) (PreH4 : (p_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= p_pre)) (PreH7 : (ModularInversePrefix p_pre i values_2 )) ,
  (0 < ((p_pre - (p_pre ÷ i ) ) * (Znth ((p_pre % ( i ) ) - 1 ) values_2 0) ))
.

Definition linear_modular_inverse_entail_wit_2_split_goal_3 := 
forall (p_pre: Z) (values_2: (@list Z)) (i: Z) (PreH1 : (i < p_pre)) (PreH2 : (PrimeForLinearInverse p_pre )) (PreH3 : (2 <= p_pre)) (PreH4 : (p_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= p_pre)) (PreH7 : (ModularInversePrefix p_pre i values_2 )) ,
  ((Znth ((p_pre % ( i ) ) - 1 ) values_2 0) < p_pre)
.

Definition linear_modular_inverse_entail_wit_2_split_goal_4 := 
forall (p_pre: Z) (values_2: (@list Z)) (i: Z) (PreH1 : (i < p_pre)) (PreH2 : (PrimeForLinearInverse p_pre )) (PreH3 : (2 <= p_pre)) (PreH4 : (p_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= p_pre)) (PreH7 : (ModularInversePrefix p_pre i values_2 )) ,
  (0 < (Znth ((p_pre % ( i ) ) - 1 ) values_2 0))
.

Definition linear_modular_inverse_entail_wit_2_split_goal_5 := 
forall (p_pre: Z) (values_2: (@list Z)) (i: Z) (PreH1 : (i < p_pre)) (PreH2 : (PrimeForLinearInverse p_pre )) (PreH3 : (2 <= p_pre)) (PreH4 : (p_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= p_pre)) (PreH7 : (ModularInversePrefix p_pre i values_2 )) ,
  ((p_pre - (p_pre ÷ i ) ) < p_pre)
.

Definition linear_modular_inverse_entail_wit_2_split_goal_6 := 
forall (p_pre: Z) (values_2: (@list Z)) (i: Z) (PreH1 : (i < p_pre)) (PreH2 : (PrimeForLinearInverse p_pre )) (PreH3 : (2 <= p_pre)) (PreH4 : (p_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= p_pre)) (PreH7 : (ModularInversePrefix p_pre i values_2 )) ,
  (0 < (p_pre - (p_pre ÷ i ) ))
.

Definition linear_modular_inverse_entail_wit_2_split_goal_7 := 
forall (p_pre: Z) (values_2: (@list Z)) (i: Z) (PreH1 : (i < p_pre)) (PreH2 : (PrimeForLinearInverse p_pre )) (PreH3 : (2 <= p_pre)) (PreH4 : (p_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= p_pre)) (PreH7 : (ModularInversePrefix p_pre i values_2 )) ,
  ((p_pre % ( i ) ) < i)
.

Definition linear_modular_inverse_entail_wit_2_split_goal_8 := 
forall (p_pre: Z) (values_2: (@list Z)) (i: Z) (PreH1 : (i < p_pre)) (PreH2 : (PrimeForLinearInverse p_pre )) (PreH3 : (2 <= p_pre)) (PreH4 : (p_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= p_pre)) (PreH7 : (ModularInversePrefix p_pre i values_2 )) ,
  (1 <= (p_pre % ( i ) ))
.

Definition linear_modular_inverse_entail_wit_2_split_goal_9 := 
forall (p_pre: Z) (values_2: (@list Z)) (i: Z) (PreH1 : (i < p_pre)) (PreH2 : (PrimeForLinearInverse p_pre )) (PreH3 : (2 <= p_pre)) (PreH4 : (p_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= p_pre)) (PreH7 : (ModularInversePrefix p_pre i values_2 )) ,
  (1 <= (p_pre ÷ i ))
.

Definition linear_modular_inverse_entail_wit_2_split_goal_10 := 
forall (p_pre: Z) (values_2: (@list Z)) (i: Z) (PreH1 : (i < p_pre)) (PreH2 : (PrimeForLinearInverse p_pre )) (PreH3 : (2 <= p_pre)) (PreH4 : (p_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= p_pre)) (PreH7 : (ModularInversePrefix p_pre i values_2 )) ,
  (p_pre = (((p_pre ÷ i ) * i ) + (p_pre % ( i ) ) ))
.

Definition linear_modular_inverse_entail_wit_3 := 
(
forall (inverse_pre: Z) (p_pre: Z) (values_2: (@list Z)) (i: Z) (quotient: Z) (remainder: Z) (PreH1 : (PrimeForLinearInverse p_pre )) (PreH2 : (2 <= p_pre)) (PreH3 : (p_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i < p_pre)) (PreH6 : (quotient = (p_pre ÷ i ))) (PreH7 : (remainder = (p_pre % ( i ) ))) (PreH8 : (p_pre = ((quotient * i ) + remainder ))) (PreH9 : (1 <= quotient)) (PreH10 : (1 <= remainder)) (PreH11 : (remainder < i)) (PreH12 : (0 < (p_pre - quotient ))) (PreH13 : ((p_pre - quotient ) < p_pre)) (PreH14 : (0 < (Znth (remainder - 1 ) values_2 0))) (PreH15 : ((Znth (remainder - 1 ) values_2 0) < p_pre)) (PreH16 : (0 < ((p_pre - quotient ) * (Znth (remainder - 1 ) values_2 0) ))) (PreH17 : (((p_pre - quotient ) * (Znth (remainder - 1 ) values_2 0) ) <= INT_MAX)) (PreH18 : (ModularInversePrefix p_pre i values_2 )) ,
  (IntArray.seg inverse_pre 1 (i + 1 ) (app (values_2) ((cons ((((p_pre - quotient ) * (Znth (remainder - 1 ) values_2 0) ) % ( p_pre ) )) ((@nil Z))))) )
  **  (IntArray.undef_seg inverse_pre (i + 1 ) p_pre )
|--
  EX (values: (@list Z)) ,
  “ (PrimeForLinearInverse p_pre ) ” 
  &&  “ (2 <= p_pre) ” 
  &&  “ (p_pre <= 46340) ” 
  &&  “ (2 <= (i + 1 )) ” 
  &&  “ ((i + 1 ) <= p_pre) ” 
  &&  “ (ModularInversePrefix p_pre (i + 1 ) values ) ”
  &&  (IntArray.seg inverse_pre 1 (i + 1 ) values )
  **  (IntArray.undef_seg inverse_pre (i + 1 ) p_pre )
) \/
(
forall (p_pre: Z) (values_2: (@list Z)) (i: Z) (quotient: Z) (remainder: Z) (PreH1 : (PrimeForLinearInverse p_pre )) (PreH2 : (2 <= p_pre)) (PreH3 : (p_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i < p_pre)) (PreH6 : (quotient = (p_pre ÷ i ))) (PreH7 : (remainder = (p_pre % ( i ) ))) (PreH8 : (p_pre = ((quotient * i ) + remainder ))) (PreH9 : (1 <= quotient)) (PreH10 : (1 <= remainder)) (PreH11 : (remainder < i)) (PreH12 : (0 < (p_pre - quotient ))) (PreH13 : ((p_pre - quotient ) < p_pre)) (PreH14 : (0 < (Znth (remainder - 1 ) values_2 0))) (PreH15 : ((Znth (remainder - 1 ) values_2 0) < p_pre)) (PreH16 : (0 < ((p_pre - quotient ) * (Znth (remainder - 1 ) values_2 0) ))) (PreH17 : (((p_pre - quotient ) * (Znth (remainder - 1 ) values_2 0) ) <= INT_MAX)) (PreH18 : (ModularInversePrefix p_pre i values_2 )) ,
  TT && emp 
|--
  “ (ModularInversePrefix ((quotient * i ) + remainder ) (i + 1 ) (app (values_2) ((cons ((((((quotient * i ) + remainder ) - (((quotient * i ) + remainder ) ÷ i ) ) * (Znth ((((quotient * i ) + remainder ) % ( i ) ) - 1 ) values_2 0) ) % ( ((quotient * i ) + remainder ) ) )) ((@nil Z))))) ) ”
  &&  emp
).

Definition linear_modular_inverse_entail_wit_3_split_goal_1 := 
forall (p_pre: Z) (values_2: (@list Z)) (i: Z) (quotient: Z) (remainder: Z) (PreH1 : (PrimeForLinearInverse p_pre )) (PreH2 : (2 <= p_pre)) (PreH3 : (p_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i < p_pre)) (PreH6 : (quotient = (p_pre ÷ i ))) (PreH7 : (remainder = (p_pre % ( i ) ))) (PreH8 : (p_pre = ((quotient * i ) + remainder ))) (PreH9 : (1 <= quotient)) (PreH10 : (1 <= remainder)) (PreH11 : (remainder < i)) (PreH12 : (0 < (p_pre - quotient ))) (PreH13 : ((p_pre - quotient ) < p_pre)) (PreH14 : (0 < (Znth (remainder - 1 ) values_2 0))) (PreH15 : ((Znth (remainder - 1 ) values_2 0) < p_pre)) (PreH16 : (0 < ((p_pre - quotient ) * (Znth (remainder - 1 ) values_2 0) ))) (PreH17 : (((p_pre - quotient ) * (Znth (remainder - 1 ) values_2 0) ) <= INT_MAX)) (PreH18 : (ModularInversePrefix p_pre i values_2 )) ,
  (ModularInversePrefix ((quotient * i ) + remainder ) (i + 1 ) (app (values_2) ((cons ((((((quotient * i ) + remainder ) - (((quotient * i ) + remainder ) ÷ i ) ) * (Znth ((((quotient * i ) + remainder ) % ( i ) ) - 1 ) values_2 0) ) % ( ((quotient * i ) + remainder ) ) )) ((@nil Z))))) )
.

Definition linear_modular_inverse_return_wit_1 := 
(
forall (inverse_pre: Z) (p_pre: Z) (values_2: (@list Z)) (i: Z) (PreH1 : (i >= p_pre)) (PreH2 : (PrimeForLinearInverse p_pre )) (PreH3 : (2 <= p_pre)) (PreH4 : (p_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= p_pre)) (PreH7 : (ModularInversePrefix p_pre i values_2 )) ,
  (IntArray.seg inverse_pre 1 i values_2 )
  **  (IntArray.undef_seg inverse_pre i p_pre )
|--
  EX (values: (@list Z)) ,
  “ (ModularInversePrefix p_pre p_pre values ) ”
  &&  (IntArray.seg inverse_pre 1 p_pre values )
) \/
(
forall (inverse_pre: Z) (p_pre: Z) (values_2: (@list Z)) (i: Z) (PreH1 : (i >= p_pre)) (PreH2 : (PrimeForLinearInverse p_pre )) (PreH3 : (2 <= p_pre)) (PreH4 : (p_pre <= 46340)) (PreH5 : (2 <= i)) (PreH6 : (i <= p_pre)) (PreH7 : (ModularInversePrefix p_pre i values_2 )) ,
  (IntArray.seg inverse_pre 1 i values_2 )
|--
  EX (values: (@list Z)) ,
  “ (ModularInversePrefix p_pre p_pre values ) ”
  &&  (IntArray.seg inverse_pre 1 p_pre values )
).

Definition linear_modular_inverse_partial_solve_wit_1 := 
forall (inverse_pre: Z) (p_pre: Z) (PreH1 : (PrimeForLinearInverse p_pre )) (PreH2 : (2 <= p_pre)) (PreH3 : (p_pre <= 46340)) ,
  (IntArray.undef_seg inverse_pre 1 p_pre )
|--
  “ (PrimeForLinearInverse p_pre ) ” 
  &&  “ (2 <= p_pre) ” 
  &&  “ (p_pre <= 46340) ”
  &&  (((inverse_pre + (1 * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg inverse_pre (1 + 1 ) p_pre )
.

Definition linear_modular_inverse_partial_solve_wit_2 := 
forall (inverse_pre: Z) (p_pre: Z) (values: (@list Z)) (i: Z) (quotient: Z) (remainder: Z) (PreH1 : (PrimeForLinearInverse p_pre )) (PreH2 : (2 <= p_pre)) (PreH3 : (p_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i < p_pre)) (PreH6 : (quotient = (p_pre ÷ i ))) (PreH7 : (remainder = (p_pre % ( i ) ))) (PreH8 : (p_pre = ((quotient * i ) + remainder ))) (PreH9 : (1 <= quotient)) (PreH10 : (1 <= remainder)) (PreH11 : (remainder < i)) (PreH12 : (0 < (p_pre - quotient ))) (PreH13 : ((p_pre - quotient ) < p_pre)) (PreH14 : (0 < (Znth (remainder - 1 ) values 0))) (PreH15 : ((Znth (remainder - 1 ) values 0) < p_pre)) (PreH16 : (0 < ((p_pre - quotient ) * (Znth (remainder - 1 ) values 0) ))) (PreH17 : (((p_pre - quotient ) * (Znth (remainder - 1 ) values 0) ) <= INT_MAX)) (PreH18 : (ModularInversePrefix p_pre i values )) ,
  (IntArray.seg inverse_pre 1 i values )
  **  (IntArray.undef_seg inverse_pre i p_pre )
|--
  “ (PrimeForLinearInverse p_pre ) ” 
  &&  “ (2 <= p_pre) ” 
  &&  “ (p_pre <= 46340) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i < p_pre) ” 
  &&  “ (quotient = (p_pre ÷ i )) ” 
  &&  “ (remainder = (p_pre % ( i ) )) ” 
  &&  “ (p_pre = ((quotient * i ) + remainder )) ” 
  &&  “ (1 <= quotient) ” 
  &&  “ (1 <= remainder) ” 
  &&  “ (remainder < i) ” 
  &&  “ (0 < (p_pre - quotient )) ” 
  &&  “ ((p_pre - quotient ) < p_pre) ” 
  &&  “ (0 < (Znth (remainder - 1 ) values 0)) ” 
  &&  “ ((Znth (remainder - 1 ) values 0) < p_pre) ” 
  &&  “ (0 < ((p_pre - quotient ) * (Znth (remainder - 1 ) values 0) )) ” 
  &&  “ (((p_pre - quotient ) * (Znth (remainder - 1 ) values 0) ) <= INT_MAX) ” 
  &&  “ (ModularInversePrefix p_pre i values ) ”
  &&  (((inverse_pre + (remainder * sizeof(INT)))) # Int  |-> (Znth (remainder - 1 ) values 0))
  **  (IntArray.missing_i inverse_pre remainder 1 i values )
  **  (IntArray.undef_seg inverse_pre i p_pre )
.

Definition linear_modular_inverse_partial_solve_wit_3 := 
forall (inverse_pre: Z) (p_pre: Z) (values: (@list Z)) (i: Z) (quotient: Z) (remainder: Z) (PreH1 : (PrimeForLinearInverse p_pre )) (PreH2 : (2 <= p_pre)) (PreH3 : (p_pre <= 46340)) (PreH4 : (2 <= i)) (PreH5 : (i < p_pre)) (PreH6 : (quotient = (p_pre ÷ i ))) (PreH7 : (remainder = (p_pre % ( i ) ))) (PreH8 : (p_pre = ((quotient * i ) + remainder ))) (PreH9 : (1 <= quotient)) (PreH10 : (1 <= remainder)) (PreH11 : (remainder < i)) (PreH12 : (0 < (p_pre - quotient ))) (PreH13 : ((p_pre - quotient ) < p_pre)) (PreH14 : (0 < (Znth (remainder - 1 ) values 0))) (PreH15 : ((Znth (remainder - 1 ) values 0) < p_pre)) (PreH16 : (0 < ((p_pre - quotient ) * (Znth (remainder - 1 ) values 0) ))) (PreH17 : (((p_pre - quotient ) * (Znth (remainder - 1 ) values 0) ) <= INT_MAX)) (PreH18 : (ModularInversePrefix p_pre i values )) ,
  (IntArray.seg inverse_pre 1 i values )
  **  (IntArray.undef_seg inverse_pre i p_pre )
|--
  “ (PrimeForLinearInverse p_pre ) ” 
  &&  “ (2 <= p_pre) ” 
  &&  “ (p_pre <= 46340) ” 
  &&  “ (2 <= i) ” 
  &&  “ (i < p_pre) ” 
  &&  “ (quotient = (p_pre ÷ i )) ” 
  &&  “ (remainder = (p_pre % ( i ) )) ” 
  &&  “ (p_pre = ((quotient * i ) + remainder )) ” 
  &&  “ (1 <= quotient) ” 
  &&  “ (1 <= remainder) ” 
  &&  “ (remainder < i) ” 
  &&  “ (0 < (p_pre - quotient )) ” 
  &&  “ ((p_pre - quotient ) < p_pre) ” 
  &&  “ (0 < (Znth (remainder - 1 ) values 0)) ” 
  &&  “ ((Znth (remainder - 1 ) values 0) < p_pre) ” 
  &&  “ (0 < ((p_pre - quotient ) * (Znth (remainder - 1 ) values 0) )) ” 
  &&  “ (((p_pre - quotient ) * (Znth (remainder - 1 ) values 0) ) <= INT_MAX) ” 
  &&  “ (ModularInversePrefix p_pre i values ) ”
  &&  (((inverse_pre + (i * sizeof(INT)))) # Int  |->_)
  **  (IntArray.undef_seg inverse_pre (i + 1 ) p_pre )
  **  (IntArray.seg inverse_pre 1 i values )
.

Module Type VC_Correct.


Axiom proof_of_linear_modular_inverse_safety_wit_1 : linear_modular_inverse_safety_wit_1.
Axiom proof_of_linear_modular_inverse_safety_wit_2 : linear_modular_inverse_safety_wit_2.
Axiom proof_of_linear_modular_inverse_safety_wit_3 : linear_modular_inverse_safety_wit_3.
Axiom proof_of_linear_modular_inverse_safety_wit_4 : linear_modular_inverse_safety_wit_4.
Axiom proof_of_linear_modular_inverse_safety_wit_5 : linear_modular_inverse_safety_wit_5.
Axiom proof_of_linear_modular_inverse_safety_wit_6 : linear_modular_inverse_safety_wit_6.
Axiom proof_of_linear_modular_inverse_safety_wit_7 : linear_modular_inverse_safety_wit_7.
Axiom proof_of_linear_modular_inverse_safety_wit_8 : linear_modular_inverse_safety_wit_8.
Axiom proof_of_linear_modular_inverse_safety_wit_9 : linear_modular_inverse_safety_wit_9.
Axiom proof_of_linear_modular_inverse_entail_wit_1 : linear_modular_inverse_entail_wit_1.
Axiom proof_of_linear_modular_inverse_entail_wit_2 : linear_modular_inverse_entail_wit_2.
Axiom proof_of_linear_modular_inverse_entail_wit_3 : linear_modular_inverse_entail_wit_3.
Axiom proof_of_linear_modular_inverse_return_wit_1 : linear_modular_inverse_return_wit_1.
Axiom proof_of_linear_modular_inverse_partial_solve_wit_1 : linear_modular_inverse_partial_solve_wit_1.
Axiom proof_of_linear_modular_inverse_partial_solve_wit_2 : linear_modular_inverse_partial_solve_wit_2.
Axiom proof_of_linear_modular_inverse_partial_solve_wit_3 : linear_modular_inverse_partial_solve_wit_3.

End VC_Correct.
