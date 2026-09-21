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
Require Import SimpleC.EE.LLM_bench.Algorithms.euler_theorem_inverse.euler_theorem_inverse_lib.
Local Open Scope sac.

(*----- Function euler_phi -----*)

Definition euler_phi_safety_wit_1 := 
forall (value_pre: Z) (PreH1 : (2 <= value_pre)) (PreH2 : (value_pre <= 46341)) ,
  ((( &( "factor" ) )) # Int  |->_)
  **  ((( &( "result" ) )) # Int  |-> value_pre)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition euler_phi_safety_wit_2 := 
forall (value_pre: Z) (factor: Z) (result: Z) (value: Z) (PreH1 : (2 <= value_pre)) (PreH2 : (value_pre <= 46341)) (PreH3 : (1 <= value)) (PreH4 : (value <= value_pre)) (PreH5 : (1 <= result)) (PreH6 : (result <= value_pre)) (PreH7 : (2 <= factor)) (PreH8 : (factor <= 216)) (PreH9 : (EulerPhiProgress value_pre factor value result )) ,
  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "result" ) )) # Int  |-> result)
  **  ((( &( "factor" ) )) # Int  |-> factor)
|--
  “ ((factor * factor ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (factor * factor )) ”
.

Definition euler_phi_safety_wit_3 := 
forall (value_pre: Z) (factor: Z) (result: Z) (value: Z) (PreH1 : ((factor * factor ) <= value)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= factor)) (PreH9 : (factor <= 216)) (PreH10 : (EulerPhiProgress value_pre factor value result )) ,
  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "result" ) )) # Int  |-> result)
  **  ((( &( "factor" ) )) # Int  |-> factor)
|--
  “ ((value <> (INT_MIN)) \/ (factor <> (-1))) ” 
  &&  “ (factor <> 0) ”
.

Definition euler_phi_safety_wit_4 := 
forall (value_pre: Z) (factor: Z) (result: Z) (value: Z) (PreH1 : ((factor * factor ) <= value)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= factor)) (PreH9 : (factor <= 216)) (PreH10 : (EulerPhiProgress value_pre factor value result )) ,
  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "result" ) )) # Int  |-> result)
  **  ((( &( "factor" ) )) # Int  |-> factor)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition euler_phi_safety_wit_5 := 
forall (value_pre: Z) (factor: Z) (result: Z) (value: Z) (PreH1 : (2 <= value_pre)) (PreH2 : (value_pre <= 46341)) (PreH3 : (1 <= value)) (PreH4 : (value <= value_pre)) (PreH5 : (1 <= result)) (PreH6 : (result <= value_pre)) (PreH7 : (2 <= factor)) (PreH8 : (factor <= 216)) (PreH9 : (EulerPhiRemovalProgress value_pre factor value result )) ,
  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "result" ) )) # Int  |-> result)
  **  ((( &( "factor" ) )) # Int  |-> factor)
|--
  “ ((value <> (INT_MIN)) \/ (factor <> (-1))) ” 
  &&  “ (factor <> 0) ”
.

Definition euler_phi_safety_wit_6 := 
forall (value_pre: Z) (factor: Z) (result: Z) (value: Z) (PreH1 : (2 <= value_pre)) (PreH2 : (value_pre <= 46341)) (PreH3 : (1 <= value)) (PreH4 : (value <= value_pre)) (PreH5 : (1 <= result)) (PreH6 : (result <= value_pre)) (PreH7 : (2 <= factor)) (PreH8 : (factor <= 216)) (PreH9 : (EulerPhiRemovalProgress value_pre factor value result )) ,
  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "result" ) )) # Int  |-> result)
  **  ((( &( "factor" ) )) # Int  |-> factor)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition euler_phi_safety_wit_7 := 
forall (value_pre: Z) (factor: Z) (result: Z) (value: Z) (PreH1 : ((value % ( factor ) ) = 0)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= factor)) (PreH9 : (factor <= 216)) (PreH10 : (EulerPhiRemovalProgress value_pre factor value result )) ,
  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "result" ) )) # Int  |-> result)
  **  ((( &( "factor" ) )) # Int  |-> factor)
|--
  “ ((value <> (INT_MIN)) \/ (factor <> (-1))) ” 
  &&  “ (factor <> 0) ”
.

Definition euler_phi_safety_wit_8 := 
(
forall (value_pre: Z) (factor: Z) (result: Z) (value: Z) (PreH1 : ((value % ( factor ) ) <> 0)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= factor)) (PreH9 : (factor <= 216)) (PreH10 : (EulerPhiRemovalProgress value_pre factor value result )) ,
  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "result" ) )) # Int  |-> result)
  **  ((( &( "factor" ) )) # Int  |-> factor)
|--
  “ (((result ÷ factor ) * (factor - 1 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((result ÷ factor ) * (factor - 1 ) )) ”
) \/
(
forall (value_pre: Z) (factor: Z) (result: Z) (value: Z) (PreH1 : ((value % ( factor ) ) <> 0)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= factor)) (PreH9 : (factor <= 216)) (PreH10 : (EulerPhiRemovalProgress value_pre factor value result )) ,
  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "result" ) )) # Int  |-> result)
  **  ((( &( "factor" ) )) # Int  |-> factor)
|--
  “ (((result ÷ factor ) * (factor - 1 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((result ÷ factor ) * (factor - 1 ) )) ”
).

Definition euler_phi_safety_wit_8_split_goal_1 := 
forall (value_pre: Z) (factor: Z) (result: Z) (value: Z) (PreH1 : ((value % ( factor ) ) <> 0)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= factor)) (PreH9 : (factor <= 216)) (PreH10 : (EulerPhiRemovalProgress value_pre factor value result )) ,
  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "result" ) )) # Int  |-> result)
  **  ((( &( "factor" ) )) # Int  |-> factor)
|--
  “ (((result ÷ factor ) * (factor - 1 ) ) <= INT_MAX) ”
.

Definition euler_phi_safety_wit_8_split_goal_2 := 
forall (value_pre: Z) (factor: Z) (result: Z) (value: Z) (PreH1 : ((value % ( factor ) ) <> 0)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= factor)) (PreH9 : (factor <= 216)) (PreH10 : (EulerPhiRemovalProgress value_pre factor value result )) ,
  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "result" ) )) # Int  |-> result)
  **  ((( &( "factor" ) )) # Int  |-> factor)
|--
  “ ((INT_MIN) <= ((result ÷ factor ) * (factor - 1 ) )) ”
.

Definition euler_phi_safety_wit_9 := 
forall (value_pre: Z) (factor: Z) (result: Z) (value: Z) (PreH1 : ((value % ( factor ) ) <> 0)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= factor)) (PreH9 : (factor <= 216)) (PreH10 : (EulerPhiRemovalProgress value_pre factor value result )) ,
  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "result" ) )) # Int  |-> result)
  **  ((( &( "factor" ) )) # Int  |-> factor)
|--
  “ ((factor - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (factor - 1 )) ”
.

Definition euler_phi_safety_wit_10 := 
forall (value_pre: Z) (factor: Z) (result: Z) (value: Z) (PreH1 : ((value % ( factor ) ) <> 0)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= factor)) (PreH9 : (factor <= 216)) (PreH10 : (EulerPhiRemovalProgress value_pre factor value result )) ,
  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "result" ) )) # Int  |-> result)
  **  ((( &( "factor" ) )) # Int  |-> factor)
|--
  “ ((result <> (INT_MIN)) \/ (factor <> (-1))) ” 
  &&  “ (factor <> 0) ”
.

Definition euler_phi_safety_wit_11 := 
forall (value_pre: Z) (factor: Z) (result: Z) (value: Z) (PreH1 : ((value % ( factor ) ) <> 0)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= factor)) (PreH9 : (factor <= 216)) (PreH10 : (EulerPhiRemovalProgress value_pre factor value result )) ,
  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "result" ) )) # Int  |-> result)
  **  ((( &( "factor" ) )) # Int  |-> factor)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition euler_phi_safety_wit_12 := 
forall (value_pre: Z) (factor: Z) (result: Z) (value: Z) (PreH1 : ((value % ( factor ) ) <> 0)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= factor)) (PreH9 : (factor <= 216)) (PreH10 : (EulerPhiRemovalProgress value_pre factor value result )) ,
  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "result" ) )) # Int  |-> ((result ÷ factor ) * (factor - 1 ) ))
  **  ((( &( "factor" ) )) # Int  |-> factor)
|--
  “ ((factor + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (factor + 1 )) ”
.

Definition euler_phi_safety_wit_13 := 
forall (value_pre: Z) (factor: Z) (result: Z) (value: Z) (PreH1 : ((value % ( factor ) ) <> 0)) (PreH2 : ((factor * factor ) <= value)) (PreH3 : (2 <= value_pre)) (PreH4 : (value_pre <= 46341)) (PreH5 : (1 <= value)) (PreH6 : (value <= value_pre)) (PreH7 : (1 <= result)) (PreH8 : (result <= value_pre)) (PreH9 : (2 <= factor)) (PreH10 : (factor <= 216)) (PreH11 : (EulerPhiProgress value_pre factor value result )) ,
  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "result" ) )) # Int  |-> result)
  **  ((( &( "factor" ) )) # Int  |-> factor)
|--
  “ ((factor + 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (factor + 1 )) ”
.

Definition euler_phi_safety_wit_14 := 
forall (value_pre: Z) (frontier: Z) (value: Z) (result: Z) (PreH1 : (2 <= value_pre)) (PreH2 : (value_pre <= 46341)) (PreH3 : (1 <= value)) (PreH4 : (value <= value_pre)) (PreH5 : (1 <= result)) (PreH6 : (result <= value_pre)) (PreH7 : (2 <= frontier)) (PreH8 : (frontier <= 216)) (PreH9 : ((frontier * frontier ) > value)) (PreH10 : ((result % ( value ) ) = 0)) (PreH11 : (1 <= (result ÷ value ))) (PreH12 : (0 <= ((result ÷ value ) * (value - 1 ) ))) (PreH13 : (((result ÷ value ) * (value - 1 ) ) <= value_pre)) (PreH14 : (EulerPhiProgress value_pre frontier value result )) ,
  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition euler_phi_safety_wit_15 := 
forall (value_pre: Z) (frontier: Z) (value: Z) (result: Z) (PreH1 : (2 <= value_pre)) (PreH2 : (value_pre <= 46341)) (PreH3 : (1 <= value)) (PreH4 : (value <= value_pre)) (PreH5 : (1 <= result)) (PreH6 : (result <= value_pre)) (PreH7 : (2 <= frontier)) (PreH8 : (frontier <= 216)) (PreH9 : ((frontier * frontier ) > value)) (PreH10 : (value = 1)) (PreH11 : (EulerPhiProgress value_pre frontier value result )) ,
  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition euler_phi_safety_wit_16 := 
forall (value_pre: Z) (frontier: Z) (value: Z) (result: Z) (PreH1 : (value <> 1)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= frontier)) (PreH9 : (frontier <= 216)) (PreH10 : ((frontier * frontier ) > value)) (PreH11 : (value = 1)) (PreH12 : (EulerPhiProgress value_pre frontier value result )) ,
  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ False ”
.

Definition euler_phi_safety_wit_17 := 
forall (value_pre: Z) (frontier: Z) (value: Z) (result: Z) (PreH1 : (value <> 1)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= frontier)) (PreH9 : (frontier <= 216)) (PreH10 : ((frontier * frontier ) > value)) (PreH11 : ((result % ( value ) ) = 0)) (PreH12 : (1 <= (result ÷ value ))) (PreH13 : (0 <= ((result ÷ value ) * (value - 1 ) ))) (PreH14 : (((result ÷ value ) * (value - 1 ) ) <= value_pre)) (PreH15 : (EulerPhiProgress value_pre frontier value result )) ,
  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ (((result ÷ value ) * (value - 1 ) ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= ((result ÷ value ) * (value - 1 ) )) ”
.

Definition euler_phi_safety_wit_18 := 
forall (value_pre: Z) (frontier: Z) (value: Z) (result: Z) (PreH1 : (value <> 1)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= frontier)) (PreH9 : (frontier <= 216)) (PreH10 : ((frontier * frontier ) > value)) (PreH11 : ((result % ( value ) ) = 0)) (PreH12 : (1 <= (result ÷ value ))) (PreH13 : (0 <= ((result ÷ value ) * (value - 1 ) ))) (PreH14 : (((result ÷ value ) * (value - 1 ) ) <= value_pre)) (PreH15 : (EulerPhiProgress value_pre frontier value result )) ,
  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ ((value - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (value - 1 )) ”
.

Definition euler_phi_safety_wit_19 := 
forall (value_pre: Z) (frontier: Z) (value: Z) (result: Z) (PreH1 : (value <> 1)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= frontier)) (PreH9 : (frontier <= 216)) (PreH10 : ((frontier * frontier ) > value)) (PreH11 : ((result % ( value ) ) = 0)) (PreH12 : (1 <= (result ÷ value ))) (PreH13 : (0 <= ((result ÷ value ) * (value - 1 ) ))) (PreH14 : (((result ÷ value ) * (value - 1 ) ) <= value_pre)) (PreH15 : (EulerPhiProgress value_pre frontier value result )) ,
  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ ((result <> (INT_MIN)) \/ (value <> (-1))) ” 
  &&  “ (value <> 0) ”
.

Definition euler_phi_safety_wit_20 := 
forall (value_pre: Z) (frontier: Z) (value: Z) (result: Z) (PreH1 : (value <> 1)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= frontier)) (PreH9 : (frontier <= 216)) (PreH10 : ((frontier * frontier ) > value)) (PreH11 : ((result % ( value ) ) = 0)) (PreH12 : (1 <= (result ÷ value ))) (PreH13 : (0 <= ((result ÷ value ) * (value - 1 ) ))) (PreH14 : (((result ÷ value ) * (value - 1 ) ) <= value_pre)) (PreH15 : (EulerPhiProgress value_pre frontier value result )) ,
  ((( &( "value" ) )) # Int  |-> value)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition euler_phi_entail_wit_1 := 
(
forall (value_pre: Z) (PreH1 : (2 <= value_pre)) (PreH2 : (value_pre <= 46341)) ,
  TT && emp 
|--
  “ (2 <= value_pre) ” 
  &&  “ (value_pre <= 46341) ” 
  &&  “ (1 <= value_pre) ” 
  &&  “ (value_pre <= value_pre) ” 
  &&  “ (1 <= value_pre) ” 
  &&  “ (value_pre <= value_pre) ” 
  &&  “ (2 <= 2) ” 
  &&  “ (2 <= 216) ” 
  &&  “ (EulerPhiProgress value_pre 2 value_pre value_pre ) ”
  &&  emp
) \/
(
forall (value_pre: Z) (PreH1 : (2 <= value_pre)) (PreH2 : (value_pre <= 46341)) ,
  TT && emp 
|--
  “ (EulerPhiProgress value_pre 2 value_pre value_pre ) ”
  &&  emp
).

Definition euler_phi_entail_wit_1_split_goal_1 := 
forall (value_pre: Z) (PreH1 : (2 <= value_pre)) (PreH2 : (value_pre <= 46341)) ,
  (EulerPhiProgress value_pre 2 value_pre value_pre )
.

Definition euler_phi_entail_wit_2 := 
(
forall (value_pre: Z) (factor: Z) (result: Z) (value: Z) (PreH1 : ((value % ( factor ) ) = 0)) (PreH2 : ((factor * factor ) <= value)) (PreH3 : (2 <= value_pre)) (PreH4 : (value_pre <= 46341)) (PreH5 : (1 <= value)) (PreH6 : (value <= value_pre)) (PreH7 : (1 <= result)) (PreH8 : (result <= value_pre)) (PreH9 : (2 <= factor)) (PreH10 : (factor <= 216)) (PreH11 : (EulerPhiProgress value_pre factor value result )) ,
  TT && emp 
|--
  “ (2 <= value_pre) ” 
  &&  “ (value_pre <= 46341) ” 
  &&  “ (1 <= value) ” 
  &&  “ (value <= value_pre) ” 
  &&  “ (1 <= result) ” 
  &&  “ (result <= value_pre) ” 
  &&  “ (2 <= factor) ” 
  &&  “ (factor <= 216) ” 
  &&  “ (EulerPhiRemovalProgress value_pre factor value result ) ”
  &&  emp
) \/
(
forall (value_pre: Z) (factor: Z) (result: Z) (value: Z) (PreH1 : ((value % ( factor ) ) = 0)) (PreH2 : ((factor * factor ) <= value)) (PreH3 : (2 <= value_pre)) (PreH4 : (value_pre <= 46341)) (PreH5 : (1 <= value)) (PreH6 : (value <= value_pre)) (PreH7 : (1 <= result)) (PreH8 : (result <= value_pre)) (PreH9 : (2 <= factor)) (PreH10 : (factor <= 216)) (PreH11 : (EulerPhiProgress value_pre factor value result )) ,
  TT && emp 
|--
  “ (EulerPhiRemovalProgress value_pre factor value result ) ”
  &&  emp
).

Definition euler_phi_entail_wit_2_split_goal_1 := 
forall (value_pre: Z) (factor: Z) (result: Z) (value: Z) (PreH1 : ((value % ( factor ) ) = 0)) (PreH2 : ((factor * factor ) <= value)) (PreH3 : (2 <= value_pre)) (PreH4 : (value_pre <= 46341)) (PreH5 : (1 <= value)) (PreH6 : (value <= value_pre)) (PreH7 : (1 <= result)) (PreH8 : (result <= value_pre)) (PreH9 : (2 <= factor)) (PreH10 : (factor <= 216)) (PreH11 : (EulerPhiProgress value_pre factor value result )) ,
  (EulerPhiRemovalProgress value_pre factor value result )
.

Definition euler_phi_entail_wit_3 := 
(
forall (value_pre: Z) (factor: Z) (result: Z) (value: Z) (PreH1 : ((value % ( factor ) ) = 0)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= factor)) (PreH9 : (factor <= 216)) (PreH10 : (EulerPhiRemovalProgress value_pre factor value result )) ,
  TT && emp 
|--
  “ (2 <= value_pre) ” 
  &&  “ (value_pre <= 46341) ” 
  &&  “ (1 <= (value ÷ factor )) ” 
  &&  “ ((value ÷ factor ) <= value_pre) ” 
  &&  “ (1 <= result) ” 
  &&  “ (result <= value_pre) ” 
  &&  “ (2 <= factor) ” 
  &&  “ (factor <= 216) ” 
  &&  “ (EulerPhiRemovalProgress value_pre factor (value ÷ factor ) result ) ”
  &&  emp
) \/
(
forall (value_pre: Z) (factor: Z) (result: Z) (value: Z) (PreH1 : ((value % ( factor ) ) = 0)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= factor)) (PreH9 : (factor <= 216)) (PreH10 : (EulerPhiRemovalProgress value_pre factor value result )) ,
  TT && emp 
|--
  “ (EulerPhiRemovalProgress value_pre factor (value ÷ factor ) result ) ” 
  &&  “ ((value ÷ factor ) <= value_pre) ” 
  &&  “ (1 <= (value ÷ factor )) ”
  &&  emp
).

Definition euler_phi_entail_wit_3_split_goal_1 := 
forall (value_pre: Z) (factor: Z) (result: Z) (value: Z) (PreH1 : ((value % ( factor ) ) = 0)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= factor)) (PreH9 : (factor <= 216)) (PreH10 : (EulerPhiRemovalProgress value_pre factor value result )) ,
  (EulerPhiRemovalProgress value_pre factor (value ÷ factor ) result )
.

Definition euler_phi_entail_wit_3_split_goal_2 := 
forall (value_pre: Z) (factor: Z) (result: Z) (value: Z) (PreH1 : ((value % ( factor ) ) = 0)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= factor)) (PreH9 : (factor <= 216)) (PreH10 : (EulerPhiRemovalProgress value_pre factor value result )) ,
  ((value ÷ factor ) <= value_pre)
.

Definition euler_phi_entail_wit_3_split_goal_3 := 
forall (value_pre: Z) (factor: Z) (result: Z) (value: Z) (PreH1 : ((value % ( factor ) ) = 0)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= factor)) (PreH9 : (factor <= 216)) (PreH10 : (EulerPhiRemovalProgress value_pre factor value result )) ,
  (1 <= (value ÷ factor ))
.

Definition euler_phi_entail_wit_4_1 := 
(
forall (value_pre: Z) (factor: Z) (result: Z) (value: Z) (PreH1 : ((value % ( factor ) ) <> 0)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= factor)) (PreH9 : (factor <= 216)) (PreH10 : (EulerPhiRemovalProgress value_pre factor value result )) ,
  TT && emp 
|--
  “ (2 <= value_pre) ” 
  &&  “ (value_pre <= 46341) ” 
  &&  “ (1 <= value) ” 
  &&  “ (value <= value_pre) ” 
  &&  “ (1 <= ((result ÷ factor ) * (factor - 1 ) )) ” 
  &&  “ (((result ÷ factor ) * (factor - 1 ) ) <= value_pre) ” 
  &&  “ (2 <= (factor + 1 )) ” 
  &&  “ ((factor + 1 ) <= 216) ” 
  &&  “ (EulerPhiProgress value_pre (factor + 1 ) value ((result ÷ factor ) * (factor - 1 ) ) ) ”
  &&  emp
) \/
(
forall (value_pre: Z) (factor: Z) (result: Z) (value: Z) (PreH1 : ((value % ( factor ) ) <> 0)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= factor)) (PreH9 : (factor <= 216)) (PreH10 : (EulerPhiRemovalProgress value_pre factor value result )) ,
  TT && emp 
|--
  “ (EulerPhiProgress value_pre (factor + 1 ) value ((result ÷ factor ) * (factor - 1 ) ) ) ” 
  &&  “ ((factor + 1 ) <= 216) ” 
  &&  “ (((result ÷ factor ) * (factor - 1 ) ) <= value_pre) ” 
  &&  “ (1 <= ((result ÷ factor ) * (factor - 1 ) )) ”
  &&  emp
).

Definition euler_phi_entail_wit_4_1_split_goal_1 := 
forall (value_pre: Z) (factor: Z) (result: Z) (value: Z) (PreH1 : ((value % ( factor ) ) <> 0)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= factor)) (PreH9 : (factor <= 216)) (PreH10 : (EulerPhiRemovalProgress value_pre factor value result )) ,
  (EulerPhiProgress value_pre (factor + 1 ) value ((result ÷ factor ) * (factor - 1 ) ) )
.

Definition euler_phi_entail_wit_4_1_split_goal_2 := 
forall (value_pre: Z) (factor: Z) (result: Z) (value: Z) (PreH1 : ((value % ( factor ) ) <> 0)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= factor)) (PreH9 : (factor <= 216)) (PreH10 : (EulerPhiRemovalProgress value_pre factor value result )) ,
  ((factor + 1 ) <= 216)
.

Definition euler_phi_entail_wit_4_1_split_goal_3 := 
forall (value_pre: Z) (factor: Z) (result: Z) (value: Z) (PreH1 : ((value % ( factor ) ) <> 0)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= factor)) (PreH9 : (factor <= 216)) (PreH10 : (EulerPhiRemovalProgress value_pre factor value result )) ,
  (((result ÷ factor ) * (factor - 1 ) ) <= value_pre)
.

Definition euler_phi_entail_wit_4_1_split_goal_4 := 
forall (value_pre: Z) (factor: Z) (result: Z) (value: Z) (PreH1 : ((value % ( factor ) ) <> 0)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= factor)) (PreH9 : (factor <= 216)) (PreH10 : (EulerPhiRemovalProgress value_pre factor value result )) ,
  (1 <= ((result ÷ factor ) * (factor - 1 ) ))
.

Definition euler_phi_entail_wit_4_2 := 
(
forall (value_pre: Z) (factor: Z) (result: Z) (value: Z) (PreH1 : ((value % ( factor ) ) <> 0)) (PreH2 : ((factor * factor ) <= value)) (PreH3 : (2 <= value_pre)) (PreH4 : (value_pre <= 46341)) (PreH5 : (1 <= value)) (PreH6 : (value <= value_pre)) (PreH7 : (1 <= result)) (PreH8 : (result <= value_pre)) (PreH9 : (2 <= factor)) (PreH10 : (factor <= 216)) (PreH11 : (EulerPhiProgress value_pre factor value result )) ,
  TT && emp 
|--
  “ (2 <= value_pre) ” 
  &&  “ (value_pre <= 46341) ” 
  &&  “ (1 <= value) ” 
  &&  “ (value <= value_pre) ” 
  &&  “ (1 <= result) ” 
  &&  “ (result <= value_pre) ” 
  &&  “ (2 <= (factor + 1 )) ” 
  &&  “ ((factor + 1 ) <= 216) ” 
  &&  “ (EulerPhiProgress value_pre (factor + 1 ) value result ) ”
  &&  emp
) \/
(
forall (value_pre: Z) (factor: Z) (result: Z) (value: Z) (PreH1 : ((value % ( factor ) ) <> 0)) (PreH2 : ((factor * factor ) <= value)) (PreH3 : (2 <= value_pre)) (PreH4 : (value_pre <= 46341)) (PreH5 : (1 <= value)) (PreH6 : (value <= value_pre)) (PreH7 : (1 <= result)) (PreH8 : (result <= value_pre)) (PreH9 : (2 <= factor)) (PreH10 : (factor <= 216)) (PreH11 : (EulerPhiProgress value_pre factor value result )) ,
  TT && emp 
|--
  “ (EulerPhiProgress value_pre (factor + 1 ) value result ) ”
  &&  emp
).

Definition euler_phi_entail_wit_4_2_split_goal_1 := 
forall (value_pre: Z) (factor: Z) (result: Z) (value: Z) (PreH1 : ((value % ( factor ) ) <> 0)) (PreH2 : ((factor * factor ) <= value)) (PreH3 : (2 <= value_pre)) (PreH4 : (value_pre <= 46341)) (PreH5 : (1 <= value)) (PreH6 : (value <= value_pre)) (PreH7 : (1 <= result)) (PreH8 : (result <= value_pre)) (PreH9 : (2 <= factor)) (PreH10 : (factor <= 216)) (PreH11 : (EulerPhiProgress value_pre factor value result )) ,
  (EulerPhiProgress value_pre (factor + 1 ) value result )
.

Definition euler_phi_entail_wit_5 := 
forall (value_pre: Z) (factor: Z) (result: Z) (value: Z) (PreH1 : ((factor * factor ) > value)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= factor)) (PreH9 : (factor <= 216)) (PreH10 : (EulerPhiProgress value_pre factor value result )) ,
  TT && emp 
|--
  (EX (frontier: Z) ,
  “ (2 <= value_pre) ” 
  &&  “ (value_pre <= 46341) ” 
  &&  “ (1 <= value) ” 
  &&  “ (value <= value_pre) ” 
  &&  “ (1 <= result) ” 
  &&  “ (result <= value_pre) ” 
  &&  “ (2 <= frontier) ” 
  &&  “ (frontier <= 216) ” 
  &&  “ ((frontier * frontier ) > value) ” 
  &&  “ ((result % ( value ) ) = 0) ” 
  &&  “ (1 <= (result ÷ value )) ” 
  &&  “ (0 <= ((result ÷ value ) * (value - 1 ) )) ” 
  &&  “ (((result ÷ value ) * (value - 1 ) ) <= value_pre) ” 
  &&  “ (EulerPhiProgress value_pre frontier value result ) ”
  &&  emp)
  ||
  (EX (frontier: Z) ,
  “ (2 <= value_pre) ” 
  &&  “ (value_pre <= 46341) ” 
  &&  “ (1 <= value) ” 
  &&  “ (value <= value_pre) ” 
  &&  “ (1 <= result) ” 
  &&  “ (result <= value_pre) ” 
  &&  “ (2 <= frontier) ” 
  &&  “ (frontier <= 216) ” 
  &&  “ ((frontier * frontier ) > value) ” 
  &&  “ (value = 1) ” 
  &&  “ (EulerPhiProgress value_pre frontier value result ) ”
  &&  emp)
.

Definition euler_phi_return_wit_1 := 
(
forall (value_pre: Z) (frontier: Z) (value: Z) (result: Z) (PreH1 : (value <> 1)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= frontier)) (PreH9 : (frontier <= 216)) (PreH10 : ((frontier * frontier ) > value)) (PreH11 : ((result % ( value ) ) = 0)) (PreH12 : (1 <= (result ÷ value ))) (PreH13 : (0 <= ((result ÷ value ) * (value - 1 ) ))) (PreH14 : (((result ÷ value ) * (value - 1 ) ) <= value_pre)) (PreH15 : (EulerPhiProgress value_pre frontier value result )) ,
  TT && emp 
|--
  “ (1 <= ((result ÷ value ) * (value - 1 ) )) ” 
  &&  “ (((result ÷ value ) * (value - 1 ) ) <= value_pre) ” 
  &&  “ (EulerPhi value_pre ((result ÷ value ) * (value - 1 ) ) ) ”
  &&  emp
) \/
(
forall (value_pre: Z) (frontier: Z) (value: Z) (result: Z) (PreH1 : (value <> 1)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= frontier)) (PreH9 : (frontier <= 216)) (PreH10 : ((frontier * frontier ) > value)) (PreH11 : ((result % ( value ) ) = 0)) (PreH12 : (1 <= (result ÷ value ))) (PreH13 : (0 <= ((result ÷ value ) * (value - 1 ) ))) (PreH14 : (((result ÷ value ) * (value - 1 ) ) <= value_pre)) (PreH15 : (EulerPhiProgress value_pre frontier value result )) ,
  TT && emp 
|--
  “ (EulerPhi value_pre ((result ÷ value ) * (value - 1 ) ) ) ”
  &&  emp
).

Definition euler_phi_return_wit_1_split_goal_1 := 
forall (value_pre: Z) (frontier: Z) (value: Z) (result: Z) (PreH1 : (value <> 1)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= frontier)) (PreH9 : (frontier <= 216)) (PreH10 : ((frontier * frontier ) > value)) (PreH11 : ((result % ( value ) ) = 0)) (PreH12 : (1 <= (result ÷ value ))) (PreH13 : (0 <= ((result ÷ value ) * (value - 1 ) ))) (PreH14 : (((result ÷ value ) * (value - 1 ) ) <= value_pre)) (PreH15 : (EulerPhiProgress value_pre frontier value result )) ,
  (EulerPhi value_pre ((result ÷ value ) * (value - 1 ) ) )
.

Definition euler_phi_return_wit_2 := 
(
forall (value_pre: Z) (frontier: Z) (value: Z) (result: Z) (PreH1 : (value = 1)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= frontier)) (PreH9 : (frontier <= 216)) (PreH10 : ((frontier * frontier ) > value)) (PreH11 : ((result % ( value ) ) = 0)) (PreH12 : (1 <= (result ÷ value ))) (PreH13 : (0 <= ((result ÷ value ) * (value - 1 ) ))) (PreH14 : (((result ÷ value ) * (value - 1 ) ) <= value_pre)) (PreH15 : (EulerPhiProgress value_pre frontier value result )) ,
  TT && emp 
|--
  “ (1 <= result) ” 
  &&  “ (result <= value_pre) ” 
  &&  “ (EulerPhi value_pre result ) ”
  &&  emp
) \/
(
forall (value_pre: Z) (frontier: Z) (value: Z) (result: Z) (PreH1 : (value = 1)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= frontier)) (PreH9 : (frontier <= 216)) (PreH10 : ((frontier * frontier ) > value)) (PreH11 : ((result % ( value ) ) = 0)) (PreH12 : (1 <= (result ÷ value ))) (PreH13 : (0 <= ((result ÷ value ) * (value - 1 ) ))) (PreH14 : (((result ÷ value ) * (value - 1 ) ) <= value_pre)) (PreH15 : (EulerPhiProgress value_pre frontier value result )) ,
  TT && emp 
|--
  “ (EulerPhi value_pre result ) ”
  &&  emp
).

Definition euler_phi_return_wit_2_split_goal_1 := 
forall (value_pre: Z) (frontier: Z) (value: Z) (result: Z) (PreH1 : (value = 1)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= frontier)) (PreH9 : (frontier <= 216)) (PreH10 : ((frontier * frontier ) > value)) (PreH11 : ((result % ( value ) ) = 0)) (PreH12 : (1 <= (result ÷ value ))) (PreH13 : (0 <= ((result ÷ value ) * (value - 1 ) ))) (PreH14 : (((result ÷ value ) * (value - 1 ) ) <= value_pre)) (PreH15 : (EulerPhiProgress value_pre frontier value result )) ,
  (EulerPhi value_pre result )
.

Definition euler_phi_return_wit_3 := 
(
forall (value_pre: Z) (frontier: Z) (value: Z) (result: Z) (PreH1 : (value = 1)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= frontier)) (PreH9 : (frontier <= 216)) (PreH10 : ((frontier * frontier ) > value)) (PreH11 : (value = 1)) (PreH12 : (EulerPhiProgress value_pre frontier value result )) ,
  TT && emp 
|--
  “ (1 <= result) ” 
  &&  “ (result <= value_pre) ” 
  &&  “ (EulerPhi value_pre result ) ”
  &&  emp
) \/
(
forall (value_pre: Z) (frontier: Z) (value: Z) (result: Z) (PreH1 : (value = 1)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= frontier)) (PreH9 : (frontier <= 216)) (PreH10 : ((frontier * frontier ) > value)) (PreH11 : (value = 1)) (PreH12 : (EulerPhiProgress value_pre frontier value result )) ,
  TT && emp 
|--
  “ (EulerPhi value_pre result ) ”
  &&  emp
).

Definition euler_phi_return_wit_3_split_goal_1 := 
forall (value_pre: Z) (frontier: Z) (value: Z) (result: Z) (PreH1 : (value = 1)) (PreH2 : (2 <= value_pre)) (PreH3 : (value_pre <= 46341)) (PreH4 : (1 <= value)) (PreH5 : (value <= value_pre)) (PreH6 : (1 <= result)) (PreH7 : (result <= value_pre)) (PreH8 : (2 <= frontier)) (PreH9 : (frontier <= 216)) (PreH10 : ((frontier * frontier ) > value)) (PreH11 : (value = 1)) (PreH12 : (EulerPhiProgress value_pre frontier value result )) ,
  (EulerPhi value_pre result )
.

(*----- Function modular_power -----*)

Definition modular_power_safety_wit_1 := 
forall (modulus_pre: Z) (exponent_pre: Z) (base_pre: Z) (PreH1 : (0 <= base_pre)) (PreH2 : (base_pre < modulus_pre)) (PreH3 : (0 <= exponent_pre)) (PreH4 : (2 <= modulus_pre)) (PreH5 : (modulus_pre <= 46341)) ,
  ((( &( "result" ) )) # Int  |->_)
  **  ((( &( "base" ) )) # Int  |-> base_pre)
  **  ((( &( "exponent" ) )) # Int  |-> exponent_pre)
  **  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition modular_power_safety_wit_2 := 
forall (modulus_pre: Z) (exponent_pre: Z) (base_pre: Z) (result: Z) (exponent: Z) (base: Z) (PreH1 : (2 <= modulus_pre)) (PreH2 : (modulus_pre <= 46341)) (PreH3 : (0 <= base)) (PreH4 : (base < modulus_pre)) (PreH5 : (0 <= exponent)) (PreH6 : (0 <= result)) (PreH7 : (result < modulus_pre)) (PreH8 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "base" ) )) # Int  |-> base)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ (0 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 0) ”
.

Definition modular_power_safety_wit_3 := 
forall (modulus_pre: Z) (exponent_pre: Z) (base_pre: Z) (result: Z) (exponent: Z) (base: Z) (PreH1 : (exponent > 0)) (PreH2 : (2 <= modulus_pre)) (PreH3 : (modulus_pre <= 46341)) (PreH4 : (0 <= base)) (PreH5 : (base < modulus_pre)) (PreH6 : (0 <= exponent)) (PreH7 : (0 <= result)) (PreH8 : (result < modulus_pre)) (PreH9 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "base" ) )) # Int  |-> base)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ ((exponent <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition modular_power_safety_wit_4 := 
forall (modulus_pre: Z) (exponent_pre: Z) (base_pre: Z) (result: Z) (exponent: Z) (base: Z) (PreH1 : (exponent > 0)) (PreH2 : (2 <= modulus_pre)) (PreH3 : (modulus_pre <= 46341)) (PreH4 : (0 <= base)) (PreH5 : (base < modulus_pre)) (PreH6 : (0 <= exponent)) (PreH7 : (0 <= result)) (PreH8 : (result < modulus_pre)) (PreH9 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "base" ) )) # Int  |-> base)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition modular_power_safety_wit_5 := 
forall (modulus_pre: Z) (exponent_pre: Z) (base_pre: Z) (result: Z) (exponent: Z) (base: Z) (PreH1 : (exponent > 0)) (PreH2 : (2 <= modulus_pre)) (PreH3 : (modulus_pre <= 46341)) (PreH4 : (0 <= base)) (PreH5 : (base < modulus_pre)) (PreH6 : (0 <= exponent)) (PreH7 : (0 <= result)) (PreH8 : (result < modulus_pre)) (PreH9 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "base" ) )) # Int  |-> base)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition modular_power_safety_wit_6 := 
forall (modulus_pre: Z) (exponent_pre: Z) (base_pre: Z) (result: Z) (exponent: Z) (base: Z) (PreH1 : ((exponent % ( 2 ) ) = 1)) (PreH2 : (exponent > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 46341)) (PreH5 : (0 <= base)) (PreH6 : (base < modulus_pre)) (PreH7 : (0 <= exponent)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "base" ) )) # Int  |-> base)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ (((result * base ) <> (INT_MIN)) \/ (modulus_pre <> (-1))) ” 
  &&  “ (modulus_pre <> 0) ”
.

Definition modular_power_safety_wit_7 := 
forall (modulus_pre: Z) (exponent_pre: Z) (base_pre: Z) (result: Z) (exponent: Z) (base: Z) (PreH1 : ((exponent % ( 2 ) ) = 1)) (PreH2 : (exponent > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 46341)) (PreH5 : (0 <= base)) (PreH6 : (base < modulus_pre)) (PreH7 : (0 <= exponent)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "base" ) )) # Int  |-> base)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ ((result * base ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (result * base )) ”
.

Definition modular_power_safety_wit_8 := 
forall (modulus_pre: Z) (exponent_pre: Z) (base_pre: Z) (result: Z) (exponent: Z) (base: Z) (PreH1 : ((exponent % ( 2 ) ) = 1)) (PreH2 : (exponent > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 46341)) (PreH5 : (0 <= base)) (PreH6 : (base < modulus_pre)) (PreH7 : (0 <= exponent)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "base" ) )) # Int  |-> base)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "result" ) )) # Int  |-> ((result * base ) % ( modulus_pre ) ))
|--
  “ (((base * base ) <> (INT_MIN)) \/ (modulus_pre <> (-1))) ” 
  &&  “ (modulus_pre <> 0) ”
.

Definition modular_power_safety_wit_9 := 
forall (modulus_pre: Z) (exponent_pre: Z) (base_pre: Z) (result: Z) (exponent: Z) (base: Z) (PreH1 : ((exponent % ( 2 ) ) = 1)) (PreH2 : (exponent > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 46341)) (PreH5 : (0 <= base)) (PreH6 : (base < modulus_pre)) (PreH7 : (0 <= exponent)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "base" ) )) # Int  |-> base)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "result" ) )) # Int  |-> ((result * base ) % ( modulus_pre ) ))
|--
  “ ((base * base ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (base * base )) ”
.

Definition modular_power_safety_wit_10 := 
forall (modulus_pre: Z) (exponent_pre: Z) (base_pre: Z) (result: Z) (exponent: Z) (base: Z) (PreH1 : ((exponent % ( 2 ) ) <> 1)) (PreH2 : (exponent > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 46341)) (PreH5 : (0 <= base)) (PreH6 : (base < modulus_pre)) (PreH7 : (0 <= exponent)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "base" ) )) # Int  |-> base)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ (((base * base ) <> (INT_MIN)) \/ (modulus_pre <> (-1))) ” 
  &&  “ (modulus_pre <> 0) ”
.

Definition modular_power_safety_wit_11 := 
forall (modulus_pre: Z) (exponent_pre: Z) (base_pre: Z) (result: Z) (exponent: Z) (base: Z) (PreH1 : ((exponent % ( 2 ) ) <> 1)) (PreH2 : (exponent > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 46341)) (PreH5 : (0 <= base)) (PreH6 : (base < modulus_pre)) (PreH7 : (0 <= exponent)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "base" ) )) # Int  |-> base)
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ ((base * base ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (base * base )) ”
.

Definition modular_power_safety_wit_12 := 
forall (modulus_pre: Z) (exponent_pre: Z) (base_pre: Z) (result: Z) (exponent: Z) (base: Z) (PreH1 : ((exponent % ( 2 ) ) = 1)) (PreH2 : (exponent > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 46341)) (PreH5 : (0 <= base)) (PreH6 : (base < modulus_pre)) (PreH7 : (0 <= exponent)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "base" ) )) # Int  |-> ((base * base ) % ( modulus_pre ) ))
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "result" ) )) # Int  |-> ((result * base ) % ( modulus_pre ) ))
|--
  “ ((exponent <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition modular_power_safety_wit_13 := 
forall (modulus_pre: Z) (exponent_pre: Z) (base_pre: Z) (result: Z) (exponent: Z) (base: Z) (PreH1 : ((exponent % ( 2 ) ) = 1)) (PreH2 : (exponent > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 46341)) (PreH5 : (0 <= base)) (PreH6 : (base < modulus_pre)) (PreH7 : (0 <= exponent)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "base" ) )) # Int  |-> ((base * base ) % ( modulus_pre ) ))
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "result" ) )) # Int  |-> ((result * base ) % ( modulus_pre ) ))
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition modular_power_safety_wit_14 := 
forall (modulus_pre: Z) (exponent_pre: Z) (base_pre: Z) (result: Z) (exponent: Z) (base: Z) (PreH1 : ((exponent % ( 2 ) ) <> 1)) (PreH2 : (exponent > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 46341)) (PreH5 : (0 <= base)) (PreH6 : (base < modulus_pre)) (PreH7 : (0 <= exponent)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "base" ) )) # Int  |-> ((base * base ) % ( modulus_pre ) ))
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ ((exponent <> (INT_MIN)) \/ (2 <> (-1))) ” 
  &&  “ (2 <> 0) ”
.

Definition modular_power_safety_wit_15 := 
forall (modulus_pre: Z) (exponent_pre: Z) (base_pre: Z) (result: Z) (exponent: Z) (base: Z) (PreH1 : ((exponent % ( 2 ) ) <> 1)) (PreH2 : (exponent > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 46341)) (PreH5 : (0 <= base)) (PreH6 : (base < modulus_pre)) (PreH7 : (0 <= exponent)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result )) ,
  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
  **  ((( &( "base" ) )) # Int  |-> ((base * base ) % ( modulus_pre ) ))
  **  ((( &( "exponent" ) )) # Int  |-> exponent)
  **  ((( &( "result" ) )) # Int  |-> result)
|--
  “ (2 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 2) ”
.

Definition modular_power_entail_wit_1 := 
(
forall (modulus_pre: Z) (exponent_pre: Z) (base_pre: Z) (PreH1 : (0 <= base_pre)) (PreH2 : (base_pre < modulus_pre)) (PreH3 : (0 <= exponent_pre)) (PreH4 : (2 <= modulus_pre)) (PreH5 : (modulus_pre <= 46341)) ,
  TT && emp 
|--
  “ (2 <= modulus_pre) ” 
  &&  “ (modulus_pre <= 46341) ” 
  &&  “ (0 <= base_pre) ” 
  &&  “ (base_pre < modulus_pre) ” 
  &&  “ (0 <= exponent_pre) ” 
  &&  “ (0 <= 1) ” 
  &&  “ (1 < modulus_pre) ” 
  &&  “ (EulerModularPowerProgress base_pre exponent_pre modulus_pre base_pre exponent_pre 1 ) ”
  &&  emp
) \/
(
forall (modulus_pre: Z) (exponent_pre: Z) (base_pre: Z) (PreH1 : (0 <= base_pre)) (PreH2 : (base_pre < modulus_pre)) (PreH3 : (0 <= exponent_pre)) (PreH4 : (2 <= modulus_pre)) (PreH5 : (modulus_pre <= 46341)) ,
  TT && emp 
|--
  “ (EulerModularPowerProgress base_pre exponent_pre modulus_pre base_pre exponent_pre 1 ) ”
  &&  emp
).

Definition modular_power_entail_wit_1_split_goal_1 := 
forall (modulus_pre: Z) (exponent_pre: Z) (base_pre: Z) (PreH1 : (0 <= base_pre)) (PreH2 : (base_pre < modulus_pre)) (PreH3 : (0 <= exponent_pre)) (PreH4 : (2 <= modulus_pre)) (PreH5 : (modulus_pre <= 46341)) ,
  (EulerModularPowerProgress base_pre exponent_pre modulus_pre base_pre exponent_pre 1 )
.

Definition modular_power_entail_wit_2_1 := 
(
forall (modulus_pre: Z) (exponent_pre: Z) (base_pre: Z) (result: Z) (exponent: Z) (base: Z) (PreH1 : ((exponent % ( 2 ) ) = 1)) (PreH2 : (exponent > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 46341)) (PreH5 : (0 <= base)) (PreH6 : (base < modulus_pre)) (PreH7 : (0 <= exponent)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result )) ,
  TT && emp 
|--
  “ (2 <= modulus_pre) ” 
  &&  “ (modulus_pre <= 46341) ” 
  &&  “ (0 <= ((base * base ) % ( modulus_pre ) )) ” 
  &&  “ (((base * base ) % ( modulus_pre ) ) < modulus_pre) ” 
  &&  “ (0 <= (exponent ÷ 2 )) ” 
  &&  “ (0 <= ((result * base ) % ( modulus_pre ) )) ” 
  &&  “ (((result * base ) % ( modulus_pre ) ) < modulus_pre) ” 
  &&  “ (EulerModularPowerProgress base_pre exponent_pre modulus_pre ((base * base ) % ( modulus_pre ) ) (exponent ÷ 2 ) ((result * base ) % ( modulus_pre ) ) ) ”
  &&  emp
) \/
(
forall (modulus_pre: Z) (exponent_pre: Z) (base_pre: Z) (result: Z) (exponent: Z) (base: Z) (PreH1 : ((exponent % ( 2 ) ) = 1)) (PreH2 : (exponent > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 46341)) (PreH5 : (0 <= base)) (PreH6 : (base < modulus_pre)) (PreH7 : (0 <= exponent)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result )) ,
  TT && emp 
|--
  “ (EulerModularPowerProgress base_pre exponent_pre modulus_pre ((base * base ) % ( modulus_pre ) ) (exponent ÷ 2 ) ((result * base ) % ( modulus_pre ) ) ) ” 
  &&  “ (((result * base ) % ( modulus_pre ) ) < modulus_pre) ” 
  &&  “ (0 <= ((result * base ) % ( modulus_pre ) )) ” 
  &&  “ (0 <= (exponent ÷ 2 )) ” 
  &&  “ (((base * base ) % ( modulus_pre ) ) < modulus_pre) ” 
  &&  “ (0 <= ((base * base ) % ( modulus_pre ) )) ”
  &&  emp
).

Definition modular_power_entail_wit_2_1_split_goal_1 := 
forall (modulus_pre: Z) (exponent_pre: Z) (base_pre: Z) (result: Z) (exponent: Z) (base: Z) (PreH1 : ((exponent % ( 2 ) ) = 1)) (PreH2 : (exponent > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 46341)) (PreH5 : (0 <= base)) (PreH6 : (base < modulus_pre)) (PreH7 : (0 <= exponent)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result )) ,
  (EulerModularPowerProgress base_pre exponent_pre modulus_pre ((base * base ) % ( modulus_pre ) ) (exponent ÷ 2 ) ((result * base ) % ( modulus_pre ) ) )
.

Definition modular_power_entail_wit_2_1_split_goal_2 := 
forall (modulus_pre: Z) (exponent_pre: Z) (base_pre: Z) (result: Z) (exponent: Z) (base: Z) (PreH1 : ((exponent % ( 2 ) ) = 1)) (PreH2 : (exponent > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 46341)) (PreH5 : (0 <= base)) (PreH6 : (base < modulus_pre)) (PreH7 : (0 <= exponent)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result )) ,
  (((result * base ) % ( modulus_pre ) ) < modulus_pre)
.

Definition modular_power_entail_wit_2_1_split_goal_3 := 
forall (modulus_pre: Z) (exponent_pre: Z) (base_pre: Z) (result: Z) (exponent: Z) (base: Z) (PreH1 : ((exponent % ( 2 ) ) = 1)) (PreH2 : (exponent > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 46341)) (PreH5 : (0 <= base)) (PreH6 : (base < modulus_pre)) (PreH7 : (0 <= exponent)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result )) ,
  (0 <= ((result * base ) % ( modulus_pre ) ))
.

Definition modular_power_entail_wit_2_1_split_goal_4 := 
forall (modulus_pre: Z) (exponent_pre: Z) (base_pre: Z) (result: Z) (exponent: Z) (base: Z) (PreH1 : ((exponent % ( 2 ) ) = 1)) (PreH2 : (exponent > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 46341)) (PreH5 : (0 <= base)) (PreH6 : (base < modulus_pre)) (PreH7 : (0 <= exponent)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result )) ,
  (0 <= (exponent ÷ 2 ))
.

Definition modular_power_entail_wit_2_1_split_goal_5 := 
forall (modulus_pre: Z) (exponent_pre: Z) (base_pre: Z) (result: Z) (exponent: Z) (base: Z) (PreH1 : ((exponent % ( 2 ) ) = 1)) (PreH2 : (exponent > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 46341)) (PreH5 : (0 <= base)) (PreH6 : (base < modulus_pre)) (PreH7 : (0 <= exponent)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result )) ,
  (((base * base ) % ( modulus_pre ) ) < modulus_pre)
.

Definition modular_power_entail_wit_2_1_split_goal_6 := 
forall (modulus_pre: Z) (exponent_pre: Z) (base_pre: Z) (result: Z) (exponent: Z) (base: Z) (PreH1 : ((exponent % ( 2 ) ) = 1)) (PreH2 : (exponent > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 46341)) (PreH5 : (0 <= base)) (PreH6 : (base < modulus_pre)) (PreH7 : (0 <= exponent)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result )) ,
  (0 <= ((base * base ) % ( modulus_pre ) ))
.

Definition modular_power_entail_wit_2_2 := 
(
forall (modulus_pre: Z) (exponent_pre: Z) (base_pre: Z) (result: Z) (exponent: Z) (base: Z) (PreH1 : ((exponent % ( 2 ) ) <> 1)) (PreH2 : (exponent > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 46341)) (PreH5 : (0 <= base)) (PreH6 : (base < modulus_pre)) (PreH7 : (0 <= exponent)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result )) ,
  TT && emp 
|--
  “ (2 <= modulus_pre) ” 
  &&  “ (modulus_pre <= 46341) ” 
  &&  “ (0 <= ((base * base ) % ( modulus_pre ) )) ” 
  &&  “ (((base * base ) % ( modulus_pre ) ) < modulus_pre) ” 
  &&  “ (0 <= (exponent ÷ 2 )) ” 
  &&  “ (0 <= result) ” 
  &&  “ (result < modulus_pre) ” 
  &&  “ (EulerModularPowerProgress base_pre exponent_pre modulus_pre ((base * base ) % ( modulus_pre ) ) (exponent ÷ 2 ) result ) ”
  &&  emp
) \/
(
forall (modulus_pre: Z) (exponent_pre: Z) (base_pre: Z) (result: Z) (exponent: Z) (base: Z) (PreH1 : ((exponent % ( 2 ) ) <> 1)) (PreH2 : (exponent > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 46341)) (PreH5 : (0 <= base)) (PreH6 : (base < modulus_pre)) (PreH7 : (0 <= exponent)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result )) ,
  TT && emp 
|--
  “ (EulerModularPowerProgress base_pre exponent_pre modulus_pre ((base * base ) % ( modulus_pre ) ) (exponent ÷ 2 ) result ) ” 
  &&  “ (0 <= (exponent ÷ 2 )) ” 
  &&  “ (((base * base ) % ( modulus_pre ) ) < modulus_pre) ” 
  &&  “ (0 <= ((base * base ) % ( modulus_pre ) )) ”
  &&  emp
).

Definition modular_power_entail_wit_2_2_split_goal_1 := 
forall (modulus_pre: Z) (exponent_pre: Z) (base_pre: Z) (result: Z) (exponent: Z) (base: Z) (PreH1 : ((exponent % ( 2 ) ) <> 1)) (PreH2 : (exponent > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 46341)) (PreH5 : (0 <= base)) (PreH6 : (base < modulus_pre)) (PreH7 : (0 <= exponent)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result )) ,
  (EulerModularPowerProgress base_pre exponent_pre modulus_pre ((base * base ) % ( modulus_pre ) ) (exponent ÷ 2 ) result )
.

Definition modular_power_entail_wit_2_2_split_goal_2 := 
forall (modulus_pre: Z) (exponent_pre: Z) (base_pre: Z) (result: Z) (exponent: Z) (base: Z) (PreH1 : ((exponent % ( 2 ) ) <> 1)) (PreH2 : (exponent > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 46341)) (PreH5 : (0 <= base)) (PreH6 : (base < modulus_pre)) (PreH7 : (0 <= exponent)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result )) ,
  (0 <= (exponent ÷ 2 ))
.

Definition modular_power_entail_wit_2_2_split_goal_3 := 
forall (modulus_pre: Z) (exponent_pre: Z) (base_pre: Z) (result: Z) (exponent: Z) (base: Z) (PreH1 : ((exponent % ( 2 ) ) <> 1)) (PreH2 : (exponent > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 46341)) (PreH5 : (0 <= base)) (PreH6 : (base < modulus_pre)) (PreH7 : (0 <= exponent)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result )) ,
  (((base * base ) % ( modulus_pre ) ) < modulus_pre)
.

Definition modular_power_entail_wit_2_2_split_goal_4 := 
forall (modulus_pre: Z) (exponent_pre: Z) (base_pre: Z) (result: Z) (exponent: Z) (base: Z) (PreH1 : ((exponent % ( 2 ) ) <> 1)) (PreH2 : (exponent > 0)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 46341)) (PreH5 : (0 <= base)) (PreH6 : (base < modulus_pre)) (PreH7 : (0 <= exponent)) (PreH8 : (0 <= result)) (PreH9 : (result < modulus_pre)) (PreH10 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result )) ,
  (0 <= ((base * base ) % ( modulus_pre ) ))
.

Definition modular_power_return_wit_1 := 
(
forall (modulus_pre: Z) (exponent_pre: Z) (base_pre: Z) (result: Z) (exponent: Z) (base: Z) (PreH1 : (exponent <= 0)) (PreH2 : (2 <= modulus_pre)) (PreH3 : (modulus_pre <= 46341)) (PreH4 : (0 <= base)) (PreH5 : (base < modulus_pre)) (PreH6 : (0 <= exponent)) (PreH7 : (0 <= result)) (PreH8 : (result < modulus_pre)) (PreH9 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result )) ,
  TT && emp 
|--
  “ (0 <= result) ” 
  &&  “ (result < modulus_pre) ” 
  &&  “ (ModularPower base_pre exponent_pre modulus_pre result ) ”
  &&  emp
) \/
(
forall (modulus_pre: Z) (exponent_pre: Z) (base_pre: Z) (result: Z) (exponent: Z) (base: Z) (PreH1 : (exponent <= 0)) (PreH2 : (2 <= modulus_pre)) (PreH3 : (modulus_pre <= 46341)) (PreH4 : (0 <= base)) (PreH5 : (base < modulus_pre)) (PreH6 : (0 <= exponent)) (PreH7 : (0 <= result)) (PreH8 : (result < modulus_pre)) (PreH9 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result )) ,
  TT && emp 
|--
  “ (ModularPower base_pre exponent_pre modulus_pre result ) ”
  &&  emp
).

Definition modular_power_return_wit_1_split_goal_1 := 
forall (modulus_pre: Z) (exponent_pre: Z) (base_pre: Z) (result: Z) (exponent: Z) (base: Z) (PreH1 : (exponent <= 0)) (PreH2 : (2 <= modulus_pre)) (PreH3 : (modulus_pre <= 46341)) (PreH4 : (0 <= base)) (PreH5 : (base < modulus_pre)) (PreH6 : (0 <= exponent)) (PreH7 : (0 <= result)) (PreH8 : (result < modulus_pre)) (PreH9 : (EulerModularPowerProgress base_pre exponent_pre modulus_pre base exponent result )) ,
  (ModularPower base_pre exponent_pre modulus_pre result )
.

(*----- Function euler_theorem_inverse -----*)

Definition euler_theorem_inverse_safety_wit_1 := 
forall (modulus_pre: Z) (value_pre: Z) (retval: Z) (PreH1 : (1 <= retval)) (PreH2 : (retval <= modulus_pre)) (PreH3 : (EulerPhi modulus_pre retval )) (PreH4 : (0 < value_pre)) (PreH5 : (value_pre < modulus_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((Zgcd (value_pre) (modulus_pre)) = 1)) ,
  ((( &( "exponent" ) )) # Int  |->_)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
|--
  “ ((retval - 1 ) <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= (retval - 1 )) ”
.

Definition euler_theorem_inverse_safety_wit_2 := 
forall (modulus_pre: Z) (value_pre: Z) (retval: Z) (PreH1 : (1 <= retval)) (PreH2 : (retval <= modulus_pre)) (PreH3 : (EulerPhi modulus_pre retval )) (PreH4 : (0 < value_pre)) (PreH5 : (value_pre < modulus_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((Zgcd (value_pre) (modulus_pre)) = 1)) ,
  ((( &( "exponent" ) )) # Int  |->_)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
|--
  “ (1 <= INT_MAX) ” 
  &&  “ ((INT_MIN) <= 1) ”
.

Definition euler_theorem_inverse_return_wit_1 := 
(
forall (modulus_pre: Z) (value_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < modulus_pre)) (PreH3 : (ModularPower value_pre (retval_2 - 1 ) modulus_pre retval )) (PreH4 : (1 <= retval_2)) (PreH5 : (retval_2 <= modulus_pre)) (PreH6 : (EulerPhi modulus_pre retval_2 )) (PreH7 : (0 < value_pre)) (PreH8 : (value_pre < modulus_pre)) (PreH9 : (2 <= modulus_pre)) (PreH10 : (modulus_pre <= 46341)) (PreH11 : ((Zgcd (value_pre) (modulus_pre)) = 1)) ,
  TT && emp 
|--
  “ (0 <= retval) ” 
  &&  “ (retval < modulus_pre) ” 
  &&  “ (EulerTheoremInverse value_pre modulus_pre retval ) ”
  &&  emp
) \/
(
forall (modulus_pre: Z) (value_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < modulus_pre)) (PreH3 : (ModularPower value_pre (retval_2 - 1 ) modulus_pre retval )) (PreH4 : (1 <= retval_2)) (PreH5 : (retval_2 <= modulus_pre)) (PreH6 : (EulerPhi modulus_pre retval_2 )) (PreH7 : (0 < value_pre)) (PreH8 : (value_pre < modulus_pre)) (PreH9 : (2 <= modulus_pre)) (PreH10 : (modulus_pre <= 46341)) (PreH11 : ((Zgcd (value_pre) (modulus_pre)) = 1)) ,
  TT && emp 
|--
  “ (EulerTheoremInverse value_pre modulus_pre retval ) ”
  &&  emp
).

Definition euler_theorem_inverse_return_wit_1_split_goal_1 := 
forall (modulus_pre: Z) (value_pre: Z) (retval_2: Z) (retval: Z) (PreH1 : (0 <= retval)) (PreH2 : (retval < modulus_pre)) (PreH3 : (ModularPower value_pre (retval_2 - 1 ) modulus_pre retval )) (PreH4 : (1 <= retval_2)) (PreH5 : (retval_2 <= modulus_pre)) (PreH6 : (EulerPhi modulus_pre retval_2 )) (PreH7 : (0 < value_pre)) (PreH8 : (value_pre < modulus_pre)) (PreH9 : (2 <= modulus_pre)) (PreH10 : (modulus_pre <= 46341)) (PreH11 : ((Zgcd (value_pre) (modulus_pre)) = 1)) ,
  (EulerTheoremInverse value_pre modulus_pre retval )
.

Definition euler_theorem_inverse_partial_solve_wit_1_pure := 
forall (modulus_pre: Z) (value_pre: Z) (PreH1 : (0 < value_pre)) (PreH2 : (value_pre < modulus_pre)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 46341)) (PreH5 : ((Zgcd (value_pre) (modulus_pre)) = 1)) ,
  ((( &( "exponent" ) )) # Int  |->_)
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
|--
  “ (2 <= modulus_pre) ” 
  &&  “ (modulus_pre <= 46341) ”
.

Definition euler_theorem_inverse_partial_solve_wit_1_aux := 
forall (modulus_pre: Z) (value_pre: Z) (PreH1 : (0 < value_pre)) (PreH2 : (value_pre < modulus_pre)) (PreH3 : (2 <= modulus_pre)) (PreH4 : (modulus_pre <= 46341)) (PreH5 : ((Zgcd (value_pre) (modulus_pre)) = 1)) ,
  TT && emp 
|--
  “ (2 <= modulus_pre) ” 
  &&  “ (modulus_pre <= 46341) ” 
  &&  “ (0 < value_pre) ” 
  &&  “ (value_pre < modulus_pre) ” 
  &&  “ (2 <= modulus_pre) ” 
  &&  “ (modulus_pre <= 46341) ” 
  &&  “ ((Zgcd (value_pre) (modulus_pre)) = 1) ”
  &&  emp
.

Definition euler_theorem_inverse_partial_solve_wit_1 := euler_theorem_inverse_partial_solve_wit_1_pure -> euler_theorem_inverse_partial_solve_wit_1_aux.

Definition euler_theorem_inverse_partial_solve_wit_2_pure := 
forall (modulus_pre: Z) (value_pre: Z) (retval: Z) (PreH1 : (1 <= retval)) (PreH2 : (retval <= modulus_pre)) (PreH3 : (EulerPhi modulus_pre retval )) (PreH4 : (0 < value_pre)) (PreH5 : (value_pre < modulus_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((Zgcd (value_pre) (modulus_pre)) = 1)) ,
  ((( &( "exponent" ) )) # Int  |-> (retval - 1 ))
  **  ((( &( "value" ) )) # Int  |-> value_pre)
  **  ((( &( "modulus" ) )) # Int  |-> modulus_pre)
|--
  “ (0 <= value_pre) ” 
  &&  “ (value_pre < modulus_pre) ” 
  &&  “ (0 <= (retval - 1 )) ” 
  &&  “ (2 <= modulus_pre) ” 
  &&  “ (modulus_pre <= 46341) ”
.

Definition euler_theorem_inverse_partial_solve_wit_2_aux := 
forall (modulus_pre: Z) (value_pre: Z) (retval: Z) (PreH1 : (1 <= retval)) (PreH2 : (retval <= modulus_pre)) (PreH3 : (EulerPhi modulus_pre retval )) (PreH4 : (0 < value_pre)) (PreH5 : (value_pre < modulus_pre)) (PreH6 : (2 <= modulus_pre)) (PreH7 : (modulus_pre <= 46341)) (PreH8 : ((Zgcd (value_pre) (modulus_pre)) = 1)) ,
  TT && emp 
|--
  “ (0 <= value_pre) ” 
  &&  “ (value_pre < modulus_pre) ” 
  &&  “ (0 <= (retval - 1 )) ” 
  &&  “ (2 <= modulus_pre) ” 
  &&  “ (modulus_pre <= 46341) ” 
  &&  “ (1 <= retval) ” 
  &&  “ (retval <= modulus_pre) ” 
  &&  “ (EulerPhi modulus_pre retval ) ” 
  &&  “ (0 < value_pre) ” 
  &&  “ (value_pre < modulus_pre) ” 
  &&  “ (2 <= modulus_pre) ” 
  &&  “ (modulus_pre <= 46341) ” 
  &&  “ ((Zgcd (value_pre) (modulus_pre)) = 1) ”
  &&  emp
.

Definition euler_theorem_inverse_partial_solve_wit_2 := euler_theorem_inverse_partial_solve_wit_2_pure -> euler_theorem_inverse_partial_solve_wit_2_aux.

Module Type VC_Correct.


Axiom proof_of_euler_phi_safety_wit_1 : euler_phi_safety_wit_1.
Axiom proof_of_euler_phi_safety_wit_2 : euler_phi_safety_wit_2.
Axiom proof_of_euler_phi_safety_wit_3 : euler_phi_safety_wit_3.
Axiom proof_of_euler_phi_safety_wit_4 : euler_phi_safety_wit_4.
Axiom proof_of_euler_phi_safety_wit_5 : euler_phi_safety_wit_5.
Axiom proof_of_euler_phi_safety_wit_6 : euler_phi_safety_wit_6.
Axiom proof_of_euler_phi_safety_wit_7 : euler_phi_safety_wit_7.
Axiom proof_of_euler_phi_safety_wit_8 : euler_phi_safety_wit_8.
Axiom proof_of_euler_phi_safety_wit_9 : euler_phi_safety_wit_9.
Axiom proof_of_euler_phi_safety_wit_10 : euler_phi_safety_wit_10.
Axiom proof_of_euler_phi_safety_wit_11 : euler_phi_safety_wit_11.
Axiom proof_of_euler_phi_safety_wit_12 : euler_phi_safety_wit_12.
Axiom proof_of_euler_phi_safety_wit_13 : euler_phi_safety_wit_13.
Axiom proof_of_euler_phi_safety_wit_14 : euler_phi_safety_wit_14.
Axiom proof_of_euler_phi_safety_wit_15 : euler_phi_safety_wit_15.
Axiom proof_of_euler_phi_safety_wit_16 : euler_phi_safety_wit_16.
Axiom proof_of_euler_phi_safety_wit_17 : euler_phi_safety_wit_17.
Axiom proof_of_euler_phi_safety_wit_18 : euler_phi_safety_wit_18.
Axiom proof_of_euler_phi_safety_wit_19 : euler_phi_safety_wit_19.
Axiom proof_of_euler_phi_safety_wit_20 : euler_phi_safety_wit_20.
Axiom proof_of_euler_phi_entail_wit_1 : euler_phi_entail_wit_1.
Axiom proof_of_euler_phi_entail_wit_2 : euler_phi_entail_wit_2.
Axiom proof_of_euler_phi_entail_wit_3 : euler_phi_entail_wit_3.
Axiom proof_of_euler_phi_entail_wit_4_1 : euler_phi_entail_wit_4_1.
Axiom proof_of_euler_phi_entail_wit_4_2 : euler_phi_entail_wit_4_2.
Axiom proof_of_euler_phi_entail_wit_5 : euler_phi_entail_wit_5.
Axiom proof_of_euler_phi_return_wit_1 : euler_phi_return_wit_1.
Axiom proof_of_euler_phi_return_wit_2 : euler_phi_return_wit_2.
Axiom proof_of_euler_phi_return_wit_3 : euler_phi_return_wit_3.
Axiom proof_of_modular_power_safety_wit_1 : modular_power_safety_wit_1.
Axiom proof_of_modular_power_safety_wit_2 : modular_power_safety_wit_2.
Axiom proof_of_modular_power_safety_wit_3 : modular_power_safety_wit_3.
Axiom proof_of_modular_power_safety_wit_4 : modular_power_safety_wit_4.
Axiom proof_of_modular_power_safety_wit_5 : modular_power_safety_wit_5.
Axiom proof_of_modular_power_safety_wit_6 : modular_power_safety_wit_6.
Axiom proof_of_modular_power_safety_wit_7 : modular_power_safety_wit_7.
Axiom proof_of_modular_power_safety_wit_8 : modular_power_safety_wit_8.
Axiom proof_of_modular_power_safety_wit_9 : modular_power_safety_wit_9.
Axiom proof_of_modular_power_safety_wit_10 : modular_power_safety_wit_10.
Axiom proof_of_modular_power_safety_wit_11 : modular_power_safety_wit_11.
Axiom proof_of_modular_power_safety_wit_12 : modular_power_safety_wit_12.
Axiom proof_of_modular_power_safety_wit_13 : modular_power_safety_wit_13.
Axiom proof_of_modular_power_safety_wit_14 : modular_power_safety_wit_14.
Axiom proof_of_modular_power_safety_wit_15 : modular_power_safety_wit_15.
Axiom proof_of_modular_power_entail_wit_1 : modular_power_entail_wit_1.
Axiom proof_of_modular_power_entail_wit_2_1 : modular_power_entail_wit_2_1.
Axiom proof_of_modular_power_entail_wit_2_2 : modular_power_entail_wit_2_2.
Axiom proof_of_modular_power_return_wit_1 : modular_power_return_wit_1.
Axiom proof_of_euler_theorem_inverse_safety_wit_1 : euler_theorem_inverse_safety_wit_1.
Axiom proof_of_euler_theorem_inverse_safety_wit_2 : euler_theorem_inverse_safety_wit_2.
Axiom proof_of_euler_theorem_inverse_return_wit_1 : euler_theorem_inverse_return_wit_1.
Axiom proof_of_euler_theorem_inverse_partial_solve_wit_1_pure : euler_theorem_inverse_partial_solve_wit_1_pure.
Axiom proof_of_euler_theorem_inverse_partial_solve_wit_1 : euler_theorem_inverse_partial_solve_wit_1.
Axiom proof_of_euler_theorem_inverse_partial_solve_wit_2_pure : euler_theorem_inverse_partial_solve_wit_2_pure.
Axiom proof_of_euler_theorem_inverse_partial_solve_wit_2 : euler_theorem_inverse_partial_solve_wit_2.

End VC_Correct.
